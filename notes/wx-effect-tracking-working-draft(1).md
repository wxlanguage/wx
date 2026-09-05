Hi! I'm building a programming language and compiler specifically for WebAssembly called WX. In this post I want to explain an effect tracking system I've been designing for it: what problems it tries to solve, how effects are represented in the compiler, and what benefits this information can give both developers and the optimizer.

WX is heavily inspired by Rust in its syntax and many of its concepts, but there are some important differences. One of the main goals of the language is to stay relatively close to WebAssembly and expose its features directly, while still providing convenient high-level abstractions on top.

Before getting into effects, there is one important property of WebAssembly we need to understand.

WebAssembly was designed as a platform for sandboxed code execution. A module doesn't automatically have access to things outside of its sandbox. If it wants to communicate with the outside world, that functionality has to be explicitly provided by the host.

For example, WebAssembly itself doesn't have a `print` function. If we want our module to print something, the host needs to provide that functionality as an import.

In WX that could look like this:

```rs
import "console" as console {
    fn log(n: i32) [log] -> ();
}

fn main() {
    console::log(123);
}

export {
    main,
}
```

You can think about a WebAssembly module almost like a function itself. The host provides its imports, while the module exposes exports that the host can call:

```text
                 +--------------------------+
                 |                          |
                 |                          |
                 +----.                .----+
                       \              /      \
  [HOST PLUG] --------> )    WASM    (        ) ---> [HOST SOCKET]
 (console::log)        /    MODULE    \      /        (main)
                 +----'                '----+
                 |                          |
                 |                          |
                 +--------------------------+
```

The host instantiates the module with the required imports and can then call its exported functions.

This sandbox boundary is going to become important for effects. An imported function such as `console::log` can do something observable outside of the WebAssembly module, while its implementation isn't even available for our compiler to inspect.

Now let's go back to our `main` function and ask a simple question: **what does this function actually do?**

A normal function signature describes its inputs and outputs. It tells us which values go in and which value comes back, but it doesn't tell us everything that might happen while the function is executing.

For example, consider:

```rs
fn do_something() -> () {
    console::log(123);
}
```

Looking only at `fn() -> ()`, we might think there isn't much interesting about this function. It takes nothing and returns nothing.

But removing the call would obviously change the behaviour of the program because it prints something to the outside world.

That's useful information for us as developers. A function signature tells us what values a function exchanges with us, so why shouldn't it also tell us what else the function might do?

It's useful to the compiler too. If the result of a computation isn't used, it would like to remove it, but before doing that it needs to know whether the computation can have some observable effect. The compiler works that out for itself, further down the pipeline where it can see the individual instructions — but as we'll see, there is one boundary where it can't, and has to rely on what we wrote in the signature.

This is where effects come in.

In WX, a function signature can contain an effect set after its arguments:

```rs
import "console" as console {
    fn log(n: i32) [log] -> ();
}
```

The square brackets describe the effects that may happen when the function is executed. Here, calling `console::log` has the `log` effect.

But this immediately raises another question: **what exactly is `log`? Where does an effect come from in the first place?**

## Effect origin and tracking

The one big problem in this model is: how do we even originate an effect? What is an effect from the compiler's perspective?

Many languages with effect systems introduce a separate vocabulary for effects. You might have effects such as `IO`, `Exception`, `State`, or user-defined effect operations. Functions can then declare that performing some operation introduces one of these effects.

But why do we need a separate concept for effects at all? We already have functions describing operations that can happen in our program. What if an effect could simply be a function?

This is essentially what WX does. A function with a body doesn't need to explicitly declare its effects — the compiler can infer them by looking at what happens inside the body. Effects can still be declared explicitly, but we'll come back to the relationship between declared and inferred effects later.

For a function without a body there is nothing to inspect, so the compiler cannot infer a more precise set. In that case, its declared effects are also its effective effect summary.

A bodyless function can declare no effects at all:

```rs
fn some_intrinsic() [] -> i32;
```

It can say that calling it may perform some already existing effect:

```rs
fn i32_div(a: i32, b: i32) [trap] -> i32;
```

Or it can reference itself, effectively becoming the origin of a new effect:

```rs
fn trap() [trap] -> never;
```

There is no separate `effect trap` declaration here. `trap` is just a function, and putting itself into its own effect set tells the compiler that this is where the `trap` effect originates.

In practice there are two main places where such bodyless functions come from in WX: imported functions, whose implementation lives outside the WebAssembly module, and compiler intrinsics representing WebAssembly instructions.

### How effects compose

Once an effect originates somewhere, it needs to propagate through everything that can reach it.

The rule here is fairly simple: the **inferred effects** of a function are the union of the effects that can happen inside its body.

Suppose we have two effectful operations:

```rs
fn foo() [foo];
fn bar() [bar];
```

and call both of them:

```rs
fn do_something() {
    foo();
    bar();
}
```

The compiler can infer the resulting effect set:

```rs
fn do_something() [foo, bar] {
    // ...
}
```

Effects form a set, so duplicates don't matter. Calling `foo()` once or ten times still only adds `foo` once.

An **effect** here is always one concrete identity, such as `trap` or `throw<ApplicationError>`. A fully resolved **effect set** is a finite set of those identities. Even a parameterized effect becomes concrete once its type arguments are known: `throw<ApplicationError>` and `throw<ConnectionError>` are two separate effects. Generic code may temporarily leave parts of a set unresolved, but we'll come back to that later.

The same process continues transitively through the call graph. If another function calls `do_something`, it inherits both `foo` and `bar` unless something handles those effects before they escape.

This means that for ordinary functions we don't have to manually propagate effects through every layer of the program. The compiler already knows which operations a function performs and which other functions it calls, so it can infer the resulting set automatically.

### Tracking traps

Let's look at a real example.

One of the most basic relevant WebAssembly instructions is `unreachable`, which unconditionally traps when executed. For clarity, WX exposes this operation as `trap`:

```rs
fn trap() [trap] -> never;
```

The `never` return type tells us that normal control flow cannot continue after this call. Separately, `[trap]` tells us why this computation is effectful: executing it may terminate the current WebAssembly execution with a trap.

When we call `trap` inside another function:

```rs
fn main() {
    trap();
}
```

the compiler can infer something equivalent to:

```rs
fn main() [trap] -> never;
```

Nothing special happened here specifically because this was a trap. We just applied the composition rule from above: `main` calls something with the `[trap]` effect, so `trap` becomes part of `main`'s effect set as well.

Now consider integer division. WebAssembly integer division traps when the divisor is zero, so WX can describe the intrinsic like this:

```rs
fn i32_div(a: i32, b: i32) [trap] -> i32;
```

Notice that this is `[trap]`, not `[i32_div]`.

Division itself isn't an effect we are interested in tracking. It's an ordinary computation which happens to be capable of reaching the already established `trap` effect.

This distinction is important: a bodyless function doesn't necessarily introduce a new effect. Its declared effect bound describes what effects executing that operation may ultimately perform. Because there is no body from which to infer anything more precise, that bound is also used as the function's effect summary. Self-reference is simply the mechanism for saying that the operation itself originates a new effect.

For this model to work, the compiler needs to eventually represent every potentially effectful operation through something whose effects it knows. This doesn't mean that everything has to **look** like a function call in source code. Operators and other syntax can still provide the usual abstractions, as long as they eventually lower to functions whose effects the compiler can track.

Operators in WX work through traits, similarly to Rust. For example, integer division eventually resolves to:

```rs
impl Div for i32 {
    fn div(self, other: Self) -> Self {
        i32_div(self, other)
    }
}
```

So when you write:

```rs
a / b
```

the compiler can follow that operation down to `i32_div`, which we already know has the `[trap]` effect. The abstraction doesn't hide the effect from the compiler.

Assignment variants work the same way. Unlike Rust, WX doesn't have a separate `DivAssign` trait: `a /= b` is syntax sugar derived from `Div`, so it ultimately carries the same effects.

## Exception handling

So far our effect system isn't particularly exciting. We can track that an operation might trap, propagate that information through arbitrary layers of functions, and then... that's about it. A WebAssembly trap cannot be caught by ordinary module code, so once the `trap` effect appears there isn't much we can do with it.

Exceptions give us a more interesting example because they can be handled.

The basic idea is similar to `trap`: somewhere in the program we perform an operation which interrupts normal control flow. The difference is that an exception can be caught before it escapes, allowing us to recover and continue execution.

This also gives us our first example of a parameterized effect.

WebAssembly exceptions are represented using tags. In WX, a tag declaration looks like this:

```rs
tag ApplicationError(status: ErrorStatus) -> never;
```

Tags automatically implement the `Tag` trait:

```rs
trait Tag {
    type Result;
}
```

An exception is a tag whose result is `never`:

```rs
trait Exception: Tag where { Result = never } {
    fn throw(self) -> never {
        throw(self)
    }
}
```

The underlying `throw` operation can then be represented as another bodyless intrinsic:

```rs
fn throw<E: Exception>(exception: E) [throw<E>] -> never;
```

This looks very similar to our earlier `trap`:

```rs
fn trap() [trap] -> never;
```

but there is one important difference. `throw` is generic, and the instantiated generic argument becomes part of the effect.

So these are distinct effects:

```rs
throw<ApplicationError>
throw<ConnectionError>
```

This means we don't merely know that a function "might throw". We know exactly which exception types it might throw.

For example:

```rs
fn handler() {
    if something() {
        ApplicationError(ErrorStatus::Internal).throw();
    }
}
```

The compiler can infer:

```rs
fn handler() [throw<ApplicationError>] {
    // ...
}
```

And just like before, if `handler` calls another function which can throw `ConnectionError`, the effects compose:

```rs
[throw<ApplicationError>, throw<ConnectionError>]
```

### Exceptions across the JavaScript boundary

WebAssembly exception tags can also be shared with JavaScript. A tag imported from JavaScript or exported by a module has one runtime identity. JavaScript can use that same `WebAssembly.Tag` to construct a `WebAssembly.Exception`, and WebAssembly matches the exception using the tag itself — another tag with the same payload types is not enough. In the other direction, a typed exception which escapes from an exported WebAssembly function appears in JavaScript as a `WebAssembly.Exception` carrying that same tag.

This means that WX can import a tag together with a host function which may throw it:

```rs
import "host" as host {
    tag HostError(error: externref) -> never;
    fn request() [throw<HostError>] -> Response;
}
```

The host provides the `HostError` tag when the module is instantiated. If `request` throws an exception constructed with that same tag, WX can catch it as `HostError` and keep the precise `[throw<HostError>]` contract.

If the host function has a known finite set of possible tags, it can list each concrete effect in the same way. This is particularly useful at an import boundary because the compiler cannot inspect the JavaScript implementation. The annotation is the only effect information it has.

An arbitrary JavaScript exception is different. Under the current [WebAssembly JavaScript API](https://webassembly.github.io/spec/js-api/), a value thrown by JavaScript through an imported function is carried into WebAssembly using the separate `WebAssembly.JSTag`. It does not automatically become a WX exception type based on its JavaScript class. WX may eventually expose that as a separate interop effect, but that part of the design is not settled.

So JavaScript interop is not a reason to widen an import to `[throw<_>]`. When a precise tag contract is available, the import should name those concrete effects directly.

### Handling effects

This is where exceptions become more interesting than our previous examples.

So far effects could only originate and propagate outward. A `catch` gives us a way to handle an effect before it escapes:

```rs
fn main() {
    local result = handler() catch {
        ApplicationError(status) -> {
            fallback()
        },
    };
}
```

If `handler()` has:

```rs
[throw<ApplicationError>]
```

and the `catch` handles `ApplicationError`, then that effect no longer propagates beyond the `catch`.

You can think of it as transforming the effect set of the expression:

```text
handler()
    [throw<ApplicationError>]
        catch ApplicationError
    []
```

If the expression can perform other effects, however, those remain:

```text
[log, throw<ApplicationError>, throw<ConnectionError>]
        catch ApplicationError
[log, throw<ConnectionError>]
```

So handling an effect doesn't make the whole expression pure. It only removes the effects which were actually handled.

When the expression has a concrete effect set, the compiler knows which exception effects can reach a `catch` and can check whether the handler is exhaustive. You can explicitly handle every possible exception:

```rs
local result = handler() catch {
    ApplicationError(status) -> ...,
    ConnectionError(code) -> ...,
};
```

or use a `_` fallback when you intentionally don't care which exception was thrown:

```rs
local result = handler() catch {
    ApplicationError(status) -> ...,
    _ -> fallback(),
};
```

The `_` here is only a catch-all pattern for the handler. It removes the concrete exception effects which can reach this `catch`; it does not add a wildcard effect to the set.

In that sense, `catch` is similar to a `match`: instead of exhaustively matching possible values, we're exhaustively handling possible exceptional exits from a computation.

The analogy carries a consequence worth flagging early. What the compiler checks against is the effect contract used for `handler`, so if that contract later grows a new exception, this exhaustive `catch` stops compiling — exactly as adding a variant breaks a `match`. Handling exceptions precisely is what buys that breakage; we'll come back to what it means at a public API boundary.

### Effect scopes

So far we have treated the effects of a function as one flat set. That works until the same effect appears both inside and outside of a `catch`:

```rs
fn f() {
    might_throw();
    might_throw() catch {
        AppError(status) -> 0,
    };
}
```

Both calls have the `[throw<AppError>]` effect, but the `catch` only handles the exception from the second call. The first one can still escape, so `f` must also have `[throw<AppError>]`.

If the compiler flattened the body first, both calls would collapse into the same set element. Subtracting `throw<AppError>` would then remove the effect from both of them. We need to preserve the structure of the body until the `catch` has been applied.

Instead of a flat set, we can describe the effects using a small expression:

```text
term = atom(effect)
     | term ∪ term
     | term − [effects]
```

There are only three cases:

- `atom(effect)` represents one effect, such as `log` or `trap`.
- `a ∪ b` combines the effects of two terms.
- `a − [effects]` removes a set of handled effects from one term.

Without a `catch`, a function body is just a union of atoms. For example:

```rs
fn f() {
    console::log(1);
    might_trap();
}
```

can be represented as:

```text
atom(log) ∪ atom(trap)
```

Evaluating the term is just a set union:

```text
[log] ∪ [trap] = [log, trap]
```

In the first example, subtraction applies only to the second call:

```text
atom(throw<AppError>)
    ∪ (atom(throw<AppError>) − [throw<AppError>])
```

which evaluates to:

```text
[throw<AppError>] ∪ ([throw<AppError>] − [throw<AppError>])
    = [throw<AppError>]
```

The term on the left side of that subtraction is the **effect scope** of the `catch`. Only effects from that term can be removed. The same effect outside of it continues to propagate normally.

There is one more important part of this rule: the handler itself is outside of the scope it handles.

```rs
fn f() {
    fetch() catch {
        ConnectionError(_) -> retry(),   // retry() can throw it too
    };
}
```

Here `fetch()` throws `ConnectionError`, but `retry()` can throw the same exception again. The effect term looks like this:

```text
(atom(throw<ConnectionError>) − [throw<ConnectionError>])  // fetch
    ∪ atom(throw<ConnectionError>)                          // retry
```

The subtraction removes the exception from `fetch()`. It does not remove the one from `retry()`, because that atom is outside the subtraction. The final effect set is therefore still:

```text
[throw<ConnectionError>]
```

This is the same behaviour we would expect from `try`/`catch` in other languages. An exception thrown by a handler does not loop back into the same handler. Catching it requires another `catch`.

So effect composition comes down to three operations. Functions introduce effect atoms, ordinary control flow combines them using unions, and constructs such as `catch` subtract handled effects from a particular scope.

This gives us the other half of effect tracking. Function calls and operations add and compose effects, while constructs that understand a particular effect can handle it and prevent it from propagating further.

### Recursive functions

There is one case where inference needs a little more care: functions can call each other.

```rs
fn ping() {
    console::log(1);
    pong();
}

fn pong() {
    if something() {
        ping();
    }
}
```

Here `ping` depends on the effects of `pong`, while `pong` depends on the effects of `ping`. The compiler cannot finish either function independently. It has to solve the group together until the effect sets stop changing.

With union alone, both functions end up with `[log]`. A `catch` can make the result more precise: two mutually recursive functions do not necessarily have the same effects if one of them handles an effect before it escapes.

Groups like this are known as strongly connected components of the call graph. The exact algorithm used to solve them is an implementation detail, but the language-level rule stays the same: effects propagate through calls unless a surrounding scope handles them.

## Memory effects

Before we continue, I need to briefly explain how memory works in WX, since it's somewhat different from what you might be used to in other languages.

WebAssembly modules aren't required to have linear memory at all. A module can simply export functions that operate on values directly. When you do need memory, however, it has to be explicitly declared. In WX, that looks like this:

```rs
memory heap: Memory where { Size = u32 };
```

`heap` is the name of the memory and can be referenced elsewhere in the program. The `Memory` trait describes the memory itself, while `Size` tells us the size of its addresses. In this case, pointers into `heap` use 32-bit addresses.

More importantly, every memory declaration creates its own unique type. If we declare two memories:

```rs
memory heap: Memory where { Size = u32 };
memory secondary: Memory where { Size = u64 };
```

`heap` and `secondary` aren't just two values referring to different memories — they also represent distinct types.

Pointers carry this information as part of their type:

```rs
// type alias just for demonstration purposes
type Pointer<Mem: Memory> = Mem::*u8;
                            ^^^
```

A `heap::*u8` therefore cannot be confused with a `secondary::*u8`. From the pointer type alone, the compiler knows exactly which linear memory the pointer belongs to.

This means that whenever we perform an operation through a pointer, the compiler doesn't merely know that we're accessing **some memory**. It knows exactly which memory is being accessed.

This distinction is going to become important for effect tracking.

```rs
fn read<Mem: Memory>(mem: Mem) [read<Mem>];
fn write<Mem: Memory>(mem: Mem) [write<Mem>];
fn grow<Mem: Memory>(mem: Mem) [grow<Mem>];
```

Just like `throw<E>` from the previous example, these effects are parameterized by a type. Since every memory has its own unique type, `read<heap>` and `read<secondary>` are two distinct effects.

What's slightly unusual here is that these functions don't actually read or write anything themselves. They don't even take a pointer. The memory instance is effectively just a zero-sized value identifying a particular memory, so these calls don't need to produce any runtime code.

But that's the whole idea.

There are many different operations that can access memory. WebAssembly itself has a whole set of load, store and memory instructions, while imported host functions can access a module's memory as well. Giving every one of those operations its own effect would preserve information we don't really care about.

What we usually want to know is much simpler: **which memory can this computation read or modify?**

So all operations that read `heap` can share `read<heap>`, while operations that may modify it share `write<heap>`.

This information is also useful for the optimizer. Consider an imported function:

```rs
fn process_audio(...) [write<audio_memory>];
```

The compiler can't inspect its implementation, but it still knows something very important: after calling it, any previously loaded value from `audio_memory` might be stale.

At the same time, the effect says nothing about other memories. If we also have a separate `heap`, the compiler knows that `process_audio` cannot modify it, so values loaded from `heap` can still be safely reused.

There is a limit to how precise this information is. `write<audio_memory>` doesn't tell us **where** inside that memory the function writes. It might modify one byte or the entire memory, so across an opaque call like this the safe assumption is that any previous read from `audio_memory` may have been invalidated.

This doesn't mean that the compiler has to be equally conservative when optimizing code it can actually see. Inside the module we can still perform normal alias analysis and use the language's borrowing rules to prove that two pointers cannot refer to the same location. In those cases, the optimizer can reason about individual accesses much more precisely.

So these two mechanisms complement each other. Alias analysis gives us fine-grained information while we're looking at code the compiler understands, while memory effects preserve the information we need when we cross a boundary where that analysis stops — most importantly, when calling imported functions.

This is worth stating as a general rule, because it isn't specific to memory. **The effect sets in your signatures aren't what drives optimization.** Not because the compiler doesn't need that information — it very much does — but because it derives it later, at a level where the information fits better.

An effect set is a high-level construct. Its unit is the whole function, so `[trap]` tells us that something in here might trap, without saying which operation or under what conditions. It is also a contract, which means it is deliberately allowed to be broader than the truth. Both of those are exactly what we want from a signature, and neither is what an optimizer wants. Working on the actual instructions instead, the compiler can tell that a particular division cannot trap because the divisor was already checked — which no function signature could ever express.

What the optimizer does need is the effects declared on **imported** functions. That's the one place where there is no body to look at, so the annotation is the only information that exists. Telling the compiler that `process_audio` writes `audio_memory` and nothing else isn't a hint it could have derived on its own — it's the only thing standing between "this call might do anything" and a useful answer.

We could theoretically make the effects themselves more precise by tracking individual memory regions or ranges, but that would be too much of a headache to manage properly. I think the current abstraction is more than enough to produce good, optimizable code.

As a small side note, `grow` is a separate effect because WebAssembly linear memory can grow during execution, but currently cannot shrink. The effect model simply reflects that asymmetry.


## Global variables

Global variables follow the same general model as the other low-level WebAssembly features we've looked at so far.

At the bottom we have a couple of compiler intrinsics that directly represent WebAssembly's global instructions and act as effect sources:

```rs
fn global_get<G: Global>(g: G) [global_get<G>] -> G::Value;
fn global_set<G: GlobalMut>(g: G, value: G::Value) [global_set<G>];
```

On top of those, the standard library exposes separate traits for immutable and mutable globals:

```rs
trait Global {
    type Value: Copy;
    fn get(self) -> Self::Value {
        global_get(self)
    }
}

trait GlobalMut: Global {
    fn set(self, value: Self::Value) {
        global_set(self, value)
    }
}
```

A global can then be declared like any other item:

```rs
global x: GlobalMut where { Value = i32 } = 0;
```

and accessed explicitly through `get` and `set`:

```rs
fn main() { // [global_get<x>, global_set<x>]
    x.set(x.get() + 1);
}
```

Just like with memories, every global has its own identity, so `global_get<x>` and `global_get<y>` are different effects. This gives the compiler precise information about which particular global a function may observe or modify.

One deliberate difference from local variables is that globals have to be accessed through `get()` and `set()`. WX doesn't implement ordinary arithmetic or assignment operators directly on global values.

For example, something like this is intentionally not supported:

```rs
x += 1;
```

Allowing that would mean otherwise simple primitive operators such as `Add`, or assignment syntax itself, could silently introduce global effects. I want primitive operations to stay as predictable as possible, so global access remains explicit in the source code.

The slightly more verbose version:

```rs
x.set(x.get() + 1);
```

makes it immediately visible that we're reading and then modifying global state. It also maps very directly to the underlying WebAssembly operations.

There is one more restriction: WebAssembly globals in WX can only contain primitive values. You cannot store an aggregate such as a struct or tuple directly in a global.

If you need global aggregate state, you can instead place the value in memory and store a pointer to it:

```rs
global state: GlobalMut where { Value = heap::&mut State } = ...;
```

A pointer is itself a primitive value, so it can be stored in a global normally.

This restriction also keeps importing and exporting globals simple. If aggregate globals were supported directly, WX would need to define an ABI for how those aggregates are represented across the WebAssembly module boundary, including how they are laid out and how imported or exported globals map to their underlying representation.

By keeping globals limited to values that WebAssembly itself can represent directly, imports and exports stay predictable and don't require any hidden transformations.

I also quite like the explicit `get()` and `set()` syntax as a side effect of this design. Global state stands out visually from ordinary local computation, and the corresponding effects are equally explicit to the compiler. The exact API may still change, but I think the underlying model is useful.

## Effect bounds

There are now two effect sets we need to distinguish. The **inferred effects** come from the function body. The **declared effects** are the ones written explicitly in its annotation.

The declared effects act as an upper bound. The compiler still infers the body and checks that everything it finds is allowed by the annotation. If there is no annotation, the inferred effects become the function's effect set directly.

Consider:

```rs
fn calculate() [trap] -> i32 {
    100 / get_value()
}
```

The compiler still infers the effects of the body and checks them against the annotation:

```text
inferred effects = [trap]
declared effects = [trap]

[trap] ⊆ [trap]
```

The inferred set is allowed to be smaller:

```rs
fn calculate() [trap] -> i32 {
    42
}
```

Here `[] ⊆ [trap]`, so the function is perfectly valid. The annotation says that `calculate` is allowed to trap, not that it necessarily does.

An effect outside the bound is different:

```rs
fn calculate() [trap] -> i32 {
    console::log(42);
    42
}
```

Now `[log] ⊄ [trap]`, so the compiler reports a hard error. The general rule is simply:

```text
inferred effects ⊆ declared effects
```

This also gives `[]` a useful meaning: because the only subset of the empty set is itself, annotating a function with `[]` requires it to remain pure.

At the other extreme, `[*]` is the unrestricted top bound. It is not a concrete effect set and `*` is not an effect that can originate from a function. It simply means that there is no useful restriction on which effects are permitted.


### What callers see

We've set up a question but haven't answered it. Take:

```rs
fn calculate() [trap] -> i32 {
    42
}
```

The body has no inferred effects, but the function declares `[trap]`. So when something calls `calculate`, which set does it get?

WX answers: **the declared effects**. If you write the effects yourself, you own them — everyone who calls your function uses the set you wrote, not the one the compiler inferred from your body.

We can see it directly:

```rs
fn calculate() [trap] -> i32 {
    42
}

fn main() {          // inferred: [trap]
    calculate();
}
```

`main` calls a function that cannot trap, and still comes out with `[trap]`. Not because the compiler failed to notice — it can see perfectly well that the body is `42` — but because it uses what `calculate` promised rather than what it happens to do today.

It has to work that way, or the annotation would be worthless. `calculate` is explicitly allowed to trap. If callers were compiled against `[]` instead, then changing the body to something that actually divides would break every one of them, without the signature ever changing.

So an annotation can only ever **widen** what the rest of the program sees. There is no way to write one that makes a function look purer than it really is:

```text
what callers see  ⊇  what the function can actually do
```

The practical advice follows from that. Inside your own code, just let the compiler infer. It knows more than you're going to write down, and it keeps up when you edit the body. Write the annotation where you actually need a fixed contract — a public function, or a trait method.

And when you do write one, keeping it tight is now your job. A bound that's wider than necessary isn't wrong and isn't an error, but it does reduce effect-system precision for every caller. Their inferred effects include the wider contract even when the current implementation happens to do less.

That does not necessarily make the implementation itself harder to optimize. If the compiler can inspect the body of `calculate`, it can still see that the body is just `42` and optimize it using the lowered instructions and whatever more precise analysis is available there. The declared effects become important to optimization when that implementation is opaque — for example, across an imported function, an unresolved indirect call, or another boundary where the body is unavailable.

WX doesn't have a linter yet, but this is exactly the sort of thing one could report: an annotation listing an effect the body never performs. I mention it as a future idea rather than a feature, and it would have to stay a lint you can switch off — declaring room to grow is a perfectly reasonable thing to do on purpose, so it can't be a warning the compiler insists on.

## Effect polymorphism

Effects also appear in function types. For example:

```rs
fn() [trap] -> i32
```

describes a callable whose effects are bounded by `[trap]`. A pure function can safely be used where this type is expected because `[] ⊆ [trap]`.

More generally, a function with effect bound `A` can be coerced to one with bound `B` whenever:

```text
A ⊆ B
```

So these coercions are safe:

```text
fn() []          -> i32
        ↓
fn() [trap]      -> i32
        ↓
fn() [trap, log] -> i32
        ↓
fn() [*]         -> i32
```

The reverse direction is not safe: a caller expecting `fn() [] -> i32` relies on the guarantee that invoking it cannot perform any effects.

### Losing precision

Widening an effect bound is safe, but it deliberately loses information:

```rs
fn get_number() -> i32 {
    42
}

local f: fn() [trap] -> i32 = get_number;
```

The effect analysis originally knew that `get_number` was pure. Through the type of `f`, however, all it knows is the declared bound, so `f()` contributes `[trap]`. A later optimization may recover more precise information if it can prove which function `f` refers to, but the function type itself does not provide that guarantee.

The same happens in a higher-order function:

```rs
fn apply(
    f: fn() [trap] -> i32,
) [trap] -> i32 {
    f()
}
```

A pure callback is accepted, but calling `apply` still exposes `[trap]`. What we would sometimes like to express instead is that `apply` has exactly whatever effects its callback has.

### Effect-set parameters

WX introduces a separate generic parameter kind for effect sets using `fx`:

```rs
fn apply<fx E>(
    f: fn() [E] -> i32,
) [E] -> i32 {
    f()
}
```

`E` represents an entire effect set rather than one individual effect. Depending on the callback it might become `[]`, `[trap]`, `[log]`, or any other set. Until that callback is known, `E` is a symbolic part of the surrounding effect set rather than a new kind of effect.

This preserves the relationship instead of widening every callback to one common bound:

```text
apply(pure)   → E = []     → []
apply(divide) → E = [trap] → [trap]
apply(logger) → E = [log]  → [log]
```

Effect-set parameters compose with concrete effects using the same set union as everything else:

```rs
fn apply_and_log<fx E>(
    f: fn() [E] -> i32,
) [log, E] -> i32 {
    console::log(123);
    f()
}
```

Here `[log, E]` means `{log} ∪ E`:

```text
[E, log]
    where E = [trap]

        ↓ substitution

[trap, log]
```

This is still the same set union as before. `E` only postpones the final answer until a substitution is available.

Multiple parameters work the same way:

```rs
fn apply_both<fx A, fx B>(
    a: fn() [A],
    b: fn() [B],
) [A, B] {
    a();
    b();
}
```

where `[A, B]` means `A ∪ B`.

### Effect-set bounds

Effect-set parameters can themselves be bounded:

```rs
fn apply<fx E: [trap]>(
    f: fn() [E] -> i32,
) [E] -> i32 {
    f()
}
```

This uses exactly the same upper-bound relation again:

```text
E ⊆ [trap]
```

So `E = []` and `E = [trap]` are valid, while `E = [log]` or `[trap, log]` are not.

This differs subtly from accepting `fn() [trap] -> i32` directly. Both versions restrict the callback to effects within `[trap]`, but the concrete function type widens the callback to that bound. The polymorphic version preserves which particular subset was actually supplied.

Sometimes we want to restrict an effect-set parameter to one particular kind of effect. This is where wildcard patterns become useful:

```rs
fn apply<fx E: [throw<_>]>(
    f: fn() [E] -> i32,
) [E] -> i32 {
    f()
}
```

Here `[throw<_>]` is not an ordinary effect set and it is not the effect set of `apply`. It is a pattern constraining which concrete effects `E` may contain:

```text
every effect in E must match throw<_>
```

For example:

```text
E = []                                      valid
E = [throw<ApplicationError>]               valid
E = [throw<A>, throw<B>]                    valid

E = [trap]                                  invalid
E = [throw<ApplicationError>, log]          invalid
```

The pattern only checks `E`; it does not replace it. If the callback has `[throw<ApplicationError>]`, the result of `apply` is still `[throw<ApplicationError>]`, not `[throw<_>]`.

This keeps the different forms separate:

```text
resolved effect set     a finite set of concrete effects

symbolic effect set     a set containing unresolved generic information,
                        such as an fx parameter or generic trait call

effect-bound patterns   constraints on which concrete effects an fx
                        parameter may contain

unrestricted bound      [*], which permits any effect
```

Fully resolved effect sets therefore keep their simple set-theoretic structure. They are ordered by subset, and union is their join:

```text
[] ⊆ [throw<A>] ⊆ [throw<A>, throw<B>]
```

`[throw<_>]` is not another element in this lattice. It selects which concrete sets are valid substitutions for `E`. In particular, catching never has to produce a set such as `[throw<_>] − [throw<ApplicationError>]`, with the implied meaning of every exception except one. Catching continues to subtract concrete effects from the term it handles.

`[*]` remains different. It is the unrestricted top bound, meaning that any effect is permitted. `[throw<_>]` is narrower and structured: in `<fx E: [throw<_>]>`, every effect in `E` must be an instantiation of `throw`.

A type parameter cannot take its place. Writing `fn f<E: Exception>() [throw<E>]` says that `f` can only throw the single exception type `E`, chosen by whoever calls it — not that it may throw any number of exception types.

### Traits

Trait methods use exactly the same rule:

```rs
trait Validator {
    fn validate(value: i32) [throw<ValidationError>] -> bool;
}
```

The annotation is an upper bound on every implementation. An implementation may use the whole bound:

```rs
impl Validator for StrictValidator {
    fn validate(value: i32) -> bool {
        if value <= 0 {
            ValidationError::{}.throw();
        }

        true
    }
}
```

or a smaller set:

```rs
impl Validator for PositiveValidator {
    fn validate(value: i32) -> bool {
        value > 0
    }
}
```

The second implementation is pure, and `[] ⊆ [throw<ValidationError>]`, so it satisfies the trait just as well. An implementation that introduces `log`, however, would be rejected because `[log]` is not a subset of the declared effects.

There is therefore no special meaning attached to an effect annotation inside a trait. The interesting difference is simply that a bodyless trait method has no implementation from which the compiler could infer a more precise set. At the trait boundary, its declared effects are the best effect summary available.

Omitting the annotation from a trait method means that the trait places no restriction on its effects, which is equivalent to using `[*]`.

### Generic trait calls

Now consider using the trait through a generic parameter:

```rs
fn validate_with<V: Validator>(validator: V, value: i32) -> bool {
    validator.validate(value)
}
```

It would be safe to immediately treat the call as `[throw<ValidationError>]`, but doing so would throw away information. The actual effects depend on which implementation is eventually selected, so the compiler can preserve the unresolved call itself:

```text
[<V as Validator>::validate]
```

This is symbolic effect information, not a new runtime effect. The trait bound already tells us that it is restricted:

```text
effects(<V as Validator>::validate)
    ⊆ [throw<ValidationError>]
```

So the compiler can check the generic function without pretending that the call is completely unrestricted. When `V` becomes concrete, it resolves the symbolic call to the implementation's actual effect set:

```text
<V as Validator>::validate
        ↓ V = PositiveValidator
<PositiveValidator as Validator>::validate
        ↓
[]
```

while `StrictValidator` resolves to:

```text
<V as Validator>::validate
        ↓ V = StrictValidator
<StrictValidator as Validator>::validate
        ↓
[throw<ValidationError>]
```

The trait bound still guarantees that every possible implementation stays within `[throw<ValidationError>]`; static generic dispatch simply lets the compiler retain a more precise set whenever the implementation becomes known.

### Default implementations

Default method bodies are checked against their declared effects in the same way as any other function. They can also call other bounded trait methods:

```rs
trait Reporter {
    fn report(self, message: str) [log];

    fn report_error(self, message: str) [log] {
        self.report(message)
    }
}
```

The exact implementation of `report` isn't known, but every implementation is guaranteed to stay within `[log]`, so the compiler can prove that the default body also satisfies its bound.

If `report` were unrestricted, its call would have to be conservatively treated as `[*]`, which cannot be proven to fit inside `[log]`.

### Dynamic dispatch

With static generic dispatch, an unresolved call such as `<V as Validator>::validate` may eventually become concrete. With dynamic dispatch, the implementation is selected at runtime, so that opportunity never arrives.

At the effect-analysis level, as long as the call remains dynamically dispatched, the trait's declared effects are the best summary available. A call to a method declaring `[throw<ValidationError>]` therefore contributes that whole set, even if the implementation selected at runtime happens to be pure. A later optimization may become more precise if it can devirtualize the call; otherwise it has the same abstraction boundary. An unrestricted method similarly contributes `[*]`.

### When symbolic effects become concrete

We can now connect effect polymorphism back to the effect terms we introduced earlier.

A function body is first described as an effect term made from atoms, unions, and subtractions. For an ordinary function, all of those pieces become concrete once its callees are known, so the term can be evaluated directly:

```text
function body
      ↓
effect term
      ↓
[trap, log]
```

A generic body may not have enough information yet. Its term can contain an effect-set parameter such as `E`, or an unresolved call such as `<V as Validator>::validate`. Instead of replacing those symbols with a wider bound, the compiler keeps them in the term until the generic is instantiated.

For example, a generic body might produce:

```text
generic body
      ↓
[log] ∪ (E − [throw<ApplicationError>])
      ↓
E = [log, throw<ApplicationError>]
      ↓ substitution
[log] ∪ ([log, throw<ApplicationError>] − [throw<ApplicationError>])
      ↓
[log]
```

The same idea applies to a symbolic trait call. Once `V` is known, `<V as Validator>::validate` is replaced by the effects of the selected implementation, and the surrounding term can be evaluated normally.

These symbols are placeholders for effect sets which will eventually become concrete. That is different from a pattern such as `throw<_>`, which only constrains a substitution and never becomes part of the propagated term.

**The function body is not analyzed again from scratch for every instantiation.** It is analyzed once into a symbolic effect term. Instantiation only supplies the missing pieces and evaluates that reusable term.

So generics postpone effect resolution, not effect analysis. Symbolic effects are what let the compiler retain the relationships found in the body until enough context exists to produce the final concrete set.

## Effects at public boundaries

Public functions require an explicit effect bound:

```rs
pub fn calculate(value: i32) [trap] -> i32 {
    ...
}
```

Not because a different rule applies across a package boundary — the one from earlier holds everywhere — but because inference would make your published API implicit. Without the annotation your signature would be whatever the body happened to do most recently, so editing an implementation detail would change what downstream code sees, without you touching anything you thought of as public.

Writing the bound is what buys back the freedom to change that implementation. `calculate` may be pure today and grow a division tomorrow; both satisfy `[trap]`, which is what callers were already compiled against.

There is a limit to that freedom, and it's worth being explicit about it. Moving *within* the bound is free; growing the bound itself is not. If `calculate` later declares `[trap, throw<ParseError>]`, every caller that was catching exhaustively suddenly has an exception it doesn't handle, and stops compiling. Widening is a breaking change in exactly the way adding a variant to a public enum is — invisible to anyone who ignored the effects, breaking for anyone who was handling them precisely.

An effect-bound pattern such as `[throw<_>]` does not provide an escape hatch here. It can constrain an `fx` parameter, but it cannot be used as the declared effect set of a concrete public function. If WX needs an equivalent of a non-exhaustive public exception set, that will require a separate design.

What makes a package boundary the place this matters most is the stakes rather than the rule. Downstream code is compiled separately, so a change inside your implementation must not be able to move the effects it was compiled against.

Public APIs can also expose polymorphic relationships rather than one concrete set:

```rs
pub fn apply<fx E>(
    f: fn() [E] -> i32,
) [E] -> i32 {
    f()
}
```

or compose them:

```rs
pub fn apply_and_log<fx E>(
    f: fn() [E] -> i32,
) [log, E] -> i32 {
    console::log(123);
    f()
}
```

These signatures don't commit the API to one concrete effect set. Instead, they describe how the effects exposed by the function depend on the effects of its arguments.

This is where making effects part of the type system becomes useful. Within a concrete body, inference can discover what the implementation does. But once functions are passed around, abstracted over, dynamically dispatched, or exposed across package boundaries, their types need to preserve both what effects are allowed and how those effects depend on other parts of the program.
