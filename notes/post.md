Hi! I'm building a programming language and compiler specifically for WebAssembly called WX. In this post I want to explain an effect tracking system I've been designing for it: what problems it tries to solve, how effects are represented in the compiler, and what benefits this information can give both developers and the optimizer.

WX is heavily inspired by Rust in its syntax and many of its concepts, but there are some important differences. One of the main goals of the language is to stay relatively close to WebAssembly and expose its features directly, while still providing convenient high-level abstractions on top.

Before getting into effects, there is one important property of WebAssembly we need to understand.

WebAssembly was designed as a platform for sandboxed code execution. A module doesn't automatically have access to things outside of its sandbox. If it wants to communicate with the outside world, that functionality has to be explicitly provided by the host.

For example, WebAssembly itself doesn't have a `print` function. If we want our module to print something, the host needs to provide that functionality as an import.

In WX that could look like this:

```rust
import "console" as console {
    fn log(n: i32) [log];
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

```rust
fn do_something() -> () {
    console::log(123);
}
```

Looking only at `fn() -> ()`, we might think there isn't much interesting about this function. It takes nothing and returns nothing.

But removing the call would obviously change the behaviour of the program because it prints something to the outside world.

This information matters to the optimizer. If the result of a computation isn't used, the compiler would like to remove it when possible. But before doing that, it needs to know whether executing that computation can have some observable effect.

It would also be useful information for us as developers. A function signature tells us what values a function exchanges with us, so why shouldn't it also tell us what else the function might do?

This is where effects come in.

In WX, a function signature can contain an effect set after its arguments:

```rust
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

This is essentially what WX does. A function with a body doesn't need to explicitly declare its effects — the compiler can infer them by looking at what happens inside the body. But for a function without a body there is nothing to inspect, so its effects have to be declared explicitly.

A bodyless function can declare no effects at all:

```rust
fn some_intrinsic() [] -> i32;
```

It can say that calling it may perform some already existing effect:

```rust
fn i32_div(a: i32, b: i32) [trap] -> i32;
```

Or it can reference itself, effectively becoming the origin of a new effect:

```rust
fn trap() [trap] -> never;
```

There is no separate `effect trap` declaration here. `trap` is just a function, and putting itself into its own effect set tells the compiler that this is where the `trap` effect originates.

In practice there are two main places where such bodyless functions come from in WX: imported functions, whose implementation lives outside the WebAssembly module, and compiler intrinsics representing WebAssembly instructions.

### How effects compose

Once an effect originates somewhere, it needs to propagate through everything that can reach it.

The rule here is fairly simple: the effects of a function are the union of the effects that can happen inside its body.

Suppose we have two effectful operations:

```rust
fn foo() [foo];
fn bar() [bar];
```

and call both of them:

```rust
fn do_something() {
    foo();
    bar();
}
```

The compiler can infer the resulting effect set:

```rust
fn do_something() [foo, bar] {
    // ...
}
```

Effects form a set, so duplicates don't matter. Calling `foo()` once or ten times still only adds `foo` once.

The same process continues transitively through the call graph. If another function calls `do_something`, it inherits both `foo` and `bar` unless something handles those effects before they escape.

This means that for ordinary functions we don't have to manually propagate effects through every layer of the program. The compiler already knows which operations a function performs and which other functions it calls, so it can infer the resulting set automatically.

### Tracking traps

Let's look at a real example.

One of the most basic relevant WebAssembly instructions is `unreachable`, which unconditionally traps when executed. For clarity, WX exposes this operation as `trap`:

```rust
fn trap() [trap] -> never;
```

The `never` return type tells us that normal control flow cannot continue after this call. Separately, `[trap]` tells us why this computation is effectful: executing it may terminate the current WebAssembly execution with a trap.

When we call `trap` inside another function:

```rust
fn main() {
    trap();
}
```

the compiler can infer something equivalent to:

```rust
fn main() [trap] -> never;
```

Nothing special happened here specifically because this was a trap. We just applied the composition rule from above: `main` calls something with the `[trap]` effect, so `trap` becomes part of `main`'s effect set as well.

Now consider integer division. WebAssembly integer division traps when the divisor is zero, so WX can describe the intrinsic like this:

```rust
fn i32_div(a: i32, b: i32) [trap] -> i32;
```

Notice that this is `[trap]`, not `[i32_div]`.

Division itself isn't an effect we are interested in tracking. It's an ordinary computation which happens to be capable of reaching the already established `trap` effect.

This distinction is important: a bodyless function doesn't necessarily introduce a new effect. Its declared effect set describes what effects executing that operation may ultimately perform. Self-reference is simply the mechanism for saying that the operation itself originates a new one.

For this model to work, the compiler needs to eventually represent every potentially effectful operation through something whose effects it knows. This doesn't mean that everything has to *look* like a function call in source code. Operators and other syntax can still provide the usual abstractions, as long as they eventually lower to functions whose effects the compiler can track.

Operators in WX work through traits, similarly to Rust. For example, integer division eventually resolves to:

```rust
impl Div for i32 {
    fn div(self, other: Self) -> Self {
        i32_div(self, other)
    }
}
```

So when you write:

```rust
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

```rust
tag ApplicationError(status: ErrorStatus) -> never;
```

Tags automatically implement the `Tag` trait:

```rust
trait Tag {
    type Result;
}
```

An exception is a tag whose result is `never`:

```rust
trait Exception: Tag where { Result = never } {
    fn throw(self) -> never {
        throw(self)
    }
}
```

The underlying `throw` operation can then be represented as another bodyless intrinsic:

```rust
fn throw<E: Exception>(exception: E) [throw<E>] -> never;
```

This looks very similar to our earlier `trap`:

```rust
fn trap() [trap] -> never;
```

but there is one important difference. `throw` is generic, and the instantiated generic argument becomes part of the effect.

So these are distinct effects:

```rust
throw<ApplicationError>
throw<ConnectionError>
```

This means we don't merely know that a function "might throw". We know exactly which exception types it might throw.

For example:

```rust
fn handler() {
    if something() {
        ApplicationError(ErrorStatus::Internal).throw();
    }
}
```

The compiler can infer:

```rust
fn handler() [throw<ApplicationError>] {
    // ...
}
```

And just like before, if `handler` calls another function which can throw `ConnectionError`, the effects compose:

```rust
[throw<ApplicationError>, throw<ConnectionError>]
```

### Handling effects

This is where exceptions become more interesting than our previous examples.

So far effects could only originate and propagate outward. A `catch` gives us a way to handle an effect before it escapes:

```rust
fn main() {
    local result = handler() catch {
        ApplicationError(status) -> {
            fallback()
        },
    };
}
```

If `handler()` has:

```rust
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

Because the compiler knows the exact set of exception effects that can reach a `catch`, WX can also check whether the handler is exhaustive. You can explicitly handle every possible exception:

```rust
local result = handler() catch {
    ApplicationError(status) -> ...,
    ConnectionError(code) -> ...,
};
```

or use a `_` fallback when you intentionally don't care which exception was thrown:

```rust
local result = handler() catch {
    ApplicationError(status) -> ...,
    _ -> fallback(),
};
```

In that sense, `catch` is similar to a `match`: instead of exhaustively matching possible values, we're exhaustively handling possible exceptional exits from a computation.

This gives us the other half of effect tracking. Function calls and operations add and compose effects, while constructs that understand a particular effect can handle it and prevent it from propagating further.

## Memory effects

Before we continue, I need to briefly explain how memory works in WX, since it's somewhat different from what you might be used to in other languages.

WebAssembly modules aren't required to have linear memory at all. A module can simply export functions that operate on values directly. When you do need memory, however, it has to be explicitly declared. In WX, that looks like this:

```wx
memory heap: Memory where { Size = u32 };
```

`heap` is the name of the memory and can be referenced elsewhere in the program. The `Memory` trait describes the memory itself, while `Size` tells us the size of its addresses. In this case, pointers into `heap` use 32-bit addresses.

More importantly, every memory declaration creates its own unique type. If we declare two memories:

```wx
memory heap: Memory where { Size = u32 };
memory secondary: Memory where { Size = u64 };
```

`heap` and `secondary` aren't just two values referring to different memories — they also represent distinct types.

Pointers carry this information as part of their type:

```wx
// type alias just for demonstration purposes
type Pointer<Mem: Memory> = Mem::*u8;
                            ^^^
```

A `heap::*u8` therefore cannot be confused with a `secondary::*u8`. From the pointer type alone, the compiler knows exactly which linear memory the pointer belongs to.

This means that whenever we perform an operation through a pointer, the compiler doesn't merely know that we're accessing *some memory*. It knows exactly which memory is being accessed.

This distinction is going to become important for effect tracking.

```rs
fn read<Mem: Memory>(mem: Mem) [read<Mem>];

fn write<Mem: Memory>(mem: Mem) [read<Mem>, write<Mem>];

fn grow<Mem: Memory>(mem: Mem) [read<Mem>, grow<Mem>];
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

There is a limit to how precise this information is. `write<audio_memory>` doesn't tell us *where* inside that memory the function writes. It might modify one byte or the entire memory, so across an opaque call like this the safe assumption is that any previous read from `audio_memory` may have been invalidated.

This doesn't mean that the compiler has to be equally conservative when optimizing code it can actually see. Inside the module we can still perform normal alias analysis and use the language's borrowing rules to prove that two pointers cannot refer to the same location. In those cases, the optimizer can reason about individual accesses much more precisely.

So these two mechanisms complement each other. Alias analysis gives us fine-grained information while we're looking at code the compiler understands, while memory effects preserve the information we need when we cross a boundary where that analysis stops — most importantly, when calling imported functions.

We could theoretically make the effects themselves more precise by tracking individual memory regions or ranges, but that would be too much of a headache to manage properly. I think the current abstraction is more than enough to produce good, optimizable code.

As a small side note, `grow` is a separate effect because WebAssembly linear memory can grow during execution, but currently cannot shrink. The effect model simply reflects that asymmetry.

## Traits and effect polymorphism

Effects become a bit more interesting once traits and generics get involved.

So far, an effect annotation on a normal function with a body describes its exact expected effect set. Usually you don't need to write it because the compiler can infer it:

```rs
fn add(a: i32, b: i32) -> i32 { // []
    a + b
}
```

But you can still specify the effects explicitly if you want to restrict the function:

```rs
fn calculate() [trap] -> i32 {
    ...
}
```

The compiler still infers the effects from the body and compares them with the annotation. If the body produces an effect that isn't listed, that's an error. If an effect is listed but never actually appears, the compiler can report a warning.

This also means that:

```rs
fn calculate() [] -> i32 {
    ...
}
```

is a convenient way to require that a function stays pure.

Traits are slightly different. A trait method doesn't necessarily have a concrete implementation yet, so its effect annotation describes an **upper bound** rather than an exact set:

```rs
trait Validator {
    fn validate(value: i32) [throw<ValidationError>] -> bool;
}
```

An implementation is allowed to use the effects listed in this bound:

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

But it is also perfectly fine for an implementation to use fewer effects:

```rs
impl Validator for PositiveValidator {
    fn validate(value: i32) -> bool {
        value > 0
    }
}
```

`PositiveValidator::validate` is completely pure even though the trait allows it to throw a `ValidationError`.

What an implementation cannot do is introduce an effect outside of the trait's bound:

```rs
impl Validator for DebugValidator {
    fn validate(value: i32) -> bool {
        console::log(value);
        value > 0
    }
}
```

Here the implementation produces `log`, which isn't allowed by `[throw<ValidationError>]`, so the compiler rejects it.

We can think about these bounds as a small lattice of effect sets. At the bottom we have the empty set:

```text
[]
```

which allows no effects. From there, larger sets allow progressively more:

```text
[]
    ⊆ [throw<ValidationError>]
    ⊆ [throw<ValidationError>, log]
    ⊆ ...
```

And at the very top we have `[*]`, meaning that any effect is allowed:

```text
[] ⊆ [throw<ValidationError>] ⊆ [throw<ValidationError>, log] ⊆ [*]
```

`*` isn't an effect by itself. There is no function that can originate it and you can't actually call it. It's simply a special value for an effect set that means there are no restrictions on which effects may appear.

This also gives us a natural meaning for omitting the effect annotation from a trait method:

```wx
trait Task {
    fn run();
}
```

The trait doesn't place any restrictions on the effects of `run`. In that sense, omitting the annotation is equivalent to using `[*]`.

Each implementation still has its actual effects inferred normally. One implementation of `Task::run` could be pure, another could trap, and another could perform several completely different effects.

Things get more interesting once we use traits through generics.

Let's return to our validator:

```rs
fn validate_with<V: Validator>(validator: V, value: i32) -> bool {
    validator.validate(value)
}
```

It might seem like `validate_with` should immediately get `[throw<ValidationError>]`, since that's the bound declared by `Validator::validate`.

But doing that would throw away information.

At this point the compiler doesn't know which implementation of `validate` will eventually be called. Instead, it can preserve the method call itself as an abstract effect:

```text
[<V as Validator>::validate]
```

This behaves similarly to other things that depend on generic parameters. For example:

```rs
fn get_memory_size<Mem: Memory>(mem: Mem) -> Mem::Size;
```

The actual type behind `Mem::Size` isn't known until we know what `Mem` is. Effects can behave in much the same way: the actual effects behind `<V as Validator>::validate` aren't known until `V` is instantiated.

Now consider:

```rs
fn check_positive(value: i32) -> bool {
    validate_with(PositiveValidator {}, value)
}
```

Once `V` becomes `PositiveValidator`, the compiler can resolve the abstract call:

```text
<V as Validator>::validate
        ↓ V = PositiveValidator
<PositiveValidator as Validator>::validate
        ↓
[]
```

So this particular instantiation of `validate_with` is pure, and `check_positive` remains pure as well.

If we instantiate it with `StrictValidator` instead:

```text
<V as Validator>::validate
        ↓ V = StrictValidator
<StrictValidator as Validator>::validate
        ↓
[throw<ValidationError>]
```

then that instantiation may throw.

The important part is that `[throw<ValidationError>]` on the trait is only an upper bound. It tells the compiler what an implementation is *allowed* to do, but it doesn't force every implementation and every generic caller to inherit that entire effect set.

### Default implementations

Trait methods can also have default implementations, but the same upper-bound rule still applies:

```rs
trait Validator {
    fn validate(value: i32) [throw<ValidationError>] -> bool {
        true
    }
}
```

The default implementation itself is pure, which is perfectly valid:

```text
[] ⊆ [throw<ValidationError>]
```

Unlike a normal function, this shouldn't produce a warning that `throw<ValidationError>` is unused. The annotation isn't claiming that the default implementation actually throws. It describes the upper bound that this method and any implementation overriding it must respect.

The compiler still checks the default body against that bound. If the default implementation itself performs an effect outside of it, that's an error.

If we omit the annotation:

```rs
trait Validator {
    fn validate(value: i32) -> bool {
        true
    }
}
```

then the effects of this particular default implementation are inferred normally, but they don't become a restriction on future implementations. The trait method itself is unrestricted, just as if it had `[*]`.

Another interesting case appears when one trait method calls another:

```rs
trait Reporter {
    fn report(self, message: str) [log];

    fn report_error(self, message: str) [log] {
        self.report(message)
    }
}
```

The compiler doesn't know exactly which implementation of `report` will eventually be called from `report_error`, but it does know its upper bound. Since `report` cannot produce anything outside `[log]`, the compiler can prove that the default implementation of `report_error` also stays within its `[log]` bound.

Now remove that restriction:

```rs
trait Reporter {
    fn report(message: str);

    fn report_error(message: str) [log] {
        self.report(message)
    }
}
```

This is no longer safe.

`report` is unrestricted, so an implementation could perform `log`, `trap`, `throw<E>`, memory effects, or anything else. The compiler cannot prove that calling it stays within the `[log]` bound of `report_error`, so this default implementation has to be rejected.

### Dynamic dispatch

There is one final case where we cannot wait for a generic parameter to become concrete: dynamic dispatch.

With static generic dispatch, something like:

```text
<V as Validator>::validate
```

can stay unresolved until `V` is instantiated. With dynamic dispatch, the actual implementation is selected at runtime, so there is no concrete implementation whose effects the compiler can substitute.

In that case, we simply have to use the trait's upper bound.

If `Validator::validate` is bounded by `[throw<ValidationError>]`, a dynamically dispatched call has `[throw<ValidationError>]`.

If the method is unrestricted:

```rs
trait Task {
    fn run();
}
```

then a dynamically dispatched call to `run` has `[*]`.

Naturally, `[*]` then propagates through the call graph. Anything calling a function that may perform any effect may itself perform any effect as well.

This makes `[*]` fairly undesirable for code where we actually care about tracking effects. Once we dynamically call something whose behavior is completely unrestricted, there simply isn't any more precise information the compiler could safely preserve.

## Effects at public boundaries

Effects are normally inferred, but functions exposed across package boundaries require explicit effect annotations. The compiler still infers the effects from the implementation and checks them against the declared set. This makes effects part of the public API and prevents an implementation change from silently introducing new effects to its callers.

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