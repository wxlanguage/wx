Hi! I'm building a programming language and compiler specifically for WebAssembly called WX. In this post I want to explain an effect tracking system I've been designing for it: what problems it tries to solve, how effects are represented in the compiler, and what benefits this information can give both developers and the optimizer.

WX is heavily inspired by Rust in its syntax and many of its concepts, but there are some important differences. One of the main goals of the language is to stay relatively close to WebAssembly and expose its features directly, while still providing convenient high-level abstractions on top.

Before getting into effects, there is one important property of WebAssembly we need to understand.

WebAssembly was designed as a platform for sandboxed code execution. A module doesn't automatically have access to things outside of its sandbox. If it wants to communicate with the outside world, that functionality has to be explicitly provided by the host.

For example, WebAssembly itself doesn't have a \`print\` function. If we want our module to print something, the host needs to provide that functionality as an import.

In WX that could look like this:

\`\`\`rust

import "console" as console {

    fn log(n: i32) [log];

}

fn main() {

    console::log(123);

}

export {

    main,

}

\`\`\`

You can think about a WebAssembly module almost like a function itself. The host provides its imports, while the module exposes exports that the host can call:

\`\`\`text

                 +--------------------------+

                 |                          |

                 |                          |

                 +----.                .----+

                       \              /      \\

  [HOST PLUG] --------> )    WASM    (        ) ---> [HOST SOCKET]

 (console::log)        /    MODULE    \      /        (main)

                 +----'                '----+

                 |                          |

                 |                          |

                 +--------------------------+

\`\`\`

The host instantiates the module with the required imports and can then call its exported functions.

This sandbox boundary is going to become important for effects. An imported function such as \`console::log\` can do something observable outside of the WebAssembly module, while its implementation isn't even available for our compiler to inspect.

Now let's go back to our \`main\` function and ask a simple question: **\*\*what does this function actually do?\*\***

A normal function signature describes its inputs and outputs. It tells us which values go in and which value comes back, but it doesn't tell us everything that might happen while the function is executing.

For example, consider:

\`\`\`rust

fn do\_something() -> () {

    console::log(123);

}

\`\`\`

Looking only at \`fn() -> ()\`, we might think there isn't much interesting about this function. It takes nothing and returns nothing.

But removing the call would obviously change the behaviour of the program because it prints something to the outside world.

This information matters to the optimizer. If the result of a computation isn't used, the compiler would like to remove it when possible. But before doing that, it needs to know whether executing that computation can have some observable effect.

It would also be useful information for us as developers. A function signature tells us what values a function exchanges with us, so why shouldn't it also tell us what else the function might do?

This is where effects come in.

In WX, a function signature can contain an effect set after its arguments:

\`\`\`rust

import "console" as console {

    fn log(n: i32) [log] -> ();

}

\`\`\`

The square brackets describe the effects that may happen when the function is executed. Here, calling \`console::log\` has the \`log\` effect.

But this immediately raises another question: **\*\*what exactly is \`log\`? Where does an effect come from in the first place?\*\***

**## Effect origin and tracking**

The one big problem in this model is: how do we even originate an effect? What is an effect from the compiler's perspective?

Many languages with effect systems introduce a separate vocabulary for effects. You might have effects such as \`IO\`, \`Exception\`, \`State\`, or user-defined effect operations. Functions can then declare that performing some operation introduces one of these effects.

But why do we need a separate concept for effects at all? We already have functions describing operations that can happen in our program. What if an effect could simply be a function?

This is essentially what WX does. A function with a body doesn't need to explicitly declare its effects — the compiler can infer them by looking at what happens inside the body. Effects can still be annotated explicitly, in which case the annotation acts as an **upper bound**: every effect inferred from the function body must be contained within the declared set.

For a function without a body there is nothing to inspect, so the compiler cannot infer a more precise set. In that case, the declared bound is also the function's effective effect summary.

A bodyless function can declare no effects at all:

\`\`\`rust

fn some\_intrinsic() [] -> i32;

\`\`\`

It can say that calling it may perform some already existing effect:

\`\`\`rust

fn i32\_div(a: i32, b: i32) [trap] -> i32;

\`\`\`

Or it can reference itself, effectively becoming the origin of a new effect:

\`\`\`rust

fn trap() [trap] -> never;

\`\`\`

There is no separate \`effect trap\` declaration here. \`trap\` is just a function, and putting itself into its own effect set tells the compiler that this is where the \`trap\` effect originates.

In practice there are two main places where such bodyless functions come from in WX: imported functions, whose implementation lives outside the WebAssembly module, and compiler intrinsics representing WebAssembly instructions.

**### How effects compose**

Once an effect originates somewhere, it needs to propagate through everything that can reach it.

The rule here is fairly simple: the **inferred effects** of a function are the union of the effects that can happen inside its body.

Suppose we have two effectful operations:

\`\`\`rust

fn foo() [foo];

fn bar() [bar];

\`\`\`

and call both of them:

\`\`\`rust

fn do\_something() {

    foo();

    bar();

}

\`\`\`

The compiler can infer the resulting effect set:

\`\`\`rust

fn do\_something() [foo, bar] {

    // ...

}

\`\`\`

Effects form a set, so duplicates don't matter. Calling \`foo()\` once or ten times still only adds \`foo\` once.

The same process continues transitively through the call graph. If another function calls \`do\_something\`, it inherits both \`foo\` and \`bar\` unless something handles those effects before they escape.

This means that for ordinary functions we don't have to manually propagate effects through every layer of the program. The compiler already knows which operations a function performs and which other functions it calls, so it can infer the resulting set automatically.

**### Tracking traps**

Let's look at a real example.

One of the most basic relevant WebAssembly instructions is \`unreachable\`, which unconditionally traps when executed. For clarity, WX exposes this operation as \`trap\`:

\`\`\`rust

fn trap() [trap] -> never;

\`\`\`

The \`never\` return type tells us that normal control flow cannot continue after this call. Separately, \`[trap]\` tells us why this computation is effectful: executing it may terminate the current WebAssembly execution with a trap.

When we call \`trap\` inside another function:

\`\`\`rust

fn main() {

    trap();

}

\`\`\`

the compiler can infer something equivalent to:

\`\`\`rust

fn main() [trap] -> never;

\`\`\`

Nothing special happened here specifically because this was a trap. We just applied the composition rule from above: \`main\` calls something with the \`[trap]\` effect, so \`trap\` becomes part of \`main\`'s effect set as well.

Now consider integer division. WebAssembly integer division traps when the divisor is zero, so WX can describe the intrinsic like this:

\`\`\`rust

fn i32\_div(a: i32, b: i32) [trap] -> i32;

\`\`\`

Notice that this is \`[trap]\`, not \`[i32\_div]\`.

Division itself isn't an effect we are interested in tracking. It's an ordinary computation which happens to be capable of reaching the already established \`trap\` effect.

This distinction is important: a bodyless function doesn't necessarily introduce a new effect. Its declared effect bound describes what effects executing that operation may ultimately perform. Because there is no body from which to infer anything more precise, that bound is also used as the function's effect summary. Self-reference is simply the mechanism for saying that the operation itself originates a new effect.

For this model to work, the compiler needs to eventually represent every potentially effectful operation through something whose effects it knows. This doesn't mean that everything has to *\*look\** like a function call in source code. Operators and other syntax can still provide the usual abstractions, as long as they eventually lower to functions whose effects the compiler can track.

Operators in WX work through traits, similarly to Rust. For example, integer division eventually resolves to:

\`\`\`rust

impl Div for i32 {

    fn div(self, other: Self) -> Self {

        i32\_div(self, other)

    }

}

\`\`\`

So when you write:

\`\`\`rust

a / b

\`\`\`

the compiler can follow that operation down to \`i32\_div\`, which we already know has the \`[trap]\` effect. The abstraction doesn't hide the effect from the compiler.

Assignment variants work the same way. Unlike Rust, WX doesn't have a separate \`DivAssign\` trait: \`a /= b\` is syntax sugar derived from \`Div\`, so it ultimately carries the same effects.

**## Exception handling**

So far our effect system isn't particularly exciting. We can track that an operation might trap, propagate that information through arbitrary layers of functions, and then... that's about it. A WebAssembly trap cannot be caught by ordinary module code, so once the \`trap\` effect appears there isn't much we can do with it.

Exceptions give us a more interesting example because they can be handled.

The basic idea is similar to \`trap\`: somewhere in the program we perform an operation which interrupts normal control flow. The difference is that an exception can be caught before it escapes, allowing us to recover and continue execution.

This also gives us our first example of a parameterized effect.

WebAssembly exceptions are represented using tags. In WX, a tag declaration looks like this:

\`\`\`rust

tag ApplicationError(status: ErrorStatus) -> never;

\`\`\`

Tags automatically implement the \`Tag\` trait:

\`\`\`rust

trait Tag {

    type Result;

}

\`\`\`

An exception is a tag whose result is \`never\`:

\`\`\`rust

trait Exception: Tag where { Result = never } {

    fn throw(self) -> never {

        throw(self)

    }

}

\`\`\`

The underlying \`throw\` operation can then be represented as another bodyless intrinsic:

\`\`\`rust

fn throw\<E: Exception>(exception: E) [throw\<E>] -> never;

\`\`\`

This looks very similar to our earlier \`trap\`:

\`\`\`rust

fn trap() [trap] -> never;

\`\`\`

but there is one important difference. \`throw\` is generic, and the instantiated generic argument becomes part of the effect.

So these are distinct effects:

\`\`\`rust

throw\<ApplicationError>

throw\<ConnectionError>

\`\`\`

This means we don't merely know that a function "might throw". We know exactly which exception types it might throw.

For example:

\`\`\`rust

fn handler() {

    if something() {

        ApplicationError(ErrorStatus::Internal).throw();

    }

}

\`\`\`

The compiler can infer:

\`\`\`rust

fn handler() [throw\<ApplicationError>] {

    // ...

}

\`\`\`

And just like before, if \`handler\` calls another function which can throw \`ConnectionError\`, the effects compose:

\`\`\`rust

[throw\<ApplicationError>, throw\<ConnectionError>]

\`\`\`

**### Handling effects**

This is where exceptions become more interesting than our previous examples.

So far effects could only originate and propagate outward. A \`catch\` gives us a way to handle an effect before it escapes:

\`\`\`rust

fn main() {

    local result = handler() catch {

        ApplicationError(status) -> {

            fallback()

        },

    };

}

\`\`\`

If \`handler()\` has:

\`\`\`rust

[throw\<ApplicationError>]

\`\`\`

and the \`catch\` handles \`ApplicationError\`, then that effect no longer propagates beyond the \`catch\`.

You can think of it as transforming the effect set of the expression:

\`\`\`text

handler()

    [throw\<ApplicationError>]

        catch ApplicationError

    []

\`\`\`

If the expression can perform other effects, however, those remain:

\`\`\`text

[log, throw\<ApplicationError>, throw\<ConnectionError>]

        catch ApplicationError

[log, throw\<ConnectionError>]

\`\`\`

So handling an effect doesn't make the whole expression pure. It only removes the effects which were actually handled.

Because the compiler knows the exact set of exception effects that can reach a \`catch\`, WX can also check whether the handler is exhaustive. You can explicitly handle every possible exception:

\`\`\`rust

local result = handler() catch {

    ApplicationError(status) -> ...,

    ConnectionError(code) -> ...,

};

\`\`\`

or use a \`\_\` fallback when you intentionally don't care which exception was thrown:

\`\`\`rust

local result = handler() catch {

    ApplicationError(status) -> ...,

    \_ -> fallback(),

};

\`\`\`

In that sense, \`catch\` is similar to a \`match\`: instead of exhaustively matching possible values, we're exhaustively handling possible exceptional exits from a computation.

This gives us the other half of effect tracking. Function calls and operations add and compose effects, while constructs that understand a particular effect can handle it and prevent it from propagating further.

**## Memory effects**

Before we continue, I need to briefly explain how memory works in WX, since it's somewhat different from what you might be used to in other languages.

WebAssembly modules aren't required to have linear memory at all. A module can simply export functions that operate on values directly. When you do need memory, however, it has to be explicitly declared. In WX, that looks like this:

\`\`\`wx

memory heap: Memory where { Size = u32 };

\`\`\`

\`heap\` is the name of the memory and can be referenced elsewhere in the program. The \`Memory\` trait describes the memory itself, while \`Size\` tells us the size of its addresses. In this case, pointers into \`heap\` use 32-bit addresses.

More importantly, every memory declaration creates its own unique type. If we declare two memories:

\`\`\`wx

memory heap: Memory where { Size = u32 };

memory secondary: Memory where { Size = u64 };

\`\`\`

\`heap\` and \`secondary\` aren't just two values referring to different memories — they also represent distinct types.

Pointers carry this information as part of their type:

\`\`\`wx

// type alias just for demonstration purposes

type Pointer\<Mem: Memory> = Mem::\*u8;

                            ^^^

\`\`\`

A \`heap::\*u8\` therefore cannot be confused with a \`secondary::\*u8\`. From the pointer type alone, the compiler knows exactly which linear memory the pointer belongs to.

This means that whenever we perform an operation through a pointer, the compiler doesn't merely know that we're accessing *\*some memory\**. It knows exactly which memory is being accessed.

This distinction is going to become important for effect tracking.

\`\`\`rs

fn read\<Mem: Memory>(mem: Mem) [read\<Mem>];

fn write\<Mem: Memory>(mem: Mem) [read\<Mem>, write\<Mem>];

fn grow\<Mem: Memory>(mem: Mem) [read\<Mem>, grow\<Mem>];

\`\`\`

Just like \`throw\<E>\` from the previous example, these effects are parameterized by a type. Since every memory has its own unique type, \`read\<heap>\` and \`read\<secondary>\` are two distinct effects.

What's slightly unusual here is that these functions don't actually read or write anything themselves. They don't even take a pointer. The memory instance is effectively just a zero-sized value identifying a particular memory, so these calls don't need to produce any runtime code.

But that's the whole idea.

There are many different operations that can access memory. WebAssembly itself has a whole set of load, store and memory instructions, while imported host functions can access a module's memory as well. Giving every one of those operations its own effect would preserve information we don't really care about.

What we usually want to know is much simpler: **\*\*which memory can this computation read or modify?\*\***

So all operations that read \`heap\` can share \`read\<heap>\`, while operations that may modify it share \`write\<heap>\`.

This information is also useful for the optimizer. Consider an imported function:

\`\`\`rs

fn process\_audio(...) [write\<audio\_memory>];

\`\`\`

The compiler can't inspect its implementation, but it still knows something very important: after calling it, any previously loaded value from \`audio\_memory\` might be stale.

At the same time, the effect says nothing about other memories. If we also have a separate \`heap\`, the compiler knows that \`process\_audio\` cannot modify it, so values loaded from \`heap\` can still be safely reused.

There is a limit to how precise this information is. \`write\<audio\_memory>\` doesn't tell us *\*where\** inside that memory the function writes. It might modify one byte or the entire memory, so across an opaque call like this the safe assumption is that any previous read from \`audio\_memory\` may have been invalidated.

This doesn't mean that the compiler has to be equally conservative when optimizing code it can actually see. Inside the module we can still perform normal alias analysis and use the language's borrowing rules to prove that two pointers cannot refer to the same location. In those cases, the optimizer can reason about individual accesses much more precisely.

So these two mechanisms complement each other. Alias analysis gives us fine-grained information while we're looking at code the compiler understands, while memory effects preserve the information we need when we cross a boundary where that analysis stops — most importantly, when calling imported functions.

We could theoretically make the effects themselves more precise by tracking individual memory regions or ranges, but that would be too much of a headache to manage properly. I think the current abstraction is more than enough to produce good, optimizable code.

As a small side note, \`grow\` is a separate effect because WebAssembly linear memory can grow during execution, but currently cannot shrink. The effect model simply reflects that asymmetry.

**## Effect bounds and polymorphism

Earlier we established that an explicit effect annotation is an **upper bound**, not necessarily the exact effects of a function. So far this distinction hasn't mattered much: ordinary functions usually had their effects inferred, while bodyless functions gave the compiler no more precise information to work with. Once effects become part of the type system, however, the distinction becomes important.

Consider:

```rs
fn calculate() [trap] -> i32 {
    100 / get_value()
}
```

The compiler still infers the effects of the body and checks them against the annotation:

```text
inferred effects = [trap]
declared bound   = [trap]

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
inferred effects ⊆ declared bound
```

A broader bound is sound but less precise. When the compiler knows both the implementation and its annotation, it can warn if the annotation unnecessarily includes effects that never appear. Narrowing such a bound gives callers a stronger guarantee, but the broader annotation is not incorrect.

This also gives `[]` a useful meaning: because the only subset of the empty set is itself, annotating a function with `[]` requires it to remain pure.

At the other extreme, `[*]` represents an unrestricted bound. `*` is not an effect that can originate from a function; it is simply the top of the effect-set lattice, meaning that any effect is permitted.

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

The second implementation is pure, and `[] ⊆ [throw<ValidationError>]`, so it satisfies the trait just as well. An implementation that introduces `log`, however, would be rejected because `[log]` is not a subset of the declared bound.

There is therefore no special meaning attached to an effect annotation inside a trait. The interesting difference is simply that a bodyless trait method has no implementation from which the compiler could infer a more precise set. At the trait boundary, its declared bound is the best effect summary available.

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

When `V` becomes concrete, this can be resolved to the effects of the actual implementation:

```text
<V as Validator>::validate
        ↓ V = PositiveValidator
<PositiveValidator as Validator>::validate
        ↓
[]
```

while `StrictValidator` resolves to `[throw<ValidationError>]`.

The trait bound still guarantees that every possible implementation stays within `[throw<ValidationError>]`; static generic dispatch simply lets the compiler retain a more precise set whenever the implementation becomes known.

### Default implementations

Default implementations follow the same rule:

```rs
trait Validator {
    fn validate(value: i32) [throw<ValidationError>] -> bool {
        true
    }
}
```

The default body is inferred as `[]`, which fits inside the declared bound. Unlike an annotation on an ordinary concrete function, however, there is little reason to warn that `throw<ValidationError>` is unused here: the bound also constrains implementations that may override the default.

Default methods can call other bounded trait methods as well:

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

In that case the declared trait bound becomes the best effect summary available. A dynamically dispatched call to a method bounded by `[throw<ValidationError>]` contributes that whole set, even if the implementation selected at runtime happens to be pure. An unrestricted method similarly contributes `[*]`.

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

The compiler originally knew that `get_number` was pure. Through `f`, however, all we know is the bound encoded in its type, so `f()` must be conservatively treated as `[trap]`.

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

`E` represents an entire effect set rather than one individual effect. Depending on the callback it might become `[]`, `[trap]`, `[log]`, or any other set.

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

Here `[log, E]` means `{log} ∪ E`. Multiple parameters work the same way:

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

## Effects at public boundaries

For private functions, inference is usually enough. If the implementation is available, the compiler can determine its actual effect set directly from the body.

Across a package boundary, however, callers need a stable contract. Public functions therefore require an explicit effect bound:

```rs
pub fn calculate(value: i32) [trap] -> i32 {
    ...
}
```

The implementation is still inferred and checked using the same rule:

```text
inferred effects ⊆ [trap]
```

The implementation may currently be pure and later change to one that can trap without changing the public API. Both implementations satisfy the same bound that callers already had to assume.

Introducing `log`, on the other hand, would violate the contract because `[log] ⊄ [trap]`. The public annotation would have to be explicitly widened before such an implementation could be accepted.

This separates two pieces of information:

```text
inferred effects    what this particular implementation is known to do
declared bound      what callers are allowed to assume
```

Internally, the compiler can preserve the more precise inferred set wherever the implementation is available. Across a package boundary, callers rely on the declared bound instead. This prevents implementation changes from silently changing the effects visible to downstream packages.

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


## Global variables**

Global variables follow the same general model as the other low-level WebAssembly features we've looked at so far.

At the bottom we have a couple of compiler intrinsics that directly represent WebAssembly's global instructions and act as effect sources:

\`\`\`rs

fn global\_get\<G: Global>(g: G) [global\_get\<G>] -> G::Value;

fn global\_set\<G: GlobalMut>(g: G, value: G::Value) [global\_set\<G>];

\`\`\`

On top of those, the standard library exposes separate traits for immutable and mutable globals:

\`\`\`rs

trait Global {

    type Value: Copy;

    fn get(self) -> Self::Value {

        global\_get(self)

    }

}

trait GlobalMut: Global {

    fn set(self, value: Self::Value) {

        global\_set(self, value)

    }

}

\`\`\`

A global can then be declared like any other item:

\`\`\`rs

global x: GlobalMut where { Value = i32 } = 0;

\`\`\`

and accessed explicitly through \`get\` and \`set\`:

\`\`\`rs

fn main() { // [global\_get\<x>, global\_set\<x>]

    x.set(x.get() + 1);

}

\`\`\`

Just like with memories, every global has its own identity, so \`global\_get\<x>\` and \`global\_get\<y>\` are different effects. This gives the compiler precise information about which particular global a function may observe or modify.

One deliberate difference from local variables is that globals have to be accessed through \`get()\` and \`set()\`. WX doesn't implement ordinary arithmetic or assignment operators directly on global values.

For example, something like this is intentionally not supported:

\`\`\`rs

x += 1;

\`\`\`

Allowing that would mean otherwise simple primitive operators such as \`Add\`, or assignment syntax itself, could silently introduce global effects. I want primitive operations to stay as predictable as possible, so global access remains explicit in the source code.

The slightly more verbose version:

\`\`\`rs

x.set(x.get() + 1);

\`\`\`

makes it immediately visible that we're reading and then modifying global state. It also maps very directly to the underlying WebAssembly operations.

There is one more restriction: WebAssembly globals in WX can only contain primitive values. You cannot store an aggregate such as a struct or tuple directly in a global.

If you need global aggregate state, you can instead place the value in memory and store a pointer to it:

\`\`\`rs

global state: GlobalMut where { Value = heap::&mut State } = ...;

\`\`\`

A pointer is itself a primitive value, so it can be stored in a global normally.

This restriction also keeps importing and exporting globals simple. If aggregate globals were supported directly, WX would need to define an ABI for how those aggregates are represented across the WebAssembly module boundary, including how they are laid out and how imported or exported globals map to their underlying representation.

By keeping globals limited to values that WebAssembly itself can represent directly, imports and exports stay predictable and don't require any hidden transformations.

I also quite like the explicit \`get()\` and \`set()\` syntax as a side effect of this design. Global state stands out visually from ordinary local computation, and the corresponding effects are equally explicit to the compiler. The exact API may still change, but I think the underlying model is useful.