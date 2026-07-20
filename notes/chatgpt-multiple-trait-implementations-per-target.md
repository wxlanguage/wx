# Rust Trait Design Choices

**Date:** 2026-07-18
**Source:** [chat.openai.com](https://chatgpt.com/c/6a5bc414-b790-83eb-9d1d-19b2dde766f2)

---

### **You**

so there's this feature in rust where you can implement the same trait for the same impl target if the type arguments are different there. I'm wondering, is this actually useful feature or does it mostly creates complexity and confuses the developers? I'm just thinking maybe it would be reasonable to limit the implementation for the same method name to have only one implementation, but this doesn't exlucde the ability to make this implementation generic, so something like impl<T> Trait for Type<T> { fn foo() { ... } }  would be correct, but doing something like impl Trait for Type<i32> { fn foo() { ... } } and impl Trait for Type<u8> { fn foo() { ... } } wouldn't work with my assumption because we would have two different implementation for the same name in the trait namespace for that implementation target type. Does it make sense or I'm just confusing myself?

Asking this for my own language design. I already banned the generic traits in my langauge so I'm thinking about this second way which is similar but choses different implementation if receiver type params differ.

---

### **ChatGPT**

You're asking about a real language design tradeoff, not just a Rust feature. There are good arguments on both sides.
First, it's worth distinguishing three things Rust allows:

\`\`\`
Rustimpl<T> Trait for Vec<T> {}
\`\`\`

One implementation for all Vec<T>.

\`\`\`
Rustimpl Trait for Vec<u8> {}
impl Trait for Vec<i32> {}
\`\`\`

Different implementations depending on the concrete type arguments.

\`\`\`
Rustimpl<T: Display> Trait for Vec<T> {}
impl Trait for Vec<u8> {}
\`\`\`

This third case is where things become really interesting, because now overlap and specialization become concerns.

Why Rust allows it
The main benefit is that the behavior is genuinely different for different concrete types.
For example:

\`\`\`
Rustimpl Serialize for Vec<u8> {
    // binary blob
}

impl<T: Serialize> Serialize for Vec<T> {
    // serialize each element
}
\`\`\`

Vec<u8> is often treated as raw bytes rather than "a vector containing numbers."
Another example:

\`\`\`
Rustimpl Display for Matrix<f32> {}
impl Display for Matrix<f64> {}
\`\`\`

Maybe the formatting algorithms differ.
Or

\`\`\`
Rustimpl Hash for Id<User> {}
impl Hash for Id<Post> {}
\`\`\`

where Id<T> is a phantom-type wrapper.
These aren't just optimizations—they represent genuinely different semantics.

The downside
It definitely increases complexity.
A reader now has to ask

Which implementation am I actually calling?

instead of simply

What does Trait do for Vec<T>?

Rust has coherence rules specifically because unrestricted multiple implementations become very difficult to reason about.
Specialization makes this even harder.

Your proposal
Your rule is essentially

For every (Trait, TypeConstructor) pair there is exactly one implementation.

So if

\`\`\`
Type<T>
\`\`\`

exists, then only

\`\`\`
impl<T> Trait for Type<T>
\`\`\`

is legal.
These would be illegal:

\`\`\`
impl Trait for Type<u8>
impl Trait for Type<i32>
\`\`\`

because they would both belong to the same type constructor.
This is a perfectly coherent rule.

Benefits
This gives several nice properties.
1. Easy lookup
If I know

\`\`\`
foo.bar()
\`\`\`

I only need to find

\`\`\`
impl Trait for Foo<T>
\`\`\`

There is never another candidate.

2. Simpler compiler
No overlap checking.
No specialization.
No "most specific implementation."
No coherence headaches.

3. Stable semantics
Changing

\`\`\`
Type<u8>
\`\`\`

into

\`\`\`
Type<i32>
\`\`\`

doesn't silently switch to an entirely different implementation.
The implementation itself may branch internally,

\`\`\`
if T == u8 {
    ...
}
\`\`\`

(or whatever equivalent your language provides),
but there is still only one definition.

The cost
You lose expressive power.
Suppose you're implementing

\`\`\`
ToBytes
\`\`\`

For

\`\`\`
Buffer<T>
\`\`\`

Most types should serialize element-by-element.
But

\`\`\`
Buffer<u8>
\`\`\`

should just return its memory directly.
Without specialization you end up with

\`\`\`
fn toBytes() {
    if T == u8 {
        ...
    } else {
        ...
    }
}
\`\`\`

or

\`\`\`
match type(T)
\`\`\`

or some compile-time conditional.
Now one implementation contains many unrelated cases.
Sometimes that's acceptable.
Sometimes it becomes ugly.

Since you already banned generic traits
This changes the equation significantly.
If traits themselves cannot be generic,
you're already aiming for a simpler trait system.
In that context your proposal feels much more consistent.
Your philosophy becomes

every trait has one implementation per type constructor

generic parameters don't affect implementation lookup

type parameters can still be inspected inside the implementation if necessary

That's actually a fairly elegant model.

An interesting middle ground
Some languages effectively distinguish between

\`\`\`
Type<T>
\`\`\`

(the family)
and

\`\`\`
Type<u8>
\`\`\`

(a completely separate concrete type).
Rust treats every instantiation as a distinct type.
Your proposal instead treats them as sharing one implementation namespace.
That's a valid design choice.

One question I'd ask
How often do you expect programmers to want different behavior versus different algorithms?
Different algorithms can usually live inside one generic implementation.
Different semantics are harder.
For example:

\`\`\`
Display for Result<T>
\`\`\`

versus

\`\`\`
Display for Result<Error>
\`\`\`

Those arguably mean different things.
If your language doesn't support separate implementations, users must encode those differences inside one implementation.
Whether that's acceptable depends on your goals.

My impression
If your goal is a language that's easy to understand, predictable, and has a simple implementation model, your rule makes a lot of sense. It establishes a strong invariant:

For any trait and type constructor, there is exactly one implementation.

That invariant is easy to explain, easy to implement, and easy for users to reason about.
The main thing you're giving up is the ability to express that certain instantiations have fundamentally different behavior. Rust pays quite a bit of complexity (coherence rules, orphan rules, specialization discussions, overlap checking) to support that flexibility. If your language values simplicity over maximal expressiveness, it's a reasonable tradeoff.
One thing to think about is whether you'll eventually want a form of compile-time type matching inside a generic implementation (for example, if type(T) == u8 or a compile-time match type(T)). That preserves your "one implementation" rule while still allowing optimized or specialized code paths where needed, without introducing multiple implementations into the trait namespace.

---

### **You**

but can't you just wrap the CpuTensor(Tensor<Cpu>) and implement methods on it?

---

### **ChatGPT**

Exactly. That's one of the strongest arguments against allowing multiple implementations based solely on generic arguments.
Take the Rust example:

\`\`\`
Ruststruct Tensor<B> {
    ...
}

struct Cpu;
struct Gpu;

impl Compute for Tensor<Cpu> {
    ...
}

impl Compute for Tensor<Gpu> {
    ...
}
\`\`\`

You could instead write

\`\`\`
Ruststruct CpuTensor(Tensor<Cpu>);
struct GpuTensor(Tensor<Gpu>);

impl Compute for CpuTensor {
    ...
}

impl Compute for GpuTensor {
    ...
}
\`\`\`

or even

\`\`\`
Ruststruct CpuTensor { ... }
struct GpuTensor { ... }
\`\`\`

without exposing Tensor<B> at all.
The semantics are arguably clearer:

CpuTensor is a CPU tensor.

GpuTensor is a GPU tensor.

instead of

Tensor<Cpu> magically behaving differently from Tensor<Gpu>.

The same applies to many of the examples I gave.
Instead of

\`\`\`
RustQuantity<Meter>
Quantity<Second>
\`\`\`

you could define

\`\`\`
Ruststruct MeterQuantity(Quantity<Meter>);
struct SecondQuantity(Quantity<Second>);
\`\`\`

or even

\`\`\`
Ruststruct Meters(f64);
struct Seconds(f64);
\`\`\`

if they really are conceptually different.

Why does Rust still allow it?
Mostly because it avoids boilerplate.
Suppose you have

\`\`\`
Ruststruct Handle<T> {
    id: u64,
}
\`\`\`

and 30 marker types:

\`\`\`
RustHandle<User>
Handle<Post>
Handle<Comment>
...
\`\`\`

Creating 30 wrapper structs just to implement Display differently is tedious.
Rust lets you reuse the generic structure while varying behavior.
So it's largely an ergonomic feature.

The deeper language-design question
You're essentially deciding whether a generic instantiation like

\`\`\`
Tensor<Cpu>
\`\`\`

is merely a parameterization of one type, or whether it's allowed to behave as if it were a completely different type.
Rust says:

Every monomorphized type is its own concrete type.

Your proposal says:

These are all instances of the same type constructor, so they should share the same trait implementation.

That's a perfectly coherent philosophy.

One caveat
There is one place where wrappers are genuinely less ergonomic: third-party types.
Imagine a library provides

\`\`\`
RustTensor<T>
\`\`\`

You'd like Tensor<Cpu> to implement Compute differently from Tensor<Gpu>.
If your language forbids multiple implementations, you now have to define:

\`\`\`
struct CpuTensor(Tensor<Cpu>);
struct GpuTensor(Tensor<Gpu>);
\`\`\`

and convert between them.
That's extra ceremony.
Rust lets you express that distinction directly on the original type.
Whether that's worth the added complexity is subjective.

Personally, I think your proposed rule has a nice conceptual invariant:

Traits describe the behavior of a type constructor, not of individual type arguments.

It's simple to teach, simple to implement, and makes trait lookup almost trivial. When a particular instantiation truly deserves different behavior, introducing a distinct named type makes that distinction explicit rather than implicit in trait resolution. That's a very defensible design choice for a language that prioritizes simplicity and predictability.

---

### **You**

let me tell you a bit about my project and you tell me (but be honest) whether it makes sense to make such limitation in the langauge (at least for now)

<h1 align="center">
WX - Web Assembly Expressive Language
</h1>

WX is a Rust-inspired language that compiles directly to WebAssembly. It stays close to the WASM spec instead of hiding it, so the code you write maps predictably onto the module you get — no hidden runtime, no GC, no surprises.

This project is part of my bachelor's thesis exploring what it takes to build a full WASM compiler from scratch. It's still early — expect rough edges.

---

### **ChatGPT**

I actually think it makes more sense for your language than it does for Rust.
Not because the limitation is universally good, but because it matches the goals you've stated.
Let's break down the goals from your README.

Rust-inspired

This doesn't mean you have to copy every feature Rust has. Rust's trait system is one of its most complicated pieces, and many of those complexities exist because Rust has to support an enormous ecosystem with backward compatibility and highly expressive generic programming.

Compiles directly to WebAssembly

This is important.
You're not trying to build "Rust 2.0." You're building a language whose primary abstraction level is close to WASM.
That suggests valuing:

predictable code generation,

simple type checking,

easy-to-understand dispatch,

minimal compiler magic.

Having exactly one implementation per (Trait, TypeConstructor) fits those goals well.

Stays close to the WASM spec

This is probably the strongest argument.
WASM itself doesn't know anything about generic specialization.
If your language says

\`\`\`
Vec<T>
\`\`\`

has exactly one implementation of Clone, then the compiler can monomorphize that implementation for each T.
Very predictable.
If instead you allow

\`\`\`
Clone for Vec<u8>
Clone for Vec<i32>
Clone for Vec<f32>
\`\`\`

then trait resolution depends on concrete type arguments, which is another layer of language semantics that doesn't correspond to anything in WASM.

No hidden runtime, no surprises

This is exactly where I think your restriction shines.
Imagine reading

\`\`\`
foo.clone()
\`\`\`

If I know foo has type

\`\`\`
Vec<T>
\`\`\`

I immediately know which implementation exists.
I don't have to wonder

"Is there a special implementation for u8?"

or

"Did another crate specialize this?"

That predictability is valuable.

It also simplifies your compiler significantly
You eliminate entire categories of problems.
No overlap checking.
No specialization.
No ambiguity.
No "most specific implementation."
No future coherence headaches.
Trait lookup becomes almost trivial.
For a bachelor's thesis, that's a huge win.

What are you actually losing?
This is the important question.
Suppose someone wants

\`\`\`
Tensor<Cpu>
\`\`\`

and

\`\`\`
Tensor<Gpu>
\`\`\`

to behave differently.
They can write

\`\`\`
CpuTensor
GpuTensor
\`\`\`

instead.
Is that really terrible?
I don't think so.
It forces programmers to explicitly acknowledge that these are different concepts.

The biggest downside
The biggest thing you're sacrificing isn't expressiveness—it's ergonomics.
Imagine a library with

\`\`\`
Image<PixelFormat>
\`\`\`

There are ten pixel formats.
Without specialization, users might end up writing

\`\`\`
RgbImage(Image<Rgb>)
GrayImage(Image<Gray>)
RgbaImage(Image<Rgba>)
...
\`\`\`

That's boilerplate.
Rust lets you avoid it.
Whether that's worth the added complexity depends on your priorities.

One thing I'd recommend
If you make this restriction, I'd make it a deliberate language principle, not "something we haven't implemented yet."
Something like:

A trait has exactly one implementation for each type constructor. Generic arguments do not participate in implementation selection.

That's a clean rule.
If you later decide you need specialization, you can always relax the rule.
Going the other direction is much harder.

One caveat
I wouldn't justify it by saying "because wrappers can always be used."
That's true, but it's not the strongest argument.
The stronger argument is:

Trait implementations describe the behavior of a type constructor, not individual instantiations.

Wrappers are simply the escape hatch when an instantiation genuinely represents a different abstraction.

Overall
Given your project's goals, I think this restriction is well aligned with the language's philosophy. It makes the compiler simpler, trait resolution more predictable, and the mental model easier to explain—all valuable qualities for a language that emphasizes being close to WebAssembly and avoiding hidden behavior.
The only thing I'd be careful about is how you communicate it. If you present it as "we don't support this yet," users will expect it to arrive eventually. If instead you present it as a conscious design decision rooted in simplicity and predictability, it becomes part of the language's identity. Even if you later revisit the decision, starting from a small, coherent core is often the better path for a new language.

---

### **You**

how would this rule work in practice? let's say developer wants to impl Trait for Vec<u8> and then he also wants to implement it for impl Trait for Vec<u32>. What should I report, how to handle this?

---

### **ChatGPT**

I think you should lean into the rule instead of trying to make it feel like an arbitrary restriction. The error should explain why it's illegal.
For example, suppose the user writes:

\`\`\`
wximpl Display for Vec<u8> { ... }

impl Display for Vec<u32> { ... }
\`\`\`

The compiler should reject the second one because it sees that there is already a Display implementation whose receiver's type constructor is Vec.
Something along these lines:

\`\`\`
error: duplicate trait implementation

\`Display\` is already implemented for the type constructor \`Vec<\_>\`.

WX allows at most one implementation of a trait for each type constructor.
Generic arguments do not participate in trait selection.

Consider:
  - merging both implementations into a single generic implementation
  - introducing distinct wrapper types if the behaviors are semantically different
\`\`\`

Notice it doesn't even mention Vec<u8> vs Vec<u32>. It talks about the type constructor.

How I'd implement it
When you parse

\`\`\`
wximpl Trait for Type<Args...>
\`\`\`

you normalize the receiver into something like

\`\`\`
(TypeConstructor = Type, Trait = Trait)
\`\`\`

So internally

\`\`\`
Vec<u8>
Vec<u32>
Vec<T>
\`\`\`

all become

\`\`\`
(Trait = Display, Constructor = Vec)
\`\`\`

meaning they're duplicates.

Even nicer: distinguish between families and instances
You could explain it in the language spec like this:

Trait implementations are attached to generic type families, not to individual generic instantiations.

Examples:

\`\`\`
wxVec<T>
Vec<u8>
Vec<u32>
\`\`\`

are all members of the same family.
Only one implementation may exist.

What about impl<T>?
I'd still allow

\`\`\`
wximpl<T> Display for Vec<T> {
    ...
}
\`\`\`

because that's just saying

"The Vec family implements Display."

The T is only available inside the implementation.

If someone really wants different behavior
Then the compiler should almost guide them:

\`\`\`
wxstruct ByteVec(Vec<u8>);
struct IntVec(Vec<u32>);

impl Display for ByteVec { ... }
impl Display for IntVec { ... }
\`\`\`

Notice how the types now have different names.

One thing I would not do
I wouldn't special-case concrete types.
Don't say

"Only one concrete implementation is allowed."

Say

"Traits are implemented for type constructors."

That's a much cleaner mental model.

I actually have one suggestion that might make this design even more elegant.
Instead of thinking of this as "ignoring generic arguments during trait lookup," define the language so that generic parameters are never part of trait identity in the first place. Formally, the key for an implementation could be:

\`\`\`
(TraitId, TypeConstructorId)
\`\`\`

—not—

\`\`\`
(TraitId, ConcreteType)
\`\`\`

That becomes a fundamental property of the language rather than a restriction. It also means your trait lookup algorithm is extremely simple: strip the generic arguments from the receiver type, find the unique implementation for that constructor, instantiate it with the current type arguments, and you're done. That's a very clean model, especially for a language whose goals are predictability and a close mapping to WebAssembly.

---

trait Iterator {
    type Item;
    fn next(&self) -> Option<Item>;
}

[1, 2, 3].(Iterator::next).(Option::unwrap)