# Named Invocation and Struct Constructors

## Status

Design proposal for WX. This document defines a uniform model for named function calls, tuple-struct construction, and record-struct construction. It is intended to guide parser, type-checker, and lowering implementation.

## Motivation

WX already models the constructor of a tuple struct as a compiler-generated function in the value namespace:

```wx
struct Point(i32, i32);

Point : fn(i32, i32) -> Point
```

The type name `Point` therefore occupies the type namespace, while its constructor occupies the value namespace. A value is constructed with an ordinary positional call:

```wx
local point = Point(5, 1);
```

A record struct can follow the same model. Its declaration generates a constructor whose parameters are named after the fields:

```wx
struct User {
    id: i32,
    age: i32,
}

User : fn(id: i32, age: i32) -> User
```

Instead of introducing separate record-initializer semantics, WX can provide a general named invocation form:

```wx
User({
    id: 1,
    age: 21,
})
```

This is a call to the generated `User` constructor, not a record literal passed as one argument. The same syntax is available to ordinary functions whose declarations expose parameter names.

## Design overview

WX has two mutually exclusive call forms:

```wx
callee(first, second)              // positional invocation

callee({
    first: expression,
    second: expression,
})                                  // named invocation
```

The named argument group is special syntax belonging to a call. It is not an expression or a record value, and it is valid only as the complete contents of a call's argument list. Positional and named arguments cannot be mixed.

A callable whose parameters are unnamed supports only positional invocation. Ordinary function declarations with named parameters support both forms. A generated record-struct constructor is deliberately stricter: it supports only named invocation because its fields carry semantic names that must not be erased at the call site.

```text
fn(i32, i32) -> R                 positional only
fn(x: i32, y: i32) -> R          positional and named ordinary function
record constructor               named only
```

Parameter names form part of the source-level callable interface. For public declarations, changing a parameter name is therefore a breaking API change. Names do not need to affect the runtime function signature emitted to WebAssembly.

## Struct constructors

### Tuple structs

A tuple-struct declaration synthesizes a constructor with unnamed parameters:

```wx
struct Point(i32, i32);

Point : fn(i32, i32) -> Point
```

Consequently, only positional construction is valid:

```wx
Point(5, 1) // valid
```

Tuple-struct elements have no externally visible field names or numeric projections. Access such as `point.0` is invalid. Values are extracted through positional destructuring:

```wx
local (x, y) = point;
```

This makes a tuple struct an ordered product whose components can be constructed and destructured positionally, rather than a record with numeric field names.

### Record structs

A record-struct declaration synthesizes a constructor with parameters named and ordered according to the field declarations:

```wx
struct User {
    id: i32,
    age: i32,
}

User : fn(id: i32, age: i32) -> User // named-only constructor
```

Only named construction is valid:

```wx
User({
    id: 1,
    age: 21,
})

User(1, 21) // error: record fields cannot be supplied positionally
```

Field declaration order is not part of the record's source-level semantics. The compiler may reorder fields for layout optimization without changing construction or pattern-matching behavior. Record fields retain their names and support field projection such as `user.id`.

This follows the name-preservation rule:

> Positional information may gain local names, but named information must not lose its names.

Allowing `User(1, 21)` would erase the relationship between each value and its field name, make construction sensitive to source declaration order, and create error-prone behavior when fields are reordered. The generated constructor is therefore an implementation-level callable with a named-only invocation policy, rather than an ordinary function that can always be called positionally.

### Destructuring

Tuple structs are destructured positionally because their components have no names:

```wx
local Point(x, y) = point;
```

Record structs are destructured only with named patterns:

```wx
local User({
    id,
    age,
}) = user;
```

Positional destructuring of a record struct is invalid:

```wx
local User(id, age) = user; // error
```

Named patterns preserve the association between bindings and fields, remain independent of declaration and physical layout order, and naturally permit field renaming:

```wx
local User({
    id: user_id,
    age,
}) = user;
```

## Name resolution and validation

Named invocation is permitted only when the callee statically resolves to a callable declaration whose parameter names are known. This includes direct functions, generated record constructors, qualified function names, and imported aliases that still resolve to a concrete declaration.

```wx
create_user({ id: 1, age: 21 })
User({ id: 1, age: 21 })
users::create({ id: 1, age: 21 })
```

Ordinary function values and function pointers have structural types with unnamed parameter positions:

```wx
fn(i32, i32) -> User
```

Calls through them are positional only, even if the value originated from a named function:

```wx
fn create_user(id: i32, age: i32) -> User {
    User({ id, age })
}

local constructor: fn(i32, i32) -> User = create_user;

constructor(1, 21);                 // valid
constructor({ id: 1, age: 21 });    // error
```

This avoids carrying parameter-name metadata through function-type equality, indirect calls, tables, trait matching, or WebAssembly signatures.

### Separate compilation and metadata

Parameter names and invocation policies are part of the public source-level interface and must be preserved in compiled package and interface metadata. A separately compiled caller must therefore receive enough information to:

- resolve named arguments to parameter positions;
- distinguish `PositionalOnly`, `PositionalOrNamed`, and `NamedOnly` declarations;
- diagnose unknown, duplicate, and missing argument names; and
- detect parameter renames as public API changes.

This metadata does not need to affect the underlying WebAssembly function type. It is consumed by the WX compiler when type-checking calls across package boundaries.

For a named call, the compiler must verify that:

1. the callee supports named invocation;
2. every supplied name corresponds to exactly one parameter;
3. no name appears more than once;
4. every parameter is supplied exactly once; and
5. each expression has a type compatible with its corresponding parameter.

Because WX has no default parameter values, omitted arguments are always errors.

For a positional call, the compiler must additionally reject a callable whose invocation policy is named-only. In particular, this prevents a record constructor from being called positionally.

## Evaluation order

Named argument expressions are evaluated exactly once in source order, from top to bottom. Parameter names determine binding, not evaluation order.

Given:

```wx
fn consume(a: i32, b: i32);

consume({
    b: make_b(),
    a: make_a(),
});
```

the observable order is `make_b()` followed by `make_a()`, even though `a` precedes `b` in the declaration. The call itself receives values in canonical parameter order. Conceptually, lowering behaves like:

```wx
local temporary_b = make_b();
local temporary_a = make_a();
consume(temporary_a, temporary_b);
```

This rule makes reordering named entries safe with respect to binding while keeping the execution order visible in source code.

## Effects

Named invocation does not inherently require pure argument expressions. Effects produced while evaluating arguments are tracked normally and occur in source order.

The compiler may represent the named argument group as a distinct checking scope if that is useful for diagnostics or future restrictions, but the initial language semantics should not reject effects merely because an argument appears in a named group.

## Compiler representation

The parser should represent named invocation as a call-specific argument form rather than parsing `{ name: value }` as a general expression:

```text
CallExpression {
    callee,
    arguments: Positional([Expression])
             | Named([NamedArgument]),
}

NamedArgument {
    name,
    value,
}
```

Callable declarations should expose a compile-time parameter interface:

```text
Parameter {
    name: Optional<Symbol>,
    type,
}

InvocationPolicy = PositionalOnly
                 | PositionalOrNamed
                 | NamedOnly
```

Function-pointer types may discard names and retain only the ordered parameter types. Generated tuple constructors contain unnamed parameters and use `PositionalOnly`; ordinary named functions use `PositionalOrNamed`; generated record constructors contain field-derived names and use `NamedOnly`.

### Constructor-to-function-pointer conversion

WX does not expose a machine address for a WebAssembly function, but it can convert a statically known function item into a function-pointer value suitable for indirect calls. For a tuple-struct constructor this is straightforward because the constructor is already positional:

```wx
struct Point(i32, i32);

local constructor = Point as fn(i32, i32) -> Point;
local point = constructor(1, 2);
```

A record-struct constructor creates a design tension. Converting it to a plain function pointer erases its names and exposes positional invocation:

```wx
struct User {
    id: i32,
    age: i32,
}

local constructor = User as fn(i32, i32) -> User;
local user = constructor(1, 21);
```

The conversion cannot be defined merely by saying that the constructor is an ordinary function. The target function type needs an ordering for its parameters, while record field declaration order is intentionally not semantic and physical layout order may be independently optimized.

Possible resolutions are:

1. **Reject direct erasure.** Record constructors remain callable items but cannot be converted to plain function pointers. A programmer who intentionally needs a positional adapter writes an explicit wrapper, thereby choosing and documenting the order:

   ```wx
   fn make_user(id: i32, age: i32) -> User {
       User({ id, age })
   }
   ```

2. **Allow an explicit cast using declaration order.** This makes the loss of names intentional, but also makes field declaration order observable through the cast. Reordering fields would then be a breaking semantic change, contradicting the otherwise order-independent record model.

3. **Introduce named function-pointer types.** Such a type could preserve the constructor's field names and `NamedOnly` policy while sharing the same runtime WebAssembly signature. This retains the invariant but introduces names and invocation policies into function-type metadata and compatibility rules.

The first option preserves the current record semantics most cleanly. The second keeps constructors closest to ordinary functions but weakens the claim that record field order does not matter. The third fully preserves names but adds the most type-system complexity. This decision remains open.

## Type-checking algorithm

For a positional call:

1. Resolve the callee and obtain its ordered parameter types.
2. Reject the call if its invocation policy is `NamedOnly`.
3. Check the argument count.
4. Type-check each argument against the parameter at the same position.

For a named call:

1. Resolve the callee to a concrete callable declaration.
2. Reject the call if its invocation policy is `PositionalOnly` or if any required parameter name is unavailable.
3. Build or query a name-to-parameter-index map.
4. Visit arguments in source order, resolving each name and type-checking its value against the selected parameter.
5. Detect unknown, duplicate, and missing names.
6. Record the canonical parameter index for each checked argument while preserving source order.

## Lowering

Named invocation is compile-time syntax and introduces no special WebAssembly calling convention.

If named arguments are already written in parameter order and the target IR preserves left-to-right evaluation, they can lower directly to an ordinary call. Otherwise, evaluate each expression in source order into an IR temporary or WebAssembly local, then emit the call operands in parameter order.

```text
source entries:       [(b, make_b), (a, make_a)]
resolved indices:     [(1, make_b), (0, make_a)]
evaluation sequence:  temp1 = make_b; temp0 = make_a
call operands:        [temp0, temp1]
```

Constructor calls use the same checking and lowering pipeline as other calls. The only constructor-specific operation is synthesizing the callable declaration and constructing the resulting aggregate value.

## Diagnostics

Diagnostics should use the declaration's parameter names and offer targeted fixes:

```text
unknown named argument `ag`
help: a parameter named `age` exists
```

```text
named argument `id` is provided more than once
```

```text
missing named argument `age`
```

```text
named invocation is not available through a function value
help: call this value positionally
```

```text
constructor `Point` has unnamed parameters
help: use positional syntax: Point(...)
```

```text
record constructor `User` requires named arguments
help: use `User({ id: ..., age: ... })`
```

```text
record `User` cannot be destructured positionally
help: use `User({ id, age })`
```

## Consequences

The design provides one call abstraction for ordinary functions and synthesized struct constructors while allowing declarations to restrict their invocation policy. Record construction no longer requires an independent initializer expression in the AST or type checker. Tuple structs remain genuinely positional; record structs preserve field names during both construction and destructuring.

The main costs are that public parameter names become stable API, compiled interfaces must preserve source-level call metadata, reordered named arguments may require temporaries to preserve source evaluation order, and conversion of record constructors to function pointers requires an explicit design decision.

## Open questions

- Should named invocation be supported for trait methods when the method resolves to a concrete declaration, with the receiver/self parameter implicitly consumed by the method-call receiver and excluded from the named argument list? For example, `object.method({ foo: 1, bar: 10 })` should resolve named arguments against the concrete method's explicit parameters while `self` is supplied by `object`.
- How should record constructors convert to function pointers without silently making record field order semantic? The options are rejecting direct erasure, allowing an explicit order-dependent cast, or preserving names in a richer function-pointer type.
- Should named record patterns require every field initially, or support partial destructuring through explicit rest syntax?
