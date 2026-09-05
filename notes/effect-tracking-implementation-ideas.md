Fixed-point iteration can be inefficient in the worst case, but for your particular effect system it may still be completely reasonable. The important question is what exactly is changing during iteration and how large your SCCs/effect sets are.
For your case, each function has a finite effect set, and during inference that set only grows. If an SCC has F functions and there are at most E distinct effects relevant to it, each (function, effect) pair can only be discovered once. So a well-implemented worklist solver is not the scary version of:
scan every function
scan every function
scan every function
...
Instead, you enqueue only functions whose dependencies changed.
For example:
while let Some(f) = worklist.pop() {
    let new = infer_effects(f);

    if new != effects[f] {
        effects[f] = new;

        for caller in reverse_dependencies[f] {
            worklist.push(caller);
        }
    }
}
With your small effect sets, I would seriously consider this first. It is simple, robust, and handles catch naturally.
The alternatives mostly amount to exploiting more structure in your equations.
1. Solve each effect independently as a reachability problem
This is probably the most interesting alternative for WX.
Suppose you want to answer:
Does effect A escape function f?
A normal call edge propagates A:
f -> g
but if that call is under:
g() catch A
then that edge blocks A:
f -X-> g   for effect A
So for a particular effect A, your problem becomes almost:
Is there a path from f to an origin of A that does not cross a handler for A?
Example:
a -> b -> throw<A>
     |
   catch A
For A, the catch edge cuts propagation.
You could therefore construct an effect-specific graph and perform reachability rather than iterative set propagation.
Conceptually:
origin A
   ↑
   b
   ↑
   a
versus:
origin A
   ↑
   b
   X   catch A
   a
This can give you a direct graph algorithm.
The downside is that you’d potentially repeat graph traversal for many effects. If there are thousands of distinct instantiated effects like:
throw<Foo>
throw<Bar>
read<heap>
write<heap>
...
doing a separate traversal for every effect may end up worse than propagating compact effect sets once.
2. Symbolically solve SCC equations
Your equations have a fairly restricted shape:
F = direct
    ∪ (G - handled1)
    ∪ (H - handled2)
You could keep these as symbolic expressions and simplify them.
For example:
A = B - X
B = A ∪ X
Substitute A:
B = (B - X) ∪ X
which simplifies to:
B = B ∪ X
and the least solution is:
B = X
A = {}
So theoretically you could construct and solve recursive set equations algebraically.
But I would probably not do this in a compiler unless you find that you actually need it. Once you have larger SCCs:
A = (B - X) ∪ C
B = (D - Y) ∪ A
C = ...
D = ...
symbolic substitution can explode in size. Then you end up implementing a proper constraint solver just to avoid a tiny fixed-point loop.
3. Turn it into boolean dataflow equations
Each individual effect is really a boolean property.
For a specific effect E:
has_effect(f, E): bool
Union becomes OR:
A ∪ B
becomes:
a || b
and subtraction by a known handler becomes:
effects(g) - {E}
which, specifically for E, becomes:
false
So this:
effects(f) =
    direct(f)
    ∪ (effects(g) - {A})
can be viewed separately for each effect.
For effect A:
F_A = direct_A || false
For effect B:
F_B = direct_B || G_B
That is a monotone boolean equation system. There are algorithms for solving those very efficiently, often effectively as graph reachability.
This is mathematically cleaner than thinking about arbitrary set arithmetic.
4. Push handlers onto edges
I think this is likely the most useful optimization for your representation.
Represent:
foo();
as:
caller -> foo
filter = {}
and:
foo() catch A
as:
caller -> foo
filter = {A}
Then propagation is:
callee_effects - filter
Now you don’t need to walk the entire expression tree every time an SCC member changes. You can precompute something like:
struct EffectEdge {
    callee: FunctionId,
    handled: EffectSet,
}
plus the function’s direct effects:

struct EffectEquation {
    direct: EffectSet,
    calls: Vec<EffectEdge>,
}
and inference becomes:
result = direct;

for edge in calls {
    result |= effects[edge.callee] - edge.handled;
}
That’s extremely cheap, especially if your effect sets are small sorted vectors or small inline sets.
Would Tarjan + worklist actually be slow?
Probably not for your expected compiler workloads.
Imagine a recursive SCC of 5 functions and 8 effects. There are only:
5 × 8 = 40
possible pieces of information to discover.
Even an SCC of 50 functions with 16 effects gives only:
800
function has effect facts.
With a worklist, every newly discovered fact causes only relevant dependents to be reconsidered.
The pathological case is something like:
f1 -> f2 -> f3 -> ... -> f10000
^                        |
|________________________|
with effects being discovered one at a time and propagated around a giant SCC. You could do quite a lot of repeated work there.
But giant mutually recursive SCCs are relatively unusual in normal source programs.
There is also an important optimization: propagate deltas
You don’t necessarily need to recompute:
effects(f)
from scratch every time.
Suppose g previously had:
[A, B]
and now becomes:
[A, B, C]
The only new information is:
delta = [C]
If:
f -> g except {B}
then you propagate:
delta - {B}
which is just:
[C]
This gives you a classic incremental worklist solver:
new effect discovered
       ↓
propagate only that effect through callers
       ↓
stop when caught or already present
At that point, the implementation starts looking very close to graph reachability anyway.
For example, discovering:
throw<ApplicationError>
at some origin could conceptually propagate backwards:
throw<ApplicationError>
        ↑
        b
        ↑
        a
        X  catch ApplicationError
        caller
The handler literally stops that effect from propagating farther.
That suggests a particularly elegant implementation for WX: propagate individual newly discovered effects backwards through the call graph, stopping at edges that handle that effect.
Then you don’t even think much in terms of “iterations”:
discover effect E in f
    ↓
mark (f, E)
    ↓
for every caller of f:
    if edge doesn't catch E:
        mark (caller, E)
If (caller, E) was already marked, stop there.
This naturally terminates because every (function, effect) pair is inserted at most once.
Tarjan may actually become less important with this approach. You don’t need special recursion handling at all because the “already marked” check handles cycles:
A -> B -> C -> A
When E reaches A the second time, A already has E, so propagation stops.
So there are really two viable designs:
Tarjan SCCs
+ solve each SCC with a worklist
or:
global incremental propagation of (function, effect) facts
+ filters on call edges
For your effect system as you’ve described it so far, I actually like the second one more. Because your lattice consists basically of finite sets, union is your join, and catch removes a statically known effect, you can propagate effects individually and get very simple termination behavior.
Tarjan becomes useful again if your analysis grows more sophisticated later—for example effect variables, polymorphic constraints, relationships between effects, or other facts that aren’t just independent set members.


Yes — that makes the flat “filtered call edge” representation insufficient by itself.
If catch can wrap an arbitrary expression:
{
    foo();
    bar();
    baz();
} catch {
    A(_) -> ...
}
then semantically the effect calculation is:
subtract(
    union(
        effects(foo),
        effects(bar),
        effects(baz),
    ),
    {A}
)
The subtraction applies to the whole subtree, not to one particular call edge.
You can still normalize this particular example into three filtered dependencies:
effects(foo) - {A}
effects(bar) - {A}
effects(baz) - {A}
because set difference distributes over union:
(X ∪ Y) - A
=
(X - A) ∪ (Y - A)
So for simple composition, flattening still works.
But now consider that the handlers themselves can presumably have effects:
{
    foo();
    bar();
} catch {
    A(_) -> recover(),
}
If:
foo     = [A, B]
bar     = [C]
recover = [D]
the result is something like:
((effects(foo) ∪ effects(bar)) - {A})
∪ effects(recover)
giving:
[B, C, D]
Critically, D from the handler is not itself inside the same catch. So you can’t just say “everything under this source span gets -A” without respecting expression structure.
That makes the tree model much more compelling:
Union
├── Subtract {A}
│   └── Union
│       ├── Function(foo)
│       └── Function(bar)
│
└── Function(recover)
And nested handlers make the value even clearer:
{
    foo();

    {
        bar();
        baz();
    } catch B;
} catch A;
naturally becomes:
Subtract {A}
└── Union
    ├── Function(foo)
    │
    └── Subtract {B}
        └── Union
            ├── Function(bar)
            └── Function(baz)
This precisely expresses which handler applies to which effects.
You could still flatten it later
I think that’s probably the interesting architecture:
source/HIR
    ↓
EffectExpr tree
    ↓
normalization
    ↓
flat constraints / dependencies
    ↓
solver
So the tree doesn’t necessarily have to be what Tarjan or the fixed-point solver operates on.
For example:
Subtract {A}
└── Union
    ├── Function(foo)
    └── Function(bar)
can normalize into:
foo with filter {A}
bar with filter {A}
But:
Union
├── Subtract {A}
│   └── Function(foo)
└── Function(recover)
normalizes to:
foo     with filter {A}
recover with filter {}
And nested catches just accumulate filters along the path:
Subtract {A}
└── Subtract {B}
    └── Function(foo)
becomes:
foo with filter {A, B}
So you could traverse the effect tree while carrying a set of currently handled effects:
fn flatten(
    expr: &EffectExpr,
    filtered: EffectSet,
    out: &mut Vec<Dependency>,
) {
    match expr {
        Function(f) => {
            out.push(Dependency {
                function: *f,
                filtered,
            });
        }

        Union(children) => {
            for child in children {
                flatten(child, filtered.clone(), out);
            }
        }

        Subtract { expr, effects } => {
            flatten(
                expr,
                filtered.union(effects),
                out,
            );
        }
    }
}
Conceptually that is very clean.
One caveat is direct effect origins. If an intrinsic directly introduces A, then the flattening pass also needs to filter those:
Subtract {A}
└── Literal {A, B}
becomes:
direct = {B}
So the normalized result for a function could still be something like:
struct EffectConstraints {
    direct: EffectSet,
    dependencies: Vec<EffectDependency>,
}

struct EffectDependency {
    function: FunctionId,
    filtered: EffectSet,
}
The important difference is that you derive this from the structured effect expression, rather than trying to build it directly from call sites.
That seems like a pretty strong design to me:
EffectExpr captures lexical/scoped semantics.
The flattened constraint representation is optimized for solving.
And this also answers part of our diagnostics question: retaining the tree at least through inference gives you a very natural representation of where an effect was handled and over what expression, even if you eventually discard or compress it after producing solver constraints.

I wouldn’t optimize that case yet. The naive tree can look redundant, but it’s probably cheap enough, and you can get most of the benefit with very simple structural compression that does not require knowing the resolved effects.
Suppose:
fn foo() {
    a();
    b();
    c();
    d();
}
Initially you might imagine:
Union(
    Function(a),
    Function(b),
    Function(c),
    Function(d),
)
Even if all four eventually resolve to [trap], you don’t know that while constructing the expression. But that isn’t really a problem: you only stored four function IDs and one Union node. You haven’t copied their effect sets.
If this is represented compactly:
enum EffectExpr {
    Function(FunctionId),
    Union(Box<[EffectExpr]>),
    Subtract {
        expr: Box<EffectExpr>,
        effects: EffectSet,
    },
}
then a function containing 100 calls costs roughly 100 IDs plus some enum/node overhead. That’s likely insignificant compared with its HIR/MIR.
More importantly, I would flatten unions while constructing them. Don’t create:
Union(
    Function(a),
    Union(
        Function(b),
        Union(
            Function(c),
            Function(d)
        )
    )
)
Just create:
Union([
    Function(a),
    Function(b),
    Function(c),
    Function(d),
])
So Union is really an n-ary container rather than a binary AST operation.
You can go even further. For a block with no catch, you don’t necessarily need an EffectExpr node per statement at all. Build its aggregate directly:
Block effects:

direct:
    [...]

dependencies:
    a
    b
    c
    d
Then only introduce actual structural nodes at places where structure matters — mainly catch.
Conceptually:
enum EffectExpr {
    Group(EffectGroup),

    Subtract {
        expr: Box<EffectExpr>,
        effects: EffectSet,
    },
}

struct EffectGroup {
    direct: EffectSet,
    calls: Vec<FunctionId>,
    nested: Vec<EffectExpr>,
}
Although I wouldn’t commit to exactly that representation yet.
The key insight is:
union itself doesn’t require tree structure. subtract does.
Consider:
{
    a();
    b();
    c();
}
There’s no reason to preserve:
Union(a, b, c)
as a meaningful hierarchy. Union is associative and commutative:
A ∪ (B ∪ C) = A ∪ B ∪ C
So flatten it aggressively.
But:
{
    a();

    {
        b();
        c();
    } catch A;

    d();
}
does have meaningful structure:
Union
├── a
├── Subtract {A}
│   └── Union
│       ├── b
│       └── c
└── d
Although even that could be stored more compactly as:
root:
    calls = [a, d]

    children = [
        Subtract {A}:
            calls = [b, c]
    ]
So rather than thinking of it as a conventional AST where every operation creates a node, I would think of it as a tree of effect scopes.
For example:
struct EffectScope {
    direct: EffectSet,

    calls: Vec<FunctionId>,

    children: Vec<HandledScope>,
}

struct HandledScope {
    handled: EffectSet,
    scope: EffectScope,
}
Then:
fn f() {
    a();
    b();

    {
        c();
        d();

        {
            e();
        } catch B;
    } catch A;

    x();
}
becomes roughly:
EffectScope
│
├── calls: [a, b, x]
│
└── catch A
    │
    ├── calls: [c, d]
    │
    └── catch B
        └── calls: [e]
I actually like this representation more than the generic EffectExpr now that we’ve established that catch can wrap arbitrary expressions.
It reflects what matters semantically:
normal composition  → just accumulate things into current scope
catch               → introduces a new boundary/scope
And your common case becomes extremely cheap.
For a function with:
a();
b();
c();
d();
e();
...
and no catches, you have essentially:
EffectScope {
    calls: [a, b, c, d, e, ...],
    children: [],
}
No expression tree at all.
Then if all of them eventually resolve to [trap], your solver naturally unions them into a set:
{}

a → +trap     {trap}
b → +trap     {trap}  // already there
c → +trap     {trap}
d → +trap     {trap}
If EffectSet insertion is cheap, duplicates disappear naturally.
And with the effect sets you’ve described—usually very small—I’d expect this to be plenty efficient.

One additional optimization is worth doing almost for free: deduplicate identical dependencies within the same effect scope.
If:
foo();
foo();
foo();
exists in one scope, effect inference doesn’t care that there are three calls:
effects(foo) ∪ effects(foo) ∪ effects(foo)
=
effects(foo)
So that scope only needs one dependency on foo.
But beware:
foo();

{
    foo();
} catch A;
cannot be deduplicated across the two scopes, because they’re under different effect transformations.
So I think a very nice invariant would be:
Within one effect scope, each dependency matters only once. A catch creates a new effect scope.
That gives you compression without needing to know what effects any callee ultimately has.
I wouldn’t try to optimize the later fact that a, b, c, and d all turn out to have [trap]. Once resolved, the EffectSet itself already collapses those duplicates. Trying to discover equivalent callees early would add complexity for probably very little benefit.