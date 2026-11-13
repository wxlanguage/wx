# Declarations as symbol table rows

Status: in progress (2026-11-12). All five steps are done. The text before each step uses the names of its time (`DeclKey`, `LocalDeclIdx`, `decl`), which step 5 renamed.

## The problem

`tir/decls.rs` records what a declaration means and where it is written, but
it spreads the "where" across many structs and has two identities for one
declaration:

- **Two identities, two kind enums.** A `DeclKey` is a namespace plus a slot
  in its `SymbolTable::items`, which holds an `ItemDecl { kind: DeclKind,
  span }`. A `DeclId` is an arena plus an index (`DeclId::Function(..)`).
  `DeclKind` (15 variants) is the namespace's view, `DeclId` (12) the arenas'.
  They overlap, and they cover different things. Items have both. Trait and
  impl members have only a `DeclId` (through `MemberKind`), and so do impls.
  Modules, import blocks, packages and enum variants have only a `DeclKind`.
- **The same source facts in about 13 structs.** `file_id`, `namespace` (or
  `parent_namespace`), `name: Spanned<SymbolU32>` and often `pub_span` are
  repeated in `StructDecl`, `EnumDecl`, `TraitDecl`, `TypeAliasDecl`,
  `TypesetDecl`, `FunctionDecl`, `MemoryDecl`, `GlobalDecl`, `ConstDecl`,
  `AssocTypeDecl`, `PackageInstanceDecl`, `ModuleDecl` and `ImportDecl`.
  `ItemDecl::span` repeats the name span, except on a module's or an import
  block's own entry, where it is the content span.
- **So every question about a name is a match over kinds.** Examples:
  - `Declarations::name(DeclId)`, which hits `todo!()` for an impl;
  - `declaration_name_span`, which special-cases `Module` and `Import`;
  - the `MemberKind` match in `Semantics::definition_span`;
  - `Semantics::definitions()`, one loop per arena.

  A feature that needs a span nobody stored (rename inserting `"old": ` before
  a host import entry) has no natural place to put it.

Scale, for the migration (uses in `wx-compiler` and `wx-lsp`): about 245
`DeclKind::`, 76 `DeclId::` and 61 `DeclKey` uses, 140 `.name.inner` and 63
`.name.span` uses.

## Three concepts that are currently mixed

1. **A declaration** binds a name somewhere and has a visibility. Examples:
   - a struct, an enum and its variants, a trait, a typeset, a type alias;
   - a function, constant, global or memory;
   - a module, an import block (its alias), a package instance (its alias);
   - a trait's or an impl's member.

   Members are not bound in any namespace (they are reached through a type),
   but they have names and their own `pub` (`check_member_access`).
2. **Something whose signature is built.** `ensure_signature` is keyed by
   this. It covers the declarations that have a signature (not a module, an
   import block, a package or a package instance) and also trait and
   inherent impls, whose headers (target, trait, type parameters, bounds)
   are built and checked like signatures. `DeclId` includes
   `TraitImpl`/`InherentImpl` for this reason, which is right for a query
   key and wrong for "a declaration" (step 4).
3. **A namespace.** This is what a path continues into, and a scope is where
   code is written. A module, an import block and an enum are each named by
   a declaration in the scope around them. A package's root is named by its
   own entry, slot 0 of its table (`LocalDeclIdx::SELF`, `DeclKind::Package`):
   `self` and `package` at its root, `super` in its top-level modules, `std`
   in every other package, and an alias `use` gives one of those
   (`use package as p;`) all bind it, and `Namespaces::entered_by` turns it
   into the namespace a path continues into. `self`, `super` and `package`
   are plain names bound in each scope's table, not path qualifiers.

An impl is not a declaration. It binds no name, nothing can mark it `pub`, and
nothing can import it. It is an item in the syntax and a signature query, and
it stays in its own arena (`TraitImplDecl`, `InherentImplDecl`) with its
`Scope`, which is meaning: where names written inside it are looked up.

A `use` item is not a declaration either. It binds an existing declaration
under a name (`UseItemDecl`, `BindingSource::Import`) and stays as it is.

## The rows

A `SymbolTable` already holds the declarations made in its namespace
(`items: Vec<ItemDecl>`, which a `DeclKey`, namespace plus slot, addresses),
apart from the names it binds (`bindings`). The row is `ItemDecl`, grown into
what a declaration is:

```rust
/// A declaration made in this table's namespace, as written.
pub(super) struct ItemDecl {
	/// Which arena holds what it means, and its index there.
	pub kind: DeclKind,
	pub name: Spanned<SymbolU32>,
	pub visibility: Visibility,
}
```

- **`DeclKey` stays the identity.** Bindings, `Reference::Item` and
  `Definition::Item` already hold one, so nothing that refers to a
  declaration changes. A global table indexed by a new global index was
  considered: it gives a one-`u32` index and one loop over every declaration,
  but it introduces a second identity to migrate every reference to, and its
  row needs a `namespace` field the table position already gives.
- **The row has no namespace or file.** The table is the namespace, and every
  namespace is written in one file (`SymbolTable::file_id`), so the name's
  span is a `TextSpan`.
- **No span of the whole declaration.** What it would cover changes with the
  kind (attributes or not, an import entry's `"field":`, a block's body), so
  it would not be one fact, and only rename needs one such span, an import
  entry's. Spans that belong to a particular syntax unit live with what
  records that unit (see "Host import field names"); a general one can be
  added when something needs it and its meaning is settled.
- **A row lives where the declaration is declared.** A module's and an import
  block's rows are in the parent's table, with their names in the parent's
  file; the file of a module's contents stays in `ModuleDecl::own_file`, as
  meaning (see step 1). A package's own entry stays in its own table, since a
  package has no declaring site outside itself; as a row it is a generated
  declaration named `package`, with an empty span (see "Generated
  declarations").
- **Members are rows too**, in the table of the scope their trait or impl is
  written in, and not bound there: a row is reachable by name only if a
  binding points at it, so a member stays reachable only through its type.
  Enum variants already work this way in `Namespace::Enum`'s table.
- **Each per-kind arena keeps only meaning** (signature inputs, members, impl
  links, limits) plus a back-pointer `decl: DeclKey`. That one field replaces
  `file_id`, `namespace`, `name` and `pub_span`.
- **Name, file and visibility are one lookup away.** `name()`,
  `declaration_span`, the `Definition::Member` arm of `definition_span` and
  the per-arena loops of `definitions()` become reads of the row and its
  table.

### Generated declarations

A typeset's trait, and the `Size`/`Value` associated types of a memory's or a
global's impl, have names but are not written. They get rows, in the table of
the scope their generator is written in, whose `name.span` is empty, as it is
today; what generates them stays recorded as meaning in their arenas
(`TraitDecl::typeset`, the memory's or global's impl). Every arena entry then
has a `decl`, so the back-pointer is never optional. (The alternative, no row
and an `Option<DeclKey>` in the arena, brings an `Option` back elsewhere.)

A package's own entry is generated the same way: the compiler declares it so
that `self`, `package` and `std` have something to name, and nobody writes it.
Its row's name is `package` and its span is empty.

### Visibility

Today it is recorded in different ways:
- `pub_span: Option<TextSpan>` on some decls;
- `InherentMemberDecl::visibility`;
- computed when a binding is made (`Binding::definition(.., Visibility::..)`);
- a trait member is as visible as its trait.

The row holds the declaration's own visibility, as written (`pub` or not).
Rules that derive one from another (a trait member's is its trait's, an
import's entries are public within the block) stay in the code that applies
them, which then reads the rows. The `pub` keyword's own span is only needed
by diagnostics that point at it (see the open questions).

## Steps

Each step preserves behaviour and leaves every test passing.

1. **Rows for modules and import blocks where they are declared (done).** A
   module's and an import block's row is in the parent's table, at its name
   (`push_module`, `push_import`), and `ModuleDecl::decl`/`ImportDecl::decl`
   point at it. The parent's binding of its name, `self` inside it and
   `super` inside its children bind that row (`ScopeTable::child`,
   `bind_child`, `scope_key`); `entered_by` turns it into the namespace as
   before. Their old self entries, slot 0 of their own tables with the
   content's span, are gone, and so is `declaration_name_span` with its
   `Module`/`Import` special case: every row's span is its name's. A
   package's own entry stays as it is, and so does `std`'s binding to the
   standard library's.

   Considered and set aside: removing the package's own entry too, with
   `self`/`package`/`std` binding a namespace through a new
   `BindingTarget` variant. It made "no `DeclKey`" mean either an error or a
   package, which about 25 callers of `decl_key()` would have read as
   "already reported", silently dropping diagnostics; and `self`, `super`
   and `package` are to stay plain names, which `use package as p;` binds
   like any other. Whether `std` should name an instance instead is an open
   question below; for now it names the standard library's own entry.
2. **Grow the rows (done).** `ItemDecl` is `{ kind, name, visibility }`; its
   `span` is gone (`DeclKey::source_span` reads `name.span`). Members (of
   traits, inherent impls and trait impls) and generated declarations (a
   typeset's trait; the `Args`/`Result`, `Size` and `Value` associated
   types of a function's, memory's and global's impl) are unbound rows in
   their scope's table, and the package's own entry is a row named
   `package`. Every per-kind arena has `decl: DeclKey`, the old fields
   stay, and `every_declaration_is_a_row_that_agrees_with_its_arena` pins
   that the row's kind leads back to the entry, that name, file and (where
   recorded) visibility agree, and that every row but a package's own
   entry belongs to exactly one arena entry. Along the way:
   - `DeclKind::TraitAssocType` is `DeclKind::AssocType`, since an impl's
     and a generated associated type are rows of that kind too;
   - each row is pushed before its arena entry (an enum's variant rows
     before the variants' run of constants), so `decl` is known when the
     entry is built;
   - a package instance with an unknown key has a row too, which its
     poisoned alias does not bind; a malformed alias (already a parse
     error) records no instance at all;
   - `Semantics::definitions` reads only the rows: one loop over
     `Namespaces::keys`, members included, as `Definition::Item`. The three
     loops that added members as `Definition::Member` are gone. Generated
     rows, the package's own entry among them, are left out by their empty
     spans. Hover and semantic tokens render a member the same either way,
     and `reference_identity` already makes the two forms one, so rename and
     references are unchanged;
   - a typeset's trait has an empty name span in its row, while
     `TraitDecl::name` (and so `Declarations::name`) keeps the typeset's
     written span. Step 3 decides which a diagnostic about the generated
     trait points at;
   - the rows' `visibility` has no reader yet, so a release build warns that
     it is never read until step 3.
3. **Move the readers to the rows, then delete the copies (done).** The
   per-kind arenas hold only meaning plus `decl`: `name` (with
   `PackageInstanceDecl::alias` and `ImportDecl::internal_name`),
   `file_id` (with `ModuleDecl::declaration_file`), `pub_span` (with
   `InherentMemberDecl::visibility`) and `namespace` (with
   `parent_namespace`) are gone. Readers go through the row:
   - `Declarations::item(key)` is the row (`ItemDecl` is public, for the
     LSP), `Declarations::file_id(key)` its table's file, and
     `Declarations::scope(key)` the scope its signature is read in: its
     table's, or for an enum's variant the enum's;
   - `Declarations::decl_key(DeclId)` mapped a signature query to its row
     (`None` for an impl), and `Declarations::name(DeclId)` read the row
     through it (both replaced in step 4);
   - `DeclKind::declared_at` and `definition_span`'s `Member` arm are
     `declaration_span` of the row;
   - `check_member_access` reads the row's visibility, for an inherent
     member and for a trait.

   No diagnostic needed the `pub` keyword's own span, which settles the
   first open question below. A typeset's trait now has an empty name span
   everywhere (`Declarations::name` included), not the typeset's; no test
   pinned a diagnostic at it. The agreement test is now
   `every_declaration_is_a_row_its_arena_entry_points_at`: each arena
   entry's row has its kind, every row but a package's own entry belongs
   to exactly one entry, and the rows' names, spans and visibilities are
   checked against the source.

   Left as is: `TraitMemberDecl::span`/`InherentMemberDecl::span`, a
   member's span in its impl's member list. For a written member it is the
   row's name span, but for a generated impl's member (a memory's `Size`, a
   function's `Args`) it is the generator's name, which impl overlap
   diagnostics point at, while the row's span is empty. Whether to keep
   that span is a separate decision. The matches over kinds that remain
   are `decl_key` and `declared_at`; step 4 removes the first, with what
   treats `DeclId` as a declaration.
4. **`DeclId` is the signature query domain, not a declaration (done).**
   It became `SignatureQuery`, with the shape it has: one typed index per
   arena whose entries have a signature, impls included.

   ```rust
   enum SignatureQuery {
   	Struct(StructIdx),
   	Enum(EnumIdx),
   	Trait(TraitIdx),
   	Typeset(TypesetIdx),
   	TypeAlias(TypeAliasIdx),
   	Function(FunctionIdx),
   	Const(ConstIdx),
   	Memory(MemoryIdx),
   	Global(GlobalIdx),
   	AssocType(AssocTypeIdx),
   	TraitImpl(TraitImplIdx),
   	InherentImpl(InherentImplIdx),
   }
   ```

   Keyed by typed indices, not by the row's key, as rust-analyzer keys its
   queries (`GenericDefId`, a union of typed ids that includes `ImplId`;
   `DefWithBodyId`, …), and not as rustc does (one flat `DefId` for every
   definition, its kind a lookup). Considered and set aside: keying it by
   the row (`Decl(DeclKey)` plus the two impls), because
   - the results live in arenas indexed by the typed index
     (`sema.structs[StructIdx]`), so a query would read the row only to
     learn where its result goes;
   - a typed key cannot ask for something that has no signature (a module,
     a package);
   - rows and queries do not correspond one to one: a typeset's trait has a
     row of its own, but its signature is built by the typeset's query
     (`trait_decl_id`);
   - a key derived from a location pays off when ids must stay stable
     across edits (rust-analyzer interns its `ItemLoc`s for that), and
     nothing here needs that: the LSP rebuilds the whole snapshot.

   What treated `DeclId` as a declaration is gone, since an impl is not one:
   - `Declarations::name(DeclId)` (with its `todo!` for an impl) and
     `Declarations::decl_key(DeclId) -> Option`. A typed index reaches its
     row through its arena entry's `decl`, by the `Declared` trait
     (`index.decl(decls)`), which every arena index with a row implements,
     and `MemberKind` too; `Declarations::name(index)` reads the name of
     any of them. No impl index implements it, so asking an impl for a
     name does not compile;
   - a member reaches its row directly, with no `Option` and no `expect`
     (`check_member_access`, `definition_span`'s `Member` arm);
   - a cycle diagnostic does not name an impl: a step through an impl's
     header is "resolving the header of this impl", at the span its
     secondary label already has, and a struct cycle lists and labels only
     the declarations in it. Whether an impl can be on a cycle at all is not
     settled, so this is handled rather than assumed unreachable.

   `import_fields` is keyed by the row (`DeclKey`), as the host import
   field design below already has it. `DeclKind` (a row's kind, the
   namespace's view) and `SignatureQuery` (what has a signature) stay two
   enums over different sets: modules, packages and package instances have
   rows and no signature, impls a signature and no row. The rename covered
   the query machinery too: `AstNodeRef::query()`, `QueryInfo::query`,
   `query_state` keys, `Semantics::trait_query`.
5. **`DeclKey` becomes `ItemLoc` (done).** What it is is a location: slot `n` of a
   namespace's table, where a declaration is made, as rust-analyzer's
   `ItemLoc { container, id }` is (and rustc's `DefKey`, parent plus what
   the definition is), not an id assigned to the declaration. The name says
   so, and pairs with the row it addresses, `ItemDecl`. The back-pointer
   field in the arenas (`decl`) follows (`loc`), and so do the readers
   (`Declarations::item(loc)`, `declaration_span(loc)`, `file_id(loc)`,
   `scope(loc)`). Its slot, `LocalDeclIdx`, becomes `DeclIdx`: once
   `DeclId` is gone there is no other declaration index for it to be told
   apart from, and it is always read with the namespace that holds it
   (`ItemLoc { namespace, decl_idx }`). A rename only: what it addresses and
   how is unchanged. It also covered the `Declared` trait's method
   (`index.loc(decls)`), `BindingTarget::loc()`, and the locals that held a
   location (`decl_key`, and `decl` where it was one).

## On top: host import field names (done)

An import entry may write the field the host provides its item as
(`"Log": func log(value: u32);`). Wasm allows the same `module.field` to be
imported as several items, of any kind, so the field is not an identity.
Several declarations, each with its own name, may share one field. Once the
rows exist:

- each entry is recorded with the item it declares:

  ```rust
  /// An import block's entry: the field of the block's module the host
  /// provides its item as.
  pub struct ImportEntry {
  	/// The string written before the item, or else the item's name, which
  	/// then names it both in wx and to the host (as
  	/// `ExportEntrySource::external_span` does for `export { run }`).
  	pub field: Spanned<SymbolU32>,
  	/// The entry as written, `"field":` included.
  	pub span: TextSpan,
  }

  import_entries: FxHashMap<ItemLoc, ImportEntry>
  ```

  Its spans are in the item's file, the block's;
- lowering imports `module.field`;
- rename inserts `"old": ` at the entry's `span.start` when the field's span
  is the item's name's.

This replaced the interim `import_fields: FxHashMap<ItemLoc, SymbolU32>` and
the AST walk in `wx-lsp/src/rename.rs` that found an entry's start. A field
string that does not decode (which is reported) keeps its span, with the
item's name as its value, so "the field's span is the name's" still means
that no field is written. `Declarations::import_entry(loc)` reads an entry;
`a_host_import_records_its_entry_and_field` in `decls.rs` checks the three
cases.

## Separately: `std` becomes `core`

The package the compiler supplies is named `std`, but it is a core library
in Rust's sense: the primitives, the operator traits, `StackValue`,
`Pointer`, `Slice`/`Array`, `Memory`, `Global`, `Call`, the intrinsics and
the impls on primitives, which the language itself needs. It does no I/O,
allocates nothing and assumes no host. `core` names what it is, and leaves
`std` free for a library built on it and on a host's imports.

This rename is independent of the steps above. It goes in a commit of its
own, not mixed with a step, and it goes before the instance question below,
whose text then speaks of `core`. What carries the name:

- the source name: the binding in every package's root (`std::Bool`), the
  dependency key the loader registers first (so a manifest key `core`
  becomes the E0002 duplicate), and diagnostics that say "package `std`" or
  "the standard library";
- the manifest kind, `"type": "std"` (`PackageManifestKind::Std`, the E0004
  check), with `crates/wx-compiler/std/wx.json` and the VS Code extension's
  `wx.schema.json`. The language has no stability promise yet, so the old
  spelling is dropped, not kept as an alias;
- the embedded sources: `crates/wx-compiler/std/`, `build.rs`'s
  `STDLIB_FILES`, `StdlibFileSource`, `load_stdlib`;
- the checker's names for it: `stdlib_root`, `Intrinsic::from_std_name`,
  `std_intrinsics`, and the "std" in doc comments and test helpers
  (`TestCase::std`, `std_source_graph`, `with_pending_std_signatures`);
- the LSP's `wx://std/` URIs (`convert.rs`, `backend.rs`) and `web-next`'s
  virtual files, which must agree with them;
- CLAUDE.md and the notes.

Whatever reads Rust's `std::` is untouched; the rename is by identifier and
string, not a text substitution over `std`.

## Open questions

- (Settled in step 3.) No diagnostic needs the `pub` keyword's own span:
  the only reader of `pub_span` built a `Visibility` from it.
- Should `std` name a package instance rather than the standard library's
  own entry? Source reaches every other package only through an instance
  (`package "key" as alias;`), so an implicit instance would remove the one
  exception, and std is an instance in substance: the compiler instantiates
  it and supplies its package functions. Implementing it is small (a
  generated `PackageInstanceDecl` and row aliased `std` in each package's
  root, bound as `std`; `entered_by` already enters an instance's package),
  but it is deferred to the package instance follow-up (per-instance
  namespaces, `Namespace::PackageInstance`), because only then does it mean
  anything, and what it means is not settled:
  - CLAUDE.md makes each instance its own instantiation site, which will get
    its own copy of the package's code. A row per package would say every
    package instantiates std separately, while std is meant to be
    instantiated once, by the compiler, and shared as the prelude (one set of
    intrinsics, one `Bool` and `Char`, which the type interner depends on).
    The accurate model is likely a single compiler-declared instance that
    every package refers to.
  - The prelude falls back into std's namespace directly (`stdlib_root`), not
    through the `std` binding. Once instances are distinct, `std::Bool` and a
    bare `Bool` must reach the same instantiation, so how the prelude reaches
    std is decided together with this.

  Until then the cost is small: diagnostics say "package `std`", and the
  duplicate-definition label for `struct std();` points into std's file (a
  separate fix: the package's own entry has an empty span, so the label
  should say the compiler declares `std` instead).
