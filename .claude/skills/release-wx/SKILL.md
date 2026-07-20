---
name: release-wx
description: Cut and publish a new wx release (compiler/CLI/LSP, and/or the wxlanguage/vscode extension). Use when asked to bump versions, prepare a release, write a changelog for a release, or publish/tag wx or the VS Code extension.
---

# Releasing wx

Two independently-versioned things can be released: **wx itself** (compiler +
CLI + LSP, versioned in lockstep) and the **`editors/vscode` extension** (its
own repo, own version, own publish pipeline). Don't conflate them — a wx
release does not touch the extension and vice versa; editor integrations
under `editors/` version independently in their own repos, each with its own
`CHANGELOG.md` and release tags.

## 1. Before touching anything: pick the version bump correctly

Before tagging a `wx` release, check whether the diff actually warrants
`0.MINOR.0` vs `0.x.PATCH`: under the standard pre-1.0 semver convention,
`0.MINOR.0` is for breaking changes (removes previously-working behavior, or
makes previously-accepted code newly fail) and `0.x.PATCH` is for
backward-compatible ones. A pile of new features is **not** automatically a
minor bump if nothing breaks; conversely, one small breaking rule change
(e.g. a new coherence check that rejects previously-legal code) *does*
justify a minor bump even if everything else is a bugfix. Don't default to a
patch bump just because nothing looks dramatic on its face — actually read
the diff for this.

## 2. Housekeeping before committing

- `git status` — check for stray untracked files before staging. Scratch/debug
  files left behind by prior agent runs in this repo have made it into a
  release diff before (e.g. an unrelated example dir). Don't blindly
  `git add -A` without a skim.
- If snapshot tests regenerated (`INSTA_UPDATE=always cargo test -p
  wx-compiler`), spot-check a couple of the `.snap` diffs, don't just trust
  green tests — a wrong-but-still-passing snapshot is possible if the test's
  assertions are weak.
- Run the full gate before opening a PR: `cargo test --workspace`,
  `cargo clippy --workspace --all-targets -- -D warnings`, `cargo fmt --check`.

## 3. Version bump locations (wx itself)

All in lockstep, all six:
`crates/{wx-compiler,wx-cli,wx-fmt,wx-compiler-wasm,wx-lsp-wasm,wx-lsp}/Cargo.toml`
Plus npm: `cli/package.json` and each
`cli/npm/{darwin-arm64,darwin-x64,linux-x64,win32-x64}/package.json`
(their `optionalDependencies` in `cli/package.json` use `workspace:*`, so
those don't need per-version edits).
Then `cargo check --workspace` once to refresh `Cargo.lock` — don't hand-edit it.

`web/` and `web-next/` (playground apps) stay pinned at `0.0.0` — not part of
this lockstep, leave them alone.

`editors/vscode/package.json` versions **independently** — only bump it when
that repo itself has changes, using ordinary semver (no special
minor-means-breaking rule there).

## 4. Changelog

- Root `CHANGELOG.md`: new `## [x.y.z] - <date>` section, Keep a Changelog
  style (`### Added`/`Changed`/`Fixed`). Skip internal-only renames/refactors
  that don't change observable behavior.
- `editors/vscode/CHANGELOG.md`: separate entry, only for that repo's own changes.
- **The GitHub Release body convention is literally the new CHANGELOG section,
  pasted verbatim** — not a separately-written announcement. Extract it with:
  ```bash
  awk '/^## \[X.Y.Z\]/{flag=1; next} /^## \[PREV\]/{flag=0} flag' CHANGELOG.md
  ```

## 5. `main` is protected — you cannot push straight to it

Verify before assuming either way (this differs per repo — main `wx` has a
ruleset, `wxlanguage/vscode` currently does not):
```bash
gh api repos/<owner>/<repo>/rulesets
gh api repos/<owner>/<repo>/branches/main/protection
```
If protected: commit on a branch (e.g. `release/x.y.z`), push, open a PR,
wait for the required status check, merge — then `git checkout main && git
pull` locally before tagging (your local `main` is stale otherwise).

**Gotcha already hit once:** the required status check is matched by the CI
job's `name:` string, not the workflow name. If you rename the job in
`ci.yml`, the ruleset's `required_status_checks[].context` must be updated to
match in the same change, or every future PR stalls forever on a check that
can never report. Update it with:
```bash
gh api -X PUT repos/<owner>/<repo>/rulesets/<id> --input updated-ruleset.json
```
(fetch the current ruleset first and only change the `context` field — don't
hand-reconstruct the whole payload from memory).

## 6. Tag + release (triggers publish)

Convention: `gh release create` both creates the tag and the release in one
step, targeting `main` — don't pre-create an annotated tag separately.
```bash
gh release create vX.Y.Z --target main --title vX.Y.Z --notes-file <extracted-changelog-section>
```
This fires the repo's publish workflow (`on: release: types: [published]`).

**Check whether the publish workflow has an approval gate before assuming
anything is safe to trigger** — the two repos differ:
- main `wx`'s `publish-cli.yml` job is scoped to a `npm-publish` GitHub
  Environment with `required_reviewers` — creating the release only *queues*
  the build; nothing publishes until a human approves the deployment. Check:
  `gh api repos/<owner>/<repo>/environments/npm-publish`
- `wxlanguage/vscode`'s `publish.yml` has **no such gate** — the release
  immediately builds, packages, and runs `vsce publish` to the Marketplace
  with nothing to approve. Confirm gate presence/absence before creating the
  release, don't assume symmetry between repos.

Watch the run: `gh run list --workflow=<file>.yml --limit 3` /
`gh run view <id> --json status,conclusion`.

If a release's workflow fails on a real bug (not the code being released,
but the workflow/tooling itself): fix it on `main`, then **delete and
recreate the tag/release** rather than just re-running — a `release`-
triggered workflow resolves its YAML from the tag's target commit, so a
rerun against the old tag reuses the broken workflow file. Safe to delete as
long as the failure happened before anything external actually got
published: `gh release delete vX.Y.Z --yes && git push origin --delete
vX.Y.Z`, then recreate against the fixed commit.

## 7. After release

- Delete the merged release branch, local + remote (`git branch -d`,
  `git push origin --delete`).
- If `editors/vscode` had unrelated changes bundled into the same working
  session, it still needs its own separate commit/tag/release in its own
  repo — nothing about releasing wx itself touches that submodule's pointer
  automatically.
