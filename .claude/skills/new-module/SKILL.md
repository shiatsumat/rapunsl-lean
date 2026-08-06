---
name: new-module
description: Checklist and boilerplate for creating a new .lean file in the rapunsl-lean repo. Use this whenever adding a new Lean module/file to the library, even if the user only says "add a file for X" or "factor this out into a new file" — it covers the module-system header, umbrella-module registration, and placement conventions that are easy to miss.
---

# Creating a new module (rapunsl-lean)

## 1. Pick the location

Place the file in the directory matching its layer:

- `RapunSL/Math/Mset/` — multiset library (`Ifam`/`Mset`/`Mseti`/`Msetiv`)
- `RapunSL/Math/Algebra/` — resource-algebra hierarchy (`PCM`, `PCMI`, `PCMC`, `PCMP`, `RR`)
- `RapunSL/Logic/` — BI utilities; `RapunSL/Logic/RBI/` — RapunSL's own model and connectives
- `RapunSL/Util/` — general syntax/meta utilities

Lower layers must not import higher ones (`Mset` → `Algebra` → `Logic`).

## 2. File boilerplate

Every file follows this exact skeleton (see e.g. `RapunSL/Logic/RBI/Add.lean`):

```lean
module

public import RapunSL.Math.Mset.Core
open Ifam Mset

@[expose] public section

/-! # <Title of the file> -/

namespace <Namespace>
...
```

Details that are easy to get wrong:

- Start with the bare `module` keyword, then a blank line.
- Use `public import` for imports that downstream files must see; plain `import` for implementation-only ones.
- The `open` line comes directly after the imports, **before** `@[expose] public section` (no blank line between the last import and `open`). Scoped notation lives in namespaces (`Mset`, `PCM`, `RBI`, …), so `open` what the file uses.
- Wrap everything in a single `@[expose] public section`; no closing `end` for it is needed at the end of the file.
- Title the file with a `/-! # ... -/` doc header, and use `/-! ## ... -/` for sections within.

## 3. Register in the umbrella module

Add a `public import` line for the new file in the directory's umbrella module — `Mset.lean`, `Algebra.lean`, `RBI.lean`, `Math.lean`, `Logic.lean`, `Util.lean` — which is how everything reaches the root `RapunSL.lean`. Umbrella files contain only `module` plus `public import` lines. **This step is the one most often forgotten**; without it the file never gets built as part of the library.

Keep the import list in dependency-ish order, matching the existing lists (e.g. `Core` first).

## 4. Content conventions

- Declarations belonging to a type's namespace are typically `protected`.
- Introduce notation with `scoped` prefixes/macros inside the relevant namespace.
- Give every definition and lemma a doc comment (`/-- ... -/`); reuse the doc for notation via `@[inherit_doc]`.
- Follow the naming conventions in CLAUDE.md (type variables, multiset names, hypothesis names).

## 5. Verify

Build just the new module first — it's the fastest check:

```bash
lake build RapunSL.<Dotted.Module.Path>
```

Then `lake build` to confirm the umbrella wiring and downstream files still compile. Linter warnings (Mathlib standard set) surface during the build and should be fixed.
