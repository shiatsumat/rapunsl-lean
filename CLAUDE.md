# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

A Lean 4 mechanization of **RapunSL**, a separation logic for quantum computing (POPL 2026 paper: https://dl.acm.org/doi/10.1145/3776648, full version: https://arxiv.org/abs/2511.23472).

Toolchain: `leanprover/lean4:v4.32.2` (pinned in `lean-toolchain`). Depends on **Mathlib** (v4.32.2) and **iris-lean** (the Iris BI framework for Lean).

## Commands

```bash
# Fetch prebuilt Mathlib oleans (do this first after cloning or bumping deps)
lake exe cache get

# Build everything
lake build

# Build a single module (fastest way to check one file)
lake build RapunSL.Logic.RBI.Core
```

There is no separate test suite or lint command; the build itself is the check. Mathlib's standard linter set is enabled via `weak.linter.mathlibStandardSet = true` in `lakefile.toml`, so linter warnings surface during `lake build`.

## Code conventions

- Proofs may freely use Lean's standard axioms (notably `Classical.choice`, `propext`, and `Quot.sound`); there is no constructivity requirement.
- Every file uses the Lean **module system**: it starts with `module`, uses `public import` for imports that must be visible to downstream files (plain `import` for implementation-only ones), and wraps its content in `@[expose] public section`.
- Definitions and lemmas that belong to a type's namespace are typically declared `protected`.
- Notation is introduced with `scoped` prefixes/macros inside the relevant namespace, so `open` the namespace to use it.
- `RapunSL/Util/Syntax.lean` provides the `delab_rules` command (a shorthand for `app_unexpander`) used to pretty-print custom notation.

## Notation

Superscripts tag the level an operator lives at: `ᴵ` = `Ifam`, `ᴹ` = `Mset`, `ᴹⁱ` = `Mseti` (e.g. `<$>ᴹ`, `⊕ᴹⁱ`, `⨁ᴹ`, `≃ᴹ`, `×ᴹ`, `<*>ᴹ`, `>>=ᴹ` and their variants at each level).

Algebra (scoped in `PCM`, `PCMI`, `PCMC`, `RR`):

- `✓ a` — validity (`PCM.valid`)
- `a # b` — incompatibility (`PCMI.incomp`)
- `a ≎ b` — coherence (`PCMC.coher`)
- `a +ᴿ b =ᴿ c` — addition relation in a resource ring (`RR.radd`)

Logic, over `RProp` (scoped in `RBI`):

- `P ⊕ Q`, `⨁ i, P i` — bare mixing (`bmix`, `bigbmix`); `P -⊕ Q` — pine, the right adjoint of `⊕`
- `P #ᴿ Q` — incompatibility of propositions (`Incomp`); `P ≎ᴿ Q` — coherence of propositions (`Coher`)
- `A +ᴿᴹ B =ᴿᴹ C` — addition relation on `Mset`s (`RBI.Mset.radd`), auxiliary to `+` on `RProp`

## Architecture

The library root is `RapunSL.lean` → `RapunSL.Math` + `RapunSL.Logic`. The layering (each layer builds on the previous):

1. **`RapunSL/Math/Mset/`** — possibly-infinite multisets. `Ifam` (indexed family) quotiented by index-set equivalence gives `Mset` (`Core.lean`); then bijections (`Bij`), the disjoint-union operation `⊕ᴹ` (`Oplus`), products, a monad structure (`Monad`), infinite sums (`InfiniteSum`), and `Mseti` — inhabited multisets `{ A : Mset α // A.inhab }` (`Mseti.lean`).

   **Caution — this multiset library is unusual.** There is no multiplicity (element-count) function; do not think of an `Mset` as "each element with a count". Instead, reason in terms of the library's own vocabulary: bijections `≃ᴹ` (`Mset.Bij`, an `Equiv` between index domains) and their `graph` (the multiset of pairs, with projections `graph_fst`/`graph_snd`), the map operation `<$>ᴹ` (`<$>ᴹⁱ` for `Mseti`), `⊕ᴹ`/`⨁ᴹ`, `<*>ᴹ`, `>>=ᴹ`, and the existing lemmas about them. As a rule, do not descend into the underlying `Ifam` world (`.out`, `⟦ ⟧`, `Quotient` reasoning, `ᴵ`-superscripted operations): stay at the `Mset`/`Mseti` level and prove new `Mset` lemmas from existing `Mset` lemmas, dropping to `Ifam` only when adding a genuinely new primitive to the library.

2. **`RapunSL/Math/Algebra/`** — the resource-algebra hierarchy in `PCM.lean` and `RR.lean`:
   `CommMonoid'` → `PCM` (partial commutative monoid with validity `✓`) → `PCMI` (adds incompatibility `#`) → `PCMC` (coherence) and `PCMP` (probability/weights via `ENNReal`) → `RR` (resource ring, combining `PCMC` and `PCMP`).
   `Algebra/Mseti.lean` lifts algebra structure to inhabited multisets and defines `Msetiv α = { A : Mseti α // ✓ A }` (valid inhabited multisets), the carrier of the model.

3. **`RapunSL/Logic/`** — the logic itself:
   - `BI.lean`: utilities over iris-lean's `BI` type class (preorder/equivalence instances for `⊢`/`⊣⊢`, connective reinterpretations).
   - `RBI/Core.lean`: RapunSL's model — `RProp ρ [RR ρ] = DiscreteO (Set (Msetiv ρ))` with its `BIBase`/`BI` instances (entailment is set inclusion, separating conjunction via the PCM).
   - `RBI/Bmix.lean`: bare mixing connectives (`⊕`, big mixing `⨁`, and its adjoint).
   - `RBI/Add.lean`: the sum connective `+` on `RProp` (via `RProp.instAdd`). The relation `Mset.radd` (notation `A +ᴿᴹ B =ᴿᴹ C`, "adding multisets `A` and `B` can yield `C`") is only an auxiliary definition used to state it.

When adding a file, create it under the matching directory and add a `public import` for it in the directory's umbrella module (`Mset.lean`, `Algebra.lean`, `RBI.lean`, etc.), which is how everything reaches the root.

## Proof tips

Lessons learned working in this codebase:

- **`<$>` vs `<$>ᴹ`.** Use `<$>ᴹ` (`Mset.map`) in definitions and lemma statements, as the library does. The generic `<$>` (`Functor.map`) is defeq but not syntactically equal to it, and lemmas come in matching variants — primed for `<$>ᴹ` (`Mset.map'_mem`, `Mset.inhab_map'`), unprimed for `<$>` (`Mset.map_mem`, `Mset.inhab_map`). Pick the variant matching the goal; `Mset.map_unfold` rewrites `<$>` into `<$>ᴹ` where the two meet.
- **Finish `rw` chains with an explicit `rfl`.** After fusing maps with `←Mset.comp_map`, the two sides are usually defeq (match-lambdas vs compositions of projections reduce via structure eta) but not syntactically equal. `rw`'s automatic `rfl` only works up to reducible transparency, so append `; rfl`. When a rewrite unexpectedly fails to match, compare your lemma statement against the goal printout in the error — `simp` can, e.g., turn a pattern-match lambda `fun (a, b) ↦ a + b` into projection form `fun x ↦ x.1 + x.2`.
- **Motive failures when rewriting near `Bij.graph`.** For `r : A ≃ᴹ B`, the term `r.graph` carries `A` and `B` as implicit arguments. Rewriting `A` in a goal that also contains `r.graph` somewhere (even deep inside another bijection's implicit arguments) makes the motive ill-typed; restrict the rewrite with `rw (occs := [1]) [...]`.
- **Strategy for graph-defined relations (like `Mset.radd`).** To combine two such relations (e.g. for associativity), compose the given bijections (`Mset.Bij.map_l`/`map_r` with `.trans`) into a single bijection and take its graph: a multiset of nested tuples of which every multiset in sight becomes a `<$>ᴹ`-image under a projection, and membership in it yields the pointwise hypotheses (coherence etc.) to push through the corresponding pointwise algebra lemma (e.g. `RR.radd_assoc_l`). Useful general lemmas: `Mset.map_congr` (maps agree when the functions agree on members — needed because pointwise facts like associativity of `+` hold only under coherence, so `funext` is unavailable), `Mset.Bij.graph_unmap_l` (turn a bijection out of `f <$>ᴹ T` into a multiset of pairs projecting to `T` and the codomain), and `RBI.pairs_radd` (build `+ᴿᴹ` from a multiset of coherent pairs). See the proof of `radd_assoc_l` in `RBI/Add.lean` for the pattern in action.
