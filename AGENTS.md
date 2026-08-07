# AGENTS.md

This file provides guidance to coding agents (such as Claude Code) when working with code in this repository.

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
- Definitions and lemmas that belong to a type's namespace are typically declared `protected`.
- Lemma signatures bind only data (multisets, bijections, elements) by name; proof obligations are stated as a chain of `→`s after the colon and bound with `intro`/`rintro` at the start of the proof, not as named hypothesis binders in the signature (e.g. `lemma rmadd_comm' : A +ᴿᴹ B =ᴿᴹ C → B +ᴿᴹ A =ᴿᴹ C`).
- Notation is introduced with `scoped` prefixes/macros inside the relevant namespace, so `open` the namespace to use it.
- `RapunSL/Util/Syntax.lean` provides the `delab_rules` command (a shorthand for `app_unexpander`) used to pretty-print custom notation.
- Adding general-purpose lemmas to the library layers is welcome: when a proof needs a reusable fact about, say, `Mset` or the algebra classes, state it in the appropriate library file (e.g. `Mset/Bij.lean`) rather than keeping it local to the use site.
- Keep individual proofs from growing too long, for readability: factor out auxiliary lemmas as appropriate.

## Naming conventions

- Type variables: `α`, `β`, `γ` for generic types (primed `α'`, `β'` for modified copies), `ι` for index types, `σ` for a generic index type, and `ρ` for the resource-ring carrier in `Logic/`.
- Multisets (`Ifam`/`Mset`/`Mseti`/`Msetiv`) are uppercase `A`, `B`, `C`, …, and their elements the matching lowercase (`a ∈ A`, `b ∈ B`); combined multisets concatenate the names (`AB`, `ABC`, `BC` for sums). `S` is a multiset of pairs/tuples serving as a common index (as in `pairs_radd`, `radd_map`, `Mset.Bij.graph_unmap_l`). `F` is a multiset of functions, `K` a monadic continuation (`α → Mset β`). `i`, `j` are `Ifam` indices, `p` a pair.
- Functions are `f`, `g`; bijections are `r`, `s` (`r : A ≃ᴹ B`, `s : B ≃ᴹ C`); `e` is an equivalence or equality proof.
- Algebra elements are `a`, `b`, `c` (also `r`, `s` for owned resources in `Logic/`); `RProp`s are `P`, `Q`, `R` (primed `P'`, `Q'`); probabilities are `p`, `q`.
- Witnesses and proofs of a relation between `X` and `Y` are often named `XY` (`AB : A ≃ᴹ B` in `Mset.radd`, `PP' : P ⊢ P'`). Common hypothesis names: `coh` (coherence), `val` (validity), `inc` (incompatibility), `inh` (inhabitedness), `mem` (membership in a multiset), `elP` (membership in the proposition `P`), `eq` (an equation).

## Notation

Superscripts tag the level an operator lives at: `ᴵ` = `Ifam`, `ᴹ` = `Mset`, `ᴹⁱ` = `Mseti` (e.g. `<$>ᴹ`, `⊕ᴹⁱ`, `⨁ᴹ`, `≃ᴹ`, `×ᴹ`, `<*>ᴹ`, `>>=ᴹ` and their variants at each level).

Finite products/sums (scoped in `Finiprod`, `Finisum`):

- `∏ᶠⁱ i, a i`, `∑ᶠⁱ i, a i` — product/sum over a finite inhabited type (`finiprod`, `finisum`)

Algebra (scoped in `PCM`, `PCMI`, `PCMC`, `RR`):

- `✓ a` — validity (`PCM.valid`)
- `a # b` — incompatibility (`PCMI.incomp`)
- `a ≎ b` — coherence (`PCMC.coher`)
- `a +ᴿ b =ᴿ c` — addition relation in a resource ring (`RR.radd`)

Logic, over any BI (unscoped, from `Logic/BI.lean`):

- `P =ᴮᴵ Q` — equality of BI propositions, with both sides elaborated as `iprop`; used to state connective laws as equalities. Over a `BIE` (BI with extensionality, e.g. `RProp`), prove it by `ext1`, which reduces the goal to `⊣⊢`.

Logic, over `RProp` (scoped in `RBI`):

- `P ⊕ Q`, `⨁ i, P i` — bare mixing (`bmix`, `bigbmix`); `P -⊕ Q` — pine, the right adjoint of `⊕`
- `P + Q`, `∑ᶠⁱ i, P i` — sum connectives: the ordinary generic `+` and `∑ᶠⁱ`, via instances on `RProp`; `P -+ Q` — cross, the right adjoint of `+`
- `P #ᴿ Q` — incompatibility of propositions (`Incomp`); `P ≎ᴿ Q` — coherence of propositions (`Coher`)
- `A +ᴿᴹ B =ᴿᴹ C` — addition relation on `Mset`s (`RBI.rmadd`), auxiliary to `+` on `RProp`

## Architecture

The library root is `RapunSL.lean` → `RapunSL.Math` + `RapunSL.Logic`. The layering (each layer builds on the previous):

1. **`RapunSL/Math/Mset/`** — possibly-infinite multisets. `Ifam` (indexed family) quotiented by index-set equivalence gives `Mset` (`Core.lean`); then bijections (`Bij`), the disjoint-union operation `⊕ᴹ` (`Oplus`), products, a monad structure (`Monad`), infinite sums (`InfiniteSum`), and `Mseti` — inhabited multisets `{ A : Mset α // A.inhab }` (`Mseti.lean`).

   **Caution — this multiset library is unusual.** There is no multiplicity (element-count) function; do not think of an `Mset` as "each element with a count". Instead, reason in terms of the library's own vocabulary: bijections `≃ᴹ` (`Mset.Bij`, an `Equiv` between index domains) and their `graph` (the multiset of pairs, with projections `graph_fst`/`graph_snd`), the map operation `<$>ᴹ` (`<$>ᴹⁱ` for `Mseti`), `⊕ᴹ`/`⨁ᴹ`, `<*>ᴹ`, `>>=ᴹ`, and the existing lemmas about them. As a rule, do not descend into the underlying `Ifam` world (`.out`, `⟦ ⟧`, `Quotient` reasoning, `ᴵ`-superscripted operations): stay at the `Mset`/`Mseti` level and prove new `Mset` lemmas from existing `Mset` lemmas, dropping to `Ifam` only when adding a genuinely new primitive to the library.

2. **`RapunSL/Math/Algebra/`** — the resource-algebra hierarchy in `PCM.lean` and `RR.lean`:
   `CommMonoid'` → `PCM` (partial commutative monoid with validity `✓`) → `PCMI` (adds incompatibility `#`) → `PCMC` (coherence) and `PCMP` (probability/weights via `ENNReal`) → `RR` (resource ring, combining `PCMC` and `PCMP`).
   `Algebra/Mseti.lean` lifts algebra structure to inhabited multisets and defines `Msetiv α = { A : Mseti α // ✓ A }` (valid inhabited multisets), the carrier of the model.
   `Algebra/Finiprod.lean` defines `Finitype` (finite inhabited types) and the product `∏ᶠⁱ` of a `CommSemigroup`-valued and the sum `∑ᶠⁱ` of an `AddCommSemigroup`-valued family over a `Finitype`.

   **Caution — for `RR`, work with `+`, not `radd`.** The relation `radd` (`+ᴿ`) is only the primitive underlying the total addition `+`. Downstream proofs should stay in the `+` world and use its lemmas (`RR.add_assoc`, `RR.add_coher_l`/`r`, `RR.add_valid_l`/`r`, …). When a fact about `+` is missing, add it as a lemma in `Algebra/RR.lean` (where proving it via `radd` is fine) rather than reaching for `radd` at the use site.

3. **`RapunSL/Logic/`** — the logic itself:
   - `BI.lean`: utilities over iris-lean's `BI` type class (preorder/equivalence instances for `⊢`/`⊣⊢`, connective reinterpretations), the `BIE` class (BI with extensionality: `⊣⊢` implies `=`, registered `@[ext]`), and the `=ᴮᴵ` notation.
   - `RBI/Core.lean`: RapunSL's model — `RProp ρ [RR ρ] = DiscreteO (Set (Msetiv ρ))` with its `BIBase`/`BI` instances (entailment is set inclusion, separating conjunction via the PCM).
   - `RBI/Bmix.lean`: bare mixing connectives (`⊕`, big mixing `⨁`, and its adjoint).
   - `RBI/Add.lean`: the sum connectives on `RProp` — the binary `+`, its right adjoint `-+` (`cross`), and the finite sum `∑ᶠⁱ`. Here `+` and `∑ᶠⁱ` are the generic operations, not bespoke notation: `+` is Lean's `HAdd.hAdd` via `RProp.instAdd`/`instAddCommSemigroup` (so `add_comm`/`add_assoc` and other generic lemmas apply), and `∑ᶠⁱ` is `Finisum`'s `finisum` instantiated through that `AddCommSemigroup` instance. The relation `RBI.rmadd` (notation `A +ᴿᴹ B =ᴿᴹ C`, "adding multisets `A` and `B` can yield `C`") is only an auxiliary definition used to state `+`.

When adding a file, follow the `new-module` skill (`.claude/skills/new-module/SKILL.md`): it covers placement, the module-system boilerplate, and registration in the directory's umbrella module.

## Proof tips

Lessons learned working in this codebase:

- **`<$>` vs `<$>ᴹ`.** Use `<$>ᴹ` (`Mset.map`) in definitions and lemma statements, as the library does. The generic `<$>` (`Functor.map`) is defeq but not syntactically equal to it, and lemmas come in matching variants — primed for `<$>ᴹ` (`Mset.map'_mem`, `Mset.inhab_map'`), unprimed for `<$>` (`Mset.map_mem`, `Mset.inhab_map`). Pick the variant matching the goal; `Mset.map_unfold` rewrites `<$>` into `<$>ᴹ` where the two meet.
- **Finish `rw` chains with an explicit `rfl`.** After fusing maps with `←Mset.comp_map`, the two sides are usually defeq (match-lambdas vs compositions of projections reduce via structure eta) but not syntactically equal. `rw`'s automatic `rfl` only works up to reducible transparency, so append `; rfl`. When a rewrite unexpectedly fails to match, compare your lemma statement against the goal printout in the error — `simp` can, e.g., turn a pattern-match lambda `fun (a, b) ↦ a + b` into projection form `fun x ↦ x.1 + x.2`.
- **Motive failures when rewriting near `Bij.graph`.** For `r : A ≃ᴹ B`, the term `r.graph` carries `A` and `B` as implicit arguments. Rewriting `A` in a goal that also contains `r.graph` somewhere (even deep inside another bijection's implicit arguments) makes the motive ill-typed; restrict the rewrite with `rw (occs := [...]) [...]`. When picking the occurrence number, remember that the hidden occurrences inside `r.graph`'s implicit arguments are counted too, so the visible occurrence you want is often `[2]` or later.
- **Strategy for graph-defined relations (like `RBI.rmadd`).** Reduce to a single common multiset whose membership yields the pointwise hypotheses (coherence etc.): compose the given bijections (`Mset.Bij.map_l`/`map_r` with `.trans`) and take its graph when combining two relations, or take `A ×ᴹ r.graph` when combining with a pointwise product. Every multiset in sight is then a `<$>ᴹ`-image of it; `RBI.pairs_rmadd`/`RBI.rmadd_map` rebuild `+ᴿᴹ`, and `Mset.map_congr` pushes pointwise algebra lemmas (`RR.radd_assoc_l`, `RR.add_mul_l`) through the maps (`funext` is unavailable — those facts hold only under coherence). `Mset.Bij.graph_unmap_l` unpacks a bijection out of `f <$>ᴹ A` into a multiset of pairs. To cancel a common `*`-frame out of `+ᴿᴹ`, conjugate the bijection with `Mset.Bij.map_r`/`map_l` into a bijection between the underlying `×ᴹ`-products and apply `Mset.Bij.prod_cancel_l` (first-component preservation follows from incompatibility via `PCMI.incomp_mul_l` and `PCMC.incomp_neg_coher`, uniqueness of the result from `rmadd_unique_l`). See `rmadd_assoc_l`/`rmadd_mul_l`/`rmadd_mul_inv_l` in `RBI/Add.lean`.
- **Adding an `Ifam`-level primitive and lifting it to `Mset`.** Prove the `Ifam` version first, then transport (see `Mset.Bij.prod_cancel_l` in `Mset/Prod.lean`). To align `(A ×ᴹ B).out` with `A.out ×ᴵ B.out`, derive the `≈` by `apply Quotient.exact; rw [Mset.out_eq]; rw (occs := [1]) [←A.out_eq]; …; rfl` and turn it into a bijection with `Ifam.Bij.lift_equiv`; its graph is identity-shaped (`lift_equiv_graph_mem`), so `Ifam.Bij.trans_graph_id_l`/`r` show conjugating by it preserves the graph, and `Ifam.mem_proper` transfers membership across the resulting `≈`.
- **Dot notation picks the wrong level when mixing `≃ᴹ` and `≃ᴵ`.** On `r : A ≃ᴹ B`, dot notation like `r.trans` resolves to the `Mset.Bij` version, whose other endpoints must be `.out`s of `Mset`s; when composing with a genuine `Ifam` bijection, write `Ifam.Bij.trans` explicitly (both `Bij`s are abbrevs for `Equiv` over index domains, so the levels unify definitionally).
- **Near `Ifam` index types, prefer `exact`-level defeq over `rw`.** `(A ×ᴵ B).dom` unfolds to `A.dom × B.dom` only semireducibly, so `rw` there can fail with ill-typed motives. Assemble equalities with `congrArg` (plus `Equiv.apply_symm_apply`/`symm_apply_apply`) and pass them to `exact`, which checks at full transparency; close pair goals like `r p = (p.1, (r p).2)` with an explicit `rfl` — structure eta for `Prod` is definitional.
- **Relating `Mseti` multiplication to `Mset` combinators.** `(A * B).val` unfolds by `Mseti.mul_val` into the generic `HMul.hMul <$> A.val <*> B.val`; follow with `Mset.map_seq` to reach `Function.uncurry HMul.hMul <$> (A.val ×ᴹ B.val)` and `Mset.map_unfold` to turn `<$>` into `<$>ᴹ`. From there the `×ᴹ` lemmas (`Mset.prod_map'_r`, `←Mset.comp_map`, …) apply, ending in the usual `; rfl`.
- **Use `change`, not `show`, to restate a goal up to defeq.** The Mathlib linter set flags `show` whenever it actually changes the goal (e.g. reducing a pattern-match lambda applied to a tuple after `rintro`); `change` is the accepted tactic for that.
- **`Msetiv` equality and validity.** `Msetiv α = { A : Mseti α // ✓ A }` is a subtype of a subtype: prove `Msetiv` equality with two `Subtype.ext`s, reducing to `Mset` equality. For `A : Msetiv α`, `A.prop : ✓ A.val` is definitionally `∀ a ∈ A.val.val, ✓ a` and can be passed directly where the latter is expected. Use `.prop`, not the longer `.property`.
- **New `finiprod`/`finisum` lemmas go through `WithOne`/`WithZero`.** `finiprod` is defined by lifting into `WithOne α`: prove facts by moving the goal there with `coe_finiprod`, inducting over the product with `Finset.prod_induction_nonempty` (nonemptiness from `Finset.univ_nonempty`), and pulling the result back along `WithOne.coe_inj`. To relate two `finiprod`s pointwise, take the product of pairs in `WithOne α × WithOne β` and split it with `Prod.fst_prod`/`Prod.snd_prod` — or use `finiprod_rel`/`finisum_rel`, which packages this for any multiplication-compatible relation (see `finisum_mono` in `RBI/Add.lean` for a use).
