module

public import RapunSL.Util.Syntax
public import Mathlib.Algebra.Group.WithOne.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod

@[expose] public section

/-! # Products and sums over finite inhabited types -/

/-! ## Finite inhabited types -/

/-- Finite inhabited type -/
class abbrev FiniType (ι : Type*) := Inhabited ι, Fintype ι

/-- Product preserves `FiniType` -/
instance FiniType.prod {ι ι' : Type*} [FiniType ι] [FiniType ι'] : FiniType (ι × ι') :=
  inferInstance

/-! ## Product/sum over finite inhabited sets -/

section finiprod
variable {ι ι' : Type*} [FiniType ι] [FiniType ι']
  {α : Type*} [CommSemigroup α]

/-- Prelimary definition of `∏ᶠⁱ` -/
@[to_additive finisum' /-- Prelimary definition of `∑ᶠⁱ` -/]
def finiprod' (a : ι → α) : WithOne α :=
  ∏ i, (a i : WithOne α)

/-- `∏ᶠⁱ` is not `1` -/
@[to_additive finisum'_ne_zero /-- `∑ᶠⁱ` is not `0` -/]
lemma finiprod'_ne_one (a : ι → α) : finiprod' a ≠ 1 := by
  refine Finset.prod_induction_nonempty _ (· ≠ 1) ?_ Finset.univ_nonempty
    fun i _ => WithOne.coe_ne_one
  intro x y nex ney
  rcases WithOne.ne_one_iff_exists.mp nex with ⟨b, rfl⟩
  rcases WithOne.ne_one_iff_exists.mp ney with ⟨c, rfl⟩
  rw [←WithOne.coe_mul]; exact WithOne.coe_ne_one

/-- Product over finite inhabited sets -/
@[to_additive finisum /-- Sum over finite inhabited sets -/]
def finiprod (a : ι → α) : α :=
  (finiprod' a).unone <| finiprod'_ne_one _

/-- `∏ᶠⁱ` mapped into `WithOne` -/
@[to_additive coe_finisum /-- `∑ᶠⁱ` mapped into `WithZero` -/]
lemma coe_finiprod (a : ι → α) : (↑(finiprod a) : WithOne α) = finiprod' a :=
  WithOne.coe_unone _

@[inherit_doc finiprod]
scoped[Finiprod] notation "∏ᶠⁱ " i ", " a:67 => finiprod (fun i => a)

@[inherit_doc finisum]
scoped[Finisum] notation "∑ᶠⁱ " i ", " a:67 => finisum (fun i => a)

open Finiprod Finisum

/-- Product over a unique type -/
@[to_additive finisum_unique /-- Sum over a unique type -/]
lemma finiprod_unique [Unique ι] (i : ι) (a : ι → α) : ∏ᶠⁱ j, a j = a i := by
  apply WithOne.coe_inj.mp; rw [coe_finiprod]
  exact Fintype.prod_subsingleton _ i

/-- Modifying `∏ᶠⁱ` with a bijection -/
@[to_additive finisum_bij /-- Modifying `∑ᶠⁱ` with a bijection -/]
lemma finiprod_bij (f : ι ≃ ι') (a : ι' → α) :
    ∏ᶠⁱ i, a (f i) = ∏ᶠⁱ i', a i' := by
  apply WithOne.coe_inj.mp; rw [coe_finiprod, coe_finiprod]
  exact Equiv.prod_comp f fun i' => (a i' : WithOne α)

/-- Modifying `∏ᶠⁱ` with a bijection -/
@[to_additive finisum_bij' /-- Modifying `∑ᶠⁱ` with a bijection -/]
lemma finiprod_bij' (f : ι ≃ ι') (a : ι → α) (a' : ι' → α) :
    (∀ i, a i = a' (f i)) → ∏ᶠⁱ i, a i = ∏ᶠⁱ i', a' i' := by
  intro eq; rw [←finiprod_bij f a']
  exact congrArg finiprod (funext eq)

/-- Product over a product -/
@[to_additive (attr := simp) finisum_prod /-- Sum over a product -/]
lemma finiprod_prod (a : ι → ι' → α) :
    ∏ᶠⁱ i, ∏ᶠⁱ i', a i i' = ∏ᶠⁱ (i, i'), a i i' := by
  apply WithOne.coe_inj.mp
  simp only [coe_finiprod, finiprod', Fintype.prod_prod_type]

/-- `∏ᶠⁱ` over `∏ᶠⁱ` -/
@[to_additive finisum_comm /-- `∑ᶠⁱ` over `∑ᶠⁱ` -/]
lemma finiprod_finiprod (a : ι → ι' → α) :
    ∏ᶠⁱ i, ∏ᶠⁱ i', a i i' = ∏ᶠⁱ i', ∏ᶠⁱ i, a i i' := by
  simp only [finiprod_prod]; apply finiprod_bij' (Equiv.prodComm _ _); tauto

/-- Transfer a multiplication-compatible relation to `∏ᶠⁱ`s -/
@[to_additive finisum_rel /-- Transfer an addition-compatible relation to `∑ᶠⁱ`s -/]
lemma finiprod_rel {β : Type*} [CommSemigroup β] (r : α → β → Prop) (a : ι → α) (b : ι → β) :
    (∀ x y x' y', r x y → r x' y' → r (x * x') (y * y')) →
    (∀ i, r (a i) (b i)) → r (finiprod a) (finiprod b) := by
  intro mul rel
  have key : ∃ (c : α) (d : β),
      (∏ i, ((a i : WithOne α), (b i : WithOne β))).1 = ↑c ∧
      (∏ i, ((a i : WithOne α), (b i : WithOne β))).2 = ↑d ∧ r c d := by
    apply Finset.prod_induction_nonempty _
      (fun x : WithOne α × WithOne β => ∃ (c : α) (d : β), x.1 = ↑c ∧ x.2 = ↑d ∧ r c d)
      ?_ Finset.univ_nonempty fun i _ => ⟨a i, b i, rfl, rfl, rel i⟩
    rintro x y ⟨c, d, hc, hd, rcd⟩ ⟨c', d', hc', hd', rcd'⟩
    refine ⟨c * c', d * d', ?_, ?_, mul _ _ _ _ rcd rcd'⟩
    · rw [Prod.fst_mul, hc, hc', WithOne.coe_mul]
    · rw [Prod.snd_mul, hd, hd', WithOne.coe_mul]
  rcases key with ⟨c, d, hc, hd, rcd⟩
  rw [Prod.fst_prod] at hc; rw [Prod.snd_prod] at hd
  obtain rfl : finiprod a = c := WithOne.coe_inj.mp ((coe_finiprod a).trans hc)
  obtain rfl : finiprod b = d := WithOne.coe_inj.mp ((coe_finiprod b).trans hd); exact rcd

end finiprod
