module

public import RapunSL.Util.Syntax
public import Mathlib.Algebra.Group.WithOne.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! # Products and sums over finite inhabited types -/

/-! ## Finite inhabited types -/

/-- Finite inhabited type -/
class abbrev Finitype (ι : Type*) := Inhabited ι, Fintype ι

namespace Finitype

/-- Cardinality minus 1 for `Finitype` -/
protected def card (ι : Type*) [Finitype ι] : ℕ :=
  (Fintype.card ι).pred

/-- `Fintype.card` is `Finitype.card` plus 1 -/
@[simp] protected lemma card_succ (ι : Type*) [Finitype ι] :
    Fintype.card ι = Finitype.card ι + 1 := by
  symm; apply Nat.succ_pred_eq_of_pos; apply Fintype.card_pos_iff.mpr; infer_instance

/-- Bijection between `Finitype` `ι` and `Fin` -/
protected noncomputable def equivFin {ι : Type*} [Finitype ι] :
    ι ≃ Fin (Finitype.card ι + 1) := by
  rw [←Finitype.card_succ]; apply Fintype.equivFin

end Finitype

/-! ## Product/sum over finite inhabited sets -/

section finiprod
variable {ι ι' : Type*} [Finitype ι] [Finitype ι']
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

/-- `∏ᶠⁱ` over a sigma type -/
@[to_additive (attr := simp) finisum_sigma /-- `∑ᶠⁱ` over a product -/]
lemma finiprod_sigma {ι' : ι → Type*} [∀ ι, Finitype (ι' ι)] (a : Sigma ι' → α) :
    ∏ᶠⁱ ii', a ii' = ∏ᶠⁱ i, ∏ᶠⁱ i', a ⟨i, i'⟩ := by
  apply WithOne.coe_inj.mp
  simp only [coe_finiprod, finiprod', Fintype.prod_sigma]

/-- Merge nested `∏ᶠⁱ` using a sigma type -/
@[to_additive finisum_sigma' /-- Merge nested `∑ᶠⁱ` using a sigma type -/]
lemma finiprod_sigma' {ι' : ι → Type*} [∀ ι, Finitype (ι' ι)] (a : ∀ i, ι' i → α) :
    ∏ᶠⁱ i, ∏ᶠⁱ i', a i i' = ∏ᶠⁱ (p : Sigma ι'), a p.1 p.2 := by
  symm; apply finiprod_sigma

/-- `∏ᶠⁱ` over a product type -/
@[to_additive (attr := simp) finisum_prod_type /-- `∑ᶠⁱ` over a product -/]
lemma finiprod_prod_type (a : ι × ι' → α) :
    ∏ᶠⁱ ii', a ii' = ∏ᶠⁱ i, ∏ᶠⁱ i', a (i, i') := by
  apply WithOne.coe_inj.mp
  simp only [coe_finiprod, finiprod', Fintype.prod_prod_type]

/-- Merge nested `∏ᶠⁱ` using a product type -/
@[to_additive finisum_prod_type' /-- Merge nested `∑ᶠⁱ` using a product type -/]
lemma finiprod_prod_type' (a : ι → ι' → α) :
    ∏ᶠⁱ i, ∏ᶠⁱ i', a i i' = ∏ᶠⁱ (p : ι × ι'), a p.1 p.2 := by
  symm; apply finiprod_prod_type

/-- Swap `∏ᶠⁱ`s -/
@[to_additive finisum_swap /-- Swap `∑ᶠⁱ`s -/]
lemma finiprod_swap (a : ι → ι' → α) :
    ∏ᶠⁱ i, ∏ᶠⁱ i', a i i' = ∏ᶠⁱ i', ∏ᶠⁱ i, a i i' := by
  simp only [finiprod_prod_type']; apply finiprod_bij' (Equiv.prodComm _ _); tauto

/-- `∏ᶠⁱ` over a sum type -/
@[to_additive (attr := simp) finisum_sum_type /-- `∑ᶠⁱ` over a sum type -/]
lemma finiprod_sum_type (a : ι ⊕ ι' → α) :
    ∏ᶠⁱ ii', a ii' = (∏ᶠⁱ i, a (Sum.inl i)) * (∏ᶠⁱ i', a (Sum.inr i')) := by
  apply WithOne.coe_inj.mp
  simp only [coe_finiprod, finiprod', Fintype.prod_sum_type, WithOne.coe_mul]

/-- Merge `*` over `∏ᶠⁱ` using a sum type -/
@[to_additive finisum_sum_type' /-- Merge `+` over `∑ᶠⁱ` using a sum type -/]
lemma finiprod_sum_type' (a : ι → α) (b : ι' → α) :
    (∏ᶠⁱ i, a i) * (∏ᶠⁱ i', b i') = ∏ᶠⁱ (ii' : ι ⊕ ι'), ii'.elim a b := by
  symm; apply finiprod_sum_type

/-- `∏ᶠⁱ` over an option type -/
@[to_additive (attr := simp) finisum_option /-- `∑ᶠⁱ` over an option type -/]
lemma finiprod_option (a : Option ι → α) :
    ∏ᶠⁱ i, a i = a none * ∏ᶠⁱ i, a (some i) := by
  apply WithOne.coe_inj.mp
  simp only [WithOne.coe_mul, coe_finiprod, finiprod', Fintype.prod_option]

/-- Merge `*` with `∏ᶠⁱ` using an option type -/
@[to_additive finisum_option' /-- Merge `+` with `∑ᶠⁱ` using an option type -/]
lemma finiprod_option' (a : α) (b : ι → α) :
    a * ∏ᶠⁱ i, b i = ∏ᶠⁱ (i : Option ι), i.elim a b := by
  symm; apply finiprod_option

/-- `∏ᶠⁱ` over `Fin (n + 1)` -/
@[to_additive (attr := simp) finisum_fin_succ /-- `∑ᶠⁱ` over `Fin (n + 1)` -/]
lemma finiprod_fin_succ (n : ℕ) (a : Fin ((n + 1) + 1) → α) :
    ∏ᶠⁱ i, a i = (∏ᶠⁱ (i : Fin (n + 1)), a i.castSucc) * a (Fin.last (n + 1)) := by
  rw [mul_comm, finiprod_option']; symm; apply finiprod_bij' finSuccEquivLast.symm
  rintro (_ | _); { simp only [Option.elim_none, finSuccEquivLast_symm_none] }
  { simp only [Option.elim_some, finSuccEquivLast_symm_some] }

/-- `∏ᶠⁱ` over `Fin 1` -/
@[to_additive (attr := simp) finisum_fin_one /-- `∑ᶠⁱ` over `Fin 1` -/]
lemma finiprod_fin_one (a : Fin 1 → α) :
    ∏ᶠⁱ i, a i = a 0 := by
  apply finiprod_unique

/-- `∏ᶠⁱ` into `∏ᶠⁱ` over `Fin` -/
@[to_additive finisum_fin /-- `∑ᶠⁱ` into `∑ᶠⁱ` over `Fin` -/]
lemma finiprod_fin (a : ι → α) :
    ∏ᶠⁱ i, a i = ∏ᶠⁱ i', a (Finitype.equivFin.symm i') := by
  symm; apply finiprod_bij

/-- Transfer a multiplication-compatible binary relation to `∏ᶠⁱ`s -/
@[to_additive finisum_rel /-- Transfer an addition-compatible binary relation to `∑ᶠⁱ`s -/]
lemma finiprod_rel {β : Type*} [CommSemigroup β] (r : α → β → Prop) (a : ι → α) (b : ι → β) :
    (∀ x y x' y', r x y → r x' y' → r (x * x') (y * y')) →
    (∀ i, r (a i) (b i)) → r (∏ᶠⁱ i, a i) (∏ᶠⁱ i, b i) := by
  intro rel; revert a b
  suffices h : ∀ n (a : Fin (n + 1) → α) (b : Fin (n + 1) → β),
      (∀ i, r (a i) (b i)) → r (∏ᶠⁱ i, a i) (∏ᶠⁱ i, b i) by
    intro a b _; rw [finiprod_fin a, finiprod_fin b]; apply h; tauto
  intro n; induction n with
  | zero => simp only [Nat.reduceAdd, Fin.forall_fin_one, finiprod_fin_one]; tauto
  | succ _ _ => simp only [finiprod_fin_succ]; intro _ _ _; apply rel <;> tauto

/-- Transfer a binary relation to `∏ᶠⁱ`s, multiplying one factor at a time -/
@[to_additive finisum_rel'
  /-- Transfer a binary relation to `∑ᶠⁱ`s, adding one summand at a time -/]
lemma finiprod_rel' {β : Type*} [CommSemigroup β] (r : α → β → Prop) (a : ι → α) (b : ι → β) :
    (∀ i x y, r x y → r (a i * x) (b i * y)) →
    (∀ i, r (a i) (b i)) → r (∏ᶠⁱ i, a i) (∏ᶠⁱ i, b i) := by
  intro _ _
  suffices _ : ∀ n (f : Fin (n + 1) → ι), r (∏ᶠⁱ k, a (f k)) (∏ᶠⁱ k, b (f k)) by
    rw [finiprod_fin a, finiprod_fin b]; tauto
  intro n; induction n with
  | zero => intro _; simp only [Nat.reduceAdd, finiprod_fin_one]; tauto
  | succ _ _ =>
    intro f; simp only [finiprod_fin_succ]
    rw [mul_comm _ (a (f (Fin.last _))), mul_comm _ (b (f (Fin.last _)))]; tauto

/-- Transfer a multiplication-compatible predicate to `∏ᶠⁱ`s -/
@[to_additive finisum_pred /-- Transfer an addition-compatible predicate to `∑ᶠⁱ`s -/]
lemma finiprod_pred (r : α → Prop) (a : ι → α) :
    (∀ x x', r x → r x' → r (x * x')) → (∀ i, r (a i)) → r (∏ᶠⁱ i, a i) := by
  intro _; apply finiprod_rel (fun _ => r) a; tauto

end finiprod
