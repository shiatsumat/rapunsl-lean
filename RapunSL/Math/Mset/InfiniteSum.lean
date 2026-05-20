module

public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import RapunSL.Math.Mset.Oplus
public import RapunSL.Math.Mset.Prod
open Ifam Mset ENNReal

@[expose] public section

/-! # Infinite products and sums over multisets -/

/-! ## Definition -/

section CommMonoid
variable {κ} [CommMonoid κ] [TopologicalSpace κ]

/-- Infinite product over an indexed family -/
@[to_additive /-- Infinite sum over an indexed family -/]
protected noncomputable def Ifam.tprod (k : α → κ) (A : Ifam α) : κ :=
  ∏' i, k (A.elem i)

@[inherit_doc Ifam.tprod]
scoped[Ifam] notation "∏ᴵ " a " ∈ᴵ " A ", " b:67 => Ifam.tprod (fun a => b) A

@[inherit_doc Ifam.tsum]
scoped[Ifam] notation "∑ᴵ " a " ∈ᴵ " A ", " b:67 => Ifam.tsum (fun a => b) A

@[to_additive]
protected lemma Ifam.tprod_proper {α} A B (k : α → κ) :
    A ≈ B → ∏ᴵ a ∈ᴵ A, k a = ∏ᴵ b ∈ᴵ B, k b := by
  have ⟨ι, A⟩ := A; have ⟨ι', B⟩ := B; rintro ⟨ιι', AB⟩; simp only at *;
  trans; swap; { apply Equiv.tprod_eq ιι' }; simp only [Ifam.tprod]; congr;  ext1 _; rw [AB]

/-- Infinite product over a multiset -/
@[to_additive /-- Infinite sum over a multiset -/]
protected noncomputable def Mset.tprod (k : α → κ) : Mset α → κ :=
  Quotient.lift (Ifam.tprod k) <| by intro _ _; apply Ifam.tprod_proper

@[inherit_doc Mset.tprod]
scoped[Mset] notation "∏ᴹ " a " ∈ᴹ " A ", " b:67 => Mset.tprod (fun a => b) A

@[inherit_doc Mset.tsum]
scoped[Mset] notation "∑ᴹ " a " ∈ᴹ " A ", " b:67 => Mset.tsum (fun a => b) A

/-! ## Properties -/

@[to_additive]
protected lemma Mset.tprod_map' (f : α → β) (k : β → κ) A :
    Mset.tprod k (f <$>ᴹ A) = ∏ᴹ a ∈ᴹ A, k (f a) := by
  cases A using Quotient.ind; rfl

@[to_additive]
protected lemma Mset.tprod_map (f : α → β) (k : β → κ) A :
    Mset.tprod k (f <$> A) = ∏ᴹ a ∈ᴹ A, k (f a) := by
  cases A using Quotient.ind; rfl

@[to_additive]
protected lemma Mset.tprod_empty (k : α → κ) :
    Mset.tprod k ∅ = 1 := by apply tprod_empty

@[to_additive]
protected lemma Mset.tprod_pure (k : α → κ) a :
    Mset.tprod k (pure a) = k a := by
  apply tprod_eq_mulSingle; { intro (); tauto }

section ContinuousMul
variable [ContinuousMul κ]

@[to_additive]
protected lemma Mset.tprod_oplus [T2Space κ] (k : α → κ) A B :
    (∀ ι : Type, ∀ k : ι → κ, Multipliable k) →
    Mset.tprod k (A ⊕ᴹ B) = Mset.tprod k A * Mset.tprod k B := by
  intro mul; cases A using Quotient.ind; cases B using Quotient.ind;
  apply Multipliable.tprod_sum <;> apply mul

@[to_additive]
protected lemma Mset.tprod_bigoplus [T3Space κ] (k : α → κ) (A : ι → Mset α) :
    (∀ ι : Type, ∀ k : ι → κ, Multipliable k) →
    Mset.tprod k (Mset.bigoplus A) = ∏' i, Mset.tprod k (A i) := by
  intro mul; trans;
  { apply Multipliable.tprod_sigma' <;> intros <;> apply mul };
  simp only [Ifam.bigoplus_elem]; congr; ext1 i; cases A i using Quotient.ind;
  apply Ifam.tprod_proper; apply Quotient.mk_out

@[to_additive tsum_prod]
protected lemma Mset.tprod_prod [T3Space κ] (k : α × β → κ) A B :
    (∀ ι : Type, ∀ k : ι → κ, Multipliable k) →
    Mset.tprod k (A ×ᴹ B) = ∏ᴹ a ∈ᴹ A, ∏ᴹ b ∈ᴹ B, k (a, b) := by
  intro mul; cases A using Quotient.ind; cases B using Quotient.ind;
  apply Multipliable.tprod_prod' <;> intros <;> apply mul

end ContinuousMul

end CommMonoid

section TopologicalSemiring
variable {κ} [NonUnitalNonAssocSemiring κ] [TopologicalSpace κ]
  [IsTopologicalSemiring κ]

protected lemma Mset.tsum_mul_left [T2Space κ] (k : α → κ) A l :
    (∀ ι : Type, ∀ k : ι → κ, Summable k) →
    ∑ᴹ a ∈ᴹ A, l * k a = l * Mset.tsum k A := by
  intro sum; cases A using Quotient.ind; apply Summable.tsum_mul_left; apply sum

protected lemma Mset.tsum_mul_right [T2Space κ] (k : α → κ) A l :
    (∀ ι : Type, ∀ k : ι → κ, Summable k) →
    ∑ᴹ a ∈ᴹ A, k a * l = Mset.tsum k A * l := by
  intro sum; cases A using Quotient.ind; apply Summable.tsum_mul_right; apply sum

protected lemma Mset.tsum_mul_tsum [T3Space κ] (k : α → κ) (l : β → κ) A B :
    (∀ ι : Type, ∀ k : ι → κ, Summable k) →
    Mset.tsum k A * Mset.tsum l B = ∑ᴹ (a, b) ∈ᴹ A ×ᴹ B, k a * l b := by
  intro sum; cases A using Quotient.ind; cases B using Quotient.ind;
  apply Summable.tsum_mul_tsum <;> apply sum

end TopologicalSemiring

section ENNReal

protected lemma ENNReal.Mset.tsum_bigoplus (k : α → ℝ≥0∞) (A : ι → Mset α) :
    Mset.tsum k (Mset.bigoplus A) = ∑' i, Mset.tsum k (A i) := by
  apply _root_.Mset.tsum_bigoplus; intros; apply ENNReal.summable

protected lemma ENNReal.Mset.tsum_oplus (k : α → ℝ≥0∞) A B :
    Mset.tsum k (A ⊕ᴹ B) = Mset.tsum k A + Mset.tsum k B := by
  apply _root_.Mset.tsum_oplus; intros; apply ENNReal.summable

protected lemma ENNReal.Mset.tsum_prod (k : α × β → ℝ≥0∞) A B :
    Mset.tsum k (A ×ᴹ B) = ∑ᴹ a ∈ᴹ A, ∑ᴹ b ∈ᴹ B, k (a, b) := by
  apply _root_.Mset.tsum_prod; intros; apply ENNReal.summable

protected lemma ENNReal.Mset.tsum_mul_left (k : α → ℝ≥0∞) A l :
    ∑ᴹ a ∈ᴹ A, l * k a = l * Mset.tsum k A := by
  cases A using Quotient.ind; apply ENNReal.tsum_mul_left

protected lemma ENNReal.Mset.tsum_mul_right (k : α → ℝ≥0∞) A l :
    ∑ᴹ a ∈ᴹ A, k a * l = Mset.tsum k A * l := by
  cases A using Quotient.ind; apply ENNReal.tsum_mul_right

protected lemma ENNReal.Mset.tsum_mul_tsum (k : α → ℝ≥0∞) (l : β → ℝ≥0∞) A B :
    Mset.tsum k A * Mset.tsum l B = ∑ᴹ (a, b) ∈ᴹ A ×ᴹ B, k a * l b := by
  rw [ENNReal.Mset.tsum_prod, ←ENNReal.Mset.tsum_mul_right];
  congr; ext1 _; rw [ENNReal.Mset.tsum_mul_left]

end ENNReal
