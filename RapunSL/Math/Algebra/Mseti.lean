module

public import Mathlib.Algebra.Group.Defs
public import RapunSL.Math.Algebra.Core
public import RapunSL.Math.Mset
open Mset Mseti PCM PCMP

@[expose] public section

/-! # Algebra constructions for inhabited multisets -/

/-! ## Inhabited multiset PCM -/

/-- `*` for inhabited multisets -/
protected instance Mseti.instMul (α : Type u) [Mul α] : Mul (Mseti α) where
  mul A B := ⟨HMul.hMul <$> A.val <*> B.val, by
    simp only [Mset.inhab_seq, Mset.inhab_map]; grind only⟩

protected lemma Mseti.mul_val [Mul α] (A B : Mseti α) :
    (A * B).val = HMul.hMul <$> A.val <*> B.val := rfl

protected lemma Mseti.pure_mul [Mul α] (a b : α) :
    pure (f := Mseti) (a * b) = pure a * pure b := by
  ext; simp only [Mseti.mul_val, Mseti.pure_val, functor_norm]

protected lemma Mseti.mul_bigoplus_l [Mul α] [Inhabited ι] A (B : ι → Mseti α) :
    A * (⨁ᴹⁱ i, B i) = ⨁ᴹⁱ i, A * B i := by
  ext; simp only [Mseti.mul_val, Mseti.bigoplus_val, Mset.seq_bigoplus_l]

protected lemma Mseti.mul_bigoplus_r [Mul α] [Inhabited ι] (A : ι → Mseti α) B :
    (⨁ᴹⁱ i, A i) * B = ⨁ᴹⁱ i, A i * B := by
  ext; simp only [Mseti.mul_val, Mseti.bigoplus_val, Mset.bigoplus_map, Mset.seq_bigoplus_r]

protected lemma Mseti.mul_oplus_l [Mul α] (A B C : Mseti α) :
    A * (B ⊕ᴹⁱ C) = A * B ⊕ᴹⁱ A * C := by
  ext; simp only [Mseti.oplus_as_bigoplus, Mseti.mul_bigoplus_l]; grind only

protected lemma Mseti.mul_oplus_r [Mul α] (A B C : Mseti α) :
    (A ⊕ᴹⁱ B) * C = A * C ⊕ᴹⁱ B * C := by
  ext; simp only [Mseti.oplus_as_bigoplus, Mseti.mul_bigoplus_r]; grind only

@[simp] protected lemma Mseti.mem_mul [Mul α] (A B : Mseti α) a :
    (a ∈ (A * B).val) = ∃ b c, b ∈ A.val ∧ c ∈ B.val ∧ a = b * c := by
  simp only [Mseti.mul_val, Mset.mem_seq, Mset.mem_map, existsAndEq];
  ext1; tauto

@[simp] protected lemma Mseti.pairmem_mul [Mul α] (A B : Mseti α) c c' :
    (A * B).val.pairmem c c' =
      ∃ a a' b b', c = a * b ∧ c' = a' * b' ∧
        ((A.val.pairmem a a' ∧ B.val.pairmem b b') ∨
         (a = a' ∧ a ∈ A.val ∧ B.val.pairmem b b') ∨
         (b = b' ∧ b ∈ B.val ∧ A.val.pairmem a a')) := by
  simp only [Mseti.mul_val, Mset.map_seq, Mset.pairmem_map, Mset.pairmem_prod]; aesop

/-- `1` for multisets -/
protected instance Mseti.instOne (α : Type u) [One α] : One (Mseti α) where
  one := pure 1

protected lemma Mseti.one_unfold [PCM α] : (1 : Mseti α) = pure 1 := rfl

/-- Multiset PCM -/
protected instance Mseti.instPCM (α : Type u) [PCM α] : PCM (Mseti α) where
  one := pure 1
  mul_one _ := by
    ext; simp only [Mseti.mul_val, Mseti.one_unfold, Mseti.pure_val];
    rw [seq_pure, ←comp_map]; trans; swap; { apply id_map }; congr; grind only [mul_one, id_eq]
  mul_comm _ _ := by
    ext; simp only [Mseti.mul_val]; rw [CommApplicative.commutative_map]; congr;
    grind only [mul_comm]
  mul_assoc _ _ _ := by
    ext; simp only [Mseti.mul_val, functor_norm]; grind only [mul_assoc]
  valid A := ∀ a ∈ A.val, ✓ a
  valid_one := by
    simp only [Mseti.one_unfold, Mseti.pure_val, Mset.mem_pure, forall_eq]; apply PCM.valid_one
  valid_mul_l := by
    intro A ⟨B, ⟨b, _⟩⟩ val a _; apply PCM.valid_mul_l _ b;
    apply val; simp only [Mseti.mem_mul]; exists a, b

protected lemma Mseti.valid_unfold [PCM α] :
    PCM.valid (α := Mseti α) = fun A => ∀ a ∈ A.val, ✓ a := rfl

protected lemma Mseti.valid_pure [PCM α] (a : α) :
    (✓ (pure a : Mseti α)) = (✓ a) := by
  simp only [Mseti.valid_unfold, Mseti.pure_val, Mset.mem_pure, forall_eq]

/-- Valid inhabited multisets -/
abbrev Msetiv α [PCM α] := { A : Mseti α // ✓ A }

/-! ## Inhabited multiset PCMP -/

/-- Inhabited multiset PCMP -/
protected noncomputable instance Mseti.instPCMP (α : Type u) [PCMP α] : PCMP (Mseti α) where
  prob A := ∑ᴹ a ∈ᴹ A.val, PCMP.prob a
  prob_one := by
    rw [Mseti.one_unfold, Mseti.pure_val, Mset.tsum_pure, PCMP.prob_one]
  prob_mul := by
    intro _ _; rw [Mseti.mul_val, Mset.map_seq, Mset.tsum_map, ENNReal.Mset.tsum_mul_tsum];
    congr; ext1 _; apply PCMP.prob_mul

protected lemma Mseti.prob_unfold [PCMP α] (A : Mseti α) :
    PCMP.prob A = ∑ᴹ a ∈ᴹ A.val, PCMP.prob a := rfl

protected lemma Mseti.prob_pure [PCMP α] (a : α) :
    PCMP.prob (pure a : Mseti α) = PCMP.prob a := by
  rw [Mseti.prob_unfold, Mseti.pure_val, Mset.tsum_pure]

protected lemma Mseti.prob_bigoplus [Inhabited ι] [PCMP α] (A : ι → Mseti α) :
    PCMP.prob (⨁ᴹⁱ i, A i) = ∑' i, PCMP.prob (A i) := by
  rw [Mseti.prob_unfold, Mseti.bigoplus_val, ENNReal.Mset.tsum_bigoplus]; rfl

protected lemma Mseti.prob_oplus [PCMP α] (A B : Mseti α) :
    PCMP.prob (A ⊕ᴹⁱ B) = PCMP.prob A + PCMP.prob B := by
  rw [Mseti.prob_unfold, Mseti.oplus_val, ENNReal.Mset.tsum_oplus]; rfl
