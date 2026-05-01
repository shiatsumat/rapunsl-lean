module

public import Mathlib.Algebra.Group.Defs
public import RapunSL.Mset
open Mset

@[expose] public section

/-! # PCM -/

/-! ## Commutative monoid -/

/-- Utility version of `CommMonoid`, where only `mul_one` is required -/
class CommMonoid' (α : Type u) extends CommSemigroup α, One α where
  protected mul_one : ∀ a : α, a * 1 = a

/-- `CommMonoid'` induces `CommMonoid` -/
protected instance CommMonoid'.instCommMonoid (α : Type u) [CommMonoid' α] : CommMonoid α where
  mul_one := CommMonoid'.mul_one
  one_mul _ := by rw [mul_comm]; apply CommMonoid'.mul_one

/-! ## PCM, i.e., partial commutative monoid -/

/-- PCM, i.e., partial commutative monoid -/
class PCM (α : Type u) extends CommMonoid' α where
  /-- Validity predicate for partiality -/
  protected valid : α → Prop
  /-- `1` is valid -/
  protected valid_one : valid 1

scoped[PCM] prefix:50 "✓ " => PCM.valid
open PCM

/-- PCM whose validity is antitone w.r.t. `*` -/
class PCMa.{u} (α : Type u) extends PCM α where
  /-- Take the left-hand side of `*` in `✓` -/
  protected valid_mul_l : ∀ a b : α, ✓ (a * b) → ✓ a

/-- Take the right-hand side of `*` in `✓` -/
protected lemma PCMa.valid_mul_r [PCMa α] (a b : α) : ✓ (a * b) → ✓ b := by
  rw [mul_comm]; apply PCMa.valid_mul_l

/-! ## PCM constructions -/

/-! ### Exclusive PCM -/

/-- Data type for the exclusive PCM -/
inductive Excl (α : Type u) where
  | /-- Exclusive element -/
    protected excl : α → Excl α
  | /-- Unit element -/
    protected unit : Excl α
  | /-- Bottom element -/
    protected bot : Excl α

/-- Exclusive PCM -/
protected instance Excl.instPCMa : PCMa (Excl α) where
  one := .unit
  mul | a, .unit => a | .unit, b => b | _, _ => .bot
  mul_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one _ := rfl
  valid | .bot => False | _ => True
  valid_one := trivial
  valid_mul_l a b := by cases a <;> cases b <;> tauto

protected lemma Excl.one_unfold : (1 : Excl α) = .unit := rfl

protected lemma Excl.mul_unfold :
    (HMul.hMul : Excl α → Excl α → _) =
      fun | a, .unit => a | .unit, b => b | _, _ => .bot := rfl

protected lemma Excl.valid_unfold :
    PCM.valid (α := Excl α) = fun | .bot => False | _ => True := rfl

/-! ### Product PCM -/

/-- Product PCM -/
protected instance Prod.instPCM (α : Type u) (β : Type u') [PCM α] [PCM β] : PCM (α × β) where
  one := (1, 1)
  mul | (a, b), (a', b') => (a * a', b * b')
  mul_one _ := by ext1 <;> apply mul_one
  mul_comm _ _ := by ext1 <;> apply mul_comm
  mul_assoc _ _ _ := by ext1 <;> apply mul_assoc
  valid | (a, b) => ✓ a ∧ ✓ b
  valid_one := by and_intros <;> apply PCM.valid_one

protected lemma Prod.one_unfold [PCM α] [PCM β] : (1 : α × β) = (1, 1) := rfl

protected lemma Prod.mul_unfold [PCM α] [PCM β] :
    (HMul.hMul : α × β → α × β → _) = fun | (a, b), (a', b') => (a * a', b * b') := rfl

protected lemma Prod.valid_unfold [PCM α] [PCM β] :
    PCM.valid (α := α × β) = fun | (a, b) => ✓ a ∧ ✓ b := rfl

protected instance Prod.instPCMa (α : Type u) (β : Type u') [PCMa α] [PCMa β] : PCMa (α × β) where
  valid_mul_l := by
    intro _ _ ⟨val, val'⟩; and_intros;
    { apply PCMa.valid_mul_l _ _ val }; { apply PCMa.valid_mul_l _ _ val' }

/-! ### Pi PCM -/

/-- Pi PCM -/
protected instance Pi.instPCM (ι : Type u) (α : ι → Type u') [∀ i, PCM (α i)] :
    PCM (∀ i, α i) where
  one i := 1
  mul f g i := f i * g i
  mul_one _ := by funext; apply mul_one
  mul_comm _ _ := by funext; apply mul_comm
  mul_assoc _ _ _ := by funext; apply mul_assoc
  valid f := ∀ i, ✓ f i
  valid_one := by intro i; apply PCM.valid_one

protected lemma Pi.one_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    (1 : ∀ i, α i) = fun _ => 1 := rfl

protected lemma Pi.mul_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    (HMul.hMul : (∀ i, α i) → (∀ i, α i) → (∀ i, α i)) =
      fun f g i => f i * g i := by rfl

protected lemma Pi.valid_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    PCM.valid (α := ∀ i, α i) = fun f => ∀ i, ✓ f i := rfl

protected instance Pi.instPCMa (ι : Type u) (α : ι → Type u') [∀ i, PCMa (α i)] :
    PCMa (∀ i, α i) where
  valid_mul_l := by intro _ _ val i; apply PCMa.valid_mul_l _ _ (val i)

/-! ### Multiset PCM -/

/-- `*` for multisets -/
protected instance Mset.Mul (α : Type u) [Mul α] : Mul (Mset α) where
  mul A B := HMul.hMul <$> A <*> B

protected lemma Mset.mul_unfold [Mul α] :
    (HMul.hMul : Mset α → Mset α → _) = fun A B => HMul.hMul <$> A <*> B := rfl

protected lemma Mset.pure_mul [Mul α] (a b : α) :
    pure (f := Mset) (a * b) = pure a * pure b := by
  simp only [Mset.mul_unfold, functor_norm]

protected lemma Mset.mul_bigoplus_l [Mul α] A (B : ι → Mset α) :
    A * (⨁ᴹ i, B i) = ⨁ᴹ i, A * B i := by
  simp only [Mset.mul_unfold, Mset.seq_bigoplus_l]

protected lemma Mset.mul_bigoplus_r [Mul α] (A : ι → Mset α) B :
    (⨁ᴹ i, A i) * B = ⨁ᴹ i, A i * B := by
  simp only [Mset.mul_unfold, Mset.bigoplus_map, Mset.seq_bigoplus_r]

protected lemma Mset.mul_oplus_l [Mul α] (A B C : Mset α) :
    A * (B ⊕ᴹ C) = A * B ⊕ᴹ A * C := by
  simp only [Mset.oplus_bigoplus, Mset.mul_bigoplus_l]; grind only

protected lemma Mset.mul_oplus_r [Mul α] (A B C : Mset α) :
    (A ⊕ᴹ B) * C = A * C ⊕ᴹ B * C := by
  simp only [Mset.oplus_bigoplus, Mset.mul_bigoplus_r]; grind only

protected lemma Mset.mul_empty_l [Mul α] (A : Mset α) : A * ∅ = ∅ := by
  simp only [Mset.empty_bigoplus, Mset.mul_bigoplus_l]; congr; ext1 _; tauto

protected lemma Mset.mul_empty_r [Mul α] (A : Mset α) : ∅ * A = ∅ := by
  simp only [Mset.empty_bigoplus, Mset.mul_bigoplus_r]; congr; ext1 _; tauto

@[simp] protected lemma Mset.mem_mul [Mul α] (A B : Mset α) a :
    (a ∈ A * B) = ∃ b ∈ A, ∃ c ∈ B, a = b * c := by
  simp only [Mset.mul_unfold, Mset.mem_seq, Mset.mem_map, existsAndEq]; ext1; tauto

@[simp] protected lemma Mset.inhab_mul [Mul α] (A B : Mset α) :
    (A * B).inhab = (A.inhab ∧ B.inhab) := by
  simp only [Mset.inhab, Mset.mem_mul]; grind only

/-- `1` for multisets -/
protected instance Mset.instOne (α : Type u) [One α] : One (Mset α) where
  one := pure 1

protected lemma Mset.one_unfold [PCM α] : (1 : Mset α) = pure 1 := rfl

/-- Multiset PCM -/
protected instance Mset.instPCM (α : Type u) [PCM α] : PCM (Mset α) where
  one := pure 1
  mul_one _ := by
    simp only [Mset.mul_unfold, Mset.one_unfold]; rw [seq_pure, ←comp_map];
    trans; swap; { apply id_map }; congr; grind only [mul_one, id_eq]
  mul_comm _ _ := by
    simp only [Mset.mul_unfold]; rw [CommApplicative.commutative_map]; congr;
    grind only [mul_comm]
  mul_assoc _ _ _ := by
    simp only [Mset.mul_unfold, functor_norm]; grind only [mul_assoc]
  valid A := ∀ a ∈ A, ✓ a
  valid_one := by
    simp only [Mset.one_unfold, Mset.mem_pure, forall_eq]; apply PCM.valid_one

protected lemma Mset.valid_unfold [PCM α] :
    PCM.valid (α := Mset α) = fun A => ∀ a ∈ A, ✓ a := rfl

protected lemma Mset.valid_empty [PCM α] : ✓ (∅ : Mset α) := by
  simp only [Mset.valid_unfold, Mset.mem_empty]; tauto

protected lemma Mset.valid_pure [PCM α] (a : α) :
    ✓ a → ✓ (pure a : Mset α) := by
  simp only [Mset.valid_unfold, Mset.mem_pure, forall_eq]; tauto

/-! ### Antitonicity of `✓` for `Mset` under inhabitedness -/

protected lemma Mset.valid_mul_l [PCMa α] (A B : Mset α) :
    B.inhab → ✓ (A * B) → ✓ A := by
  simp only [Mset.mul_unfold, Mset.valid_unfold, Mset.mem_seq, Mset.mem_map];
  simp only [existsAndEq, and_true]; intro ⟨b, _⟩ val _ _;
  apply PCMa.valid_mul_l _ b; apply val; tauto

protected lemma Mset.valid_mul_r [PCMa α] (A B : Mset α) :
    A.inhab → ✓ (A * B) → ✓ B := by
  rw [mul_comm]; apply Mset.valid_mul_l
