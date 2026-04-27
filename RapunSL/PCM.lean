module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.ScopedNS
public import RapunSL.Mset

@[expose] public section

/-! # PCM -/

/-! ## Commutative monoid -/

/-- Utility version of `CommMonoid`, where only `mul_one` is required -/
class CommMonoid' (α : Type u) extends CommSemigroup α, One α where
  protected mul_one : ∀ a, a * one = a

/-- `CommMonoid'` induces `CommMonoid` -/
protected instance CommMonoid'.instCommMonoid (α : Type u) [CommMonoid' α] : CommMonoid α where
  mul_one := CommMonoid'.mul_one
  one_mul _ := by rw [mul_comm]; apply CommMonoid'.mul_one

/-! ## PCM, i.e., partial commutative monoid -/

/-- PCM, i.e., partial commutative monoid -/
class PCM (α : Type u) extends CommMonoid' α where
  /-- Validity predicate for partiality -/
  pvalid : α → Prop
  /-- `one` is valid -/
  pvalid_one : pvalid one

scoped[PCM] prefix:50 "✓ᴾ " => PCM.pvalid
open PCM

/-- PCM with an antitone validity -/
class PCMa.{u} (α : Type u) extends PCM α where
  /-- Validity -/
  pvalid_mul_l : ∀ a b, pvalid (a * b) → pvalid a

lemma PCMa.pvalid_mul_r [PCMa α] (a b : α) : pvalid (a * b) → pvalid b := by
  rw [mul_comm]; apply PCMa.pvalid_mul_l

/-! ## PCM constructions -/

/-! ### Exclusive PCM -/

/-- Data type for the exclusive PCM -/
inductive Excl (α : Type u) where
  | /-- Exclusive element -/
    excl : α → Excl α
  | /-- Unit element -/
    unit : Excl α
  | /-- Bottom element -/
    bot : Excl α

/-- Exclusive PCM -/
protected instance Excl.instPCMa : PCMa (Excl α) where
  one := Excl.unit
  mul | a, Excl.unit => a | Excl.unit, b => b | _, _ => Excl.bot
  mul_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one _ := rfl
  pvalid | Excl.bot => False | _ => True
  pvalid_one := trivial
  pvalid_mul_l a b := by cases a <;> cases b <;> grind only

protected lemma Excl.one_unfold : (1 : Excl α) = Excl.unit := rfl

protected lemma Excl.mul_unfold :
    (HMul.hMul : Excl α → Excl α → _) =
      fun | a, Excl.unit => a | Excl.unit, b => b | _, _ => Excl.bot := rfl

protected lemma Excl.pvalid_unfold :
    pvalid (α := Excl α) = fun | Excl.bot => False | _ => True := rfl

/-! ### Product PCM -/

/-- Product PCM -/
protected instance Prod.instPCM (α : Type u) (β : Type u') [PCM α] [PCM β] : PCM (α × β) where
  one := (1, 1)
  mul | (a, b), (a', b') => (a * a', b * b')
  mul_one _ := by ext1 <;> apply mul_one
  mul_comm _ _ := by ext1 <;> apply mul_comm
  mul_assoc _ _ _ := by ext1 <;> apply mul_assoc
  pvalid | (a, b) => ✓ᴾ a ∧ ✓ᴾ b
  pvalid_one := by and_intros <;> apply PCM.pvalid_one

protected lemma Prod.one_unfold [PCM α] [PCM β] : (1 : α × β) = (1, 1) := rfl

protected lemma Prod.mul_unfold [PCM α] [PCM β] :
    (HMul.hMul : α × β → α × β → _) = fun | (a, b), (a', b') => (a * a', b * b') := rfl

protected lemma Prod.pvalid_unfold [PCM α] [PCM β] :
    pvalid (α := α × β) = fun | (a, b) => ✓ᴾ a ∧ ✓ᴾ b := rfl

protected instance Prod.instPCMa (α : Type u) (β : Type u') [PCMa α] [PCMa β] : PCMa (α × β) where
  pvalid_mul_l := by
    intro _ _ ⟨val, val'⟩; and_intros;
    { apply PCMa.pvalid_mul_l _ _ val }; { apply PCMa.pvalid_mul_l _ _ val' }

/-! ### Pi PCM -/

/-- Pi PCM -/
protected instance Pi.instPCM (ι : Type u) (α : ι → Type u') [∀ i, PCM (α i)] :
    PCM (∀ i, α i) where
  one i := 1
  mul f g i := f i * g i
  mul_one _ := by funext; apply mul_one
  mul_comm _ _ := by funext; apply mul_comm
  mul_assoc _ _ _ := by funext; apply mul_assoc
  pvalid f := ∀ i, ✓ᴾ f i
  pvalid_one := by intro i; apply PCM.pvalid_one

protected lemma Pi.one_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    (1 : ∀ i, α i) = fun _ => 1 := rfl

protected lemma Pi.mul_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    (HMul.hMul : (∀ i, α i) → (∀ i, α i) → (∀ i, α i)) =
      fun f g i => f i * g i := by rfl

protected lemma Pi.pvalid_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    pvalid (α := ∀ i, α i) = fun f => ∀ i, ✓ᴾ f i := rfl

protected instance Pi.instPCMa (ι : Type u) (α : ι → Type u') [∀ i, PCMa (α i)] :
    PCMa (∀ i, α i) where
  pvalid_mul_l := by intro _ _ val i; apply PCMa.pvalid_mul_l _ _ (val i)

/-! ### Multiset PCM -/

/-- `*` for multisets -/
protected instance Mset.Mul (α : Type u) [Mul α] : Mul (Mset α) where
  mul A B := HMul.hMul <$> A <*> B

protected lemma Mset.mul_unfold [Mul α] :
    (HMul.hMul : Mset α → Mset α → _) = fun A B => HMul.hMul <$> A <*> B := rfl

/-- Multiset PCM -/
protected instance Mset.instPCM (α : Type u) [PCM α] : PCM (Mset α) where
  one := pure 1
  mul_one _ := by
    simp only [Mset.mul_unfold]; rw [seq_pure, ←comp_map];
    trans; swap; { apply id_map }; congr; grind only [mul_one, id_eq]
  mul_comm _ _ := by
    simp only [Mset.mul_unfold]; rw [CommApplicative.commutative_map]; congr;
    grind only [mul_comm]
  mul_assoc _ _ _ := by
    simp only [Mset.mul_unfold, functor_norm]; grind only [mul_assoc]
  pvalid A := ∀ a ∈ A, ✓ᴾ a
  pvalid_one := by
    simp only [Mset.mem_pure, forall_eq]; apply PCM.pvalid_one

protected lemma Mset.one_unfold [PCM α] : (1 : Mset α) = pure 1 := rfl

protected lemma Mset.pvalid_unfold [PCM α] :
    pvalid (α := Mset α) = fun A => ∀ a ∈ A, ✓ᴾ a := rfl

/-! ### Antitonicity of `✓ᴾ` for `Mset` under inhabitedness -/

protected lemma Mset.pvalid_mul_l [PCMa α] (A B : Mset α) :
    B.inhab → pvalid (A * B) → pvalid A := by
  simp only [Mset.mul_unfold, Mset.pvalid_unfold, Mset.mem_seq, Mset.mem_map];
  simp only [existsAndEq, and_true]; intro ⟨b, _⟩ val _ _;
  apply PCMa.pvalid_mul_l _ b; apply val; grind only

protected lemma Mset.pvalid_mul_r [PCMa α] (A B : Mset α) :
    A.inhab → pvalid (A * B) → pvalid B := by
  rw [mul_comm]; apply Mset.pvalid_mul_l
