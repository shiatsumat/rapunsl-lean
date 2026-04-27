module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.ScopedNS

@[expose] public section

/-! # PCM -/

/-! ## Commutative monoid -/

/-- Utility version of `CommMonoid`, where only `mul_one` is required -/
class CommMonoid' (α : Type u) extends CommSemigroup α, One α where
  protected mul_one : ∀ a, a * one = a

/-- `CommMonoid'` induces `CommMonoid` -/
protected instance CommMonoid'.CommMonoid (α : Type u) [CommMonoid' α] : CommMonoid α where
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
protected instance Excl.PCM : PCM (Excl α) where
  one := Excl.unit
  mul | a, Excl.unit => a | Excl.unit, b => b | _, _ => Excl.bot
  mul_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one _ := rfl
  pvalid | Excl.bot => False | _ => True
  pvalid_one := trivial

protected lemma Excl.one_unfold : (1 : Excl α) = Excl.unit := rfl

protected lemma Excl.mul_unfold :
    (HMul.hMul : Excl α → Excl α → _) =
      fun | a, Excl.unit => a | Excl.unit, b => b | _, _ => Excl.bot := rfl

protected lemma Excl.pvalid_unfold :
    pvalid (α := Excl α) = fun | Excl.bot => False | _ => True := rfl

/-! ### Product PCM -/

/-- Product PCM -/
protected instance Prod.PCM (α : Type u) (β : Type u') [PCM α] [PCM β] : PCM (α × β) where
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

/-! ### Pi PCM -/

/-- Pi PCM -/
protected instance Pi.PCM (ι : Type u) (α : ι → Type u') [∀ i, PCM (α i)] : PCM (∀ i, α i) where
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
