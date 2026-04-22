module

public import Mathlib.Algebra.Group.Defs

@[expose] public section

/-! # PCM -/

/-! ## Commutative monoid -/

/-- Utility version of `CommMonoid`, where only `mul_one` is required -/
class CommMonoid' (α : Type u) extends CommSemigroup α, One α where
  mul_one : ∀ a, a * one = a

/-- `CommMonoid'` induces `CommMonoid` -/
instance CommMonoid'.CommMonoid (α : Type u) [CommMonoid' α] : CommMonoid α where
  mul_one := mul_one
  one_mul _ := by rw [mul_comm]; apply mul_one

/-! ## PCM, i.e., partial commutative monoid -/

/-- PCM, where the partiality is formulated by a validity predicate -/
class PCM.{u} (α : Type u) extends CommMonoid' α where
  /-- Validity -/
  valid : α → Prop
  /-- `one` is valid -/
  valid_one : valid one

prefix:50 "✓ " => PCM.valid

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
instance Excl.PCM : PCM (Excl α) where
  one := Excl.unit
  mul | a, Excl.unit => a
      | Excl.unit, b => b
      | _, _ => Excl.bot
  mul_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one _ := rfl
  valid | Excl.excl _ | Excl.unit => True
        | Excl.bot => False
  valid_one := trivial

/-! ### Product PCM -/

/-- Product PCM -/
instance Prod.PCM (α β : Type u) [PCM α] [PCM β] : PCM (α × β) where
  one := (1, 1)
  mul | (a, b), (a', b') => (a * a', b * b')
  mul_one _ := by ext1 <;> apply mul_one
  mul_comm _ _ := by ext1 <;> apply mul_comm
  mul_assoc _ _ _ := by ext1 <;> apply mul_assoc
  valid | (a, b) => ✓ a ∧ ✓ b
  valid_one := by and_intros <;> apply PCM.valid_one

/-! ### Pi PCM -/

/-- Pi PCM -/
instance piPCM (ι : Type u) (α : ι → Type u') [∀ i, PCM (α i)] : PCM (∀ i, α i) where
  one i := 1
  mul f g i := f i * g i
  mul_one _ := by funext; apply mul_one
  mul_comm _ _ := by funext; apply mul_comm
  mul_assoc _ _ _ := by funext; apply mul_assoc
  valid f := ∀ i, ✓ f i
  valid_one := by intro i; apply PCM.valid_one
