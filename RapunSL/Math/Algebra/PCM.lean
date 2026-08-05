module

public import RapunSL.Util.Syntax
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.ENNReal.Basic
open ENNReal

@[expose] public section

/-! # Algebras -/

/-! ## Commutative monoid -/

/-- Utility version of `CommMonoid`, where only `mul_one` is required -/
class CommMonoid' (α : Type u) extends CommSemigroup α, One α where
  protected mul_one : ∀ a : α, a * 1 = a

/-- `CommMonoid'` induces `CommMonoid` -/
protected instance CommMonoid'.instCommMonoid [CommMonoid' α] : CommMonoid α where
  mul_one := CommMonoid'.mul_one
  one_mul _ := by rw [mul_comm]; apply CommMonoid'.mul_one

/-! ## PCM, i.e., partial commutative monoid -/

/-- PCM, i.e., partial commutative monoid -/
class PCM (α : Type u) extends CommMonoid' α where
  /-- Validity predicate for partiality -/
  protected valid : α → Prop
  /-- `1` is valid -/
  protected valid_one : valid 1
  /-- Take the left-hand side of `*` in `✓` -/
  protected valid_mul_l : ∀ a b : α, valid (a * b) → valid a

open PCM

namespace PCM
variable [PCM α] (a b : α)

@[inherit_doc]
scoped prefix:55 "✓ " => PCM.valid

/-- Take the right-hand side of `*` in `✓` -/
protected lemma valid_mul_r : ✓ (a * b) → ✓ b := by
  rw [mul_comm]; apply PCM.valid_mul_l

end PCM

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
protected instance Excl.instPCM : PCM (Excl α) where
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
protected instance Prod.instPCM [PCM α] [PCM β] : PCM (α × β) where
  one := (1, 1)
  mul p q := (p.1 * q.1, p.2 * q.2)
  mul_one _ := by ext1 <;> apply mul_one
  mul_comm _ _ := by ext1 <;> apply mul_comm
  mul_assoc _ _ _ := by ext1 <;> apply mul_assoc
  valid p := ✓ p.1 ∧ ✓ p.2
  valid_one := by and_intros <;> apply PCM.valid_one
  valid_mul_l := by
    intro _ _ ⟨val, val'⟩; and_intros;
    { apply PCM.valid_mul_l _ _ val }; { apply PCM.valid_mul_l _ _ val' }

protected lemma Prod.one_unfold [PCM α] [PCM β] : (1 : α × β) = (1, 1) := rfl

protected lemma Prod.mul_unfold [PCM α] [PCM β] :
    (HMul.hMul : α × β → α × β → _) = fun p q => (p.1 * q.1, p.2 * q.2) := rfl

protected lemma Prod.valid_unfold [PCM α] [PCM β] :
    PCM.valid (α := α × β) = fun p => ✓ p.1 ∧ ✓ p.2 := rfl

/-! ### Pi PCM -/

/-- Pi PCM -/
protected instance Pi.instPCM {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    PCM (∀ i, α i) where
  one i := 1
  mul f g i := f i * g i
  mul_one _ := by funext; apply mul_one
  mul_comm _ _ := by funext; apply mul_comm
  mul_assoc _ _ _ := by funext; apply mul_assoc
  valid f := ∀ i, ✓ f i
  valid_one := by intro i; apply PCM.valid_one
  valid_mul_l := by intro _ _ val i; apply PCM.valid_mul_l _ _ (val i)

protected lemma Pi.one_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    (1 : ∀ i, α i) = fun _ => 1 := rfl

protected lemma Pi.mul_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    (HMul.hMul : (∀ i, α i) → (∀ i, α i) → (∀ i, α i)) =
      fun f g i => f i * g i := rfl

protected lemma Pi.valid_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    PCM.valid (α := ∀ i, α i) = fun f => ∀ i, ✓ f i := rfl

/-! ## Cancellative PCM -/

/-- Cancellative PCM -/
class PCMCan (α : Type u) extends PCM α where
  /-- Product is cancellative under validity -/
  protected mul_cancel_l : ∀ a b c : α, ✓ a * c → a * c = b * c → a = b

open PCMCan

namespace PCMCan
variable [PCMCan α] (a b c : α)

/-- Product is cancellative under validity -/
protected lemma mul_cancel_r : ✓ a * b → a * b = a * c → b = c := by
  simp only [mul_comm a]; apply PCMCan.mul_cancel_l

end PCMCan

/-! ## Cancellative PCM constructions -/

/-- Exclusive cancellative PCM -/
instance Excl.instPCMCan : PCMCan (Excl α) where
  mul_cancel_l := by intro a b c; cases a <;> cases b <;> cases c <;> tauto

/-- Product cancellative PCM -/
instance Prod.instPCMCan [PCMCan α] [PCMCan β] : PCMCan (α × β) where
  mul_cancel_l := by
    intro (_, _) (_, _) (_, _) ⟨_, _⟩; simp only [mk_mul_mk, mk.injEq] at *;
    intro ⟨_, _⟩; and_intros <;> apply PCMCan.mul_cancel_l <;> trivial

/-- Pi cancellative PCM -/
instance Pi.instPCMCan {ι : Type*} {α : ι → Type*} [∀ i, PCMCan (α i)] :
    PCMCan (∀ i, α i) where
  mul_cancel_l := by
    intro _ _ _ val eq; ext1 i; apply PCMCan.mul_cancel_l; { apply val }; apply congrFun eq

/-! ## PCM with probability -/

/-- PCM with probability -/
class PCMP (α : Type u) extends PCM α where
  /-- Probability function -/
  protected prob : α → ℝ≥0∞
  /-- `1` has probability `1` -/
  protected prob_one : prob 1 = 1
  /-- The probability of `*` is the product of the probabilities -/
  protected prob_mul : ∀ a b : α, ✓ a * b → prob (a * b) = prob a * prob b
