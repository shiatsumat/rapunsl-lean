module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
open ENNReal

@[expose] public section

/-! # Algebras -/

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
  /-- Take the left-hand side of `*` in `✓` -/
  protected valid_mul_l : ∀ a b : α, valid (a * b) → valid a

@[inherit_doc]
scoped[PCM] prefix:55 "✓ " => PCM.valid
open PCM

/-- Take the right-hand side of `*` in `✓` -/
protected lemma PCM.valid_mul_r [PCM α] (a b : α) : ✓ (a * b) → ✓ b := by
  rw [mul_comm]; apply PCM.valid_mul_l

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
protected instance Prod.instPCM (α : Type u) (β : Type u') [PCM α] [PCM β] : PCM (α × β) where
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
protected instance Pi.instPCM (ι : Type u) (α : ι → Type u') [∀ i, PCM (α i)] :
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

/-! ## PCMC, i.e., PCM with coherence and incompatibility -/

/-- PCM with coherence and incompatibility -/
class PCMC (α : Type u) extends PCM α where
  /-- Coherence relation -/
  protected coher : α → α → Prop
  /-- Coherence is an equivalence relation -/
  protected coher_instIsEquiv : IsEquiv α coher
  /-- Coherence is compatible with `*` -/
  protected coher_mul_l : ∀ a b c, coher a b → coher (a * c) (b * c)
  /-- Coherence respects validity -/
  protected coher_valid : ∀ a b, coher a b → ✓ a → ✓ b
  /-- Incompatibility relation -/
  protected incomp : α → α → Prop
  /-- Incompatibility is symmetric -/
  protected incomp_instSymm : Std.Symm incomp
  /-- Incompatibility negates coherence -/
  protected incomp_neg_coher : ∀ a b, ✓ a → incomp a b → ¬ coher a b
  /-- Incompatibility is preserved by `*` under validity -/
  protected incomp_mul_l : ∀ a b c, ✓ a * c → incomp a b → incomp (a * c) b

open PCMC

namespace PCMC
variable [PCMC α]

@[inherit_doc]
scoped infix:50 " ≎ " => PCMC.coher

@[inherit_doc]
scoped infix:50 " # " => PCMC.incomp

/-- Coherence is reflexive -/
@[refl] protected lemma coher_refl (a : α) : a ≎ a := by
  apply PCMC.coher_instIsEquiv.refl

/-- Coherence is symmetric -/
@[symm] protected lemma coher_symm (a b : α) : a ≎ b → b ≎ a := by
  apply PCMC.coher_instIsEquiv.symm

/-- Coherence is transitive -/
@[trans] protected lemma coher_trans (a b c : α) : a ≎ b → b ≎ c → a ≎ c := by
  apply PCMC.coher_instIsEquiv.trans

/-- Coherence is compatible with `*` -/
protected lemma coher_mul_r (a b c : α) : a ≎ b → c * a ≎ c * b := by
  rw [mul_comm c a, mul_comm c b]; apply PCMC.coher_mul_l

/-- Coherence respects validity -/
protected lemma coher_valid' (a b : α) :
    a ≎ b → ✓ a = ✓ b := by
  intro _; ext1;
  constructor <;> apply PCMC.coher_valid; { trivial }; { symm; trivial }

/-- Incompatibility is symmetric -/
@[symm] protected lemma incomp_symm (a b : α) : a # b → b # a := by
  apply PCMC.incomp_instSymm.symm

/-- Incompatibility is preserved by `*` under validity -/
protected lemma incomp_mul_r (a b c : α) : ✓ c * a → a # b → c * a # b := by
  rw [mul_comm]; apply PCMC.incomp_mul_l

end PCMC

/-! ## PCMC constructions -/

/-! ### Exclusive PCMC -/

protected instance Excl.instPCMC : PCMC (Excl α) where
  coher := Eq
  coher_instIsEquiv := by infer_instance
  coher_mul_l := by intro _ _ _ rfl; rfl
  coher_valid := by intro _ _ rfl _; trivial
  incomp | .excl a, .excl b => a ≠ b | _, _ => False
  incomp_instSymm := by constructor; intro a b; cases a <;> cases b <;> tauto
  incomp_neg_coher := by intro a b; cases a <;> cases b <;> grind only
  incomp_mul_l := by intro a b c; cases a <;> cases b <;> cases c <;> tauto

protected lemma Excl.coher_unfold : PCMC.coher (α := Excl α) = Eq := rfl

protected lemma Excl.incomp_unfold :
    PCMC.incomp (α := Excl α) = fun | .excl a, .excl b => a ≠ b | _, _ => False := rfl

/-! ### Product PCMC -/

protected instance Prod.instPCMC (α : Type u) (β : Type u') [PCMC α] [PCMC β] :
    PCMC (α × β) where
  coher p q := p.1 ≎ q.1 ∧ p.2 ≎ q.2
  coher_instIsEquiv := {
    refl := by intros; and_intros <;> rfl
    symm := by intros; and_intros <;> symm <;> tauto
    trans := by intros; and_intros <;> apply PCMC.coher_trans <;> tauto
  }
  coher_mul_l := by intros; and_intros <;> apply PCMC.coher_mul_l <;> tauto
  coher_valid := by
    intro _ _ _ ⟨_, _⟩; and_intros <;> apply PCMC.coher_valid <;> tauto
  incomp p q := p.1 # q.1 ∨ p.2 # q.2
  incomp_instSymm := by
    constructor; rintro _ _ (inc | inc) <;> symm at inc <;> tauto
  incomp_neg_coher := by
    rintro _ _ ⟨_, _⟩ (inc | inc) <;> apply PCMC.incomp_neg_coher at inc <;> tauto
  incomp_mul_l := by
    rintro _ _ _ ⟨_, _⟩ (_ | _); (on_goal 1 => left); (on_goal 2 => right);
      any_goals apply PCMC.incomp_mul_l <;> tauto

protected lemma Prod.coher_unfold [PCMC α] [PCMC β] :
    PCMC.coher (α := α × β) = fun p q => p.1 ≎ q.1 ∧ p.2 ≎ q.2 := rfl

protected lemma Prod.incomp_unfold [PCMC α] [PCMC β] :
    PCMC.incomp (α := α × β) = fun p q => p.1 # q.1 ∨ p.2 # q.2 := rfl

/-! ### Pi PCMC -/

protected instance Pi.instPCMC (ι : Type u) (α : ι → Type u') [∀ i, PCMC (α i)] :
    PCMC (∀ i, α i) where
  coher f g := ∀ i, f i ≎ g i
  coher_instIsEquiv := {
    refl := by intros; rfl
    symm := by intros; symm; tauto
    trans := by intro _ f _ _ _ i; apply PCMC.coher_trans _ (f i) <;> tauto
  }
  coher_mul_l := by intro _ _ _ _ _; apply PCMC.coher_mul_l; tauto
  coher_valid := by intro _ _ coh _ i; apply PCMC.coher_valid _ _ (coh i); tauto
  incomp f g := ∃ i, f i # g i
  incomp_instSymm := by constructor; intro _ _ ⟨i, _⟩; exists i; symm; trivial
  incomp_neg_coher := by
    intro _ _ val ⟨i, inc⟩ _; apply PCMC.incomp_neg_coher _ _ (val i) at inc; tauto
  incomp_mul_l := by
    intro _ _ _ _ ⟨i, _⟩; exists i; apply PCMC.incomp_mul_l <;> tauto

/-! ## PCM with probability -/

/-- PCM with probability -/
class PCMP (α : Type u) extends PCM α where
  /-- Probability function -/
  protected prob : α → ℝ≥0∞
  /-- `1` has probability `1` -/
  protected prob_one : prob 1 = 1
  /-- The probability of `*` is the product of the probabilities -/
  protected prob_mul : ∀ a b : α, prob (a * b) = prob a * prob b

/-! ## RM, i.e., resource monoid -/

/-- RM, i.e., resource monoid -/
class RM (α : Type u) extends PCMC α, PCMP α
