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

/-! ## PCMI, i.e., PCM with incompatibility -/

/-- PCM with coherence and incompatibility -/
class PCMI (α : Type u) extends PCM α where
  /-- Incompatibility relation -/
  protected incomp : α → α → Prop
  /-- Incompatibility is irreflexive -/
  protected incomp_Irrefl : Std.Irrefl incomp
  /-- Incompatibility is symmetric -/
  protected incomp_Symm : Std.Symm incomp
  /-- Incompatibility is preserved by `*` under validity -/
  protected incomp_mul_l : ∀ a b c, ✓ a * c → incomp a b → incomp (a * c) b

open PCMI

namespace PCMI
variable [PCMI α] (a b c : α)

@[inherit_doc]
scoped infix:50 " # " => PCMI.incomp

/-- Incompatibility is irreflexive -/
protected instance incomp_instIrrefl :
    Std.Irrefl (α := α) PCMI.incomp := PCMI.incomp_Irrefl

/-- Incompatibility is irreflexive -/
protected lemma incomp_irrefl : ¬ a # a := by
  apply irrefl

/-- Incompatibility is symmetric -/
protected instance incomp_instSymm :
    Std.Symm (α := α) PCMI.incomp := PCMI.incomp_Symm

/-- Incompatibility is symmetric -/
@[symm] protected lemma incomp_symm : a # b → b # a := by
  apply symm

/-- Incompatibility is preserved by `*` under validity -/
protected lemma incomp_mul_r : ✓ c * a → a # b → c * a # b := by
  rw [mul_comm]; apply PCMI.incomp_mul_l

end PCMI

/-! ## PCMI constructions -/

/-! ### Exclusive PCMI -/

protected instance Excl.instPCMI : PCMI (Excl α) where
  incomp | .excl a, .excl b => a ≠ b | _, _ => False
  incomp_Irrefl := by constructor; intro a; cases a <;> grind only
  incomp_Symm := by constructor; intro a b; cases a <;> cases b <;> tauto
  incomp_mul_l := by intro a b c; cases a <;> cases b <;> cases c <;> tauto

protected lemma Excl.incomp_unfold :
    PCMI.incomp (α := Excl α) = fun | .excl a, .excl b => a ≠ b | _, _ => False := rfl

/-! ### Product PCMI -/

protected instance Prod.instPCMI [PCMI α] [PCMI β] :
    PCMI (α × β) where
  incomp p q := p.1 # q.1 ∨ p.2 # q.2
  incomp_Irrefl := by
    constructor; rintro ⟨_, _⟩ (inc | inc) <;> apply irrefl _ inc
  incomp_Symm := by
    constructor; rintro _ _ (inc | inc) <;> symm at inc <;> tauto
  incomp_mul_l := by
    rintro _ _ _ ⟨_, _⟩ (_ | _); (on_goal 1 => left); (on_goal 2 => right);
      any_goals apply PCMI.incomp_mul_l <;> tauto

protected lemma Prod.incomp_unfold [PCMI α] [PCMI β] :
    PCMI.incomp (α := α × β) = fun p q => p.1 # q.1 ∨ p.2 # q.2 := rfl

/-! ### Pi PCMI -/

protected instance Pi.instPCMI {ι : Type*} {α : ι → Type*} [∀ i, PCMI (α i)] :
    PCMI (∀ i, α i) where
  incomp f g := ∃ i, f i # g i
  incomp_Irrefl := by constructor; intro _ ⟨_, inc⟩; apply irrefl _ inc
  incomp_Symm := by constructor; intro _ _ ⟨i, _⟩; exists i; symm; trivial
  incomp_mul_l := by
    intro _ _ _ _ ⟨i, _⟩; exists i; apply PCMI.incomp_mul_l <;> tauto

/-! ## PCMC, i.e., PCM with coherence and incompatibility -/

/-- PCM with coherence -/
class PCMC (α : Type u) extends PCMI α where
  /-- Coherence relation -/
  protected coher : α → α → Prop
  /-- Coherence is an equivalence relation -/
  protected coher_IsEquiv : IsEquiv α coher
  /-- Coherence respects validity -/
  protected coher_valid : ∀ a b, coher a b → ✓ a → ✓ b
  /-- Coherence is compatible with `*` -/
  protected coher_mul_l : ∀ a b c, coher a b → coher (a * c) (b * c)
  /-- Incompatibility negates coherence -/
  protected incomp_neg_coher : ∀ a b, ✓ a → a # b → ¬ coher a b

open PCMC

namespace PCMC
variable [PCMC α] (a a' b b' c : α)

@[inherit_doc]
scoped infix:50 " ≎ " => PCMC.coher

/-- Coherence is an equivalence relation -/
protected instance coher_instIsEquiv [PCMC α] :
    IsEquiv α (PCMC.coher) := PCMC.coher_IsEquiv

/-- Coherence is reflexive -/
@[refl] protected lemma coher_refl : a ≎ a := by
  apply refl

/-- Coherence is symmetric -/
@[symm] protected lemma coher_symm : a ≎ b → b ≎ a := by
  apply symm

/-- Coherence is transitive -/
@[trans] protected lemma coher_trans : a ≎ b → b ≎ c → a ≎ c := by
  apply Trans.trans

/-- Coherence respects validity -/
protected lemma coher_valid' : a ≎ b → ✓ a = ✓ b := by
  intro _; ext1;
  constructor <;> apply PCMC.coher_valid; { trivial }; { symm; trivial }

/-- Coherence is compatible with `*` -/
protected lemma coher_mul_r : a ≎ b → c * a ≎ c * b := by
  rw [mul_comm c a, mul_comm c b]; apply PCMC.coher_mul_l

/-- Coherence is compatible with `*` -/
protected lemma coher_mul : a ≎ a' → b ≎ b' → a * b ≎ a' * b' := by
  intro aa' _; trans; { apply PCMC.coher_mul_l; apply aa' }; apply PCMC.coher_mul_r; trivial

end PCMC

/-! ## Product PCMC -/

/-- Product PCMC from a PCMC and a PCMI -/
protected instance Prod.instPCMC [PCMC α] [PCMI β] : PCMC (α × β) where
  coher p q := p.1 ≎ q.1 ∧ p.2 = q.2
  coher_IsEquiv := {
    refl := by intro ⟨_, _⟩; and_intros <;> rfl
    symm := by
      rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, rfl⟩; and_intros; swap; { rfl }; symm; trivial
    trans := by
      rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, rfl⟩ ⟨_, rfl⟩;
      and_intros; swap; { rfl }; trans <;> assumption
  }
  coher_valid := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨coh, rfl⟩ ⟨val, _⟩; and_intros; swap; { trivial };
    apply PCMC.coher_valid _ _ coh val
  coher_mul_l := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, rfl⟩; and_intros; swap; { rfl };
    apply PCMC.coher_mul_l; trivial
  incomp_neg_coher := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨val, _⟩ (inc | inc) ⟨coh, rfl⟩;
    { apply PCMC.incomp_neg_coher _ _ val inc coh }; { apply irrefl _ inc }

/-! ## PCM with probability -/

/-- PCM with probability -/
class PCMP (α : Type u) extends PCM α where
  /-- Probability function -/
  protected prob : α → ℝ≥0∞
  /-- `1` has probability `1` -/
  protected prob_one : prob 1 = 1
  /-- The probability of `*` is the product of the probabilities -/
  protected prob_mul : ∀ a b : α, ✓ a * b → prob (a * b) = prob a * prob b

/-! ## RM, i.e., resource monoid -/

/-- RM, i.e., resource monoid -/
class RM (α : Type u) extends PCMC α, PCMP α
