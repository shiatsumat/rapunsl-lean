module

public import RapunSL.Math.Algebra.PCM
open PCM

@[expose] public section

/-! # RR, i.e., resource ring -/

/-! ## PCMI, i.e., PCM with incompatibility -/

/-- PCM with incompatibility -/
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
protected lemma incomp_mul_r : ✓ a * b → b # c → a * b # c := by
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

/-! ## Cancellable PCMI -/

/-- Cancellable PCMI -/
class PCMICan (α : Type u) extends PCMI α, PCMCan α

protected instance Excl.instPCMICan : PCMICan (Excl α) where

protected instance Prod.instPCMICan [PCMICan α] [PCMICan β] : PCMICan (α × β) where

protected instance Pi.instPCMICan {ι : Type*} {α : ι → Type*} [∀ i, PCMICan (α i)] :
    PCMICan (∀ i, α i) where

/-! ## PCMC, i.e., PCM with coherence -/

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
  /-- Coherence is compatible with inverse of `*` under validity -/
  protected coher_mul_inv_l : ∀ a b c, ✓ a * c → coher (a * c) (b * c) → coher a b
  /-- Incompatibility negates coherence -/
  protected incomp_neg_coher : ∀ a b, ✓ a → a # b → ¬ coher a b

open PCMC

namespace PCMC
variable [PCMC α] (a a' b b' c : α)

@[inherit_doc]
scoped infix:50 " ≎ " => PCMC.coher

/-- Coherence is an equivalence relation -/
protected instance coher_instIsEquiv :
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
protected lemma coher_mul_r : b ≎ c → a * b ≎ a * c := by
  simp only [mul_comm a]; apply PCMC.coher_mul_l

/-- Coherence is compatible with `*` -/
protected lemma coher_mul : a ≎ a' → b ≎ b' → a * b ≎ a' * b' := by
  intro aa' _; trans; { apply PCMC.coher_mul_l; apply aa' }; apply PCMC.coher_mul_r; trivial

/-- Coherence is compatible with inverse of `*` under validity -/
protected lemma coher_mul_inv_r : ✓ a * b → a * b ≎ a * c → b ≎ c := by
  simp only [mul_comm a]; apply PCMC.coher_mul_inv_l

end PCMC

/-! ## Product PCMC -/

/-- Product PCMC from a PCMC and a cancellative PCMI -/
protected instance Prod.instPCMC [PCMC α] [PCMICan β] : PCMC (α × β) where
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
  coher_mul_inv_l := by
    intro (_, _) (_, _) (_, _) ⟨_, _⟩; simp only [mk_mul_mk] at *; intro ⟨_, _⟩;
    and_intros; { apply PCMC.coher_mul_inv_l <;> trivial };
    { apply PCMCan.mul_cancel_l <;> trivial }
  incomp_neg_coher := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨val, _⟩ (inc | inc) ⟨coh, rfl⟩;
    { apply PCMC.incomp_neg_coher _ _ val inc coh }; { apply irrefl _ inc }

/-! ## RR, i.e., resource ring -/

/-- RR, i.e., resource ring -/
class RR (α : Type u) extends PCMC α, PCMP α where
  /-- Addition, defined only for coherent elements -/
  protected radd : ∀ a b : α, a ≎ b → α
  /-- Addition preserves coherence -/
  protected radd_coher_l : ∀ a b h, radd a b h ≎ a
  /-- Addition is commutative -/
  protected radd_comm : ∀ a b h₁ h₂, radd a b h₁ = radd b a h₂
  /-- Addition is associative -/
  protected radd_assoc : ∀ a b c h₁ h₂ h₃ h₄,
    radd (radd a b h₁) c h₂ = radd a (radd b c h₃) h₄
  /-- Product distributes over addition -/
  protected radd_mul_l : ∀ a b c h₁ h₂, a * radd b c h₁ = radd (a * b) (a * c) h₂

open RR

/-! ### Utility -/

namespace RR
variable [RR α] (a b c : α)

scoped macro:65 a:term:65 " +[" h:term "] " b:term:66 : term => `(RR.radd $a $b $h)

scoped delab_rules RR.radd
  | `($_ $a $b $h) => `($a +[$h] $b)

/-- Addition is commutative -/
protected lemma radd_comm' h : a +[h] b = b +[Std.Symm.symm _ _ h] a := by
  apply RR.radd_comm

/-- Addition preserves coherence -/
protected lemma radd_coher_r h : a +[h] b ≎ b := by
  rw [RR.radd_comm']; apply RR.radd_coher_l

/-- Helper for `radd_assoc_l` -/
protected lemma radd_assoc_l_aux h : a +[h] b ≎ c → b ≎ c := by
  intro h'; trans; swap; { exact h' }; symm; apply RR.radd_coher_r

/-- Helper for `radd_assoc_l` -/
protected lemma radd_assoc_l_aux' h h' :
    a ≎ b +[RR.radd_assoc_l_aux a b c h h'] c := by
  trans; { exact h }; symm; apply RR.radd_coher_l

/-- Addition is associative -/
protected lemma radd_assoc_l h h' :
    (a +[h] b) +[h'] c =
      a +[RR.radd_assoc_l_aux' _ _ _ h h'] (b +[RR.radd_assoc_l_aux _ _ _ h h'] c) := by
  apply RR.radd_assoc

/-- Helper for `radd_assoc_r` -/
protected lemma radd_assoc_r_aux h : a ≎ b +[h] c → a ≎ b := by
  intro h'; trans; { exact h' }; apply RR.radd_coher_l

/-- Helper for `radd_assoc_r` -/
protected lemma radd_assoc_r_aux' h h' :
    a +[RR.radd_assoc_r_aux a b c h h'] b ≎ c := by
  trans; swap; { exact h }; apply RR.radd_coher_r

/-- Addition is associative -/
protected lemma radd_assoc_r h h' :
    a +[h'] (b +[h] c) =
      (a +[RR.radd_assoc_r_aux _ _ _ h h'] b) +[RR.radd_assoc_r_aux' _ _ _ h h'] c := by
  symm; apply RR.radd_assoc

/-- Product distributes over addition -/
protected lemma radd_mul_r h₁ h₂ : (a +[h₁] b) * c = a * c +[h₂] b * c := by
  simp only [mul_comm _ c]; apply RR.radd_mul_l

/-- Product distributes over addition -/
protected lemma radd_mul_l_fwd h :
    a * (b +[h] c) = a * b +[PCMC.coher_mul_r _ _ _ h] a * c := by
  apply RR.radd_mul_l

/-- Product distributes over addition -/
protected lemma radd_mul_l_bwd val h :
    a * b +[h] a * c = a * (b +[PCMC.coher_mul_inv_r _ _ _ val h] c) := by
  symm; apply RR.radd_mul_l

/-- Product distributes over addition -/
protected lemma radd_mul_r_fwd h :
    (a +[h] b) * c = a * c +[PCMC.coher_mul_l _ _ _ h] b * c := by
  apply RR.radd_mul_r

/-- Product distributes over addition -/
protected lemma radd_mul_r_bwd val h :
    a * c +[h] b * c = (a +[PCMC.coher_mul_inv_l _ _ _ val h] b) * c := by
  symm; apply RR.radd_mul_r

end RR

/-! ## Product RR -/

/-- Product RR from an RR and a cancellative PCMI -/
protected instance Prod.instRR (α : Type u) (β : Type u') [RR α] [PCMICan β] :
    RR (α × β) where
  prob p := PCMP.prob p.1
  prob_one := by apply PCMP.prob_one
  prob_mul := by intro _ _ ⟨_, _⟩; apply PCMP.prob_mul; trivial
  radd p q h := (RR.radd p.1 q.1 h.1, p.2)
  radd_coher_l := by
    intro (_, _) (_, _) h; generalize h.1 = h1; rcases h with ⟨_, rfl⟩;
    and_intros; swap; { rfl }; apply RR.radd_coher_l
  radd_comm := by
    intro (_, _) (_, _) h _; generalize h.1 = h1; rcases h with ⟨_, rfl⟩;
    simp only; ext; { apply RR.radd_comm }; { rfl }
  radd_assoc := by
    intro (_, _) (_, _) (_, _) h; generalize h.1 = h1; rcases h with ⟨_, rfl⟩;
    intro h; generalize h.1 = h1; rcases h with ⟨_, rfl⟩; simp only at *;
    intro _ _; ext; { apply RR.radd_assoc }; { rfl }
  radd_mul_l := by
    intro (_, _) (_, _) (_, _) h _; generalize h.1 = h1; rcases h with ⟨_, rfl⟩;
    ext; { apply RR.radd_mul_l }; { trivial }
