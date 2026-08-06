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
@[symm] protected lemma incomp_symm' : a # b → b # a := by
  apply symm

/-- Incompatibility is symmetric -/
protected lemma incomp_symm : a # b ↔ b # a := by
  constructor <;> (intro _; symm; trivial)

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

/-! ## Cancellative PCMI -/

/-- Cancellative PCMI -/
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
  protected coher_valid' : ∀ a b, coher a b → ✓ a → ✓ b
  /-- Coherence is compatible with `*` -/
  protected coher_mul_l : ∀ a b c, coher a b → coher (a * c) (b * c)
  /-- Coherence is compatible with inverse of `*` under validity -/
  protected coher_mul_inv_l : ∀ a b c, ✓ a * c → coher (a * c) (b * c) → coher a b
  /-- Incompatibility negates coherence -/
  protected incomp_neg_coher : ∀ a b, ✓ a → a # b → ¬ coher a b
  /-- Coherence preserves incompatibility -/
  protected coher_incomp : ∀ a b c, coher a b → a # c → b # c

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
@[symm] protected lemma coher_symm' : a ≎ b → b ≎ a := by
  apply symm

/-- Coherence is symmetric -/
protected lemma coher_symm : a ≎ b ↔ b ≎ a := by
  constructor <;> (intro _; symm; trivial)

/-- Coherence is transitive -/
@[trans] protected lemma coher_trans : a ≎ b → b ≎ c → a ≎ c := by
  apply Trans.trans

/-- Coherence respects validity -/
protected lemma coher_valid : a ≎ b → (✓ a ↔ ✓ b) := by
  intro _; constructor <;> apply PCMC.coher_valid'; { trivial }; { symm; trivial }

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
  coher_valid' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨coh, rfl⟩ ⟨val, _⟩; and_intros; swap; { trivial };
    apply PCMC.coher_valid' _ _ coh val
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
  coher_incomp := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨coh, rfl⟩ (inc | inc) <;> simp only at *;
    { left; apply PCMC.coher_incomp _ _ _ coh inc }; { right; trivial }

/-! ## RR, i.e., resource ring -/

/-- RR, i.e., resource ring -/
class RR (α : Type u) extends PCMC α, PCMP α where
  /-- Partial addition over `RR`, formulated as a ternary relation -/
  protected radd : α → α → α → Prop
  /-- `+ᴿ` is unique -/
  protected radd_unique : ∀ a b c c', radd a b c → radd a b c' → c = c'
  /-- `+ᴿ` is defined for coherent arguments -/
  protected coher_radd : ∀ a b, a ≎ b → ∃ c, radd a b c
  /-- `+ᴿ` requires coherence -/
  protected radd_coher : ∀ a b c, radd a b c → a ≎ b
  /-- `+ᴿ` is coherent with the left argument -/
  protected radd_coher_l : ∀ a b c, radd a b c → a ≎ c
  /-- `+ᴿ` is commutative -/
  protected radd_comm' : ∀ a b c, radd a b c → radd b a c
  /-- `+ᴿ` is associative -/
  protected radd_assoc_l : ∀ a b c ab abc,
    radd a b ab → radd ab c abc → ∃ bc, radd b c bc ∧ radd a bc abc
  /-- `*` distributes over `+ᴿ` -/
  protected radd_mul_l : ∀ a b c bc,
    radd b c bc → radd (a * b) (a * c) (a * bc)

open RR

/-! ### Utility -/

namespace RR
variable [RR α] (a b c ab bc abc : α)

@[inherit_doc RR.radd]
scoped macro:50 a:term:50 " +ᴿ " b:term " =ᴿ " c:term:50 : term => `(RR.radd $a $b $c)

scoped delab_rules RR.radd
  | `($_ $a $b $c) => `($a +ᴿ $b =ᴿ $c)

open Classical in
/-- Total version of `radd` -/
protected noncomputable instance instAdd : Add α where
  add a b := if h : a ≎ b
    then Classical.choose (RR.coher_radd a b h) else 1

open Classical in
/-- Unfold `+` for `RR` -/
protected lemma add_unfold :
    (HAdd.hAdd : α → α → α) = fun a b => if h : a ≎ b
      then Classical.choose (RR.coher_radd a b h) else 1 := rfl

/-- Get `+ᴿ` for `+` -/
protected lemma add_radd : a ≎ b → a +ᴿ b =ᴿ a + b := by
  intro h; simp only [RR.add_unfold, dif_pos h]; apply Classical.choose_spec

/-- Get `+` from `+ᴿ` -/
protected lemma radd_add : a ≎ b → a +ᴿ b =ᴿ c → a + b = c := by
  intro h e; apply RR.radd_unique _ _ _ _ _ e; apply RR.add_radd _ _ h

/-- Unfold `+` under `¬ (a ≎ b)` -/
protected lemma add_one : ¬ a ≎ b → a + b = 1 := by
  intro h; simp only [RR.add_unfold, dif_neg h]

/-- `+ᴿ` is commutative -/
@[simp]
protected lemma radd_comm : a +ᴿ b =ᴿ c ↔ b +ᴿ a =ᴿ c := by
  constructor <;> (intro _; apply RR.radd_comm'; trivial)

open Classical in
/-- `+` is commutative -/
protected noncomputable instance instAddCommMagma : AddCommMagma α where
  add_comm := by
    intro a b; rcases Classical.em (a ≎ b) with (h | h); swap;
    { rw [RR.add_one _ _ h]; symm; apply RR.add_one; rw [PCMC.coher_symm]; trivial }
    apply RR.radd_unique _ _ _ _ (RR.add_radd _ _ h); apply RR.radd_comm';
    apply RR.add_radd; symm; trivial

/-- `+ᴿ` is coherent with the right argument -/
protected lemma radd_coher_r : a +ᴿ b =ᴿ c → b ≎ c := by
  rw [RR.radd_comm]; apply RR.radd_coher_l

/-- `+` is coherent with the left argument -/
protected lemma add_coher_l : a ≎ b → a + b ≎ a := by
  intro coh; symm; apply RR.radd_coher_l; apply RR.add_radd; trivial

/-- `+` is coherent with the right argument -/
protected lemma add_coher_r : a ≎ b → a + b ≎ b := by
  intro coh; symm; apply RR.radd_coher_r; apply RR.add_radd; trivial

/-- `+` preserves the validity -/
protected lemma add_valid_l : a ≎ b → (✓ (a + b) ↔ ✓ a) := by
  intro coh; apply PCMC.coher_valid; apply RR.add_coher_l; trivial

/-- `+` preserves the validity -/
protected lemma add_valid_r : a ≎ b → (✓ (a + b) ↔ ✓ b) := by
  intro coh; apply PCMC.coher_valid; apply RR.add_coher_r; trivial

/-- `+` inherits incompatibility from the left summand -/
protected lemma add_incomp_l : a ≎ b → a # c → a + b # c := by
  intro coh inc; apply PCMC.coher_incomp a;
  { symm; apply RR.add_coher_l; trivial }; { trivial }

/-- `+` inherits incompatibility from the right summand -/
protected lemma add_incomp_r : a ≎ b → b # c → a + b # c := by
  intro coh inc; rw [add_comm]; apply RR.add_incomp_l;
  { symm; trivial }; { trivial }

/-- `+` preserves incompatibility of summands -/
protected lemma add_incomp (a' b' : α) : a ≎ b → a' ≎ b' → a # a' → a + b # a' + b' := by
  intro coh coh' inc; symm; apply RR.add_incomp_l _ _ _ coh'; symm;
  apply RR.add_incomp_l _ _ _ coh; trivial

/-- `+ᴿ` is associative -/
protected lemma radd_assoc_r :
    b +ᴿ c =ᴿ bc → a +ᴿ bc =ᴿ abc → ∃ ab, a +ᴿ b =ᴿ ab ∧ ab +ᴿ c =ᴿ abc := by
  simp only [RR.radd_comm b c, RR.radd_comm a bc, RR.radd_comm a b, RR.radd_comm _ c abc];
  apply RR.radd_assoc_l

/-- `+` is associative under coherence -/
protected lemma add_assoc : a ≎ b → b ≎ c → (a + b) + c = a + (b + c) := by
  intro h h'; have e1 := RR.add_radd _ _ h;
  have e2 := RR.add_radd (a + b) c
    (by trans; swap; { apply h' }; symm; apply RR.radd_coher_r _ _ _ e1);
  have ⟨bc, e1', e2'⟩ := RR.radd_assoc_l _ _ _ _ _ e1 e2;
  rcases RR.radd_add _ _ _ h' e1' with rfl; symm;
  apply RR.radd_add _ _ _ _ e2'; trans; { exact h }; apply RR.radd_coher_l _ _ _ e1'

/-- `+ᴿ` distributes over `*` -/
protected lemma radd_mul_r : a +ᴿ b =ᴿ ab → a * c +ᴿ b * c =ᴿ ab * c := by
  simp only [mul_comm _ c]; apply RR.radd_mul_l

/-- `+` distributes over `*` under coherence -/
protected lemma add_mul_l : b ≎ c → a * (b + c) = a * b + a * c := by
  intro h; have e1 := RR.add_radd _ _ h;
  have e2 := RR.radd_mul_l a _ _ _ e1; symm; apply RR.radd_add _ _ _ _ e2;
  apply PCMC.coher_mul_r; trivial

/-- `+` distributes over `*` under coherence -/
protected lemma add_mul_r : a ≎ b → (a + b) * c = a * c + b * c := by
  intro _; simp only [mul_comm _ c]; apply RR.add_mul_l; trivial

end RR

/-! ## Product RR -/

/-- Product RR from an RR and a cancellative PCMI -/
protected instance Prod.instRR (α : Type u) (β : Type u') [RR α] [PCMICan β] :
    RR (α × β) where
  prob p := PCMP.prob p.1
  prob_one := by apply PCMP.prob_one
  prob_mul := by intro _ _ ⟨_, _⟩; apply PCMP.prob_mul; trivial
  radd p q r := RR.radd p.1 q.1 r.1 ∧ p.2 = q.2 ∧ q.2 = r.2
  radd_unique := by
    intro (_, _) (_, _) (_, _) (_, _); simp only; intro ⟨e, rfl, rfl⟩ ⟨e', rfl, rfl⟩;
    congr; exact RR.radd_unique _ _ _ _ e e'
  coher_radd := by
    rintro ⟨_, b⟩ ⟨_, _⟩ ⟨e, rfl⟩; have ⟨s, _⟩ := RR.coher_radd _ _ e;
    exists ⟨s, b⟩
  radd_coher := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, rfl, rfl⟩; and_intros; swap; { rfl };
    apply RR.radd_coher; trivial
  radd_coher_l := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, rfl, rfl⟩; and_intros; swap; { rfl };
    apply RR.radd_coher_l; trivial
  radd_comm' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, rfl, rfl⟩; simp only at *;
    rw [RR.radd_comm]; trivial
  radd_assoc_l := by
    rintro ⟨_, b⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨e, rfl, rfl⟩ ⟨e', rfl, rfl⟩; simp only at *;
    have ⟨s, _, _⟩ := RR.radd_assoc_l _ _ _ _ _ e e'; exists ⟨s, b⟩
  radd_mul_l := by
    rintro ⟨_, b⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨e, rfl, rfl⟩; simp only at *;
    and_intros; rotate_left 1; { rfl }; { rfl }; apply RR.radd_mul_l; trivial
