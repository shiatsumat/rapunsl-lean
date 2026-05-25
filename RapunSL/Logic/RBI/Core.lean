module

public import Iris.BI
public import RapunSL.Math.Algebra.Mset
public import RapunSL.Logic.BI
open Iris OFE BI PCM RM ENNReal

@[expose] public section

/-! # RapunSL's BI -/

namespace RBI

/-! ## RapunSL propositions -/

/-- RapunSL proposition based on a multiset RM -/
def RProp ρ [RM ρ] := LeibnizO (Set (Msetiv ρ))

variable {ρ : Type u} [RM ρ] (P P' Q Q' R : RProp ρ) (r : ρ)

protected instance instMembership : Membership (Msetiv ρ) (RProp ρ) where
  mem P A := P.car A

lemma mem_unfold A : (A ∈ P) = P.car A := rfl

lemma set_ext : (∀ A, A ∈ P ↔ A ∈ Q) → P = Q := by
  intro _; apply congrArg LeibnizO.mk; apply Set.ext; trivial

protected instance instCOFE : COFE (RProp ρ) := instCOFELeibnizO

/-! ## BI structure -/

/-- BI definitions for `RProp` -/
protected instance instBIBase : BIBase (RProp ρ) where
  Entails P Q := ∀ A ∈ P, A ∈ Q
  pure φ := .mk fun _ => φ
  and P Q := .mk fun A => A ∈ P ∧ A ∈ Q
  or P Q := .mk fun A => A ∈ P ∨ A ∈ Q
  imp P Q := .mk fun A => A ∈ P → A ∈ Q
  sForall S := .mk fun A => ∀ P, S P → A ∈ P
  sExists S := .mk fun A => ∃ P, S P ∧ A ∈ P
  emp := .mk fun A => A.val = 1
  sep P Q := .mk fun A => ∃ B C, B ∈ P ∧ C ∈ Q ∧ A.val = B.val * C.val
  wand P Q := .mk fun A => ∀ B ∈ P, ∀ val, ⟨A.val * B.val, val⟩ ∈ Q
  persistently P := .mk fun _ => ⟨1, PCM.valid_one⟩ ∈ P
  later P := P

lemma emp_unfold A : (A ∈ emp (PROP := RProp ρ)) = (A.val = 1) := rfl

lemma forall_simple :
    BIBase.forall = fun P : α → RProp ρ => .mk fun A => ∀ x, A ∈ P x := by
  funext; apply set_ext; intro _; constructor; { tauto };
  simp only [mem_unfold]; rintro _ _ ⟨_, rfl⟩; tauto

lemma exists_simple :
    BIBase.exists = fun P : α → RProp ρ => .mk fun A => ∃ x, A ∈ P x := by
  funext P; apply set_ext; intro _; constructor;
  { rintro ⟨_, ⟨_, rfl⟩, _⟩; tauto }; { rintro ⟨a, _⟩; exists P a; tauto }

@[refl] lemma entails_refl : P ⊢ P := by tauto

@[trans] lemma entails_trans : (P ⊢ Q) → (Q ⊢ R) → P ⊢ R := by tauto

macro:25 P:term:29 " =ᴿ@{" ρ:term "} " Q:term:29 : term =>
  `(Eq (α := RProp $ρ) iprop($P) iprop($Q))
macro:25 P:term:29 " =ᴿ " Q:term:29 : term => `($P =ᴿ@{_} $Q)

lemma entails_antisymm :
    (P ⊢ Q) → (Q ⊢ P) → P = Q := by
  intro _ _; apply set_ext; intro _; constructor <;> tauto

protected instance instPreorder_Entails : Std.Preorder (Entails (PROP := RProp ρ)) where
  refl := entails_refl _
  trans := entails_trans _ _ _

/-- BI properties for `RProp` -/
protected instance instBI : BI (RProp ρ) where
  entails_preorder := inferInstance
  equiv_iff := by
    intro _ _; constructor; { intro rfl; constructor <;> rfl };
    intro ⟨_, _⟩; apply entails_antisymm <;> trivial
  and_ne := by constructor; intro _ _ _ rfl _ _ rfl; rfl
  or_ne := by constructor; intro _ _ _ rfl _ _ rfl; rfl
  imp_ne := by constructor; intro _ _ _ rfl _ _ rfl; rfl
  sForall_ne := by intro _ _ _ eq; rw [liftRel_eq.mp eq]
  sExists_ne := by intro _ _ _ eq; rw [liftRel_eq.mp eq]
  sep_ne := by constructor; intro _ _ _ rfl _ _ rfl; rfl
  wand_ne := by constructor; intro _ _ _ rfl _ _ rfl; rfl
  persistently_ne := by tauto
  later_ne := by tauto
  pure_intro := by tauto
  pure_elim' := by tauto
  and_elim_l := by intro _ _ _ ⟨_, _⟩; tauto
  and_elim_r := by intro _ _ _ ⟨_, _⟩; tauto
  and_intro := by tauto
  or_intro_l := by intro _ _ _ _; left; trivial
  or_intro_r := by intro _ _ _ _; right; trivial
  or_elim := by rintro _ _ _ _ _ _ (_ | _) <;> tauto
  imp_intro := by tauto
  imp_elim := by intro _ _ _ _ _ ⟨_, _⟩; tauto
  sForall_intro := by tauto
  sForall_elim := by tauto
  sExists_intro := by tauto
  sExists_elim := by intro _ _ _ _ ⟨_, _⟩; tauto
  sep_mono := by intro _ _ _ _ _ _ _ ⟨A, B, _, _, _⟩; exists A, B; tauto
  sep_symm := by intro _ _ _ ⟨A, B, _, _, _⟩; exists B, A; rw [mul_comm]; trivial
  emp_sep := by
    intro _; constructor;
    · rintro ⟨_, _⟩ ⟨⟨_, _⟩, _, rfl, val, rfl⟩; simp only [one_mul]; tauto
    · intro A _; exists ⟨1, PCM.valid_one⟩; exists A; rw [one_mul]; trivial
  sep_assoc_l := by
    rintro _ _ _ ⟨_, val⟩ ⟨⟨_, _⟩, C, ⟨A, B, _, _, rfl⟩, _, rfl⟩;
    exists A, ⟨B.val * C.val, by apply PCM.valid_mul_r; rw [←mul_assoc]; apply val⟩;
    simp only [mul_assoc]; and_intros; { trivial }; { exists B, C }; { trivial };
  wand_intro := by
    intro _ _ _ toR A _ B _ _; apply toR; exists A, B
  wand_elim := by
    rintro _ _ _ toR ⟨_, _⟩ ⟨_, _, _, _, rfl⟩; apply toR <;> trivial
  persistently_mono := by tauto
  persistently_idem_2 := by tauto
  persistently_emp_2 := by tauto
  persistently_and_2 := by tauto
  persistently_sExists_1 := by simp only [exists_simple]; tauto
  persistently_absorb_l := by rintro _ _ ⟨_, _⟩ ⟨_, _, _, _, rfl⟩; tauto
  persistently_and_l := by
    intro _ _ A ⟨_, _⟩; exists ⟨1, PCM.valid_one⟩, A; rw [one_mul]; trivial
  later_mono := by tauto
  later_intro := by tauto
  later_sForall_2 := by simp only [forall_simple]; tauto
  later_sExists_false := by simp only [exists_simple]; tauto
  later_sep := by intro _ _; constructor <;> rfl
  later_persistently := by intro _; constructor <;> rfl
  later_false_em := by tauto

@[ext] lemma bi_entails_eq : (P ⊣⊢ Q) → P = Q := by
  intro ⟨_, _⟩; apply entails_antisymm <;> trivial

/-! ### Extra properties -/

lemma not_contra : P ∧ ¬ P ⊢ Q := nofun

lemma not_em : Q ⊢ P ∨ ¬ P := by tauto

lemma choice {β : α → Sort*} (P : ∀ a, β a → RProp ρ) :
    (∀ x, ∃ y, P x y) =ᴿ ∃ f : ∀ a, β a, ∀ x, P x (f x) := by
  simp only [forall_simple, exists_simple];
  apply set_ext; intro _; apply Classical.skolem

lemma persistently_emp_entails : <pers> P =ᴿ ⌜emp ⊢ P⌝ := by
  apply set_ext; intro _; constructor; swap; { tauto };
  intro _ ⟨_, _⟩; rw [emp_unfold]; intro rfl; trivial

/-! ### Utility -/

lemma or_as_exists : P ∨ Q =ᴿ ∃ b : Bool, if b then P else Q := by
  ext1; apply BI.or_as_exists

lemma false_as_exists : False =ᴿ@{ρ} ∃ e : Empty, nomatch e := by
  ext1; apply BI.false_as_exists

lemma sep_comm : P ∗ Q =ᴿ Q ∗ P := by
  ext1; apply BI.sep_comm

lemma and_comm : P ∧ Q =ᴿ Q ∧ P := by
  ext1; apply BI.and_comm

lemma and_assoc : (P ∧ Q) ∧ R =ᴿ P ∧ (Q ∧ R) := by
  ext1; apply BI.and_assoc

/-! ## Ownership -/

/-- Ownership of an element -/
def own (r : ρ) : RProp ρ := .mk fun A => A.val = pure r

lemma own_unfold r A : (A ∈ own (ρ := ρ) r) = (A.val = pure r) := rfl

/-! ### Rules for `own` -/

lemma emp_as_own : emp = own (ρ := ρ) 1 := rfl

lemma own_sep : own (ρ := ρ) r ∗ own s =ᴿ own (r * s) := by
  apply set_ext; intro ⟨_, val⟩; constructor;
  · rintro ⟨⟨_, _⟩, ⟨_, _⟩, rfl, rfl, rfl⟩; simp only [own_unfold, Mseti.pure_mul]
  · intro rfl; revert val; rw [Mseti.pure_mul]; intro val;
    exists ⟨pure r, by apply PCM.valid_mul_l _ (pure s); trivial⟩;
    exists ⟨pure s, by apply PCM.valid_mul_r (pure r); trivial⟩

/-! ## Preciseness -/

/-- Preciseness -/
class Precise (P : RProp ρ) : Prop where
  precise : ∀ A B, A ∈ P → B ∈ P → A = B

lemma precise (P : RProp ρ) [Precise P] : ∀ A B, A ∈ P → B ∈ P → A = B := by
  apply Precise.precise

/-! ### Rules for `Precise` -/

lemma precise_anti [Precise Q] : (P ⊢ Q) → Precise P := by
  intro _; constructor; intro _ _ _ _; apply precise Q <;> tauto

instance false_instPrecise : Precise (ρ := ρ) iprop(False) := by
  constructor; nofun

instance own_instPrecise : Precise (own r) := by
  constructor; intro _; simp only [own_unfold]; grind only

instance emp_instPrecise : Precise (ρ := ρ) emp := own_instPrecise _

instance sep_instPrecise [Precise P] [Precise Q] : Precise iprop(P ∗ Q) := by
  constructor; rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _, elP, elQ, rfl⟩ ⟨_, _, elP', elQ', rfl⟩;
  simp only [precise P _ _ elP elP', precise Q _ _ elQ elQ']

/-! ## Probability -/

/-- Probability -/
class Prob (P : RProp ρ) (p : ℝ≥0∞) : Prop where
  prob : ∀ A ∈ P, RM.prob A.val = p

lemma prob (P : RProp ρ) (p : ℝ≥0∞) [Prob P p] : ∀ A ∈ P, RM.prob A.val = p := by
  apply Prob.prob

/-! ### Rules for `Prob` -/

lemma prob_anti [Prob Q p] : (P ⊢ Q) → Prob P p := by
  intro _; constructor; intro _ _; apply prob Q; tauto

lemma precise_prob [Precise P] : ∃ p, Prob P p := by
  rcases em (∃ A, A ∈ P) with (⟨A, el⟩ | _); swap; { exists 0; constructor; tauto };
  exists (RM.prob A.val); constructor; intro _ el'; rw [precise P _ _ el el']

instance false_instProb p : Prob (ρ := ρ) iprop(False) p := by
  constructor; nofun

instance own_instProb (r : ρ) : Prob (own r) (RM.prob r) := by
  constructor; rintro ⟨_, _⟩ rfl; apply Mseti.prob_pure

instance emp_instProb : Prob (ρ := ρ) emp 1 := by
  constructor; rintro ⟨_, _⟩ rfl; simp only [Mseti.one_unfold, Mseti.prob_pure, RM.prob_one]

instance sep_instProb [Prob P p] [Prob Q q] : Prob iprop(P ∗ Q) (p * q) := by
  constructor; rintro ⟨_, _⟩ ⟨_, _, elP, elQ, rfl⟩;
  rw [RM.prob_mul, prob P p _ elP, prob Q q _ elQ]

end RBI
