module

public import Iris.BI
public import RapunSL.Math.PCM
public import RapunSL.Logic.BI
import Mathlib.Logic.Equiv.Bool
open Iris OFE BI PCM Mset

@[expose] public section

/-! # RapunSL's BI -/

namespace RBI

/-! ## RapunSL propositions -/

/-- RapunSL proposition based on a multiset PCM -/
def RProp ρ [PCMa ρ] := LeibnizO (Set (Mset ρ))

variable {ρ : Type u} [PCMa ρ] (P P' Q Q' R : RProp ρ) (r : ρ)

protected instance instMembership : Membership (Mset ρ) (RProp ρ) where
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
  emp := .mk fun A => A = 1
  sep P Q := .mk fun A => ∃ B ∈ P, ∃ C ∈ Q, A = B * C
  wand P Q := .mk fun A => ∀ B ∈ P, A * B ∈ Q
  persistently P := .mk fun _ => 1 ∈ P
  later P := P

lemma emp_unfold A : (A ∈ emp (PROP := RProp ρ)) = (A = 1) := rfl

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
  sep_mono := by
    intro _ _ _ _ _ _ _ ⟨A, _, B, _, _⟩; exists A, by tauto, B; tauto
  sep_symm := by
    rintro _ _ _ ⟨A, _, B, _, rfl⟩; exists B, by trivial, A; rw [mul_comm]; trivial
  emp_sep := by
    intro _; constructor;
    · rintro _ ⟨_, eq, _, _, rfl⟩; rw [emp_unfold] at *; rw [eq, one_mul]; trivial
    · intro A _; exists 1; and_intros; { rfl }; exists A; simp only [one_mul]; trivial
  sep_assoc_l := by
    rintro _ _ _ _ ⟨_, ⟨A, _, B, _, rfl⟩, C, _, rfl⟩;
    exists A, by trivial, B * C; simp only [mul_assoc, _root_.and_true];
    exists B, by trivial, C, by trivial
  wand_intro := by
    intro _ _ _ toR A _ B _; apply toR; exists A, by trivial, B
  wand_elim := by
    rintro _ _ _ toR _ ⟨_, _, _, _, rfl⟩; apply toR <;> trivial
  persistently_mono := by tauto
  persistently_idem_2 := by tauto
  persistently_emp_2 := by tauto
  persistently_and_2 := by tauto
  persistently_sExists_1 := by simp only [exists_simple]; tauto
  persistently_absorb_l := by
    rintro _ _ _ ⟨_, _, _, _, rfl⟩; tauto
  persistently_and_l := by
    intro _ _ A ⟨_, _⟩; exists 1, by trivial, A; rw [one_mul]; trivial
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
  intro _ _; rw [emp_unfold]; intro rfl; trivial

/-! ### Utility -/

lemma or_exists : P ∨ Q =ᴿ ∃ b : Bool, if b then P else Q := by
  ext; apply BI.or_exists

lemma false_exists : False =ᴿ@{ρ} ∃ e : Empty, nomatch e := by
  ext; apply BI.false_exists

lemma sep_comm : P ∗ Q =ᴿ Q ∗ P := by
  ext1; apply BI.sep_comm

/-! ## RapunSL-specific structure -/

/-! ### Ownership -/

/-- Ownership of an element -/
def own (r : ρ) : RProp ρ := .mk fun A => A = pure r

lemma own_unfold r A : (A ∈ own (ρ := ρ) r) = (A = pure r) := rfl

/-! ### Multiset connectives -/

/-- No behavior -/
def nb : RProp ρ := .mk fun A => A = ∅

lemma nb_unfold A : (A ∈ nb (ρ := ρ)) = (A = ∅) := rfl

/-- Multiset sum -/
def oplus (P Q : RProp ρ) : RProp ρ :=
  .mk fun A => ∃ B ∈ P, ∃ C ∈ Q, A = B ⊕ᴹ C

scoped syntax:30 term:31 " ⊕ " term:30 : term

/-- Big multiset sum -/
def bigoplus (P : ι → RProp ρ) : RProp ρ :=
  .mk fun A => ∃ B : ι → Mset ρ, (∀ i, B i ∈ P i) ∧ A = ⨁ᴹ i, B i

scoped syntax "⨁ " Lean.Parser.Term.funBinder ", " term : term

/-- Pine, the right adjoint of `⊕` -/
def pine (P Q : RProp ρ) : RProp ρ :=
  .mk fun A => ∀ B ∈ P, B ⊕ᴹ A ∈ Q

scoped syntax:25 term:26 " -⊕ " term:25 : term

scoped macro_rules
  | `(iprop($P ⊕ $Q)) => `(RBI.oplus iprop($P) iprop($Q))
  | `(iprop(⨁ $i, $P)) => `(RBI.bigoplus (fun $i => iprop($P)))
  | `(iprop($P -⊕ $Q)) => `(pine iprop($P) iprop($Q))

delab_rule RBI.oplus
  | `($_ $P $Q) => do ``(iprop($(←unpackIprop P) ⊕ $(←unpackIprop Q)))

delab_rule RBI.bigoplus
  | `($_ fun $i => $P) => do ``(iprop(⨁ $i, $(←unpackIprop P)))

delab_rule RBI.pine
  | `($_ $P $Q) => do ``(iprop($(←unpackIprop P) -⊕ $(←unpackIprop Q)))

/-! ### Judgments -/

/-- Preciseness -/
class Precise (P : RProp ρ) : Prop where
  precise : ∀ A ∈ P, ∀ B ∈ P, A = B

lemma precise (P : RProp ρ) [Precise P] : ∀ A ∈ P, ∀ B ∈ P, A = B := by
  apply Precise.precise

/-- Inhabitance, or being not `False` -/
class Inhab (P : RProp ρ) : Prop where
  inhab : ∃ A, A ∈ P

lemma inhab (P : RProp ρ) [Inhab P] : ∃ A, A ∈ P := by
  apply Inhab.inhab

/-- Multiset inhabitance -/
class Nonnb (P : RProp ρ) : Prop where
  nonnb : ∀ A ∈ P, A.inhab

lemma nonnb (P : RProp ρ) [Nonnb P] : ∀ A ∈ P, A.inhab := by
  apply Nonnb.nonnb

/-! ### Entailment rules for `own` -/

lemma emp_own : emp = own (ρ := ρ) 1 := rfl

lemma own_sep : own (ρ := ρ) r ∗ own s =ᴿ own (r * s) := by
  apply set_ext; intro _; constructor;
  · rintro ⟨_, rfl, _, rfl, rfl⟩; rw [own_unfold, ←Mset.pure_mul]
  · intro rfl; exists pure r, rfl, pure s; and_intros; { rfl }; { rw [←Mset.pure_mul] }

/-! ### Entailment rules for `nb`, `⊕`, `⨁` and `-⊕` -/

lemma nb_bigoplus : nb = bigoplus (ρ := ρ) (ι := Empty) nofun := by
  apply set_ext; intro _; rw [nb_unfold]; constructor;
  · intro rfl; exists nofun; simp only [IsEmpty.forall_iff, true_and];
    rw [Mset.empty_bigoplus]; rfl
  · rintro ⟨_, _, rfl⟩; rw [Mset.empty_bigoplus]; congr; ext1; trivial

lemma oplus_bigoplus : P ⊕ Q =ᴿ ⨁ (b : Bool), if b then P else Q := by
  apply set_ext; intro _; constructor;
  · rintro ⟨A, _, B, _, rfl⟩; exists fun b => if b then A else B;
    simp only; constructor; { grind only }; rw [Mset.oplus_bigoplus]
  · rintro ⟨A, el, rfl⟩; exists A true, el true, A false, el false;
    rw [Mset.oplus_bigoplus]; grind only

lemma unary_bigoplus : (⨁ (_ : Unit), P) =ᴿ P := by
  apply set_ext; intro A; constructor;
  · rintro ⟨_, _, rfl⟩; rw [Mset.unary_bigoplus]; tauto
  · intro _; exists fun _ => A; simp only [Mset.unary_bigoplus]; tauto

@[gcongr] lemma bigoplus_mono (P Q : ι → RProp ρ) :
    (∀ i, P i ⊢ Q i) → (⨁ i, P i) ⊢ ⨁ i, Q i := by
  intro _ _ ⟨A, _, _⟩; exists A; tauto

@[gcongr] lemma oplus_mono : (P ⊢ P') → (Q ⊢ Q') → P ⊕ Q ⊢ P' ⊕ Q' := by
  intro _ _; grw [oplus_bigoplus, oplus_bigoplus]; gcongr; grind only

private lemma bigoplus_comm_fwd (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ i, P i) ⊢ ⨁ j, P (f j) := by
  intro _ ⟨A, _, eq⟩; exists A ∘ f; rw [eq, Mset.bigoplus_comm f]; tauto

private lemma bigoplus_comm_bwd (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ j, P (f j)) ⊢ ⨁ i, P i := by
  grw [bigoplus_comm_fwd f.symm]; gcongr; rw [Equiv.apply_symm_apply]

lemma bigoplus_comm (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ i, P i) =ᴿ ⨁ j, P (f j) := by
  ext1; constructor; { apply bigoplus_comm_fwd }; { apply bigoplus_comm_bwd }

lemma bigoplus_comm' (P : ι → RProp ρ) (Q : ι' → RProp ρ) (f : ι → ι') (g : ι' → ι) :
    (∀ i, P i = Q (f i)) → g.LeftInverse f → g.RightInverse f →
    (⨁ i, P i) =ᴿ ⨁ j, Q j := by
  intro _ li ri; rw [bigoplus_comm ⟨f, g, li, ri⟩]; congr; ext1 _; tauto

lemma oplus_comm : P ⊕ Q =ᴿ Q ⊕ P := by
  simp only [oplus_bigoplus]; rw [bigoplus_comm Equiv.boolNot]; congr;
  simp only [Equiv.boolNot_apply]; grind only

lemma bigoplus_assoc {ι' : ι → Type} (P : ∀ i, ι' i → RProp ρ) :
    (⨁ i, ⨁ j, P i j) =ᴿ ⨁ (⟨i, j⟩ : Sigma ι'), P i j := by
  ext1; constructor;
  · intro _ ⟨_, el, eq⟩; simp only at *; subst eq; have ⟨A, el⟩ := Classical.skolem.mp el;
    exists fun ⟨i, j⟩ => A i j; simp only at *; and_intros; { grind only };
    trans; swap; { apply Mset.bigoplus_assoc (fun i j => (A i j)) }; grind only
  · rintro _ ⟨A, el, rfl⟩; exists fun i => ⨁ᴹ j, A ⟨i, j⟩; simp only at *;
    and_intros; swap;
    { symm; apply Mset.bigoplus_assoc }; intro i; exists fun j => A ⟨i, j⟩;
    simp only [and_true]; intro _; apply el ⟨_, _⟩

lemma oplus_assoc : (P ⊕ Q) ⊕ R =ᴿ P ⊕ (Q ⊕ R) := by
  have eq : ∀ P Q R : RProp ρ,
      (P ⊕ Q) ⊕ R =ᴿ ⨁ (b : Bool),
        ⨁ (i : match b with | true => Bool | false => Unit),
          match b with | true => if i then P else Q | false => R := by
    intro _ _ _; simp only [oplus_bigoplus]; congr; ext1 b; cases b <;> simp only;
    { rw [unary_bigoplus]; rfl }; { rfl }
  rw [eq, oplus_comm, eq]; simp only [bigoplus_assoc];
  apply bigoplus_comm' _ _
    (fun | ⟨true, b⟩ => if b then ⟨false, ()⟩ else ⟨true, true⟩ | ⟨false, _⟩ => ⟨true, false⟩)
    (fun | ⟨true, b⟩ => if b then ⟨true, false⟩ else ⟨false, ()⟩ | ⟨false, _⟩ => ⟨true, true⟩) <;>
    { rintro ⟨(_ | _), i⟩; { rfl }; cases i <;> rfl }

lemma oplus_nb : P ⊕ nb =ᴿ P := by
  have eq : P ⊕ nb =ᴿ ⨁ (b : Bool),
      ⨁ (i : match b with | true => Unit | false => Empty), match b with | true => P := by
    rw [oplus_bigoplus, nb_bigoplus]; congr; ext1 b; cases b <;> simp only;
    { simp only [Bool.false_eq_true, reduceIte]; congr; ext1 _; trivial };
    { simp only [reduceIte]; rw [unary_bigoplus] }
  rw [eq, bigoplus_assoc]; trans; swap; { apply unary_bigoplus };
  apply bigoplus_comm' _ _ (fun | ⟨true, _⟩ => ()) (fun _ => ⟨true, ()⟩) <;>
    { rintro ⟨(_ | _), _⟩ <;> trivial }

lemma nb_oplus : nb ⊕ P =ᴿ P := by rw [oplus_comm, oplus_nb]

lemma pine_intro_l : (P ⊕ Q ⊢ R) → Q ⊢ P -⊕ R := by
  intro toR A _ B _; apply toR; exists B, by trivial, A, by trivial

lemma pine_intro_r : (P ⊕ Q ⊢ R) → P ⊢ Q -⊕ R := by
  rw [oplus_comm]; apply pine_intro_l

lemma pine_elim_l : P ⊕ (P -⊕ Q) ⊢ Q := by
  rintro _ ⟨_, _, _, _, rfl⟩; tauto

lemma pine_elim_r : (P -⊕ Q) ⊕ P ⊢ Q := by
  rw [oplus_comm]; apply pine_elim_l

lemma pine_adj : (P ⊕ Q ⊢ R) = (Q ⊢ P -⊕ R) := by
  ext1; constructor; { apply pine_intro_l };
  intro Qto; grw [Qto]; apply pine_elim_l

lemma oplus_exists_l (Q : α → RProp ρ) : P ⊕ (∃ a, Q a) =ᴿ ∃ a, P ⊕ Q a := by
  ext1; constructor; swap; { apply exists_elim; intro a; grw [exists_intro (Ψ := Q) a] };
  rw [pine_adj]; apply exists_elim; intro a; rw [←pine_adj]; apply exists_intro a

lemma oplus_exists_r (P : α → RProp ρ) Q : (∃ a, P a) ⊕ Q =ᴿ ∃ a, P a ⊕ Q := by
  rw [oplus_comm, oplus_exists_l]; congr; ext1 _; rw [oplus_comm]

lemma oplus_or_l : P ⊕ (Q ∨ R) =ᴿ (P ⊕ Q) ∨ (P ⊕ R) := by
  simp only [or_exists, oplus_exists_l]; congr; ext1 b; cases b <;> rfl

lemma oplus_or_r : (P ∨ Q) ⊕ R =ᴿ (P ⊕ R) ∨ (Q ⊕ R) := by
  rw [oplus_comm, oplus_or_l, oplus_comm, oplus_comm R]

lemma oplus_false_l : P ⊕ False =ᴿ False := by
  simp only [false_exists, oplus_exists_l]; congr; ext1 _; trivial

lemma oplus_false_r : False ⊕ P =ᴿ False := by
  rw [oplus_comm, oplus_false_l]

lemma bigoplus_exists {α : ι → Sort*} (P : ∀ i, α i → RProp ρ) :
    (⨁ i, ∃ a, P i a) =ᴿ ∃ f : (∀ i, α i), ⨁ i, P i (f i) := by
  ext1; constructor; swap;
  { apply exists_elim; intro f; gcongr; apply exists_intro };
  simp only [exists_simple]; rintro _ ⟨F, el, rfl⟩;
  have ⟨f, el⟩ := Classical.skolem.mp el; exists f; exists F

/-! ### Entailment rules for interaction of `nb`, `⊕` and `⨁` with `∗` -/

lemma bigoplus_frame_l (Q : ι → RProp ρ) : P ∗ (⨁ i, Q i) ⊢ ⨁ i, P ∗ Q i := by
  rintro _ ⟨A, _, _, ⟨B, _, rfl⟩, rfl⟩; exists fun i => A * B i; simp only; and_intros;
  { intros i; exists A, by trivial, B i, by tauto }; { rw [Mset.mul_bigoplus_l] }

lemma bigoplus_frame_r (P : ι → RProp ρ) Q : (⨁ i, P i) ∗ Q ⊢ ⨁ i, P i ∗ Q := by
  grw [sep_comm, bigoplus_frame_l]; gcongr 1; rw [sep_comm]

lemma oplus_frame_l : P ∗ (Q ⊕ R) ⊢ (P ∗ Q) ⊕ (P ∗ R) := by
  grw [oplus_bigoplus, oplus_bigoplus, bigoplus_frame_l];
  gcongr with b; cases b <;> rfl

lemma oplus_frame_r : (P ⊕ Q) ∗ R ⊢ (P ∗ R) ⊕ (Q ∗ R) := by
  grw [sep_comm, oplus_frame_l, sep_comm, sep_comm R]

lemma nb_sep_l : P ∗ nb ⊢ nb := by
  simp only [nb_bigoplus]; grw [bigoplus_frame_l]; gcongr; tauto

lemma nb_sep_r : nb ∗ P ⊢ nb := by grw [sep_comm, nb_sep_l]

lemma bigoplus_unframe_l P (Q : ι → RProp ρ) [Nonempty ι] [Precise P] :
    (⨁ i, P ∗ Q i) =ᴿ P ∗ ⨁ i, Q i := by
  ext1; constructor; swap; { apply bigoplus_frame_l };
  rintro _ ⟨_, el, rfl⟩;
  have ⟨A, el⟩ := Classical.skolem.mp el; have AQ i := (el i).left;
  have ⟨B, el⟩ := Classical.skolem.mp (fun i => (el i).right);
  have i0 : ι := Classical.choice inferInstance;
  exists A i0, by tauto, ⨁ᴹ i, B i; and_intros; { exists B, fun i => (el i).left };
  rw [Mset.mul_bigoplus_l]; congr; ext1 i; rw [precise P _ (AQ i0) _ (AQ i)]; grind only

lemma bigoplus_unframe_r (P : ι → RProp ρ) Q [Nonempty ι] [Precise Q] :
    (⨁ i, P i ∗ Q) =ᴿ ((⨁ i, P i) ∗ Q) := by
  ext1; constructor; swap; { apply bigoplus_frame_r };
  grw [sep_comm, ←bigoplus_unframe_l _ _]; gcongr 1; rw [sep_comm]

lemma oplus_unframe_l [Precise P] : (P ∗ Q) ⊕ (P ∗ R) =ᴿ P ∗ (Q ⊕ R) := by
  ext1; constructor; swap; { apply oplus_frame_l };
  simp only [oplus_bigoplus]; grw [←bigoplus_unframe_l]; gcongr with b; cases b <;> rfl

lemma oplus_unframe_r [Precise R] : (P ∗ R) ⊕ (Q ∗ R) =ᴿ (P ⊕ Q) ∗ R := by
  ext1; constructor; swap; { apply oplus_frame_r };
  grw [sep_comm iprop(P ⊕ Q), ←oplus_unframe_l, sep_comm, sep_comm Q]

lemma nb_unsep_l [Inhab P] : nb =ᴿ P ∗ nb := by
  ext1; constructor; swap; { apply nb_sep_l };
  intro _ rfl; have ⟨A, _⟩ := inhab P;
  exists A, by trivial, ∅, rfl; simp only [Mset.mul_empty_l]

lemma nb_unsep_r [Inhab P] : nb =ᴿ nb ∗ P := by
  rw [sep_comm]; apply nb_unsep_l

/-! ### Rules for `Precise` -/

lemma precise_anti [Precise Q] : (P ⊢ Q) → Precise P := by
  intro _; constructor; intro _ _ _ _; apply precise Q <;> tauto

instance false_instPrecise : Precise (ρ := ρ) iprop(False) := by
  constructor; nofun

instance own_instPrecise : Precise (own r) := by
  constructor; intro _; simp only [own_unfold]; grind only

instance emp_instPrecise : Precise (ρ := ρ) emp := own_instPrecise _

instance sep_instPrecise [Precise P] [Precise Q] : Precise iprop(P ∗ Q) := by
  constructor; rintro _ ⟨_, elP, _, elQ, rfl⟩ _ ⟨_, elP', _, elQ', rfl⟩;
  rw [precise P _ elP _ elP', precise Q _ elQ _ elQ']

lemma bigoplus_precise (P : ι → RProp ρ) :
    (∀ i, Precise (P i)) → Precise iprop(⨁ i, P i) := by
  intro _; constructor; rintro _ ⟨F, el, rfl⟩ _ ⟨G, el', rfl⟩; congr; ext1 i;
  apply precise (P i) <;> tauto

instance bigoplus_instPrecise (P : ι → RProp ρ) [∀ i, Precise (P i)] :
    Precise iprop(⨁ i, P i) :=
  bigoplus_precise P inferInstance

instance oplus_instPrecise [Precise P] [Precise Q] : Precise iprop(P ⊕ Q) := by
  constructor; rw [oplus_bigoplus]; apply (bigoplus_precise _ _).precise; rintro (_ | _) <;> tauto

instance nb_instPrecise : Precise (nb (ρ := ρ)) := by
  constructor; rw [nb_bigoplus]; apply (bigoplus_precise _ _).precise; nofun

/-! ### Rules for `Inhab` -/

lemma Inhab_not_false : Inhab P = (P ≠ iprop(False)) := by
  ext1; constructor; { intro ⟨_, _⟩ rfl; trivial };
  intro ne; suffices P.car.Nonempty by tauto;
  apply Set.nonempty_iff_ne_empty.mpr; cases P; intro rfl; tauto

lemma Inhab_mono [Inhab P] : (P ⊢ Q) → Inhab Q := by
  intro _; have _ := inhab P; tauto

lemma pure_Inhab : φ → Inhab (ρ := ρ) iprop(⌜φ⌝) := by
  intro φ; exists 1

instance true_instInhab : Inhab (ρ := ρ) iprop(True) := pure_Inhab trivial

lemma own_Inhab : Inhab (own r) := by
  exists pure r

instance emp_instInhab : Inhab (ρ := ρ) emp := own_Inhab _

lemma exists_Inhab a (P : α → RProp ρ) :
    Inhab (P a) → Inhab iprop(∃ x, P x) := by
  intro ⟨A, _⟩; constructor; exists A; rw [exists_simple]; exists a

instance (priority := mid) exists_instInhab (P : α → RProp ρ)
    [Inhabited α] [Inhab (P default)] : Inhab iprop(∃ x, P x) := by
  apply exists_Inhab; trivial

instance (priority := mid) or_instInhab_l [Inhab P] : Inhab iprop(P ∨ Q) := by
  rw [or_exists]; apply exists_Inhab true; trivial

instance (priority := mid) or_instInhab_r [Inhab Q] : Inhab iprop(P ∨ Q) := by
  rw [or_exists]; apply exists_Inhab false; trivial

instance sep_instInhab [Inhab P] [Inhab Q] : Inhab iprop(P ∗ Q) := by
  have ⟨A, _⟩ := inhab P; have ⟨B, _⟩ := inhab Q;
  exists A * B; exists A, by trivial, B

instance bigoplus_instInhab (P : ι → RProp ρ) [∀ i, Inhab (P i)] :
    Inhab iprop(⨁ i, P i) := by
  have ⟨A, _⟩ := Classical.skolem.mp (fun i => inhab (P i)); exists ⨁ᴹ i, A i, A

lemma bigoplus_Inhab (P : ι → RProp ρ) :
    (∀ i, Inhab (P i)) → Inhab iprop(⨁ i, P i) := by apply bigoplus_instInhab

instance oplus_instInhab [Inhab P] [Inhab Q] : Inhab iprop(P ⊕ Q) := by
  rw [oplus_bigoplus]; apply bigoplus_Inhab; rintro (_ | _) <;> trivial

instance nb_instInhab : Inhab (nb (ρ := ρ)) := by
  rw [nb_bigoplus]; apply bigoplus_Inhab; nofun

/-! ### Rules for `Nonnb` -/

lemma Nonnb_anti [Nonnb Q] : (P ⊢ Q) → Nonnb P := by
  intro _; constructor; intro _ _; apply nonnb Q; tauto

instance not_nb_instNonnb : Nonnb (ρ := ρ) iprop(¬ nb) := by
  constructor; intro _ _; rw [←Mset.not_empty_inhab]; tauto

lemma to_not_nb_Nonnb : (P ⊢ ¬ nb) → Nonnb P := by
  apply Nonnb_anti

lemma Nonnb_not_nb : Nonnb P = (P ⊢ ¬ nb) := by
  ext1; constructor; swap; { apply to_not_nb_Nonnb };
  intro _ _ elP; have inh := nonnb P _ elP; rw [←Mset.not_empty_inhab] at inh; tauto

instance false_instNonnb : Nonnb (ρ := ρ) iprop(False) := by
  constructor; nofun

instance own_instNonnb : Nonnb (own r) := by
  constructor; rintro _ rfl; simp only [Mset.inhab_pure]

instance emp_instNonnb : Nonnb (ρ := ρ) emp := own_instNonnb _

instance sep_instNonnb [Nonnb P] [Nonnb Q] : Nonnb iprop(P ∗ Q) := by
  constructor; rintro _ ⟨A, _, B, _, rfl⟩;
  simp only [Mset.mul_unfold, functor_norm, Mset.inhab_seq, Mset.inhab_map];
  and_intros; { apply nonnb P; trivial }; { apply nonnb Q; trivial }

lemma bigoplus_Nonnb (P : ι → RProp ρ) i0 :
    Nonnb (P i0) → Nonnb iprop(⨁ i, P i) := by
  intro _; constructor; rintro _ ⟨F, el, rfl⟩; simp only [Mset.inhab_bigoplus];
  exists i0; apply nonnb (P i0); tauto

instance (priority := mid) bigoplus_instNonnb (P : ι → RProp ρ)
    [Inhabited ι] [Nonnb (P default)] : Nonnb iprop(⨁ i, P i) := by
  apply bigoplus_Nonnb; trivial

instance (priority := mid) oplus_instNonnb_l [Nonnb P] : Nonnb iprop(P ⊕ Q) := by
  rw [oplus_bigoplus]; apply bigoplus_Nonnb _ true; trivial

instance (priority := mid) oplus_instNonnb_r [Nonnb Q] : Nonnb iprop(P ⊕ Q) := by
  rw [oplus_bigoplus]; apply bigoplus_Nonnb _ false; trivial

end RBI
