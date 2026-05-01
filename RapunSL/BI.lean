module

import Mathlib.Logic.Equiv.Bool
public import RapunSL.PCM

@[expose] public section

open PCM Mset

/-! # RapunSL's BI -/

/-! ## Propositions -/

/-- RapunSL proposition based on a multiset PCM -/
def RProp ρ [PCMa ρ] := Set (Mset ρ)

namespace RProp
variable {ρ : Type u} [PCMa ρ]

protected instance instMembership :
    Membership (Mset ρ) (RProp ρ) := Set.instMembership

lemma set_ext (P Q : RProp ρ) : (∀ A, A ∈ P ↔ A ∈ Q) → P = Q := by
  intro _; apply Set.ext; trivial

/-- Entailment between `RProp`s -/
def entails (P Q : RProp ρ) : Prop := ∀ A ∈ P, A ∈ Q

scoped infix:25 " ⊢ " => RProp.entails

@[refl] lemma entails_refl (P : RProp ρ) : P ⊢ P := by
  intro _ _; assumption

@[trans] lemma entails_trans (P Q R : RProp ρ) :
    P ⊢ Q → Q ⊢ R → P ⊢ R :=
  by intro PQ QR _ _; apply QR; apply PQ; assumption

@[ext] lemma entails_antisymm (P Q : RProp ρ) :
    P ⊢ Q → Q ⊢ P → P = Q := by
  intro PQ QP; apply set_ext; intro _; constructor <;> { intro _; tauto }

protected instance instIsPartialOrder : IsPartialOrder (RProp ρ) entails where
  refl := RProp.entails_refl
  trans := RProp.entails_trans
  antisymm := RProp.entails_antisymm

/-! ## BI connectives -/

/-! ### Standard logical connectives -/

/-- Embedded pure proposition -/
def pur (φ : Prop) : RProp ρ := fun _ => φ

scoped notation "⌜" φ "⌝" => RProp.pur φ

/-- Truth -/
def RTrue : RProp ρ := fun _ => True

/-- Falsehood -/
def RFalse : RProp ρ := fun _ => False

/-- Conjunction -/
def rand (P Q : RProp ρ) : RProp ρ := fun A => A ∈ P ∧ A ∈ Q

scoped infixr:35 " ∧ᴿ " => RProp.rand

/-- Disjunction -/
def ror (P Q : RProp ρ) : RProp ρ := fun A => A ∈ P ∨ A ∈ Q

scoped infixr:30 " ∨ᴿ " => RProp.ror

/-- Implication -/
def rimp (P Q : RProp ρ) : RProp ρ := fun A => A ∈ P → A ∈ Q

scoped infixr:27 " →ᴿ " => RProp.rimp

/-- Negation -/
def rnot (P : RProp ρ) : RProp ρ := fun A => A ∉ P

scoped notation:max "¬ᴿ " P:40 => RProp.rnot P

/-- Universal quantification -/
def rforall {α : Sort u'} (P : α → RProp ρ) : RProp ρ :=
  fun A => ∀ x, A ∈ P x

scoped notation "∀ᴿ " x ", " P => RProp.rforall (fun x => P)

/-- Existential quantification -/
def rexists {α : Sort u'} (P : α → RProp ρ) : RProp ρ :=
  fun A => ∃ x, A ∈ P x

scoped notation "∃ᴿ " x ", " P => RProp.rexists (fun x => P)

/-! ### BI-specific connectives -/

/-- Empty ownership -/
def emp : RProp ρ := fun A => A = pure 1

lemma emp_unfold A : (A ∈ emp (ρ := ρ)) = (A = 1) := rfl

/-- Separating conjunction -/
def sep (P Q : RProp ρ) : RProp ρ :=
  fun A => ∃ B ∈ P, ∃ C ∈ Q, A = B * (C : Mset ρ)

scoped infixr:35 " ∗ " => RProp.sep

/-- Magic wand -/
def wand (P Q : RProp ρ) : RProp ρ :=
  fun A => ∀ B ∈ P, B * A ∈ Q

scoped infixr:27 " -∗ " => RProp.wand

/-! ### Ownership -/

/-- Ownership of an element -/
def own (r : ρ) : RProp ρ := fun A => A = pure r

lemma own_unfold r A : (A ∈ own (ρ := ρ) r) = (A = pure r) := rfl

/-! ### Multiset connectives -/

/-- No behavior -/
def nb : RProp ρ := fun A => A = ∅

lemma nb_unfold A : (A ∈ nb (ρ := ρ)) = (A = ∅) := rfl

/-- Multiset sum -/
def oplus (P Q : RProp ρ) : RProp ρ :=
  fun A => ∃ B ∈ P, ∃ C ∈ Q, A = B ⊕ᴹ (C : Mset ρ)

scoped infixr:30 " ⊕ᴿ " => RProp.oplus

/-- Big multiset sum -/
def bigoplus (P : ι → RProp ρ) : RProp ρ :=
  fun A => ∃ B : ι → Mset ρ, (∀ i, B i ∈ P i) ∧ A = ⨁ᴹ i, B i

scoped notation "⨁ᴿ " i ", " P => RProp.bigoplus (fun i => P)

/-- Pine, the right adjoint of `⊕ᴿ` -/
def pine (P Q : RProp ρ) : RProp ρ :=
  fun A => ∀ B ∈ P, B ⊕ᴹ A ∈ Q

scoped infixr:27 " -⊕ " => RProp.pine

/-! ## Judgments -/

/-- Preciseness -/
class Precise (P : RProp ρ) : Prop where
  precise : ∀ A ∈ P, ∀ B ∈ P, A = B

lemma precise (P : RProp ρ) [Precise P] : ∀ A ∈ P, ∀ B ∈ P, A = B := by
  apply Precise.precise

/-- Multiset inhabitance -/
class Nonnb (P : RProp ρ) : Prop where
  nonnb : ∀ A ∈ P, A.inhab

lemma nonnb (P : RProp ρ) [Nonnb P] : ∀ A ∈ P, A.inhab := by
  apply Nonnb.nonnb

/-- Inhabitance, or being not `False` -/
class Inhab (P : RProp ρ) : Prop where
  inhab : ∃ A, A ∈ P

lemma inhab (P : RProp ρ) [Inhab P] : ∃ A, A ∈ P := by
  apply Inhab.inhab

variable (P P' Q Q' R : RProp ρ) (r : ρ)

/-! ## Entailment rules for standard logical connectives -/

lemma pur_intro : φ → P ⊢ ⌜φ⌝ := by tauto

lemma pur_elim' : (φ → RTrue ⊢ P) → ⌜φ⌝ ⊢ P := by tauto

lemma pur_intro_l : φ → P ⊢ ⌜φ⌝ ∧ᴿ P := by tauto

lemma pur_elim_l : (φ → P ⊢ Q) → ⌜φ⌝ ∧ᴿ P ⊢ Q := by intro _ _ ⟨_, _⟩; tauto

lemma pur_adj : (φ → P ⊢ Q) = (⌜φ⌝ ∧ᴿ P ⊢ Q) := by
  ext1; constructor; { apply pur_elim_l }; { tauto }

lemma rtrue_intro : P ⊢ RTrue := by tauto

lemma rtrue_pur : RTrue (ρ := ρ) = ⌜True⌝ := rfl

lemma rfalse_elim : RFalse ⊢ P := nofun

lemma rfalse_pur : RFalse (ρ := ρ) = ⌜False⌝ := rfl

lemma rand_elim_l : P ∧ᴿ Q ⊢ P := by intro _ ⟨_, _⟩; tauto

lemma rand_elim_r : P ∧ᴿ Q ⊢ Q := by intro _ ⟨_, _⟩; tauto

lemma rand_intro : R ⊢ P → R ⊢ Q → R ⊢ P ∧ᴿ Q := by tauto

@[gcongr] lemma rand_mono : P ⊢ P' → Q ⊢ Q' → P ∧ᴿ Q ⊢ P' ∧ᴿ Q' := by
  intro PP' QQ'; apply rand_intro;
  { grw [←PP']; apply rand_elim_l }; { grw [←QQ']; apply rand_elim_r }

lemma ror_intro_l : P ⊢ P ∨ᴿ Q := by tauto

lemma ror_intro_r : Q ⊢ P ∨ᴿ Q := by tauto

lemma ror_elim : P ⊢ R → Q ⊢ R → P ∨ᴿ Q ⊢ R := by rintro _ _ _ (_ | _) <;> tauto

@[gcongr] lemma ror_mono : P ⊢ P' → Q ⊢ Q' → P ∨ᴿ Q ⊢ P' ∨ᴿ Q' := by
  intro PP' QQ'; apply ror_elim;
  { grw [PP']; apply ror_intro_l }; { grw [QQ']; apply ror_intro_r }

lemma rimp_intro : P ∧ᴿ Q ⊢ R → P ⊢ Q →ᴿ R := by tauto

lemma rimp_elim : P ⊢ Q →ᴿ R → P ∧ᴿ Q ⊢ R := by intro _ _ ⟨_, _⟩; tauto

lemma rimp_adj : (P ⊢ Q →ᴿ R) = (P ∧ᴿ Q ⊢ R) := by
  ext1; constructor; { apply rimp_elim }; { apply rimp_intro }

lemma rnot_contra : P ∧ᴿ ¬ᴿ P ⊢ Q := nofun

lemma rnot_em : Q ⊢ P ∨ᴿ ¬ᴿ P := by tauto

lemma rnot_rimp : (¬ᴿ P) = (P →ᴿ RFalse) := rfl

lemma rforall_elim a (P : α → RProp ρ) : (∀ᴿ x, P x) ⊢ P a := by tauto

lemma rforall_intro (P : α → RProp ρ) Q : (∀ x, Q ⊢ P x) → Q ⊢ ∀ᴿ x, P x := by tauto

lemma rand_rforall : (P ∧ᴿ Q) = ∀ᴿ (B : Bool), if B then P else Q := by
  ext1;
  · apply rforall_intro; rintro (_ | _); { apply rand_elim_r }; { apply rand_elim_l }
  · apply rand_intro; { apply rforall_elim true }; { apply rforall_elim false }

lemma rexists_intro a (P : α → RProp ρ) : P a ⊢ ∃ᴿ x, P x := by tauto

lemma rexists_elim (P : α → RProp ρ) Q : (∀ x, P x ⊢ Q) → (∃ᴿ x, P x) ⊢ Q := by
  intro _ _ ⟨_, _⟩; tauto

lemma ror_rexists : (P ∨ᴿ Q) = ∃ᴿ (B : Bool), if B then P else Q := by
  ext1;
  · apply ror_elim; { grw [←rexists_intro true]; rfl }; { grw [←rexists_intro false]; rfl }
  · apply rexists_elim; rintro (_ | _); { apply ror_intro_r }; { apply ror_intro_l }

lemma rfalse_rexists : RFalse (ρ := ρ) = rexists (α := Empty) nofun := by
  ext1 <;> nofun

lemma rforall_rexists {β : α → Sort*} (P : ∀ a, β a → RProp ρ) :
    (∀ᴿ x, ∃ᴿ y, P x y) = ∃ᴿ (f : ∀ a, β a), ∀ᴿ x, P x (f x) := by
  ext1; { intro _; exact Classical.skolem.mp };
  intro _ _; apply Classical.skolem.mpr; tauto

/-! ### Entailment rules for `∗` and `-∗` -/

@[gcongr] lemma sep_mono : P ⊢ P' → Q ⊢ Q' → P ∗ Q ⊢ P' ∗ Q' := by
  intro PQ P'Q' _ ⟨A, _, B, _, _⟩; exists A, by tauto, B; tauto

private lemma sep_comm' : P ∗ Q ⊢ Q ∗ P := by
  intro _ ⟨A, _, B, _, _⟩; exists B, by trivial, A; rw [mul_comm]; trivial

lemma sep_comm : (P ∗ Q) = (Q ∗ P) := by ext1 <;> apply sep_comm'

lemma sep_emp : (P ∗ emp) = P := by
  ext1;
  · rintro _ ⟨_, _, _, eq1, rfl⟩; rw [emp_unfold] at eq1; rw [eq1, mul_one]; tauto
  · intro A _; exists A; and_intros; { trivial }; exists 1; simp only [mul_one]; trivial

lemma emp_sep : (emp ∗ P) = P := by rw [sep_comm, sep_emp]

lemma sep_assoc_l : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by
  rintro _ ⟨_, ⟨A, _, B, _, rfl⟩, C, _, rfl⟩;
  exists A, by trivial, B * C; simp only [mul_assoc, and_true];
  exists B, by trivial, C, by trivial

lemma sep_assoc_r : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by
  grind only [sep_comm, sep_assoc_l]

lemma sep_assoc : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  ext1; { apply sep_assoc_l }; { apply sep_assoc_r }

lemma wand_intro_l : P ∗ Q ⊢ R → Q ⊢ P -∗ R := by
  intro toR A _ B _; apply toR; exists B, by trivial, A, by trivial

lemma wand_intro_r : P ∗ Q ⊢ R → P ⊢ Q -∗ R := by
  rw [sep_comm]; apply wand_intro_l

lemma wand_elim_l : P ∗ (P -∗ Q) ⊢ Q := by
  rintro _ ⟨_, _, _, _, rfl⟩; tauto

lemma wand_elim_r : (P -∗ Q) ∗ P ⊢ Q := by
  rw [sep_comm]; apply wand_elim_l

lemma wand_adj : (P ∗ Q ⊢ R) = (Q ⊢ P -∗ R) := by
  ext1; constructor; { apply wand_intro_l };
  intro Qto; grw [Qto]; apply wand_elim_l

@[gcongr] lemma wand_mono : P' ⊢ P → Q ⊢ Q' → P -∗ Q ⊢ P' -∗ Q' := by
  intro P'P QQ'; grw [←wand_adj, P'P, ←QQ', wand_adj];

lemma sep_rexists_l (Q : α → RProp ρ) : (P ∗ (∃ᴿ x, Q x)) = ∃ᴿ x, P ∗ Q x := by
  ext1; swap; { apply rexists_elim; intro a; grw [rexists_intro a Q] };
  rw [wand_adj]; apply rexists_elim; intro a; rw [←wand_adj]; apply rexists_intro a

lemma sep_rexists_r (P : α → RProp ρ) Q : ((∃ᴿ x, P x) ∗ Q) = ∃ᴿ x, P x ∗ Q := by
  rw [sep_comm, sep_rexists_l]; congr; ext1 _; rw [sep_comm]

lemma sep_ror_l : (P ∗ (Q ∨ᴿ R)) = ((P ∗ Q) ∨ᴿ (P ∗ R)) := by
  simp only [ror_rexists, sep_rexists_l]; congr; ext1 b; cases b <;> rfl

lemma sep_ror_r : ((P ∨ᴿ Q) ∗ R) = ((P ∗ R) ∨ᴿ (Q ∗ R)) := by
  rw [sep_comm, sep_ror_l, sep_comm, sep_comm R]

lemma sep_rfalse_l : (P ∗ RFalse) = RFalse := by
  simp only [rfalse_rexists, sep_rexists_l]; congr; ext1 _; trivial

lemma sep_rfalse_r : (RFalse ∗ P) = RFalse := by
  rw [sep_comm, sep_rfalse_l]

/-! ### Entailment rules for `own` -/

lemma emp_own : emp (ρ := ρ) = own 1 := rfl

lemma own_sep : (own r ∗ own s) = own (r * s) := by
  apply set_ext; intro _; constructor;
  · rintro ⟨_, rfl, _, rfl, rfl⟩; rw [own_unfold, ←Mset.pure_mul]
  · intro rfl; exists pure r, rfl, pure s; and_intros; { rfl }; { rw [←Mset.pure_mul] }

/-! ### Entailment rules for `nb`, `⊕ᴿ`, `⨁ᴿ` and `-⊕` -/

lemma nb_bigoplus : nb = bigoplus (ρ := ρ) (ι := Empty) nofun := by
  apply set_ext; intro _; rw [nb_unfold]; constructor;
  · intro rfl; exists nofun; simp only [IsEmpty.forall_iff, true_and];
    rw [Mset.empty_bigoplus]; rfl
  · rintro ⟨_, _, rfl⟩; rw [Mset.empty_bigoplus]; congr; ext1; trivial

lemma oplus_bigoplus : (P ⊕ᴿ Q) = ⨁ᴿ (b : Bool), if b then P else Q := by
  apply set_ext; intro _; constructor;
  · rintro ⟨A, _, B, _, rfl⟩; exists fun b => if b then A else B;
    simp only; constructor; { grind only }; rw [Mset.oplus_bigoplus]
  · rintro ⟨A, el, rfl⟩; exists A true, el true, A false, el false;
    rw [Mset.oplus_bigoplus]; grind only

lemma unary_bigoplus : (⨁ᴿ (_ : Unit), P) = P := by
  apply set_ext; intro A; constructor;
  · rintro ⟨_, _, rfl⟩; rw [Mset.unary_bigoplus]; tauto
  · intro _; exists fun _ => A; simp only [Mset.unary_bigoplus]; tauto

@[gcongr] lemma bigoplus_mono (P Q : ι → RProp ρ) :
    (∀ i, P i ⊢ Q i) → (⨁ᴿ i, P i) ⊢ ⨁ᴿ i, Q i := by
  intro _ _ ⟨A, _, _⟩; exists A; tauto

@[gcongr] lemma oplus_mono : P ⊢ P' → Q ⊢ Q' → P ⊕ᴿ Q ⊢ P' ⊕ᴿ Q' := by
  intro _ _; grw [oplus_bigoplus, oplus_bigoplus]; gcongr; grind only

private lemma bigoplus_comm_fwd (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ᴿ i, P i) ⊢ ⨁ᴿ j, P (f j) := by
  intro _ ⟨A, _, eq⟩; exists A ∘ f; rw [eq, Mset.bigoplus_comm f]; tauto

private lemma bigoplus_comm_bwd (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ᴿ j, P (f j)) ⊢ ⨁ᴿ i, P i := by
  grw [bigoplus_comm_fwd f.symm]; gcongr; rw [Equiv.apply_symm_apply]

lemma bigoplus_comm (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ᴿ i, P i) = (⨁ᴿ j, P (f j)) := by
  ext1; { apply bigoplus_comm_fwd }; { apply bigoplus_comm_bwd }

lemma bigoplus_comm' (P : ι → RProp ρ) (Q : ι' → RProp ρ) (f : ι → ι') (g : ι' → ι) :
    (∀ i, P i = Q (f i)) → g.LeftInverse f → g.RightInverse f →
    (⨁ᴿ i, P i) = (⨁ᴿ j, Q j) := by
  intro _ li ri; rw [bigoplus_comm ⟨f, g, li, ri⟩]; congr; ext1 _; tauto

lemma oplus_comm : (P ⊕ᴿ Q) = (Q ⊕ᴿ P) := by
  simp only [oplus_bigoplus]; rw [bigoplus_comm Equiv.boolNot]; congr;
  simp only [Equiv.boolNot_apply]; grind only

lemma bigoplus_assoc {ι' : ι → Type} (P : ∀ i, ι' i → RProp ρ) :
    (⨁ᴿ i, ⨁ᴿ j, P i j) = (⨁ᴿ (⟨i, j⟩ : Sigma ι'), P i j) := by
  ext1;
  · intro _ ⟨_, el, eq⟩; simp only at *; subst eq; have ⟨A, el⟩ := Classical.skolem.mp el;
    exists fun ⟨i, j⟩ => A i j; simp only at *; and_intros; { grind only };
    trans; swap; { apply Mset.bigoplus_assoc (fun i j => (A i j)) }; grind only
  · rintro _ ⟨A, el, rfl⟩; exists fun i => ⨁ᴹ j, A ⟨i, j⟩; simp only at *;
    and_intros; swap;
    { symm; apply Mset.bigoplus_assoc }; intro i; exists fun j => A ⟨i, j⟩;
    simp only [and_true]; intro _; apply el ⟨_, _⟩

lemma oplus_assoc : ((P ⊕ᴿ Q) ⊕ᴿ R) = (P ⊕ᴿ (Q ⊕ᴿ R)) := by
  have eq : ∀ P Q R : RProp ρ,
      ((P ⊕ᴿ Q) ⊕ᴿ R) = ⨁ᴿ (b : Bool),
        ⨁ᴿ (i : match b with | true => Bool | false => Unit),
          match b with | true => if i then P else Q | false => R := by
    intro _ _ _; simp only [oplus_bigoplus]; congr; ext1 b; cases b <;> simp only;
    { rw [unary_bigoplus]; rfl }; { rfl }
  rw [eq, oplus_comm, eq]; simp only [bigoplus_assoc];
  apply bigoplus_comm' _ _
    (fun | ⟨true, b⟩ => if b then ⟨false, ()⟩ else ⟨true, true⟩ | ⟨false, _⟩ => ⟨true, false⟩)
    (fun | ⟨true, b⟩ => if b then ⟨true, false⟩ else ⟨false, ()⟩ | ⟨false, _⟩ => ⟨true, true⟩) <;>
    { rintro ⟨(_ | _), i⟩; { rfl }; cases i <;> rfl }

lemma oplus_nb : (P ⊕ᴿ nb) = P := by
  have eq : (P ⊕ᴿ nb) = ⨁ᴿ (b : Bool),
      ⨁ᴿ (i : match b with | true => Unit | false => Empty), match b with | true => P := by
    rw [oplus_bigoplus, nb_bigoplus]; congr; ext1 b; cases b <;> simp only;
    { simp only [Bool.false_eq_true, reduceIte]; congr; ext1 _; trivial };
    { simp only [reduceIte]; rw [unary_bigoplus] }
  rw [eq, bigoplus_assoc]; trans; swap; { apply unary_bigoplus };
  apply bigoplus_comm' _ _ (fun | ⟨true, _⟩ => ()) (fun _ => ⟨true, ()⟩) <;>
    { rintro ⟨(_ | _), _⟩ <;> trivial }

lemma nb_oplus : (nb ⊕ᴿ P) = P := by rw [oplus_comm, oplus_nb]

lemma pine_intro_l : P ⊕ᴿ Q ⊢ R → Q ⊢ P -⊕ R := by
  intro toR A _ B _; apply toR; exists B, by trivial, A, by trivial

lemma pine_intro_r : P ⊕ᴿ Q ⊢ R → P ⊢ Q -⊕ R := by
  rw [oplus_comm]; apply pine_intro_l

lemma pine_elim_l : P ⊕ᴿ (P -⊕ Q) ⊢ Q := by
  rintro _ ⟨_, _, _, _, rfl⟩; tauto

lemma pine_elim_r : (P -⊕ Q) ⊕ᴿ P ⊢ Q := by
  rw [oplus_comm]; apply pine_elim_l

lemma pine_adj : (P ⊕ᴿ Q ⊢ R) = (Q ⊢ P -⊕ R) := by
  ext1; constructor; { apply pine_intro_l };
  intro Qto; grw [Qto]; apply pine_elim_l

lemma oplus_rexists_l (Q : α → RProp ρ) : (P ⊕ᴿ (∃ᴿ a, Q a)) = (∃ᴿ a, P ⊕ᴿ Q a) := by
  ext1; swap; { apply rexists_elim; intro a; grw [rexists_intro a Q] };
  rw [pine_adj]; apply rexists_elim; intro a; rw [←pine_adj]; apply rexists_intro a

lemma oplus_rexists_r (P : α → RProp ρ) Q : ((∃ᴿ a, P a) ⊕ᴿ Q) = (∃ᴿ a, P a ⊕ᴿ Q) := by
  rw [oplus_comm, oplus_rexists_l]; congr; ext1 _; rw [oplus_comm]

lemma oplus_ror_l : (P ⊕ᴿ (Q ∨ᴿ R)) = ((P ⊕ᴿ Q) ∨ᴿ (P ⊕ᴿ R)) := by
  simp only [ror_rexists, oplus_rexists_l]; congr; ext1 b; cases b <;> rfl

lemma oplus_ror_r : ((P ∨ᴿ Q) ⊕ᴿ R) = ((P ⊕ᴿ R) ∨ᴿ (Q ⊕ᴿ R)) := by
  rw [oplus_comm, oplus_ror_l, oplus_comm, oplus_comm R]

lemma oplus_rfalse_l : (P ⊕ᴿ RFalse) = RFalse := by
  simp only [rfalse_rexists, oplus_rexists_l]; congr; ext1 _; trivial

lemma oplus_rfalse_r : (RFalse ⊕ᴿ P) = RFalse := by
  rw [oplus_comm, oplus_rfalse_l]

/-! ### Rules for interaction with `∗` -/

lemma bigoplus_frame_l (Q : ι → RProp ρ) : P ∗ (⨁ᴿ i, Q i) ⊢ ⨁ᴿ i, P ∗ Q i := by
  rintro _ ⟨A, _, _, ⟨B, _, rfl⟩, rfl⟩; exists fun i => A * B i; simp only; and_intros;
  { intros i; exists A, by trivial, B i, by tauto }; { rw [Mset.mul_bigoplus_l] }

lemma bigoplus_frame_r (P : ι → RProp ρ) Q : (⨁ᴿ i, P i) ∗ Q ⊢ ⨁ᴿ i, P i ∗ Q := by
  grw [sep_comm, bigoplus_frame_l]; gcongr 1; rw [sep_comm]

lemma oplus_frame_l : P ∗ (Q ⊕ᴿ R) ⊢ (P ∗ Q) ⊕ᴿ (P ∗ R) := by
  grw [oplus_bigoplus, oplus_bigoplus, bigoplus_frame_l]; gcongr with b; cases b <;> rfl

lemma oplus_frame_r : (P ⊕ᴿ Q) ∗ R ⊢ (P ∗ R) ⊕ᴿ (Q ∗ R) := by
  grw [sep_comm, oplus_frame_l, sep_comm, sep_comm R]

lemma nb_sep_l : P ∗ nb ⊢ nb := by
  simp only [nb_bigoplus]; grw [bigoplus_frame_l]; gcongr; tauto

lemma nb_sep_r : nb ∗ P ⊢ nb := by grw [sep_comm, nb_sep_l]

lemma bigoplus_unframe_l P (Q : ι → RProp ρ) [Nonempty ι] [Precise P] :
    (⨁ᴿ i, P ∗ Q i) = (P ∗ ⨁ᴿ i, Q i) := by
  ext1; swap; { apply bigoplus_frame_l };
  rintro _ ⟨_, el, rfl⟩;
  have ⟨A, el⟩ := Classical.skolem.mp el; have AQ i := (el i).left;
  have ⟨B, el⟩ := Classical.skolem.mp (fun i => (el i).right);
  have i0 : ι := Classical.choice inferInstance;
  exists A i0, by tauto, ⨁ᴹ i, B i; and_intros; { exists B, fun i => (el i).left };
  rw [Mset.mul_bigoplus_l]; congr; ext1 i; rw [P.precise _ (AQ i0) _ (AQ i)]; grind only

lemma bigoplus_unframe_r (P : ι → RProp ρ) Q [Nonempty ι] [Precise Q] :
    (⨁ᴿ i, P i ∗ Q) = ((⨁ᴿ i, P i) ∗ Q) := by
  ext1; swap; { apply bigoplus_frame_r };
  grw [sep_comm, ←bigoplus_unframe_l _ _]; gcongr 1; rw [sep_comm]

lemma oplus_unframe_l [Precise P] :
    ((P ∗ Q) ⊕ᴿ (P ∗ R)) = (P ∗ (Q ⊕ᴿ R)) := by
  ext1; swap; { apply oplus_frame_l };
  simp only [oplus_bigoplus]; grw [←bigoplus_unframe_l]; gcongr with b; cases b <;> rfl

lemma oplus_unframe_r [Precise R] :
    ((P ∗ R) ⊕ᴿ (Q ∗ R)) = ((P ⊕ᴿ Q) ∗ R) := by
  ext1; swap; { apply oplus_frame_r };
  grw [sep_comm (P ⊕ᴿ Q), ←oplus_unframe_l, sep_comm, sep_comm Q]

lemma nb_unsep_l [Inhab P] : nb = (P ∗ nb) := by
  ext1; swap; { apply nb_sep_l };
  intro _ rfl; have ⟨A, _⟩ := inhab P;
  exists A, by trivial, ∅, rfl; simp only [Mset.mul_empty_l]

lemma nb_unsep_r [Inhab P] : nb = (nb ∗ P) := by
  rw [sep_comm]; apply nb_unsep_l

/-! ## Entailment rules for `Precise` -/

lemma precise_anti [Precise Q] : P ⊢ Q → Precise P := by
  intro _; constructor; intro _ _ _ _; apply Q.precise <;> tauto

instance rfalse_instPrecise : Precise (RFalse (ρ := ρ)) where
  precise := nofun

instance own_instPrecise : Precise (own r) where
  precise := by intro _; simp only [own_unfold]; grind only

instance emp_instPrecise : Precise (emp (ρ := ρ)) := own_instPrecise _

instance sep_instPrecise [Precise P] [Precise Q] : Precise (P ∗ Q) where
  precise := by
    rintro _ ⟨_, elP, _, elQ, rfl⟩ _ ⟨_, elP', _, elQ', rfl⟩;
    rw [P.precise _ elP _ elP', Q.precise _ elQ _ elQ']

lemma bigsum_precise (P : ι → RProp ρ) :
    (∀ i, Precise (P i)) → Precise (⨁ᴿ i, P i) := by
  intro _; constructor; rintro _ ⟨F, el, rfl⟩ _ ⟨G, el', rfl⟩; congr; ext1 i;
  apply (P i).precise <;> tauto

instance bigsum_instPrecise (P : ι → RProp ρ) [∀ i, Precise (P i)] : Precise (⨁ᴿ i, P i) :=
  bigsum_precise P inferInstance

instance oplus_instPrecise [Precise P] [Precise Q] : Precise (P ⊕ᴿ Q) where
  precise := by
    rw [oplus_bigoplus]; apply (bigsum_precise _ _).precise; rintro (_ | _) <;> tauto

instance nb_instPrecise : Precise (nb (ρ := ρ)) where
  precise := by rw [nb_bigoplus]; apply (bigsum_precise _ _).precise; nofun

/-! ## Rules for `Nonnb` -/

lemma nonnb_anti [Nonnb Q] : P ⊢ Q → Nonnb P := by
  intro _; constructor; intro _ _; apply Q.nonnb; tauto

instance not_nb_instNonnb : Nonnb (¬ᴿ nb (ρ := ρ)) := by
  constructor; intro _ _; rw [←Mset.not_empty_inhab]; tauto

lemma to_not_nb_nonnb : P ⊢ ¬ᴿ nb → Nonnb P := by
  apply nonnb_anti;

lemma nonnb_not_nb : Nonnb P = (P ⊢ ¬ᴿ nb) := by
  ext1; constructor; swap; { apply to_not_nb_nonnb };
  intro _ _ elP; have inh := P.nonnb _ elP; rw [←Mset.not_empty_inhab] at inh; tauto

instance rfalse_instNonnb : Nonnb (RFalse (ρ := ρ)) := by
  constructor; nofun

instance own_instNonnb : Nonnb (own r) := by
  constructor; rintro _ rfl; simp only [Mset.inhab_pure]

instance emp_instNonnb : Nonnb (emp (ρ := ρ)) := own_instNonnb _

instance sep_instNonnb [Nonnb P] [Nonnb Q] : Nonnb (P ∗ Q) := by
  constructor; rintro _ ⟨A, _, B, _, rfl⟩;
  simp only [Mset.mul_unfold, functor_norm, Mset.inhab_seq, Mset.inhab_map];
  and_intros; { apply P.nonnb; trivial }; { apply Q.nonnb; trivial }

lemma bigoplus_nonnb (P : ι → RProp ρ) i0 :
    Nonnb (P i0) → Nonnb (⨁ᴿ i, P i) := by
  intro _; constructor; rintro _ ⟨F, el, rfl⟩; simp only [Mset.inhab_bigoplus];
  exists i0; apply (P i0).nonnb; tauto

instance (priority := mid) bigsum_instNonnb (P : ι → RProp ρ)
    [Inhabited ι] [Nonnb (P default)] : Nonnb (⨁ᴿ i, P i) :=
  by apply bigoplus_nonnb; trivial

instance (priority := mid) oplus_instNonnb_l [Nonnb P] : Nonnb (P ⊕ᴿ Q) := by
  rw [oplus_bigoplus]; apply bigoplus_nonnb _ true; trivial

instance (priority := mid) oplus_instNonnb_r [Nonnb Q] : Nonnb (P ⊕ᴿ Q) := by
  rw [oplus_bigoplus]; apply bigoplus_nonnb _ false; trivial

/-! ## Rules for `Inhab` -/

lemma inhab_not_rfalse : Inhab P = (P ≠ RFalse) := by
  ext1; constructor; { intro ⟨_, _⟩ rfl; trivial };
  intro ne; have _ := Set.nonempty_iff_ne_empty.mpr ne; tauto

lemma inhab_mono [Inhab P] : P ⊢ Q → Inhab Q := by
  intro _; have _ := P.inhab; tauto

lemma pur_inhab : φ → Inhab (ρ := ρ) ⌜φ⌝ := by
  intro φ; exists 1

instance rtrue_instInhab : Inhab (RTrue (ρ := ρ)) := pur_inhab trivial

lemma own_inhab : Inhab (own r) := by
  exists pure r

instance emp_instInhab : Inhab (emp (ρ := ρ)) := own_inhab _

lemma rexists_inhab a (P : α → RProp ρ) :
    Inhab (P a) → Inhab (∃ᴿ x, P x) := by
  intro ⟨_, _⟩; constructor; tauto

instance (priority := mid) rexists_instInhab (P : α → RProp ρ)
    [Inhabited α] [Inhab (P default)] : Inhab (∃ᴿ x, P x) :=
  by apply rexists_inhab; trivial

instance (priority := mid) ror_instInhab_l [Inhab P] : Inhab (P ∨ᴿ Q) := by
  rw [ror_rexists]; apply rexists_inhab true; trivial

instance (priority := mid) ror_instInhab_r [Inhab Q] : Inhab (P ∨ᴿ Q) := by
  rw [ror_rexists]; apply rexists_inhab false; trivial

instance bigoplus_instInhab (P : ι → RProp ρ) [∀ i, Inhab (P i)] :
    Inhab (⨁ᴿ i, P i) := by
  have ⟨A, _⟩ := Classical.skolem.mp (fun i => (P i).inhab); exists ⨁ᴹ i, A i, A

lemma bigoplus_inhab (P : ι → RProp ρ) :
    (∀ i, Inhab (P i)) → Inhab (⨁ᴿ i, P i) := by apply bigoplus_instInhab

instance oplus_instInhab [Inhab P] [Inhab Q] : Inhab (P ⊕ᴿ Q) := by
  rw [oplus_bigoplus]; apply bigoplus_inhab; rintro (_ | _) <;> trivial

end RProp
