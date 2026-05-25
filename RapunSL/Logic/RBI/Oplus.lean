module

public import RapunSL.Logic.RBI.Core
import Mathlib.Logic.Equiv.Bool
open Iris BI RBI Mseti ENNReal

@[expose] public section

/-! # Multiset connectives in RapunSL -/

namespace RBI

variable {ρ : Type u} [RM ρ] (P P' Q Q' R : RProp ρ)

/-! ## Multiset connectives -/

/-- Binary multiset sum -/
def oplus (P Q : RProp ρ) : RProp ρ :=
  .mk fun A => ∃ B C, B ∈ P ∧ C ∈ Q ∧ A.val = B.val ⊕ᴹⁱ C.val

@[inherit_doc oplus]
scoped syntax:30 term:31 " ⊕ " term:30 : term

/-- Big multiset sum -/
def bigoplus [Inhabited ι] (P : ι → RProp ρ) : RProp ρ :=
  .mk fun A => ∃ B : ι → Msetiv ρ, (∀ i, B i ∈ P i) ∧ A.val = ⨁ᴹⁱ i, (B i).val

@[inherit_doc bigoplus]
scoped syntax "⨁ " Lean.Parser.Term.funBinder ", " term : term

/-- Pine, the right adjoint of `⊕` -/
def pine (P Q : RProp ρ) : RProp ρ :=
  .mk fun A => ∀ B ∈ P, ∀ val, ⟨B.val ⊕ᴹⁱ A.val, val⟩ ∈ Q

@[inherit_doc pine]
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

/-! ## Rules for `⊕`, `⨁` and `-⊕` -/

lemma oplus_as_bigoplus : P ⊕ Q =ᴿ ⨁ (b : Bool), if b then P else Q := by
  apply set_ext; intro ⟨_, _⟩; constructor;
  · rintro ⟨A, B, _, _, rfl⟩; exists fun b => if b then A else B;
    simp only; constructor; { grind only }; rw [Mseti.oplus_as_bigoplus];
    congr; ext1 b; cases b <;> rfl
  · rintro ⟨A, el, rfl⟩; exists A true, A false, el true, el false;
    rw [Mseti.oplus_as_bigoplus]; grind only

lemma unary_bigoplus : (⨁ (_ : Unit), P) =ᴿ P := by
  apply set_ext; intro ⟨A, val⟩; constructor;
  · rintro ⟨A, el, rfl⟩;
    suffices eq : ⟨(⨁ᴹⁱ u, ↑(A u)), val⟩ = A () by { rw [eq]; apply el };
    ext : 2; simp only [Mseti.bigoplus_val, Mset.unary_bigoplus]
  · intro _; exists fun _ => ⟨A, val⟩; simp only; and_intros; { tauto };
    ext1; simp only [Mseti.bigoplus_val, Mset.unary_bigoplus]

@[gcongr] lemma bigoplus_mono [Inhabited ι] (P Q : ι → RProp ρ) :
    (∀ i, P i ⊢ Q i) → (⨁ i, P i) ⊢ ⨁ i, Q i := by
  intro _ _ ⟨A, _, _⟩; exists A; tauto

@[gcongr] lemma oplus_mono : (P ⊢ P') → (Q ⊢ Q') → P ⊕ Q ⊢ P' ⊕ Q' := by
  intro _ _; grw [oplus_as_bigoplus, oplus_as_bigoplus]; gcongr; grind only

private lemma bigoplus_comm_fwd [Inhabited ι] [Inhabited ι'] (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ i, P i) ⊢ ⨁ j, P (f j) := by
  intro _ ⟨A, _, eq⟩; exists A ∘ f; rw [eq]; and_intros; { tauto };
  ext1; simp only [Mseti.bigoplus_val]; rw [Mset.bigoplus_comm f]; rfl

private lemma bigoplus_comm_bwd [Inhabited ι] [Inhabited ι'] (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ j, P (f j)) ⊢ ⨁ i, P i := by
  grw [bigoplus_comm_fwd f.symm]; gcongr; rw [Equiv.apply_symm_apply]

lemma bigoplus_comm [Inhabited ι] [Inhabited ι'] (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ i, P i) =ᴿ ⨁ j, P (f j) := by
  ext1; constructor; { apply bigoplus_comm_fwd }; { apply bigoplus_comm_bwd }

lemma bigoplus_comm' [Inhabited ι] [Inhabited ι']
    (P : ι → RProp ρ) (Q : ι' → RProp ρ) (f : ι → ι') (g : ι' → ι) :
    (∀ i, P i = Q (f i)) → g.LeftInverse f → g.RightInverse f →
    (⨁ i, P i) =ᴿ ⨁ j, Q j := by
  intro _ li ri; rw [bigoplus_comm ⟨f, g, li, ri⟩]; congr; ext1 _; tauto

lemma oplus_comm : P ⊕ Q =ᴿ Q ⊕ P := by
  simp only [oplus_as_bigoplus]; rw [bigoplus_comm Equiv.boolNot]; congr;
  simp only [Equiv.boolNot_apply]; grind only

lemma bigoplus_assoc {ι' : ι → Type} [Inhabited ι] [∀ i, Inhabited (ι' i)]
    (P : ∀ i, ι' i → RProp ρ) :
    (⨁ i, ⨁ j, P i j) =ᴿ ⨁ (⟨i, j⟩ : Sigma ι'), P i j := by
  ext1; constructor;
  · rintro ⟨_, _⟩ ⟨_, el, rfl⟩; have ⟨A, el⟩ := Classical.skolem.mp el;
    exists fun ⟨i, j⟩ => A i j; simp only at *; and_intros; { grind only };
    ext; simp only [Mseti.bigoplus_val];
    trans; swap; { apply Mset.bigoplus_assoc (fun i j => (A i j).val.val) };
    congr; ext1 i; rw [(el i).right]; rfl
  · rintro ⟨_, val⟩ ⟨A, el, rfl⟩;
    exists fun i => ⟨⨁ᴹⁱ j, A ⟨i, j⟩, by
      intro _; simp only [Mseti.mem_unfold, Mseti.bigoplus_val, Mset.mem_bigoplus];
      intro ⟨_, _⟩; apply val;
      simp only [Mseti.mem_unfold, Mseti.bigoplus_val, Mset.mem_bigoplus]; tauto⟩;
    and_intros; swap; { symm; ext; apply Mset.bigoplus_assoc };
    intro i; exists fun j => A ⟨i, j⟩; simp only [and_true]; intro _; apply el ⟨_, _⟩

lemma oplus_assoc : (P ⊕ Q) ⊕ R =ᴿ P ⊕ (Q ⊕ R) := by
  have _ : ∀ b, Inhabited (match b with | true => Bool | false => Unit) := by
    rintro (_ | _) <;> apply inferInstance
  have eq : ∀ P Q R : RProp ρ,
      (P ⊕ Q) ⊕ R =ᴿ ⨁ (b : Bool),
        ⨁ (i : match b with | true => Bool | false => Unit),
          match b with | true => if i then P else Q | false => R := by
    intro _ _ _; simp only [oplus_as_bigoplus]; congr; ext1 b; cases b <;> simp only;
    { rw [unary_bigoplus]; rfl }; { rfl }
  rw [eq, oplus_comm, eq]; simp only [bigoplus_assoc];
  apply bigoplus_comm' _ _
    (fun | ⟨true, b⟩ => if b then ⟨false, ()⟩ else ⟨true, true⟩ | ⟨false, _⟩ => ⟨true, false⟩)
    (fun | ⟨true, b⟩ => if b then ⟨true, false⟩ else ⟨false, ()⟩ | ⟨false, _⟩ => ⟨true, true⟩) <;>
    { rintro ⟨(_ | _), i⟩; { rfl }; cases i <;> rfl }

lemma pine_intro_l : (P ⊕ Q ⊢ R) → Q ⊢ P -⊕ R := by
  intro toR A _ B _ _; apply toR; exists B, A, by trivial

lemma pine_intro_r : (P ⊕ Q ⊢ R) → P ⊢ Q -⊕ R := by
  rw [oplus_comm]; apply pine_intro_l

lemma pine_elim_l : P ⊕ (P -⊕ Q) ⊢ Q := by
  rintro ⟨_, _⟩ ⟨_, _, _, _, rfl⟩; tauto

lemma pine_elim_r : (P -⊕ Q) ⊕ P ⊢ Q := by
  rw [oplus_comm]; apply pine_elim_l

lemma pine_adj : (P ⊕ Q ⊢ R) = (Q ⊢ P -⊕ R) := by
  ext1; constructor; { apply pine_intro_l };
  intro Qto; grw [Qto]; apply pine_elim_l

lemma oplus_exists_l (Q : α → RProp ρ) :
    P ⊕ (∃ a, Q a) =ᴿ ∃ a, P ⊕ Q a := by
  ext1; constructor; swap; { apply exists_elim; intro a; grw [exists_intro (Ψ := Q) a] };
  rw [pine_adj]; apply exists_elim; intro a; rw [←pine_adj]; apply exists_intro a

lemma oplus_exists_r (P : α → RProp ρ) Q :
    (∃ a, P a) ⊕ Q =ᴿ ∃ a, P a ⊕ Q := by
  rw [oplus_comm, oplus_exists_l]; congr; ext1 _; rw [oplus_comm]

lemma oplus_or_l : P ⊕ (Q ∨ R) =ᴿ (P ⊕ Q) ∨ (P ⊕ R) := by
  simp only [or_as_exists, oplus_exists_l]; congr; ext1 b; cases b <;> rfl

lemma oplus_or_r : (P ∨ Q) ⊕ R =ᴿ (P ⊕ R) ∨ (Q ⊕ R) := by
  rw [oplus_comm, oplus_or_l, oplus_comm, oplus_comm R]

lemma oplus_false_l : P ⊕ False =ᴿ False := by
  simp only [false_as_exists, oplus_exists_l]; congr; ext1 _; trivial

lemma oplus_false_r : False ⊕ P =ᴿ False := by
  rw [oplus_comm, oplus_false_l]

lemma bigoplus_exists [Inhabited ι] {α : ι → Sort*} (P : ∀ i, α i → RProp ρ) :
    (⨁ i, ∃ a, P i a) =ᴿ ∃ f : (∀ i, α i), ⨁ i, P i (f i) := by
  ext1; constructor; swap;
  { apply exists_elim; intro f; gcongr; apply exists_intro };
  simp only [exists_simple]; rintro ⟨_, _⟩ ⟨F, el, rfl⟩;
  have ⟨f, el⟩ := Classical.skolem.mp el; exists f; exists F

/-! ## Rules for interaction of `⊕` and `⨁` with `∗` -/

lemma bigoplus_frame_l [Inhabited ι] (Q : ι → RProp ρ) :
    P ∗ (⨁ i, Q i) ⊢ ⨁ i, P ∗ Q i := by
  rintro ⟨_, val⟩ ⟨A, ⟨_, _⟩, _, ⟨B, _, rfl⟩, rfl⟩;
  exists fun i => ⟨A.val * (B i).val, by
    intro _; simp only [Mseti.mem_mul]; rintro ⟨r, s, _, _, rfl⟩; apply val; simp only;
    rw [Mseti.mem_mul]; exists r, s;
    simp only [Mseti.mem_unfold, Mseti.bigoplus_val, Mset.mem_bigoplus]; tauto⟩;
  simp only; and_intros; { intro i; exists A, B i; tauto }; { rw [Mseti.mul_bigoplus_l] }

lemma bigoplus_frame_r [Inhabited ι] (P : ι → RProp ρ) Q :
    (⨁ i, P i) ∗ Q ⊢ ⨁ i, P i ∗ Q := by
  grw [sep_comm, bigoplus_frame_l]; gcongr 1; rw [sep_comm]

lemma oplus_frame_l : P ∗ (Q ⊕ R) ⊢ (P ∗ Q) ⊕ (P ∗ R) := by
  grw [oplus_as_bigoplus, oplus_as_bigoplus, bigoplus_frame_l];
  gcongr with b; cases b <;> rfl

lemma oplus_frame_r : (P ⊕ Q) ∗ R ⊢ (P ∗ R) ⊕ (Q ∗ R) := by
  grw [sep_comm, oplus_frame_l, sep_comm, sep_comm R]

lemma bigoplus_unframe_l [Inhabited ι] P (Q : ι → RProp ρ) [Precise P] :
    (⨁ i, P ∗ Q i) =ᴿ P ∗ ⨁ i, Q i := by
  ext1; constructor; swap; { apply bigoplus_frame_l };
  rintro ⟨_, _⟩ ⟨_, el, rfl⟩;
  have ⟨A, el⟩ := Classical.skolem.mp el; have ⟨B, el⟩ := Classical.skolem.mp el;
  have i0 : ι := Classical.choice inferInstance;
  exists A i0, ⟨⨁ᴹⁱ i, B i, by
    intro _; simp only [Mseti.mem_unfold, Mseti.bigoplus_val, Mset.mem_bigoplus];
    intro ⟨i, _⟩; apply (B i).prop; trivial⟩;
  and_intros; { apply (el i0).left };
  { exists B; and_intros; { intro i; exact (el i).right.left }; { rfl } };
  ext1; simp only [Mseti.mul_bigoplus_l]; congr; ext1 i;
  rw [precise P _ _ (el i0).left (el i).left]; grind only

lemma bigoplus_unframe_r [Inhabited ι] (P : ι → RProp ρ) Q [Precise Q] :
    (⨁ i, P i ∗ Q) =ᴿ ((⨁ i, P i) ∗ Q) := by
  ext1; constructor; swap; { apply bigoplus_frame_r };
  grw [sep_comm, ←bigoplus_unframe_l _ _]; gcongr 1; rw [sep_comm]

lemma oplus_unframe_l [Precise P] : (P ∗ Q) ⊕ (P ∗ R) =ᴿ P ∗ (Q ⊕ R) := by
  ext1; constructor; swap; { apply oplus_frame_l };
  simp only [oplus_as_bigoplus]; grw [←bigoplus_unframe_l]; gcongr with b; cases b <;> rfl

lemma oplus_unframe_r [Precise R] : (P ∗ R) ⊕ (Q ∗ R) =ᴿ (P ⊕ Q) ∗ R := by
  ext1; constructor; swap; { apply oplus_frame_r };
  grw [sep_comm iprop(P ⊕ Q), ←oplus_unframe_l, sep_comm, sep_comm Q]

/-! ## Rules for `Precise` -/

lemma bigoplus_precise [Inhabited ι] (P : ι → RProp ρ) :
    (∀ i, Precise (P i)) → Precise iprop(⨁ i, P i) := by
  intro _; constructor; rintro ⟨_, _⟩ ⟨_, _⟩ ⟨F, el, rfl⟩ ⟨G, el', rfl⟩;
  congr; ext1 i; congr; apply precise (P i) <;> tauto

instance bigoplus_instPrecise [Inhabited ι] (P : ι → RProp ρ) [∀ i, Precise (P i)] :
    Precise iprop(⨁ i, P i) :=
  bigoplus_precise P inferInstance

instance oplus_instPrecise [Precise P] [Precise Q] : Precise iprop(P ⊕ Q) := by
  constructor; rw [oplus_as_bigoplus]; apply (bigoplus_precise _ _).precise;
  rintro (_ | _) <;> tauto

/-! ## Rules for `Prob` -/

instance bigoplus_instProb [Inhabited ι] (P : ι → RProp ρ) (p : ι → ℝ≥0∞) [∀ i, Prob (P i) (p i)] :
    Prob iprop(⨁ i, P i) (∑' i, p i) := by
  constructor; rintro ⟨_, _⟩ ⟨_, _, rfl⟩; trans; { apply ENNReal.Mset.tsum_bigoplus };
  congr; ext1 i; apply prob (P i); tauto

instance oplus_instProb [Prob P p] [Prob Q q] : Prob iprop(P ⊕ Q) (p + q) := by
  constructor; rintro ⟨_, _⟩ ⟨_, _, _, _, rfl⟩; trans; { apply ENNReal.Mset.tsum_oplus };
  congr; { apply prob P; trivial }; { apply prob Q; trivial }

end RBI
