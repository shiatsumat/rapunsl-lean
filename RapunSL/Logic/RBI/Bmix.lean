module

public import RapunSL.Logic.RBI.Core
import Mathlib.Logic.Equiv.Bool
open Iris BI RBI Mseti ENNReal

@[expose] public section

/-! # Bare mixing in RapunSL -/

namespace RBI

variable {ρ : Type u} [RM ρ] (P P' Q Q' R : RProp ρ)

/-! ## Bare mixing connectives -/

/-- Binary bare mixing -/
def bmix (P Q : RProp ρ) : RProp ρ :=
  .mk fun A => ∃ B C, B ∈ P ∧ C ∈ Q ∧ A.val = B.val ⊕ᴹⁱ C.val

@[inherit_doc bmix]
scoped syntax:30 term:31 " ⊕ " term:30 : term

/-- Big bare mixing -/
def bigbmix [Inhabited ι] (P : ι → RProp ρ) : RProp ρ :=
  .mk fun A => ∃ B : ι → Msetiv ρ, (∀ i, B i ∈ P i) ∧ A.val = ⨁ᴹⁱ i, (B i).val

@[inherit_doc bigbmix]
scoped syntax "⨁ " Syntax.funBinder ", " term : term

/-- Pine, the right adjoint of `⊕` -/
def pine (P Q : RProp ρ) : RProp ρ :=
  .mk fun A => ∀ B ∈ P, ∀ val, ⟨B.val ⊕ᴹⁱ A.val, val⟩ ∈ Q

@[inherit_doc pine]
scoped syntax:25 term:26 " -⊕ " term:25 : term

scoped macro_rules
  | `(iprop($P ⊕ $Q)) => `(RBI.bmix iprop($P) iprop($Q))
  | `(iprop(⨁ $i, $P)) => `(RBI.bigbmix (fun $i => iprop($P)))
  | `(iprop($P -⊕ $Q)) => `(RBI.pine iprop($P) iprop($Q))

scoped delab_rules RBI.bmix
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ⊕ $(← unpackIprop Q)))

scoped delab_rules RBI.bigbmix
  | `($_ fun $i => $P) => do ``(iprop(⨁ $i, $(← unpackIprop P)))

scoped delab_rules RBI.pine
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) -⊕ $(← unpackIprop Q)))

/-! ## Rules for `⊕`, `⨁` and `-⊕` -/

/-! ### Reinterpretation -/

lemma bmix_as_bigbmix : P ⊕ Q =ᴿ ⨁ (b : Bool), if b then P else Q := by
  apply set_ext; intro ⟨_, _⟩; constructor;
  · rintro ⟨A, B, _, _, rfl⟩; exists fun b => if b then A else B;
    simp only; constructor; { grind only }; rw [Mseti.oplus_as_bigoplus];
    congr; ext1 b; cases b <;> rfl
  · rintro ⟨A, el, rfl⟩; exists A true, A false, el true, el false;
    rw [Mseti.oplus_as_bigoplus]; grind only

lemma unary_bigbmix : (⨁ (_ : Unit), P) =ᴿ P := by
  apply set_ext; intro ⟨A, val⟩; constructor;
  · rintro ⟨A, el, rfl⟩;
    suffices eq : ⟨(⨁ᴹⁱ u, ↑(A u)), val⟩ = A () by { rw [eq]; apply el };
    ext : 2; simp only [Mseti.bigoplus_val, Mset.unary_bigoplus]
  · intro _; exists fun _ => ⟨A, val⟩; simp only; and_intros; { tauto };
    ext1; simp only [Mseti.bigoplus_val, Mset.unary_bigoplus]

/-! ### Monotonicity -/

@[gcongr] lemma bigbmix_mono [Inhabited ι] (P Q : ι → RProp ρ) :
    (∀ i, P i ⊢ Q i) → (⨁ i, P i) ⊢ ⨁ i, Q i := by
  intro _ _ ⟨A, _, _⟩; exists A; tauto

@[gcongr] lemma bmix_mono : (P ⊢ P') → (Q ⊢ Q') → P ⊕ Q ⊢ P' ⊕ Q' := by
  intro _ _; grw [bmix_as_bigbmix, bmix_as_bigbmix]; gcongr; grind only

/-! ### Commutativity -/

private lemma bigbmix_comm_fwd [Inhabited ι] [Inhabited ι'] (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ i, P i) ⊢ ⨁ j, P (f j) := by
  intro _ ⟨A, _, eq⟩; exists A ∘ f; rw [eq]; and_intros; { tauto };
  ext1; simp only [Mseti.bigoplus_val]; rw [Mset.bigoplus_comm f]; rfl

private lemma bigbmix_comm_bwd [Inhabited ι] [Inhabited ι'] (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ j, P (f j)) ⊢ ⨁ i, P i := by
  grw [bigbmix_comm_fwd f.symm]; gcongr; rw [Equiv.apply_symm_apply]

lemma bigbmix_comm [Inhabited ι] [Inhabited ι'] (f : ι' ≃ ι) (P : ι → RProp ρ) :
    (⨁ i, P i) =ᴿ ⨁ j, P (f j) := by
  ext1; constructor; { apply bigbmix_comm_fwd }; { apply bigbmix_comm_bwd }

lemma bigbmix_comm' [Inhabited ι] [Inhabited ι']
    (P : ι → RProp ρ) (Q : ι' → RProp ρ) (f : ι → ι') (g : ι' → ι) :
    (∀ i, P i = Q (f i)) → g.LeftInverse f → g.RightInverse f →
    (⨁ i, P i) =ᴿ ⨁ j, Q j := by
  intro _ li ri; rw [bigbmix_comm ⟨f, g, li, ri⟩]; congr; ext1 _; tauto

lemma bmix_comm : P ⊕ Q =ᴿ Q ⊕ P := by
  simp only [bmix_as_bigbmix]; rw [bigbmix_comm Equiv.boolNot]; congr;
  simp only [Equiv.boolNot_apply]; grind only

/-! ### Associativity -/

lemma bigbmix_assoc {ι' : ι → Type} [Inhabited ι] [∀ i, Inhabited (ι' i)]
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
      intro _; simp only [Mseti.bigoplus_val, Mset.mem_bigoplus];
      intro ⟨_, _⟩; apply val;
      simp only [Mseti.bigoplus_val, Mset.mem_bigoplus]; tauto⟩;
    and_intros; swap; { symm; ext; apply Mset.bigoplus_assoc };
    intro i; exists fun j => A ⟨i, j⟩; simp only [and_true]; intro _; apply el ⟨_, _⟩

lemma bmix_assoc : (P ⊕ Q) ⊕ R =ᴿ P ⊕ (Q ⊕ R) := by
  have _ : ∀ b, Inhabited (match b with | true => Bool | false => Unit) := by
    rintro (_ | _) <;> apply inferInstance
  have eq : ∀ P Q R : RProp ρ,
      (P ⊕ Q) ⊕ R =ᴿ ⨁ (b : Bool),
        ⨁ (i : match b with | true => Bool | false => Unit),
          match b with | true => if i then P else Q | false => R := by
    intro _ _ _; simp only [bmix_as_bigbmix]; congr; ext1 b; cases b <;> simp only;
    { rw [unary_bigbmix]; rfl }; { rfl }
  rw [eq, bmix_comm, eq]; simp only [bigbmix_assoc];
  apply bigbmix_comm' _ _
    (fun | ⟨true, b⟩ => if b then ⟨false, ()⟩ else ⟨true, true⟩ | ⟨false, _⟩ => ⟨true, false⟩)
    (fun | ⟨true, b⟩ => if b then ⟨true, false⟩ else ⟨false, ()⟩ | ⟨false, _⟩ => ⟨true, true⟩) <;>
    { rintro ⟨(_ | _), i⟩; { rfl }; cases i <;> rfl }

/-! ### `-⊕` -/

lemma pine_intro_l : (P ⊕ Q ⊢ R) → Q ⊢ P -⊕ R := by
  intro toR A _ B _ _; apply toR; exists B, A, by trivial

lemma pine_intro_r : (P ⊕ Q ⊢ R) → P ⊢ Q -⊕ R := by
  rw [bmix_comm]; apply pine_intro_l

lemma pine_elim_l : P ⊕ (P -⊕ Q) ⊢ Q := by
  rintro ⟨_, _⟩ ⟨_, _, _, _, rfl⟩; tauto

lemma pine_elim_r : (P -⊕ Q) ⊕ P ⊢ Q := by
  rw [bmix_comm]; apply pine_elim_l

lemma pine_adj : (P ⊕ Q ⊢ R) = (Q ⊢ P -⊕ R) := by
  ext1; constructor; { apply pine_intro_l };
  intro Qto; grw [Qto]; apply pine_elim_l

/-! ### Interaction of `⊕` and `⨁` with disjunction -/

lemma bmix_exists_l (Q : α → RProp ρ) :
    P ⊕ (∃ a, Q a) =ᴿ ∃ a, P ⊕ Q a := by
  ext1; constructor; swap; { apply exists_elim; intro a; grw [exists_intro (Ψ := Q) a] };
  rw [pine_adj]; apply exists_elim; intro a; rw [←pine_adj]; apply exists_intro a

lemma bmix_exists_r (P : α → RProp ρ) Q :
    (∃ a, P a) ⊕ Q =ᴿ ∃ a, P a ⊕ Q := by
  rw [bmix_comm, bmix_exists_l]; congr; ext1 _; rw [bmix_comm]

lemma bmix_or_l : P ⊕ (Q ∨ R) =ᴿ (P ⊕ Q) ∨ (P ⊕ R) := by
  simp only [or_as_exists, bmix_exists_l]; congr; ext1 b; cases b <;> rfl

lemma bmix_or_r : (P ∨ Q) ⊕ R =ᴿ (P ⊕ R) ∨ (Q ⊕ R) := by
  rw [bmix_comm, bmix_or_l, bmix_comm, bmix_comm R]

lemma bmix_false_l : P ⊕ False =ᴿ False := by
  simp only [false_as_exists, bmix_exists_l]; congr; ext1 _; trivial

lemma bmix_false_r : False ⊕ P =ᴿ False := by
  rw [bmix_comm, bmix_false_l]

lemma bigbmix_exists [Inhabited ι] {α : ι → Sort*} (P : ∀ i, α i → RProp ρ) :
    (⨁ i, ∃ a, P i a) =ᴿ ∃ f : (∀ i, α i), ⨁ i, P i (f i) := by
  ext1; constructor; swap;
  { apply exists_elim; intro f; gcongr; apply exists_intro };
  simp only [exists_simple]; rintro ⟨_, _⟩ ⟨F, el, rfl⟩;
  have ⟨f, el⟩ := Classical.skolem.mp el; exists f; exists F

/-! ## Rules for interaction of `⊕` and `⨁` with `∗` -/

lemma bigbmix_frame_l [Inhabited ι] (Q : ι → RProp ρ) :
    P ∗ (⨁ i, Q i) ⊢ ⨁ i, P ∗ Q i := by
  rintro ⟨_, val⟩ ⟨A, ⟨_, _⟩, _, ⟨B, _, rfl⟩, rfl⟩;
  exists fun i => ⟨A.val * (B i).val, by
    intro _; simp only [Mseti.mem_mul]; rintro ⟨r, s, _, _, rfl⟩; apply val; simp only;
    rw [Mseti.mem_mul]; exists r, s;
    simp only [Mseti.bigoplus_val, Mset.mem_bigoplus]; tauto⟩;
  simp only; and_intros; { intro i; exists A, B i; tauto }; { rw [Mseti.mul_bigoplus_l] }

lemma bigbmix_frame_r [Inhabited ι] (P : ι → RProp ρ) Q :
    (⨁ i, P i) ∗ Q ⊢ ⨁ i, P i ∗ Q := by
  grw [sep_comm, bigbmix_frame_l]; gcongr 1; rw [sep_comm]

lemma bmix_frame_l : P ∗ (Q ⊕ R) ⊢ (P ∗ Q) ⊕ (P ∗ R) := by
  grw [bmix_as_bigbmix, bmix_as_bigbmix, bigbmix_frame_l];
  gcongr with b; cases b <;> rfl

lemma bmix_frame_r : (P ⊕ Q) ∗ R ⊢ (P ∗ R) ⊕ (Q ∗ R) := by
  grw [sep_comm, bmix_frame_l, sep_comm, sep_comm R]

lemma bigbmix_unframe_l [Inhabited ι] P (Q : ι → RProp ρ) [Precise P] :
    (⨁ i, P ∗ Q i) =ᴿ P ∗ ⨁ i, Q i := by
  ext1; constructor; swap; { apply bigbmix_frame_l };
  rintro ⟨_, _⟩ ⟨_, el, rfl⟩;
  have ⟨A, el⟩ := Classical.skolem.mp el; have ⟨B, el⟩ := Classical.skolem.mp el;
  have i0 : ι := Classical.choice inferInstance;
  exists A i0, ⟨⨁ᴹⁱ i, B i, by
    intro _; simp only [Mseti.bigoplus_val, Mset.mem_bigoplus];
    intro ⟨i, _⟩; apply (B i).prop; trivial⟩;
  and_intros; { apply (el i0).left };
  { exists B; and_intros; { intro i; exact (el i).right.left }; { rfl } };
  ext1; simp only [Mseti.mul_bigoplus_l]; congr; ext1 i;
  rw [precise P _ _ (el i0).left (el i).left]; grind only

lemma bigbmix_unframe_r [Inhabited ι] (P : ι → RProp ρ) Q [Precise Q] :
    (⨁ i, P i ∗ Q) =ᴿ ((⨁ i, P i) ∗ Q) := by
  ext1; constructor; swap; { apply bigbmix_frame_r };
  grw [sep_comm, ←bigbmix_unframe_l _ _]; gcongr 1; rw [sep_comm]

lemma bmix_unframe_l [Precise P] : (P ∗ Q) ⊕ (P ∗ R) =ᴿ P ∗ (Q ⊕ R) := by
  ext1; constructor; swap; { apply bmix_frame_l };
  simp only [bmix_as_bigbmix]; grw [←bigbmix_unframe_l]; gcongr with b; cases b <;> rfl

lemma bmix_unframe_r [Precise R] : (P ∗ R) ⊕ (Q ∗ R) =ᴿ (P ⊕ Q) ∗ R := by
  ext1; constructor; swap; { apply bmix_frame_r };
  grw [sep_comm iprop(P ⊕ Q), ←bmix_unframe_l, sep_comm, sep_comm Q]

/-! ## Rules for `Precise` -/

/-- Preciseness of `⨁` -/
lemma bigbmix_precise [Inhabited ι] (P : ι → RProp ρ) :
    (∀ i, Precise (P i)) → Precise iprop(⨁ i, P i) := by
  intro _; constructor; rintro ⟨_, _⟩ ⟨_, _⟩ ⟨F, el, rfl⟩ ⟨G, el', rfl⟩;
  congr; ext1 i; congr; apply precise (P i) <;> tauto

/-- Preciseness of `⨁` -/
instance bigbmix_instPrecise [Inhabited ι] (P : ι → RProp ρ) [∀ i, Precise (P i)] :
    Precise iprop(⨁ i, P i) :=
  bigbmix_precise P inferInstance

/-- Preciseness of `⊕` -/
instance bmix_instPrecise [Precise P] [Precise Q] : Precise iprop(P ⊕ Q) := by
  rw [bmix_as_bigbmix]; apply bigbmix_precise; rintro (_ | _) <;> tauto

/-! ## Rules for `Satis` -/

/-- Satisfiability of `⨁` -/
lemma bigbmix_satis [Inhabited ι] (P : ι → RProp ρ) :
    (∀ i, Satis (P i)) → Satis iprop(⨁ i, P i) := by
  intro _; constructor; have ⟨A, el⟩ := Classical.skolem.mp (fun i => satis (P i));
  exists ⟨⨁ᴹⁱ i, A i, by
    intro _; simp only [Mseti.bigoplus_val, Mset.mem_bigoplus]; intro ⟨i, _⟩;
    apply (A i).prop; trivial⟩;
  exists A

instance bigbmix_instSatis [Inhabited ι] (P : ι → RProp ρ) [∀ i, Satis (P i)] :
    Satis iprop(⨁ i, P i) := bigbmix_satis P inferInstance

/-- Satisfiability of `⊕` -/
instance bmix_instSatis [Satis P] [Satis Q] : Satis iprop(P ⊕ Q) := by
  rw [bmix_as_bigbmix]; apply bigbmix_satis; rintro (_ | _) <;> tauto

/-! ## Rules for `Incomp` -/

/-- Incompatibility over `⨁` -/
lemma incomp_bigbmix [Inhabited ι] (P : ι → RProp ρ) :
    (∀ i, P i #ᴿ Q) → (⨁ i, P i) #ᴿ Q := by
  rintro inc ⟨_, val⟩ _ ⟨_, _, rfl⟩ _ _ _; simp only [Mseti.bigoplus_val, Mset.mem_bigoplus];
  intro ⟨i, _⟩; apply inc i <;> tauto

/-- Incompatibility over `⊕` -/
lemma incomp_bmix : (P #ᴿ R) → (Q #ᴿ R) → P ⊕ Q #ᴿ R := by
  intros; rw [bmix_as_bigbmix]; apply incomp_bigbmix; rintro (_ | _) <;> trivial

/-! ## Rules for `Unambig` -/

/-- Unambiguity over `⨁` -/
lemma bigbmix_unambig [Inhabited ι] (P : ι → RProp ρ) :
    (∀ i, Unambig (P i)) → (∀ i j, i ≠ j → Incomp (P i) (P j)) →
    Unambig (ρ := ρ) iprop(⨁ i, P i) := by
  intro _ inc; constructor; rintro ⟨_, _⟩ ⟨_, _, rfl⟩ _ _;
  rw [Mseti.bigoplus_val, Mset.pairmem_bigoplus];
  rintro (⟨i, _⟩ | ⟨_, _, _, _, _⟩);
  { apply unambig (P i) <;> tauto }; { apply inc <;> tauto }

/-- Unambiguity over `⊕` -/
lemma bmix_unambig [Unambig P] [Unambig Q] :
    Incomp P Q → Unambig (ρ := ρ) iprop(P ⊕ Q) := by
  intro inc; rw [bmix_as_bigbmix]; apply bigbmix_unambig;
  { rintro (_ | _) <;> simp only [Bool.false_eq_true, reduceIte] <;> trivial };
  rintro (_ | _) (_ | _) <;> simp only [Bool.false_eq_true, reduceIte] <;> tauto

/-! ## Rules for `Coher` -/

/-- Coherence over `⨁` -/
lemma bigbmix_coher [Inhabited ι] (P : ι → RProp ρ) (Q : ι → RProp ρ) :
    (∀ i, P i ≎ᴿ Q i) → (⨁ i, P i) ≎ᴿ ⨁ i, Q i := by
  rintro coh ⟨_, _⟩ ⟨_, _⟩ ⟨_, elP, rfl⟩ ⟨_, elQ, rfl⟩;
  rcases Classical.skolem.mp (fun i => coh i _ _ (elP i) (elQ i)) with ⟨r, coh⟩;
  exists Mset.Bij.bigoplus r; intro _ _;
  simp only [Mseti.bigoplus_val, Mset.Bij.bigoplus_graph, Mset.mem_bigoplus];
  intro ⟨_, _⟩; tauto

/-- Coherence over `⊕` -/
lemma bmix_coher (P Q : RProp ρ) (R R' : RProp ρ) :
    (P ≎ᴿ R) → (Q ≎ᴿ R') → P ⊕ Q ≎ᴿ R ⊕ R' := by
  intro _ _; simp only [bmix_as_bigbmix]; apply bigbmix_coher;
  rintro (_ | _) <;> simp only [Bool.false_eq_true, reduceIte] <;> trivial

/-! ## Rules for `Prob` -/

/-- Probability of `⨁` -/
instance bigbmix_instProb [Inhabited ι] (P : ι → RProp ρ) (p : ι → ℝ≥0∞) [∀ i, Prob (P i) (p i)] :
    Prob iprop(⨁ i, P i) (∑' i, p i) := by
  constructor; rintro ⟨_, _⟩ ⟨_, _, rfl⟩; trans; { apply ENNReal.Mset.tsum_bigoplus };
  congr; ext1 i; apply prob (P i); tauto

/-- Probability of `⊕` -/
instance bmix_instProb [Prob P p] [Prob Q q] : Prob iprop(P ⊕ Q) (p + q) := by
  constructor; rintro ⟨_, _⟩ ⟨_, _, _, _, rfl⟩; trans; { apply ENNReal.Mset.tsum_oplus };
  congr; { apply prob P; trivial }; { apply prob Q; trivial }

end RBI
