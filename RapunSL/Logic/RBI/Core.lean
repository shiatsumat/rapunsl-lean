module

public import RapunSL.Util.Syntax
public import Iris.BI
public import RapunSL.Math.Algebra.Mseti
public import RapunSL.Logic.BI
open Iris OFE BI PCM PCMI PCMC PCMP ENNReal Mset

@[expose] public section

/-! # RapunSL's BI -/

namespace RBI

/-! ## RapunSL propositions -/

/-- RapunSL proposition based on a multiset PCMP -/
def RProp ρ [RM ρ] := LeibnizO (Set (Msetiv ρ))

variable {ρ : Type u} [RM ρ] (P Q R : RProp ρ) (r s : ρ)

instance RProp_instMembership : Membership (Msetiv ρ) (RProp ρ) where
  mem P A := P.car A

lemma unfold_mem A : (A ∈ P) = P.car A := rfl

lemma set_ext : (∀ A, A ∈ P ↔ A ∈ Q) → P = Q := by
  intro _; apply congrArg LeibnizO.mk; apply Set.ext; trivial

instance RProp_instCOFE : COFE (RProp ρ) := instCOFELeibnizO

/-! ## BI structure -/

/-- BI definitions for `RProp` -/
instance RProp_instBIBase : BIBase (RProp ρ) where
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
  simp only [unfold_mem]; rintro _ _ ⟨_, rfl⟩; tauto

lemma exists_simple :
    BIBase.exists = fun P : α → RProp ρ => .mk fun A => ∃ x, A ∈ P x := by
  funext P; apply set_ext; intro _; constructor;
  { rintro ⟨_, ⟨_, rfl⟩, _⟩; tauto }; { rintro ⟨a, _⟩; exists P a; tauto }

@[refl] lemma entails_refl : P ⊢ P := by tauto

@[trans] lemma entails_trans : (P ⊢ Q) → (Q ⊢ R) → P ⊢ R := by tauto

lemma entails_antisymm :
    (P ⊢ Q) → (Q ⊢ P) → P = Q := by
  intro _ _; apply set_ext; intro _; constructor <;> tauto

instance RProp_entails_instPreorder : Std.Preorder (Entails (PROP := RProp ρ)) where
  refl := entails_refl _
  trans := entails_trans _ _ _

/-- BI properties for `RProp` -/
instance RProp_instBI : BI (RProp ρ) where
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

instance RProp_entails_instPartialOrder : IsPartialOrder (RProp ρ) Entails where
  antisymm := entails_antisymm

/-- Extensionality for `RProp` -/
instance RProp_instBIE : BIE (RProp ρ) where
  bi_ext := by intro _ _ ⟨PQ, QP⟩; apply antisymm PQ QP

/-! ### Extra properties -/

lemma not_contra : P ∧ ¬ P ⊢ Q := nofun

lemma not_em : Q ⊢ P ∨ ¬ P := by tauto

lemma choice {β : α → Sort*} (P : ∀ a, β a → RProp ρ) :
    (∀ x, ∃ y, P x y) =ᴮᴵ ∃ f : ∀ a, β a, ∀ x, P x (f x) := by
  simp only [forall_simple, exists_simple];
  apply set_ext; intro _; apply Classical.skolem

lemma persistently_emp_entails : <pers> P =ᴮᴵ ⌜emp ⊢ P⌝ := by
  apply set_ext; intro _; constructor; swap; { tauto };
  intro _ ⟨_, _⟩; rw [emp_unfold]; intro rfl; trivial

/-! ## Ownership -/

/-- Ownership of an element -/
def own (r : ρ) : RProp ρ := .mk fun A => A.val = pure r

lemma own_unfold r A : (A ∈ own (ρ := ρ) r) = (A.val = pure r) := rfl

/-! ### Rules for `own` -/

lemma emp_as_own : emp = own (ρ := ρ) 1 := rfl

lemma own_sep : own (ρ := ρ) r ∗ own s =ᴮᴵ own (r * s) := by
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

/-! ## Satisfiability -/

/-- Satisfiability of a proposition, i.e., not being `False` -/
class Satis (P : RProp ρ) : Prop where
  satis : ∃ A, A ∈ P

lemma satis (P : RProp ρ) [Satis P] : ∃ A, A ∈ P := by
  apply Satis.satis

/-! ### Satisfiability lemmas -/

/-- Satisfiability is the same as not being `False` -/
lemma satis_ne_false : Satis P = (P ≠ iprop(False)) := by
  ext1; constructor; { intro ⟨_, _⟩ rfl; trivial }
  intro ne; constructor; apply Classical.not_forall_not.mp; intro el;
  suffices P =ᴮᴵ False by { tauto }; ext1; constructor <;> tauto

/-- Satisfiability is monotone -/
lemma satis_mono [Satis P] : (P ⊢ Q) → Satis Q := by
  intro PQ; constructor; rcases satis P with ⟨A, _⟩; exists A; apply PQ; trivial

/-- Satisfiability of `own` -/
lemma own_instSatis : ✓ r → Satis (own r) := by
  intro val; constructor; exists ⟨pure r, by rw [Mseti.valid_pure]; trivial⟩

/-- Satisfiability of `emp` -/
instance emp_instSatis : Satis (ρ := ρ) emp := by
  constructor; exists ⟨1, PCM.valid_one⟩

/-- Satisfiability of `pure` -/
lemma pure_instSatis (φ : Prop) : φ → Satis (ρ := ρ) (pure φ) := by
  intro h; constructor; exists ⟨1, PCM.valid_one⟩

/-- Satisfiability of `True` -/
instance true_instSatis : Satis (ρ := ρ) iprop(True) := by
  apply pure_instSatis; trivial

/-! ## Incompatibility -/

/-- Incompatibility between propositions -/
def Incomp (P Q : RProp ρ) : Prop :=
  ∀ A B, A ∈ P → B ∈ Q → ∀ a b, a ∈ A.val.val → b ∈ B.val.val → a # b

@[inherit_doc Incomp]
scoped macro:25 P:term:25 " #ᴿ " Q:term:25 : term => `(Incomp iprop($P) iprop($Q))

scoped delab_rules Incomp
  | `($_ $P $Q) => do ``($(← unpackIprop P) #ᴿ $(← unpackIprop Q))

/-! ### Incompatibility lemmas -/

/-- Incompatibility is symmetric -/
@[symm] lemma incomp_symm : (P #ᴿ Q) → Q #ᴿ P := by
  intro inc _ _ _ _ _ _ _ _; symm; apply inc <;> trivial

/-- Incompatibility is antitone -/
lemma incomp_anti :
    (P' #ᴿ Q') → (P ⊢ P') → (Q ⊢ Q') → P #ᴿ Q := by
  intro inc PP' QQ' _ _ _ _ ; apply inc; { apply PP'; trivial }; { apply QQ'; trivial }

/-- Incompatibility over `∃` -/
lemma incomp_exists (P : α → RProp ρ) : (∀ x, P x #ᴿ Q) → (∃ x, P x) #ᴿ Q := by
  rewrite [exists_simple]; intro _ _ _ ⟨_, _⟩; tauto

/-- Incompatibility over `∨` -/
lemma incomp_or : (P #ᴿ R) → (Q #ᴿ R) → (P ∨ Q) #ᴿ R := by
  rintro _ _ _ _ (_ | _) <;> tauto

/-- Incompatibility over `False` -/
lemma incomp_false : False #ᴿ P := nofun

/-- Incompatibility over `own` -/
lemma incomp_own : r # s → own r #ᴿ own s := by
  rintro inc ⟨_, _⟩ ⟨_, _⟩ rfl rfl _ _; simp only [Mseti.pure_val, Mset.pure_mem]; aesop

/-- Incompatibility over `∗` -/
lemma incomp_sep_l : (P #ᴿ Q) → P ∗ R #ᴿ Q := by
  rintro inc ⟨_, val⟩ _ ⟨_, _, _, _, rfl⟩ _ _ _; simp only [Mseti.mul_mem];
  rintro ⟨_, _, _, _, rfl⟩ _; apply PCMI.incomp_mul_l;
  { apply val; simp only [Mseti.mul_mem]; tauto }; { apply inc <;> try trivial }

/-- Incompatibility over `∗` -/
lemma incomp_sep_r : (P #ᴿ Q) → R ∗ P #ᴿ Q := by
  rw [sep_comm']; apply incomp_sep_l

/-! ## Unambiguity -/

/-- Unambiguity of a proposition -/
class Unambig (P : RProp ρ) : Prop where
  /-- Unambiguity condition -/
  unambig : ∀ A ∈ P, ∀ a b, A.val.val.pairmem a b → a # b

/-- Unambiguity condition -/
lemma unambig [Unambig P] : ∀ A ∈ P, ∀ a b, A.val.val.pairmem a b → a # b := by
  apply Unambig.unambig

/-! ### Unambiguity lemmas -/

/-- Unambiguity is antitone -/
lemma unambig_anti [Unambig Q] : (P ⊢ Q) → Unambig P := by
  intro PQ; constructor; intro _ _ _ _; apply unambig Q; apply PQ; trivial

/-- Unambiguity over `∃` -/
instance exists_instUnambig (P : α → RProp ρ) [∀ x, Unambig (P x)] : Unambig iprop(∃ x, P x) := by
  rewrite [exists_simple]; constructor; intro _ ⟨a, _⟩; apply unambig (P a); trivial

/-- Unambiguity over `∨` -/
instance or_instUnambig [Unambig P] [Unambig Q] : Unambig iprop(P ∨ Q) := by
  constructor; rintro _ (_ | _); { apply unambig P; trivial }; { apply unambig Q; trivial }

/-- Unambiguity over `False` -/
instance false_instUnambig : Unambig (ρ := ρ) iprop(False) := by
  constructor; nofun

/-- Unambiguity over `own` -/
instance own_instUnambig (r : ρ) : Unambig (own r) := by
  constructor; intro ⟨_, _⟩ rfl _ _; rw [Mseti.pure_val, Mset.pure_pairmem r]; tauto

/-- Unambiguity over `emp` -/
instance emp_instUnambig : Unambig (ρ := ρ) emp := by apply own_instUnambig

/-- Unambiguity over `∗` -/
instance sep_instUnambig [Unambig P] [Unambig Q] :
    Unambig iprop(P ∗ Q) := by
  constructor; rintro ⟨_, val⟩ ⟨_, _, elP, _, rfl⟩ _ _; simp only [Mseti.mul_pairmem];
  rintro ⟨_, _, _, _, rfl, rfl, (⟨_, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩)⟩;
  swap;
  { apply PCMI.incomp_mul_r;
    { apply val; rw [Mseti.mul_mem]; grind only [Mset.pairmem_mem_l] };
    symm; apply PCMI.incomp_mul_r;
    { apply val; rw [Mseti.mul_mem]; grind only [Mset.pairmem_mem_r] };
    apply unambig Q <;> tauto };
  all_goals
  { apply PCMI.incomp_mul_l;
    { apply val; rw [Mseti.mul_mem]; grind only [Mset.pairmem_mem_l] };
    symm; apply PCMI.incomp_mul_l;
    { apply val; rw [Mseti.mul_mem]; grind only [Mset.pairmem_mem_r] };
    apply unambig P <;> tauto }

/-! ## Coherence -/

/-- Coherence of propositions -/
def Coher (P Q : RProp ρ) : Prop :=
  ∀ A B, A ∈ P → B ∈ Q → ∃ f : A.val.val ≃ᴹ B.val.val, ∀ a b, (a, b) ∈ f.graph → a ≎ b

@[inherit_doc Coher]
scoped macro:25 P:term:25 " ≎ᴿ " Q:term:25 : term => `(Coher iprop($P) iprop($Q))

scoped delab_rules Coher
  | `($_ $P $Q) => do ``($(← unpackIprop P) ≎ᴿ $(← unpackIprop Q))

/-! ### Coherence lemmas -/

/-- Coherence is symmetric -/
@[symm] lemma coher_symm : (P ≎ᴿ Q) → Q ≎ᴿ P := by
  intro coh _ _ elQ elP; rcases coh _ _ elP elQ with ⟨f, eq⟩; exists f.symm; intro _ _;
  simp only [Mset.Bij.symm_graph, Mset.map'_mem]; rintro ⟨_, _, _⟩; symm; grind only

/-- Coherence is transitive, under satisfiability of the middle proposition -/
@[trans] lemma coher_trans [Satis Q] : (P ≎ᴿ Q) → (Q ≎ᴿ R) → P ≎ᴿ R := by
  intro coh coh' _ _ elP elR; have ⟨_, elQ⟩ := satis Q;
  rcases coh _ _ elP elQ with ⟨f, coh⟩; rcases coh' _ _ elQ elR with ⟨g, coh'⟩;
  exists f.trans g; intro _ _ mem;
  rcases Mset.Bij.trans_graph_mem _ _ _ _ mem with ⟨_, _, _⟩;
  apply PCMC.coher_trans; { apply coh; trivial }; { apply coh'; trivial }

/-- Coherence is antitone -/
lemma coher_anti : (P' ≎ᴿ Q') → (P ⊢ P') → (Q ⊢ Q') → P ≎ᴿ Q := by
  intro coh PP' QQ' _ _ elP elQ; apply coh; { apply PP'; trivial }; { apply QQ'; trivial }

/-- Coherence over `∃` -/
lemma coher_exists (P : α → RProp ρ) : (∀ x, P x ≎ᴿ Q) → (∃ x, P x) ≎ᴿ Q := by
  rewrite [exists_simple]; intro _ _ _ ⟨_, _⟩; tauto

/-- Coherence over `∨` -/
lemma coher_or : (P ≎ᴿ R) → (Q ≎ᴿ R) → (P ∨ Q) ≎ᴿ R := by
  rintro _ _ _ _ (_ | _) <;> tauto

/-- Coherence over `False` -/
lemma coher_false : False ≎ᴿ P := nofun

/-- Coherence over `own` -/
lemma coher_own : r ≎ s → own r ≎ᴿ own s := by
  intro coh ⟨_, _⟩ ⟨_, _⟩ rfl rfl; exists Mset.Bij.pure _ _; intro _ _;
  simp only [Mset.Bij.pure_graph, Mset.pure_mem]; rintro ⟨_, _⟩; trivial

/-- Coherence over `∗` -/
lemma coher_sep : (P ≎ᴿ P') → (Q ≎ᴿ Q') → P ∗ Q ≎ᴿ P' ∗ Q' := by
  rintro cohP cohQ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _, elP, elQ, rfl⟩ ⟨_, _, elP', elQ', rfl⟩;
  rcases cohP _ _ elP elP' with ⟨r, _⟩; rcases cohQ _ _ elQ elQ' with ⟨s, _⟩;
  exists Mseti.Bij.mul r s; intro _ _;
  simp only [Mseti.Bij.mul_graph, Mset.seq'_mem, Mset.map'_mem];
  rintro ⟨_, ⟨_, _, rfl⟩, _, _, _, ⟨_, _⟩, _⟩; apply PCMC.coher_mul <;> tauto

/-! ## Probability -/

/-- `P` entails the probability `p` -/
class Prob (P : RProp ρ) (p : ℝ≥0∞) : Prop where
  /-- Probability condition -/
  prob : ∀ A ∈ P, PCMP.prob A.val = p

/-- Probability condition -/
lemma prob (P : RProp ρ) (p : ℝ≥0∞) [Prob P p] : ∀ A ∈ P, PCMP.prob A.val = p := by
  apply Prob.prob

/-! ### Rules for `Prob` -/

/-- `Prob` is antitone -/
lemma prob_anti [Prob Q p] : (P ⊢ Q) → Prob P p := by
  intro _; constructor; intro _ _; apply prob Q; tauto

/-- Probability under preciseness -/
lemma precise_prob [Precise P] : ∃ p, Prob P p := by
  rcases em (∃ A, A ∈ P) with ⟨A, el⟩ | _; swap; { exists 0; constructor; tauto };
  exists PCMP.prob A.val; constructor; intro _ el'; rw [precise P _ _ el el']

/-- Probability of `∃` -/
instance exists_instProb (P : α → RProp ρ) [∀ x, Prob (P x) p] : Prob iprop(∃ x, P x) p := by
  rw [exists_simple]; constructor; rintro ⟨_, _⟩ ⟨a, _⟩; apply prob (P a); trivial

/-- Probability of `∨` -/
instance or_instProb [Prob P p] [Prob Q p] : Prob iprop(P ∨ Q) p := by
  constructor; rintro ⟨_, _⟩ (_ | _); { apply prob P; trivial }; { apply prob Q; trivial }

/-- Probability of `False` -/
instance false_instProb p : Prob (ρ := ρ) iprop(False) p := by
  constructor; nofun

/-- Probability of `own` -/
instance own_instProb : Prob (own r) (PCMP.prob r) := by
  constructor; rintro ⟨_, _⟩ rfl; apply Mseti.prob_pure

/-- Probability of `emp` -/
instance emp_instProb : Prob (ρ := ρ) emp 1 := by
  constructor; rintro ⟨_, _⟩ rfl; simp only [Mseti.one_unfold, Mseti.prob_pure, PCMP.prob_one]

/-- Probability of `∗` -/
instance sep_instProb [Prob P p] [Prob Q q] : Prob iprop(P ∗ Q) (p * q) := by
  constructor; rintro ⟨_, val⟩ ⟨_, _, elP, elQ, rfl⟩;
  rw [PCMP.prob_mul _ _ val, prob P p _ elP, prob Q q _ elQ]

end RBI
