module

public import RapunSL.Logic.RBI.Core
open Iris BI RBI Mset Mseti PCM PCMC RR

@[expose] public section

/-! # Sum in RapunSL -/

namespace RBI
variable {ρ : Type u} [RR ρ] (P P' Q Q' R : RProp ρ)
  (A B C AB ABC : Mset ρ)

/-! ## Addition of multisets -/

/-- Addition relation over `Mset`s -/
def rmadd (A B C : Mset ρ) : Prop :=
  ∃ AB : A ≃ᴹ B,
    (∀ a b, (a, b) ∈ AB.graph → a ≎ b) ∧
    C = (fun (a, b) ↦ a + b) <$>ᴹ AB.graph

@[inherit_doc rmadd]
scoped macro:50 A:term:50 " +ᴿᴹ " B:term " =ᴿᴹ " C:term:50 : term => `(RBI.rmadd $A $B $C)

/-- `+ᴿᴹ` is commutative -/
lemma rmadd_comm' : A +ᴿᴹ B =ᴿᴹ C → B +ᴿᴹ A =ᴿᴹ C := by
  rintro ⟨AB, coh, rfl⟩; exists AB.symm; and_intros;
  · intro _ _; rw [Bij.symm_graph_mem]; intro _; symm; apply coh; trivial
  · simp only [Bij.symm_graph, ←Mset.comp_map];
    congr; ext1 ⟨a, b⟩; rw [add_comm a b]; rfl

/-- `+ᴿᴹ` is commutative -/
lemma rmadd_comm : A +ᴿᴹ B =ᴿᴹ C ↔ B +ᴿᴹ A =ᴿᴹ C := by
  constructor <;> (intro _; apply rmadd_comm'; trivial)

/-- Construct `+ᴿᴹ` from a multiset of coherent pairs -/
lemma pairs_rmadd (S : Mset (ρ × ρ)) :
    (∀ a b, (a, b) ∈ S → a ≎ b) →
    (Prod.fst <$>ᴹ S) +ᴿᴹ (Prod.snd <$>ᴹ S) =ᴿᴹ (fun (a, b) ↦ a + b) <$>ᴹ S := by
  intro coh;
  have hg : ((Mset.Bij.map_l Prod.fst S).trans (Mset.Bij.map_r Prod.snd S)).graph = S := by
    rw [Mset.Bij.trans_graph_map_l (Mset.Bij.map_l Prod.fst S) (Mset.Bij.map_r Prod.snd S)
      Prod.fst (by intro _ _ mem; rw [Mset.Bij.map_l_graph_mem] at mem; exact mem.1)];
    rw [Mset.Bij.map_r_graph, ←Mset.comp_map]; exact Mset.id_map S
  exists (Mset.Bij.map_l Prod.fst S).trans (Mset.Bij.map_r Prod.snd S); and_intros;
  { rw [hg]; exact coh }; { rw [hg] }

/-- Construct `+ᴿᴹ` from two coherent images of a common multiset -/
lemma rmadd_map {σ : Type*} (S : Mset σ) (f g : σ → ρ) {A B C : Mset ρ} :
    (∀ x ∈ S, f x ≎ g x) → f <$>ᴹ S = A → g <$>ᴹ S = B →
    (fun x ↦ f x + g x) <$>ᴹ S = C → A +ᴿᴹ B =ᴿᴹ C := by
  rintro coh rfl rfl rfl;
  have hcoh : ∀ a b, (a, b) ∈ (fun x ↦ (f x, g x)) <$>ᴹ S → a ≎ b := by
    intro a b mem; rw [Mset.map'_mem] at mem;
    rcases mem with ⟨x, memS, eq⟩; injection eq with ea eb; subst ea; subst eb;
    exact coh _ memS
  have h := pairs_rmadd _ hcoh;
  rw [←Mset.comp_map, ←Mset.comp_map, ←Mset.comp_map] at h; exact h

/-- `+ᴿᴹ` preserves inhabitedness -/
lemma rmadd_inhab : A +ᴿᴹ B =ᴿᴹ C → A.inhab → C.inhab := by
  rintro ⟨r, _, rfl⟩ inh; rw [Mset.inhab_map'];
  rw [←Mset.Bij.graph_fst r, Mset.inhab_map'] at inh; exact inh

/-- `+ᴿᴹ` transfers validity of the sum to the left-hand summand -/
lemma rmadd_valid_l : A +ᴿᴹ B =ᴿᴹ C → (∀ c ∈ C, ✓ c) → ∀ a ∈ A, ✓ a := by
  rintro ⟨r, coh, rfl⟩ val a elA;
  rw [←Mset.Bij.graph_fst r, Mset.map'_mem] at elA;
  rcases elA with ⟨⟨a', b⟩, mem, rfl⟩;
  refine (RR.add_valid_l _ _ (coh _ _ mem)).mp ?_;
  apply val; rw [Mset.map'_mem]; exact ⟨_, mem, rfl⟩

/-- `+ᴿᴹ` transfers validity of the sum to the right-hand summand -/
lemma rmadd_valid_r : A +ᴿᴹ B =ᴿᴹ C → (∀ c ∈ C, ✓ c) → ∀ b ∈ B, ✓ b := by
  rw [rmadd_comm]; apply rmadd_valid_l

/-- `+ᴿᴹ` is associative -/
lemma rmadd_assoc_l :
    A +ᴿᴹ B =ᴿᴹ AB → AB +ᴿᴹ C =ᴿᴹ ABC → ∃ BC, B +ᴿᴹ C =ᴿᴹ BC ∧ A +ᴿᴹ BC =ᴿᴹ ABC := by
  rintro ⟨r₁, coh₁, rfl⟩ ⟨r₂, coh₂, rfl⟩;
  rcases Mset.Bij.graph_unmap_l (fun ((a, b) : ρ × ρ) ↦ a + b) r₂ with ⟨S, hfst, hsnd, hgr⟩;
  have pw : ∀ a b c, ((a, b), c) ∈ S → b ≎ c ∧ a ≎ b + c ∧ (a + b) + c = a + (b + c) := by
    intro a b c mem;
    have h₁ : a ≎ b := by
      apply coh₁; rw [←hfst, Mset.map'_mem]; exact ⟨((a, b), c), mem, rfl⟩
    have h₂ : a + b ≎ c := by
      apply coh₂; rw [←hgr, Mset.map'_mem]; exact ⟨((a, b), c), mem, rfl⟩
    have hbc := PCMC.coher_trans _ _ _ (PCMC.coher_symm' _ _ (RR.add_coher_r _ _ h₁)) h₂;
    exact ⟨hbc, PCMC.coher_trans _ _ _ h₁ (PCMC.coher_symm' _ _ (RR.add_coher_l _ _ hbc)),
      RR.add_assoc _ _ _ h₁ hbc⟩
  refine ⟨(fun ((a, b), c) ↦ b + c) <$>ᴹ S, ?_, ?_⟩
  · apply rmadd_map S (fun ((a, b), c) ↦ b) Prod.snd;
    · rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).1
    · rw [←Mset.Bij.graph_snd r₁, ←hfst, ←Mset.comp_map]; rfl
    · exact hsnd
    · rfl
  · apply rmadd_map S (fun ((a, b), c) ↦ a) (fun ((a, b), c) ↦ b + c);
    · rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).2.1
    · rw [←Mset.Bij.graph_fst r₁, ←hfst, ←Mset.comp_map]; rfl
    · rfl
    · rw [←hgr, ←Mset.comp_map]; apply Mset.map_congr;
      rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).2.2.symm

/-! ## Sum connectives -/

/-- Binary sum over `RProp` -/
instance RProp.instAdd : Add (RProp ρ) where
  add P Q := .mk fun C ↦ ∃ A B, A ∈ P ∧ B ∈ Q ∧
    A.val.val +ᴿᴹ B.val.val =ᴿᴹ C.val.val

scoped macro_rules
  | `(iprop($P + $Q)) => `(iprop($P) + iprop($Q))

/-- Cross, the right adjoint of `+` -/
def cross (P Q : RProp ρ) : RProp ρ :=
  .mk fun A ↦ ∀ B, B ∈ P → ∀ C, A.val.val +ᴿᴹ B.val.val =ᴿᴹ C.val.val → C ∈ Q

@[inherit_doc cross]
scoped syntax:25 term:26 " -+ " term:25 : term

scoped macro_rules
  | `(iprop($P -+ $Q)) => `(RBI.cross iprop($P) iprop($Q))

scoped delab_rules RBI.cross
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) -+ $(← unpackIprop Q)))

/-- Unfold `+` for `RProp` -/
lemma add_unfold :
    (HAdd.hAdd : RProp ρ → RProp ρ → RProp ρ) =
      fun P Q => .mk fun C ↦ ∃ A B, A ∈ P ∧ B ∈ Q ∧
        A.val.val +ᴿᴹ B.val.val =ᴿᴹ C.val.val := rfl

/-- `+` is monotone -/
@[gcongr] lemma add_mono : (P ⊢ P') → (Q ⊢ Q') → P + Q ⊢ P' + Q' := by
  intro PP' QQ' _ ⟨A, B, _, _, _⟩; exists A, B; and_intros;
  { apply PP'; trivial }; { apply QQ'; trivial }; trivial

/-- `+` is commutative -/
private lemma add_comm' : P + Q ⊢ Q + P := by
  intro _ ⟨A, B, _, _, _⟩; exists B, A; and_intros; { trivial }; { trivial };
  apply rmadd_comm'; trivial

/-- `+` is commutative -/
instance RProp.instAddCommMagma : AddCommMagma (RProp ρ) where
  add_comm := by intro _ _; ext; constructor <;> apply add_comm'

/-- `+` is associative -/
private lemma add_assoc' : (P + Q) + R ⊢ P + (Q + R) := by
  rintro D ⟨ABv, Cv, ⟨Av, Bv, elP, elQ, hAB⟩, elR, hABC⟩;
  rcases rmadd_assoc_l _ _ _ _ _ hAB hABC with ⟨BC, hBC, hA⟩;
  have inh : BC.inhab := rmadd_inhab _ _ _ hBC Bv.val.property;
  have val : ∀ b ∈ BC, ✓ b := rmadd_valid_r _ _ _ hA D.property;
  exists Av, ⟨⟨BC, inh⟩, val⟩; and_intros;
  { trivial }; { exists Bv, Cv }; { trivial }

/-- `+` is associative -/
instance RProp.instAddCommSemigroup : AddCommSemigroup (RProp ρ) where
  add_assoc := by
    intro P Q R; apply entails_antisymm; { apply add_assoc' };
    rw [add_comm P (Q + R), add_comm Q R, add_comm P Q, add_comm (Q + P) R];
    apply add_assoc'

/-! ### Rules for `-+` -/

/-- Introduce `-+`, absorbing the left operand of `+` -/
lemma cross_intro_l : (P + Q ⊢ R) → Q ⊢ P -+ R := by
  intro toR A elQ B elP C hadd; apply toR; exists B, A; and_intros;
  { trivial }; { trivial }; apply rmadd_comm'; trivial

/-- Introduce `-+`, absorbing the right operand of `+` -/
lemma cross_intro_r : (P + Q ⊢ R) → P ⊢ Q -+ R := by
  rw [add_comm]; apply cross_intro_l

/-- Eliminate `-+`, with the argument supplied on the left -/
lemma cross_elim_l : P + (P -+ Q) ⊢ Q := by
  rintro C ⟨A, B, elP, elPQ, hadd⟩; apply elPQ A elP; apply rmadd_comm'; trivial

/-- Eliminate `-+`, with the argument supplied on the right -/
lemma cross_elim_r : (P -+ Q) + P ⊢ Q := by
  rw [add_comm]; apply cross_elim_l

/-- `-+` is the right adjoint of `+` -/
lemma cross_adj : (P + Q ⊢ R) ↔ (Q ⊢ P -+ R) := by
  constructor; { apply cross_intro_l };
  intro Qto; grw [Qto]; apply cross_elim_l

/-- `-+` is antitone on the left and monotone on the right -/
@[gcongr] lemma cross_mono : (P' ⊢ P) → (Q ⊢ Q') → (P -+ Q) ⊢ P' -+ Q' := by
  intro P'P QQ'; rw [←cross_adj]; grw [P'P, ←QQ']; rw [cross_adj]

end RBI
