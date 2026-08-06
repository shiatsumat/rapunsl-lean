module

public import RapunSL.Logic.RBI.Core
open Iris BI RBI Mset Mseti PCM PCMC RR

@[expose] public section

/-! # Sum in RapunSL -/

namespace RBI
variable {ρ : Type u} [RR ρ] (P P' Q Q' R : RProp ρ)
  (A B C AB ABC : Mset ρ)

/-! ## Sum connectives -/

/-- Addition of `Mset`s -/
def Mset.radd (A B C : Mset ρ) : Prop :=
  ∃ AB : A ≃ᴹ B,
    (∀ a b, (a, b) ∈ AB.graph → a ≎ b) ∧
    C = (fun (a, b) ↦ a + b) <$>ᴹ AB.graph

scoped macro:50 A:term:50 " +ᴿᴹ " B:term " =ᴿᴹ " C:term:50 : term => `(RBI.Mset.radd $A $B $C)

/-- Binary sum over `RProp` -/
instance RProp.instAdd : Add (RProp ρ) where
  add P Q := .mk fun C ↦ ∃ A B, A ∈ P ∧ B ∈ Q ∧
    A.val.val +ᴿᴹ B.val.val =ᴿᴹ C.val.val

/-- Unfold `+` for `RProp` -/
lemma add_unfold :
    (HAdd.hAdd : RProp ρ → RProp ρ → RProp ρ) =
      fun P Q => .mk fun C ↦ ∃ A B, A ∈ P ∧ B ∈ Q ∧
        A.val.val +ᴿᴹ B.val.val =ᴿᴹ C.val.val := rfl

/-- `+` is monotone -/
@[gcongr] lemma add_mono : (P ⊢ P') → (Q ⊢ Q') → P + Q ⊢ P' + Q' := by
  intro PP' QQ' _ ⟨A, B, _, _, _⟩; exists A, B; and_intros;
  { apply PP'; trivial }; { apply QQ'; trivial }; trivial

/-- `+ᴿᴹ` is commutative -/
lemma radd_comm' : A +ᴿᴹ B =ᴿᴹ C → B +ᴿᴹ A =ᴿᴹ C := by
  rintro ⟨AB, coh, rfl⟩; exists AB.symm; and_intros;
  · intro _ _; rw [Bij.symm_graph_mem]; intro _; symm; apply coh; trivial
  · simp only [Bij.symm_graph, ←Mset.comp_map];
    congr; ext1 ⟨a, b⟩; rw [add_comm a b]; rfl

/-- `+` is commutative -/
private lemma add_comm' : P + Q ⊢ Q + P := by
  intro _ ⟨A, B, _, _, _⟩; exists B, A; and_intros; { trivial }; { trivial };
  apply radd_comm'; trivial

/-- `+` is commutative -/
instance RProp.instAddCommMagma : AddCommMagma (RProp ρ) where
  add_comm := by intro _ _; ext; constructor <;> apply add_comm'

/-- Construct `+ᴿᴹ` from a multiset of coherent pairs -/
lemma pairs_radd (S : Mset (ρ × ρ)) :
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
lemma radd_map {σ : Type*} (S : Mset σ) (f g : σ → ρ) {A B C : Mset ρ} :
    (∀ x ∈ S, f x ≎ g x) → f <$>ᴹ S = A → g <$>ᴹ S = B →
    (fun x ↦ f x + g x) <$>ᴹ S = C → A +ᴿᴹ B =ᴿᴹ C := by
  rintro coh rfl rfl rfl;
  have hcoh : ∀ a b, (a, b) ∈ (fun x ↦ (f x, g x)) <$>ᴹ S → a ≎ b := by
    intro a b mem; rw [Mset.map'_mem] at mem;
    rcases mem with ⟨x, memS, eq⟩; injection eq with ea eb; subst ea; subst eb;
    exact coh _ memS
  have h := pairs_radd _ hcoh;
  rw [←Mset.comp_map, ←Mset.comp_map, ←Mset.comp_map] at h; exact h

/-- `+ᴿᴹ` preserves inhabitedness -/
lemma radd_inhab : A +ᴿᴹ B =ᴿᴹ C → A.inhab → C.inhab := by
  rintro ⟨r, _, rfl⟩ inh; rw [Mset.inhab_map'];
  rw [←Mset.Bij.graph_fst r, Mset.inhab_map'] at inh; exact inh

/-- `+ᴿᴹ` transfers validity of the sum to the right-hand summand -/
lemma radd_valid_r : A +ᴿᴹ B =ᴿᴹ C → (∀ c ∈ C, ✓ c) → ∀ b ∈ B, ✓ b := by
  rintro ⟨r, coh, rfl⟩ val b elB;
  rw [←Mset.Bij.graph_snd r, Mset.map'_mem] at elB;
  rcases elB with ⟨⟨a, b'⟩, mem, rfl⟩;
  refine (PCMC.coher_valid _ _ (RR.radd_coher_r _ _ _ (RR.add_radd _ _ (coh _ _ mem)))).mpr ?_;
  apply val; rw [Mset.map'_mem]; exact ⟨_, mem, rfl⟩

/-- Pointwise consequences of `a ≎ b` and `a + b ≎ c` for associativity -/
private lemma add_pointwise {a b c : ρ} :
    a ≎ b → a + b ≎ c → b ≎ c ∧ a ≎ b + c ∧ (a + b) + c = a + (b + c) := by
  intro h₁ h₂;
  have hbc := PCMC.coher_trans _ _ _ (RR.radd_coher_r _ _ _ (RR.add_radd _ _ h₁)) h₂;
  exact ⟨hbc, PCMC.coher_trans _ _ _ h₁ (RR.radd_coher_l _ _ _ (RR.add_radd _ _ hbc)),
    RR.add_assoc _ _ _ h₁ hbc⟩

/-- `+ᴿᴹ` is associative -/
lemma radd_assoc_l :
    A +ᴿᴹ B =ᴿᴹ AB → AB +ᴿᴹ C =ᴿᴹ ABC → ∃ BC, B +ᴿᴹ C =ᴿᴹ BC ∧ A +ᴿᴹ BC =ᴿᴹ ABC := by
  rintro ⟨r₁, coh₁, rfl⟩ ⟨r₂, coh₂, rfl⟩;
  rcases Mset.Bij.graph_unmap_l (fun ((a, b) : ρ × ρ) ↦ a + b) r₂ with ⟨S, hfst, hsnd, hgr⟩;
  have pw : ∀ a b c, ((a, b), c) ∈ S → b ≎ c ∧ a ≎ b + c ∧ (a + b) + c = a + (b + c) := by
    intro a b c mem; apply add_pointwise;
    { apply coh₁; rw [←hfst, Mset.map'_mem]; exact ⟨((a, b), c), mem, rfl⟩ };
    { apply coh₂; rw [←hgr, Mset.map'_mem]; exact ⟨((a, b), c), mem, rfl⟩ }
  refine ⟨(fun ((a, b), c) ↦ b + c) <$>ᴹ S, ?_, ?_⟩
  · apply radd_map S (fun ((a, b), c) ↦ b) Prod.snd;
    · rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).1
    · rw [←Mset.Bij.graph_snd r₁, ←hfst, ←Mset.comp_map]; rfl
    · exact hsnd
    · rfl
  · apply radd_map S (fun ((a, b), c) ↦ a) (fun ((a, b), c) ↦ b + c);
    · rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).2.1
    · rw [←Mset.Bij.graph_fst r₁, ←hfst, ←Mset.comp_map]; rfl
    · rfl
    · rw [←hgr, ←Mset.comp_map]; apply Mset.map_congr;
      rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).2.2.symm

/-- `+` is associative -/
private lemma add_assoc' : (P + Q) + R ⊢ P + (Q + R) := by
  rintro D ⟨ABv, Cv, ⟨Av, Bv, elP, elQ, hAB⟩, elR, hABC⟩;
  rcases radd_assoc_l _ _ _ _ _ hAB hABC with ⟨BC, hBC, hA⟩;
  have inh : BC.inhab := radd_inhab _ _ _ hBC Bv.val.property;
  have val : ∀ b ∈ BC, ✓ b := radd_valid_r _ _ _ hA D.property;
  exists Av, ⟨⟨BC, inh⟩, val⟩; and_intros;
  { trivial }; { exists Bv, Cv }; { trivial }

/-- `+` is associative -/
instance RProp.instAddCommSemigroup : AddCommSemigroup (RProp ρ) where
  add_assoc := by
    intro P Q R; apply entails_antisymm; { apply add_assoc' };
    rw [add_comm P (Q + R), add_comm Q R, add_comm P Q, add_comm (Q + P) R];
    apply add_assoc'

end RBI
