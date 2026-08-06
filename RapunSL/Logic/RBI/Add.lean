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
lemma pairs_radd (T : Mset (ρ × ρ)) :
    (∀ a b, (a, b) ∈ T → a ≎ b) →
    (Prod.fst <$>ᴹ T) +ᴿᴹ (Prod.snd <$>ᴹ T) =ᴿᴹ (fun (a, b) ↦ a + b) <$>ᴹ T := by
  intro coh;
  have hg : ((Mset.Bij.map_l Prod.fst T).trans (Mset.Bij.map_r Prod.snd T)).graph = T := by
    rw [Mset.Bij.trans_graph_map_l (Mset.Bij.map_l Prod.fst T) (Mset.Bij.map_r Prod.snd T)
      Prod.fst (by intro _ _ mem; rw [Mset.Bij.map_l_graph_mem] at mem; exact mem.1)];
    rw [Mset.Bij.map_r_graph, ←Mset.comp_map]; exact Mset.id_map T
  exists (Mset.Bij.map_l Prod.fst T).trans (Mset.Bij.map_r Prod.snd T); and_intros;
  { rw [hg]; exact coh }; { rw [hg] }

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
  rcases RR.radd_assoc_l _ _ _ _ _ (RR.add_radd _ _ h₁) (RR.add_radd _ _ h₂)
    with ⟨bc, e₃, e₄⟩;
  have hbc := RR.radd_coher _ _ _ e₃;
  rcases RR.radd_add _ _ _ hbc e₃ with rfl;
  have habc := RR.radd_coher _ _ _ e₄;
  exact ⟨hbc, habc, (RR.radd_add _ _ _ habc e₄).symm⟩

/-- `+ᴿᴹ` is associative -/
lemma radd_assoc_l :
    A +ᴿᴹ B =ᴿᴹ AB → AB +ᴿᴹ C =ᴿᴹ ABC → ∃ BC, B +ᴿᴹ C =ᴿᴹ BC ∧ A +ᴿᴹ BC =ᴿᴹ ABC := by
  rintro ⟨r₁, coh₁, rfl⟩ ⟨r₂, coh₂, rfl⟩;
  rcases Mset.Bij.graph_unmap_l (fun ((a, b) : ρ × ρ) ↦ a + b) r₂ with ⟨S, hfst, hsnd, hgr⟩;
  have mem_S : ∀ a b c, ((a, b), c) ∈ S → a ≎ b ∧ a + b ≎ c := by
    intro a b c mem; and_intros;
    { apply coh₁; rw [←hfst, Mset.map'_mem]; exact ⟨((a, b), c), mem, rfl⟩ };
    { apply coh₂; rw [←hgr, Mset.map'_mem]; exact ⟨((a, b), c), mem, rfl⟩ }
  refine ⟨(fun ((a, b), c) ↦ b + c) <$>ᴹ S, ?_, ?_⟩
  · have e₁ : Prod.fst <$>ᴹ ((fun ((a, b), c) ↦ (b, c)) <$>ᴹ S) = B := by
      rw [←Mset.comp_map, ←Mset.Bij.graph_snd r₁, ←hfst, ←Mset.comp_map]; rfl
    have e₂ : Prod.snd <$>ᴹ ((fun ((a, b), c) ↦ (b, c)) <$>ᴹ S) = C := by
      rw [←Mset.comp_map, ←hsnd]; rfl
    have e₃ : (fun (b, c) ↦ b + c) <$>ᴹ ((fun ((a, b), c) ↦ (b, c)) <$>ᴹ S) =
        (fun ((a, b), c) ↦ b + c) <$>ᴹ S := by
      rw [←Mset.comp_map]; rfl
    rw [←e₁, ←e₂, ←e₃]; apply pairs_radd;
    rintro b c mem; rw [Mset.map'_mem] at mem;
    rcases mem with ⟨⟨⟨a, b'⟩, c'⟩, memS, eq⟩;
    injection eq with eb ec; subst eb; subst ec;
    exact (add_pointwise (mem_S _ _ _ memS).1 (mem_S _ _ _ memS).2).1
  · have e₄ : Prod.fst <$>ᴹ ((fun ((a, b), c) ↦ (a, b + c)) <$>ᴹ S) = A := by
      rw [←Mset.comp_map, ←Mset.Bij.graph_fst r₁, ←hfst, ←Mset.comp_map]; rfl
    have e₅ : Prod.snd <$>ᴹ ((fun ((a, b), c) ↦ (a, b + c)) <$>ᴹ S) =
        (fun ((a, b), c) ↦ b + c) <$>ᴹ S := by
      rw [←Mset.comp_map]; rfl
    have e₆ : (fun (a, b) ↦ a + b) <$>ᴹ ((fun ((a, b), c) ↦ (a, b + c)) <$>ᴹ S) =
        (fun x ↦ x.1 + x.2) <$>ᴹ r₂.graph := by
      rw [←hgr, ←Mset.comp_map, ←Mset.comp_map]; apply Mset.map_congr;
      rintro ⟨⟨a, b⟩, c⟩ memS;
      exact ((add_pointwise (mem_S _ _ _ memS).1 (mem_S _ _ _ memS).2).2.2).symm
    rw (occs := [1]) [←e₄]; rw [←e₅, ←e₆]; apply pairs_radd;
    rintro x y mem; rw [Mset.map'_mem] at mem;
    rcases mem with ⟨⟨⟨a, b⟩, c⟩, memS, eq⟩;
    injection eq with ex ey; subst ex; subst ey;
    exact (add_pointwise (mem_S _ _ _ memS).1 (mem_S _ _ _ memS).2).2.1

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
