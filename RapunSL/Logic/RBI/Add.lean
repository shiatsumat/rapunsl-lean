module

public import RapunSL.Logic.RBI.Core
open Iris BI RBI Mset Mseti PCMC RR

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
    C = (fun (a, b) ↦ a + b) <$> AB.graph

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
  · simp only [Bij.symm_graph, Mset.map_unfold, ←Mset.comp_map];
    congr; ext1 ⟨a, b⟩; rw [add_comm a b]; rfl

/-- `+` is commutative -/
private lemma add_comm' : P + Q ⊢ Q + P := by
  intro _ ⟨A, B, _, _, _⟩; exists B, A; and_intros; { trivial }; { trivial };
  apply radd_comm'; trivial

/-- `+` is commutative -/
instance RProp.instAddCommMagma : AddCommMagma (RProp ρ) where
  add_comm := by intro _ _; ext; constructor <;> apply add_comm'

end RBI
