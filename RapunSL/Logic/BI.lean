module

public import Batteries.Tactic.Trans
public import Mathlib.Tactic.Gcongr
public import Iris.BI
import Mathlib.Tactic.Lemma
import Iris.ProofMode
open Iris BI

@[expose] public section

/-! # Utility for `BI` -/

namespace BI
variable {PROP} [BI PROP] (P Q R S : PROP)

@[refl] lemma entails_refl : P ⊢ P := by
  apply Std.refl

@[trans] lemma entails_trans : (P ⊢ Q) → (Q ⊢ R) → P ⊢ R := by
  apply Std.trans

@[refl] lemma bi_entails_refl : P ⊣⊢ P := by
  constructor <;> rfl

@[symm] lemma bi_entails_symm : P ⊣⊢ Q → Q ⊣⊢ P := by
  intro ⟨_, _⟩; constructor <;> trivial

@[trans] lemma bi_entails_trans : P ⊣⊢ Q → Q ⊣⊢ R → P ⊣⊢ R := by
  intro ⟨_, _⟩ ⟨_, _⟩; constructor <;> trans <;> assumption

lemma or_exists : P ∨ Q ⊣⊢ ∃ b : Bool, if b then P else Q := by
  constructor;
  · iintro (_ | _); { iexists true; trivial }; { iexists false; trivial }
  · iintro ⟨%b, _⟩; cases b; { iright; trivial }; { ileft; trivial }

lemma false_exists :
    False ⊣⊢@{PROP} ∃ e : Empty, nomatch e := by
  constructor; { iintro %_; trivial }; { iintro ⟨%_, _⟩; trivial }

/-! ## `gcongr` lemmas -/

@[gcongr] lemma and_mono' : (P ⊢ Q) → (R ⊢ S) → P ∧ R ⊢ Q ∧ S := by
  apply and_mono

@[gcongr] lemma or_mono' : (P ⊢ Q) → (R ⊢ S) → P ∨ R ⊢ Q ∨ S := by
  apply or_mono

@[gcongr] lemma imp_mono' : (Q ⊢ P) → (R ⊢ S) → (P → R) ⊢ (Q → S) := by
  apply imp_mono

@[gcongr] lemma forall_mono' {α : Sort*} (P Q : α → PROP) :
    (∀ a, P a ⊢ Q a) → (∀ a, P a) ⊢ (∀ a, Q a) := by
  apply forall_mono

@[gcongr] lemma exists_mono' {α : Sort*} (P Q : α → PROP) :
    (∀ a, P a ⊢ Q a) → (∃ a, P a) ⊢ (∃ a, Q a) := by
  apply exists_mono

@[gcongr] lemma sep_mono' : (P ⊢ Q) → (R ⊢ S) → P ∗ R ⊢ Q ∗ S := by
  apply sep_mono

@[gcongr] lemma wand_mono' : (Q ⊢ P) → (R ⊢ S) → (P -∗ R) ⊢ Q -∗ S := by
  apply wand_mono

@[gcongr] lemma persistently_mono' : (P ⊢ Q) → <pers> P ⊢ <pers> Q := by
  apply persistently_mono

@[gcongr] lemma later_mono' : (P ⊢ Q) → ▷ P ⊢ ▷ Q := by
  apply later_mono

end BI
