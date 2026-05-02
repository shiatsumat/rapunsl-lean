module

public import Batteries.Tactic.Trans
public import Iris.BI
import Mathlib.Tactic.Lemma
import Iris.ProofMode
open Iris

@[expose] public section

/-! # Utility for `BI` -/

namespace BI
variable {PROP} [BI PROP] (P Q R : PROP)

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

end BI
