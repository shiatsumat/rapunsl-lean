module

public import Iris.BI
public import Mathlib.Order.Defs.Unbundled
import Batteries.Tactic.Trans
import Mathlib.Tactic.Gcongr
import Iris.ProofMode
open Iris BI

@[expose] public section

/-! # Utility for `BI` -/

namespace Iris.BI
variable {PROP} [BI PROP] (P Q R S : PROP)

/-! ## `⊢` is a preorder -/

@[refl] lemma entails_refl : P ⊢ P := by
  apply Std.refl

@[trans] lemma entails_trans' : (P ⊢ Q) → (Q ⊢ R) → P ⊢ R := by
  apply Trans.trans

instance entails_instPreorder : IsPreorder PROP Entails where
  refl := entails_refl

/-! ## `⊣⊢` is an equivalence relation -/

@[refl] lemma bi_entails_refl : P ⊣⊢ P := by
  constructor <;> rfl

@[symm] lemma bi_entails_symm : P ⊣⊢ Q → Q ⊣⊢ P := by
  intro ⟨_, _⟩; constructor <;> trivial

@[trans] lemma bi_entails_trans : P ⊣⊢ Q → Q ⊣⊢ R → P ⊣⊢ R := by
  apply Trans.trans

instance bi_entails_instIsEquiv : IsEquiv PROP BiEntails where
  refl := bi_entails_refl
  symm := bi_entails_symm
  trans := bi_entails_trans

/-! ## Reinterpretation of connectives -/

lemma or_as_exists : P ∨ Q ⊣⊢ ∃ b : Bool, if b then P else Q := by
  constructor;
  · iintro (_ | _); { iexists true; trivial }; { iexists false; trivial }
  · iintro ⟨%b, _⟩; cases b; { iright; trivial }; { ileft; trivial }

lemma false_as_exists :
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

end Iris.BI

/-! ## BI with extensionality -/

class Iris.BIE PROP extends Iris.BI PROP where
  bi_ext : ∀ P Q : PROP, (P ⊣⊢ Q) → P = Q

macro:25 P:term:29 " =ᴮᴵ " Q:term:29 : term => `(Eq iprop($P) iprop($Q))

namespace Iris.BI

variable {PROP} [BIE PROP] (P Q : PROP)

@[ext]
lemma bi_ext : (P ⊣⊢ Q) → P = Q := by apply Iris.BIE.bi_ext

lemma or_as_exists' : P ∨ Q =ᴮᴵ ∃ b : Bool, if b then P else Q := by
  ext1; apply or_as_exists

lemma false_as_exists' : (False : PROP) =ᴮᴵ ∃ e : Empty, nomatch e := by
  ext1; apply false_as_exists

lemma sep_comm' : P ∗ Q =ᴮᴵ Q ∗ P := by
  ext1; apply sep_comm

lemma and_comm' : P ∧ Q =ᴮᴵ Q ∧ P := by
  ext1; apply and_comm

lemma and_assoc' : (P ∧ Q) ∧ R =ᴮᴵ P ∧ (Q ∧ R) := by
  ext1; apply and_assoc

end Iris.BI
