module

public import Iris.BI
public import Mathlib.Order.Defs.Unbundled
import Batteries.Tactic.Trans
import Mathlib.Tactic.GCongr
import Iris.ProofMode
open Iris BI

@[expose] public section

/-! # Utility for `BI` -/

namespace Iris.BI
variable {PROP} [BI PROP] (P Q R S : PROP)

/-! ## `⊢` is a preorder -/

attribute [refl] entails_refl
attribute [trans] entails_trans

instance entails_instPreorder : IsPreorder PROP Entails where
  refl := by intro _; rfl

/-! ## `⊣⊢` is an equivalence relation -/

attribute [refl] BIBase.BiEntails.rfl
attribute [symm] BIBase.BiEntails.symm
attribute [trans] BIBase.BiEntails.trans

instance bi_entails_instIsEquiv : IsEquiv PROP BiEntails where
  refl := by intro _; rfl
  symm := by intro _ _ _; symm; trivial
  trans := by intro _ _ _ _ _; trans <;> assumption

/-! ## Reinterpretation of connectives -/

lemma or_as_exists : P ∨ Q ⊣⊢ ∃ b : Bool, if b then P else Q := by
  constructor;
  · iintro (_ | _);
    { iexists true; simp only [reduceIte]; itrivial };
    { iexists false; simp only [Bool.false_eq_true, reduceIte]; itrivial }
  · iintro ⟨%b, _⟩; cases b <;> simp only [Bool.false_eq_true, reduceIte];
    { iright; itrivial }; { ileft; itrivial }

lemma false_as_exists :
    False ⊣⊢@{PROP} ∃ e : Empty, nomatch e := by
  constructor; { iintro %_; trivial }; { iintro ⟨%_, _⟩; trivial }

/-! ## `gcongr` lemmas -/

attribute [gcongr] and_mono or_mono imp_mono forall_mono exists_mono sep_mono wand_mono
  persistently_mono later_mono

end Iris.BI

/-! ## BI with extensionality -/

class Iris.BIE PROP extends Iris.BI PROP where
  bi_ext : ∀ P Q : PROP, (P ⊣⊢ Q) → P = Q

attribute [ext] Iris.BIE.bi_ext

macro:25 P:term:29 " =ᴮᴵ " Q:term:29 : term => `(Eq iprop($P) iprop($Q))

namespace Iris.BI
variable {PROP} [BIE PROP] (P Q : PROP)

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
