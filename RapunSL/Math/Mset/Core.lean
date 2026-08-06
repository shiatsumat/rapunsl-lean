module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Setoid.Basic

@[expose] public section

/-! # Multisets, possibly infinite -/

/-! ## `Ifam`: Indexed family -/

/-- Indexed family -/
structure Ifam (α : Type u) : Type (max 1 u) where
  protected dom : Type
  protected elem : dom → α

/-! ### Equivalence and setoid for `Ifam` -/

/-- Equivalence between indexed families -/
protected def Ifam.equiv (A B : Ifam α) : Prop :=
  ∃ f : A.dom ≃ B.dom, ∀ i, A.elem i = B.elem (f i)

/-- Utility for getting the inverse element equality -/
protected lemma Ifam.equiv_elem_eq_symm {A B : Ifam α} {f : A.dom ≃ B.dom} :
    (∀ i, A.elem i = B.elem (f i)) → ∀ j, B.elem j = A.elem (f.symm j) := by
  intro AB j; rw [AB, Equiv.apply_symm_apply]

/-- `Ifam.equiv` is an equivalence relation -/
protected lemma Ifam.equiv_is_equiv :
    Equivalence (α := Ifam α) Ifam.equiv where
  refl _ := by exists Equiv.refl _; intros; rfl
  symm := by
    intro _ _ ⟨f, AB⟩; exists f.symm; intro _; rw [AB, Equiv.apply_symm_apply]
  trans := by
    intro _ _ _ ⟨f, _⟩ ⟨g, _⟩; exists f.trans g; intro _; simp_all only [Equiv.trans_apply]

/-- Setoid for `Ifam` -/
protected instance Ifam.instSetoid α : Setoid (Ifam α) :=
  Setoid.mk (Ifam.equiv) Ifam.equiv_is_equiv

/-! ## `Mset`: Multiset, possibly infinite -/

/-- Multiset, possibly infinite -/
def Mset (α : Type u) : Type (max 1 u) :=
  Quotient (Ifam.instSetoid α)

/-! ## Utility for working with `out` on `Mset` -/

set_option linter.defProp false in
/-- `Quotient.out_eq` for `Mset` -/
protected def Mset.out_eq (A : Mset α) := Quotient.out_eq A

namespace Mset
/-- `simp_out_eq A A'` discharges `A.out_eq`, generalizing `A.out` to `A'` -/
scoped syntax "simp_out_eq" ident ident : tactic
/-- `simp_out_eq A` discharges `A.out_eq`, generalizing `A.out` -/
scoped syntax "simp_out_eq" ident : tactic
macro_rules
  | `(tactic| simp_out_eq $A $Ao) => `(tactic|
        generalize Mset.out_eq $A = eq; revert eq;
        generalize Quotient.out $A = $Ao; intro eq; subst eq; try simp only)
  | `(tactic| simp_out_eq $A) => `(tactic| simp_out_eq $A Ao)
end Mset

/-! ## Functor -/

/-- Functor map for `Ifam`, more universe-polymorphic than `Functor.map` -/
protected def Ifam.map {α β : Type*} (f : α → β) (A : Ifam α) : Ifam β :=
  .mk A.dom (fun i => f (A.elem i))

@[inherit_doc]
scoped[Ifam] infixr:100 " <$>ᴵ " => Ifam.map
open Ifam

/-- `Functor` for `Ifam` -/
protected instance Ifam.instFunctor : Functor Ifam where
  map := Ifam.map

/-- Unfold `<$>` into `<$>ᴵ` -/
protected lemma Ifam.map_unfold : Functor.map = Ifam.map (α := α) (β := β) := rfl

/-- `<$>ᴵ` preserves the identity -/
protected lemma Ifam.id_map (A : Ifam α) : id <$>ᴵ A = A := rfl

/-- `<$>ᴵ` respects function composition -/
protected lemma Ifam.comp_map (f : α → β) (g : β → γ) (A : Ifam α) :
    (g ∘ f) <$>ᴵ A = g <$>ᴵ (f <$>ᴵ A) := rfl

/-- `LawfulFunctor` for `Ifam` -/
protected instance Ifam.instLawfulFunctor : LawfulFunctor Ifam where
  id_map _ := rfl
  comp_map _ _ _ := rfl
  map_const := rfl

/-- The index domain of `<$>ᴵ` -/
@[simp] protected lemma Ifam.map_dom (f : α → β) (A : Ifam α) :
  (f <$>ᴵ A).dom = A.dom := rfl

/-- The elements of `<$>ᴵ` -/
@[simp] protected lemma Ifam.map_elem (f : α → β) (A : Ifam α) (i : A.dom) :
  (f <$>ᴵ A).elem i = f (A.elem i) := rfl

/-- `<$>ᴵ` respects `≈` -/
@[gcongr] protected lemma Ifam.map_proper (A B : Ifam α) :
    A ≈ B → f <$>ᴵ A ≈ f <$>ᴵ B := by
  intro ⟨g, AB⟩; exists g; simp only [Ifam.map_elem]; intro _; rw [AB]; rfl

/-- Functor map for `Mset`, more universe-polymorphic than `Functor.map` -/
protected def Mset.map {α β : Type*} (f : α → β) : Mset α → Mset β :=
  .lift (⟦ f <$>ᴵ · ⟧) <| by
    intros; apply Quotient.sound; gcongr

@[inherit_doc]
scoped[Mset] infixr:100 " <$>ᴹ " => Mset.map
open Mset

/-- `Functor` for `Mset` -/
protected instance Mset.instFunctor : Functor Mset where
  map := Mset.map

/-- Unfold `<$>` into `<$>ᴹ` -/
protected lemma Mset.map_unfold : Functor.map = Mset.map (α := α) (β := β) := rfl

/-- `<$>ᴹ` preserves the identity -/
protected lemma Mset.id_map (A : Mset α) : id <$>ᴹ A = A := by
  cases A using Quotient.ind; rfl

/-- `<$>ᴹ` respects function composition -/
protected lemma Mset.comp_map (f : α → β) (g : β → γ) (A : Mset α) :
    (g ∘ f) <$>ᴹ A = g <$>ᴹ (f <$>ᴹ A) := by
  cases A using Quotient.ind; rfl

/-- Functor laws for `Mset` -/
protected instance Mset.instLawfulFunctor : LawfulFunctor Mset where
  id_map := Mset.id_map
  comp_map := Mset.comp_map
  map_const := rfl

/-! ## Empty multiset -/

/-- Empty indexed family -/
protected instance Ifam.instEmptyCollection : EmptyCollection (Ifam α) where
  emptyCollection := .mk Empty nofun

/-- Unfold `∅` for `Ifam` -/
protected lemma Ifam.empty_unfold : (∅ : Ifam α) = .mk Empty nofun := rfl

/-- The index domain of `∅` -/
@[simp] protected lemma Ifam.empty_dom :
    (∅ : Ifam α).dom = Empty := rfl

/-- The index domain of `∅` is empty -/
protected instance Ifam.empty_dom_Empty : IsEmpty (∅ : Ifam α).dom := by
  apply Empty.instIsEmpty

/-- Empty multiset -/
protected instance Mset.instEmptyCollection : EmptyCollection (Mset α) where
  emptyCollection := ⟦ ∅ ⟧

/-- Unfold `∅` for `Mset` -/
protected lemma Mset.empty_unfold : (∅ : Mset α) = ⟦ ∅ ⟧ := rfl

/-! ### `map` over `∅` -/

/-- `<$>ᴵ` over `∅` is `∅` -/
protected lemma Ifam.empty_map (f : α → β) :
    f <$>ᴵ (∅ : Ifam α) = ∅ := by
  simp only [Ifam.map, Ifam.empty_unfold]; congr; ext1 _; nofun

/-- `<$>ᴹ` over `∅` is `∅` -/
protected lemma Mset.empty_map (f : α → β) :
    f <$>ᴹ (∅ : Mset α) = ∅ := by
  apply congr_arg (Quotient.mk _); apply Ifam.empty_map

/-! ## Singleton -/

/-- Singleton indexed family -/
protected instance Ifam.instPure : Pure Ifam where
  pure a := .mk Unit (fun _ => a)

/-- Unfold `pure` for `Ifam` -/
protected lemma Ifam.pure_unfold (a : α) :
    pure (f := Ifam) a = .mk Unit (fun _ => a) := rfl

/-- The index domain of `pure` -/
@[simp] protected lemma Ifam.pure_dom (a : α) :
    (pure (f := Ifam) a).dom = Unit := rfl

/-- The elements of `pure` -/
@[simp] protected lemma Ifam.pure_elem (a : α) u :
    (pure (f := Ifam) a).elem u = a := rfl

/-- Singleton multiset -/
protected instance Mset.instPure : Pure Mset where
  pure a := ⟦ pure a ⟧

/-- Unfold `pure` for `Mset` -/
protected lemma Mset.pure_unfold (a : α) :
    pure (f := Mset) a = ⟦ .mk Unit (fun _ => a) ⟧ := rfl

/-! ### `map` over `pure` -/

/-- `<$>ᴵ` over `pure` -/
protected lemma Ifam.pure_map' (f : α → β) (a : α) :
    f <$>ᴵ pure a = pure (f a) := rfl

/-- `<$>ᴹ` over `pure` -/
protected lemma Mset.pure_map' (f : α → β) (a : α) :
    f <$>ᴹ pure a = pure (f a) := rfl

/-- `<$>` over `pure` -/
protected lemma Mset.pure_map (f : α → β) (a : α) :
    f <$> pure (f := Mset) a = pure (f a) := by apply Mset.pure_map'

/-! ## Membership -/

/-- Membership for `Ifam` -/
protected instance Ifam.instMembership : Membership α (Ifam α) where
  mem A a := ∃ i, A.elem i = a

/-- Membership respects `≈`, one direction -/
protected lemma Ifam.mem_proper' (A B : Ifam α) :
    A ≈ B → a ∈ A → a ∈ B := by
  rintro ⟨f, AB⟩ ⟨i, Ai⟩; exists f i; rw [←AB]; trivial

/-- Membership respects `≈` -/
protected lemma Ifam.mem_proper (A B : Ifam α) :
    A ≈ B → (a ∈ A) = (a ∈ B) := by
  intro _; ext1; constructor <;> apply Ifam.mem_proper' <;> tauto

/-- Membership for `Mset` -/
protected instance Mset.instMembership : Membership α (Mset α) where
  mem A a := A.liftOn (a ∈ ·) Ifam.mem_proper

/-! ### Membership lemmas -/

/-- Membership for `.out` -/
@[simp] protected lemma Mset.out_mem (A : Mset α) a : a ∈ A.out ↔ a ∈ A := by
  cases A using Quotient.ind; apply iff_of_eq; apply Ifam.mem_proper; apply Quotient.mk_out

/-- Membership for `<$>ᴵ` -/
@[simp] protected lemma Ifam.map'_mem (f : α → β) (A : Ifam α) b :
    b ∈ f <$>ᴵ A ↔ ∃ a ∈ A, b = f a := by
  constructor;
  · intro ⟨i, eq⟩; subst eq; exists A.elem i; and_intros; { exists i }; { rfl }
  · intro ⟨a, ⟨i, eq⟩, eq'⟩; subst eq eq'; exists i

/-- Membership for `<$>ᴹ` -/
@[simp] protected lemma Mset.map'_mem (f : α → β) (A : Mset α) b :
    b ∈ f <$>ᴹ A ↔ ∃ a ∈ A, b = f a := by
  cases A using Quotient.ind; apply Ifam.map'_mem

/-- Membership for `<$>` -/
@[simp] protected lemma Mset.map_mem (f : α → β) (A : Mset α) b :
    b ∈ f <$> A ↔ ∃ a ∈ A, b = f a := by apply Mset.map'_mem

/-- `∅` has no members -/
@[simp] protected lemma Ifam.empty_mem (a : α) : a ∈ (∅ : Ifam α) ↔ False := by
  rw [iff_false]; nofun

/-- `∅` has no members -/
@[simp] protected lemma Mset.empty_mem (a : α) : a ∈ (∅ : Mset α) ↔ False := by
  apply Ifam.empty_mem

/-- Membership for `pure` -/
@[simp] protected lemma Ifam.pure_mem (a b : α) : a ∈ pure (f := Ifam) b ↔ a = b := by
  constructor; { intro ⟨(), eq⟩; rw [←eq]; rfl }; { intro rfl; exists () }

/-- Membership for `pure` -/
@[simp] protected lemma Mset.pure_mem (a b : α) : a ∈ pure (f := Mset) b ↔ a = b := by
  apply Ifam.pure_mem

/-! ## Inhabitedness -/

/-- Inhabitedness for `Mset` -/
protected def Mset.inhab (A : Mset α) : Prop := ∃ a, a ∈ A

/-! ### Inhabitedness lemmas -/

/-- `<$>ᴹ` preserves inhabitedness -/
@[simp] protected lemma Mset.inhab_map' (f : α → β) (A : Mset α) :
    (f <$>ᴹ A).inhab ↔ A.inhab := by
  simp only [Mset.inhab, Mset.map'_mem]; grind only

/-- `<$>` preserves inhabitedness -/
@[simp] protected lemma Mset.inhab_map (f : α → β) (A : Mset α) :
    (f <$> A).inhab ↔ A.inhab := by apply Mset.inhab_map'

/-- `∅` is not inhabited -/
@[simp] protected lemma Mset.inhab_empty : (∅ : Mset α).inhab ↔ False := by
  simp only [Mset.inhab, Mset.empty_mem]; grind only

/-- `pure` is inhabited -/
@[simp] protected lemma Mset.inhab_pure (a : α) : (pure a : Mset α).inhab ↔ True := by
  simp only [Mset.inhab, Mset.pure_mem]; grind only

/-! ### Inhabitedness is non-emptiness -/

/-- An indexed family with no members is equivalent to `∅` -/
protected lemma Ifam.no_elem_empty (A : Ifam α) :
    (∀ a, a ∉ A) → A ≈ ∅ := by
  intro noA;
  have noAdom : A.dom → False := by intro i; apply noA (A.elem i); tauto;
  exists ⟨fun i => (noAdom i).elim, nofun, by tauto, by tauto⟩; tauto

/-- A multiset is uninhabited iff it is `∅` -/
protected lemma Mset.not_inhab_empty (A : Mset α) :
    ¬ A.inhab ↔ A = ∅ := by
  constructor; swap; { intro rfl; rw [Mset.inhab_empty]; trivial };
  cases A using Quotient.ind; intro nin; apply Quotient.sound;
  apply Ifam.no_elem_empty; intro a _; apply nin; exists a

/-- A multiset is inhabited iff it is not `∅` -/
protected lemma Mset.not_empty_inhab (A : Mset α) :
    A ≠ ∅ ↔ A.inhab := by rw [Ne, ←Mset.not_inhab_empty, not_not]

/-! ## Pair membership -/

/-- Pair membership for `Ifam` -/
protected def Ifam.pairmem (A : Ifam α) (a b : α) : Prop :=
  ∃ i j, i ≠ j ∧ A.elem i = a ∧ A.elem j = b

/-- Pair membership respects `≈`, one direction -/
protected lemma Ifam.pairmem_proper' (A B : Ifam α) :
    A ≈ B → A.pairmem a b → B.pairmem a b := by
  rintro ⟨f, AB⟩ ⟨i, j, _, rfl, rfl⟩; exists f i, f j;
  constructor; swap; { simp only [AB]; trivial };
  grind only [EquivLike.apply_eq_iff_eq f]

/-- Pair membership respects `≈` -/
protected lemma Ifam.pairmem_proper (A B : Ifam α) :
    A ≈ B → A.pairmem a b = B.pairmem a b := by
  intro _; ext1; constructor <;> { apply Ifam.pairmem_proper'; tauto }

/-- Pair membership for `Mset` -/
protected def Mset.pairmem (A : Mset α) (a b : α) : Prop :=
  A.liftOn (·.pairmem a b) Ifam.pairmem_proper

/-! ### Pair membership lemmas -/

/-- Pair membership is symmetric -/
protected instance Mset.pairmem_instSymm (A : Mset α) : Std.Symm A.pairmem where
  symm := by
    cases A using Quotient.ind; rintro _ _ ⟨i, j, _, rfl, rfl⟩;
    exists j, i; constructor <;> tauto

/-- Pair membership is symmetric -/
@[symm] protected lemma Mset.pairmem_symm (A : Mset α) a b :
    A.pairmem a b → A.pairmem b a := by
  apply (Mset.pairmem_instSymm A).symm

/-- Pair membership implies membership -/
protected lemma Mset.pairmem_mem_l (A : Mset α) a b : A.pairmem a b → a ∈ A := by
  cases A using Quotient.ind; rintro ⟨i, _, _, rfl, _⟩; exists i

/-- Pair membership implies membership -/
protected lemma Mset.pairmem_mem_r (A : Mset α) a b : A.pairmem a b → b ∈ A := by
  intro mem; symm at mem; apply Mset.pairmem_mem_l; trivial

/-- Two members with distinct values form a pair membership -/
protected lemma Ifam.mem_ne_pairmem (A : Ifam α) a b :
    a ∈ A → b ∈ A → a ≠ b → A.pairmem a b := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ ne; exact ⟨i, j, by rintro rfl; exact ne rfl, rfl, rfl⟩

/-- Two members with distinct values form a pair membership -/
protected lemma Mset.mem_ne_pairmem (A : Mset α) a b :
    a ∈ A → b ∈ A → a ≠ b → A.pairmem a b := by
  cases A using Quotient.ind; apply Ifam.mem_ne_pairmem

/-- Pair membership for `.out` -/
@[simp] protected lemma Mset.out_pairmem (A : Mset α) a b :
    A.out.pairmem a b ↔ A.pairmem a b := by
  cases A using Quotient.ind; apply iff_of_eq; apply Ifam.pairmem_proper; apply Quotient.mk_out

/-- Pair membership for `<$>ᴵ` -/
@[simp] protected lemma Ifam.map'_pairmem (f : α → β) (A : Ifam α) b b' :
    (f <$>ᴵ A).pairmem b b' ↔ ∃ a a', A.pairmem a a' ∧ b = f a ∧ b' = f a' := by
  constructor;
  · rintro ⟨i, j, _, rfl, rfl⟩; exists A.elem i, A.elem j; constructor; { exists i, j }; trivial
  · rintro ⟨_, _, ⟨i, j, _, rfl, rfl⟩, rfl, rfl⟩; exists i, j

/-- Pair membership for `<$>ᴹ` -/
@[simp] protected lemma Mset.map'_pairmem (f : α → β) (A : Mset α) b b' :
    (f <$>ᴹ A).pairmem b b' ↔ ∃ a a', A.pairmem a a' ∧ b = f a ∧ b' = f a' := by
  cases A using Quotient.ind; apply Ifam.map'_pairmem

/-- Pair membership for `<$>` -/
@[simp] protected lemma Mset.map_pairmem (f : α → β) (A : Mset α) b b' :
    (f <$> A).pairmem b b' ↔ ∃ a a', A.pairmem a a' ∧ b = f a ∧ b' = f a' := by
  apply Mset.map'_pairmem

/-- `∅` has no pair membership -/
@[simp] protected lemma Ifam.empty_pairmem (a b : α) : (∅ : Ifam α).pairmem a b ↔ False := by
  simp only [iff_false]; nofun

/-- `∅` has no pair membership -/
@[simp] protected lemma Mset.empty_pairmem a b : (∅ : Mset α).pairmem a b ↔ False := by
  apply Ifam.empty_pairmem

/-- `pure` has no pair membership -/
@[simp] protected lemma Ifam.pure_pairmem a b c : (pure a : Ifam α).pairmem b c ↔ False := by
  simp only [iff_false]; nofun

/-- `pure` has no pair membership -/
@[simp] protected lemma Mset.pure_pairmem a b c : (pure a : Mset α).pairmem b c ↔ False := by
  apply Ifam.pure_pairmem
