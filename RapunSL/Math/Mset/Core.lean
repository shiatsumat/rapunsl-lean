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

protected lemma Ifam.map_unfold : Functor.map = Ifam.map (α := α) (β := β) := rfl

protected lemma Ifam.id_map (A : Ifam α) : id <$>ᴵ A = A := by rfl

protected lemma Ifam.comp_map (f : α → β) (g : β → γ) (A : Ifam α) :
    (g ∘ f) <$>ᴵ A = g <$>ᴵ (f <$>ᴵ A) := by rfl

/-- `LawfulFunctor` for `Ifam` -/
protected instance Ifam.instLawfulFunctor : LawfulFunctor Ifam where
  id_map _ := rfl
  comp_map _ _ _ := rfl
  map_const := rfl

@[simp] protected lemma Ifam.map_dom (f : α → β) (A : Ifam α) :
  (f <$>ᴵ A).dom = A.dom := rfl

@[simp] protected lemma Ifam.map_elem (f : α → β) (A : Ifam α) (i : A.dom) :
  (f <$>ᴵ A).elem i = f (A.elem i) := rfl

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

protected lemma Mset.map_unfold : Functor.map = Mset.map (α := α) (β := β) := rfl

protected lemma Mset.id_map (A : Mset α) : id <$>ᴹ A = A := by
  cases A using Quotient.ind; rfl

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

protected lemma Ifam.empty_unfold : (∅ : Ifam α) = .mk Empty nofun := rfl

@[simp] protected lemma Ifam.empty_dom :
    (∅ : Ifam α).dom = Empty := rfl

protected instance Ifam.empty_dom_Empty : IsEmpty (∅ : Ifam α).dom := by
  apply Empty.instIsEmpty

/-- Empty multiset -/
protected instance Mset.instEmptyCollection : EmptyCollection (Mset α) where
  emptyCollection := ⟦ ∅ ⟧

protected lemma Mset.empty_unfold : (∅ : Mset α) = ⟦ ∅ ⟧ := rfl

/-! ### `map` over `∅` -/

protected lemma Ifam.empty_map (f : α → β) :
    f <$>ᴵ (∅ : Ifam α) = ∅ := by
  simp only [Ifam.map, Ifam.empty_unfold]; congr; ext1 _; nofun

protected lemma Mset.empty_map (f : α → β) :
    f <$>ᴹ (∅ : Mset α) = ∅ := by
  apply (congr_arg (Quotient.mk _)); apply Ifam.empty_map

/-! ## Singleton -/

/-- Singleton indexed family -/
protected instance Ifam.instPure : Pure Ifam where
  pure a := .mk Unit (fun _ => a)

protected lemma Ifam.pure_unfold (a : α) :
    pure (f := Ifam) a = .mk Unit (fun _ => a) := rfl

@[simp] protected lemma Ifam.pure_dom (a : α) :
    (pure (f := Ifam) a).dom = Unit := rfl

@[simp] protected lemma Ifam.pure_elem (a : α) u :
    (pure (f := Ifam) a).elem u = a := rfl

/-- Singleton multiset -/
protected instance Mset.instPure : Pure Mset where
  pure a := ⟦ pure a ⟧

protected lemma Mset.pure_unfold (a : α) :
    pure (f := Mset) a = ⟦ .mk Unit (fun _ => a) ⟧ := rfl

/-! ### `map` over `pure` -/

protected lemma Ifam.pure_map' (f : α → β) (a : α) :
    f <$>ᴵ pure a = pure (f a) := rfl

protected lemma Mset.pure_map' (f : α → β) (a : α) :
    f <$>ᴹ pure a = pure (f a) := rfl

protected lemma Mset.pure_map (f : α → β) (a : α) :
    f <$> pure (f := Mset) a = pure (f a) := by apply Mset.pure_map'

/-! ## Membership -/

/-- Membership for `Ifam` -/
protected instance Ifam.instMembership : Membership α (Ifam α) where
  mem A a := ∃ i, A.elem i = a

protected lemma Ifam.mem_proper' (A B : Ifam α) :
    A ≈ B → a ∈ A → a ∈ B := by
  rintro ⟨f, AB⟩ ⟨i, Ai⟩; exists f i; rw [←AB]; trivial

protected lemma Ifam.mem_proper (A B : Ifam α) :
    A ≈ B → (a ∈ A) = (a ∈ B) := by
  intro _; ext1; constructor <;> apply Ifam.mem_proper' <;> tauto

/-- Membership for `Mset` -/
protected instance Mset.instMembership : Membership α (Mset α) where
  mem A a := A.liftOn (a ∈ ·) <| Ifam.mem_proper

/-! ### Membership lemmas -/

@[simp] protected lemma Mset.mem_out (A : Mset α) a : (a ∈ A.out) = (a ∈ A) := by
  cases A using Quotient.ind; apply Ifam.mem_proper; apply Quotient.mk_out

@[simp] protected lemma Ifam.mem_map' (f : α → β) (A : Ifam α) b :
    (b ∈ f <$>ᴵ A) = ∃ a ∈ A, f a = b := by
  ext1; constructor;
  · intro ⟨i, eq⟩; subst eq; exists A.elem i; and_intros; { exists i }; { rfl }
  · intro ⟨a, ⟨i, eq⟩, eq'⟩; subst eq eq'; exists i

@[simp] protected lemma Mset.mem_map' (f : α → β) (A : Mset α) b :
    (b ∈ f <$>ᴹ A) = ∃ a ∈ A, f a = b := by
  cases A using Quotient.ind; apply Ifam.mem_map'

@[simp] protected lemma Mset.mem_map (f : α → β) (A : Mset α) b :
    (b ∈ f <$> A) = ∃ a ∈ A, f a = b := by apply Mset.mem_map'

@[simp] protected lemma Ifam.mem_empty (a : α) : (a ∈ (∅ : Ifam α)) = False := by
  rw [eq_iff_iff, iff_false]; nofun

@[simp] protected lemma Mset.mem_empty (a : α) : (a ∈ (∅ : Mset α)) = False := by
  apply Ifam.mem_empty

@[simp] protected lemma Ifam.mem_pure (a b : α) : (a ∈ pure (f := Ifam) b) = (a = b) := by
  ext1; constructor;
  { intro ⟨(), eq⟩; rw [←eq]; rfl }; { intro rfl; exists () }

@[simp] protected lemma Mset.mem_pure (a b : α) : (a ∈ pure (f := Mset) b) = (a = b) := by
  apply Ifam.mem_pure

/-! ## Inhabitedness -/

/-- Inhabitedness for `Mset` -/
protected def Mset.inhab (A : Mset α) : Prop := ∃ a, a ∈ A

/-! ### Inhabitedness lemmas -/

@[simp] protected lemma Mset.inhab_map' (f : α → β) (A : Mset α) :
    (f <$>ᴹ A).inhab = A.inhab := by
  simp only [Mset.inhab, Mset.mem_map']; grind only

@[simp] protected lemma Mset.inhab_map (f : α → β) (A : Mset α) :
    (f <$> A).inhab = A.inhab := by apply Mset.inhab_map'

@[simp] protected lemma Mset.inhab_empty : (∅ : Mset α).inhab = False := by
  simp only [Mset.inhab, Mset.mem_empty]; grind only

@[simp] protected lemma Mset.inhab_pure (a : α) : (pure a : Mset α).inhab = True := by
  simp only [Mset.inhab, Mset.mem_pure]; grind only

/-! ### Inhabitedness is non-emptiness -/

protected lemma Ifam.no_elem_empty (A : Ifam α) :
    (∀ a, a ∉ A) → A ≈ ∅ := by
  intro noA;
  have noAdom : A.dom → False := by intro i; apply noA (A.elem i); tauto;
  exists ⟨fun i => (noAdom i).elim, nofun, by tauto, by tauto⟩; tauto

protected lemma Mset.not_inhab_empty (A : Mset α) :
    (¬ A.inhab) = (A = ∅) := by
  ext1; constructor; swap; { intro rfl; rw [Mset.inhab_empty]; trivial };
  cases A using Quotient.ind; intro nin; apply Quotient.sound;
  apply Ifam.no_elem_empty; intro a _; apply nin; exists a

protected lemma Mset.not_empty_inhab (A : Mset α) :
    (A ≠ ∅) = A.inhab := by rw [Ne, ←Mset.not_inhab_empty, not_not]
