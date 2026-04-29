module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Control.Applicative

@[expose] public section

/-! # Multisets, possibly infinite -/

/-! ## `Ifam`: Indexed family -/

/-- Indexed family -/
structure Ifam.{u} (α : Type u) : Type (max 1 u) where
  protected dom : Type
  protected elem : dom → α

/-! ### Equivalence and setoid for `Ifam` -/

/-- Equivalence between indexed families -/
protected def Ifam.equiv.{u} (A B : Ifam.{u} α) : Prop :=
  ∃ f : A.dom ≃ B.dom, ∀ i, A.elem i = B.elem (f i)

/-- Utility for getting the inverse element equality -/
protected lemma Ifam.equiv_elem_eq_symm {A B : Ifam α} {f : A.dom ≃ B.dom} :
    (∀ i, A.elem i = B.elem (f i)) → ∀ j, B.elem j = A.elem (f.symm j) := by
  intro AB j; rw [AB, Equiv.apply_symm_apply]

protected lemma Ifam.equiv_is_equiv :
    Equivalence (α := Ifam.{u} α) Ifam.equiv where
  refl _ := by exists Equiv.refl _; intros; rfl
  symm := by
    intro _ _ ⟨f, AB⟩; exists f.symm; intro _; rw [AB, Equiv.apply_symm_apply]
  trans := by
    intro _ _ _ ⟨f, _⟩ ⟨g, _⟩; exists f.trans g; intro _; simp_all only [Equiv.trans_apply]

/-- Setoid for `Ifam` -/
protected instance Ifam.instSetoid.{u} α : Setoid (Ifam α) :=
  Setoid.mk (Ifam.equiv.{u}) Ifam.equiv_is_equiv

/-! ## `Mset`: Multiset, possibly infinite -/

/-- Multiset, possibly infinite -/
def Mset.{u} (α : Type u) : Type (max 1 u) :=
  Quotient (Ifam.instSetoid.{u} α)

/-! ## Functor -/

/-- Functor map for `Ifam`, more universe-polymorphic than `Functor.map` -/
protected def Ifam.map {α β : Type*} (f : α → β) (A : Ifam α) : Ifam β :=
  .mk A.dom (fun i => f (A.elem i))

scoped[Ifam] infixr:100 " <$>ᴵ " => Ifam.map
open Ifam

/-- `Functor` for `Ifam` -/
protected instance Ifam.instFunctor : Functor Ifam.{u} where
  map := Ifam.map

protected lemma Ifam.map_unfold : Functor.map = Ifam.map (α := α) (β := β) := rfl

protected lemma Ifam.id_map (A : Ifam α) : id <$>ᴵ A = A := by rfl

protected lemma Ifam.comp_map (f : α → β) (g : β → γ) (A : Ifam α) :
    (g ∘ f) <$>ᴵ A = g <$>ᴵ (f <$>ᴵ A) := by rfl

/-- `LawfulFunctor` for `Ifam` -/
protected instance Ifam.instLawfulFunctor : LawfulFunctor Ifam.{u} where
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

scoped[Mset] infixr:100 " <$>ᴹ " => Mset.map
open Mset

/-- `Functor` for `Mset` -/
protected instance Mset.instFunctor : Functor Mset.{u} where
  map := Mset.map

protected lemma Mset.map_unfold : Functor.map = Mset.map (α := α) (β := β) := rfl

protected lemma Mset.id_map (A : Mset α) : id <$>ᴹ A = A := by
  cases A using Quotient.ind; rfl

protected lemma Mset.comp_map (f : α → β) (g : β → γ) (A : Mset α) :
    (g ∘ f) <$>ᴹ A = g <$>ᴹ (f <$>ᴹ A) := by
  cases A using Quotient.ind; rfl

/-- Functor laws for `Mset` -/
protected instance Mset.instLawfulFunctor : LawfulFunctor Mset.{u} where
  id_map := Mset.id_map
  comp_map := Mset.comp_map
  map_const := rfl

/-! ## Empty multiset -/

/-- Empty indexed family -/
protected instance Ifam.instEmptyCollection : EmptyCollection (Ifam α) where
  emptyCollection := .mk Empty nofun

@[simp] protected lemma Ifam.empty_dom :
    (∅ : Ifam α).dom = Empty := rfl

protected instance Ifam.empty_dom_Empty : IsEmpty (∅ : Ifam α).dom := by
  apply Empty.instIsEmpty

/-- Empty multiset -/
protected instance Mset.instEmptyCollection : EmptyCollection (Mset α) where
  emptyCollection := ⟦ ∅ ⟧

/-! ## Singleton -/

/-- Singleton indexed family -/
protected instance Ifam.instPure : Pure Ifam.{u} where
  pure a := .mk Unit (fun _ => a)

protected lemma Ifam.pure_unfold (a : α) :
    pure (f := Ifam) a = .mk Unit (fun _ => a) := rfl

@[simp] protected lemma Ifam.pure_dom (a : α) :
    (pure (f := Ifam) a).dom = Unit := rfl

@[simp] protected lemma Ifam.pure_elem (a : α) u :
    (pure (f := Ifam) a).elem u = a := rfl

/-- Singleton multiset -/
protected instance Mset.instPure : Pure Mset.{u} where
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

/-! ## Binary sum -/

/-- Sum of two indexed families -/
protected def Ifam.oplus {α} (A B : Ifam α) : Ifam α :=
  .mk (A.dom ⊕ B.dom) (fun s => s.casesOn A.elem B.elem)

scoped[Ifam] infixr:60 " ⊕ᴵ " => Ifam.oplus

@[simp] protected lemma Ifam.oplus_dom (A B : Ifam α) :
  (A ⊕ᴵ B).dom = (A.dom ⊕ B.dom) := rfl

@[simp] protected lemma Ifam.oplus_elem_inl (A B : Ifam α) {i} :
  (A ⊕ᴵ B).elem (.inl i) = A.elem i := rfl

@[simp] protected lemma Ifam.oplus_elem_inr (A B : Ifam α) {i} :
  (A ⊕ᴵ B).elem (.inr i) = B.elem i := rfl

@[gcongr] protected lemma Ifam.oplus_proper (A A' B B' : Ifam α) :
    A ≈ A' → B ≈ B' → A ⊕ᴵ B ≈ A' ⊕ᴵ B' :=
  fun ⟨f, AB⟩ ⟨g, A'B'⟩ => by
    exists Equiv.sumCongr f g; simp only [Ifam.oplus_dom];
    rintro (_ | _) <;> simp_all only [Ifam.oplus_elem_inl, Ifam.oplus_elem_inr] <;> rfl

/-- Sum of two multisets -/
protected def Mset.oplus.{u} {α} : Mset.{u} α → Mset.{u} α → Mset α :=
  .lift₂ (⟦ · ⊕ᴵ · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.oplus_proper <;> tauto

scoped[Mset] infixr:60 " ⊕ᴹ " => Mset.oplus

/-! ### `map` over `⊕` -/

protected lemma Ifam.oplus_map' (f : α → β) (A B : Ifam α) :
    f <$>ᴵ (A ⊕ᴵ B) ≈ f <$>ᴵ A ⊕ᴵ f <$>ᴵ B := by
  exists Equiv.refl _; rintro (_ | _) <;> rfl

protected lemma Mset.oplus_map' (f : α → β) (A B : Mset α) :
    f <$>ᴹ (A ⊕ᴹ B) = f <$>ᴹ A ⊕ᴹ f <$>ᴹ B := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.oplus_map'

protected lemma Mset.oplus_map (f : α → β) (A B : Mset α) :
    f <$> (A ⊕ᴹ B) = f <$> A ⊕ᴹ f <$> B := by apply Mset.oplus_map'

/-! ### `⊕` is commutative -/

protected lemma Ifam.oplus_comm (A B : Ifam α) : A ⊕ᴵ B ≈ B ⊕ᴵ A := by
  exists Equiv.sumComm _ _; rintro (_ | _) <;> rfl

protected instance Mset.oplus_Commutative :
    Std.Commutative (Mset.oplus (α := α)) where
  comm A B := by
    cases A using Quotient.ind; cases B using Quotient.ind;
    apply Quotient.sound; apply Ifam.oplus_comm

/-! ### `⊕` is unital -/

protected lemma Ifam.oplus_id_r (A : Ifam α) : A ⊕ᴵ ∅ ≈ A := by
  exists Equiv.sumEmpty _ _; rintro (_ | _) <;> tauto

protected instance Mset.oplus_LawfulCommIdentity :
    Std.LawfulCommIdentity (Mset.oplus (α := α)) ∅ where
  right_id A := by
    cases A using Quotient.ind; apply Quotient.sound; apply Ifam.oplus_id_r

/-! ### `⊕` is assoc -/

protected lemma Ifam.oplus_assoc (A B C : Ifam α) : (A ⊕ᴵ B) ⊕ᴵ C ≈ A ⊕ᴵ (B ⊕ᴵ C) := by
  exists Equiv.sumAssoc _ _ _; rintro ((_ | _) | _) <;> rfl

protected instance Mset.oplus_Associative :
    Std.Associative (Mset.oplus (α := α)) where
  assoc A B C := by
    cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
    apply Quotient.sound; apply Ifam.oplus_assoc

/-! ## Big sum -/

/-- Big sum of indexed families -/
protected def Ifam.bigoplus {ι : Type} (A : ι → Ifam α) : Ifam α :=
  .mk (Σ i, (A i).dom) (fun ⟨i, j⟩ => (A i).elem j)

scoped[Ifam] notation "⨁ᴵ " i ", " A => Ifam.bigoplus (fun i => A)

@[gcongr] protected lemma Ifam.bigoplus_proper (A A' : ι → Ifam α) :
    (∀ i, A i ≈ A' i) → Ifam.bigoplus A ≈ Ifam.bigoplus A' := by
  intro AA'; have ⟨f, AA'⟩ := Classical.skolem.mp AA';
  exists Equiv.sigmaCongrRight f; tauto

@[simp] protected lemma Ifam.bigoplus_dom (A : ι → Ifam α) :
    (Ifam.bigoplus (α := α) (ι := ι) A).dom = Σ i, (A i).dom := rfl

@[simp] protected lemma Ifam.bigoplus_elem (A : ι → Ifam α) (i j) :
    (Ifam.bigoplus (α := α) (ι := ι) A).elem ⟨i, j⟩ = (A i).elem j := rfl

/-- Big sum of multisets -/
protected noncomputable def Mset.bigoplus.{u} {ι : Type} (A : ι → Mset.{u} α) : Mset.{u} α :=
  ⟦ ⨁ᴵ i, (A i).out ⟧

scoped[Mset] notation "⨁ᴹ " i ", " A => Mset.bigoplus (fun i => A)

/-! ### `map` over `bigoplus` -/

protected lemma Ifam.bigoplus_map' (f : α → β) (A : ι → Ifam α) :
    f <$>ᴵ Ifam.bigoplus A = ⨁ᴵ i, f <$>ᴵ A i := rfl

protected lemma Mset.bigoplus_map' (f : α → β) (A : ι → Mset α) :
    f <$>ᴹ Mset.bigoplus A = ⨁ᴹ i, f <$>ᴹ A i := by
  apply Quotient.sound; rw [Ifam.bigoplus_map']; apply Ifam.bigoplus_proper; intro i; simp only;
  cases A i using Quotient.ind; grw [Quotient.mk_out]; symm; apply Quotient.mk_out

protected lemma Mset.bigoplus_map (f : α → β) (A : ι → Mset α) :
    f <$> Mset.bigoplus A = ⨁ᴹ i, f <$> A i := by apply Mset.bigoplus_map'

/-! ### `bigoplus` is commutative -/

protected lemma Ifam.bigoplus_comm {ι ι' : Type} (f : ι ≃ ι') (A : ι' → Ifam α) :
    Ifam.bigoplus A ≈ ⨁ᴵ i, A (f i) := by
  symm; exists Equiv.sigmaCongrLeft (β := fun j => (A j).dom) f; intro _; rfl

protected lemma Mset.bigoplus_comm {ι ι' : Type} (f : ι ≃ ι') (A : ι' → Mset α) :
    Mset.bigoplus A = ⨁ᴹ i, A (f i) := by
  apply Quotient.sound; apply Ifam.bigoplus_comm

/-! ### `bigoplus` is associative -/

protected lemma Ifam.bigoplus_assoc {ι : Type} {ι' : ι → Type} (A : ∀ ι, ι' ι → Ifam α) :
    (⨁ᴵ i, Ifam.bigoplus (A i)) ≈ ⨁ᴵ (⟨i, j⟩ : Sigma ι'), A i j := by
  exists (Equiv.sigmaAssoc _).symm; tauto

protected lemma Mset.bigoplus_assoc {ι : Type} {ι' : ι → Type} (A : ∀ ι, ι' ι → Mset α) :
    (⨁ᴹ i, Mset.bigoplus (A i)) = ⨁ᴹ (⟨i, j⟩ : Sigma ι'), A i j := by
  apply Quotient.sound; trans;
  { apply Ifam.bigoplus_proper; { intro _; apply Quotient.mk_out } };
  apply Ifam.bigoplus_assoc

/-! ### `empty` as `bigoplus` -/

private instance Ifam.Empty_bigoplus_IsEmpty :
    IsEmpty (Ifam.bigoplus (ι := Empty) A).dom where
  false := nofun

protected lemma Ifam.empty_bigoplus : ∅ ≈ Ifam.bigoplus (ι := Empty) A := by
  exists Equiv.equivOfIsEmpty _ _; nofun

protected lemma Mset.empty_bigoplus : ∅ = Mset.bigoplus (ι := Empty) (α := α) nofun := by
  apply Quotient.sound; apply Ifam.empty_bigoplus

/-! ### Unary `bigoplus` -/

protected lemma Ifam.unary_bigoplus (A : Unit → Ifam α) : Ifam.bigoplus A ≈ A () := by
  exists Equiv.uniqueSigma _; intro _; rfl

protected lemma Mset.unary_bigoplus (A : Unit → Mset α) : Mset.bigoplus A = A () := by
  cases eq : A () using Quotient.ind; apply Quotient.sound;
  grw [Ifam.unary_bigoplus, eq, Quotient.mk_out]

/-! ### `⊕` as `bigoplus` -/

protected lemma Ifam.oplus_bigoplus (A B : Ifam α) :
    F true = A → F false = B → A ⊕ᴵ B ≈ Ifam.bigoplus F := by
  intro rfl rfl;
  exists { toFun := fun | .inl i => ⟨true, i⟩ | .inr i => ⟨false, i⟩,
           invFun := fun | ⟨true, i⟩ => .inl i | ⟨false, i⟩ => .inr i,
           left_inv := by rintro (_ | _) <;> rfl,
           right_inv := by rintro ⟨_ | _, _⟩ <;> rfl };
  rintro (_ | _) <;> rfl

protected lemma Mset.oplus_bigoplus (A B : Mset α) :
    A ⊕ᴹ B = ⨁ᴹ (b : Bool), if b then A else B := by
  rw (occs := [1]) [←Quotient.out_eq A, ←Quotient.out_eq B];
  apply Quotient.sound; apply Ifam.oplus_bigoplus <;> rfl

/-! ## Binary product -/

/-- Product of two indexed families -/
protected def Ifam.prod {α β} (A : Ifam α) (B : Ifam β) : Ifam (α × β) :=
  .mk (A.dom × B.dom) (fun (i, j) => (A.elem i, B.elem j))

scoped[Ifam] infixr:69 " ×ᴵ " => Ifam.prod

@[simp] protected lemma Ifam.prod_dom (A : Ifam α) (B : Ifam β) :
    (A ×ᴵ B).dom = (A.dom × B.dom) := rfl

@[simp] protected lemma Ifam.prod_elem (A : Ifam α) (B : Ifam β) i j :
  (A ×ᴵ B).elem (i, j) = (A.elem i, B.elem j) := rfl

@[gcongr] protected lemma Ifam.prod_proper (A A' : Ifam α) (B B' : Ifam β) :
    A ≈ A' → B ≈ B' → A ×ᴵ B ≈ A' ×ᴵ B' := by
  intro ⟨f, AA'⟩ ⟨g, BB'⟩; exists Equiv.prodCongr f g; intro (_, _);
  simp only [Ifam.prod_elem]; rw [AA', BB']; rfl

/-- Product of two multisets -/
protected def Mset.prod {α β} : Mset α → Mset β → Mset (α × β) :=
  .lift₂ (⟦ · ×ᴵ · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.prod_proper <;> trivial

scoped[Mset] infixr:69 " ×ᴹ " => Mset.prod

/-! ### `×` over `map` -/

protected lemma Mset.prod_map'
    (f : α → α') (g : β → β') (A : Mset α) (B : Mset β) :
    (f <$>ᴹ A) ×ᴹ (g <$>ᴹ B) = Prod.map f g <$>ᴹ (A ×ᴹ B) := by
  cases A using Quotient.ind; cases B using Quotient.ind; rfl

protected lemma Mset.prod_map (f : α → α') (g : β → β') (A : Mset α) (B : Mset β) :
    (f <$> A) ×ᴹ (g <$> B) = Prod.map f g <$> (A ×ᴹ B) := by apply Mset.prod_map'

protected lemma Mset.prod_map'_l (f : α → α') (A : Mset α) (B : Mset β) :
    (f <$>ᴹ A) ×ᴹ B = Prod.map f id <$>ᴹ (A ×ᴹ B) := by
  rw [←Mset.prod_map', Mset.id_map]

protected lemma Mset.prod_map_l (f : α → α') (A : Mset α) (B : Mset β) :
    (f <$> A) ×ᴹ B = Prod.map f id <$> (A ×ᴹ B) := by apply Mset.prod_map'_l

protected lemma Mset.prod_map'_r (g : β → β') (A : Mset α) (B : Mset β) :
    A ×ᴹ (g <$>ᴹ B) = Prod.map id g <$>ᴹ (A ×ᴹ B) := by
  rw [←Mset.prod_map', Mset.id_map]

protected lemma Mset.prod_map_r (g : β → β') (A : Mset α) (B : Mset β) :
    A ×ᴹ (g <$> B) = Prod.map id g <$> (A ×ᴹ B) := by apply Mset.prod_map'_r

/-! ### `×` is commutative -/

protected lemma Ifam.prod_comm (A : Ifam α) (B : Ifam β) :
    A ×ᴵ B ≈ Prod.swap <$>ᴵ (B ×ᴵ A) := by
  exists Equiv.prodComm _ _; tauto

protected lemma Mset.prod_comm (A : Mset α) (B : Mset β) :
    A ×ᴹ B = Prod.swap <$>ᴹ (B ×ᴹ A) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_comm

/-! ### `*` is unital -/

protected lemma Ifam.prod_id_r (A : Ifam α) (b : β) :
    A ×ᴵ pure b ≈ (·, b) <$>ᴵ A := by
  exists Equiv.prodPUnit _; intro _; rfl

protected lemma Mset.prod_id_r (A : Mset α) (b : β) :
    A ×ᴹ pure b = (·, b) <$>ᴹ A := by
  cases A using Quotient.ind; apply Quotient.sound;
  apply Ifam.prod_id_r

protected lemma Mset.prod_id_l (a : α) (B : Mset β) :
    pure a ×ᴹ B = (a, ·) <$>ᴹ B := by
  rw [Mset.prod_comm, Mset.prod_id_r, ←Mset.comp_map]; rfl

/-! ### `*` is associative -/

protected lemma Ifam.prod_assoc_l (A : Ifam α) (B : Ifam β) (C : Ifam γ) :
    (A ×ᴵ B) ×ᴵ C ≈ (fun (a, (b, c)) => ((a, b), c)) <$>ᴵ (A ×ᴵ (B ×ᴵ C)) := by
  exists Equiv.prodAssoc _ _ _; intro _; rfl

protected lemma Mset.prod_assoc_l (A : Mset α) (B : Mset β) (C : Mset γ) :
    (A ×ᴹ B) ×ᴹ C = (fun (a, (b, c)) => ((a, b), c)) <$>ᴹ (A ×ᴹ (B ×ᴹ C)) := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_assoc_l

protected lemma Mset.prod_assoc_r (A : Mset α) (B : Mset β) (C : Mset γ) :
    A ×ᴹ (B ×ᴹ C) = (fun ((a, b), c) => (a, b, c)) <$>ᴹ ((A ×ᴹ B) ×ᴹ C) := by
  rw [Mset.prod_assoc_l, ←Mset.comp_map]; rw (occs := [1]) [←Mset.id_map (_ ×ᴹ _)]; rfl

/-! ### `*` distributes over `⊕` -/

protected lemma Ifam.prod_bigoplus_l (A : Ifam α) (F : ι → Ifam β) :
    (A ×ᴵ ⨁ᴵ i, F i) ≈ ⨁ᴵ i, A ×ᴵ F i := by
  exists { toFun := fun ⟨a, ⟨i, b⟩⟩ => ⟨i, (a, b)⟩,
           invFun := fun ⟨i, ⟨a, b⟩⟩ => ⟨a, ⟨i, b⟩⟩,
           left_inv := by tauto, right_inv := by tauto };
  intro _; rfl

protected lemma Mset.prod_bigoplus_l (A : Mset α) (F : ι → Mset β) :
    A ×ᴹ (⨁ᴹ i, F i) = ⨁ᴹ i, A ×ᴹ F i := by
  cases A using Quotient.ind; apply Quotient.sound; grw [Ifam.prod_bigoplus_l];
  apply Ifam.bigoplus_proper; intro i; simp only; cases F i using Quotient.ind;
  grw [Quotient.mk_out]; symm; apply Quotient.mk_out

protected lemma Mset.prod_bigoplus_r (F : ι → Mset α) (A : Mset β) :
    (⨁ᴹ i, F i) ×ᴹ A = ⨁ᴹ i, F i ×ᴹ A := by
  rw [Mset.prod_comm, Mset.prod_bigoplus_l, Mset.bigoplus_map'];
  congr; ext1 _; rw [←Mset.prod_comm]

protected lemma Mset.prod_oplus_l (A : Mset α) (B C : Mset β) :
    A ×ᴹ (B ⊕ᴹ C) = A ×ᴹ B ⊕ᴹ A ×ᴹ C := by
  simp only [Mset.oplus_bigoplus, Mset.prod_bigoplus_l]; grind only

protected lemma Mset.prod_oplus_r (A B : Mset α) (C : Mset β) :
    (A ⊕ᴹ B) ×ᴹ C = A ×ᴹ C ⊕ᴹ B ×ᴹ C := by
  simp only [Mset.oplus_bigoplus, Mset.prod_bigoplus_r]; grind only

/-! ## Applicative -/

/-- `seq` for `Mset`, more universe-polymorphic than `Seq.seq` -/
protected def Mset.seq {α β : Type*} (F : Mset (α → β)) (A : Mset α) : Mset β :=
  (fun (f, a) => f a) <$>ᴹ (F ×ᴹ A)

scoped[Mset] infixl:60 " <*>ᴹ " => Mset.seq

/-- `Applicative` for `Mset` -/
protected instance Mset.instApplicative : Applicative Mset.{u} where
  seq F A := F <*>ᴹ A ()

protected lemma Mset.seq_unfold (F : Mset (α → β)) (A : Mset α) :
    F <*> A = F <*>ᴹ A := rfl

/-! `LawfulApplicative` is later derived from `LawfulMonad` -/

/-! ### `seq` distributes over `⊕ᴹ` -/

protected lemma Mset.seq'_bigoplus_l (F : Mset (α → β)) (A : ι → Mset α) :
    F <*>ᴹ (⨁ᴹ i, A i) = ⨁ᴹ i, F <*>ᴹ A i := by
  rw [Mset.seq, Mset.prod_bigoplus_l, Mset.bigoplus_map']; rfl

protected lemma Mset.seq_bigoplus_l (F : Mset (α → β)) (A : ι → Mset α) :
    F <*> (⨁ᴹ i, A i) = ⨁ᴹ i, F <*> A i := by apply Mset.seq'_bigoplus_l

protected lemma Mset.seq'_bigoplus_r (F : ι → Mset (α → β)) (A : Mset α) :
    (⨁ᴹ i, F i) <*>ᴹ A = ⨁ᴹ i, F i <*>ᴹ A := by
  rw [Mset.seq, Mset.prod_bigoplus_r, Mset.bigoplus_map']; rfl

protected lemma Mset.seq_bigoplus_r (F : ι → Mset (α → β)) (A : Mset α) :
    (⨁ᴹ i, F i) <*> A = ⨁ᴹ i, F i <*> A := by apply Mset.seq'_bigoplus_r

protected lemma Mset.seq'_oplus_l (F : Mset (α → β)) (A B : Mset α) :
    F <*>ᴹ (A ⊕ᴹ B) = (F <*>ᴹ A) ⊕ᴹ (F <*>ᴹ B) := by
  simp only [Mset.oplus_bigoplus, Mset.seq'_bigoplus_l]; grind only

protected lemma Mset.seq_oplus_l (F : Mset (α → β)) (A B : Mset α) :
    F <*> (A ⊕ᴹ B) = (F <*> A) ⊕ᴹ (F <*> B) := by apply Mset.seq'_oplus_l

protected lemma Mset.seq'_oplus_r (F G : Mset (α → β)) (A : Mset α) :
    (F ⊕ᴹ G) <*>ᴹ A = (F <*>ᴹ A) ⊕ᴹ (G <*>ᴹ A) := by
  simp only [Mset.oplus_bigoplus, Mset.seq'_bigoplus_r]; grind only

protected lemma Mset.seq_oplus_r (F G : Mset (α → β)) (A : Mset α) :
    (F ⊕ᴹ G) <*> A = (F <*> A) ⊕ᴹ (G <*> A) := by apply Mset.seq'_oplus_r

/-! ## Join -/

/-- `join` for `Ifam` -/
protected noncomputable def Ifam.join {α} (A : Ifam (Mset α)) : Mset α :=
  Mset.bigoplus A.elem

@[gcongr] protected lemma Ifam.join_proper (A B : Ifam (Mset α)) :
    A ≈ B → A.join = B.join := by
  intro ⟨f, AB⟩; apply Quotient.sound;
  let g : (⨁ᴵ i, (A.elem i).out).dom ≃ (⨁ᴵ i, (B.elem i).out).dom :=
    { toFun := fun ⟨i, k⟩ => ⟨f i, congrArg (·.out.dom) (AB i) ▸ k⟩,
      invFun := fun ⟨j, k⟩ => ⟨f.symm j,
        congrArg (·.out.dom) (Ifam.equiv_elem_eq_symm AB j).symm ▸ k⟩,
      left_inv := by intro _; grind only [Equiv.symm_apply_apply],
      right_inv := by intro _; grind only [Equiv.apply_symm_apply] };
  exists g; rw [←Equiv.toFun_as_coe g]; intro ⟨i, _⟩; revert g;
  simp only [Ifam.bigoplus_elem]; generalize AB i = eq; revert eq;
  generalize B.elem (f i) = Bj; intro rfl; rfl

/-- `join` for `Mset` -/
protected noncomputable def Mset.join {α} : Mset (Mset α) → Mset α :=
  .lift (·.join) <| by intros; apply Ifam.join_proper; trivial

/-! ### Join laws -/

protected lemma Mset.map_join (f : α → β) (A : Mset (Mset α)) :
    f <$>ᴹ Mset.join A = Mset.join (Mset.map f <$>ᴹ A) := by
  revert A; apply Quotient.ind; intro ⟨_, F⟩;
  apply Quotient.sound; rw [Ifam.bigoplus_map']; apply Ifam.bigoplus_proper;
  simp only [Ifam.map_elem]; intro i; cases F i using Quotient.ind;
  grw [Quotient.mk_out]; symm; apply Quotient.mk_out

protected lemma Mset.join_map_seq (F : Mset (α → β)) :
    Mset.join ((· <$>ᴹ A) <$>ᴹ F) = F <*>ᴹ A := by
  cases F using Quotient.ind; cases A using Quotient.ind;
  apply Quotient.sound; simp only [Ifam.map_elem]; trans;
  { apply Ifam.bigoplus_proper; { intro _; apply Quotient.mk_out } }
  exists { toFun := fun ⟨i, j⟩ => ⟨i, j⟩, invFun := fun ⟨i, j⟩ => ⟨i, j⟩ }; intro _; rfl

protected lemma Mset.join_pure (A : Mset α) : Mset.join (pure A) = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  simp only [Ifam.pure_elem]; grw [Quotient.mk_out]; apply Ifam.unary_bigoplus

protected lemma Ifam.bigoplus_pure (A : Ifam α) : Ifam.bigoplus (pure <$>ᴵ A).elem ≈ A := by
  exists Equiv.sigmaPUnit _; intro _; rfl

protected lemma Mset.join_pure_map (A : Mset α) : Mset.join (pure <$>ᴹ A) = A := by
  cases A using Quotient.ind; apply Quotient.sound; trans; swap;
  { apply Ifam.bigoplus_pure }; apply Ifam.bigoplus_proper; intro _; apply Quotient.mk_out

protected lemma Mset.join_join (A : Mset (Mset (Mset α))) :
    Mset.join (Mset.join A) = Mset.join (Mset.join <$>ᴹ A) := by
  revert A; apply Quotient.ind; intro ⟨_, F⟩; apply Quotient.sound;
  unfold Mset.join; unfold Ifam.join;
  simp only [Ifam.bigoplus_dom, Ifam.map_dom, Ifam.map_elem];
  trans; swap;
  { apply Ifam.bigoplus_proper;
    { intro i; rewrite [←Quotient.out_eq (F i), Quotient.lift_mk];
      symm; unfold Mset.bigoplus; apply Quotient.mk_out }; }
  exists { toFun := fun ⟨⟨i, j⟩, k⟩ => ⟨i, ⟨j, k⟩⟩, invFun := fun ⟨i, ⟨j, k⟩⟩ => ⟨⟨i, j⟩, k⟩ };
  intro _; rfl

/-! ## Monad -/

/-- Monadic bind for `Mset`, more universe-polymorphic than `Monad.bind` -/
protected noncomputable def Mset.bind {α β : Type*} (A : Mset α) (K : α → Mset β) : Mset β :=
  Mset.join (K <$>ᴹ A)

scoped[Mset] infixl:55 " >>=ᴹ " => Mset.bind

/-- `Monad` for `Mset` -/
noncomputable instance Mset.instMonad : Monad Mset.{u} where
  bind := Mset.bind

/-! ### Monad laws -/

protected lemma Mset.bind_unfold : Bind.bind = Mset.bind (α := α) (β := β) := rfl

protected lemma Mset.pure_seq (f : α → β) (A : Mset α) :
    pure f <*>ᴹ A = f <$>ᴹ A := by rw [Mset.seq, Mset.prod_id_l, ←Mset.comp_map]; rfl

protected lemma Mset.pure_bind (a : α) (K : α → Mset β) :
    pure a >>=ᴹ K = K a := by rw [Mset.bind, Mset.pure_map', Mset.join_pure]

protected lemma Mset.bind_pure_comp (f : α → β) (A : Mset α) :
    A >>=ᴹ (fun a => pure (f a)) = f <$>ᴹ A := by
  rw [Mset.bind, ←Function.comp_def, Mset.comp_map, Mset.join_pure_map]

protected lemma Mset.bind_map (F : Mset (α → β)) (A : Mset α) :
    F >>=ᴹ (· <$>ᴹ A) = F <*>ᴹ A := by apply Mset.join_map_seq

protected lemma Mset.bind_assoc (A : Mset α) (K : α → Mset β) (L : β → Mset γ) :
    (A >>=ᴹ K) >>=ᴹ L = A >>=ᴹ fun a => K a >>=ᴹ L := by
  have eq : (fun a => Mset.bind (K a) L) = Mset.join ∘ Mset.map L ∘ K := rfl; rw [eq];
  unfold Mset.bind; rw [Mset.comp_map, ←Mset.join_join, Mset.map_join, ←Mset.comp_map]

/-- Monad laws for `Mset` -/
protected instance Mset.instLawfulMonad : LawfulMonad Mset.{u} where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq := Mset.pure_seq
  pure_bind := Mset.pure_bind
  bind_pure_comp := Mset.bind_pure_comp
  bind_map := Mset.bind_map
  bind_assoc := Mset.bind_assoc

/-! ### Commutative applicative -/

protected lemma Mset.commutative_prod (A : Mset α) (B : Mset β) :
    Prod.mk <$>ᴹ A <*>ᴹ B = (fun b a => (a, b)) <$>ᴹ B <*>ᴹ A := by
  unfold Mset.seq; rw [Mset.prod_map'_l, Mset.prod_map'_l];
  rw [←Mset.comp_map, ←Mset.comp_map, Mset.prod_comm, ←Mset.comp_map]; rfl

/-- Commutative applicative laws for `Mset` -/
protected instance Mset.instCommApplicative : CommApplicative Mset.{u} where
  commutative_prod := Mset.commutative_prod

/-! ## Membership -/

/-- Membership for `Ifam` -/
protected instance Ifam.instMembership : Membership α (Ifam α) where
  mem A a := ∃ i, A.elem i = a

protected lemma Ifam.mem_proper' (A B : Ifam α) :
    A ≈ B → a ∈ A → a ∈ B := by
  rintro ⟨f, AB⟩ ⟨i, Ai⟩; exists f i; rw [←AB]; trivial

protected lemma Ifam.mem_proper (A B : Ifam α) :
    A ≈ B → (a ∈ A) = (a ∈ B) := by
  intro _; ext1; constructor <;> { apply Ifam.mem_proper'; tauto }

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

@[simp] protected lemma Ifam.mem_oplus (a : α) (A B : Ifam α) :
    (a ∈ A ⊕ᴵ B) = (a ∈ A ∨ a ∈ B) := by
  ext1; constructor;
  · rintro ⟨i | j, rfl⟩; { left; exists i }; { right; exists j }
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩); { exists (.inl i) }; { exists (.inr i) }

@[simp] protected lemma Mset.mem_oplus (A B : Mset α) a :
    (a ∈ A ⊕ᴹ B) = (a ∈ A ∨ a ∈ B) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Ifam.mem_oplus

@[simp] protected lemma Ifam.mem_bigoplus {ι : Type} (A : ι → Ifam α) a :
    (a ∈ ⨁ᴵ i, A i) = ∃ i, a ∈ A i := by
  ext1; constructor; { rintro ⟨⟨_, _⟩, rfl⟩; tauto }; { rintro ⟨_, ⟨_, rfl⟩⟩; tauto }

@[simp] protected lemma Mset.mem_bigoplus {ι : Type} (A : ι → Mset α) a :
    (a ∈ ⨁ᴹ i, A i) = ∃ i, a ∈ A i := by
  trans; { apply Ifam.mem_bigoplus }; congr; funext _; apply Mset.mem_out

@[simp] protected lemma Ifam.mem_prod (A : Ifam α) (B : Ifam β) p :
    (p ∈ A ×ᴵ B) = (p.1 ∈ A ∧ p.2 ∈ B) := by
  cases p; ext1; constructor;
  · rintro ⟨⟨_, _⟩, eq⟩; have ⟨rfl, rfl⟩ := Prod.mk_inj.mp eq; tauto
  · rintro ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩; tauto

@[simp] protected lemma Mset.mem_prod (A : Mset α) (B : Mset β) p :
    (p ∈ A ×ᴹ B) = (p.1 ∈ A ∧ p.2 ∈ B) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Ifam.mem_prod

@[simp] protected lemma Mset.mem_seq' (F : Mset (α → β)) (A : Mset α) b :
    (b ∈ F <*>ᴹ A) = ∃ f ∈ F, ∃ a ∈ A, f a = b := by
  rw [Mset.seq]; simp only [Mset.mem_map', Prod.exists, Mset.mem_prod]; grind only

@[simp] protected lemma Mset.mem_seq (F : Mset (α → β)) (A : Mset α) b :
    (b ∈ F <*> A) = ∃ f ∈ F, ∃ a ∈ A, f a = b := by apply Mset.mem_seq'

@[simp] protected lemma Mset.mem_join (A : Mset (Mset α)) a :
    (a ∈ Mset.join A) = ∃ B ∈ A, a ∈ B := by
  revert A; apply Quotient.ind; intro A;
  rw [Mset.join, Quotient.lift_mk, Ifam.join, Mset.mem_bigoplus]; ext1;
  constructor; { tauto }; intro ⟨_, ⟨_, rfl⟩, _⟩; tauto

@[simp] protected lemma Mset.mem_bind' (A : Mset α) (K : α → Mset β) b :
    (b ∈ A >>=ᴹ K) = ∃ a ∈ A, b ∈ K a := by
  rw [Mset.bind]; simp only [Mset.mem_map', Mset.mem_join]; grind only

@[simp] protected lemma Mset.mem_bind (A : Mset α) (K : α → Mset β) b :
    (b ∈ A >>= K) = ∃ a ∈ A, b ∈ K a := by apply Mset.mem_bind'

/-! ## Inhabitedness -/

/-- Inhabitedness for `Mset` -/
protected def Mset.inhab (A : Mset α) : Prop := ∃ a, a ∈ A

/-! ### Inhabitedness lemmas -/

@[simp] protected lemma Mset.inhab_map (f : α → β) (A : Mset α) :
    (f <$> A).inhab = A.inhab := by
  simp only [Mset.inhab, Mset.mem_map]; grind only

@[simp] protected lemma Mset.inhab_empty : (∅ : Mset α).inhab = False := by
  simp only [Mset.inhab, Mset.mem_empty]; grind only

@[simp] protected lemma Mset.inhab_pure (a : α) : (pure a : Mset α).inhab = True := by
  simp only [Mset.inhab, Mset.mem_pure]; grind only

@[simp] protected lemma Mset.inhab_oplus (A B : Mset α) :
    (A ⊕ᴹ B).inhab = A.inhab ∨ B.inhab := by
  simp only [Mset.inhab, Mset.mem_oplus]; grind only

@[simp] protected lemma Mset.inhab_bigoplus {ι : Type} (A : ι → Mset α) :
    (⨁ᴹ i, A i).inhab = ∃ i, (A i).inhab := by
  simp only [Mset.inhab, Mset.mem_bigoplus]; grind only

@[simp] protected lemma Mset.inhab_prod (A : Mset α) (B : Mset β) :
    (A ×ᴹ B).inhab = (A.inhab ∧ B.inhab) := by
  simp only [Mset.inhab, Mset.mem_prod]; ext1; constructor; { tauto };
  intro ⟨⟨a, _⟩, ⟨b, _⟩⟩; exists (a, b)

@[simp] protected lemma Mset.inhab_seq' (F : Mset (α → β)) (A : Mset α) :
    (F <*>ᴹ A).inhab = (F.inhab ∧ A.inhab) := by
  simp only [Mset.inhab, Mset.mem_seq']; grind only

@[simp] protected lemma Mset.inhab_seq (F : Mset (α → β)) (A : Mset α) :
    (F <*> A).inhab = (F.inhab ∧ A.inhab) := by apply Mset.inhab_seq'

@[simp] protected lemma Mset.inhab_join (A : Mset (Mset α)) :
    A.join.inhab = (A.inhab ∧ ∃ a ∈ A, a.inhab) := by
  simp only [Mset.inhab, Mset.mem_join]; grind only

@[simp] protected lemma Mset.inhab_bind' (A : Mset α) (K : α → Mset β) :
    (A >>=ᴹ K).inhab = (A.inhab ∧ ∃ a ∈ A, (K a).inhab) := by
  simp only [Mset.inhab, Mset.mem_bind']; grind only

@[simp] protected lemma Mset.inhab_bind (A : Mset α) (K : α → Mset β) :
    (A >>= K).inhab = (A.inhab ∧ ∃ a ∈ A, (K a).inhab) := by apply Mset.inhab_bind'

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
