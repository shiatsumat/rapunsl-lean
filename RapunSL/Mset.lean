module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Control.Applicative

@[expose] public section

/-! # Multisets, possibly infinite -/

/-! ## `Ifam`: Indexed family -/

/-- Indexed family -/
structure Ifam.{u} (α : Type u) : Type (max 1 u) where protected mk ::
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
protected instance Ifam.Setoid.{u} α : Setoid (Ifam α) :=
  Setoid.mk (Ifam.equiv.{u}) Ifam.equiv_is_equiv

/-! ## `Mset`: Multiset, possibly infinite -/

/-- Multiset, possibly infinite -/
def Mset.{u} (α : Type u) : Type (max 1 u) :=
  Quotient (Ifam.Setoid.{u} α)

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

protected lemma Ifam.map_proper (A B : Ifam α) :
    A ≈ B → f <$>ᴵ A ≈ f <$>ᴵ B := by
  intro ⟨g, AB⟩; exists g; simp only [Ifam.map_elem]; intro _; rw [AB]; rfl

/-- Functor map for `Mset`, more universe-polymorphic than `Functor.map` -/
protected def Mset.map {α β : Type*} (f : α → β) : Mset α → Mset β :=
  .lift (⟦ f <$>ᴵ · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.map_proper; assumption

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
protected instance Ifam.empty : EmptyCollection (Ifam α) where
  emptyCollection := .mk Empty nofun

@[simp] protected lemma Ifam.empty_dom :
    (∅ : Ifam α).dom = Empty := rfl

protected instance Ifam.empty_dom_Empty : IsEmpty (∅ : Ifam α).dom := by
  apply Empty.instIsEmpty

/-- Empty multiset -/
protected instance Mset.empty : EmptyCollection (Mset α) where
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
protected instance Mset.Pure : Pure Mset.{u} where
  pure a := ⟦ pure a ⟧

protected lemma Mset.pure_unfold (a : α) :
    pure (f := Mset) a = ⟦ .mk Unit (fun _ => a) ⟧ := rfl

/-! ## `map` over `pure` -/

protected lemma Ifam.pure_map (f : α → β) (a : α) :
    f <$>ᴵ pure a = pure (f a) := rfl

protected lemma Mset.pure_map (f : α → β) (a : α) :
    f <$>ᴹ pure a = pure (f a) := rfl

/-! ## Binary sum -/

/-- Sum of two indexed families -/
protected def Ifam.sum {α} (A B : Ifam α) : Ifam α :=
  .mk (A.dom ⊕ B.dom) (fun s => s.casesOn A.elem B.elem)

protected instance Ifam.instAdd : Add (Ifam.{u} α) where
  add := Ifam.sum

protected lemma Ifam.sum_unfold : HAdd.hAdd = Ifam.sum (α := α) := rfl

@[simp] protected lemma Ifam.sum_dom (A B : Ifam α) :
  (A + B).dom = (A.dom ⊕ B.dom) := rfl

@[simp] protected lemma Ifam.sum_elem_inl (A B : Ifam α) {i} :
  (A + B).elem (.inl i) = A.elem i := rfl

@[simp] protected lemma Ifam.sum_elem_inr (A B : Ifam α) {i} :
  (A + B).elem (.inr i) = B.elem i := rfl

protected lemma Ifam.sum_proper (A A' B B' : Ifam α) :
    A ≈ A' → B ≈ B' → A + B ≈ A' + B' :=
  fun ⟨f, AB⟩ ⟨g, A'B'⟩ => by
    exists Equiv.sumCongr f g; simp only [Ifam.sum_dom];
    rintro (_ | _) <;> simp_all only [Ifam.sum_elem_inl, Ifam.sum_elem_inr] <;> rfl

protected lemma Ifam.sum_proper_l (A A' B : Ifam α) :
    A ≈ A' → A + B ≈ A' + B := by
  intro _; apply Ifam.sum_proper; { assumption }; { rfl }

protected lemma Ifam.sum_proper_r (A B B' : Ifam α) :
    B ≈ B' → A + B ≈ A + B' := by
  intro _; apply Ifam.sum_proper; { rfl }; { assumption }

/-- Sum of two multisets -/
protected def Mset.sum.{u} {α} : Mset.{u} α → Mset.{u} α → Mset α :=
  .lift₂ (⟦ · + · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.sum_proper <;> assumption

protected instance Mset.instAdd : Add (Mset.{u} α) where
  add := Mset.sum

protected lemma Mset.sum_unfold : HAdd.hAdd = Mset.sum (α := α) := rfl

/-! ### `map` over `+` -/

protected lemma Ifam.sum_map (f : α → β) (A B : Ifam α) :
    f <$>ᴵ (A + B) ≈ f <$>ᴵ A + f <$>ᴵ B := by
  exists Equiv.refl _; rintro (_ | _) <;> rfl

protected lemma Mset.sum_map (f : α → β) (A B : Mset α) :
    f <$>ᴹ (A + B) = f <$>ᴹ A + f <$>ᴹ B := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.sum_map

/-! ### `+` is commutative -/

protected lemma Ifam.sum_comm (A B : Ifam α) : A + B ≈ B + A := by
  exists Equiv.sumComm _ _; rintro (_ | _) <;> rfl

protected instance Mset.sum_Commutative :
    Std.Commutative (HAdd.hAdd (α := Mset α)) where
  comm A B := by
    cases A using Quotient.ind; cases B using Quotient.ind;
    apply Quotient.sound; apply Ifam.sum_comm

/-! ### `+` is unital -/

protected lemma Ifam.sum_id_r (A : Ifam α) : A + ∅ ≈ A := by
  exists Equiv.sumEmpty _ _; rintro (_ | _); { rfl }; { nofun }

protected instance Mset.sum_LawfulCommIdentity :
    Std.LawfulCommIdentity (HAdd.hAdd (α := Mset α)) ∅ where
  right_id A := by
    cases A using Quotient.ind; apply Quotient.sound; apply Ifam.sum_id_r

/-! ### `+` is assoc -/

protected lemma Ifam.sum_assoc (A B C : Ifam α) : (A + B) + C ≈ A + (B + C) := by
  exists Equiv.sumAssoc _ _ _; rintro ((_ | _) | _) <;> rfl

protected instance Mset.sum_Associative :
    Std.Associative (HAdd.hAdd (α := Mset α)) where
  assoc A B C := by
    cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
    apply Quotient.sound; apply Ifam.sum_assoc

/-! ## Big sum -/

/-- Big sum of indexed families -/
protected def Ifam.bigsum {ι : Type} (A : ι → Ifam α) : Ifam α :=
  .mk (Σ i, (A i).dom) (fun ⟨i, j⟩ => (A i).elem j)

scoped[Ifam] notation "∑ᴵ " i ", " A => Ifam.bigsum (fun i => A)

protected lemma Ifam.bigsum_proper (A A' : ι → Ifam α) :
    (∀ i, A i ≈ A' i) → Ifam.bigsum A ≈ Ifam.bigsum A' := by
  intro AA'; have ⟨f, AA'⟩ := Classical.skolem.mp AA';
  exists Equiv.sigmaCongrRight f; intro _; apply AA'

@[simp] protected lemma Ifam.bigsum_dom (A : ι → Ifam α) :
    (Ifam.bigsum (α := α) (ι := ι) A).dom = Σ i, (A i).dom := rfl

@[simp] protected lemma Ifam.bigsum_elem (A : ι → Ifam α) (i j) :
    (Ifam.bigsum (α := α) (ι := ι) A).elem ⟨i, j⟩ = (A i).elem j := rfl

/-- Big sum of multisets -/
protected noncomputable def Mset.bigsum.{u} {ι : Type} (A : ι → Mset.{u} α) : Mset.{u} α :=
  ⟦ ∑ᴵ i, (A i).out ⟧

scoped[Mset] notation "∑ᴹ " i ", " A:67 => Mset.bigsum (fun i => A)

/-! ### `map` over `bigsum` -/

protected lemma Ifam.bigsum_map (f : α → β) (A : ι → Ifam α) :
    f <$>ᴵ Ifam.bigsum A = ∑ᴵ i, f <$>ᴵ A i := rfl

protected lemma Mset.bigsum_map (f : α → β) (A : ι → Mset α) :
    f <$>ᴹ Mset.bigsum A = ∑ᴹ i, f <$>ᴹ A i := by
  apply Quotient.sound; rw [Ifam.bigsum_map]; apply Ifam.bigsum_proper; intro i; simp only;
  cases A i using Quotient.ind; trans; swap; { symm; apply Quotient.mk_out };
  apply Ifam.map_proper; apply Quotient.mk_out

/-! ### `bigsum` is commutative -/

protected lemma Ifam.bigsum_comm {ι ι' : Type} (f : ι ≃ ι') (A : ι' → Ifam α) :
    Ifam.bigsum A ≈ ∑ᴵ i, A (f i) := by
  symm; exists Equiv.sigmaCongrLeft (β := fun j => (A j).dom) f; intro _; rfl

protected lemma Mset.bigsum_comm {ι ι' : Type} (f : ι ≃ ι') (A : ι' → Mset α) :
    Mset.bigsum A = ∑ᴹ i, A (f i) := by
  apply Quotient.sound; apply Ifam.bigsum_comm

/-! ### `bigsum` is associative -/

protected lemma Ifam.bigsum_assoc {ι : Type} {ι' : ι → Type} (A : ∀ ι, ι' ι → Ifam α) :
    (∑ᴵ i, Ifam.bigsum (A i)) ≈ ∑ᴵ (⟨i, j⟩ : Sigma ι'), A i j := by
  exists (Equiv.sigmaAssoc _).symm; intro _; rfl

protected lemma Mset.bigsum_assoc {ι : Type} {ι' : ι → Type} (A : ∀ ι, ι' ι → Mset α) :
    ∑ᴹ i, Mset.bigsum (A i) = ∑ᴹ (⟨i, j⟩ : Sigma ι'), A i j := by
  apply Quotient.sound; trans;
  { apply Ifam.bigsum_proper; intros; apply Quotient.mk_out };
  apply Ifam.bigsum_assoc

/-! ### `empty` as `bigsum` -/

private instance Ifam.Empty_bigsum_IsEmpty :
    IsEmpty (Ifam.bigsum (ι := Empty) A).dom where
  false := nofun

protected lemma Ifam.empty_bigsum : ∅ ≈ Ifam.bigsum (ι := Empty) A := by
  exists Equiv.equivOfIsEmpty _ _; nofun

protected lemma Mset.empty_bigsum : ∅ = Mset.bigsum (ι := Empty) (α := α) nofun := by
  apply Quotient.sound; apply Ifam.empty_bigsum

/-! ### Unary `bigsum` -/

protected lemma Ifam.unary_bigsum (A : Ifam α) : (∑ᴵ (_ : Unit), A) ≈ A := by
  exists Equiv.uniqueSigma _; intro _; rfl

protected lemma Mset.unary_bigsum (A : Mset α) : ∑ᴹ (_ : Unit), A = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  trans; swap; { apply Quotient.mk_out }; apply Ifam.unary_bigsum

/-! ### `+` as `bigsum` -/

protected lemma Ifam.sum_bigsum (A B : Ifam α) :
    F true = A → F false = B → A + B ≈ Ifam.bigsum F := by
  intro rfl rfl;
  exists { toFun := fun | .inl i => ⟨true, i⟩ | .inr i => ⟨false, i⟩,
           invFun := fun | ⟨true, i⟩ => .inl i | ⟨false, i⟩ => .inr i,
           left_inv := by rintro (_ | _) <;> rfl,
           right_inv := by rintro ⟨_ | _, _⟩ <;> rfl };
  rintro (_ | _) <;> rfl

protected lemma Mset.sum_bigsum (A B : Mset α) :
    A + B = ∑ᴹ (b : Bool), if b then A else B := by
  rw (occs := [1]) [←Quotient.out_eq A, ←Quotient.out_eq B];
  apply Quotient.sound; apply Ifam.sum_bigsum <;> rfl

/-! ## Binary product -/

/-- Product of two indexed families -/
protected def Ifam.prod {α β} (A : Ifam α) (B : Ifam β) : Ifam (α × β) :=
  .mk (A.dom × B.dom) (fun (i, j) => (A.elem i, B.elem j))

scoped[Ifam] infixr:69 " ×ᴵ " => Ifam.prod

@[simp] protected lemma Ifam.prod_dom (A : Ifam α) (B : Ifam β) :
    (A ×ᴵ B).dom = (A.dom × B.dom) := rfl

@[simp] protected lemma Ifam.prod_elem (A : Ifam α) (B : Ifam β) i j :
  (A ×ᴵ B).elem (i, j) = (A.elem i, B.elem j) := rfl

protected lemma Ifam.prod_proper (A A' : Ifam α) (B B' : Ifam β) :
    A ≈ A' → B ≈ B' → A ×ᴵ B ≈ A' ×ᴵ B' := by
  intro ⟨f, AA'⟩ ⟨g, BB'⟩;
  exists Equiv.prodCongr f g; intro (_, _); simp only [Ifam.prod_elem];
  rw [AA', BB']; rfl

/-- Product of two multisets -/
protected def Mset.prod {α β} : Mset α → Mset β → Mset (α × β) :=
  .lift₂ (⟦ · ×ᴵ · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.prod_proper <;> assumption

scoped[Mset] infixr:69 " ×ᴹ " => Mset.prod

/-! ### `×` over `map` -/

protected lemma Mset.prod_map
    (f : α → α') (g : β → β') (A : Mset α) (B : Mset β) :
    (f <$>ᴹ A) ×ᴹ (g <$>ᴹ B) = Prod.map f g <$>ᴹ (A ×ᴹ B) := by
  cases A using Quotient.ind; cases B using Quotient.ind; rfl

protected lemma Mset.prod_map_l (f : α → α') (A : Mset α) (B : Mset β) :
    (f <$>ᴹ A) ×ᴹ B = Prod.map f id <$>ᴹ (A ×ᴹ B) := by
  rw [←Mset.prod_map, Mset.id_map]

protected lemma Mset.prod_map_r (g : β → β') (A : Mset α) (B : Mset β) :
    A ×ᴹ (g <$>ᴹ B) = Prod.map id g <$>ᴹ (A ×ᴹ B) := by
  rw [←Mset.prod_map, Mset.id_map]

/-! ### `×` is commutative -/

protected lemma Ifam.prod_comm (A : Ifam α) (B : Ifam β) :
    A ×ᴵ B ≈ Prod.swap <$>ᴵ (B ×ᴵ A) := by
  exists Equiv.prodComm _ _; intro _; rfl

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

/-! ### `*` distributes over `+` -/

protected lemma Ifam.prod_sum_distrib_l (A : Ifam α) (B C : Ifam β) :
    A ×ᴵ (B + C) ≈ A ×ᴵ B + A ×ᴵ C := by
  exists Equiv.prodSumDistrib _ _ _; rintro ⟨_, (_ | _)⟩ <;> rfl

protected lemma Mset.prod_sum_distrib_l (A : Mset α) (B C : Mset β) :
    A ×ᴹ (B + C) = A ×ᴹ B + A ×ᴹ C := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_sum_distrib_l

protected lemma Mset.prod_sum_distrib_r (A B : Mset α) (C : Mset β) :
    (A + B) ×ᴹ C = A ×ᴹ C + B ×ᴹ C := by
  rw [Mset.prod_comm, Mset.prod_sum_distrib_l, Mset.prod_comm C A, Mset.prod_comm C B,
      Mset.sum_map, ←Mset.comp_map, ←Mset.comp_map, Prod.swap_swap_eq, Mset.id_map, Mset.id_map]

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

/-! ## Join -/

/-- `join` for `Ifam` -/
protected noncomputable def Ifam.join {α} (A : Ifam (Mset α)) : Mset α :=
  Mset.bigsum A.elem

protected lemma Ifam.join_proper (A B : Ifam (Mset α)) :
    A ≈ B → A.join = B.join := by
  intro ⟨f, AB⟩; apply Quotient.sound;
  let g : (∑ᴵ i, (A.elem i).out).dom ≃ (∑ᴵ i, (B.elem i).out).dom :=
    { toFun := fun ⟨i, k⟩ => ⟨f i, congrArg (·.out.dom) (AB i) ▸ k⟩,
      invFun := fun ⟨j, k⟩ => ⟨f.symm j,
        congrArg (·.out.dom) (Ifam.equiv_elem_eq_symm AB j).symm ▸ k⟩,
      left_inv := by intro _; grind only [Equiv.symm_apply_apply],
      right_inv := by intro _; grind only [Equiv.apply_symm_apply] };
  exists g; rw [←Equiv.toFun_as_coe g]; intro ⟨i, _⟩; revert g;
  simp only [Ifam.bigsum_elem]; generalize AB i = eq; revert eq;
  generalize B.elem (f i) = Bj; intro rfl; rfl

/-- `join` for `Mset` -/
protected noncomputable def Mset.join {α} : Mset (Mset α) → Mset α :=
  .lift (·.join) <| by intros; apply Ifam.join_proper; assumption

/-! ### Join laws -/

protected lemma Mset.map_join (f : α → β) (A : Mset (Mset α)) :
    f <$>ᴹ Mset.join A = Mset.join (Mset.map f <$>ᴹ A) := by
  revert A; apply Quotient.ind; intro ⟨_, F⟩;
  apply Quotient.sound; rw [Ifam.bigsum_map]; apply Ifam.bigsum_proper;
  simp only [Ifam.map_elem]; intro i; cases F i using Quotient.ind; trans; swap;
  { symm; apply Quotient.mk_out }; apply Ifam.map_proper; apply Quotient.mk_out

protected lemma Mset.join_map_seq (F : Mset (α → β)) :
    Mset.join ((· <$>ᴹ A) <$>ᴹ F) = F <*>ᴹ A := by
  cases F using Quotient.ind; cases A using Quotient.ind;
  apply Quotient.sound; simp only [Ifam.map_elem]; trans;
  { apply Ifam.bigsum_proper; { intro _; apply Quotient.mk_out } }
  exists { toFun := fun ⟨i, j⟩ => ⟨i, j⟩, invFun := fun ⟨i, j⟩ => ⟨i, j⟩ }; intro _; rfl

protected lemma Mset.join_pure (A : Mset α) : Mset.join (pure A) = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  simp only [Ifam.pure_elem]; trans; swap; { apply Quotient.mk_out };
  apply Ifam.unary_bigsum

protected lemma Ifam.bigsum_pure (A : Ifam α) : Ifam.bigsum (pure <$>ᴵ A).elem ≈ A := by
  exists Equiv.sigmaPUnit _; intro _; rfl

protected lemma Mset.join_pure_map (A : Mset α) : Mset.join (pure <$>ᴹ A) = A := by
  cases A using Quotient.ind; apply Quotient.sound; trans; swap;
  { apply Ifam.bigsum_pure }; apply Ifam.bigsum_proper;
  intro _; apply Quotient.mk_out

protected lemma Mset.join_join (A : Mset (Mset (Mset α))) :
    Mset.join (Mset.join A) = Mset.join (Mset.join <$>ᴹ A) := by
  revert A; apply Quotient.ind; intro ⟨_, F⟩; apply Quotient.sound;
  unfold Mset.join; unfold Ifam.join;
  simp only [Ifam.bigsum_dom, Ifam.map_dom, Ifam.map_elem];
  trans; swap;
  { apply Ifam.bigsum_proper;
    { intro i; rewrite [←Quotient.out_eq (F i), Quotient.lift_mk];
      symm; unfold Mset.bigsum; apply Quotient.mk_out }; }
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

protected lemma Mset.bind_unfold : Bind.bind = Mset.bind (α := α) (β := β) := rfl

protected lemma Mset.pure_seq (f : α → β) (A : Mset α) :
    pure f <*>ᴹ A = f <$>ᴹ A := by rw [Mset.seq, Mset.prod_id_l, ←Mset.comp_map]; rfl

protected lemma Mset.pure_bind (a : α) (K : α → Mset β) :
    pure a >>=ᴹ K = K a := by rw [Mset.bind, Mset.pure_map, Mset.join_pure]

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

protected lemma Mset.commutative_prod (A : Mset α) (B : Mset β) :
    Prod.mk <$>ᴹ A <*>ᴹ B = (fun b a => (a, b)) <$>ᴹ B <*>ᴹ A := by
  unfold Mset.seq; rw [Mset.prod_map_l, Mset.prod_map_l];
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
  rintro ⟨f, AB⟩ ⟨i, Ai⟩; exists f i; rw [←AB]; assumption

protected lemma Ifam.mem_proper (A B : Ifam α) :
    A ≈ B → (a ∈ A) = (a ∈ B) := by
  intro _; apply propext; constructor <;>
    apply Ifam.mem_proper';{ assumption }; { symm; assumption }

/-- Membership for `Mset` -/
protected instance Mset.instMembership : Membership α (Mset α) where
  mem A a := A.liftOn (a ∈ ·) <| Ifam.mem_proper

@[simp] protected lemma Mset.mem_out (A : Mset α) a : (a ∈ A.out) = (a ∈ A) := by
  cases A using Quotient.ind; apply Ifam.mem_proper; apply Quotient.mk_out

@[simp] protected lemma Ifam.mem_map (f : α → β) (A : Ifam α) b :
    (b ∈ f <$>ᴵ A) = ∃ a ∈ A, f a = b := by
  apply propext; constructor;
  · intro ⟨i, eq⟩; subst eq; exists A.elem i; and_intros; { exists i }; { rfl }
  · intro ⟨a, ⟨i, eq⟩, eq'⟩; subst eq eq'; exists i

@[simp] protected lemma Mset.mem_map (f : α → β) (A : Mset α) b :
    (b ∈ f <$>ᴹ A) = ∃ a ∈ A, f a = b := by
  cases A using Quotient.ind; apply Ifam.mem_map

@[simp] protected lemma Ifam.mem_empty (a : α) : (a ∈ (∅ : Ifam α)) = False := by
  rw [eq_iff_iff, iff_false]; nofun

@[simp] protected lemma Mset.mem_empty (a : α) : (a ∈ (∅ : Mset α)) = False := by
  apply Ifam.mem_empty

@[simp] protected lemma Ifam.mem_pure (a b : α) : (a ∈ pure (f := Ifam) b) = (a = b) := by
  apply propext; constructor;
  { intro ⟨(), eq⟩; rw [←eq]; rfl }; { intro rfl; exists () }

@[simp] protected lemma Mset.mem_pure (a b : α) : (a ∈ pure (f := Mset) b) = (a = b) := by
  apply Ifam.mem_pure

@[simp] protected lemma Ifam.mem_sum (a : α) (A B : Ifam α) :
    (a ∈ A + B) = (a ∈ A ∨ a ∈ B) := by
  apply propext; constructor;
  · rintro ⟨i | j, rfl⟩; { left; exists i }; { right; exists j }
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩); { exists (.inl i) }; { exists (.inr i) }

@[simp] protected lemma Mset.mem_sum (A B : Mset α) a :
    (a ∈ A + B) = (a ∈ A ∨ a ∈ B) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Ifam.mem_sum

@[simp] protected lemma Ifam.mem_bigsum {ι : Type} (A : ι → Ifam α) a :
    (a ∈ ∑ᴵ i, A i) = ∃ i, a ∈ A i := by
  apply propext; constructor;
  · rintro ⟨⟨i, j⟩, rfl⟩; exists i; exists j
  · rintro ⟨i, ⟨j, rfl⟩⟩; exists ⟨i, j⟩

@[simp] protected lemma Mset.mem_bigsum {ι : Type} (A : ι → Mset α) a :
    (a ∈ ∑ᴹ i, A i) = ∃ i, a ∈ A i := by
  trans; { apply Ifam.mem_bigsum }; congr; funext _; apply Mset.mem_out

@[simp] protected lemma Ifam.mem_prod (A : Ifam α) (B : Ifam β) a b :
    ((a, b) ∈ A ×ᴵ B) = (a ∈ A ∧ b ∈ B) := by
  apply propext; constructor;
  · rintro ⟨⟨i, j⟩, eq⟩; have ⟨rfl, rfl⟩ := Prod.mk_inj.mp eq; and_intros;
    { exists i }; { exists j }
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩; exists (i, j)

@[simp] protected lemma Mset.mem_prod (A : Mset α) (B : Mset β) a b :
    ((a, b) ∈ A ×ᴹ B) = (a ∈ A ∧ b ∈ B) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Ifam.mem_prod

@[simp] protected lemma Mset.mem_seq (F : Mset (α → β)) (A : Mset α) b :
    (b ∈ F <*>ᴹ A) = ∃ f ∈ F, ∃ a ∈ A, f a = b := by
  rw [Mset.seq]; simp only [Mset.mem_map, Prod.exists, Mset.mem_prod]; grind only

@[simp] protected lemma Mset.mem_join (A : Mset (Mset α)) a :
    (a ∈ Mset.join A) = ∃ B ∈ A, a ∈ B := by
  revert A; apply Quotient.ind; intro A;
  rw [Mset.join, Quotient.lift_mk, Ifam.join, Mset.mem_bigsum]; apply propext; constructor;
  · rintro ⟨i, _⟩; exists A.elem i; and_intros; { exists i }; { assumption }
  · rintro ⟨_, ⟨i, rfl⟩, mem⟩; exists i

@[simp] protected lemma Mset.mem_bind (A : Mset α) (K : α → Mset β) b :
    (b ∈ A >>=ᴹ K) = ∃ a ∈ A, b ∈ K a := by
  rw [Mset.bind]; simp only [Mset.mem_map, Mset.mem_join]; grind only
