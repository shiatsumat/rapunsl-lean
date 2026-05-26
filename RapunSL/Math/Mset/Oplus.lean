module

public import RapunSL.Math.Mset.Core
open Ifam Mset

@[expose] public section

/-! # Sum of multisets -/

/-! ## Binary sum -/

/-- Sum of two indexed families -/
protected def Ifam.oplus {α} (A B : Ifam α) : Ifam α :=
  .mk (A.dom ⊕ B.dom) (fun s => s.casesOn A.elem B.elem)

@[inherit_doc]
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
protected def Mset.oplus {α} : Mset α → Mset α → Mset α :=
  .lift₂ (⟦ · ⊕ᴵ · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.oplus_proper <;> tauto

@[inherit_doc]
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

/-! ### `⊕` is associative -/

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

@[inherit_doc]
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
protected noncomputable def Mset.bigoplus {ι : Type} (A : ι → Mset α) : Mset α :=
  ⟦ ⨁ᴵ i, (A i).out ⟧

@[inherit_doc]
scoped[Mset] notation "⨁ᴹ " i ", " A => Mset.bigoplus (fun i => A)

/-! ### `map` over `bigoplus` -/

protected lemma Ifam.bigoplus_map' (f : α → β) (A : ι → Ifam α) :
    f <$>ᴵ Ifam.bigoplus A = ⨁ᴵ i, f <$>ᴵ A i := rfl

protected lemma Mset.bigoplus_map' (f : α → β) (A : ι → Mset α) :
    f <$>ᴹ Mset.bigoplus A = ⨁ᴹ i, f <$>ᴹ A i := by
  apply Quotient.sound; rw [Ifam.bigoplus_map']; gcongr with i; simp only;
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

protected lemma Ifam.empty_as_bigoplus : ∅ ≈ Ifam.bigoplus (ι := Empty) A := by
  exists Equiv.equivOfIsEmpty _ _; nofun

protected lemma Mset.empty_as_bigoplus : ∅ = Mset.bigoplus (ι := Empty) (α := α) nofun := by
  apply Quotient.sound; apply Ifam.empty_as_bigoplus

/-! ### Unary `bigoplus` -/

protected lemma Ifam.unary_bigoplus (A : Unit → Ifam α) : Ifam.bigoplus A ≈ A () := by
  exists Equiv.uniqueSigma _; intro _; rfl

protected lemma Mset.unary_bigoplus (A : Unit → Mset α) : Mset.bigoplus A = A () := by
  cases eq : A () using Quotient.ind; apply Quotient.sound;
  grw [Ifam.unary_bigoplus, eq, Quotient.mk_out]

/-! ### `⊕` as `bigoplus` -/

protected lemma Ifam.oplus_as_bigoplus (A B : Ifam α) :
    F true = A → F false = B → A ⊕ᴵ B ≈ Ifam.bigoplus F := by
  intro rfl rfl;
  exists { toFun := fun | .inl i => ⟨true, i⟩ | .inr i => ⟨false, i⟩,
           invFun := fun | ⟨true, i⟩ => .inl i | ⟨false, i⟩ => .inr i,
           left_inv := by rintro (_ | _) <;> rfl,
           right_inv := by rintro ⟨_ | _, _⟩ <;> rfl };
  rintro (_ | _) <;> rfl

protected lemma Mset.oplus_as_bigoplus (A B : Mset α) :
    A ⊕ᴹ B = ⨁ᴹ (b : Bool), if b then A else B := by
  rw (occs := [1]) [←Quotient.out_eq A, ←Quotient.out_eq B];
  apply Quotient.sound; apply Ifam.oplus_as_bigoplus <;> rfl

/-! ## Membership -/

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

/-! ## Inhabitance -/

@[simp] protected lemma Mset.inhab_oplus (A B : Mset α) :
    (A ⊕ᴹ B).inhab = (A.inhab ∨ B.inhab) := by
  simp only [Mset.inhab, Mset.mem_oplus]; grind only

@[simp] protected lemma Mset.inhab_bigoplus {ι : Type} (A : ι → Mset α) :
    (⨁ᴹ i, A i).inhab = ∃ i, (A i).inhab := by
  simp only [Mset.inhab, Mset.mem_bigoplus]; grind only
