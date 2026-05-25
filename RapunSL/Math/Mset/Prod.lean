module

public import RapunSL.Math.Mset.Oplus
open Ifam Mset

@[expose] public section

/-! # Binary product of multisets -/

/-! ## Binary product of multisets -/

/-- Product of two indexed families -/
protected def Ifam.prod {α β} (A : Ifam α) (B : Ifam β) : Ifam (α × β) :=
  .mk (A.dom × B.dom) (fun (i, j) => (A.elem i, B.elem j))

@[inherit_doc]
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

@[inherit_doc]
scoped[Mset] infixr:69 " ×ᴹ " => Mset.prod

/-! ## `×` over `map` -/

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

/-! ## `×` is commutative -/

protected lemma Ifam.prod_comm (A : Ifam α) (B : Ifam β) :
    A ×ᴵ B ≈ Prod.swap <$>ᴵ (B ×ᴵ A) := by
  exists Equiv.prodComm _ _; tauto

protected lemma Mset.prod_comm (A : Mset α) (B : Mset β) :
    A ×ᴹ B = Prod.swap <$>ᴹ (B ×ᴹ A) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_comm

/-! ## `*` is unital -/

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

/-! ## `*` is associative -/

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

/-! ## `*` distributes over `⊕` -/

protected lemma Ifam.prod_bigoplus_l (A : Ifam α) (B : ι → Ifam β) :
    (A ×ᴵ ⨁ᴵ i, B i) ≈ ⨁ᴵ i, A ×ᴵ B i := by
  exists { toFun := fun ⟨a, ⟨i, b⟩⟩ => ⟨i, (a, b)⟩,
           invFun := fun ⟨i, ⟨a, b⟩⟩ => ⟨a, ⟨i, b⟩⟩,
           left_inv := by tauto, right_inv := by tauto };
  intro _; rfl

protected lemma Mset.prod_bigoplus_l (A : Mset α) (B : ι → Mset β) :
    A ×ᴹ (⨁ᴹ i, B i) = ⨁ᴹ i, A ×ᴹ B i := by
  cases A using Quotient.ind; apply Quotient.sound; grw [Ifam.prod_bigoplus_l];
  gcongr with i; simp only; cases B i using Quotient.ind;
  grw [Quotient.mk_out]; symm; apply Quotient.mk_out

protected lemma Mset.prod_bigoplus_r (A : ι → Mset α) (B : Mset β) :
    (⨁ᴹ i, A i) ×ᴹ B = ⨁ᴹ i, A i ×ᴹ B := by
  rw [Mset.prod_comm, Mset.prod_bigoplus_l, Mset.bigoplus_map'];
  congr; ext1 _; rw [←Mset.prod_comm]

protected lemma Mset.prod_oplus_l (A : Mset α) (B C : Mset β) :
    A ×ᴹ (B ⊕ᴹ C) = A ×ᴹ B ⊕ᴹ A ×ᴹ C := by
  simp only [Mset.oplus_as_bigoplus, Mset.prod_bigoplus_l]; grind only

protected lemma Mset.prod_oplus_r (A B : Mset α) (C : Mset β) :
    (A ⊕ᴹ B) ×ᴹ C = A ×ᴹ C ⊕ᴹ B ×ᴹ C := by
  simp only [Mset.oplus_as_bigoplus, Mset.prod_bigoplus_r]; grind only

protected lemma Mset.prod_empty_l (A : Mset α) : A ×ᴹ (∅ : Mset β) = ∅ := by
  simp only [Mset.empty_as_bigoplus, Mset.prod_bigoplus_l]; congr; ext1 _; trivial

protected lemma Mset.prod_empty_r (A : Mset α) : (∅ : Mset α) ×ᴹ A = ∅ := by
  simp only [Mset.empty_as_bigoplus, Mset.prod_bigoplus_r]; congr; ext1 _; trivial

/-! ## Membership -/

@[simp] protected lemma Ifam.mem_prod (A : Ifam α) (B : Ifam β) p :
    (p ∈ A ×ᴵ B) = (p.1 ∈ A ∧ p.2 ∈ B) := by
  cases p; ext1; constructor;
  · rintro ⟨⟨_, _⟩, eq⟩; have ⟨rfl, rfl⟩ := Prod.mk_inj.mp eq; tauto
  · rintro ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩; tauto

@[simp] protected lemma Mset.mem_prod (A : Mset α) (B : Mset β) p :
    (p ∈ A ×ᴹ B) = (p.1 ∈ A ∧ p.2 ∈ B) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Ifam.mem_prod

/-! ## Inhabitance -/

@[simp] protected lemma Mset.inhab_prod (A : Mset α) (B : Mset β) :
    (A ×ᴹ B).inhab = (A.inhab ∧ B.inhab) := by
  simp only [Mset.inhab, Mset.mem_prod]; ext1; constructor; { tauto };
  intro ⟨⟨a, _⟩, ⟨b, _⟩⟩; exists (a, b)
