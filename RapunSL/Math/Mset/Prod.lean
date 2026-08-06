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

/-- The index domain of `×ᴵ` -/
@[simp] protected lemma Ifam.prod_dom (A : Ifam α) (B : Ifam β) :
    (A ×ᴵ B).dom = (A.dom × B.dom) := rfl

/-- The elements of `×ᴵ` -/
@[simp] protected lemma Ifam.prod_elem (A : Ifam α) (B : Ifam β) i j :
  (A ×ᴵ B).elem (i, j) = (A.elem i, B.elem j) := rfl

/-- `×ᴵ` respects `≈` -/
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

/-- Pull `<$>ᴹ` out of both operands of `×ᴹ` -/
protected lemma Mset.prod_map'
    (f : α → α') (g : β → β') (A : Mset α) (B : Mset β) :
    (f <$>ᴹ A) ×ᴹ (g <$>ᴹ B) = Prod.map f g <$>ᴹ (A ×ᴹ B) := by
  cases A using Quotient.ind; cases B using Quotient.ind; rfl

/-- Pull `<$>` out of both operands of `×ᴹ` -/
protected lemma Mset.prod_map (f : α → α') (g : β → β') (A : Mset α) (B : Mset β) :
    (f <$> A) ×ᴹ (g <$> B) = Prod.map f g <$> (A ×ᴹ B) := by apply Mset.prod_map'

/-- Pull `<$>ᴹ` out of the left operand of `×ᴹ` -/
protected lemma Mset.prod_map'_l (f : α → α') (A : Mset α) (B : Mset β) :
    (f <$>ᴹ A) ×ᴹ B = Prod.map f id <$>ᴹ (A ×ᴹ B) := by
  rw [←Mset.prod_map', Mset.id_map]

/-- Pull `<$>` out of the left operand of `×ᴹ` -/
protected lemma Mset.prod_map_l (f : α → α') (A : Mset α) (B : Mset β) :
    (f <$> A) ×ᴹ B = Prod.map f id <$> (A ×ᴹ B) := by apply Mset.prod_map'_l

/-- Pull `<$>ᴹ` out of the right operand of `×ᴹ` -/
protected lemma Mset.prod_map'_r (g : β → β') (A : Mset α) (B : Mset β) :
    A ×ᴹ (g <$>ᴹ B) = Prod.map id g <$>ᴹ (A ×ᴹ B) := by
  rw [←Mset.prod_map', Mset.id_map]

/-- Pull `<$>` out of the right operand of `×ᴹ` -/
protected lemma Mset.prod_map_r (g : β → β') (A : Mset α) (B : Mset β) :
    A ×ᴹ (g <$> B) = Prod.map id g <$> (A ×ᴹ B) := by apply Mset.prod_map'_r

/-! ## `×` is commutative -/

/-- `×ᴵ` is commutative up to `Prod.swap` -/
protected lemma Ifam.prod_comm (A : Ifam α) (B : Ifam β) :
    A ×ᴵ B ≈ Prod.swap <$>ᴵ (B ×ᴵ A) := by
  exists Equiv.prodComm _ _; tauto

/-- `×ᴹ` is commutative up to `Prod.swap` -/
protected lemma Mset.prod_comm (A : Mset α) (B : Mset β) :
    A ×ᴹ B = Prod.swap <$>ᴹ (B ×ᴹ A) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_comm

/-! ## `*` is unital -/

/-- `pure` is a right identity for `×ᴵ`, up to `<$>ᴵ` -/
protected lemma Ifam.prod_id_r (A : Ifam α) (b : β) :
    A ×ᴵ pure b ≈ (·, b) <$>ᴵ A := by
  exists Equiv.prodPUnit _; intro _; rfl

/-- `pure` is a right identity for `×ᴹ`, up to `<$>ᴹ` -/
protected lemma Mset.prod_id_r (A : Mset α) (b : β) :
    A ×ᴹ pure b = (·, b) <$>ᴹ A := by
  cases A using Quotient.ind; apply Quotient.sound;
  apply Ifam.prod_id_r

/-- `pure` is a left identity for `×ᴹ`, up to `<$>ᴹ` -/
protected lemma Mset.prod_id_l (a : α) (B : Mset β) :
    pure a ×ᴹ B = (a, ·) <$>ᴹ B := by
  rw [Mset.prod_comm, Mset.prod_id_r, ←Mset.comp_map]; rfl

/-! ## `*` is associative -/

/-- `×ᴵ` is associative, up to `<$>ᴵ`: left-nested from right-nested -/
protected lemma Ifam.prod_assoc_l (A : Ifam α) (B : Ifam β) (C : Ifam γ) :
    (A ×ᴵ B) ×ᴵ C ≈ (fun (a, (b, c)) => ((a, b), c)) <$>ᴵ (A ×ᴵ (B ×ᴵ C)) := by
  exists Equiv.prodAssoc _ _ _; intro _; rfl

/-- `×ᴹ` is associative, up to `<$>ᴹ`: left-nested from right-nested -/
protected lemma Mset.prod_assoc_l (A : Mset α) (B : Mset β) (C : Mset γ) :
    (A ×ᴹ B) ×ᴹ C = (fun (a, (b, c)) => ((a, b), c)) <$>ᴹ (A ×ᴹ (B ×ᴹ C)) := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_assoc_l

/-- `×ᴹ` is associative, up to `<$>ᴹ`: right-nested from left-nested -/
protected lemma Mset.prod_assoc_r (A : Mset α) (B : Mset β) (C : Mset γ) :
    A ×ᴹ (B ×ᴹ C) = (fun ((a, b), c) => (a, b, c)) <$>ᴹ ((A ×ᴹ B) ×ᴹ C) := by
  rw [Mset.prod_assoc_l, ←Mset.comp_map]; rw (occs := [1]) [←Mset.id_map (_ ×ᴹ _)]; rfl

/-! ## `*` distributes over `⊕` -/

/-- `×ᴵ` distributes over `⨁ᴵ` from the left -/
protected lemma Ifam.prod_bigoplus_l (A : Ifam α) (B : ι → Ifam β) :
    A ×ᴵ (⨁ᴵ i, B i) ≈ ⨁ᴵ i, A ×ᴵ B i := by
  exists { toFun := fun ⟨a, ⟨i, b⟩⟩ => ⟨i, (a, b)⟩,
           invFun := fun ⟨i, ⟨a, b⟩⟩ => ⟨a, ⟨i, b⟩⟩,
           left_inv := by tauto, right_inv := by tauto };
  intro _; rfl

/-- `×ᴹ` distributes over `⨁ᴹ` from the left -/
protected lemma Mset.prod_bigoplus_l (A : Mset α) (B : ι → Mset β) :
    A ×ᴹ (⨁ᴹ i, B i) = ⨁ᴹ i, A ×ᴹ B i := by
  cases A using Quotient.ind; apply Quotient.sound; grw [Ifam.prod_bigoplus_l];
  gcongr with i; simp only; cases B i using Quotient.ind;
  grw [Quotient.mk_out]; symm; apply Quotient.mk_out

/-- `×ᴹ` distributes over `⨁ᴹ` from the right -/
protected lemma Mset.prod_bigoplus_r (A : ι → Mset α) (B : Mset β) :
    (⨁ᴹ i, A i) ×ᴹ B = ⨁ᴹ i, A i ×ᴹ B := by
  rw [Mset.prod_comm, Mset.prod_bigoplus_l, Mset.bigoplus_map'];
  congr; ext1 _; rw [←Mset.prod_comm]

/-- `×ᴹ` distributes over `⊕ᴹ` from the left -/
protected lemma Mset.prod_oplus_l (A : Mset α) (B C : Mset β) :
    A ×ᴹ (B ⊕ᴹ C) = A ×ᴹ B ⊕ᴹ A ×ᴹ C := by
  simp only [Mset.oplus_as_bigoplus, Mset.prod_bigoplus_l]; grind only

/-- `×ᴹ` distributes over `⊕ᴹ` from the right -/
protected lemma Mset.prod_oplus_r (A B : Mset α) (C : Mset β) :
    (A ⊕ᴹ B) ×ᴹ C = A ×ᴹ C ⊕ᴹ B ×ᴹ C := by
  simp only [Mset.oplus_as_bigoplus, Mset.prod_bigoplus_r]; grind only

/-- `∅` annihilates `×ᴹ` in the right operand -/
protected lemma Mset.prod_empty_l (A : Mset α) : A ×ᴹ (∅ : Mset β) = ∅ := by
  simp only [Mset.empty_as_bigoplus, Mset.prod_bigoplus_l]; congr; ext1 _; trivial

/-- `∅` annihilates `×ᴹ` in the left operand -/
protected lemma Mset.prod_empty_r (A : Mset α) : (∅ : Mset α) ×ᴹ A = ∅ := by
  simp only [Mset.empty_as_bigoplus, Mset.prod_bigoplus_r]; congr; ext1 _; trivial

/-! ## Membership -/

/-- Membership for `×ᴵ` -/
@[simp] protected lemma Ifam.prod_mem (A : Ifam α) (B : Ifam β) p :
    p ∈ A ×ᴵ B ↔ p.1 ∈ A ∧ p.2 ∈ B := by
  cases p; constructor;
  · rintro ⟨⟨_, _⟩, eq⟩; have ⟨rfl, rfl⟩ := Prod.mk_inj.mp eq; tauto
  · rintro ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩; tauto

/-- Membership for `×ᴹ` -/
@[simp] protected lemma Mset.prod_mem (A : Mset α) (B : Mset β) p :
    p ∈ A ×ᴹ B ↔ p.1 ∈ A ∧ p.2 ∈ B := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Ifam.prod_mem

/-! ## Inhabitedness -/

/-- Inhabitedness for `×ᴹ` -/
@[simp] protected lemma Mset.inhab_prod (A : Mset α) (B : Mset β) :
    (A ×ᴹ B).inhab ↔ A.inhab ∧ B.inhab := by
  simp only [Mset.inhab, Mset.prod_mem]; constructor; { tauto };
  intro ⟨⟨a, _⟩, ⟨b, _⟩⟩; exists (a, b)

/-! ## Pair membership -/

/-- Pair membership for `×ᴵ` -/
@[simp] protected lemma Ifam.prod_pairmem (A : Ifam α) (B : Ifam β) p q :
    (A ×ᴵ B).pairmem p q ↔
      (A.pairmem p.1 q.1 ∧ B.pairmem p.2 q.2) ∨
       (p.1 = q.1 ∧ p.1 ∈ A ∧ B.pairmem p.2 q.2) ∨
       (p.2 = q.2 ∧ p.2 ∈ B ∧ A.pairmem p.1 q.1) := by
  constructor;
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, _, rfl, rfl⟩;
    rcases Classical.em (i = i') with rfl | _;
    { right; left; constructor; { rfl }; and_intros; { exists i }; exists j, j'; aesop };
    rcases Classical.em (j = j') with rfl | _;
    { right; right; constructor; { rfl }; and_intros; { exists j }; exists i, i' };
    left; and_intros; { exists i, i' }; { exists j, j' }
  · cases p; cases q;
    rintro (⟨⟨i, i', _, rfl, rfl⟩, ⟨j, j', _, rfl, rfl⟩⟩ |
      ⟨rfl, ⟨i, rfl⟩, ⟨j, j', _, rfl, rfl⟩⟩ | ⟨rfl, ⟨j, rfl⟩, ⟨i, i', _, rfl, rfl⟩⟩);
    { exists (i, j), (i', j'); aesop };
    { exists (i, j), (i, j'); aesop }; { exists (i, j), (i', j); aesop }

/-- Pair membership for `×ᴹ` -/
@[simp] protected lemma Mset.prod_pairmem (A : Mset α) (B : Mset β) p q :
    (A ×ᴹ B).pairmem p q ↔
      (A.pairmem p.1 q.1 ∧ B.pairmem p.2 q.2) ∨
       (p.1 = q.1 ∧ p.1 ∈ A ∧ B.pairmem p.2 q.2) ∨
       (p.2 = q.2 ∧ p.2 ∈ B ∧ A.pairmem p.1 q.1) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Ifam.prod_pairmem

/-! ## Bijection -/

/-- Bijection for `×ᴵ` -/
protected def Ifam.Bij.prod {A : Ifam α} {B : Ifam β} {A' : Ifam α'} {B' : Ifam β'}
    (r : A ≃ᴵ A') (s : B ≃ᴵ B') : A ×ᴵ B ≃ᴵ A' ×ᴵ B' :=
  Equiv.prodCongr r s

/-- Bijection for `×ᴹ` -/
protected noncomputable def Mset.Bij.prod {A : Mset α} {B : Mset β} {A' : Mset α'} {B' : Mset β'}
    (r : A ≃ᴹ A') (s : B ≃ᴹ B') : A ×ᴹ B ≃ᴹ A' ×ᴹ B' :=
  A.out_eq ▸ B.out_eq ▸ A'.out_eq ▸ B'.out_eq ▸ Ifam.Bij.lift_mk (Ifam.Bij.prod r s)

/-- The graph of `Ifam.Bij.prod` -/
protected lemma Ifam.Bij.prod_graph
    {A : Ifam α} {B : Ifam β} {A' : Ifam α'} {B' : Ifam β'} (r : A ≃ᴵ A') (s : B ≃ᴵ B') :
    (Ifam.Bij.prod r s).graph =
      (fun ((a, a'), (b, b')) => ((a, b), (a', b'))) <$>ᴵ (r.graph ×ᴵ s.graph) := rfl

/-- The graph of `Mset.Bij.prod` -/
protected lemma Mset.Bij.prod_graph
    {A : Mset α} {B : Mset β} {A' : Mset α'} {B' : Mset β'} (r : A ≃ᴹ A') (s : B ≃ᴹ B') :
    (Mset.Bij.prod r s).graph =
      (fun ((a, a'), (b, b')) => ((a, b), (a', b'))) <$>ᴹ (r.graph ×ᴹ s.graph) := by
  rw [Mset.Bij.prod]; revert r s; unfold Mset.Bij Mset.Bij.graph;
  simp_out_eq A; simp_out_eq B; simp_out_eq A'; simp_out_eq B'; intro r s;
  trans; { apply Ifam.Bij.lift_mk_graph }; rw [Ifam.Bij.prod_graph]; rfl

/-- Membership for the graph of `Mset.Bij.prod` -/
@[simp] protected lemma Mset.Bij.prod_graph_mem
    {A : Mset α} {B : Mset β} {A' : Mset α'} {B' : Mset β'} (r : A ≃ᴹ A') (s : B ≃ᴹ B') a a' b b' :
    ((a, b), (a', b')) ∈ (Mset.Bij.prod r s).graph ↔
      (a, a') ∈ r.graph ∧ (b, b') ∈ s.graph := by
  simp only [Mset.Bij.prod_graph, Mset.map'_mem, Mset.prod_mem]; aesop

/-- Cancel a common left factor with pairwise-distinct elements out of a bijection
  between products whose graph preserves the first component -/
protected lemma Ifam.Bij.prod_cancel_l {A : Ifam α} {B C : Ifam β}
    (r : A ×ᴵ B ≃ᴵ A ×ᴵ C) (i₀ : A.dom) :
    (∀ a a', A.pairmem a a' → a ≠ a') →
    (∀ a b a' c, ((a, b), (a', c)) ∈ r.graph → a = a') →
    ∃ s : B ≃ᴵ C, ∀ b c, (b, c) ∈ s.graph →
      ((A.elem i₀, b), (A.elem i₀, c)) ∈ r.graph := by
  intro ne eq;
  have fst_eq : ∀ p : (A ×ᴵ B).dom, r p = (p.1, (r p).2) := by
    intro p;
    have mem : ((A.elem p.1, B.elem p.2), (A.elem (r p).1, C.elem (r p).2)) ∈ r.graph :=
      ⟨p, rfl⟩
    have eq' : (r p).1 = p.1 := by
      by_contra ne';
      exact ne _ _ ⟨p.1, (r p).1, fun h => ne' h.symm, rfl, rfl⟩ (eq _ _ _ _ mem)
    rw [←eq']; rfl
  have fst_eq' : ∀ q : (A ×ᴵ C).dom, r.symm q = (q.1, (r.symm q).2) := by
    intro q; have h := fst_eq (r.symm q); rw [Equiv.apply_symm_apply] at h;
    rw [congrArg Prod.fst h]; rfl
  refine ⟨⟨fun j => (r (i₀, j)).2, fun k => (r.symm (i₀, k)).2, ?_, ?_⟩, ?_⟩
  · intro j; have h := congrArg r.symm (fst_eq (i₀, j)).symm;
    rw [Equiv.symm_apply_apply] at h; exact congrArg Prod.snd h
  · intro k; have h := congrArg r (fst_eq' (i₀, k)).symm;
    rw [Equiv.apply_symm_apply] at h; exact congrArg Prod.snd h
  · rintro b c ⟨j, ej⟩;
    have eb : B.elem j = b := congrArg Prod.fst ej
    have ec : C.elem (r (i₀, j)).2 = c := congrArg Prod.snd ej
    refine ⟨(i₀, j), ?_⟩; rw [←eb, ←ec];
    exact congrArg (fun q => ((A.elem i₀, B.elem j), (A ×ᴵ C).elem q)) (fst_eq (i₀, j))

/-- Cancel a common left factor with pairwise-distinct elements out of a bijection
  between products whose graph preserves the first component -/
protected lemma Mset.Bij.prod_cancel_l {A : Mset α} {B C : Mset β}
    (r : A ×ᴹ B ≃ᴹ A ×ᴹ C) {a₀ : α} :
    a₀ ∈ A → (∀ a a', A.pairmem a a' → a ≠ a') →
    (∀ a b a' c, ((a, b), (a', c)) ∈ r.graph → a = a') →
    ∃ s : B ≃ᴹ C, ∀ b c, (b, c) ∈ s.graph → ((a₀, b), (a₀, c)) ∈ r.graph := by
  intro mem ne eq;
  have eAB : (A ×ᴹ B).out ≈ A.out ×ᴵ B.out := by
    apply Quotient.exact; rw [Mset.out_eq];
    rw (occs := [1]) [←A.out_eq]; rw (occs := [1]) [←B.out_eq]; rfl
  have eAC : (A ×ᴹ C).out ≈ A.out ×ᴵ C.out := by
    apply Quotient.exact; rw [Mset.out_eq];
    rw (occs := [1]) [←A.out_eq]; rw (occs := [1]) [←C.out_eq]; rfl
  let r' : A.out ×ᴵ B.out ≃ᴵ A.out ×ᴵ C.out :=
    (Ifam.Bij.lift_equiv eAB).symm.trans (Ifam.Bij.trans r (Ifam.Bij.lift_equiv eAC))
  have hg : Ifam.Bij.graph r' ≈ Ifam.Bij.graph r := by
    have hg2 : (Ifam.Bij.trans r (Ifam.Bij.lift_equiv eAC)).graph = Ifam.Bij.graph r := by
      apply Ifam.Bij.trans_graph_id_r; intro _ _ mem';
      rw [Ifam.Bij.lift_equiv_graph_mem] at mem'; exact mem'.1
    rw [←hg2]; apply Ifam.Bij.trans_graph_id_l; intro _ _ mem';
    rw [Ifam.Bij.symm_graph_mem, Ifam.Bij.lift_equiv_graph_mem] at mem'; exact mem'.1.symm
  have hmem : ∀ p, p ∈ Ifam.Bij.graph r' ↔ p ∈ r.graph :=
    fun _ => iff_of_eq (Ifam.mem_proper _ _ hg)
  rw [←Mset.out_mem] at mem; rcases mem with ⟨i₀, hi₀⟩;
  rcases Ifam.Bij.prod_cancel_l r' i₀
    (by intro a a' pm; apply ne; rw [←Mset.out_pairmem]; exact pm)
    (fun a b a' c mem' => eq a b a' c ((hmem _).mp mem')) with ⟨s, hs⟩
  exact ⟨s, fun b c mem' => (hmem _).mp (hi₀ ▸ hs b c mem')⟩
