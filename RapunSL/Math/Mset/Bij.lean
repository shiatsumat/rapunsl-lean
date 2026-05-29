module

public import RapunSL.Math.Mset.Core
open Ifam Mset

@[expose] public section

/-! # Multiset bijection -/

/-! ## Definition -/

/-- Bijection between indexed families -/
protected abbrev Ifam.Bij {α β} (A : Ifam α) (B : Ifam β) : Type :=
  A.dom ≃ B.dom

@[inherit_doc]
scoped[Ifam] infixl:25 " ≃ᴵ " => Ifam.Bij

/-- Bijection between multisets -/
protected abbrev Mset.Bij (A : Mset α) (B : Mset β) : Type :=
  A.out ≃ᴵ B.out

@[inherit_doc]
scoped[Mset] infixl:25 " ≃ᴹ " => Mset.Bij

/-! ## Basic constructions -/

/-- Reflexivity -/
protected abbrev Ifam.Bij.refl (A : Ifam α) : A ≃ᴵ A :=
  Equiv.refl _

/-- Reflexivity -/
protected abbrev Mset.Bij.refl (A : Mset α) : A ≃ᴹ A :=
  Equiv.refl _

/-- Symmetry -/
protected abbrev Ifam.Bij.symm {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) : B ≃ᴵ A :=
  Equiv.symm r

/-- Symmetry -/
protected abbrev Mset.Bij.symm {A : Mset α} {B : Mset β} (r : A ≃ᴹ B) : B ≃ᴹ A :=
  Equiv.symm r

/-- Transitivity -/
protected abbrev Ifam.Bij.trans {A : Ifam α} {B : Ifam β} {C : Ifam γ}
    (r : A ≃ᴵ B) (s : B ≃ᴵ C) : A ≃ᴵ C :=
  Equiv.trans r s

/-- Transitivity -/
protected abbrev Mset.Bij.trans {A : Mset α} {B : Mset β} {C : Mset γ}
    (r : A ≃ᴹ B) (s : B ≃ᴹ C) : A ≃ᴹ C :=
  Equiv.trans r s

/-! ## Lifting constructions -/

/-- Lift `≈` into `≃ᴵ` -/
protected noncomputable def Ifam.Bij.lift_equiv {A B : Ifam α} :
  A ≈ B → A ≃ᴵ B := Classical.choose

/-- `≃ᴵ` for ⟦ ⟧.out -/
protected noncomputable def Ifam.Bij.mk_out (A : Ifam α) :
    (⟦ A ⟧ : Mset α).out ≃ᴵ A := Ifam.Bij.lift_equiv (Quotient.mk_out A)

/-- Lift `≃ᴵ` into `≃ᴹ` -/
protected noncomputable def Ifam.Bij.lift_mk {A : Ifam α} {B : Ifam β}
    (r : A ≃ᴵ B) : ⟦ A ⟧ ≃ᴹ ⟦ B ⟧ :=
  (Ifam.Bij.mk_out A).trans <| r.trans (Ifam.Bij.mk_out B).symm

/-! ## Graph -/

/-- Indexed family graph for `≃ᴵ` -/
protected def Ifam.Bij.graph {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) : Ifam (α × β) :=
  .mk A.dom (fun i => (A.elem i, B.elem (r i)))

/-- Multiset graph for `≃ᴹ` -/
protected noncomputable def Mset.Bij.graph {A : Mset α} {B : Mset β}
    (r : A ≃ᴹ B) : Mset (α × β) :=
  ⟦ Ifam.Bij.graph r ⟧

/-! ### Projection of the graph -/

/-- Left projection of the graph -/
@[simp] protected lemma Ifam.Bij.graph_fst {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) :
    Prod.fst <$>ᴵ r.graph = A := rfl

/-- Left projection of the graph -/
@[simp] protected lemma Mset.Bij.graph_fst {A : Mset α} {B : Mset β} (r : A ≃ᴹ B) :
    Prod.fst <$>ᴹ r.graph = A := by
  rw (occs := [2]) [←A.out_eq]; apply Quotient.sound; exists Equiv.refl _; tauto

/-- Right projection of the graph -/
@[simp] protected lemma Ifam.Bij.graph_snd {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) :
    Prod.snd <$>ᴵ r.graph ≈ B := by
  exists r; tauto

/-- Right projection of the graph -/
@[simp] protected lemma Mset.Bij.graph_snd {A : Mset α} {B : Mset β} (r : A ≃ᴹ B) :
    Prod.snd <$>ᴹ r.graph = B := by
  rw (occs := [2]) [←B.out_eq]; apply Quotient.sound; apply Ifam.Bij.graph_snd

/-! ### The graph of `refl` and `symm` -/

/-- The graph of `Ifam.Bij.refl` -/
@[simp] protected lemma Ifam.Bij.refl_graph (A : Ifam α) :
    (Ifam.Bij.refl A).graph = (fun a => (a, a)) <$>ᴵ A := rfl

/-- The graph of `Mset.Bij.refl` -/
@[simp] protected lemma Mset.Bij.refl_graph (A : Mset α) :
    (Mset.Bij.refl A).graph = (fun a => (a, a)) <$>ᴹ A := by
  rw (occs := [4]) [←A.out_eq]; rfl

/-- The graph of `Ifam.Bij.symm` -/
@[simp] protected lemma Ifam.Bij.symm_graph {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) :
    r.symm.graph ≈ (fun (a, b) => (b, a)) <$>ᴵ r.graph := by
  exists r.symm; intro i; simp only [Ifam.Bij.graph, Ifam.map]; congr; symm;
  apply Equiv.apply_symm_apply

/-- The graph of `Mset.Bij.symm` -/
@[simp] protected lemma Mset.Bij.symm_graph {A : Mset α} {B : Mset β} (r : A ≃ᴹ B) :
    r.symm.graph = (fun (a, b) => (b, a)) <$>ᴹ r.graph := by
  apply Quotient.sound; apply Ifam.Bij.symm_graph

/-! ### The graph of `trans` -/

/-- Membership of the graph of `Mset.Bij.trans` -/
protected lemma Mset.Bij.trans_graph_mem {A : Mset α} {B : Mset β} {C : Mset γ}
    (r : A ≃ᴹ B) (s : B ≃ᴹ C) a c :
    (a, c) ∈ (r.trans s).graph → ∃ b, (a, b) ∈ r.graph ∧ (b, c) ∈ s.graph := by
  rintro ⟨i, _, _⟩; exists B.out.elem (r i); and_intros;
  { exists i; }; { exists r i }

/-- The graph of `Ifam.Bij.trans` with a bijection of a map-like graph -/
protected lemma Ifam.Bij.trans_graph_map_l {A : Ifam α} {B B' : Ifam β} {C : Ifam γ}
    (r : A ≃ᴵ B) (s : B ≃ᴵ C) (f : β → α) :
    r.graph ≈ (fun b => (f b, b)) <$>ᴵ B' →
    (r.trans s).graph ≈ (fun (b, c) => (f b, c)) <$>ᴵ s.graph := by
  intro ⟨_, eq⟩; exists r; intro i;
  simp only [Ifam.Bij.graph, Equiv.trans_apply, Ifam.map_elem] at *; congr;
  rcases Prod.ext_iff.mp (eq i) with ⟨eq, eq'⟩; simp only at *; rw [eq, ←eq']; rfl

/-- The graph of `Mset.Bij.trans` with a bijection of a map-like graph -/
protected lemma Mset.Bij.trans_graph_map_l {A : Mset α} {B B' : Mset β} {C : Mset γ}
    (r : A ≃ᴹ B) (s : B ≃ᴹ C) (f : β → α) :
    r.graph = (fun b => (f b, b)) <$>ᴹ B' →
    (r.trans s).graph = (fun (b, c) => (f b, c)) <$>ᴹ s.graph := by
  intro eq; apply Quotient.sound; cases B' using Quotient.ind;
  have eq := Quotient.exact eq; revert eq; apply Ifam.Bij.trans_graph_map_l

/-- The graph of `Ifam.Bij.trans` with a bijection of a map-like graph -/
protected lemma Ifam.Bij.trans_graph_map_r {A : Ifam α} {B B' : Ifam β} {C : Ifam γ}
    (r : A ≃ᴵ B) (s : B ≃ᴵ C) (f : β → γ) :
    s.graph ≈ (fun b => (b, f b)) <$>ᴵ B' →
    (r.trans s).graph = (fun (a, b) => (a, f b)) <$>ᴵ r.graph := by
  intro ⟨_, eq⟩; apply congr_arg (Ifam.mk _); ext1 i;
  simp only [Ifam.Bij.graph, Equiv.trans_apply, Ifam.map_elem] at *; congr;
  rcases Prod.ext_iff.mp (eq (r i)) with ⟨eq, eq'⟩; simp only at *; rw [eq', ←eq]

/-- The graph of `Mset.Bij.trans` with a bijection of a map-like graph -/
protected lemma Mset.Bij.trans_graph_map_r {A : Mset α} {B : Mset β} {C : Mset γ}
    (r : A ≃ᴹ B) (s : B ≃ᴹ C) (f : β → γ) B' :
    s.graph = (fun b => (b, f b)) <$>ᴹ B' →
    (r.trans s).graph = (fun (a, b) => (a, f b)) <$>ᴹ r.graph := by
  intro eq; apply congr_arg (Quotient.mk _); cases B' using Quotient.ind;
  have eq := Quotient.exact eq; revert eq; apply Ifam.Bij.trans_graph_map_r

/-- The graph of `Ifam.Bij.trans` with a bijection of an identity graph -/
protected lemma Ifam.Bij.trans_graph_id_l {A A' : Ifam α} {B : Ifam β}
    (r : A ≃ᴵ A') (s : A' ≃ᴵ B) A'' :
    r.graph ≈ (fun a => (a, a)) <$>ᴵ A'' → (r.trans s).graph ≈ s.graph := by
  rw [←Ifam.id_map s.graph]; apply Ifam.Bij.trans_graph_map_l

/-- The graph of `Mset.Bij.trans` with a bijection of an identity graph -/
protected lemma Mset.Bij.trans_graph_id_l {A A' : Mset α} {B : Mset β}
    (r : A ≃ᴹ A') (s : A' ≃ᴹ B) A'' :
    r.graph = (fun a => (a, a)) <$>ᴹ A'' → (r.trans s).graph = s.graph := by
  rw [←Mset.id_map s.graph]; apply Mset.Bij.trans_graph_map_l

/-- The graph of `Ifam.Bij.trans` with a bijection of an identity graph -/
protected lemma Ifam.Bij.trans_graph_id_r {A : Ifam α} {B B' : Ifam β}
    (r : A ≃ᴵ B) (s : B ≃ᴵ B') B'' :
    s.graph ≈ (fun b => (b, b)) <$>ᴵ B'' → (r.trans s).graph = r.graph := by
  rw [←Ifam.id_map r.graph]; apply Ifam.Bij.trans_graph_map_r

/-- The graph of `Mset.Bij.trans` with a bijection of an identity graph -/
protected lemma Mset.Bij.trans_graph_id_r {A : Mset α} {B B' : Mset β}
    (r : A ≃ᴹ B) (s : B ≃ᴹ B') B'' :
    s.graph = (fun b => (b, b)) <$>ᴹ B'' → (r.trans s).graph = r.graph := by
  rw [←Mset.id_map r.graph]; apply Mset.Bij.trans_graph_map_r

/-! ### The graph of lifting constructions -/

/-- The graph of `Ifam.Bij.lift_equiv` -/
protected lemma Ifam.Bij.lift_equiv_graph {A B : Ifam α} (e : A ≈ B) :
    (Ifam.Bij.lift_equiv e).graph = (fun a => (a, a)) <$>ᴵ A := by
  apply congr_arg (Ifam.mk _); ext1 i; ext1; { rfl }; symm; apply Classical.choose_spec e

/-- The graph of `Ifam.Bij.mk_out` -/
protected lemma Ifam.Bij.mk_out_graph (A : Ifam α) :
    (Ifam.Bij.mk_out A).graph = (fun a => (a, a)) <$>ᴵ (⟦ A ⟧ : Mset α).out := by
  rw [Ifam.Bij.mk_out, Ifam.Bij.lift_equiv_graph]

/-- The graph of `Ifam.Bij.lift_mk` -/
protected lemma Ifam.Bij.lift_mk_graph {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) :
    r.lift_mk.graph = ⟦ r.graph ⟧ := by
  apply Quotient.sound; rw [Ifam.Bij.lift_mk];
  rw [←Ifam.Bij.trans_graph_id_r r (Bij.mk_out B).symm (⟦ B ⟧ : Mset β).out];
  { apply Ifam.Bij.trans_graph_id_l; rw [Ifam.Bij.mk_out_graph] };
  trans; { apply Ifam.Bij.symm_graph }; rw [Ifam.Bij.mk_out_graph, ←Ifam.comp_map]; rfl

/-! ## Getting information from the graph -/

/-- Get `<$>ᴵ` information from a map-like graph -/
protected lemma Ifam.Bij.graph_eq_map {A A' : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) (f : α → β) :
    r.graph ≈ (fun a => (a, f a)) <$>ᴵ A' → B ≈ f <$>ᴵ A := by
  intro ⟨_, eq⟩; symm; exists r; intro i; rcases Prod.ext_iff.mp (eq i) with ⟨eq, eq'⟩;
  simp only [Ifam.Bij.graph, Ifam.map_elem] at *; rw [eq, ←eq']; rfl

/-- Get `<$>ᴹ` information from a map-like graph -/
protected lemma Mset.Bij.graph_eq_map {A A' : Mset α} {B : Mset β} (r : A ≃ᴹ B) (f : α → β) :
    r.graph = (fun a => (a, f a)) <$>ᴹ A' → B = f <$>ᴹ A := by
  rw (occs := [2]) [←A.out_eq, ←B.out_eq]; intro eq; apply Quotient.sound;
  cases A' using Quotient.ind; have eq := Quotient.exact eq; revert eq;
  apply Ifam.Bij.graph_eq_map

/-- Get equivalence from an identity graph -/
protected lemma Ifam.Bij.graph_eq {A A' : Ifam α} (r : A ≃ᴵ A') A'' :
    r.graph ≈ (fun a => (a, a)) <$>ᴵ A'' → A ≈ A' := by
  rw (occs := [2]) [←Ifam.id_map A]; intro eq; symm; revert eq;
  apply Ifam.Bij.graph_eq_map

/-- Get equality from an identity graph -/
protected lemma Mset.Bij.graph_eq {A A' : Mset α} (r : A ≃ᴹ A') A'' :
    r.graph = (fun a => (a, a)) <$>ᴹ A'' → A = A' := by
  rw (occs := [2]) [←Mset.id_map A]; intro eq; symm; revert eq;
  apply Mset.Bij.graph_eq_map

/-! ## Equality between bijections -/

/-- Equality between `≃ᴵ`s by negation of pair membership -/
protected lemma Ifam.Bij.eq_graph_no_pairmem {A : Ifam α} {B : Ifam β} (r s : A ≃ᴵ B) :
    (∀ a b b', (a, b) ∈ r.graph → (a, b') ∈ s.graph → ¬ B.pairmem b b') → r = s := by
  intro h; ext1 i; by_contra ne;
  apply h (A.elem i); { exists i }; { exists i }; { exists r i, s i }

/-- Equality between `≃ᴹ`s by negation of pair membership -/
protected lemma Mset.Bij.eq_graph_no_pairmem {A : Mset α} {B : Mset β} (r s : A ≃ᴹ B) :
    (∀ a b b', (a, b) ∈ r.graph → (a, b') ∈ s.graph → ¬ B.pairmem b b') → r = s := by
  intro h; apply Ifam.Bij.eq_graph_no_pairmem; intro _ _ _; rw [Mset.out_pairmem B]; tauto

/-- Uniqueness of `≃ᴵ` over `pure` -/
protected lemma Ifam.Bij.unique_pure {A : Ifam α} {b : β} (r s : A ≃ᴵ pure b) :
    r = s := by
  apply Ifam.Bij.eq_graph_no_pairmem; intro _ _ _; simp [Ifam.pure_pairmem]

/-- Uniqueness of `≃ᴹ` over `pure` -/
protected lemma Mset.Bij.unique_pure {A : Mset α} {b : β} (r s : A ≃ᴹ pure b) :
    r = s := by
  apply Mset.Bij.eq_graph_no_pairmem; intro _ _ _; simp [Mset.pure_pairmem]

/-- Uniqueness of `≃ᴵ` over `∅` -/
protected lemma Ifam.Bij.unique_empty {A : Ifam α} (r s : A ≃ᴵ (∅ : Ifam β)) :
    r = s := by
  apply Ifam.Bij.eq_graph_no_pairmem; intro _ _ _; simp [Ifam.empty_pairmem]

/-- Uniqueness of `≃ᴹ` over `∅` -/
protected lemma Mset.Bij.unique_empty {A : Mset α} (r s : A ≃ᴹ (∅ : Mset β)) :
    r = s := by
  apply Mset.Bij.eq_graph_no_pairmem; intro _ _ _; simp [Mset.empty_pairmem]

/-! ## Constructions for operators -/

/-! ### For `<$>` -/

/-- Left-hand bijection for `<$>ᴵ` -/
protected def Ifam.Bij.map_l (f : α → β) (A : Ifam α) : f <$>ᴵ A ≃ᴵ A :=
  Equiv.refl _

/-- Right-hand bijection for `<$>ᴵ` -/
protected def Ifam.Bij.map_r (f : α → β) (A : Ifam α) : A ≃ᴵ f <$>ᴵ A :=
  (Ifam.Bij.map_l f A).symm

/-- The graph of `Ifam.Bij.map_l` -/
@[simp] protected lemma Ifam.Bij.map_l_graph (f : α → β) (A : Ifam α) :
    (Ifam.Bij.map_l f A).graph = (fun a => (f a, a)) <$>ᴵ A := rfl

/-- The graph of `Ifam.Bij.map_r` -/
@[simp] protected lemma Ifam.Bij.map_r_graph (f : α → β) (A : Ifam α) :
    (Ifam.Bij.map_r f A).graph = (fun a => (a, f a)) <$>ᴵ A := rfl

/-- Left-hand bijection for `<$>ᴹ` -/
protected noncomputable def Mset.Bij.map_l (f : α → β) (A : Mset α) : f <$>ᴹ A ≃ᴹ A :=
  A.out_eq ▸ Ifam.Bij.lift_mk (Equiv.refl _)

/-- Right-hand bijection for `<$>ᴹ` -/
protected noncomputable def Mset.Bij.map_r (f : α → β) (A : Mset α) : A ≃ᴹ f <$>ᴹ A :=
  (Mset.Bij.map_l f A).symm

/-- Bijection for `<$>ᴹ` -/
protected noncomputable def Mset.Bij.map (f : α → α') (g : β → β')
    {A B} (r : A ≃ᴹ B) : f <$>ᴹ A ≃ᴹ g <$>ᴹ B :=
  (Mset.Bij.map_l f A).trans <| r.trans (Mset.Bij.map_r g B)

/-- The graph of `Mset.Bij.map_l` -/
@[simp] protected lemma Mset.Bij.map_l_graph (f : α → β) (A : Mset α) :
    (Mset.Bij.map_l f A).graph = (fun a => (f a, a)) <$>ᴹ A := by
  rw [Mset.Bij.map_l]; generalize A.out_eq = eq; revert eq;
  generalize A.out = A'; intro rfl; simp only; apply Bij.lift_mk_graph

/-- The graph of `Mset.Bij.map_r` -/
@[simp] protected lemma Mset.Bij.map_r_graph (f : α → β) (A : Mset α) :
    (Mset.Bij.map_r f A).graph = (fun a => (a, f a)) <$>ᴹ A := by
  rw [Mset.Bij.map_r, Mset.Bij.symm_graph, Mset.Bij.map_l_graph, ←Mset.comp_map]; rfl

/-- The graph of `Mset.Bij.map` -/
@[simp] protected lemma Mset.Bij.map_graph (f : α → α') (g : β → β') {A B} (r : A ≃ᴹ B) :
    (Mset.Bij.map f g r).graph = (fun (a, b) => (f a, g b)) <$>ᴹ r.graph := by
  have eq :
    (fun (a, b) => (f a, g b)) = ((fun (a, b) => (f a, b)) ∘ (fun (a, b) => (a, g b))) := rfl;
  simp only [eq, Mset.comp_map, Mset.Bij.map]; trans;
  { apply Mset.Bij.trans_graph_map_l; { apply Mset.Bij.map_l_graph } };
  congr; apply Mset.Bij.trans_graph_map_r; { apply Mset.Bij.map_r_graph }

/-! ### For `∅` -/

/-- Bijection for `∅` -/
protected def Ifam.Bij.empty : (∅ : Ifam α) ≃ᴵ (∅ : Ifam β) :=
  Equiv.refl _

/-- Bijection for `∅` -/
protected noncomputable def Mset.Bij.empty : (∅ : Mset α) ≃ᴹ (∅ : Mset β) :=
  Ifam.Bij.lift_mk Ifam.Bij.empty

/-- The graph of `Ifam.Bij.empty` -/
@[simp] protected lemma Ifam.Bij.empty_graph :
    Ifam.Bij.empty.graph (α := α) (β := β) ≈ ∅ := by
  exists Equiv.refl _; nofun

/-- The graph of `Mset.Bij.empty` -/
@[simp] protected lemma Mset.Bij.empty_graph :
    Mset.Bij.empty.graph (α := α) (β := β) = ∅ := by
  rw [Mset.Bij.empty, Ifam.Bij.lift_mk_graph]; apply Quotient.sound;
  apply Ifam.Bij.empty_graph

/-! ### For `pure` -/

/-- Bijection for `Ifam.pure` -/
protected def Ifam.Bij.pure (a : α) (b : β) : pure a ≃ᴵ pure b :=
  Equiv.refl _

/-- Bijection for `Mset.pure` -/
protected noncomputable def Mset.Bij.pure (a : α) (b : β) : pure a ≃ᴹ pure b :=
  Ifam.Bij.lift_mk (Ifam.Bij.pure _ _)

/-- The graph of `Ifam.Bij.pure` -/
@[simp] protected lemma Ifam.Bij.pure_graph (a : α) (b : β) :
    (Ifam.Bij.pure a b).graph = pure (a, b) := rfl

/-- The graph of `Mset.Bij.pure` -/
@[simp] protected lemma Mset.Bij.pure_graph (a : α) (b : β) :
    (Mset.Bij.pure a b).graph = pure (a, b) := by
  rw [Mset.Bij.pure, Ifam.Bij.lift_mk_graph]; rfl
