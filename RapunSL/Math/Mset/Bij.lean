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

/-- Membership for the graph of `Ifam.Bij.refl` -/
@[simp] protected lemma Ifam.Bij.refl_graph_mem {A : Ifam α} (a b : α) :
    ((a, b) ∈ (Ifam.Bij.refl A).graph) = (a = b ∧ a ∈ A) := by
  simp only [Ifam.Bij.refl_graph, Ifam.map'_mem]; grind only

/-- The graph of `Mset.Bij.refl` -/
@[simp] protected lemma Mset.Bij.refl_graph (A : Mset α) :
    (Mset.Bij.refl A).graph = (fun a => (a, a)) <$>ᴹ A := by
  rw (occs := [4]) [←A.out_eq]; rfl

/-- Membership for the graph of `Mset.Bij.refl` -/
@[simp] protected lemma Mset.Bij.refl_graph_mem {A : Mset α} (a b : α) :
    ((a, b) ∈ (Mset.Bij.refl A).graph) = (a = b ∧ a ∈ A) := by
  simp only [Mset.Bij.refl_graph, Mset.map'_mem]; grind only

/-- The graph of `Ifam.Bij.symm` -/
@[simp] protected lemma Ifam.Bij.symm_graph {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) :
    r.symm.graph ≈ (fun (a, b) => (b, a)) <$>ᴵ r.graph := by
  exists r.symm; intro i; simp only [Ifam.Bij.graph, Ifam.map]; congr; symm;
  apply Equiv.apply_symm_apply

/-- Membership for the graph of `Ifam.Bij.symm` -/
@[simp] protected lemma Ifam.Bij.symm_graph_mem {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) a b :
    ((a, b) ∈ r.symm.graph) = ((b, a) ∈ r.graph) := by
  rw [Ifam.mem_proper _ _ (Ifam.Bij.symm_graph _), Ifam.map'_mem]; grind only

/-- The graph of `Mset.Bij.symm` -/
@[simp] protected lemma Mset.Bij.symm_graph {A : Mset α} {B : Mset β} (r : A ≃ᴹ B) :
    r.symm.graph = (fun (a, b) => (b, a)) <$>ᴹ r.graph := by
  apply Quotient.sound; apply Ifam.Bij.symm_graph

/-- Membership for the graph of `Mset.Bij.symm` -/
@[simp] protected lemma Mset.Bij.symm_graph_mem {A : Mset α} {B : Mset β} (r : A ≃ᴹ B) a b :
    ((a, b) ∈ r.symm.graph) = ((b, a) ∈ r.graph) := by
  simp only [Mset.Bij.symm_graph, Mset.map'_mem]; grind only

/-! ### The graph of `trans` -/

/-- Membership for the graph of `Mset.Bij.trans` -/
protected lemma Mset.Bij.trans_graph_mem {A : Mset α} {B : Mset β} {C : Mset γ}
    (r : A ≃ᴹ B) (s : B ≃ᴹ C) a c :
    (a, c) ∈ (r.trans s).graph → ∃ b, (a, b) ∈ r.graph ∧ (b, c) ∈ s.graph := by
  rintro ⟨i, _, _⟩; exists B.out.elem (r i); and_intros;
  { exists i; }; { exists r i }

/-- The graph of `Ifam.Bij.trans` with a bijection of a map-like graph -/
protected lemma Ifam.Bij.trans_graph_map_l {A : Ifam α} {B : Ifam β} {C : Ifam γ}
    (r : A ≃ᴵ B) (s : B ≃ᴵ C) (f : β → α) :
    (∀ a b, (a, b) ∈ r.graph → a = f b) →
    (r.trans s).graph ≈ (fun (b, c) => (f b, c)) <$>ᴵ s.graph := by
  intro eq; exists r; intro i;
  simp only [Ifam.Bij.graph, Equiv.trans_apply, Ifam.map_elem] at *; congr; apply eq; exists i

/-- The graph of `Mset.Bij.trans` with a bijection of a map-like graph -/
protected lemma Mset.Bij.trans_graph_map_l {A : Mset α} {B : Mset β} {C : Mset γ}
    (r : A ≃ᴹ B) (s : B ≃ᴹ C) (f : β → α) :
    (∀ a b, (a, b) ∈ r.graph → a = f b) →
    (r.trans s).graph = (fun (b, c) => (f b, c)) <$>ᴹ s.graph := by
  intro eq; apply Quotient.sound; apply Ifam.Bij.trans_graph_map_l; trivial

/-- The graph of `Ifam.Bij.trans` with a bijection of a map-like graph -/
protected lemma Ifam.Bij.trans_graph_map_r {A : Ifam α} {B : Ifam β} {C : Ifam γ}
    (r : A ≃ᴵ B) (s : B ≃ᴵ C) (f : β → γ) :
    (∀ b c, (b, c) ∈ s.graph → c = f b) →
    (r.trans s).graph = (fun (a, b) => (a, f b)) <$>ᴵ r.graph := by
  intro eq; apply congr_arg (Ifam.mk _); ext1 i;
  simp only [Ifam.Bij.graph, Equiv.trans_apply] at *; congr; apply eq; exists r i

/-- The graph of `Mset.Bij.trans` with a bijection of a map-like graph -/
protected lemma Mset.Bij.trans_graph_map_r {A : Mset α} {B : Mset β} {C : Mset γ}
    (r : A ≃ᴹ B) (s : B ≃ᴹ C) (f : β → γ) :
    (∀ b c, (b, c) ∈ s.graph → c = f b) →
    (r.trans s).graph = (fun (a, b) => (a, f b)) <$>ᴹ r.graph := by
  intro eq; apply congr_arg (Quotient.mk _); apply Ifam.Bij.trans_graph_map_r; trivial

/-- The graph of `Ifam.Bij.trans` with a bijection of an identity graph -/
protected lemma Ifam.Bij.trans_graph_id_l {A A' : Ifam α} {B : Ifam β}
    (r : A ≃ᴵ A') (s : A' ≃ᴵ B) :
    (∀ a a', (a, a') ∈ r.graph → a = a') → (r.trans s).graph ≈ s.graph := by
  rw [←Ifam.id_map s.graph]; apply Ifam.Bij.trans_graph_map_l _ _ id

/-- The graph of `Mset.Bij.trans` with a bijection of an identity graph -/
protected lemma Mset.Bij.trans_graph_id_l {A A' : Mset α} {B : Mset β}
    (r : A ≃ᴹ A') (s : A' ≃ᴹ B) :
    (∀ a a', (a, a') ∈ r.graph → a = a') → (r.trans s).graph = s.graph := by
  rw [←Mset.id_map s.graph]; apply Mset.Bij.trans_graph_map_l

/-- The graph of `Ifam.Bij.trans` with a bijection of an identity graph -/
protected lemma Ifam.Bij.trans_graph_id_r {A : Ifam α} {B B' : Ifam β}
    (r : A ≃ᴵ B) (s : B ≃ᴵ B') :
    (∀ b b', (b, b') ∈ s.graph → b = b') → (r.trans s).graph = r.graph := by
  rw [←Ifam.id_map r.graph]; intro _; apply Ifam.Bij.trans_graph_map_r _ _ id; intros; symm; tauto

/-- The graph of `Mset.Bij.trans` with a bijection of an identity graph -/
protected lemma Mset.Bij.trans_graph_id_r {A : Mset α} {B B' : Mset β}
    (r : A ≃ᴹ B) (s : B ≃ᴹ B') :
    (∀ b b', (b, b') ∈ s.graph → b = b') → (r.trans s).graph = r.graph := by
  rw [←Mset.id_map r.graph]; intro _; apply Mset.Bij.trans_graph_map_r _ _ id; intros; symm; tauto

/-! ### The graph of lifting constructions -/

/-- The graph of `Ifam.Bij.lift_equiv` -/
@[simp] protected lemma Ifam.Bij.lift_equiv_graph {A B : Ifam α} (e : A ≈ B) :
    (Ifam.Bij.lift_equiv e).graph = (fun a => (a, a)) <$>ᴵ A := by
  apply congr_arg (Ifam.mk _); ext1 i; ext1; { rfl }; symm; apply Classical.choose_spec e

/-- Membership for the graph of `Ifam.Bij.lift_equiv` -/
@[simp] protected lemma Ifam.Bij.lift_equiv_graph_mem {A B : Ifam α} (e : A ≈ B) (a a' : α) :
    ((a, a') ∈ (Ifam.Bij.lift_equiv e).graph) = (a = a' ∧ a ∈ A) := by
  simp only [Ifam.Bij.lift_equiv_graph, Ifam.map'_mem]; grind only

/-- The graph of `Ifam.Bij.mk_out` -/
@[simp] protected lemma Ifam.Bij.mk_out_graph (A : Ifam α) :
    (Ifam.Bij.mk_out A).graph = (fun a => (a, a)) <$>ᴵ (⟦ A ⟧ : Mset α).out := by
  apply Ifam.Bij.lift_equiv_graph

/-- Membership for the graph of `Ifam.Bij.mk_out` -/
@[simp] protected lemma Ifam.Bij.mk_out_graph_mem (A : Ifam α) (a b : α) :
    ((a, b) ∈ (Ifam.Bij.mk_out A).graph) = (a = b ∧ a ∈ A) := by
  trans; { apply Ifam.Bij.lift_equiv_graph_mem }; rw [Mset.out_mem]; rfl

/-- The graph of `Ifam.Bij.lift_mk` -/
@[simp] protected lemma Ifam.Bij.lift_mk_graph {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) :
    r.lift_mk.graph = ⟦ r.graph ⟧ := by
  apply Quotient.sound; rw [Ifam.Bij.lift_mk];
  rw [←Ifam.Bij.trans_graph_id_r r (Bij.mk_out B).symm];
  { apply Ifam.Bij.trans_graph_id_l; simp only [Ifam.Bij.mk_out_graph_mem]; tauto };
  simp only [Ifam.Bij.symm_graph_mem, Ifam.Bij.mk_out_graph_mem]; tauto

/-- Membership for the graph of `Ifam.Bij.lift_mk` -/
@[simp] protected lemma Ifam.Bij.lift_mk_graph_mem {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) p :
    (p ∈ r.lift_mk.graph) = (p ∈ r.graph) := by
  rw [Ifam.Bij.lift_mk_graph]; rfl

/-! ### Bijection for the graph -/

/-- Bijection between the graph and the domain of a bijection -/
protected def Ifam.Bij.graph_dom {A : Ifam α} {B : Ifam β}
    (r : A ≃ᴵ B) : r.graph ≃ᴵ A := Equiv.refl _

/-- Bijection between the graph and the domain of a bijection -/
protected noncomputable def Mset.Bij.graph_dom {A : Mset α} {B : Mset β}
    (r : A ≃ᴹ B) : r.graph ≃ᴹ A :=
  (Ifam.Bij.mk_out _).trans (Ifam.Bij.graph_dom r)

/-- Bijection between the graph and the codomain of a bijection -/
protected def Ifam.Bij.graph_codom {A : Ifam α} {B : Ifam β}
    (r : A ≃ᴵ B) : r.graph ≃ᴵ B := r

/-- Bijection between the graph and the codomain of a bijection -/
protected noncomputable def Mset.Bij.graph_codom {A : Mset α} {B : Mset β}
    (r : A ≃ᴹ B) : r.graph ≃ᴹ B :=
  (Ifam.Bij.mk_out _).trans (Ifam.Bij.graph_codom r)

/-- The graph of `Ifam.Bij.graph_dom` -/
@[simp] protected lemma Ifam.Bij.graph_dom_graph (A : Ifam α) (B : Ifam β) (r : A ≃ᴵ B) :
    r.graph_dom.graph = (fun (a, b) => ((a, b), a)) <$>ᴵ r.graph := rfl

/-- The graph of `Mset.Bij.graph_dom` -/
@[simp] protected lemma Mset.Bij.graph_dom_graph (A : Mset α) (B : Mset β) (r : A ≃ᴹ B) :
    r.graph_dom.graph = (fun (a, b) => ((a, b), a)) <$>ᴹ r.graph := by
  apply Quotient.sound; rw [Mset.Bij.graph_dom, ←Ifam.Bij.graph_dom_graph];
  apply Ifam.Bij.trans_graph_id_l; simp only [Mset.Bij.graph, Ifam.Bij.mk_out_graph_mem]; tauto

/-- Membership for the graph of `Mset.Bij.graph_dom` -/
@[simp] protected lemma Mset.Bij.graph_dom_graph_mem (A : Mset α) (B : Mset β) (r : A ≃ᴹ B) a b :
    (((a, b), a') ∈ r.graph_dom.graph) = ((a, b) ∈ r.graph ∧ a' = a) := by
  rw [Mset.Bij.graph_dom_graph, Mset.map'_mem]; grind only

/-- The graph of `Ifam.Bij.graph_codom` -/
@[simp] protected lemma Ifam.Bij.graph_codom_graph (A : Ifam α) (B : Ifam β) (r : A ≃ᴵ B) :
    r.graph_codom.graph = (fun (a, b) => ((a, b), b)) <$>ᴵ r.graph := rfl

/-- The graph of `Mset.Bij.graph_codom` -/
@[simp] protected lemma Mset.Bij.graph_codom_graph (A : Mset α) (B : Mset β) (r : A ≃ᴹ B) :
    r.graph_codom.graph = (fun (a, b) => ((a, b), b)) <$>ᴹ r.graph := by
  apply Quotient.sound; rw [Mset.Bij.graph_codom, ←Ifam.Bij.graph_codom_graph];
  apply Ifam.Bij.trans_graph_id_l; simp only [Mset.Bij.graph, Ifam.Bij.mk_out_graph_mem]; tauto

/-- Membership for the graph of `Mset.Bij.graph_codom` -/
@[simp] protected lemma Mset.Bij.graph_codom_graph_mem (A : Mset α) (B : Mset β) (r : A ≃ᴹ B) a b :
    (((a, b), b') ∈ r.graph_codom.graph) = ((a, b) ∈ r.graph ∧ b' = b) := by
  rw [Mset.Bij.graph_codom_graph, Mset.map'_mem]; grind only

/-! ## Getting information from the graph -/

/-- Get `<$>ᴵ` information from a map-like graph -/
protected lemma Ifam.Bij.graph_eq_map {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) (f : α → β) :
    (∀ a b, (a, b) ∈ r.graph → b = f a) → B ≈ f <$>ᴵ A := by
  intro eq; symm; exists r; intro i; symm; apply eq; exists i

/-- Get `<$>ᴹ` information from a map-like graph -/
protected lemma Mset.Bij.graph_eq_map {A : Mset α} {B : Mset β} (r : A ≃ᴹ B) (f : α → β) :
    (∀ a b, (a, b) ∈ r.graph → b = f a) → B = f <$>ᴹ A := by
  rw (occs := [2]) [←A.out_eq, ←B.out_eq]; intro eq; apply Quotient.sound;
  revert eq; apply Ifam.Bij.graph_eq_map

/-- Get `<$>ᴵ` information from a map-like graph -/
protected lemma Ifam.Bij.graph_eq_map_rev {A : Ifam α} {B : Ifam β} (r : A ≃ᴵ B) (f : β → α) :
    (∀ a b, (a, b) ∈ r.graph → a = f b) → A ≈ f <$>ᴵ B := by
  intro _; apply Ifam.Bij.graph_eq_map r.symm f; intro _ _; rw [Ifam.Bij.symm_graph_mem]; tauto

/-- Get `<$>ᴹ` information from a map-like graph -/
protected lemma Mset.Bij.graph_eq_map_rev {A : Mset α} {B : Mset β} (r : A ≃ᴹ B) (f : β → α) :
    (∀ a b, (a, b) ∈ r.graph → a = f b) → A = f <$>ᴹ B := by
  intro _; apply Mset.Bij.graph_eq_map r.symm f; intro _ _; rw [Mset.Bij.symm_graph_mem]; tauto

/-- Get equivalence from an identity graph -/
protected lemma Ifam.Bij.graph_eq {A B : Ifam α} (r : A ≃ᴵ B) :
    (∀ a b, (a, b) ∈ r.graph → a = b) → A ≈ B := by
  apply Ifam.Bij.graph_eq_map_rev

/-- Get equality from an identity graph -/
protected lemma Mset.Bij.graph_eq {A B : Mset α} (r : A ≃ᴹ B) :
    (∀ a b, (a, b) ∈ r.graph → a = b) → A = B := by
  rw (occs := [2]) [←Mset.id_map B]; apply Mset.Bij.graph_eq_map_rev

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
  generalize A.out = A'; intro rfl; simp only; apply Ifam.Bij.lift_mk_graph

/-- Membership for the graph of `Mset.Bij.map_l` -/
@[simp] protected lemma Mset.Bij.map_l_graph_mem (f : α → β) (A : Mset α) a b :
    ((b, a) ∈ (Mset.Bij.map_l f A).graph) = (b = f a ∧ a ∈ A) := by
  rw [Mset.Bij.map_l_graph, Mset.map'_mem]; grind only

/-- The graph of `Mset.Bij.map_r` -/
@[simp] protected lemma Mset.Bij.map_r_graph (f : α → β) (A : Mset α) :
    (Mset.Bij.map_r f A).graph = (fun a => (a, f a)) <$>ᴹ A := by
  rw [Mset.Bij.map_r, Mset.Bij.symm_graph, Mset.Bij.map_l_graph, ←Mset.comp_map]; rfl

/-- Membership for the graph of `Mset.Bij.map_r` -/
@[simp] protected lemma Mset.Bij.map_r_graph_mem (f : α → β) (A : Mset α) a b :
    ((a, b) ∈ (Mset.Bij.map_r f A).graph) = (b = f a ∧ a ∈ A) := by
  rw [Mset.Bij.map_r_graph, Mset.map'_mem]; grind only

/-- The graph of `Mset.Bij.map` -/
@[simp] protected lemma Mset.Bij.map_graph (f : α → α') (g : β → β') {A B} (r : A ≃ᴹ B) :
    (Mset.Bij.map f g r).graph = (fun (a, b) => (f a, g b)) <$>ᴹ r.graph := by
  have eq :
    (fun (a, b) => (f a, g b)) = ((fun (a, b) => (f a, b)) ∘ (fun (a, b) => (a, g b))) := rfl;
  simp only [eq, Mset.comp_map, Mset.Bij.map]; trans;
  { apply Mset.Bij.trans_graph_map_l _ _ f; intro _ _;
    rw [Mset.Bij.map_l_graph_mem]; tauto };
  congr; apply Mset.Bij.trans_graph_map_r; intro _ _;
  rw [Mset.Bij.map_r_graph_mem]; tauto

/-- Membership for the graph of `Mset.Bij.map` -/
@[simp] protected lemma Mset.Bij.map_graph_mem (f : α → α') (g : β → β') {A B} (r : A ≃ᴹ B) a' b' :
    ((a', b') ∈ (Mset.Bij.map f g r).graph) = ∃ a b, (a, b) ∈ r.graph ∧ a' = f a ∧ b' = g b := by
  rw [Mset.Bij.map_graph, Mset.map'_mem]; grind only

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

/-- Membership for the graph of `Mset.Bij.empty` -/
@[simp] protected lemma Mset.Bij.empty_graph_mem (a b : α) :
    ((a, b) ∈ Mset.Bij.empty.graph) = False := by
  rw [Mset.Bij.empty_graph, Mset.empty_mem]

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

/-- Membership for the graph of `Mset.Bij.pure` -/
@[simp] protected lemma Mset.Bij.pure_graph_mem (a b a' b' : α) :
    ((a', b') ∈ (Mset.Bij.pure a b).graph) = (a' = a ∧ b' = b) := by
  rw [Mset.Bij.pure_graph, Mset.pure_mem]; grind only
