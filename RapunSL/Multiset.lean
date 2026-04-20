module

public import Mathlib.Data.Setoid.Basic

@[expose] public section

/-! # Multisets -/

/-! ## Premultiset -/

/-- Premultiset -/
structure Premultiset.{u} (α : Type u) : Type (max u 1) where mk ::
  dom : Type
  elem : dom → α

/-! ### Equivalence and setoid for `Premultiset` -/

/-- Equivalence between `Premultiset`s -/
def Premultiset.equiv.{u} (A B : Premultiset.{u} α) : Prop :=
  ∃ f : A.dom → B.dom, ∃ g : B.dom → A.dom,
  (∀ j, f (g j) = j) ∧ (∀ i, g (f i) = i) ∧ ∀ i, A.elem i = B.elem (f i)

lemma Premultiset.equiv.is_equiv :
    Equivalence (α:=Premultiset.{u} α) Premultiset.equiv where
  refl _ := by exists id, id; and_intros <;> intros <;> rfl
  symm := fun ⟨f, g, fg, _, AB⟩ => by
    exists g, f; and_intros <;> try assumption;
    intros; rw [AB, fg]
  trans := fun ⟨f, g, fg, gf, AB⟩ ⟨h, k, hk, kh, BC⟩ => by
    exists h ∘ f, g ∘ k; simp only [Function.comp_apply];
    and_intros <;> intro _;
    { rw [fg, hk] }; { rw [kh, gf] }; rw [←BC, ←AB]

/-- Setoid for `Premultiset` -/
instance Premultiset.Setoid.{u} α : Setoid (Premultiset α) :=
  Setoid.mk (Premultiset.equiv.{u}) Premultiset.equiv.is_equiv

/-! ## Multiset -/

/-- Multiset -/
def Multiset.{u} (α : Type u) : Type (max u 1) :=
  Quotient (Premultiset.Setoid.{u} α)

/-! ## Empty multiset -/

/-- Empty premultiset -/
def Premultiset.empty : Premultiset α := .mk Empty nofun

/-- Empty Multiset -/
def Multiset.empty : Multiset α := ⟦ .empty ⟧

/-! ## Singleton multiset -/

/-- Singleton premultiset -/
def Premultiset.singl (a : α) : Premultiset α := .mk Unit (fun _ => a)

/-- Singleton multiset -/
def Multiset.singl (a : α) : Multiset α := ⟦ .singl a ⟧

/-! ## Binary multiset sum -/

/-- Sum of two premultisets -/
def Premultiset.sum {α} (A B : Premultiset α) : Premultiset α :=
  .mk (A.dom ⊕ B.dom) (fun s => s.casesOn A.elem B.elem)

instance Premultiset.Add : Add (Premultiset.{u} α) where
  add := Premultiset.sum

lemma Premultiset.sum.unfold (A B : Premultiset α) :
  A + B = Premultiset.sum A B := rfl

@[simp] lemma Premultiset.sum.dom (A B : Premultiset α) :
  (A + B).dom = (A.dom ⊕ B.dom) := rfl

@[simp] lemma Premultiset.sum.elem_inl (A B : Premultiset α) {i} :
  (A + B).elem (.inl i) = A.elem i := rfl

@[simp] lemma Premultiset.sum.elem_inr (A B : Premultiset α) {i} :
  (A + B).elem (.inr i) = B.elem i := rfl

lemma Premultiset.sum.proper (A A' B B' : Premultiset α) :
    A ≈ A' → B ≈ B' → A + B ≈ A' + B' :=
  fun ⟨f, g, gf, fg, AB⟩ ⟨h, k, kh, hk, A'B'⟩ => by
    exists .map f h, .map g k;
    and_intros <;>
      (rintro (_ | _) <;> simp only [Sum.map_inl, Sum.map_inr]);
    { rw [gf] }; { rw [kh] }; { rw [fg] }; { rw [hk] };
    { apply AB }; { apply A'B' }

lemma Premultiset.sum.proper_l (A A' B : Premultiset α) :
    A ≈ A' → A + B ≈ A' + B := by
  intro _; apply Premultiset.sum.proper; { assumption }; { rfl }

lemma Premultiset.sum.proper_r (A B B' : Premultiset α) :
    B ≈ B' → A + B ≈ A + B' := by
  intro _; apply Premultiset.sum.proper; { rfl }; { assumption }

/-- Sum of two multisets -/
def Multiset.sum.{u} {α} : Multiset.{u} α → Multiset.{u} α → Multiset α :=
  .lift₂ (fun A B => ⟦ A + B ⟧) <| by
    intros; apply Quotient.sound; apply Premultiset.sum.proper <;> assumption

instance Multiset.Add : Add (Multiset.{u} α) where
  add := Multiset.sum

lemma Multiset.sum.unfold (A B : Multiset α) :
  A + B = Multiset.sum A B := rfl

/-! ### [+] is commutative -/

private lemma Premultiset.sum.comm (A B : Premultiset α) :
    A + B ≈ B + A := by
  exists fun | .inl i => .inr i | .inr j => .inl j,
         fun | .inl j => .inr j | .inr i => .inl i;
  and_intros <;> rintro (_ | _) <;> rfl

instance Multiset.sum.Commutative :
    Std.Commutative (HAdd.hAdd (α := Multiset α)) where
  comm A B := by
    cases A using Quotient.ind; cases B using Quotient.ind;
    apply Quotient.sound; apply Premultiset.sum.comm

/-! ### [+] is unital -/

private lemma Premultiset.sum.right_id {A : Premultiset α} :
    A + .empty ≈ A := by
  exists fun | .inl i => i | .inr e => (nomatch e), .inl
  and_intros; { intro _; rfl }; all_goals
    rintro (_ | _); { rfl }; { nofun }

instance Multiset.sum.LawfulCommIdentity :
    Std.LawfulCommIdentity (HAdd.hAdd (α := Multiset α)) Multiset.empty where
  right_id A := by
    cases A using Quotient.ind; apply Quotient.sound;
    exact Premultiset.sum.right_id

/-! ### [+] is assoc -/

private lemma Premultiset.sum.assoc (A B C : Premultiset α) :
    (A + B) + C ≈ A + (B + C) := by
  exists fun | .inl (.inl i) => .inl i | .inl (.inr j) => .inr (.inl j)
             | .inr k => .inr (.inr k),
         fun | .inl i => .inl (.inl i) | .inr (.inl j) => .inl (.inr j)
             | .inr (.inr k) => .inr k;
  and_intros; { rintro (_ | _ | _) <;> rfl }; all_goals
    rintro ((_ | _) | _) <;> rfl

instance Multiset.sum.Associative :
    Std.Associative (HAdd.hAdd (α := Multiset α)) where
  assoc A B C := by
    cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
    apply Quotient.sound; apply Premultiset.sum.assoc

/-! ## Big sum of multisets -/

/-- Big sum of premultisets -/
def Premultiset.bigsum {ι : Type} (A : ι → Premultiset α) : Premultiset α :=
  .mk (Σ i, (A i).dom) (fun ⟨i, j⟩ => (A i).elem j)

lemma Premultiset.bigsum.proper (A A' : ι → Premultiset α) :
    (∀ i, A i ≈ A' i) → Premultiset.bigsum A ≈ Premultiset.bigsum A' := by
  intro AA'; have ⟨f, AA'⟩ := Classical.skolem.mp AA';
  have ⟨g, AA'⟩ := Classical.skolem.mp AA';
  exists fun ⟨i, j⟩ => ⟨i, f i j⟩, fun ⟨i, j⟩ => ⟨i, g i j⟩;
  and_intros <;> intro ⟨i, j⟩ <;> have ⟨gf, fg, AA'⟩ := AA' i <;> simp only;
  { rw [gf] }; { rw [fg] }; { apply AA' }

@[simp] lemma Premultiset.bigsum.dom (A : ι → Premultiset α) :
    (Premultiset.bigsum (α := α) (ι := ι) A).dom = Σ i, (A i).dom := rfl

@[simp] lemma Premultiset.bigsum.elem (A : ι → Premultiset α) (i j) :
    (Premultiset.bigsum (α := α) (ι := ι) A).elem ⟨i, j⟩ = (A i).elem j := rfl

/-- Big sum of multisets -/
noncomputable def Multiset.bigsum.{u} {ι : Type}
  (A : ι → Multiset.{u} α) : Multiset.{u} α :=
  ⟦ Premultiset.bigsum (fun i => (A i).out) ⟧

lemma Multiset.bigsum.proper (A A' : ι → Multiset α) :
    (∀ i, A i = A' i) → Multiset.bigsum A = Multiset.bigsum A' := by
  intro AA'; apply Quotient.sound;
  apply Premultiset.bigsum.proper; intro _; rw [AA']

/-! ### `bigsum` is commutative -/

private lemma Premultiset.bigsum.comm {ι ι' : Type}
    (A : ι → Premultiset α) (σ : ι → ι') (σ' : ι' → ι) :
    (∀ i', σ (σ' i') = i') → (∀ i, σ' (σ i) = i) →
    Premultiset.bigsum A ≈ Premultiset.bigsum (A ∘ σ') := fun σσ' σ'σ => by
  exists fun ⟨i, j⟩ => ⟨σ i, congrArg (fun i => (A i).dom) (σ'σ i).symm ▸ j⟩,
         fun ⟨i', j⟩ => ⟨σ' i', j⟩;
  simp only [dom, Function.comp_apply];
  and_intros <;> intro ⟨_, _⟩;
  · congr; { rw [σσ'] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · congr; { rw [σ'σ] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · simp only [bigsum, Function.comp_apply]; congr; { rw [σ'σ] };
    simp only [heq_eqRec_iff_heq, heq_eq_eq]

lemma Multiset.bigsum.comm {ι ι' : Type}
    (A : ι → Multiset α) (σ : ι → ι') (σ' : ι' → ι) :
    (∀ i', σ (σ' i') = i') → (∀ i, σ' (σ i) = i) →
    Multiset.bigsum A = Multiset.bigsum (A ∘ σ') := fun σσ' σ'σ => by
  apply Quotient.sound; apply Premultiset.bigsum.comm <;> assumption

/-! ### `bigsum` is associative -/

private lemma Premultiset.bigsum.assoc {ι : Type} {ι' : ι → Type}
    (A : ∀ ι, ι' ι → Premultiset α) :
    Premultiset.bigsum (fun i => Premultiset.bigsum (A i)) ≈
      Premultiset.bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  exists fun ⟨i, j, k⟩ => ⟨⟨i, j⟩, k⟩, fun ⟨⟨i, j⟩, k⟩ => ⟨i, j, k⟩;
  and_intros <;> intros <;> rfl

lemma Multiset.bigsum.assoc {ι : Type} {ι' : ι → Type}
    (A : ∀ ι, ι' ι → Multiset α) :
    Multiset.bigsum (fun i => Multiset.bigsum (A i)) =
      Multiset.bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  apply Quotient.sound; trans;
  { apply Premultiset.bigsum.proper; intros; apply Quotient.mk_out };
  apply Premultiset.bigsum.assoc

/-! ### `empty` as `bigsum` -/

private lemma Premultiset.empty_bigsum :
    Premultiset.empty ≈ Premultiset.bigsum (ι := Empty) A := by
  exists nofun, nofun; and_intros <;> nofun

lemma Multiset.empty_bigsum :
    Multiset.empty = Multiset.bigsum (ι := Empty) (α := α) nofun := by
  apply Quotient.sound; apply Premultiset.empty_bigsum

/-! ### `+` as `bigsum` -/

private lemma Premultiset.sum_bigsum (A B : Premultiset α) :
    F true = A → F false = B →
    A + B ≈ Premultiset.bigsum F := by
  intro rfl rfl;
  exists fun | .inl i => ⟨true, i⟩ | .inr i => ⟨false, i⟩,
         fun | ⟨true, i⟩ => .inl i | ⟨false, i⟩ => .inr i;
  and_intros; { rintro ⟨_ | _, _⟩ <;> rfl }; all_goals
    rintro (_ | _) <;> rfl

lemma Multiset.sum_bigsum (A B : Multiset α) :
    A + B = Multiset.bigsum (fun b : Bool => if b then A else B) := by
  rw (occs := [1]) [←Quotient.out_eq A, ←Quotient.out_eq B];
  apply Quotient.sound; apply Premultiset.sum_bigsum <;> rfl

/-! ## Functor -/

/-- Functor over a premultiset -/
def Premultiset.map {α β} (f : α → β) (A : Premultiset α) : Premultiset β :=
  .mk A.dom (fun i => f (A.elem i))

@[simp] lemma Premultiset.map.dom (f : α → β) A :
  (Premultiset.map f A).dom = A.dom := rfl

@[simp] lemma Premultiset.map.elem (f : α → β) A i :
  (Premultiset.map f A).elem i = f (A.elem i) := rfl

lemma Premultiset.map.proper (A B : Premultiset α) :
    A ≈ B → Premultiset.map f A ≈ Premultiset.map f B := by
  rintro ⟨g, h, _, _, AB⟩; exists g, h; and_intros; iterate 2 { assumption };
  simp only [map]; intro _; rw [AB]

/-- Functor over a multiset -/
def Multiset.map {α β} (f : α → β) : Multiset α → Multiset β :=
  .lift (fun A => ⟦ .map f A ⟧) <| by
    intros; apply Quotient.sound; apply Premultiset.map.proper; assumption

/-! ### Functor laws -/

lemma Multiset.map_map (f : α → β) (g : β → γ) (A : Multiset α) :
    Multiset.map g (Multiset.map f A) = Multiset.map (g ∘ f) A := by
  cases A using Quotient.ind; rfl

lemma Multiset.map_id (A : Multiset α) :
    Multiset.map id A = A := by
  cases A using Quotient.ind; rfl

/-! ### `map` over `+` -/

private lemma Premultiset.map_sum (f : α → β) (A B : Premultiset α) :
    Premultiset.map f (A + B) ≈ Premultiset.map f A + Premultiset.map f B := by
  exists id, id; and_intros; all_goals { rintro (_ | _) <;> rfl }

lemma Multiset.map_sum (f : α → β) (A B : Multiset α) :
    Multiset.map f (A + B) = Multiset.map f A + Multiset.map f B := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Premultiset.map_sum

/-! ## Binary multiset product -/

/-- Product of two premultisets -/
def Premultiset.prod {α β} (A : Premultiset α) (B : Premultiset β)
  : Premultiset (α × β) :=
  .mk (A.dom × B.dom) (fun (i, j) => (A.elem i, B.elem j))

instance Premultiset.HMul :
    HMul (Premultiset α) (Premultiset β) (Premultiset (α × β)) where
  hMul := Premultiset.prod

lemma Premultiset.mul.unfold (A : Premultiset α) (B : Premultiset β) :
    A * B = Premultiset.prod A B := rfl

@[simp] lemma Premultiset.prod.dom (A : Premultiset α) (B : Premultiset β) :
    (A * B).dom = (A.dom × B.dom) := rfl

@[simp] lemma Premultiset.prod.elem
    (A : Premultiset α) (B : Premultiset β) i j :
  (A * B).elem (i, j) = (A.elem i, B.elem j) := rfl

lemma Premultiset.prod.proper (A A' : Premultiset α) (B B' : Premultiset β) :
    A ≈ A' → B ≈ B' → A * B ≈ A' * B' := by
  rintro ⟨f, g, fg, gf, AA'⟩ ⟨h, k, kh, hk, BB'⟩;
  exists fun (i, j) => (f i, h j), fun (i', j') => (g i', k j');
  and_intros <;> intro (_, _) <;> simp only;
  { rw [fg, kh]; }; { rw [gf, hk] }; { simp only [elem]; rw [AA', BB'] }

/-- Product of two multisets -/
def Multiset.prod {α β} : Multiset α → Multiset β → Multiset (α × β) :=
  .lift₂ (fun A B => ⟦ A * B ⟧) <| by
    intros; apply Quotient.sound; apply Premultiset.prod.proper <;> assumption

instance Multiset.HMul :
    HMul (Multiset α) (Multiset β) (Multiset (α × β)) where
  hMul := Multiset.prod

lemma Multiset.prod.unfold {A : Multiset α} {B : Multiset β} :
    A * B = Multiset.prod A B := rfl

/-! ### `*` over `map` -/

lemma Multiset.prod_map
    (f : α → α') (g : β → β') (A : Multiset α) (B : Multiset β) :
    Multiset.map f A * Multiset.map g B =
      Multiset.map (Prod.map f g) (A * B) := by
  cases A using Quotient.ind; cases B using Quotient.ind; rfl

lemma Multiset.prod_map_l
    (f : α → α') (A : Multiset α) (B : Multiset β) :
    Multiset.map f A * B = Multiset.map (Prod.map f id) (A * B) := by
  rw [←Multiset.prod_map, Multiset.map_id]

lemma Multiset.prod_map_r
    (g : β → β') (A : Multiset α) (B : Multiset β) :
    A * Multiset.map g B = Multiset.map (Prod.map id g) (A * B) := by
  rw [←Multiset.prod_map, Multiset.map_id]

/-! ### `*` is commutative -/

lemma Premultiset.prod.comm (A : Premultiset α) (B : Premultiset β) :
    A * B ≈ .map Prod.swap (B * A) := by
  exists fun (i, j) => (j, i), fun (j, i) => (i, j);
  and_intros <;> intro (_, _) <;> rfl

lemma Multiset.prod.comm (A : Multiset α) (B : Multiset β) :
    A * B = .map Prod.swap (B * A) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Premultiset.prod.comm

/-! ### `*` is unital -/

lemma Premultiset.prod.id_r (A : Premultiset α) (b : β) :
    A * Premultiset.singl b ≈ Premultiset.map (fun a => (a, b)) A := by
  exists fun (i, _) => i, fun i => (i, ());
  and_intros; { intros; trivial }; all_goals
    rintro ⟨_, _⟩; rfl

lemma Multiset.prod.id_r (A : Multiset α) (b : β) :
    A * Multiset.singl b = Multiset.map (fun a => (a, b)) A := by
  cases A using Quotient.ind; apply Quotient.sound;
  apply Premultiset.prod.id_r

lemma Multiset.prod.id_l (a : α) (B : Multiset β) :
    Multiset.singl a * B = Multiset.map (fun b => (a, b)) B := by
  rw [Multiset.prod.comm, Multiset.prod.id_r, Multiset.map_map]; rfl

/-! ### `*` is associative -/

private lemma Premultiset.prod.assoc
    (A : Premultiset α) (B : Premultiset β) (C : Premultiset γ) :
    (A * B) * C ≈ .map (fun (a, b, c) => (⟨a, b⟩, c)) (A * (B * C)) := by
  exists fun ⟨⟨i, j⟩, k⟩ => ⟨i, ⟨j, k⟩⟩, fun ⟨i, ⟨j, k⟩⟩ => ⟨⟨i, j⟩, k⟩;
  and_intros <;> intro ⟨_, _⟩ <;> rfl

lemma Multiset.prod.assoc
    (A : Multiset α) (B : Multiset β) (C : Multiset γ) :
    (A * B) * C = .map (fun (a, b, c) => ((a, b), c)) (A * (B * C)) := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Premultiset.prod.assoc

/-! ### `*` distributes over `+` -/

private lemma Premultiset.prod_sum_distrib_l
    (A : Premultiset α) (B C : Premultiset β) :
    A * (B + C) ≈ (A * B) + (A * C) := by
  exists fun (i, s) => match s with | .inl j => .inl (i, j) | .inr k => .inr (i, k),
         fun | .inl (i, j) => ⟨i, .inl j⟩ | .inr (i, k) => ⟨i, .inr k⟩;
  and_intros; { rintro (_ | _) <;> rfl }; all_goals
    rintro ⟨_, (_ | _)⟩ <;> rfl

lemma Multiset.prod_sum_distrib_l (A : Multiset α) (B C : Multiset β) :
    A * (B + C) = A * B + A * C := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Premultiset.prod_sum_distrib_l

lemma Multiset.prod_sum_distrib_r (A B : Multiset α) (C : Multiset β) :
    (A + B) * C = A * C + B * C := by
  rw [Multiset.prod.comm, Multiset.prod_sum_distrib_l,
      Multiset.prod.comm C A, Multiset.prod.comm C B, Multiset.map_sum,
      Multiset.map_map, Multiset.map_map, Prod.swap_swap_eq,
      Multiset.map_id, Multiset.map_id]
