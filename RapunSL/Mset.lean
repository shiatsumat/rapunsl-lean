module

public import Mathlib.Data.Setoid.Basic
public import Mathlib.Control.Applicative

@[expose] public section

/-! # Multisets, possibly infinite -/

/-! ## `Ifam`: Indexed family -/

/-- Indexed family -/
structure Ifam.{u} (α : Type u) : Type (max 1 u) where mk ::
  dom : Type
  elem : dom → α

/-! ### Equivalence and setoid for `Ifam` -/

/-- Equivalence between indexed families -/
def Ifam.equiv.{u} (A B : Ifam.{u} α) : Prop :=
  ∃ f : A.dom → B.dom, ∃ g : B.dom → A.dom,
  (∀ j, f (g j) = j) ∧ (∀ i, g (f i) = i) ∧ ∀ i, A.elem i = B.elem (f i)

/-- Utility for getting the inverse element equality -/
lemma Ifam.equiv_elem_eq_symm {A B : Ifam α}
    {f : A.dom → B.dom} {g : B.dom → A.dom} :
    (∀ j, f (g j) = j) → (∀ i, A.elem i = B.elem (f i)) →
    ∀ j, B.elem j = A.elem (g j) := by
  intro fg AB j; rw [AB, fg]

lemma Ifam.equiv_is_equiv :
    Equivalence (α:=Ifam.{u} α) Ifam.equiv where
  refl _ := by exists id, id; and_intros <;> intros <;> rfl
  symm := by
    rintro _ _ ⟨f, g, fg, _, AB⟩; exists g, f; and_intros <;> try assumption;
    intros; rw [AB, fg]
  trans := by
    rintro _ _ _ ⟨f, g, fg, gf, AB⟩ ⟨h, k, hk, kh, BC⟩;
    exists h ∘ f, g ∘ k; simp only [Function.comp_apply];
    and_intros <;> intro _;
    { rw [fg, hk] }; { rw [kh, gf] }; rw [←BC, ←AB]

/-- Setoid for `Ifam` -/
instance Ifam.Setoid.{u} α : Setoid (Ifam α) :=
  Setoid.mk (Ifam.equiv.{u}) Ifam.equiv_is_equiv

/-! ## `Mset`: Multiset, possibly infinite -/

/-- Multiset, possibly infinite -/
def Mset.{u} (α : Type u) : Type (max 1 u) :=
  Quotient (Ifam.Setoid.{u} α)

/-! ## Functor -/

/-- Functor map for `Ifam`, more universe-polymorphic than `Functor.map` -/
def Ifam.map {α β : Type*} (f : α → β) (A : Ifam α) : Ifam β :=
  .mk A.dom (fun i => f (A.elem i))

/-- `Functor` for `Ifam` -/
instance Ifam.Functor : Functor Ifam.{u} where
  map := Ifam.map

lemma Ifam.map_unfold : Functor.map = Ifam.map (α:=α) (β:=β) := rfl

lemma Ifam.id_map (A : Ifam α) : map id A = A := by rfl

lemma Ifam.comp_map (f : α → β) (g : β → γ) (A : Ifam α) :
    map (g ∘ f) A = map g (map f A) := by rfl

/-- `LawfulFunctor` for `Ifam` -/
instance Ifam.LawfulFunctor : LawfulFunctor Ifam.{u} where
  id_map _ := rfl
  comp_map _ _ _ := rfl
  map_const := rfl

@[simp] lemma Ifam.map_dom (f : α → β) (A : Ifam α) :
  (map f A).dom = A.dom := rfl

@[simp] lemma Ifam.map_elem (f : α → β) (A : Ifam α) (i : A.dom) :
  (map f A).elem i = f (A.elem i) := rfl

lemma Ifam.map_proper (A B : Ifam α) :
    A ≈ B → map f A ≈ map f B := by
  rintro ⟨g, h, _, _, AB⟩; exists g, h; and_intros; iterate 2 { assumption };
  simp only [map_dom, map_elem]; intro _; rw [AB]

/-- Functor map for `Mset`, more universe-polymorphic than `Functor.map` -/
def Mset.map {α β : Type*} (f : α → β) : Mset α → Mset β :=
  .lift (⟦ Ifam.map f · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.map_proper; assumption

/-- `Functor` for `Mset` -/
instance Mset.Functor : Functor Mset.{u} where
  map := Mset.map

lemma Mset.map_unfold : Functor.map = Mset.map (α:=α) (β:=β) := rfl

lemma Mset.id_map (A : Mset α) : map id A = A := by
  cases A using Quotient.ind; rfl

lemma Mset.comp_map (f : α → β) (g : β → γ) (A : Mset α) :
    map (g ∘ f) A = map g (map f A) := by
  cases A using Quotient.ind; rfl

/-- Functor laws for `Mset` -/
instance Mset.LawfulFunctor : LawfulFunctor Mset.{u} where
  id_map := Mset.id_map
  comp_map := Mset.comp_map
  map_const := rfl

/-! ## Empty multiset -/

/-- Empty indexed family -/
instance Ifam.empty : EmptyCollection (Ifam α) where
  emptyCollection := .mk Empty nofun

@[simp] lemma Ifam.empty_dom :
    (∅ : Ifam α).dom = Empty := rfl

/-- Empty multiset -/
instance Mset.empty : EmptyCollection (Mset α) where
  emptyCollection := ⟦ ∅ ⟧

/-! ## Singleton -/

/-- Singleton indexed family -/
instance Ifam.Pure : Pure Ifam.{u} where
  pure a := .mk Unit (fun _ => a)

lemma Ifam.pure_unfold (a : α) :
    pure (f:=Ifam) a = .mk Unit (fun _ => a) := rfl

@[simp] lemma Ifam.pure_dom (a : α) :
    (pure (f:=Ifam) a).dom = Unit := rfl

@[simp] lemma Ifam.pure_elem (a : α) u :
    (pure (f:=Ifam) a).elem u = a := rfl

/-- Singleton multiset -/
instance Mset.Pure : Pure Mset.{u} where
  pure a := ⟦ pure a ⟧

lemma Mset.pure_unfold (a : α) :
    pure (f:=Mset) a = ⟦ .mk Unit (fun _ => a) ⟧ := rfl

/-! ## `map` over `pure` -/

lemma Ifam.pure_map (f : α → β) (a : α) :
    map f (pure a) = pure (f a) := rfl

lemma Mset.pure_map (f : α → β) (a : α) :
    map f (pure a) = pure (f a) := rfl

/-! ## Binary sum -/

/-- Sum of two indexed families -/
def Ifam.sum {α} (A B : Ifam α) : Ifam α :=
  .mk (A.dom ⊕ B.dom) (fun s => s.casesOn A.elem B.elem)

instance Ifam.Add : Add (Ifam.{u} α) where
  add := Ifam.sum

lemma Ifam.sum_unfold : HAdd.hAdd = Ifam.sum (α:=α) := rfl

@[simp] lemma Ifam.sum_dom (A B : Ifam α) :
  (A + B).dom = (A.dom ⊕ B.dom) := rfl

@[simp] lemma Ifam.sum_elem_inl (A B : Ifam α) {i} :
  (A + B).elem (.inl i) = A.elem i := rfl

@[simp] lemma Ifam.sum_elem_inr (A B : Ifam α) {i} :
  (A + B).elem (.inr i) = B.elem i := rfl

lemma Ifam.sum_proper (A A' B B' : Ifam α) :
    A ≈ A' → B ≈ B' → A + B ≈ A' + B' :=
  fun ⟨f, g, gf, fg, AB⟩ ⟨h, k, kh, hk, A'B'⟩ => by
    exists .map f h, .map g k;
    and_intros <;>
      (rintro (_ | _) <;> simp only [Sum.map_inl, Sum.map_inr]);
    { rw [gf] }; { rw [kh] }; { rw [fg] }; { rw [hk] };
    { apply AB }; { apply A'B' }

lemma Ifam.sum_proper_l (A A' B : Ifam α) :
    A ≈ A' → A + B ≈ A' + B := by
  intro _; apply Ifam.sum_proper; { assumption }; { rfl }

lemma Ifam.sum_proper_r (A B B' : Ifam α) :
    B ≈ B' → A + B ≈ A + B' := by
  intro _; apply Ifam.sum_proper; { rfl }; { assumption }

/-- Sum of two multisets -/
def Mset.sum.{u} {α} : Mset.{u} α → Mset.{u} α → Mset α :=
  .lift₂ (⟦ · + · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.sum_proper <;> assumption

instance Mset.Add : Add (Mset.{u} α) where
  add := Mset.sum

lemma Mset.sum_unfold : HAdd.hAdd = Mset.sum (α:=α) := rfl

/-! ### `map` over `+` -/

lemma Ifam.sum_map (f : α → β) (A B : Ifam α) :
    map f (A + B) ≈ map f A + map f B := by
  exists id, id; and_intros; all_goals { rintro (_ | _) <;> rfl }

lemma Mset.sum_map (f : α → β) (A B : Mset α) :
    map f (A + B) = map f A + map f B := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.sum_map

/-! ### `+` is commutative -/

lemma Ifam.sum_comm (A B : Ifam α) : A + B ≈ B + A := by
  exists fun | .inl i => .inr i | .inr j => .inl j,
         fun | .inl j => .inr j | .inr i => .inl i;
  and_intros <;> rintro (_ | _) <;> rfl

instance Mset.sum_Commutative :
    Std.Commutative (HAdd.hAdd (α := Mset α)) where
  comm A B := by
    cases A using Quotient.ind; cases B using Quotient.ind;
    apply Quotient.sound; apply Ifam.sum_comm

/-! ### `+` is unital -/

lemma Ifam.sum_id_r (A : Ifam α) : A + ∅ ≈ A := by
  exists fun | .inl i => i | .inr e => (nomatch e), .inl
  and_intros; { intro _; rfl }; all_goals
    rintro (_ | _); { rfl }; { nofun }

instance Mset.sum_LawfulCommIdentity :
    Std.LawfulCommIdentity (HAdd.hAdd (α := Mset α)) ∅ where
  right_id A := by
    cases A using Quotient.ind; apply Quotient.sound; apply Ifam.sum_id_r

/-! ### `+` is assoc -/

lemma Ifam.sum_assoc (A B C : Ifam α) : (A + B) + C ≈ A + (B + C) := by
  exists fun | .inl (.inl i) => .inl i | .inl (.inr j) => .inr (.inl j)
             | .inr k => .inr (.inr k),
         fun | .inl i => .inl (.inl i) | .inr (.inl j) => .inl (.inr j)
             | .inr (.inr k) => .inr k;
  and_intros; { rintro (_ | _ | _) <;> rfl }; all_goals
    rintro ((_ | _) | _) <;> rfl

instance Mset.sum_Associative :
    Std.Associative (HAdd.hAdd (α := Mset α)) where
  assoc A B C := by
    cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
    apply Quotient.sound; apply Ifam.sum_assoc

/-! ## Big sum -/

/-- Big sum of indexed families -/
def Ifam.bigsum {ι : Type} (A : ι → Ifam α) : Ifam α :=
  .mk (Σ i, (A i).dom) (fun ⟨i, j⟩ => (A i).elem j)

lemma Ifam.bigsum_proper (A A' : ι → Ifam α) :
    (∀ i, A i ≈ A' i) → bigsum A ≈ bigsum A' := by
  intro AA'; have ⟨f, AA'⟩ := Classical.skolem.mp AA';
  have ⟨g, AA'⟩ := Classical.skolem.mp AA';
  exists fun ⟨i, j⟩ => ⟨i, f i j⟩, fun ⟨i, j⟩ => ⟨i, g i j⟩;
  and_intros <;> intro ⟨i, j⟩ <;> have ⟨gf, fg, AA'⟩ := AA' i <;> simp only;
  { rw [gf] }; { rw [fg] }; { apply AA' }

@[simp] lemma Ifam.bigsum_dom (A : ι → Ifam α) :
    (bigsum (α := α) (ι := ι) A).dom = Σ i, (A i).dom := rfl

@[simp] lemma Ifam.bigsum_elem (A : ι → Ifam α) (i j) :
    (bigsum (α := α) (ι := ι) A).elem ⟨i, j⟩ = (A i).elem j := rfl

/-- Big sum of multisets -/
noncomputable def Mset.bigsum.{u} {ι : Type} (A : ι → Mset.{u} α) : Mset.{u} α :=
  ⟦ Ifam.bigsum (fun i => (A i).out) ⟧

/-! ### `map` over `bigsum` -/

lemma Ifam.bigsum_map (f : α → β) (A : ι → Ifam α) :
    map f (bigsum A) ≈ bigsum (fun i => map f (A i)) := by
  exists fun ⟨i, j⟩ => ⟨i, j⟩, fun ⟨i, j⟩ => ⟨i, j⟩;
  and_intros <;> intro ⟨i, j⟩ <;> rfl

lemma Mset.bigsum_map (f : α → β) (A : ι → Mset α) :
    map f (bigsum A) = bigsum (fun i => map f (A i)) := by
  apply Quotient.sound; trans; { apply Ifam.bigsum_map };
  apply Ifam.bigsum_proper; intro i; simp only;
  cases A i using Quotient.ind; trans; swap; { symm; apply Quotient.mk_out };
  apply Ifam.map_proper; apply Quotient.mk_out

/-! ### `bigsum` is commutative -/

lemma Ifam.bigsum_comm {ι ι' : Type} (A : ι → Ifam α) (f : ι → ι') (g : ι' → ι) :
    (∀ j, f (g j) = j) → (∀ i, g (f i) = i) → bigsum A ≈ bigsum (A ∘ g) := by
  intro fg gf;
  exists fun ⟨i, k⟩ => ⟨f i, congrArg (fun i => (A i).dom) (gf i).symm ▸ k⟩,
         fun ⟨j, k⟩ => ⟨g j, k⟩;
  simp only [bigsum_dom, Function.comp_apply];
  and_intros <;> intro ⟨_, _⟩;
  · congr; { rw [fg] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · congr; { rw [gf] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · simp only [bigsum, Function.comp_apply]; congr; { rw [gf] };
    simp only [heq_eqRec_iff_heq, heq_eq_eq]

lemma Mset.bigsum_comm {ι ι' : Type} (A : ι → Mset α) (f : ι → ι') (g : ι' → ι) :
    (∀ i', f (g i') = i') → (∀ i, g (f i) = i) → bigsum A = bigsum (A ∘ g) := by
  intro fg gf; apply Quotient.sound; apply Ifam.bigsum_comm <;> assumption

/-! ### `bigsum` is associative -/

lemma Ifam.bigsum_assoc {ι : Type} {ι' : ι → Type} (A : ∀ ι, ι' ι → Ifam α) :
    bigsum (fun i => bigsum (A i)) ≈ bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  exists fun ⟨i, j, k⟩ => ⟨⟨i, j⟩, k⟩, fun ⟨⟨i, j⟩, k⟩ => ⟨i, j, k⟩;
  and_intros <;> intros <;> rfl

lemma Mset.bigsum_assoc {ι : Type} {ι' : ι → Type} (A : ∀ ι, ι' ι → Mset α) :
    bigsum (fun i => bigsum (A i)) = bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  apply Quotient.sound; trans;
  { apply Ifam.bigsum_proper; intros; apply Quotient.mk_out };
  apply Ifam.bigsum_assoc

/-! ### `empty` as `bigsum` -/

lemma Ifam.empty_bigsum : ∅ ≈ bigsum (ι := Empty) A := by
  exists nofun, nofun; and_intros <;> nofun

lemma Mset.empty_bigsum : ∅ = bigsum (ι := Empty) (α := α) nofun := by
  apply Quotient.sound; apply Ifam.empty_bigsum

/-! ### Unary `bigsum` -/

lemma Ifam.unary_bigsum (A : Ifam α) : bigsum (fun _ : Unit => A) ≈ A := by
  exists fun ⟨_, i⟩ => i, fun i => ⟨(), i⟩; and_intros; iterate 3 { intro _; rfl }

lemma Mset.unary_bigsum (A : Mset α) : bigsum (fun _ : Unit => A) = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  trans; swap; { apply Quotient.mk_out }; apply Ifam.unary_bigsum

/-! ### `+` as `bigsum` -/

lemma Ifam.sum_bigsum (A B : Ifam α) :
    F true = A → F false = B → A + B ≈ bigsum F := by
  intro rfl rfl;
  exists fun | .inl i => ⟨true, i⟩ | .inr i => ⟨false, i⟩,
         fun | ⟨true, i⟩ => .inl i | ⟨false, i⟩ => .inr i;
  and_intros; { rintro ⟨_ | _, _⟩ <;> rfl }; all_goals
    rintro (_ | _) <;> rfl

lemma Mset.sum_bigsum (A B : Mset α) :
    A + B = bigsum (fun b : Bool => if b then A else B) := by
  rw (occs := [1]) [←Quotient.out_eq A, ←Quotient.out_eq B];
  apply Quotient.sound; apply Ifam.sum_bigsum <;> rfl

/-! ## Binary product -/

/-- Product of two indexed families -/
def Ifam.prod {α β} (A : Ifam α) (B : Ifam β) : Ifam (α × β) :=
  .mk (A.dom × B.dom) (fun (i, j) => (A.elem i, B.elem j))

instance Ifam.HMul : HMul (Ifam α) (Ifam β) (Ifam (α × β)) where
  hMul := Ifam.prod

lemma Ifam.mul_unfold : HMul.hMul = Ifam.prod (α:=α) (β:=β) := rfl

@[simp] lemma Ifam.prod_dom (A : Ifam α) (B : Ifam β) :
    (A * B).dom = (A.dom × B.dom) := rfl

@[simp] lemma Ifam.prod_elem (A : Ifam α) (B : Ifam β) i j :
  (A * B).elem (i, j) = (A.elem i, B.elem j) := rfl

lemma Ifam.prod_proper (A A' : Ifam α) (B B' : Ifam β) :
    A ≈ A' → B ≈ B' → A * B ≈ A' * B' := by
  rintro ⟨f, g, fg, gf, AA'⟩ ⟨h, k, kh, hk, BB'⟩;
  exists fun (i, j) => (f i, h j), fun (i', j') => (g i', k j');
  and_intros <;> intro (_, _) <;> simp only;
  { rw [fg, kh]; }; { rw [gf, hk] }; { simp only [prod_elem]; rw [AA', BB'] }

/-- Product of two multisets -/
def Mset.prod {α β} : Mset α → Mset β → Mset (α × β) :=
  .lift₂ (⟦ · * · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.prod_proper <;> assumption

instance Mset.HMul : HMul (Mset α) (Mset β) (Mset (α × β)) where
  hMul := Mset.prod

lemma Mset.prod_unfold : HMul.hMul = Mset.prod (α:=α) (β:=β) := rfl

/-! ### `*` over `map` -/

lemma Mset.prod_map
    (f : α → α') (g : β → β') (A : Mset α) (B : Mset β) :
    map f A * map g B = map (Prod.map f g) (A * B) := by
  cases A using Quotient.ind; cases B using Quotient.ind; rfl

lemma Mset.prod_map_l (f : α → α') (A : Mset α) (B : Mset β) :
    map f A * B = map (Prod.map f id) (A * B) := by
  rw [←prod_map, id_map]

lemma Mset.prod_map_r (g : β → β') (A : Mset α) (B : Mset β) :
    A * (map g B) = Mset.map (Prod.map id g) (A * B) := by
  rw [←prod_map, id_map]

/-! ### `*` is commutative -/

lemma Ifam.prod_comm (A : Ifam α) (B : Ifam β) :
    A * B ≈ Ifam.map Prod.swap (B * A) := by
  exists fun (i, j) => (j, i), fun (j, i) => (i, j);
  and_intros <;> intro (_, _) <;> rfl

lemma Mset.prod_comm (A : Mset α) (B : Mset β) :
    A * B = Mset.map Prod.swap (B * A) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_comm

/-! ### `*` is unital -/

lemma Ifam.prod_id_r (A : Ifam α) (b : β) :
    A * pure (f:=Ifam) b ≈ map (·, b) A := by
  exists fun (i, _) => i, fun i => (i, ());
  and_intros <;> intro _; { trivial }; all_goals rfl

lemma Mset.prod_id_r (A : Mset α) (b : β) :
    A * pure (f:=Mset) b = map (·, b) A := by
  cases A using Quotient.ind; apply Quotient.sound;
  apply Ifam.prod_id_r

lemma Mset.prod_id_l (a : α) (B : Mset β) :
    pure (f:=Mset) a * B = map (a, ·) B := by
  rw [prod_comm, prod_id_r, ←comp_map]; rfl

/-! ### `*` is associative -/

lemma Ifam.prod_assoc_l (A : Ifam α) (B : Ifam β) (C : Ifam γ) :
    (A * B) * C ≈ map (fun (a, (b, c)) => ((a, b), c)) (A * (B * C)) := by
  exists fun ((i, j), k) => (i, (j, k)), fun (i, (j, k)) => ((i, j), k);
  and_intros <;> intro <;> rfl

lemma Mset.prod_assoc_l (A : Mset α) (B : Mset β) (C : Mset γ) :
    (A * B) * C = map (fun (a, (b, c)) => ((a, b), c)) (A * (B * C)) := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_assoc_l

lemma Mset.prod_assoc_r (A : Mset α) (B : Mset β) (C : Mset γ) :
    A * (B * C) = map (fun ((a, b), c) => (a, b, c)) ((A * B) * C) := by
  rw [prod_assoc_l, ←comp_map]; rw (occs := [1]) [←id_map (_ * _)]; rfl

/-! ### `*` distributes over `+` -/

lemma Ifam.prod_sum_distrib_l (A : Ifam α) (B C : Ifam β) :
    A * (B + C) ≈ A * B + A * C := by
  exists fun (i, s) => match s with | .inl j => .inl (i, j) | .inr k => .inr (i, k),
         fun | .inl (i, j) => (i, .inl j) | .inr (i, k) => (i, .inr k);
  and_intros; { rintro (_ | _) <;> rfl }; all_goals
    rintro ⟨_, (_ | _)⟩ <;> rfl

lemma Mset.prod_sum_distrib_l (A : Mset α) (B C : Mset β) :
    A * (B + C) = A * B + A * C := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod_sum_distrib_l

lemma Mset.prod_sum_distrib_r (A B : Mset α) (C : Mset β) :
    (A + B) * C = A * C + B * C := by
  rw [prod_comm, prod_sum_distrib_l, prod_comm C A, prod_comm C B, sum_map,
      ←comp_map, ←comp_map, Prod.swap_swap_eq, id_map, id_map]

/-! ## Applicative -/

/-- `seq` for `Mset`, more universe-polymorphic than `Seq.seq` -/
def Mset.seq {α β : Type*} (F : Mset (α → β)) (A : Mset α) : Mset β :=
  map (fun (f, a) => f a) (F * A)

/-- `Applicative` for `Mset` -/
instance Mset.Applicative : Applicative Mset.{u} where
  seq F A := Mset.seq F (A ())

lemma Mset.seq_unfold (F : Mset (α → β)) (A : Mset α) :
    F <*> A = seq F A := rfl

/-! `LawfulApplicative` is later derived from `LawfulMonad` -/

/-! ## Join -/

/-- `join` for `Ifam` -/
noncomputable def Ifam.join {α} (A : Ifam (Mset α)) : Mset α :=
  Mset.bigsum A.elem

lemma Ifam.join_proper (A B : Ifam (Mset α)) :
    A ≈ B → A.join = B.join := by
  rintro ⟨f, g, fg, gf, AB⟩; apply Quotient.sound;
  exists (fun ⟨i, k⟩ => ⟨f i, congrArg (·.out.dom) (AB i) ▸ k⟩),
         (fun ⟨j, k⟩ => ⟨g j,
           congrArg (·.out.dom) (equiv_elem_eq_symm fg AB j).symm ▸ k⟩);
  and_intros <;> intro ⟨i, k⟩ <;> simp only [bigsum_dom, bigsum_elem]
  · congr; { rw [fg] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · congr; { rw [gf] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · revert k; simp only; generalize AB i = eq; revert eq;
    generalize A.elem i = Ai; generalize B.elem (f i) = Bj; intro rfl _; rfl

/-- `join` for `Mset` -/
noncomputable def Mset.join {α} : Mset (Mset α) → Mset α :=
  .lift (·.join) <| by intros; apply Ifam.join_proper; assumption

/-! ### Join laws -/

lemma Mset.map_join (f : α → β) (A : Mset (Mset α)) :
    map f (join A) = join (map (map f) A) := by
  revert A; apply Quotient.ind; rintro ⟨_, F⟩;
  apply Quotient.sound; trans; { apply Ifam.bigsum_map };
  apply Ifam.bigsum_proper; simp only [Ifam.map_elem];
  intro i; cases F i using Quotient.ind; trans; swap;
  { symm; apply Quotient.mk_out }; apply Ifam.map_proper; apply Quotient.mk_out

lemma Mset.join_map_seq (F : Mset (α → β)) :
    join (map (map · A) F) = seq F A := by
  cases F using Quotient.ind; cases A using Quotient.ind;
  apply Quotient.sound; simp only [Ifam.map_elem]; trans;
  { apply Ifam.bigsum_proper; { intro _; apply Quotient.mk_out } }
  exists fun ⟨i, j⟩ => ⟨i, j⟩, fun ⟨i, j⟩ => ⟨i, j⟩; and_intros <;> { intro _; rfl }

lemma Mset.join_pure (A : Mset α) : join (pure A) = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  simp only [Ifam.pure_elem]; trans; swap; { apply Quotient.mk_out };
  apply Ifam.unary_bigsum

lemma Ifam.bigsum_pure (A : Ifam α) : bigsum (map pure A).elem ≈ A := by
  exists fun ⟨i, _⟩ => i, fun i => ⟨i, ()⟩; and_intros; iterate 3 { intro _; rfl }

lemma Mset.join_pure_map (A : Mset α) : join (map pure A) = A := by
  cases A using Quotient.ind; apply Quotient.sound; trans; swap;
  { apply Ifam.bigsum_pure }; apply Ifam.bigsum_proper;
  intro _; apply Quotient.mk_out

lemma Mset.join_join (A : Mset (Mset (Mset α))) :
    join (join A) = join (map join A) := by
  revert A; apply Quotient.ind; rintro ⟨_, F⟩; apply Quotient.sound;
  unfold join; unfold Ifam.join;
  simp only [Ifam.bigsum_dom, Ifam.map_dom, Ifam.map_elem];
  trans; swap;
  { apply Ifam.bigsum_proper;
    { intro i; rewrite [←Quotient.out_eq (F i), Quotient.lift_mk];
      symm; unfold Mset.bigsum; apply Quotient.mk_out }; }
  exists fun ⟨⟨i, j⟩, k⟩ => ⟨i, ⟨j, k⟩⟩, fun ⟨i, ⟨j, k⟩⟩ => ⟨⟨i, j⟩, k⟩;
  and_intros; iterate 3 { intro _; rfl }

/-! ## Monad -/

/-- Monadic bind for `Mset`, more universe-polymorphic than `Monad.bind` -/
noncomputable def Mset.bind {α β : Type*} (A : Mset α) (K : α → Mset β) : Mset β :=
  join (map K A)

/-- `Monad` for `Mset` -/
noncomputable instance Mset.Monad : Monad Mset.{u} where
  bind := Mset.bind

lemma Mset.bind_unfold : Bind.bind = Mset.bind (α:=α) (β:=β) := rfl

lemma Mset.pure_seq (f : α → β) (A : Mset α) :
    seq (pure f) A = map f A := by rw [seq, prod_id_l, ←comp_map]; rfl

lemma Mset.pure_bind (a : α) (K : α → Mset β) :
    bind (pure a) K = K a := by rw [bind, pure_map, join_pure]

lemma Mset.bind_pure_comp (f : α → β) (A : Mset α) :
    bind A (fun a => pure (f a)) = map f A := by
  rw [bind, ←Function.comp_def, comp_map, join_pure_map]

lemma Mset.bind_map (F : Mset (α → β)) (A : Mset α) :
    bind F (map · A) = seq F A := by apply join_map_seq

lemma Mset.bind_assoc (A : Mset α) (F : α → Mset β) (G : β → Mset γ) :
    bind (bind A F) G = bind A (fun a => bind (F a) G) := by
  have eq : (fun a => bind (F a) G) = join ∘ map G ∘ F := rfl;
  rw [eq]; unfold bind; rw [comp_map, ←join_join, map_join, ←comp_map]

/-- Monad laws for `Mset` -/
instance Mset.LawfulMonad : LawfulMonad Mset.{u} where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq := pure_seq
  pure_bind := pure_bind
  bind_pure_comp := bind_pure_comp
  bind_map := bind_map
  bind_assoc := bind_assoc

lemma Mset.comm_seq_prod (A : Mset α) (B : Mset β) :
    seq (map Prod.mk A) B = seq (map (fun b a => (a, b)) B) A := by
    unfold seq; rw [prod_map_l, prod_map_l, ←comp_map, ←comp_map, prod_comm, ←comp_map]; rfl

/-- Commutative applicative laws for `Mset` -/
instance Mset.CommApplicative : CommApplicative Mset.{u} where
  commutative_prod := comm_seq_prod
