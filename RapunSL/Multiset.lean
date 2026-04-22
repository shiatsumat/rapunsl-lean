module

public import Mathlib.Data.Setoid.Basic

@[expose] public section

/-! # Multisets -/

/-! ## Premultiset -/

/-- Premultiset -/
structure Premultiset.{u} (α : Type u) : Type (max 1 u) where mk ::
  dom : Type
  elem : dom → α

/-! ### Equivalence and setoid for `Premultiset` -/

/-- Equivalence between `Premultiset`s -/
def Premultiset.equiv.{u} (A B : Premultiset.{u} α) : Prop :=
  ∃ f : A.dom → B.dom, ∃ g : B.dom → A.dom,
  (∀ j, f (g j) = j) ∧ (∀ i, g (f i) = i) ∧ ∀ i, A.elem i = B.elem (f i)

/-- Utility for getting the inverse element equality -/
lemma Premultiset.equiv.elem_eq_symm {A B : Premultiset α}
    {f : A.dom → B.dom} {g : B.dom → A.dom} :
    (∀ j, f (g j) = j) → (∀ i, A.elem i = B.elem (f i)) →
    ∀ j, B.elem j = A.elem (g j) := by
  intro fg AB j; rw [AB, fg]

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
def Multiset.{u} (α : Type u) : Type (max 1 u) :=
  Quotient (Premultiset.Setoid.{u} α)

/-! ## Functor -/

/-- `map` for `Premultiset` -/
def Premultiset.map {α β : Type u} (f : α → β) (A : Premultiset α) : Premultiset β :=
  .mk A.dom (fun i => f (A.elem i))

/-- `Functor` for `Premultiset` -/
instance Premultiset.Functor : Functor Premultiset.{u} where
  map := Premultiset.map

lemma Premultiset.map.unfold {α β : Type u} (f : α → β) (A : Premultiset α) :
  f <$> A = Premultiset.map f A := rfl

/-- Functor laws for `Premultiset` -/
instance Premultiset.LawfulFunctor : LawfulFunctor Premultiset.{u} where
  id_map _ := rfl
  comp_map _ _ _ := rfl
  map_const := rfl

@[simp] lemma Premultiset.map.dom (f : α → β) (A : Premultiset α) :
  (f <$> A).dom = A.dom := rfl

@[simp] lemma Premultiset.map.elem (f : α → β) (A : Premultiset α) (i : A.dom) :
  (f <$> A).elem i = f (A.elem i) := rfl

lemma Premultiset.map.proper (A B : Premultiset α) :
    A ≈ B → f <$> A ≈ f <$> B := by
  rintro ⟨g, h, _, _, AB⟩; exists g, h; and_intros; iterate 2 { assumption };
  simp only [dom, elem]; intro _; rw [AB]

/-- `map` for `Multiset` -/
def Multiset.map {α β : Type u} (f : α → β) : Multiset α → Multiset β :=
  .lift (⟦ f <$> · ⟧) <| by
    intros; apply Quotient.sound; apply Premultiset.map.proper; assumption

/-- `Functor` for `Multiset` -/
instance Multiset.Functor : Functor Multiset.{u} where
  map := Multiset.map

lemma Multiset.map.unfold {α β : Type u} (f : α → β) (A : Multiset α) :
  f <$> A = Multiset.map f A := rfl

/-- Functor laws for `Multiset` -/
instance Multiset.LawfulFunctor : LawfulFunctor Multiset.{u} where
  id_map A := by cases A using Quotient.ind; rfl
  comp_map _ _ A := by cases A using Quotient.ind; rfl
  map_const := rfl

/-! ## Empty multiset -/

/-- Empty premultiset -/
instance Premultiset.empty : EmptyCollection (Premultiset α) where
  emptyCollection := .mk Empty nofun

@[simp] lemma Premultiset.empty.dom :
    (∅ : Premultiset α).dom = Empty := rfl

/-- Empty multiset -/
instance Multiset.empty : EmptyCollection (Multiset α) where
  emptyCollection := ⟦ ∅ ⟧

/-! ## Singleton -/

/-- Singleton premultiset -/
instance Premultiset.Pure : Pure Premultiset where
  pure a := .mk Unit (fun _ => a)

lemma Premultiset.pure.unfold (a : α) :
    pure (f:=Premultiset) a = .mk Unit (fun _ => a) := rfl

@[simp] lemma Premultiset.pure.dom (a : α) :
    (pure (f:=Premultiset) a).dom = Unit := rfl

@[simp] lemma Premultiset.pure.elem (a : α) u :
    (pure (f:=Premultiset) a).elem u = a := rfl

/-- Singleton multiset -/
instance Multiset.Pure : Pure Multiset where
  pure a := ⟦ pure a ⟧

lemma Multiset.pure.unfold (a : α) :
    pure (f:=Multiset) a = ⟦ .mk Unit (fun _ => a) ⟧ := rfl

/-! ## `<$>` over `pure` -/

lemma Premultiset.pure.map (f : α → β) (a : α) :
    f <$> pure (f:=Premultiset) a = pure (f a) := rfl

lemma Multiset.pure.map (f : α → β) (a : α) :
    f <$> pure (f:=Multiset) a = pure (f a) := rfl

/-! ## Binary sum -/

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
  .lift₂ (⟦ · + · ⟧) <| by
    intros; apply Quotient.sound; apply Premultiset.sum.proper <;> assumption

instance Multiset.Add : Add (Multiset.{u} α) where
  add := Multiset.sum

lemma Multiset.sum.unfold (A B : Multiset α) :
  A + B = Multiset.sum A B := rfl

/-! ### `<$>` over `+` -/

lemma Premultiset.sum.map (f : α → β) (A B : Premultiset α) :
    f <$> (A + B) ≈ f <$> A + f <$> B := by
  exists id, id; and_intros; all_goals { rintro (_ | _) <;> rfl }

lemma Multiset.sum.map (f : α → β) (A B : Multiset α) :
    f <$> (A + B) = f <$> A + f <$> B := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Premultiset.sum.map

/-! ### `+` is commutative -/

lemma Premultiset.sum.comm (A B : Premultiset α) :
    A + B ≈ B + A := by
  exists fun | .inl i => .inr i | .inr j => .inl j,
         fun | .inl j => .inr j | .inr i => .inl i;
  and_intros <;> rintro (_ | _) <;> rfl

instance Multiset.sum.Commutative :
    Std.Commutative (HAdd.hAdd (α := Multiset α)) where
  comm A B := by
    cases A using Quotient.ind; cases B using Quotient.ind;
    apply Quotient.sound; apply Premultiset.sum.comm

/-! ### `+` is unital -/

lemma Premultiset.sum.id_r {A : Premultiset α} :
    A + ∅ ≈ A := by
  exists fun | .inl i => i | .inr e => (nomatch e), .inl
  and_intros; { intro _; rfl }; all_goals
    rintro (_ | _); { rfl }; { nofun }

instance Multiset.sum.LawfulCommIdentity :
    Std.LawfulCommIdentity (HAdd.hAdd (α := Multiset α)) ∅ where
  right_id A := by
    cases A using Quotient.ind; apply Quotient.sound;
    exact Premultiset.sum.id_r

/-! ### `+` is assoc -/

lemma Premultiset.sum.assoc (A B C : Premultiset α) :
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

/-! ## Big sum -/

/-- Big sum of premultisets -/
def Premultiset.bigsum {ι : Type} (A : ι → Premultiset α) : Premultiset α :=
  .mk (Σ i, (A i).dom) (fun ⟨i, j⟩ => (A i).elem j)

lemma Premultiset.bigsum.proper (A A' : ι → Premultiset α) :
    (∀ i, A i ≈ A' i) → bigsum A ≈ bigsum A' := by
  intro AA'; have ⟨f, AA'⟩ := Classical.skolem.mp AA';
  have ⟨g, AA'⟩ := Classical.skolem.mp AA';
  exists fun ⟨i, j⟩ => ⟨i, f i j⟩, fun ⟨i, j⟩ => ⟨i, g i j⟩;
  and_intros <;> intro ⟨i, j⟩ <;> have ⟨gf, fg, AA'⟩ := AA' i <;> simp only;
  { rw [gf] }; { rw [fg] }; { apply AA' }

@[simp] lemma Premultiset.bigsum.dom (A : ι → Premultiset α) :
    (bigsum (α := α) (ι := ι) A).dom = Σ i, (A i).dom := rfl

@[simp] lemma Premultiset.bigsum.elem (A : ι → Premultiset α) (i j) :
    (bigsum (α := α) (ι := ι) A).elem ⟨i, j⟩ = (A i).elem j := rfl

/-- Big sum of multisets -/
noncomputable def Multiset.bigsum.{u} {ι : Type}
  (A : ι → Multiset.{u} α) : Multiset.{u} α :=
  ⟦ Premultiset.bigsum (fun i => (A i).out) ⟧

/-! ### `<$>` over `bigsum` -/

lemma Premultiset.bigsum.map (f : α → β) (A : ι → Premultiset α) :
    f <$> bigsum A ≈ bigsum (fun i => f <$> A i) := by
  exists fun ⟨i, j⟩ => ⟨i, j⟩, fun ⟨i, j⟩ => ⟨i, j⟩;
  and_intros <;> intro ⟨i, j⟩ <;> rfl

lemma Multiset.bigsum.map (f : α → β) (A : ι → Multiset α) :
    f <$> bigsum A = bigsum (fun i => f <$> A i) := by
  apply Quotient.sound; trans; { apply Premultiset.bigsum.map };
  apply Premultiset.bigsum.proper; intro i; simp only;
  cases A i using Quotient.ind; trans; swap; { symm; apply Quotient.mk_out };
  apply Premultiset.map.proper; apply Quotient.mk_out

/-! ### `bigsum` is commutative -/

lemma Premultiset.bigsum.comm {ι ι' : Type}
    (A : ι → Premultiset α) (f : ι → ι') (g : ι' → ι) :
    (∀ j, f (g j) = j) → (∀ i, g (f i) = i) →
    bigsum A ≈ bigsum (A ∘ g) := fun fg gf => by
  exists fun ⟨i, k⟩ => ⟨f i, congrArg (fun i => (A i).dom) (gf i).symm ▸ k⟩,
         fun ⟨j, k⟩ => ⟨g j, k⟩;
  simp only [dom, Function.comp_apply];
  and_intros <;> intro ⟨_, _⟩;
  · congr; { rw [fg] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · congr; { rw [gf] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · simp only [bigsum, Function.comp_apply]; congr; { rw [gf] };
    simp only [heq_eqRec_iff_heq, heq_eq_eq]

lemma Multiset.bigsum.comm {ι ι' : Type}
    (A : ι → Multiset α) (f : ι → ι') (g : ι' → ι) :
    (∀ i', f (g i') = i') → (∀ i, g (f i) = i) →
    bigsum A = bigsum (A ∘ g) := fun fg gf => by
  apply Quotient.sound; apply Premultiset.bigsum.comm <;> assumption

/-! ### `bigsum` is associative -/

lemma Premultiset.bigsum.assoc {ι : Type} {ι' : ι → Type}
    (A : ∀ ι, ι' ι → Premultiset α) :
    bigsum (fun i => bigsum (A i)) ≈
      bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  exists fun ⟨i, j, k⟩ => ⟨⟨i, j⟩, k⟩, fun ⟨⟨i, j⟩, k⟩ => ⟨i, j, k⟩;
  and_intros <;> intros <;> rfl

lemma Multiset.bigsum.assoc {ι : Type} {ι' : ι → Type}
    (A : ∀ ι, ι' ι → Multiset α) :
    bigsum (fun i => bigsum (A i)) = bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  apply Quotient.sound; trans;
  { apply Premultiset.bigsum.proper; intros; apply Quotient.mk_out };
  apply Premultiset.bigsum.assoc

/-! ### `empty` as `bigsum` -/

lemma Premultiset.empty_bigsum :
    ∅ ≈ bigsum (ι := Empty) A := by
  exists nofun, nofun; and_intros <;> nofun

lemma Multiset.empty_bigsum :
    ∅ = bigsum (ι := Empty) (α := α) nofun := by
  apply Quotient.sound; apply Premultiset.empty_bigsum

/-! ### Unary `bigsum` -/

lemma Premultiset.unary_bigsum (A : Premultiset α) :
    bigsum (fun _ : Unit => A) ≈ A := by
  exists fun ⟨_, i⟩ => i, fun i => ⟨(), i⟩; and_intros; iterate 3 { intro _; rfl }

lemma Multiset.unary_bigsum (A : Multiset α) :
    bigsum (fun _ : Unit => A) = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  trans; swap; { apply Quotient.mk_out }; apply Premultiset.unary_bigsum

/-! ### `+` as `bigsum` -/

lemma Premultiset.sum_bigsum (A B : Premultiset α) :
    F true = A → F false = B →
    A + B ≈ bigsum F := by
  intro rfl rfl;
  exists fun | .inl i => ⟨true, i⟩ | .inr i => ⟨false, i⟩,
         fun | ⟨true, i⟩ => .inl i | ⟨false, i⟩ => .inr i;
  and_intros; { rintro ⟨_ | _, _⟩ <;> rfl }; all_goals
    rintro (_ | _) <;> rfl

lemma Multiset.sum_bigsum (A B : Multiset α) :
    A + B = bigsum (fun b : Bool => if b then A else B) := by
  rw (occs := [1]) [←Quotient.out_eq A, ←Quotient.out_eq B];
  apply Quotient.sound; apply Premultiset.sum_bigsum <;> rfl

/-! ## Binary product -/

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

@[simp] lemma Premultiset.prod.elem (A : Premultiset α) (B : Premultiset β) i j :
  (A * B).elem (i, j) = (A.elem i, B.elem j) := rfl

lemma Premultiset.prod.proper (A A' : Premultiset α) (B B' : Premultiset β) :
    A ≈ A' → B ≈ B' → A * B ≈ A' * B' := by
  rintro ⟨f, g, fg, gf, AA'⟩ ⟨h, k, kh, hk, BB'⟩;
  exists fun (i, j) => (f i, h j), fun (i', j') => (g i', k j');
  and_intros <;> intro (_, _) <;> simp only;
  { rw [fg, kh]; }; { rw [gf, hk] }; { simp only [elem]; rw [AA', BB'] }

/-- Product of two multisets -/
def Multiset.prod {α β} : Multiset α → Multiset β → Multiset (α × β) :=
  .lift₂ (⟦ · * · ⟧) <| by
    intros; apply Quotient.sound; apply Premultiset.prod.proper <;> assumption

instance Multiset.HMul : HMul (Multiset α) (Multiset β) (Multiset (α × β)) where
  hMul := Multiset.prod

lemma Multiset.prod.unfold {A : Multiset α} {B : Multiset β} :
    A * B = Multiset.prod A B := rfl

/-! ### `*` over `<$>` -/

lemma Multiset.prod.map
    (f : α → α') (g : β → β') (A : Multiset α) (B : Multiset β) :
    (f <$> A) * (g <$> B) = Prod.map f g <$> (A * B) := by
  cases A using Quotient.ind; cases B using Quotient.ind; rfl

lemma Multiset.prod.map_l (f : α → α') (A : Multiset α) (B : Multiset β) :
    (f <$> A) * B = Prod.map f id <$> (A * B) := by
  rw [←prod.map, id_map]

lemma Multiset.prod.map_r (g : β → β') (A : Multiset α) (B : Multiset β) :
    A * (g <$> B) = Prod.map id g <$> (A * B) := by
  rw [←prod.map, id_map]

/-! ### `*` is commutative -/

lemma Premultiset.prod.comm (A : Premultiset α) (B : Premultiset β) :
    A * B ≈ Prod.swap <$> (B * A) := by
  exists fun (i, j) => (j, i), fun (j, i) => (i, j);
  and_intros <;> intro (_, _) <;> rfl

lemma Multiset.prod.comm (A : Multiset α) (B : Multiset β) :
    A * B = Prod.swap <$> (B * A) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Premultiset.prod.comm

/-! ### `*` is unital -/

lemma Premultiset.prod.id_r (A : Premultiset α) (b : β) :
    A * pure (f:=Premultiset) b ≈ (·, b) <$> A := by
  exists fun (i, _) => i, fun i => (i, ());
  and_intros; { intros; trivial }; all_goals
    rintro ⟨_, _⟩; rfl

lemma Multiset.prod.id_r (A : Multiset α) (b : β) :
    A * pure (f:=Multiset) b = (·, b) <$> A := by
  cases A using Quotient.ind; apply Quotient.sound;
  apply Premultiset.prod.id_r

lemma Multiset.prod.id_l (a : α) (B : Multiset β) :
    pure (f:=Multiset) a * B = (a, ·) <$> B := by
  rw [prod.comm, prod.id_r, ←comp_map]; rfl

/-! ### `*` is associative -/

lemma Premultiset.prod.assoc_l
    (A : Premultiset α) (B : Premultiset β) (C : Premultiset γ) :
    (A * B) * C ≈ (fun (a, (b, c)) => ((a, b), c)) <$> (A * (B * C)) := by
  exists fun ((i, j), k) => (i, (j, k)), fun (i, (j, k)) => ((i, j), k);
  and_intros <;> intro <;> rfl

lemma Multiset.prod.assoc_l (A : Multiset α) (B : Multiset β) (C : Multiset γ) :
    (A * B) * C = (fun (a, (b, c)) => ((a, b), c)) <$> (A * (B * C)) := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Premultiset.prod.assoc_l

lemma Multiset.prod.assoc_r (A : Multiset α) (B : Multiset β) (C : Multiset γ) :
    A * (B * C) = (fun ((a, b), c) => (a, b, c)) <$> ((A * B) * C) := by
  rw [prod.assoc_l, ←comp_map]; rw (occs := [1]) [←id_map (_ * _)]; rfl

/-! ### `*` distributes over `+` -/

lemma Premultiset.prod.sum.distrib_l (A : Premultiset α) (B C : Premultiset β) :
    A * (B + C) ≈ A * B + A * C := by
  exists fun (i, s) => match s with | .inl j => .inl (i, j) | .inr k => .inr (i, k),
         fun | .inl (i, j) => (i, .inl j) | .inr (i, k) => (i, .inr k);
  and_intros; { rintro (_ | _) <;> rfl }; all_goals
    rintro ⟨_, (_ | _)⟩ <;> rfl

lemma Multiset.prod.sum.distrib_l (A : Multiset α) (B C : Multiset β) :
    A * (B + C) = A * B + A * C := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Premultiset.prod.sum.distrib_l

lemma Multiset.prod.sum.distrib_r (A B : Multiset α) (C : Multiset β) :
    (A + B) * C = A * C + B * C := by
  rw [prod.comm, prod.sum.distrib_l, prod.comm C A, prod.comm C B, sum.map,
      ←comp_map, ←comp_map, Prod.swap_swap_eq, id_map, id_map]

/-! ## Applicative -/

/-- `Applicative` for `Multiset` -/
instance Multiset.Applicative : Applicative Multiset.{u} where
  seq F A := (fun (f, a) => f a) <$> (F * A ())

lemma Multiset.seq.unfold (F : Multiset (α → β)) A :
    F <*> A = (fun (f, a) => f a) <$> (F * A) := rfl

/-! `LawfulApplicative` is later derived from `LawfulMonad` -/

/-! ## Join -/

/-- `join` for `Premultiset` -/
noncomputable def Premultiset.join {α} (A : Premultiset (Multiset α)) : Multiset α :=
  Multiset.bigsum A.elem

lemma Premultiset.join.proper (A B : Premultiset (Multiset α)) :
    A ≈ B → A.join = B.join := by
  rintro ⟨f, g, fg, gf, AB⟩; apply Quotient.sound;
  exists (fun ⟨i, k⟩ => ⟨f i, congrArg (·.out.dom) (AB i) ▸ k⟩),
         (fun ⟨j, k⟩ => ⟨g j,
           congrArg (·.out.dom) (equiv.elem_eq_symm fg AB j).symm ▸ k⟩);
  and_intros <;> intro ⟨i, k⟩ <;> simp only [bigsum.dom, bigsum.elem]
  · congr; { rw [fg] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · congr; { rw [gf] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · revert k; simp only; generalize AB i = eq; revert eq;
    generalize A.elem i = Ai; generalize B.elem (f i) = Bj; intro rfl _; rfl

/-- `join` for `Multiset` -/
noncomputable def Multiset.join {α} : Multiset (Multiset α) → Multiset α :=
  .lift (·.join) <| by intros; apply Premultiset.join.proper; assumption

/-! ### Join laws -/

lemma Multiset.map_join (f : α → β) (A : Multiset (Multiset α)) :
    f <$> join A = join ((f <$> ·) <$> A) := by
  revert A; apply Quotient.ind; rintro ⟨_, F⟩;
  apply Quotient.sound; trans; { apply Premultiset.bigsum.map };
  apply Premultiset.bigsum.proper; simp only [Premultiset.map.elem];
  intro i; cases F i using Quotient.ind; trans; swap;
  { symm; apply Quotient.mk_out }; apply Premultiset.map.proper; apply Quotient.mk_out

lemma Multiset.join_map_seq (F : Multiset (α → β)) :
    join ((· <$> A) <$> F) = F <*> A := by
  cases F using Quotient.ind; cases A using Quotient.ind;
  apply Quotient.sound; simp only [Premultiset.map.elem]; trans;
  { apply Premultiset.bigsum.proper; { intro _; apply Quotient.mk_out } }
  exists fun ⟨i, j⟩ => ⟨i, j⟩, fun ⟨i, j⟩ => ⟨i, j⟩; and_intros <;> { intro _; rfl }

lemma Multiset.join_pure (A : Multiset α) :
    join (pure A) = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  simp only [Premultiset.pure.elem]; trans; swap; { apply Quotient.mk_out };
  apply Premultiset.unary_bigsum

lemma Premultiset.bigsum_pure (A : Premultiset α) :
    bigsum (pure <$> A).elem ≈ A := by
  exists fun ⟨i, _⟩ => i, fun i => ⟨i, ()⟩; and_intros; iterate 3 { intro _; rfl }

lemma Multiset.join_pure_map (A : Multiset α) :
    join (pure <$> A) = A := by
  cases A using Quotient.ind; apply Quotient.sound; trans; swap;
  { apply Premultiset.bigsum_pure }; apply Premultiset.bigsum.proper;
  intro _; apply Quotient.mk_out

lemma Multiset.join_join (A : Multiset (Multiset (Multiset α))) :
    join (join A) = join (join <$> A) := by
  revert A; apply Quotient.ind; rintro ⟨_, F⟩; apply Quotient.sound;
  unfold join; unfold Premultiset.join;
  simp only [Premultiset.bigsum.dom, Premultiset.map.dom, Premultiset.map.elem];
  trans; swap;
  { apply Premultiset.bigsum.proper;
    { intro i; rewrite [←Quotient.out_eq (F i), Quotient.lift_mk];
      symm; unfold Multiset.bigsum; apply Quotient.mk_out }; }
  exists fun ⟨⟨i, j⟩, k⟩ => ⟨i, ⟨j, k⟩⟩, fun ⟨i, ⟨j, k⟩⟩ => ⟨⟨i, j⟩, k⟩;
  and_intros; iterate 3 { intro _; rfl }

/-! ## Monad -/

/-- `Monad` for `Multiset` -/
noncomputable instance Multiset.Monad : Monad Multiset where
  bind A K := join (K <$> A)

lemma Multiset.bind.unfold (A : Multiset α) (K : α → Multiset β) :
    A >>= K = join (K <$> A) := rfl

/-- Monad laws for `Multiset` -/
instance Multiset.LawfulMonad : LawfulMonad Multiset where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := by
    rw [seq.unfold, prod.id_l, ←comp_map]; rfl
  pure_bind _ _ := by
    rw [bind.unfold, pure.map, join_pure]
  bind_pure_comp _ _ := by
    rw [bind.unfold, ←Function.comp_def, comp_map, join_pure_map]
  bind_map _ _ := by apply join_map_seq
  bind_assoc A F G := by
    have eq : (F · >>= G) = join ∘ (G <$> F ·) := rfl;
    rw [bind.unfold, bind.unfold, bind.unfold, eq];
    rw [comp_map, ←join_join, map_join, ←comp_map]; rfl
