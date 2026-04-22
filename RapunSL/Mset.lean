module

public import Mathlib.Data.Setoid.Basic

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
lemma Ifam.equiv.elem_eq_symm {A B : Ifam α}
    {f : A.dom → B.dom} {g : B.dom → A.dom} :
    (∀ j, f (g j) = j) → (∀ i, A.elem i = B.elem (f i)) →
    ∀ j, B.elem j = A.elem (g j) := by
  intro fg AB j; rw [AB, fg]

lemma Ifam.equiv.is_equiv :
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
  Setoid.mk (Ifam.equiv.{u}) Ifam.equiv.is_equiv

/-! ## `Mset`: Multiset, possibly infinite -/

/-- Multiset, possibly infinite -/
def Mset.{u} (α : Type u) : Type (max 1 u) :=
  Quotient (Ifam.Setoid.{u} α)

/-! ## Functor -/

/-- `map` for `Ifam` -/
def Ifam.map {α β : Type u} (f : α → β) (A : Ifam α) : Ifam β :=
  .mk A.dom (fun i => f (A.elem i))

/-- `Functor` for `Ifam` -/
instance Ifam.Functor : Functor Ifam.{u} where
  map := Ifam.map

lemma Ifam.map.unfold {α β : Type u} (f : α → β) (A : Ifam α) :
  f <$> A = Ifam.map f A := rfl

/-- Functor laws for `Ifam` -/
instance Ifam.LawfulFunctor : LawfulFunctor Ifam.{u} where
  id_map _ := rfl
  comp_map _ _ _ := rfl
  map_const := rfl

@[simp] lemma Ifam.map.dom (f : α → β) (A : Ifam α) :
  (f <$> A).dom = A.dom := rfl

@[simp] lemma Ifam.map.elem (f : α → β) (A : Ifam α) (i : A.dom) :
  (f <$> A).elem i = f (A.elem i) := rfl

lemma Ifam.map.proper (A B : Ifam α) :
    A ≈ B → f <$> A ≈ f <$> B := by
  rintro ⟨g, h, _, _, AB⟩; exists g, h; and_intros; iterate 2 { assumption };
  simp only [dom, elem]; intro _; rw [AB]

/-- `map` for `Mset` -/
def Mset.map {α β : Type u} (f : α → β) : Mset α → Mset β :=
  .lift (⟦ f <$> · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.map.proper; assumption

/-- `Functor` for `Mset` -/
instance Mset.Functor : Functor Mset.{u} where
  map := Mset.map

lemma Mset.map.unfold {α β : Type u} (f : α → β) (A : Mset α) :
  f <$> A = Mset.map f A := rfl

/-- Functor laws for `Mset` -/
instance Mset.LawfulFunctor : LawfulFunctor Mset.{u} where
  id_map A := by cases A using Quotient.ind; rfl
  comp_map _ _ A := by cases A using Quotient.ind; rfl
  map_const := rfl

/-! ## Empty multiset -/

/-- Empty indexed family -/
instance Ifam.empty : EmptyCollection (Ifam α) where
  emptyCollection := .mk Empty nofun

@[simp] lemma Ifam.empty.dom :
    (∅ : Ifam α).dom = Empty := rfl

/-- Empty multiset -/
instance Mset.empty : EmptyCollection (Mset α) where
  emptyCollection := ⟦ ∅ ⟧

/-! ## Singleton -/

/-- Singleton indexed family -/
instance Ifam.Pure : Pure Ifam where
  pure a := .mk Unit (fun _ => a)

lemma Ifam.pure.unfold (a : α) :
    pure (f:=Ifam) a = .mk Unit (fun _ => a) := rfl

@[simp] lemma Ifam.pure.dom (a : α) :
    (pure (f:=Ifam) a).dom = Unit := rfl

@[simp] lemma Ifam.pure.elem (a : α) u :
    (pure (f:=Ifam) a).elem u = a := rfl

/-- Singleton multiset -/
instance Mset.Pure : Pure Mset where
  pure a := ⟦ pure a ⟧

lemma Mset.pure.unfold (a : α) :
    pure (f:=Mset) a = ⟦ .mk Unit (fun _ => a) ⟧ := rfl

/-! ## `<$>` over `pure` -/

lemma Ifam.pure.map (f : α → β) (a : α) :
    f <$> pure (f:=Ifam) a = pure (f a) := rfl

lemma Mset.pure.map (f : α → β) (a : α) :
    f <$> pure (f:=Mset) a = pure (f a) := rfl

/-! ## Binary sum -/

/-- Sum of two indexed families -/
def Ifam.sum {α} (A B : Ifam α) : Ifam α :=
  .mk (A.dom ⊕ B.dom) (fun s => s.casesOn A.elem B.elem)

instance Ifam.Add : Add (Ifam.{u} α) where
  add := Ifam.sum

lemma Ifam.sum.unfold (A B : Ifam α) :
  A + B = Ifam.sum A B := rfl

@[simp] lemma Ifam.sum.dom (A B : Ifam α) :
  (A + B).dom = (A.dom ⊕ B.dom) := rfl

@[simp] lemma Ifam.sum.elem_inl (A B : Ifam α) {i} :
  (A + B).elem (.inl i) = A.elem i := rfl

@[simp] lemma Ifam.sum.elem_inr (A B : Ifam α) {i} :
  (A + B).elem (.inr i) = B.elem i := rfl

lemma Ifam.sum.proper (A A' B B' : Ifam α) :
    A ≈ A' → B ≈ B' → A + B ≈ A' + B' :=
  fun ⟨f, g, gf, fg, AB⟩ ⟨h, k, kh, hk, A'B'⟩ => by
    exists .map f h, .map g k;
    and_intros <;>
      (rintro (_ | _) <;> simp only [Sum.map_inl, Sum.map_inr]);
    { rw [gf] }; { rw [kh] }; { rw [fg] }; { rw [hk] };
    { apply AB }; { apply A'B' }

lemma Ifam.sum.proper_l (A A' B : Ifam α) :
    A ≈ A' → A + B ≈ A' + B := by
  intro _; apply Ifam.sum.proper; { assumption }; { rfl }

lemma Ifam.sum.proper_r (A B B' : Ifam α) :
    B ≈ B' → A + B ≈ A + B' := by
  intro _; apply Ifam.sum.proper; { rfl }; { assumption }

/-- Sum of two multisets -/
def Mset.sum.{u} {α} : Mset.{u} α → Mset.{u} α → Mset α :=
  .lift₂ (⟦ · + · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.sum.proper <;> assumption

instance Mset.Add : Add (Mset.{u} α) where
  add := Mset.sum

lemma Mset.sum.unfold (A B : Mset α) :
  A + B = Mset.sum A B := rfl

/-! ### `<$>` over `+` -/

lemma Ifam.sum.map (f : α → β) (A B : Ifam α) :
    f <$> (A + B) ≈ f <$> A + f <$> B := by
  exists id, id; and_intros; all_goals { rintro (_ | _) <;> rfl }

lemma Mset.sum.map (f : α → β) (A B : Mset α) :
    f <$> (A + B) = f <$> A + f <$> B := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.sum.map

/-! ### `+` is commutative -/

lemma Ifam.sum.comm (A B : Ifam α) : A + B ≈ B + A := by
  exists fun | .inl i => .inr i | .inr j => .inl j,
         fun | .inl j => .inr j | .inr i => .inl i;
  and_intros <;> rintro (_ | _) <;> rfl

instance Mset.sum.Commutative :
    Std.Commutative (HAdd.hAdd (α := Mset α)) where
  comm A B := by
    cases A using Quotient.ind; cases B using Quotient.ind;
    apply Quotient.sound; apply Ifam.sum.comm

/-! ### `+` is unital -/

lemma Ifam.sum.id_r {A : Ifam α} : A + ∅ ≈ A := by
  exists fun | .inl i => i | .inr e => (nomatch e), .inl
  and_intros; { intro _; rfl }; all_goals
    rintro (_ | _); { rfl }; { nofun }

instance Mset.sum.LawfulCommIdentity :
    Std.LawfulCommIdentity (HAdd.hAdd (α := Mset α)) ∅ where
  right_id A := by
    cases A using Quotient.ind; apply Quotient.sound;
    exact Ifam.sum.id_r

/-! ### `+` is assoc -/

lemma Ifam.sum.assoc (A B C : Ifam α) : (A + B) + C ≈ A + (B + C) := by
  exists fun | .inl (.inl i) => .inl i | .inl (.inr j) => .inr (.inl j)
             | .inr k => .inr (.inr k),
         fun | .inl i => .inl (.inl i) | .inr (.inl j) => .inl (.inr j)
             | .inr (.inr k) => .inr k;
  and_intros; { rintro (_ | _ | _) <;> rfl }; all_goals
    rintro ((_ | _) | _) <;> rfl

instance Mset.sum.Associative :
    Std.Associative (HAdd.hAdd (α := Mset α)) where
  assoc A B C := by
    cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
    apply Quotient.sound; apply Ifam.sum.assoc

/-! ## Big sum -/

/-- Big sum of indexed families -/
def Ifam.bigsum {ι : Type} (A : ι → Ifam α) : Ifam α :=
  .mk (Σ i, (A i).dom) (fun ⟨i, j⟩ => (A i).elem j)

lemma Ifam.bigsum.proper (A A' : ι → Ifam α) :
    (∀ i, A i ≈ A' i) → bigsum A ≈ bigsum A' := by
  intro AA'; have ⟨f, AA'⟩ := Classical.skolem.mp AA';
  have ⟨g, AA'⟩ := Classical.skolem.mp AA';
  exists fun ⟨i, j⟩ => ⟨i, f i j⟩, fun ⟨i, j⟩ => ⟨i, g i j⟩;
  and_intros <;> intro ⟨i, j⟩ <;> have ⟨gf, fg, AA'⟩ := AA' i <;> simp only;
  { rw [gf] }; { rw [fg] }; { apply AA' }

@[simp] lemma Ifam.bigsum.dom (A : ι → Ifam α) :
    (bigsum (α := α) (ι := ι) A).dom = Σ i, (A i).dom := rfl

@[simp] lemma Ifam.bigsum.elem (A : ι → Ifam α) (i j) :
    (bigsum (α := α) (ι := ι) A).elem ⟨i, j⟩ = (A i).elem j := rfl

/-- Big sum of multisets -/
noncomputable def Mset.bigsum.{u} {ι : Type} (A : ι → Mset.{u} α) : Mset.{u} α :=
  ⟦ Ifam.bigsum (fun i => (A i).out) ⟧

/-! ### `<$>` over `bigsum` -/

lemma Ifam.bigsum.map (f : α → β) (A : ι → Ifam α) :
    f <$> bigsum A ≈ bigsum (fun i => f <$> A i) := by
  exists fun ⟨i, j⟩ => ⟨i, j⟩, fun ⟨i, j⟩ => ⟨i, j⟩;
  and_intros <;> intro ⟨i, j⟩ <;> rfl

lemma Mset.bigsum.map (f : α → β) (A : ι → Mset α) :
    f <$> bigsum A = bigsum (fun i => f <$> A i) := by
  apply Quotient.sound; trans; { apply Ifam.bigsum.map };
  apply Ifam.bigsum.proper; intro i; simp only;
  cases A i using Quotient.ind; trans; swap; { symm; apply Quotient.mk_out };
  apply Ifam.map.proper; apply Quotient.mk_out

/-! ### `bigsum` is commutative -/

lemma Ifam.bigsum.comm {ι ι' : Type} (A : ι → Ifam α) (f : ι → ι') (g : ι' → ι) :
    (∀ j, f (g j) = j) → (∀ i, g (f i) = i) → bigsum A ≈ bigsum (A ∘ g) := by
  intro fg gf;
  exists fun ⟨i, k⟩ => ⟨f i, congrArg (fun i => (A i).dom) (gf i).symm ▸ k⟩,
         fun ⟨j, k⟩ => ⟨g j, k⟩;
  simp only [dom, Function.comp_apply];
  and_intros <;> intro ⟨_, _⟩;
  · congr; { rw [fg] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · congr; { rw [gf] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · simp only [bigsum, Function.comp_apply]; congr; { rw [gf] };
    simp only [heq_eqRec_iff_heq, heq_eq_eq]

lemma Mset.bigsum.comm {ι ι' : Type} (A : ι → Mset α) (f : ι → ι') (g : ι' → ι) :
    (∀ i', f (g i') = i') → (∀ i, g (f i) = i) → bigsum A = bigsum (A ∘ g) := by
  intro fg gf; apply Quotient.sound; apply Ifam.bigsum.comm <;> assumption

/-! ### `bigsum` is associative -/

lemma Ifam.bigsum.assoc {ι : Type} {ι' : ι → Type} (A : ∀ ι, ι' ι → Ifam α) :
    bigsum (fun i => bigsum (A i)) ≈ bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  exists fun ⟨i, j, k⟩ => ⟨⟨i, j⟩, k⟩, fun ⟨⟨i, j⟩, k⟩ => ⟨i, j, k⟩;
  and_intros <;> intros <;> rfl

lemma Mset.bigsum.assoc {ι : Type} {ι' : ι → Type} (A : ∀ ι, ι' ι → Mset α) :
    bigsum (fun i => bigsum (A i)) = bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  apply Quotient.sound; trans;
  { apply Ifam.bigsum.proper; intros; apply Quotient.mk_out };
  apply Ifam.bigsum.assoc

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

lemma Ifam.mul.unfold (A : Ifam α) (B : Ifam β) :
    A * B = Ifam.prod A B := rfl

@[simp] lemma Ifam.prod.dom (A : Ifam α) (B : Ifam β) :
    (A * B).dom = (A.dom × B.dom) := rfl

@[simp] lemma Ifam.prod.elem (A : Ifam α) (B : Ifam β) i j :
  (A * B).elem (i, j) = (A.elem i, B.elem j) := rfl

lemma Ifam.prod.proper (A A' : Ifam α) (B B' : Ifam β) :
    A ≈ A' → B ≈ B' → A * B ≈ A' * B' := by
  rintro ⟨f, g, fg, gf, AA'⟩ ⟨h, k, kh, hk, BB'⟩;
  exists fun (i, j) => (f i, h j), fun (i', j') => (g i', k j');
  and_intros <;> intro (_, _) <;> simp only;
  { rw [fg, kh]; }; { rw [gf, hk] }; { simp only [elem]; rw [AA', BB'] }

/-- Product of two multisets -/
def Mset.prod {α β} : Mset α → Mset β → Mset (α × β) :=
  .lift₂ (⟦ · * · ⟧) <| by
    intros; apply Quotient.sound; apply Ifam.prod.proper <;> assumption

instance Mset.HMul : HMul (Mset α) (Mset β) (Mset (α × β)) where
  hMul := Mset.prod

lemma Mset.prod.unfold {A : Mset α} {B : Mset β} :
    A * B = Mset.prod A B := rfl

/-! ### `*` over `<$>` -/

lemma Mset.prod.map
    (f : α → α') (g : β → β') (A : Mset α) (B : Mset β) :
    (f <$> A) * (g <$> B) = Prod.map f g <$> (A * B) := by
  cases A using Quotient.ind; cases B using Quotient.ind; rfl

lemma Mset.prod.map_l (f : α → α') (A : Mset α) (B : Mset β) :
    (f <$> A) * B = Prod.map f id <$> (A * B) := by
  rw [←prod.map, id_map]

lemma Mset.prod.map_r (g : β → β') (A : Mset α) (B : Mset β) :
    A * (g <$> B) = Prod.map id g <$> (A * B) := by
  rw [←prod.map, id_map]

/-! ### `*` is commutative -/

lemma Ifam.prod.comm (A : Ifam α) (B : Ifam β) :
    A * B ≈ Prod.swap <$> (B * A) := by
  exists fun (i, j) => (j, i), fun (j, i) => (i, j);
  and_intros <;> intro (_, _) <;> rfl

lemma Mset.prod.comm (A : Mset α) (B : Mset β) :
    A * B = Prod.swap <$> (B * A) := by
  cases A using Quotient.ind; cases B using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod.comm

/-! ### `*` is unital -/

lemma Ifam.prod.id_r (A : Ifam α) (b : β) :
    A * pure (f:=Ifam) b ≈ (·, b) <$> A := by
  exists fun (i, _) => i, fun i => (i, ());
  and_intros <;> intro _; { trivial }; all_goals rfl

lemma Mset.prod.id_r (A : Mset α) (b : β) :
    A * pure (f:=Mset) b = (·, b) <$> A := by
  cases A using Quotient.ind; apply Quotient.sound;
  apply Ifam.prod.id_r

lemma Mset.prod.id_l (a : α) (B : Mset β) :
    pure (f:=Mset) a * B = (a, ·) <$> B := by
  rw [prod.comm, prod.id_r, ←comp_map]; rfl

/-! ### `*` is associative -/

lemma Ifam.prod.assoc_l (A : Ifam α) (B : Ifam β) (C : Ifam γ) :
    (A * B) * C ≈ (fun (a, (b, c)) => ((a, b), c)) <$> (A * (B * C)) := by
  exists fun ((i, j), k) => (i, (j, k)), fun (i, (j, k)) => ((i, j), k);
  and_intros <;> intro <;> rfl

lemma Mset.prod.assoc_l (A : Mset α) (B : Mset β) (C : Mset γ) :
    (A * B) * C = (fun (a, (b, c)) => ((a, b), c)) <$> (A * (B * C)) := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod.assoc_l

lemma Mset.prod.assoc_r (A : Mset α) (B : Mset β) (C : Mset γ) :
    A * (B * C) = (fun ((a, b), c) => (a, b, c)) <$> ((A * B) * C) := by
  rw [prod.assoc_l, ←comp_map]; rw (occs := [1]) [←id_map (_ * _)]; rfl

/-! ### `*` distributes over `+` -/

lemma Ifam.prod.sum.distrib_l (A : Ifam α) (B C : Ifam β) :
    A * (B + C) ≈ A * B + A * C := by
  exists fun (i, s) => match s with | .inl j => .inl (i, j) | .inr k => .inr (i, k),
         fun | .inl (i, j) => (i, .inl j) | .inr (i, k) => (i, .inr k);
  and_intros; { rintro (_ | _) <;> rfl }; all_goals
    rintro ⟨_, (_ | _)⟩ <;> rfl

lemma Mset.prod.sum.distrib_l (A : Mset α) (B C : Mset β) :
    A * (B + C) = A * B + A * C := by
  cases A using Quotient.ind; cases B using Quotient.ind; cases C using Quotient.ind;
  apply Quotient.sound; apply Ifam.prod.sum.distrib_l

lemma Mset.prod.sum.distrib_r (A B : Mset α) (C : Mset β) :
    (A + B) * C = A * C + B * C := by
  rw [prod.comm, prod.sum.distrib_l, prod.comm C A, prod.comm C B, sum.map,
      ←comp_map, ←comp_map, Prod.swap_swap_eq, id_map, id_map]

/-! ## Applicative -/

/-- `Applicative` for `Mset` -/
instance Mset.Applicative : Applicative Mset.{u} where
  seq F A := (fun (f, a) => f a) <$> (F * A ())

lemma Mset.seq.unfold (F : Mset (α → β)) A :
    F <*> A = (fun (f, a) => f a) <$> (F * A) := rfl

/-! `LawfulApplicative` is later derived from `LawfulMonad` -/

/-! ## Join -/

/-- `join` for `Ifam` -/
noncomputable def Ifam.join {α} (A : Ifam (Mset α)) : Mset α :=
  Mset.bigsum A.elem

lemma Ifam.join.proper (A B : Ifam (Mset α)) :
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

/-- `join` for `Mset` -/
noncomputable def Mset.join {α} : Mset (Mset α) → Mset α :=
  .lift (·.join) <| by intros; apply Ifam.join.proper; assumption

/-! ### Join laws -/

lemma Mset.map_join (f : α → β) (A : Mset (Mset α)) :
    f <$> join A = join ((f <$> ·) <$> A) := by
  revert A; apply Quotient.ind; rintro ⟨_, F⟩;
  apply Quotient.sound; trans; { apply Ifam.bigsum.map };
  apply Ifam.bigsum.proper; simp only [Ifam.map.elem];
  intro i; cases F i using Quotient.ind; trans; swap;
  { symm; apply Quotient.mk_out }; apply Ifam.map.proper; apply Quotient.mk_out

lemma Mset.join_map_seq (F : Mset (α → β)) :
    join ((· <$> A) <$> F) = F <*> A := by
  cases F using Quotient.ind; cases A using Quotient.ind;
  apply Quotient.sound; simp only [Ifam.map.elem]; trans;
  { apply Ifam.bigsum.proper; { intro _; apply Quotient.mk_out } }
  exists fun ⟨i, j⟩ => ⟨i, j⟩, fun ⟨i, j⟩ => ⟨i, j⟩; and_intros <;> { intro _; rfl }

lemma Mset.join_pure (A : Mset α) : join (pure A) = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  simp only [Ifam.pure.elem]; trans; swap; { apply Quotient.mk_out };
  apply Ifam.unary_bigsum

lemma Ifam.bigsum_pure (A : Ifam α) : bigsum (pure <$> A).elem ≈ A := by
  exists fun ⟨i, _⟩ => i, fun i => ⟨i, ()⟩; and_intros; iterate 3 { intro _; rfl }

lemma Mset.join_pure_map (A : Mset α) : join (pure <$> A) = A := by
  cases A using Quotient.ind; apply Quotient.sound; trans; swap;
  { apply Ifam.bigsum_pure }; apply Ifam.bigsum.proper;
  intro _; apply Quotient.mk_out

lemma Mset.join_join (A : Mset (Mset (Mset α))) :
    join (join A) = join (join <$> A) := by
  revert A; apply Quotient.ind; rintro ⟨_, F⟩; apply Quotient.sound;
  unfold join; unfold Ifam.join;
  simp only [Ifam.bigsum.dom, Ifam.map.dom, Ifam.map.elem];
  trans; swap;
  { apply Ifam.bigsum.proper;
    { intro i; rewrite [←Quotient.out_eq (F i), Quotient.lift_mk];
      symm; unfold Mset.bigsum; apply Quotient.mk_out }; }
  exists fun ⟨⟨i, j⟩, k⟩ => ⟨i, ⟨j, k⟩⟩, fun ⟨i, ⟨j, k⟩⟩ => ⟨⟨i, j⟩, k⟩;
  and_intros; iterate 3 { intro _; rfl }

/-! ## Monad -/

/-- `Monad` for `Mset` -/
noncomputable instance Mset.Monad : Monad Mset where
  bind A K := join (K <$> A)

lemma Mset.bind.unfold (A : Mset α) (K : α → Mset β) :
    A >>= K = join (K <$> A) := rfl

/-- Monad laws for `Mset` -/
instance Mset.LawfulMonad : LawfulMonad Mset where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := by rw [seq.unfold, prod.id_l, ←comp_map]; rfl
  pure_bind _ _ := by rw [bind.unfold, pure.map, join_pure]
  bind_pure_comp _ _ := by
    rw [bind.unfold, ←Function.comp_def, comp_map, join_pure_map]
  bind_map _ _ := by apply join_map_seq
  bind_assoc A F G := by
    have eq : (F · >>= G) = join ∘ (G <$> F ·) := rfl;
    rw [bind.unfold, bind.unfold, bind.unfold, eq];
    rw [comp_map, ←join_join, map_join, ←comp_map]; rfl
