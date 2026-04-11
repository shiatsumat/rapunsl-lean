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

theorem Premultiset.equiv.is_equiv :
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
def Multiset.empty : Multiset α := .mk' .empty

/-! ## Singleton multiset -/

/-- Singleton premultiset -/
def Premultiset.singl (a : α) : Premultiset α := .mk Unit (fun _ => a)

/-- Singleton multiset -/
def Multiset.singl (a : α) : Multiset α := .mk' (.singl a)

/-! ## Binary multiset sum -/

/-- Sum of two premultisets -/
def Premultiset.add {α} (A B : Premultiset α) : Premultiset α :=
  .mk (A.dom ⊕ B.dom) (fun s => s.casesOn A.elem B.elem)

instance Premultiset.Add : Add (Premultiset.{u} α) where
  add := Premultiset.add

theorem Premultiset.add.unfold {A B : Premultiset α} :
  A + B = Premultiset.add A B := rfl

@[simp] theorem Premultiset.add.dom {A B : Premultiset α} :
  (A + B).dom = (A.dom ⊕ B.dom) := rfl

@[simp] theorem Premultiset.add.elem_inl {A B : Premultiset α} {i} :
  (A + B).elem (.inl i) = A.elem i := rfl

@[simp] theorem Premultiset.add.elem_inr {A B : Premultiset α} {i} :
  (A + B).elem (.inr i) = B.elem i := rfl

theorem Premultiset.add.proper {A A' B B' : Premultiset α} :
  A ≈ A' → B ≈ B' → A + B ≈ A' + B' :=
  fun ⟨f, g, gf, fg, AB⟩ ⟨h, k, kh, hk, A'B'⟩ => by
    exists .map f h, .map g k;
    and_intros <;>
      (rintro (_ | _) <;> simp only [Sum.map_inl, Sum.map_inr]);
    { rw [gf] }; { rw [kh] }; { rw [fg] }; { rw [hk] };
    { apply AB }; { apply A'B' }

theorem Premultiset.add.proper_l {A A' B : Premultiset α} :
  A ≈ A' → A + B ≈ A' + B := by
  intro _; apply Premultiset.add.proper; { assumption }; { rfl }

theorem Premultiset.add.proper_r {A B B' : Premultiset α} :
  B ≈ B' → A + B ≈ A + B' := by
  intro _; apply Premultiset.add.proper; { rfl }; { assumption }

/-- Sum of two multisets -/
def Multiset.add.{u} {α} : Multiset.{u} α → Multiset.{u} α → Multiset α :=
  .lift₂ (fun A B => .mk' <| A + B) <| by
    intros; apply Quotient.sound; apply Premultiset.add.proper <;> assumption

instance Multiset.Add : Add (Multiset.{u} α) where
  add := Multiset.add

theorem Multiset.add.unfold {A B : Multiset α} :
  A + B = Multiset.add A B := rfl

theorem Multiset.add.out {A B : Multiset α} :
  A + B = .mk' (A.out + B.out) := by
  rw [Multiset.add.unfold]; unfold Multiset.add;
  rw (occs := [1]) [←(Quotient.out_eq A), ←(Quotient.out_eq B)];
  simp only [Quotient.lift_mk]

/-! ### [+] is commutative -/

theorem Premultiset.add.commutative {A B : Premultiset α} :
  A + B ≈ B + A := by
  exists fun | .inl i => .inr i | .inr j => .inl j,
         fun | .inl j => .inr j | .inr i => .inl i;
  and_intros <;> rintro (_ | _) <;> rfl

instance Multiset.add.Commutative :
  Std.Commutative (HAdd.hAdd (α := Multiset α)) where
  comm _ _ := by
    iterate 2 rw [Multiset.add.out];
    apply Quotient.sound; apply Premultiset.add.commutative

/-! ### [+] is unital -/

theorem Premultiset.add.right_identity {A : Premultiset α} :
  A + .empty ≈ A := by
  exists fun | .inl i => i | .inr e => (nomatch e), .inl
  and_intros; { intro _; rfl }; all_goals
    rintro (_ | _); { rfl }; { nofun }

instance Multiset.add.LawfulCommIdentity :
  Std.LawfulCommIdentity (HAdd.hAdd (α := Multiset α)) Multiset.empty where
  right_id A := by
    rw [Multiset.add.out]; rw (occs := [2]) [←(Quotient.out_eq A)];
    apply Quotient.sound; trans; swap; { exact Premultiset.add.right_identity };
    apply Premultiset.add.proper_r; apply Quotient.mk_out

/-! ### [+] is associative -/

theorem Premultiset.add.associative {A B C : Premultiset α} :
  (A + B) + C ≈ A + (B + C) := by
  exists fun | .inl (.inl i) => .inl i | .inl (.inr j) => .inr (.inl j)
             | .inr k => .inr (.inr k),
         fun | .inl i => .inl (.inl i) | .inr (.inl j) => .inl (.inr j)
             | .inr (.inr k) => .inr k;
  and_intros; { rintro (_ | _ | _) <;> rfl }; all_goals
    rintro ((_ | _) | _) <;> rfl

instance Multiset.add.Associative :
  Std.Associative (HAdd.hAdd (α := Multiset α)) where
  assoc _ _ _ := by
    iterate 4 rw [Multiset.add.out];
    apply Quotient.sound; trans;
    { apply Premultiset.add.proper_l; apply Quotient.mk_out };
    trans; { apply Premultiset.add.associative };
    apply Premultiset.add.proper_r; symm; apply Quotient.mk_out

/-! ## Big sum of multisets -/

/-- Big sum of premultisets -/
def Premultiset.bigsum {ι : Type} (A : ι → Premultiset α) : Premultiset α :=
  .mk (Σ i, (A i).dom) (fun ⟨i, j⟩ => (A i).elem j)

theorem Premultiset.bigsum.proper :
  (∀ i, A i ≈ A' i) → Premultiset.bigsum A ≈ Premultiset.bigsum A' := by
    intro AA'; have ⟨f, AA'⟩ := Classical.skolem.mp AA';
    have ⟨g, AA'⟩ := Classical.skolem.mp AA';
    exists fun ⟨i, j⟩ => ⟨i, f i j⟩, fun ⟨i, j⟩ => ⟨i, g i j⟩;
    and_intros <;> intro ⟨i, j⟩ <;> have ⟨gf, fg, AA'⟩ := AA' i <;> simp only;
    { rw [gf] }; { rw [fg] }; { apply AA' }

@[simp] theorem Premultiset.bigsum.dom {ι A} :
  (Premultiset.bigsum (α := α) (ι := ι) A).dom = Σ i, (A i).dom := rfl

@[simp] theorem Premultiset.bigsum.elem {ι A i j} :
  (Premultiset.bigsum (α := α) (ι := ι) A).elem ⟨i, j⟩ = (A i).elem j := rfl

/-- Big sum of multisets -/
noncomputable def Multiset.bigsum.{u} {ι : Type}
  (A : ι → Multiset.{u} α) : Multiset.{u} α :=
  .mk' <| Premultiset.bigsum (fun i => (A i).out)

theorem Multiset.bigsum.proper :
  (∀ i, A i = A' i) → Multiset.bigsum A = Multiset.bigsum A' := by
    intro AA'; apply Quotient.sound;
    apply Premultiset.bigsum.proper; intro _; rw [AA']

/-! ### `bigsum` is commutative -/

theorem Premultiset.bigsum.commutative {ι ι' : Type}
  (A : ι → Premultiset α) (σ : ι → ι') (σ' : ι' → ι) :
  (∀ i', σ (σ' i') = i') → (∀ i, σ' (σ i) = i) →
  Premultiset.bigsum A ≈ Premultiset.bigsum (A ∘ σ') := fun σσ' σ'σ => by
  exists
    fun ⟨i, j⟩ => ⟨σ i, congrArg (fun i => (A i).dom) (σ'σ i).symm ▸ j⟩,
    fun ⟨i', j⟩ => ⟨σ' i', j⟩;
  simp only [dom, Function.comp_apply];
  and_intros <;> intro ⟨_, _⟩;
  · congr; { rw [σσ'] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · congr; { rw [σ'σ] }; simp only [eqRec_heq_iff_heq, heq_eq_eq]
  · unfold bigsum; simp only [Function.comp_apply]; congr; { rw [σ'σ] };
    simp only [heq_eqRec_iff_heq, heq_eq_eq]

theorem Multiset.bigsum.commutative {ι ι' : Type}
  (A : ι → Multiset α) (σ : ι → ι') (σ' : ι' → ι) :
  (∀ i', σ (σ' i') = i') → (∀ i, σ' (σ i) = i) →
  Multiset.bigsum A = Multiset.bigsum (A ∘ σ') := fun σσ' σ'σ => by
  apply Quotient.sound; apply Premultiset.bigsum.commutative <;> assumption

/-! ### `bigsum` is associative -/

theorem Premultiset.bigsum.associative {ι : Type} {ι' : ι → Type}
  (A : ∀ ι, ι' ι → Premultiset α) :
  Premultiset.bigsum (fun i => Premultiset.bigsum (A i)) ≈
    Premultiset.bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  exists fun ⟨i, j, k⟩ => ⟨⟨i, j⟩, k⟩, fun ⟨⟨i, j⟩, k⟩ => ⟨i, j, k⟩;
  and_intros <;> intros <;> rfl

theorem Multiset.bigsum.associative {ι : Type} {ι' : ι → Type}
  (A : ∀ ι, ι' ι → Multiset α) :
  Multiset.bigsum (fun i => Multiset.bigsum (A i)) =
    Multiset.bigsum (ι := Σ ι, ι' ι) (fun ⟨i, j⟩ => A i j) := by
  apply Quotient.sound; trans;
  { apply Premultiset.bigsum.proper; intros; apply Quotient.mk_out };
  apply Premultiset.bigsum.associative

/-! ### `empty` as `bigsum` -/

theorem Premultiset.empty_bigsum :
  Premultiset.empty ≈ Premultiset.bigsum (ι := Empty) A := by
  exists nofun, nofun; and_intros <;> nofun

theorem Multiset.empty_bigsum :
  Multiset.empty = Multiset.bigsum (ι := Empty) (α := α) nofun := by
  apply Quotient.sound; apply Premultiset.empty_bigsum

/-! ### `+` as `bigsum` -/

theorem Premultiset.add_bigsum :
  F true = A → F false = B →
  A + B ≈ Premultiset.bigsum F := by
  intro rfl rfl;
  exists fun | .inl i => ⟨true, i⟩ | .inr i => ⟨false, i⟩,
         fun | ⟨true, i⟩ => .inl i | ⟨false, i⟩ => .inr i;
  and_intros; { rintro ⟨_ | _, _⟩ <;> rfl }; all_goals
    rintro (_ | _) <;> rfl

theorem Multiset.add_bigsum :
  A + B = Multiset.bigsum (fun b : Bool => if b then A else B) := by
  rw [Multiset.add.out]; apply Quotient.sound;
  apply Premultiset.add_bigsum <;> rfl
