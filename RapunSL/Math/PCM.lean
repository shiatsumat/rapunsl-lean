module

public import Mathlib.Algebra.Group.Defs
public import RapunSL.Math.Mset
open Mseti

@[expose] public section

/-! # PCM -/

/-! ## Commutative monoid -/

/-- Utility version of `CommMonoid`, where only `mul_one` is required -/
class CommMonoid' (α : Type u) extends CommSemigroup α, One α where
  protected mul_one : ∀ a : α, a * 1 = a

/-- `CommMonoid'` induces `CommMonoid` -/
protected instance CommMonoid'.instCommMonoid (α : Type u) [CommMonoid' α] : CommMonoid α where
  mul_one := CommMonoid'.mul_one
  one_mul _ := by rw [mul_comm]; apply CommMonoid'.mul_one

/-! ## PCM, i.e., partial commutative monoid -/

/-- PCM, i.e., partial commutative monoid -/
class PCM (α : Type u) extends CommMonoid' α where
  /-- Validity predicate for partiality -/
  protected valid : α → Prop
  /-- `1` is valid -/
  protected valid_one : valid 1
  /-- Take the left-hand side of `*` in `✓` -/
  protected valid_mul_l : ∀ a b : α, valid (a * b) → valid a

@[inherit_doc]
scoped[PCM] prefix:50 "✓ " => PCM.valid
open PCM

/-- Take the right-hand side of `*` in `✓` -/
protected lemma PCM.valid_mul_r [PCM α] (a b : α) : ✓ (a * b) → ✓ b := by
  rw [mul_comm]; apply PCM.valid_mul_l

/-! ## PCM constructions -/

/-! ### Exclusive PCM -/

/-- Data type for the exclusive PCM -/
inductive Excl (α : Type u) where
  | /-- Exclusive element -/
    protected excl : α → Excl α
  | /-- Unit element -/
    protected unit : Excl α
  | /-- Bottom element -/
    protected bot : Excl α

/-- Exclusive PCM -/
protected instance Excl.instPCM : PCM (Excl α) where
  one := .unit
  mul | a, .unit => a | .unit, b => b | _, _ => .bot
  mul_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one _ := rfl
  valid | .bot => False | _ => True
  valid_one := trivial
  valid_mul_l a b := by cases a <;> cases b <;> tauto

protected lemma Excl.one_unfold : (1 : Excl α) = .unit := rfl

protected lemma Excl.mul_unfold :
    (HMul.hMul : Excl α → Excl α → _) =
      fun | a, .unit => a | .unit, b => b | _, _ => .bot := rfl

protected lemma Excl.valid_unfold :
    PCM.valid (α := Excl α) = fun | .bot => False | _ => True := rfl

/-! ### Product PCM -/

/-- Product PCM -/
protected instance Prod.instPCM (α : Type u) (β : Type u') [PCM α] [PCM β] : PCM (α × β) where
  one := (1, 1)
  mul | (a, b), (a', b') => (a * a', b * b')
  mul_one _ := by ext1 <;> apply mul_one
  mul_comm _ _ := by ext1 <;> apply mul_comm
  mul_assoc _ _ _ := by ext1 <;> apply mul_assoc
  valid | (a, b) => ✓ a ∧ ✓ b
  valid_one := by and_intros <;> apply PCM.valid_one
  valid_mul_l := by
    intro _ _ ⟨val, val'⟩; and_intros;
    { apply PCM.valid_mul_l _ _ val }; { apply PCM.valid_mul_l _ _ val' }

protected lemma Prod.one_unfold [PCM α] [PCM β] : (1 : α × β) = (1, 1) := rfl

protected lemma Prod.mul_unfold [PCM α] [PCM β] :
    (HMul.hMul : α × β → α × β → _) = fun | (a, b), (a', b') => (a * a', b * b') := rfl

protected lemma Prod.valid_unfold [PCM α] [PCM β] :
    PCM.valid (α := α × β) = fun | (a, b) => ✓ a ∧ ✓ b := rfl

/-- Pi PCM -/
protected instance Pi.instPCM (ι : Type u) (α : ι → Type u') [∀ i, PCM (α i)] :
    PCM (∀ i, α i) where
  one i := 1
  mul f g i := f i * g i
  mul_one _ := by funext; apply mul_one
  mul_comm _ _ := by funext; apply mul_comm
  mul_assoc _ _ _ := by funext; apply mul_assoc
  valid f := ∀ i, ✓ f i
  valid_one := by intro i; apply PCM.valid_one
  valid_mul_l := by intro _ _ val i; apply PCM.valid_mul_l _ _ (val i)

protected lemma Pi.one_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    (1 : ∀ i, α i) = fun _ => 1 := rfl

protected lemma Pi.mul_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    (HMul.hMul : (∀ i, α i) → (∀ i, α i) → (∀ i, α i)) =
      fun f g i => f i * g i := by rfl

protected lemma Pi.valid_unfold {ι : Type*} {α : ι → Type*} [∀ i, PCM (α i)] :
    PCM.valid (α := ∀ i, α i) = fun f => ∀ i, ✓ f i := rfl

/-! ### Inhabited multiset PCM -/

/-- `*` for inhabited multisets -/
protected instance Mseti.Mul (α : Type u) [Mul α] : Mul (Mseti α) where
  mul A B := ⟨HMul.hMul <$> A.val <*> B.val, by
    simp only [Mset.inhab_seq, Mset.inhab_map]; grind only⟩

protected lemma Mseti.mul_val [Mul α] (A B : Mseti α) :
    (A * B).val = HMul.hMul <$> A.val <*> B.val := rfl

protected lemma Mseti.pure_mul [Mul α] (a b : α) :
    pure (f := Mseti) (a * b) = pure a * pure b := by
  ext; simp only [Mseti.mul_val, Mseti.pure_val, functor_norm]

protected lemma Mseti.mul_bigoplus_l [Mul α] [Inhabited ι] A (B : ι → Mseti α) :
    A * (⨁ᴹⁱ i, B i) = ⨁ᴹⁱ i, A * B i := by
  ext; simp only [Mseti.mul_val, Mseti.bigoplus_val, Mset.seq_bigoplus_l]

protected lemma Mseti.mul_bigoplus_r [Mul α] [Inhabited ι] (A : ι → Mseti α) B :
    (⨁ᴹⁱ i, A i) * B = ⨁ᴹⁱ i, A i * B := by
  ext; simp only [Mseti.mul_val, Mseti.bigoplus_val, Mset.bigoplus_map, Mset.seq_bigoplus_r]

protected lemma Mseti.mul_oplus_l [Mul α] (A B C : Mseti α) :
    A * (B ⊕ᴹⁱ C) = A * B ⊕ᴹⁱ A * C := by
  ext; simp only [Mseti.oplus_bigoplus, Mseti.mul_bigoplus_l]; grind only

protected lemma Mseti.mul_oplus_r [Mul α] (A B C : Mseti α) :
    (A ⊕ᴹⁱ B) * C = A * C ⊕ᴹⁱ B * C := by
  ext; simp only [Mseti.oplus_bigoplus, Mseti.mul_bigoplus_r]; grind only

@[simp] protected lemma Mseti.mem_mul [Mul α] (A B : Mseti α) a :
    (a ∈ A * B) = ∃ b c, b ∈ A ∧ c ∈ B ∧ a = b * c := by
  simp only [Mseti.mul_val, Mseti.mem_unfold, Mset.mem_seq, Mset.mem_map, existsAndEq];
  ext1; tauto

/-- `1` for multisets -/
protected instance Mseti.instOne (α : Type u) [One α] : One (Mseti α) where
  one := pure 1

protected lemma Mseti.one_unfold [PCM α] : (1 : Mseti α) = pure 1 := rfl

/-- Multiset PCM -/
protected instance Mseti.instPCM (α : Type u) [PCM α] : PCM (Mseti α) where
  one := pure 1
  mul_one _ := by
    ext; simp only [Mseti.mul_val, Mseti.one_unfold, Mseti.pure_val];
    rw [seq_pure, ←comp_map]; trans; swap; { apply id_map }; congr; grind only [mul_one, id_eq]
  mul_comm _ _ := by
    ext; simp only [Mseti.mul_val]; rw [CommApplicative.commutative_map]; congr;
    grind only [mul_comm]
  mul_assoc _ _ _ := by
    ext; simp only [Mseti.mul_val, functor_norm]; grind only [mul_assoc]
  valid A := ∀ a ∈ A, ✓ a
  valid_one := by
    simp only [Mseti.one_unfold, Mseti.mem_unfold, Mseti.pure_val, Mset.mem_pure, forall_eq];
    apply PCM.valid_one
  valid_mul_l := by
    intro A ⟨B, ⟨b, _⟩⟩ val a _; apply PCM.valid_mul_l _ b;
    apply val; simp only [Mseti.mem_mul]; exists a, b

protected lemma Mseti.valid_unfold [PCM α] :
    PCM.valid (α := Mseti α) = fun A => ∀ a ∈ A, ✓ a := rfl

protected lemma Mseti.valid_pure [PCM α] (a : α) :
    (✓ (pure a : Mseti α)) = (✓ a) := by
  simp only [Mseti.valid_unfold, Mseti.mem_unfold, Mseti.pure_val, Mset.mem_pure, forall_eq]

/-- Valid inhabited multisets -/
abbrev Msetiv α [PCM α] := { A : Mseti α // ✓ A }
