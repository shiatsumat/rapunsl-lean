module

public import RapunSL.Math.Mset.Monad
open Mset

@[expose] public section

/-! # Nonempty multiset -/

/-- Nonempty multiset -/
abbrev Mseti.{u} (α : Type u) : Type (max 1 u) := { A : Mset α // A.inhab }

/-- Map over `Mseti` -/
protected def Mseti.map {α β : Type*} (f : α → β) (A : Mseti α) : Mseti β :=
  ⟨f <$>ᴹ A.val, by grind only [Mset.inhab_map']⟩

scoped[Mseti] infixr:100 " <$>ᴹⁱ " => Mseti.map
open Mseti

@[simp] lemma Mseti.map'_val (f : α → β) (A : Mseti α) :
    (f <$>ᴹⁱ A).val = f <$>ᴹ A.val := rfl

/-! ## Functor -/

/-- `Functor` for `Mseti` -/
protected instance Mseti.instFunctor : Functor Mseti.{u} where
  map := Mseti.map

protected lemma Mseti.map_unfold : Functor.map = Mseti.map (α := α) (β := β) := rfl

@[simp] lemma Mseti.map_val (f : α → β) (A : Mseti α) :
    (f <$> A).val = f <$> A.val := rfl

protected lemma Mseti.id_map (A : Mseti α) : id <$>ᴹⁱ A = A := by
  cases A; simp only [Mseti.map, Mset.id_map]

protected lemma Mseti.comp_map (f : α → β) (g : β → γ) (A : Mseti α) :
    (g ∘ f) <$>ᴹⁱ A = g <$>ᴹⁱ (f <$>ᴹⁱ A) := by
  cases A; simp only [Mseti.map, Mset.comp_map]

/-- Functor laws for `Mseti` -/
protected instance Mseti.instLawfulFunctor : LawfulFunctor Mseti where
  id_map := Mseti.id_map
  comp_map := Mseti.comp_map
  map_const := rfl

/-! ## Singleton -/

/-- Singleton `Mseti` -/
protected instance Mseti.instPure : Pure Mseti.{u} where
  pure a := ⟨pure a, by simp only [Mset.inhab_pure]⟩

@[simp] protected lemma Mseti.pure_val (a : α) :
    (pure a : Mseti α).val = pure a := rfl

/-! ## Membership -/

/-- Membership for `Mseti` -/
protected instance Mseti.instMembership : Membership α (Mseti α) where
  mem A a := a ∈ A.val

protected lemma Mseti.mem_unfold (A : Mseti α) (a : α) :
    (a ∈ A) = (a ∈ A.val) := rfl

/-! ## Sum -/

/-- Binary sum of `Mseti`s -/
protected def Mseti.oplus (A B : Mseti α) : Mseti α :=
  ⟨A.val ⊕ᴹ B.val, by grind only [Mset.inhab_oplus]⟩

scoped[Mseti] infixr:60 " ⊕ᴹⁱ " => Mseti.oplus

@[simp] protected lemma Mseti.oplus_val (A B : Mseti α) :
    (A ⊕ᴹⁱ B).val = A.val ⊕ᴹ B.val := rfl

/-- Big sum of `Mseti`s -/
protected noncomputable def Mseti.bigoplus {ι} [Inhabited ι] (A : ι → Mseti α) : Mseti α :=
  ⟨⨁ᴹ i, (A i).val, by
    simp only [Mset.inhab_bigoplus]; exists default; grind only⟩

scoped[Mseti] notation "⨁ᴹⁱ " i ", " A => Mseti.bigoplus (fun i => A)

@[simp] protected lemma Mseti.bigoplus_val {ι} [Inhabited ι] (A : ι → Mseti α) :
    (⨁ᴹⁱ i, A i).val = ⨁ᴹ i, (A i).val := rfl

lemma Mseti.oplus_bigoplus (A B : Mseti α) :
    A ⊕ᴹⁱ B = ⨁ᴹⁱ (b : Bool), if b then A else B := by
  ext1; simp only [Mseti.oplus_val, Mseti.bigoplus_val, Mset.oplus_bigoplus];
  congr; ext1 b; cases b <;> rfl

/-! ## Product -/

/-- Binary product of `Mseti`s -/
protected def Mseti.prod (A : Mseti α) (B : Mseti β) : Mseti (α × β) :=
  ⟨A.val ×ᴹ B.val, by grind only [Mset.inhab_prod]⟩

scoped[Mseti] infixr:69 " ×ᴹⁱ " => Mseti.prod

lemma Mseti.prod_val (A : Mseti α) (B : Mseti β) :
    (A ×ᴹⁱ B).val = A.val ×ᴹ B.val := rfl

/-! ## Applicative -/

/-- `seq` for `Mseti` -/
protected def Mseti.seq {α β : Type*} (F : Mseti (α → β)) (A : Mseti α) : Mseti β :=
  ⟨F.val <*>ᴹ A.val, by grind only [Mset.inhab_seq']⟩

scoped[Mseti] infixl:60 " <*>ᴹⁱ " => Mseti.seq

@[simp] protected lemma Mseti.seq'_val (F : Mseti (α → β)) (A : Mseti α) :
    (F <*>ᴹⁱ A).val = F.val <*>ᴹ A.val := rfl

/-- `Applicative` for `Mset` -/
protected instance Mseti.instApplicative : Applicative Mseti.{u} where
  seq F A := F <*>ᴹⁱ A ()

@[simp] protected lemma Mseti.seq_val (F : Mseti (α → β)) (A : Mseti α) :
    (F <*> A).val = F.val <*> A.val := rfl

/-! ## Monad -/

/-- `bind` for `Mseti` -/
protected noncomputable def Mseti.bind {α β : Type*} (A : Mseti α) (K : α → Mseti β) : Mseti β :=
  ⟨A.val >>=ᴹ (fun a => (K a).val), by
    simp only [Mset.inhab_bind']; have ⟨a, el⟩ := A.prop; exists a, el; grind only⟩

scoped[Mseti] infixl:55 " >>=ᴹⁱ " => Mseti.bind

@[simp] protected lemma Mseti.bind'_val (A : Mseti α) (K : α → Mseti β) :
    (A >>=ᴹⁱ K).val = A.val >>=ᴹ (fun a => (K a).val) := rfl

/-- `Monad` for `Mseti` -/
protected noncomputable instance Mseti.instMonad : Monad Mseti.{u} where
  bind A K := A >>=ᴹⁱ K

@[simp] protected lemma Mseti.bind_val (A : Mseti α) (K : α → Mseti β) :
    (A >>= K).val = A.val >>= (fun a => (K a).val) := rfl

/-- Monad laws for `Mseti` -/
protected instance Mseti.instLawfulMonad : LawfulMonad Mseti where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq := by intros; ext1; simp only [Mseti.seq_val, Mseti.pure_val, map_val, pure_seq]
  pure_bind := by intros; ext1; simp only [Mseti.bind_val, Mseti.pure_val, pure_bind]
  bind_pure_comp := by
    intros; ext1; simp only [Mseti.bind_val, Mseti.pure_val, map_val, bind_pure_comp]
  bind_map := by intros; ext1; simp only [Mseti.bind_val, Mseti.map_val, Mseti.seq_val, bind_map]
  bind_assoc := by intros; ext1; simp only [Mseti.bind_val, bind_assoc]
