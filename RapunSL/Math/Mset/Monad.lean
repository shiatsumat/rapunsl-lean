module

public import Mathlib.Control.Applicative
public import RapunSL.Math.Mset.Oplus
public import RapunSL.Math.Mset.Prod
open Ifam Mset

@[expose] public section

/-! # Applicative and monad structures for multisets -/

/-! ## Applicative -/

/-- `seq` for `Mset`, more universe-polymorphic than `Seq.seq` -/
protected def Mset.seq {α β : Type*} (F : Mset (α → β)) (A : Mset α) : Mset β :=
  (fun (f, a) => f a) <$>ᴹ (F ×ᴹ A)

@[inherit_doc]
scoped[Mset] infixl:60 " <*>ᴹ " => Mset.seq

/-- `Applicative` for `Mset` -/
protected instance Mset.instApplicative : Applicative Mset where
  seq F A := F <*>ᴹ A ()

protected lemma Mset.seq_unfold (F : Mset (α → β)) (A : Mset α) :
    F <*> A = (fun (f, a) => f a) <$> (F ×ᴹ A) := rfl

protected lemma Mset.map'_seq' (f : α → β → γ) A B :
    f <$>ᴹ A <*>ᴹ B = Function.uncurry f <$>ᴹ (A ×ᴹ B) := by
  rw [Mset.seq, Mset.prod_map'_l, ←Mset.comp_map]; rfl

protected lemma Mset.map_seq (f : α → β → γ) A B :
    f <$> A <*> B = Function.uncurry f <$> (A ×ᴹ B) := by apply Mset.map'_seq'

/-! `LawfulApplicative` is later derived from `LawfulMonad` -/

/-! ## `seq` distributes over `⊕ᴹ` -/

protected lemma Mset.seq'_bigoplus_l (F : Mset (α → β)) (A : ι → Mset α) :
    F <*>ᴹ (⨁ᴹ i, A i) = ⨁ᴹ i, F <*>ᴹ A i := by
  rw [Mset.seq, Mset.prod_bigoplus_l, Mset.bigoplus_map']; rfl

protected lemma Mset.seq_bigoplus_l (F : Mset (α → β)) (A : ι → Mset α) :
    F <*> (⨁ᴹ i, A i) = ⨁ᴹ i, F <*> A i := by apply Mset.seq'_bigoplus_l

protected lemma Mset.seq'_bigoplus_r (F : ι → Mset (α → β)) (A : Mset α) :
    (⨁ᴹ i, F i) <*>ᴹ A = ⨁ᴹ i, F i <*>ᴹ A := by
  rw [Mset.seq, Mset.prod_bigoplus_r, Mset.bigoplus_map']; rfl

protected lemma Mset.seq_bigoplus_r (F : ι → Mset (α → β)) (A : Mset α) :
    (⨁ᴹ i, F i) <*> A = ⨁ᴹ i, F i <*> A := by apply Mset.seq'_bigoplus_r

protected lemma Mset.seq'_oplus_l (F : Mset (α → β)) (A B : Mset α) :
    F <*>ᴹ (A ⊕ᴹ B) = (F <*>ᴹ A) ⊕ᴹ (F <*>ᴹ B) := by
  simp only [Mset.oplus_as_bigoplus, Mset.seq'_bigoplus_l]; grind only

protected lemma Mset.seq_oplus_l (F : Mset (α → β)) (A B : Mset α) :
    F <*> (A ⊕ᴹ B) = (F <*> A) ⊕ᴹ (F <*> B) := by apply Mset.seq'_oplus_l

protected lemma Mset.seq'_oplus_r (F G : Mset (α → β)) (A : Mset α) :
    (F ⊕ᴹ G) <*>ᴹ A = (F <*>ᴹ A) ⊕ᴹ (G <*>ᴹ A) := by
  simp only [Mset.oplus_as_bigoplus, Mset.seq'_bigoplus_r]; grind only

protected lemma Mset.seq_oplus_r (F G : Mset (α → β)) (A : Mset α) :
    (F ⊕ᴹ G) <*> A = (F <*> A) ⊕ᴹ (G <*> A) := by apply Mset.seq'_oplus_r

protected lemma Mset.seq'_empty_l (F : Mset (α → β)) :
    F <*>ᴹ (∅ : Mset α) = ∅ := by
  simp only [Mset.empty_as_bigoplus, Mset.seq'_bigoplus_l]; congr; ext1 _; trivial

protected lemma Mset.seq_empty_l (F : Mset (α → β)) :
    F <*> (∅ : Mset α) = ∅ := by apply Mset.seq'_empty_l

protected lemma Mset.seq'_empty_r (A : Mset α) :
    (∅ : Mset (α → β)) <*>ᴹ A = ∅ := by
  simp only [Mset.empty_as_bigoplus, Mset.seq'_bigoplus_r]; congr; ext1 _; trivial

protected lemma Mset.seq_empty_r (A : Mset α) :
    (∅ : Mset (α → β)) <*> A = ∅ := by apply Mset.seq'_empty_r

/-! ## Join -/

/-- `join` for `Ifam` -/
protected noncomputable def Ifam.join {α} (A : Ifam (Mset α)) : Mset α :=
  Mset.bigoplus A.elem

@[gcongr] protected lemma Ifam.join_proper (A B : Ifam (Mset α)) :
    A ≈ B → A.join = B.join := by
  intro ⟨f, AB⟩; apply Quotient.sound;
  let g : (⨁ᴵ i, (A.elem i).out).dom ≃ (⨁ᴵ i, (B.elem i).out).dom :=
    { toFun := fun ⟨i, k⟩ => ⟨f i, congrArg (·.out.dom) (AB i) ▸ k⟩,
      invFun := fun ⟨j, k⟩ => ⟨f.symm j,
        congrArg (·.out.dom) (Ifam.equiv_elem_eq_symm AB j).symm ▸ k⟩,
      left_inv := by intro _; grind only [Equiv.symm_apply_apply],
      right_inv := by intro _; grind only [Equiv.apply_symm_apply] };
  exists g; rw [←Equiv.toFun_as_coe g]; intro ⟨i, _⟩; revert g;
  simp only [Ifam.bigoplus_elem]; generalize AB i = eq; revert eq;
  generalize B.elem (f i) = Bj; intro rfl; rfl

/-- `join` for `Mset` -/
protected noncomputable def Mset.join {α} : Mset (Mset α) → Mset α :=
  .lift (·.join) Ifam.join_proper

/-! ### Join laws -/

protected lemma Mset.map_join (f : α → β) (A : Mset (Mset α)) :
    f <$>ᴹ Mset.join A = Mset.join (Mset.map f <$>ᴹ A) := by
  revert A; apply Quotient.ind; intro ⟨_, F⟩;
  apply Quotient.sound; rw [Ifam.bigoplus_map']; apply Ifam.bigoplus_proper;
  simp only [Ifam.map_elem]; intro i; cases F i using Quotient.ind;
  grw [Quotient.mk_out]; symm; apply Quotient.mk_out

protected lemma Mset.join_map_seq (F : Mset (α → β)) :
    Mset.join ((· <$>ᴹ A) <$>ᴹ F) = F <*>ᴹ A := by
  cases F using Quotient.ind; cases A using Quotient.ind;
  apply Quotient.sound; simp only [Ifam.map_elem]; trans;
  { apply Ifam.bigoplus_proper; { intro _; apply Quotient.mk_out } }
  exists { toFun := fun ⟨i, j⟩ => ⟨i, j⟩, invFun := fun ⟨i, j⟩ => ⟨i, j⟩ }; intro _; rfl

protected lemma Mset.join_pure (A : Mset α) : Mset.join (pure A) = A := by
  cases A using Quotient.ind; apply Quotient.sound;
  simp only [Ifam.pure_elem]; grw [Quotient.mk_out]; apply Ifam.unary_bigoplus

protected lemma Ifam.bigoplus_pure (A : Ifam α) : Ifam.bigoplus (pure <$>ᴵ A).elem ≈ A := by
  exists Equiv.sigmaPUnit _; intro _; rfl

protected lemma Mset.join_pure_map (A : Mset α) : Mset.join (pure <$>ᴹ A) = A := by
  cases A using Quotient.ind; apply Quotient.sound; trans; swap;
  { apply Ifam.bigoplus_pure }; apply Ifam.bigoplus_proper; intro _; apply Quotient.mk_out

protected lemma Mset.join_join (A : Mset (Mset (Mset α))) :
    Mset.join (Mset.join A) = Mset.join (Mset.join <$>ᴹ A) := by
  revert A; apply Quotient.ind; intro ⟨_, F⟩; apply Quotient.sound;
  unfold Mset.join Ifam.join; simp only [Ifam.map_elem]; trans; swap;
  { apply Ifam.bigoplus_proper;
    { intro i; rewrite [←(F i).out_eq, Quotient.lift_mk];
      symm; unfold Mset.bigoplus; apply Quotient.mk_out } }
  exists { toFun := fun ⟨⟨i, j⟩, k⟩ => ⟨i, ⟨j, k⟩⟩, invFun := fun ⟨i, ⟨j, k⟩⟩ => ⟨⟨i, j⟩, k⟩ };
  intro _; rfl

/-! ## Monad -/

/-- Monadic bind for `Mset`, more universe-polymorphic than `Monad.bind` -/
protected noncomputable def Mset.bind {α β : Type*} (A : Mset α) (K : α → Mset β) : Mset β :=
  Mset.join (K <$>ᴹ A)

@[inherit_doc]
scoped[Mset] infixl:55 " >>=ᴹ " => Mset.bind

/-- `Monad` for `Mset` -/
noncomputable instance Mset.instMonad : Monad Mset where
  bind := Mset.bind

/-! ### Monad laws -/

protected lemma Mset.bind_unfold : Bind.bind = Mset.bind (α := α) (β := β) := rfl

protected lemma Mset.pure_seq (f : α → β) (A : Mset α) :
    pure f <*>ᴹ A = f <$>ᴹ A := by rw [Mset.seq, Mset.prod_id_l, ←Mset.comp_map]; rfl

protected lemma Mset.pure_bind (a : α) (K : α → Mset β) :
    pure a >>=ᴹ K = K a := by rw [Mset.bind, Mset.pure_map', Mset.join_pure]

protected lemma Mset.bind_pure_comp (f : α → β) (A : Mset α) :
    A >>=ᴹ (fun a => pure (f a)) = f <$>ᴹ A := by
  rw [Mset.bind, ←Function.comp_def, Mset.comp_map, Mset.join_pure_map]

protected lemma Mset.bind_map (F : Mset (α → β)) (A : Mset α) :
    F >>=ᴹ (· <$>ᴹ A) = F <*>ᴹ A := by apply Mset.join_map_seq

protected lemma Mset.bind_assoc (A : Mset α) (K : α → Mset β) (L : β → Mset γ) :
    (A >>=ᴹ K) >>=ᴹ L = A >>=ᴹ fun a => K a >>=ᴹ L := by
  have eq : (fun a => Mset.bind (K a) L) = Mset.join ∘ Mset.map L ∘ K := rfl; rw [eq];
  unfold Mset.bind; rw [Mset.comp_map, ←Mset.join_join, Mset.map_join, ←Mset.comp_map]

/-- Monad laws for `Mset` -/
protected instance Mset.instLawfulMonad : LawfulMonad Mset where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq := Mset.pure_seq
  pure_bind := Mset.pure_bind
  bind_pure_comp := Mset.bind_pure_comp
  bind_map := Mset.bind_map
  bind_assoc := Mset.bind_assoc

/-! ### Commutative applicative -/

protected lemma Mset.commutative_prod (A : Mset α) (B : Mset β) :
    Prod.mk <$>ᴹ A <*>ᴹ B = (fun b a => (a, b)) <$>ᴹ B <*>ᴹ A := by
  simp only [Mset.map'_seq']; rw [Mset.prod_comm, ←Mset.comp_map]; rfl

/-- Commutative applicative laws for `Mset` -/
protected instance Mset.instCommApplicative : CommApplicative Mset where
  commutative_prod := Mset.commutative_prod

/-! ## Membership -/

@[simp] protected lemma Mset.seq'_mem (F : Mset (α → β)) (A : Mset α) b :
    (b ∈ F <*>ᴹ A) = ∃ f ∈ F, ∃ a ∈ A, b = f a := by
  rw [Mset.seq]; simp only [Mset.map'_mem, Prod.exists, Mset.prod_mem]; grind only

@[simp] protected lemma Mset.seq_mem (F : Mset (α → β)) (A : Mset α) b :
    (b ∈ F <*> A) = ∃ f ∈ F, ∃ a ∈ A, b = f a := by apply Mset.seq'_mem

@[simp] protected lemma Mset.join_mem (A : Mset (Mset α)) a :
    (a ∈ Mset.join A) = ∃ B ∈ A, a ∈ B := by
  cases A using Quotient.ind; rw [Mset.join, Quotient.lift_mk, Ifam.join, Mset.bigoplus_mem];
  ext1; constructor; { tauto }; intro ⟨_, ⟨_, rfl⟩, _⟩; tauto

@[simp] protected lemma Mset.bind'_mem (A : Mset α) (K : α → Mset β) b :
    (b ∈ A >>=ᴹ K) = ∃ a ∈ A, b ∈ K a := by
  rw [Mset.bind]; simp only [Mset.map'_mem, Mset.join_mem]; grind only

@[simp] protected lemma Mset.bind_mem (A : Mset α) (K : α → Mset β) b :
    (b ∈ A >>= K) = ∃ a ∈ A, b ∈ K a := by apply Mset.bind'_mem

/-! ## Inhabitedness -/

@[simp] protected lemma Mset.inhab_seq' (F : Mset (α → β)) (A : Mset α) :
    (F <*>ᴹ A).inhab = (F.inhab ∧ A.inhab) := by
  simp only [Mset.inhab, Mset.seq'_mem]; grind only

@[simp] protected lemma Mset.inhab_seq (F : Mset (α → β)) (A : Mset α) :
    (F <*> A).inhab = (F.inhab ∧ A.inhab) := by apply Mset.inhab_seq'

@[simp] protected lemma Mset.inhab_join (A : Mset (Mset α)) :
    A.join.inhab = (A.inhab ∧ ∃ a ∈ A, a.inhab) := by
  simp only [Mset.inhab, Mset.join_mem]; grind only

@[simp] protected lemma Mset.inhab_bind' (A : Mset α) (K : α → Mset β) :
    (A >>=ᴹ K).inhab = (∃ a ∈ A, (K a).inhab) := by
  simp only [Mset.inhab, Mset.bind'_mem]; grind only

@[simp] protected lemma Mset.inhab_bind (A : Mset α) (K : α → Mset β) :
    (A >>= K).inhab = (∃ a ∈ A, (K a).inhab) := by apply Mset.inhab_bind'

/-! ## Pair membership -/

@[simp] protected lemma Mset.seq'_pairmem (F : Mset (α → β)) (A : Mset α) b b' :
    (F <*>ᴹ A).pairmem b b' =
      ∃ f g a a', b = f a ∧ b' = g a' ∧
        ((F.pairmem f g ∧ A.pairmem a a') ∨
         (f = g ∧ f ∈ F ∧ A.pairmem a a') ∨
         (a = a' ∧ a ∈ A ∧ F.pairmem f g)) := by
  simp only [Mset.seq, Mset.map'_pairmem, Mset.prod_pairmem]; aesop

@[simp] protected lemma Mset.seq_pairmem (F : Mset (α → β)) (A : Mset α) b b' :
    (F <*> A).pairmem b b' =
      ∃ f g a a', b = f a ∧ b' = g a' ∧
        ((F.pairmem f g ∧ A.pairmem a a') ∨
         (f = g ∧ f ∈ F ∧ A.pairmem a a') ∨
         (a = a' ∧ a ∈ A ∧ F.pairmem f g)) := by apply Mset.seq'_pairmem

@[simp] protected lemma Mset.join_pairmem (A : Mset (Mset α)) a a' :
    A.join.pairmem a a' =
      ((∃ B ∈ A, B.pairmem a a') ∨
       ∃ B B', A.pairmem B B' ∧ a ∈ B ∧ a' ∈ B') := by
  revert A; apply Quotient.ind; intro A;
  rw [Mset.join, Quotient.lift_mk, Ifam.join, Mset.bigoplus_pairmem]; congr <;> ext1;
  { constructor; { tauto }; intro ⟨_, ⟨_, rfl⟩, _⟩; tauto }
  constructor; swap; { intro ⟨_, _, ⟨i, i', _, rfl, rfl⟩, _, _⟩; exists i, i' };
  intro ⟨i, i', _, el, el'⟩; exists A.elem i, A.elem i'; constructor; { exists i, i' }; { tauto }

@[simp] protected lemma Mset.bind'_pairmem (A : Mset α) (K : α → Mset β) b b' :
    (A >>=ᴹ K).pairmem b b' =
      ((∃ a ∈ A, (K a).pairmem b b') ∨
       (∃ a a', A.pairmem a a' ∧ b ∈ K a ∧ b' ∈ K a')) := by
  simp only [Mset.bind, Mset.map'_pairmem, Mset.join_pairmem]; aesop

@[simp] protected lemma Mset.bind_pairmem (A : Mset α) (K : α → Mset β) b b' :
    (A >>= K).pairmem b b' =
      ((∃ a ∈ A, (K a).pairmem b b') ∨
       (∃ a a', A.pairmem a a' ∧ b ∈ K a ∧ b' ∈ K a')) := by apply Mset.bind'_pairmem

/-! ## Bijection -/

/-- Bijection for `<*>ᴹ` -/
protected noncomputable def Mset.Bij.seq
    {A : Mset (α → β)} {B : Mset α} {A' : Mset (α' → β')} {B' : Mset α'}
    (r : A ≃ᴹ A') (s : B ≃ᴹ B') : A <*>ᴹ B ≃ᴹ A' <*>ᴹ B' :=
  Mset.Bij.map (α := (α → β) × α) (α' := β) (β := (α' → β') × α') (β' := β')
    (fun (f, a) => f a) (fun (f', a') => f' a') (Mset.Bij.prod r s)

/-- The graph of `Mset.Bij.seq` -/
protected lemma Mset.Bij.seq_graph
    {A : Mset (α → β)} {B : Mset α} {A' : Mset (α' → β')} {B' : Mset α'}
    (r : A ≃ᴹ A') (s : B ≃ᴹ B') :
    (Mset.Bij.seq r s).graph =
      (fun (f, f') (a, a') => (f a, f' a')) <$>ᴹ r.graph <*>ᴹ s.graph := by
  trans; { apply Mset.Bij.map_graph }; simp only [Mset.Bij.prod_graph, ←Mset.comp_map]; rfl

/-- Membership for the graph of `Mset.Bij.seq` -/
@[simp] protected lemma Mset.Bij.seq_graph_mem
    {A : Mset (α → β)} {B : Mset α} {A' : Mset (α' → β')} {B' : Mset α'}
    (r : A ≃ᴹ A') (s : B ≃ᴹ B') b b' :
    ((b, b') ∈ (Mset.Bij.seq r s).graph) =
      ∃ f a f' a', b = f a ∧ b' = f' a' ∧ (f, f') ∈ r.graph ∧ (a, a') ∈ s.graph := by
  simp only [Mset.Bij.seq_graph, Mset.seq'_mem, Mset.map'_mem]; grind only
