module

public import RapunSL.Logic.RBI.Core
open Iris BI RBI Mset Mseti PCM PCMI PCMC RR

@[expose] public section

/-! # Sum in RapunSL -/

namespace RBI
variable {ρ : Type u} [RR ρ] (P P' Q Q' R : RProp ρ)
  (A B C C' AB ABC : Mset ρ)

/-! ## Addition of multisets -/

/-- Addition relation over `Mset`s -/
def rmadd (A B C : Mset ρ) : Prop :=
  ∃ AB : A ≃ᴹ B,
    (∀ a b, (a, b) ∈ AB.graph → a ≎ b) ∧
    C = (fun (a, b) ↦ a + b) <$>ᴹ AB.graph

@[inherit_doc rmadd]
scoped macro:50 A:term:50 " +ᴿᴹ " B:term " =ᴿᴹ " C:term:50 : term => `(RBI.rmadd $A $B $C)

/-- `+ᴿᴹ` is commutative -/
lemma rmadd_comm' : A +ᴿᴹ B =ᴿᴹ C → B +ᴿᴹ A =ᴿᴹ C := by
  rintro ⟨AB, coh, rfl⟩; exists AB.symm; and_intros;
  · intro _ _; rw [Bij.symm_graph_mem]; intro _; symm; apply coh; trivial
  · simp only [Bij.symm_graph, ←Mset.comp_map];
    congr; ext1 ⟨a, b⟩; rw [add_comm a b]; rfl

/-- `+ᴿᴹ` is commutative -/
lemma rmadd_comm : A +ᴿᴹ B =ᴿᴹ C ↔ B +ᴿᴹ A =ᴿᴹ C := by
  constructor <;> (intro _; apply rmadd_comm'; trivial)

/-- Construct `+ᴿᴹ` from a multiset of coherent pairs -/
lemma pairs_rmadd (S : Mset (ρ × ρ)) :
    (∀ a b, (a, b) ∈ S → a ≎ b) →
    (Prod.fst <$>ᴹ S) +ᴿᴹ (Prod.snd <$>ᴹ S) =ᴿᴹ (fun (a, b) ↦ a + b) <$>ᴹ S := by
  intro coh;
  have hg : ((Mset.Bij.map_l Prod.fst S).trans (Mset.Bij.map_r Prod.snd S)).graph = S := by
    rw [Mset.Bij.trans_graph_map_l (Mset.Bij.map_l Prod.fst S) (Mset.Bij.map_r Prod.snd S)
      Prod.fst (by intro _ _ mem; rw [Mset.Bij.map_l_graph_mem] at mem; exact mem.1)];
    rw [Mset.Bij.map_r_graph, ←Mset.comp_map]; exact Mset.id_map S
  exists (Mset.Bij.map_l Prod.fst S).trans (Mset.Bij.map_r Prod.snd S); and_intros;
  { rw [hg]; exact coh }; { rw [hg] }

/-- Construct `+ᴿᴹ` from two coherent images of a common multiset -/
lemma rmadd_map {σ : Type*} (S : Mset σ) (f g : σ → ρ) {A B C : Mset ρ} :
    (∀ x ∈ S, f x ≎ g x) → f <$>ᴹ S = A → g <$>ᴹ S = B →
    (fun x ↦ f x + g x) <$>ᴹ S = C → A +ᴿᴹ B =ᴿᴹ C := by
  rintro coh rfl rfl rfl;
  have hcoh : ∀ a b, (a, b) ∈ (fun x ↦ (f x, g x)) <$>ᴹ S → a ≎ b := by
    intro a b mem; rw [Mset.map'_mem] at mem;
    rcases mem with ⟨x, memS, eq⟩; injection eq with ea eb; subst ea; subst eb;
    exact coh _ memS
  have h := pairs_rmadd _ hcoh;
  rw [←Mset.comp_map, ←Mset.comp_map, ←Mset.comp_map] at h; exact h

/-- `+ᴿᴹ` preserves inhabitedness -/
lemma rmadd_inhab : A +ᴿᴹ B =ᴿᴹ C → A.inhab → C.inhab := by
  rintro ⟨r, _, rfl⟩ inh; rw [Mset.inhab_map'];
  rw [←Mset.Bij.graph_fst r, Mset.inhab_map'] at inh; exact inh

/-- `+ᴿᴹ` transfers validity of the left-hand summand to the sum -/
lemma rmadd_valid : A +ᴿᴹ B =ᴿᴹ C → (∀ a ∈ A, ✓ a) → ∀ c ∈ C, ✓ c := by
  rintro ⟨r, coh, rfl⟩ val c elC;
  rw [Mset.map'_mem] at elC; rcases elC with ⟨⟨a, b⟩, mem, rfl⟩;
  refine (RR.add_valid_l _ _ (coh _ _ mem)).mpr ?_;
  apply val; rw [←Mset.Bij.graph_fst r, Mset.map'_mem]; exact ⟨_, mem, rfl⟩

/-- `+ᴿᴹ` transfers validity of the sum to the left-hand summand -/
lemma rmadd_valid_l : A +ᴿᴹ B =ᴿᴹ C → (∀ c ∈ C, ✓ c) → ∀ a ∈ A, ✓ a := by
  rintro ⟨r, coh, rfl⟩ val a elA;
  rw [←Mset.Bij.graph_fst r, Mset.map'_mem] at elA;
  rcases elA with ⟨⟨a', b⟩, mem, rfl⟩;
  refine (RR.add_valid_l _ _ (coh _ _ mem)).mp ?_;
  apply val; rw [Mset.map'_mem]; exact ⟨_, mem, rfl⟩

/-- `+ᴿᴹ` transfers validity of the sum to the right-hand summand -/
lemma rmadd_valid_r : A +ᴿᴹ B =ᴿᴹ C → (∀ c ∈ C, ✓ c) → ∀ b ∈ B, ✓ b := by
  rw [rmadd_comm]; apply rmadd_valid_l

/-- `+ᴿᴹ` is deterministic when the right-hand summand is valid and pairwise incompatible -/
lemma rmadd_unique_r : (∀ b ∈ B, ✓ b) → (∀ b b', B.pairmem b b' → b # b') →
    A +ᴿᴹ B =ᴿᴹ C → A +ᴿᴹ B =ᴿᴹ C' → C = C' := by
  rintro val inc ⟨r, coh, rfl⟩ ⟨s, coh', rfl⟩;
  suffices eq : r = s by rw [eq]
  apply Mset.Bij.eq_graph_no_pairmem; intro a b b' mem mem' pm;
  apply PCMC.incomp_neg_coher b b';
  · apply val; apply Mset.pairmem_mem_l _ _ _ pm
  · apply inc; trivial
  · trans a; { symm; apply coh; trivial }; { apply coh'; trivial }

/-- `+ᴿᴹ` is deterministic when the left-hand summand is valid and pairwise incompatible -/
lemma rmadd_unique_l : (∀ a ∈ A, ✓ a) → (∀ a a', A.pairmem a a' → a # a') →
    A +ᴿᴹ B =ᴿᴹ C → A +ᴿᴹ B =ᴿᴹ C' → C = C' := by
  intro val inc _ _;
  apply rmadd_unique_r B A C C' val inc <;> { apply rmadd_comm'; trivial }

/-- `+ᴿᴹ` is associative -/
lemma rmadd_assoc_l :
    A +ᴿᴹ B =ᴿᴹ AB → AB +ᴿᴹ C =ᴿᴹ ABC → ∃ BC, B +ᴿᴹ C =ᴿᴹ BC ∧ A +ᴿᴹ BC =ᴿᴹ ABC := by
  rintro ⟨r₁, coh₁, rfl⟩ ⟨r₂, coh₂, rfl⟩;
  rcases Mset.Bij.graph_unmap_l (fun ((a, b) : ρ × ρ) ↦ a + b) r₂ with ⟨S, hS1, hS2, hgr⟩;
  have pw : ∀ a b c, ((a, b), c) ∈ S → b ≎ c ∧ a ≎ b + c ∧ (a + b) + c = a + (b + c) := by
    intro a b c mem;
    have ahb : a ≎ b := by
      apply coh₁; rw [←hS1, Mset.map'_mem]; exact ⟨((a, b), c), mem, rfl⟩
    have abhc : a + b ≎ c := by
      apply coh₂; rw [←hgr, Mset.map'_mem]; exact ⟨((a, b), c), mem, rfl⟩
    have _ : b ≎ c := by grw [←abhc]; symm; apply RR.add_coher_r; trivial
    and_intros; { trivial };
    { grw [ahb]; symm; apply RR.add_coher_l; trivial }; { apply RR.add_assoc <;> trivial }
  exists (fun ((a, b), c) ↦ b + c) <$>ᴹ S; simp only; and_intros;
  · apply rmadd_map S (fun ((a, b), c) ↦ b) Prod.snd _ _ hS2 rfl;
    { rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).1 };
    { rw [←Mset.Bij.graph_snd r₁, ←hS1, ←Mset.comp_map]; rfl }
  · apply rmadd_map S (fun ((a, b), c) ↦ a) (fun ((a, b), c) ↦ b + c);
    { rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).2.1 };
    { rw [←Mset.Bij.graph_fst r₁, ←hS1, ←Mset.comp_map]; rfl }; { rfl };
    { rw [←hgr, ←Mset.comp_map]; apply Mset.map_congr;
      rintro ⟨⟨a, b⟩, c⟩ mem; exact (pw _ _ _ mem).2.2.symm }

/-! ## Sum connectives -/

/-- Binary sum over `RProp` -/
instance RProp.instAdd : Add (RProp ρ) where
  add P Q := .mk fun C ↦ ∃ A B, A ∈ P ∧ B ∈ Q ∧
    A.val.val +ᴿᴹ B.val.val =ᴿᴹ C.val.val

scoped macro_rules
  | `(iprop($P + $Q)) => `(iprop($P) + iprop($Q))

/-- Cross, the right adjoint of `+` -/
def cross (P Q : RProp ρ) : RProp ρ :=
  .mk fun A ↦ ∀ B, B ∈ P → ∀ C, A.val.val +ᴿᴹ B.val.val =ᴿᴹ C.val.val → C ∈ Q

@[inherit_doc cross]
scoped syntax:25 term:26 " -+ " term:25 : term

scoped macro_rules
  | `(iprop($P -+ $Q)) => `(RBI.cross iprop($P) iprop($Q))

scoped delab_rules RBI.cross
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) -+ $(← unpackIprop Q)))

/-- Unfold `+` for `RProp` -/
lemma add_unfold :
    (HAdd.hAdd : RProp ρ → RProp ρ → RProp ρ) =
      fun P Q => .mk fun C ↦ ∃ A B, A ∈ P ∧ B ∈ Q ∧
        A.val.val +ᴿᴹ B.val.val =ᴿᴹ C.val.val := rfl

/-! ### Basic rules -/

/-- `+` is monotone -/
@[gcongr] lemma add_mono : (P ⊢ P') → (Q ⊢ Q') → P + Q ⊢ P' + Q' := by
  intro PP' QQ' _ ⟨A, B, _, _, _⟩; exists A, B; and_intros;
  { apply PP'; trivial }; { apply QQ'; trivial }; trivial

/-- `+` is commutative -/
private lemma add_comm' : P + Q ⊢ Q + P := by
  intro _ ⟨A, B, _, _, _⟩; exists B, A; and_intros; { trivial }; { trivial };
  apply rmadd_comm'; trivial

/-- `+` is commutative -/
instance RProp.instAddCommMagma : AddCommMagma (RProp ρ) where
  add_comm := by intro _ _; ext; constructor <;> apply add_comm'

/-- `+` is associative -/
private lemma add_assoc' : (P + Q) + R ⊢ P + (Q + R) := by
  rintro D ⟨ABv, Cv, ⟨Av, Bv, elP, elQ, hAB⟩, elR, hABC⟩;
  rcases rmadd_assoc_l _ _ _ _ _ hAB hABC with ⟨BC, hBC, hA⟩;
  have inh : BC.inhab := rmadd_inhab _ _ _ hBC Bv.val.prop;
  have val : ∀ b ∈ BC, ✓ b := rmadd_valid_r _ _ _ hA D.prop;
  exists Av, ⟨⟨BC, inh⟩, val⟩; and_intros;
  { trivial }; { exists Bv, Cv }; { trivial }

/-- `+` is associative -/
instance RProp.instAddCommSemigroup : AddCommSemigroup (RProp ρ) where
  add_assoc := by
    intro P Q R; apply entails_antisymm; { apply add_assoc' };
    rw [add_comm P (Q + R), add_comm Q R, add_comm P Q, add_comm (Q + P) R];
    apply add_assoc'

/-! ### Rules for `-+` -/

/-- Introduce `-+`, absorbing the left operand of `+` -/
lemma cross_intro_l : (P + Q ⊢ R) → Q ⊢ P -+ R := by
  intro toR A elQ B elP C hadd; apply toR; exists B, A; and_intros;
  { trivial }; { trivial }; apply rmadd_comm'; trivial

/-- Introduce `-+`, absorbing the right operand of `+` -/
lemma cross_intro_r : (P + Q ⊢ R) → P ⊢ Q -+ R := by
  rw [add_comm]; apply cross_intro_l

/-- Eliminate `-+`, with the argument supplied on the left -/
lemma cross_elim_l : P + (P -+ Q) ⊢ Q := by
  rintro C ⟨A, B, elP, elPQ, hadd⟩; apply elPQ A elP; apply rmadd_comm'; trivial

/-- Eliminate `-+`, with the argument supplied on the right -/
lemma cross_elim_r : (P -+ Q) + P ⊢ Q := by
  rw [add_comm]; apply cross_elim_l

/-- `-+` is the right adjoint of `+` -/
lemma cross_adj : (P + Q ⊢ R) ↔ (Q ⊢ P -+ R) := by
  constructor; { apply cross_intro_l };
  intro Qto; grw [Qto]; apply cross_elim_l

/-- `-+` is antitone on the left and monotone on the right -/
@[gcongr] lemma cross_mono : (P' ⊢ P) → (Q ⊢ Q') → (P -+ Q) ⊢ P' -+ Q' := by
  intro P'P QQ'; rw [←cross_adj]; grw [P'P, ←QQ']; rw [cross_adj]

/-! ### Interaction of `+` with disjunction -/

/-- `+` commutes with `∃` in the right operand -/
lemma add_exists_l (Q : α → RProp ρ) :
    P + (∃ a, Q a) =ᴮᴵ ∃ a, P + Q a := by
  ext1; constructor; swap; { apply exists_elim; intro a; grw [exists_intro (Ψ := Q) a] };
  rw [cross_adj]; apply exists_elim; intro a; rw [←cross_adj]; apply exists_intro a

/-- `+` commutes with `∃` in the left operand -/
lemma add_exists_r (P : α → RProp ρ) Q :
    (∃ a, P a) + Q =ᴮᴵ ∃ a, P a + Q := by
  rw [add_comm, add_exists_l]; congr; ext1 _; rw [add_comm]

/-- `+` distributes over `∨` in the right operand -/
lemma add_or_l : P + (Q ∨ R) =ᴮᴵ (P + Q) ∨ (P + R) := by
  simp only [or_as_exists', add_exists_l]; congr; ext1 b; cases b <;> rfl

/-- `+` distributes over `∨` in the left operand -/
lemma add_or_r : (P ∨ Q) + R =ᴮᴵ (P + R) ∨ (Q + R) := by
  rw [add_comm, add_or_l, add_comm, add_comm R]

/-- `False` annihilates `+` in the right operand -/
lemma add_false_l : P + False =ᴮᴵ False := by
  simp only [false_as_exists', add_exists_l]; congr; ext1 _; trivial

/-- `False` annihilates `+` in the left operand -/
lemma add_false_r : False + P =ᴮᴵ False := by
  rw [add_comm, add_false_l]

/-! ### Judgment rules -/

/-- Preciseness of `+` -/
instance add_instPrecise [Frameable P] [Precise Q] : Precise (P + Q) := by
  constructor;
  rintro Cv Cv' ⟨Av, Bv, elP, elQ, hC⟩ ⟨Av', Bv', elP', elQ', hC'⟩;
  rcases precise P _ _ elP elP' with rfl; rcases precise Q _ _ elQ elQ' with rfl;
  apply Subtype.ext; apply Subtype.ext;
  exact rmadd_unique_l _ _ _ _ Av.prop (unambig P _ elP) hC hC'

/-- Satisfiability of `+` -/
lemma add_satis [Satis P] [Satis Q] : (P ≎ᴿ Q) → Satis iprop(P + Q) := by
  intro cohPQ; constructor;
  rcases satis P with ⟨Av, elP⟩; rcases satis Q with ⟨Bv, elQ⟩;
  rcases cohPQ _ _ elP elQ with ⟨r, coh⟩;
  have hadd : Av.val.val +ᴿᴹ Bv.val.val =ᴿᴹ (fun (a, b) ↦ a + b) <$>ᴹ r.graph :=
    ⟨r, coh, rfl⟩;
  have inh := rmadd_inhab _ _ _ hadd Av.val.prop;
  have val := rmadd_valid _ _ _ hadd Av.prop;
  exact ⟨⟨⟨_, inh⟩, val⟩, Av, Bv, elP, elQ, hadd⟩

/-- Incompatibility over `+` -/
lemma incomp_add_l : (P #ᴿ Q) → P + R #ᴿ Q := by
  rintro inc Cv Bv ⟨Av, Rv, elP, elR, r, coh, hC⟩ elQ c b elC elB;
  rw [hC, Mset.map'_mem] at elC;
  rcases elC with ⟨⟨a, x⟩, mem, rfl⟩;
  apply RR.add_incomp_l _ _ _ (coh _ _ mem);
  apply inc _ _ elP elQ _ _ ?_ elB;
  rw [←Mset.Bij.graph_fst r, Mset.map'_mem]; exact ⟨(a, x), mem, rfl⟩

/-- Incompatibility over `+` -/
lemma incomp_add_r : (P #ᴿ Q) → R + P #ᴿ Q := by
  rw [add_comm]; apply incomp_add_l

/-- Unambiguity of `+` -/
instance add_instUnambig [Unambig P] : Unambig (P + Q) := by
  constructor;
  rintro Cv ⟨Av, Bv, elP, elQ, r, coh, hC⟩ c c' pm;
  rw [hC, Mset.map'_pairmem] at pm;
  rcases pm with ⟨⟨a, b⟩, ⟨a', b'⟩, pm, rfl, rfl⟩;
  have pmA : Av.val.val.pairmem a a' := by
    rw [←Mset.Bij.graph_fst r, Mset.map'_pairmem]; exact ⟨(a, b), (a', b'), pm, rfl, rfl⟩
  apply RR.add_incomp;
  · exact coh _ _ (Mset.pairmem_mem_l _ _ _ pm)
  · exact coh _ _ (Mset.pairmem_mem_r _ _ _ pm)
  · exact unambig P _ elP _ _ pmA

/-- Frameability of `+` -/
instance add_instFrameable [Frameable P] [Precise Q] : Frameable (P + Q) := inferInstance

/-- Coherence over `+` -/
lemma coher_add' : (P ≎ᴿ P') → P + Q ≎ᴿ P' := by
  rintro coh Cv Bv ⟨Av, Qv, elP, elQ, r, cohr, hC⟩ elP';
  rcases coh _ _ elP elP' with ⟨f, cohf⟩; rw [hC];
  exists (Mset.Bij.map_l (fun (a, b) ↦ a + b) r.graph).trans (r.graph_dom.trans f);
  intro c b' mem;
  rcases Mset.Bij.trans_graph_mem _ _ _ _ mem with ⟨⟨a, b⟩, mem₁, mem₂⟩;
  rcases Mset.Bij.trans_graph_mem _ _ _ _ mem₂ with ⟨a', mem₃, mem₄⟩;
  rw [Mset.Bij.map_l_graph_mem] at mem₁; rw [Mset.Bij.graph_dom_graph_mem] at mem₃;
  rcases mem₁ with ⟨rfl, memr⟩; rcases mem₃ with ⟨_, rfl⟩;
  trans a'; { apply RR.add_coher_l; apply cohr; trivial }; { apply cohf; trivial }

/-- Coherence over `+` -/
lemma coher_add : (P ≎ᴿ P') → P + Q ≎ᴿ P' + Q' := by
  intro _; apply coher_add'; symm; apply coher_add'; symm; trivial

end RBI
