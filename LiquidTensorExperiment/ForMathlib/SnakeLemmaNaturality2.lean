import LiquidTensorExperiment.ForMathlib.SnakeLemma3
import LiquidTensorExperiment.ForMathlib.LesHomology
import LiquidTensorExperiment.ForMathlib.SnakeLemmaNaturality

#align_import for_mathlib.snake_lemma_naturality2

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

section

attribute [-instance] CategoryTheory.prod

@[elab_as_elim]
theorem preorder_prod_induction {C D : Type _} [Preorder C] [Preorder D]
    {motive : ∀ ⦃i j : C × D⦄ (f : i ⟶ j), Prop}
    (comp : ∀ {i j k : C × D} (f : i ⟶ j) (g : j ⟶ k), motive f → motive g → motive (f ≫ g))
    (H1 : ∀ (i : C) {j k : D} (f : j ≤ k), @motive (i, j) (i, k) (homOfLE <| ⟨le_rfl, f⟩))
    (H2 : ∀ {i j : C} (k : D) (f : i ≤ j), @motive (i, k) (j, k) (homOfLE <| ⟨f, le_rfl⟩))
    ⦃i j : C × D⦄ (f : i ⟶ j) : motive f :=
  by
  cases' i with i1 i2; cases' j with j1 j2
  convert comp _ _ (H1 i1 f.le.2) (H2 j2 f.le.1)

end

variable {C D : Type _} [Category C] [Category D]

@[elab_as_elim]
theorem prod_induction {motive : ∀ ⦃i j : C × D⦄ (f : i ⟶ j), Prop}
    (comp : ∀ {i j k : C × D} (f : i ⟶ j) (g : j ⟶ k), motive f → motive g → motive (f ≫ g))
    (H1 : ∀ (i : C) {j k : D} (f : j ⟶ k), @motive (i, j) (i, k) (𝟙 i, f))
    (H2 : ∀ {i j : C} (k : D) (f : i ⟶ j), @motive (i, k) (j, k) (f, 𝟙 k)) ⦃i j : C × D⦄
    (f : i ⟶ j) : motive f :=
  by
  let f1 : (i.1, i.2) ⟶ (i.1, j.2) := (𝟙 i.1, f.2)
  let f2 : (i.1, j.2) ⟶ (j.1, j.2) := (f.1, 𝟙 j.2)
  have hf : f = f1 ≫ f2 := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.id_comp, Category.comp_id]
  rw [hf]; cases i; cases j
  apply comp <;> apply_assumption

@[elab_as_elim]
theorem fin_induction (n : ℕ) {motive : ∀ ⦃i j : Fin (n + 1)⦄ (f : i ≤ j), Prop}
    (id : ∀ i, motive (le_refl i))
    (comp :
      ∀ {i j k : Fin (n + 1)} (f : i ≤ j) (g : j ≤ k),
        motive f → motive g → motive (f.trans g : i ≤ k))
    (Hsucc :
      ∀ i : Fin n, @motive i.cast_succ i.succ (le_of_lt <| by rw [Fin.castSucc_lt_iff_succ_le]))
    ⦃i j : Fin (n + 1)⦄ (f : i ≤ j) : motive f :=
  by
  revert f
  refine' Fin.inductionOn j _ _ <;> clear j
  · intro f; have hi : i = 0 := by erw [eq_bot_iff]; exact f; subst i; convert id _
  · intro j IH f
    obtain hij | rfl | hij := lt_trichotomy i j.succ
    · rw [← Fin.le_castSucc_iff] at hij 
      convert comp _ _ (IH hij) (Hsucc j)
    · convert id _
    · exact (f.not_lt hij).elim

end CategoryTheory

variable {C 𝓐 : Type _} [Category C] [Category 𝓐] [Abelian 𝓐]

namespace HomologicalComplex

variable {ι : Type _} {c : ComplexShape ι}

local notation x "⟶[" D "]" y => D.map (SnakeDiagram.hom x y)

def castHorizontal (i : Fin 4) (j : Fin 2) : SnakeDiagram :=
  (i, j.cast_succ)

def castVertical (i : Fin 3) (j : Fin 3) : SnakeDiagram :=
  (i.cast_succ, j)

def succHorizontal (i : Fin 4) (j : Fin 2) : SnakeDiagram :=
  (i, j.succ)

def succVertical (i : Fin 3) (j : Fin 3) : SnakeDiagram :=
  (i.succ, j)

def toSuccHorizontal (i : Fin 4) (j : Fin 2) : castHorizontal i j ⟶ succHorizontal i j :=
  SnakeDiagram.hom _ _

def toSuccVertical (i : Fin 3) (j : Fin 3) : castVertical i j ⟶ succVertical i j :=
  SnakeDiagram.hom _ _

theorem snakeDiagram_induction {motive : ∀ ⦃i j : SnakeDiagram⦄ (f : i ⟶ j), Prop}
    (id : ∀ i : SnakeDiagram, motive (𝟙 i))
    (comp : ∀ (i j k : SnakeDiagram) (f : i ⟶ j) (g : j ⟶ k), motive f → motive g → motive (f ≫ g))
    (succ_horizontal : ∀ (i : Fin 4) (j : Fin 2), motive (toSuccHorizontal i j))
    (succ_vertical : ∀ (i : Fin 3) (j : Fin 3), motive (toSuccVertical i j)) ⦃i j : SnakeDiagram⦄
    (f : i ⟶ j) : motive f :=
  by
  apply CategoryTheory.preorder_prod_induction comp <;> clear f i j
  · intro i
    refine'
      @CategoryTheory.fin_induction 2
        (fun j k f => motive (hom_of_le <| (⟨le_refl i, f⟩ : (i, j) ≤ (i, k)))) _ _ _
    · intro j; convert id _
    · intro i' j k f g hf hg; convert comp _ _ _ _ _ hf hg
    · intro j; convert succ_horizontal i j
  · intro i j k; revert i j
    refine'
      @CategoryTheory.fin_induction 3
        (fun i j f => motive (hom_of_le <| (⟨f, le_refl k⟩ : (i, k) ≤ (j, k)))) _ _ _
    · intro j; convert id _
    · intro i' j k f g hf hg; convert comp _ _ _ _ _ hf hg
    · intro i; convert succ_vertical i k

variable {X Y Z : C ⥤ HomologicalComplex 𝓐 c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (H : ∀ c i, ShortExact ((f.app c).f i) ((g.app c).f i)) {c₁ c₂ : C} (φ : c₁ ⟶ c₂) (i j : ι)
  (hij : c.Rel i j)

def mkSnakeDiagramNatTransApp :
    ∀ e : SnakeDiagram,
      (snake (f.app c₁) (g.app c₁) (H _) i j hij).SnakeDiagram.obj e ⟶
        (snake (f.app c₂) (g.app c₂) (H _) i j hij).SnakeDiagram.obj e
  | ⟨⟨0, _⟩, ⟨0, _⟩⟩ => (homology'Functor _ _ i).map (X.map φ)
  | ⟨⟨0, _⟩, ⟨1, _⟩⟩ => (homology'Functor _ _ i).map (Y.map φ)
  | ⟨⟨0, _⟩, ⟨2, _⟩⟩ => (homology'Functor _ _ i).map (Z.map φ)
  | ⟨⟨1, _⟩, ⟨0, _⟩⟩ => (modBoundariesFunctor _).map (X.map φ)
  | ⟨⟨1, _⟩, ⟨1, _⟩⟩ => (modBoundariesFunctor _).map (Y.map φ)
  | ⟨⟨1, _⟩, ⟨2, _⟩⟩ => (modBoundariesFunctor _).map (Z.map φ)
  | ⟨⟨2, _⟩, ⟨0, _⟩⟩ => (cycles'Functor _ _ _).map (X.map φ)
  | ⟨⟨2, _⟩, ⟨1, _⟩⟩ => (cycles'Functor _ _ _).map (Y.map φ)
  | ⟨⟨2, _⟩, ⟨2, _⟩⟩ => (cycles'Functor _ _ _).map (Z.map φ)
  | ⟨⟨3, _⟩, ⟨0, _⟩⟩ => (homology'Functor _ _ j).map (X.map φ)
  | ⟨⟨3, _⟩, ⟨1, _⟩⟩ => (homology'Functor _ _ j).map (Y.map φ)
  | ⟨⟨3, _⟩, ⟨2, _⟩⟩ => (homology'Functor _ _ j).map (Z.map φ)
  | _ => 0

-- impossible case
def mk_snakeDiagram_nat_trans_hor :
    ∀ (a : Fin 4) (b : Fin 2),
      (snake (f.app c₁) (g.app c₁) (H _) i j hij).SnakeDiagram.map (toSuccHorizontal a b) ≫
          mkSnakeDiagramNatTransApp f g H φ i j hij (succHorizontal a b) =
        mkSnakeDiagramNatTransApp f g H φ i j hij (castHorizontal a b) ≫
          (snake (f.app c₂) (g.app c₂) (H _) i j hij).SnakeDiagram.map (toSuccHorizontal a b)
  | ⟨0, _⟩, ⟨0, _⟩ => by
    repeat' erw [SnakeDiagram.mkFunctor_map_f0, ← CategoryTheory.Functor.map_comp];
    rw [NatTrans.naturality]
  | ⟨0, _⟩, ⟨1, _⟩ => by
    repeat' erw [SnakeDiagram.mkFunctor_map_g0, ← CategoryTheory.Functor.map_comp];
    rw [NatTrans.naturality]
  | ⟨0, _⟩, ⟨n + 2, h⟩ => by exfalso; rw [Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff] at h ;
    exact Nat.not_lt_zero n h
  | ⟨1, _⟩, ⟨0, _⟩ => by
    repeat' erw [SnakeDiagram.mkFunctor_map_f1, ← CategoryTheory.Functor.map_comp];
    rw [NatTrans.naturality]
  | ⟨1, _⟩, ⟨1, _⟩ => by
    repeat' erw [SnakeDiagram.mkFunctor_map_g1, ← CategoryTheory.Functor.map_comp];
    rw [NatTrans.naturality]
  | ⟨1, _⟩, ⟨n + 2, h⟩ => by exfalso; rw [Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff] at h ;
    exact Nat.not_lt_zero n h
  | ⟨2, _⟩, ⟨0, _⟩ => by
    repeat' erw [SnakeDiagram.mkFunctor_map_f2, ← CategoryTheory.Functor.map_comp];
    rw [NatTrans.naturality]
  | ⟨2, _⟩, ⟨1, _⟩ => by
    repeat' erw [SnakeDiagram.mkFunctor_map_g2, ← CategoryTheory.Functor.map_comp];
    rw [NatTrans.naturality]
  | ⟨2, _⟩, ⟨n + 2, h⟩ => by exfalso; rw [Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff] at h ;
    exact Nat.not_lt_zero n h
  | ⟨3, _⟩, ⟨0, _⟩ => by
    repeat' erw [SnakeDiagram.mkFunctor_map_f3, ← CategoryTheory.Functor.map_comp];
    rw [NatTrans.naturality]
  | ⟨3, _⟩, ⟨1, _⟩ => by
    repeat' erw [SnakeDiagram.mkFunctor_map_g3, ← CategoryTheory.Functor.map_comp];
    rw [NatTrans.naturality]
  | ⟨3, _⟩, ⟨n + 2, h⟩ => by exfalso; rw [Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff] at h ;
    exact Nat.not_lt_zero n h
  | ⟨n + 4, h⟩, _ => by exfalso; repeat' rw [Nat.succ_lt_succ_iff] at h ; exact Nat.not_lt_zero n h

def mk_snakeDiagram_nat_trans_ver :
    ∀ a b : Fin 3,
      (snake (f.app c₁) (g.app c₁) (H _) i j hij).SnakeDiagram.map (toSuccVertical a b) ≫
          mkSnakeDiagramNatTransApp f g H φ i j hij (succVertical a b) =
        mkSnakeDiagramNatTransApp f g H φ i j hij (castVertical a b) ≫
          (snake (f.app c₂) (g.app c₂) (H _) i j hij).SnakeDiagram.map (toSuccVertical a b)
  | ⟨0, _⟩, ⟨0, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_a0]; erw [NatTrans.naturality];
    rfl
  | ⟨0, _⟩, ⟨1, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_b0]; erw [NatTrans.naturality];
    rfl
  | ⟨0, _⟩, ⟨2, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_c0]; erw [NatTrans.naturality];
    rfl
  | ⟨0, _⟩, ⟨n + 3, h⟩ => by exfalso; repeat' rw [Nat.succ_lt_succ_iff] at h ;
    exact Nat.not_lt_zero n h
  | ⟨1, _⟩, ⟨0, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_a1]; erw [NatTrans.naturality];
    rfl
  | ⟨1, _⟩, ⟨1, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_b1]; erw [NatTrans.naturality];
    rfl
  | ⟨1, _⟩, ⟨2, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_c1]; erw [NatTrans.naturality];
    rfl
  | ⟨1, _⟩, ⟨n + 3, h⟩ => by exfalso; repeat' rw [Nat.succ_lt_succ_iff] at h ;
    exact Nat.not_lt_zero n h
  | ⟨2, _⟩, ⟨0, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_a2]; erw [NatTrans.naturality];
    rfl
  | ⟨2, _⟩, ⟨1, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_b2]; erw [NatTrans.naturality];
    rfl
  | ⟨2, _⟩, ⟨2, _⟩ => by repeat' erw [SnakeDiagram.mkFunctor_map_c2]; erw [NatTrans.naturality];
    rfl
  | ⟨2, _⟩, ⟨n + 3, h⟩ => by exfalso; repeat' rw [Nat.succ_lt_succ_iff] at h ;
    exact Nat.not_lt_zero n h
  | ⟨n + 3, h⟩, _ => by exfalso; repeat' rw [Nat.succ_lt_succ_iff] at h ; exact Nat.not_lt_zero n h

-- TODO: Make a general construction, similar to `snake_diagram.mk_functor`
def mkSnakeDiagramNatTrans :
    (snake (f.app c₁) (g.app c₁) (H _) i j hij).SnakeDiagram ⟶
      (snake (f.app c₂) (g.app c₂) (H _) i j hij).SnakeDiagram
    where
  app e := mkSnakeDiagramNatTransApp f g H φ i j hij e
  naturality := by
    apply HomologicalComplex.snakeDiagram_induction
    · intro; simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · intro i j k f g h1 h2; simp only [Functor.map_comp, Category.assoc, h2, reassoc_of h1]
    · exact HomologicalComplex.mk_snakeDiagram_nat_trans_hor f g H φ i j hij
    · exact HomologicalComplex.mk_snakeDiagram_nat_trans_ver f g H φ i j hij

theorem δ_natural :
    δ (f.app c₁) (g.app c₁) (H _) i j hij ≫ (homology'Functor _ _ j).map (X.map φ) =
      (homology'Functor _ _ i).map (Z.map φ) ≫ δ (f.app c₂) (g.app c₂) (H _) i j hij :=
  by
  let η := HomologicalComplex.mkSnakeDiagramNatTrans f g H φ i j hij
  apply (snake_lemma.δ_natural η _ _).symm

end HomologicalComplex

