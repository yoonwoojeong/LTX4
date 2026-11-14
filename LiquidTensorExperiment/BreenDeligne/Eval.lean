import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import LiquidTensorExperiment.ForMathlib.HomologicalComplex2
import LiquidTensorExperiment.ForMathlib.AdditiveFunctor
import LiquidTensorExperiment.BreenDeligne.Homotopy

#align_import breen_deligne.eval

noncomputable section

open scoped BigOperators

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Preadditive

variable {𝒜 : Type _} [Category 𝒜] [HasZeroMorphisms 𝒜] [HasFiniteBiproducts 𝒜]

-- move this
@[simps (config := { fullyApplied := false })]
def pow (n : ℕ) : 𝒜 ⥤ 𝒜 where
  obj A := ⨁ fun i : Fin n => A
  map A B f := biproduct.map fun i => f
  map_id A := by ext i j; simp only [biproduct.ι_map, Category.id_comp, Category.comp_id]
  map_comp A B C f g := by ext i j; simp only [biproduct.ι_map_assoc, Category.assoc]

-- move this
attribute [simps] comp_hom

instance (n : ℕ) {J : Type _} [Category J] : PreservesColimitsOfShape J (pow n : 𝒜 ⥤ 𝒜)
    where PreservesColimit K :=
    {
      preserves := fun c hc =>
        { desc := fun s =>
            biproduct.desc fun i =>
              let t : Cocone K :=
                { pt := s.pt
                  ι := {
                        app := fun j => show K.obj j ⟶ (K ⋙ pow n).obj j from biproduct.ι _ i
                        naturality := by
                          intro X Y f <;> simp only [Functor.comp_map, Pow_map, biproduct.ι_map] } ≫
                      s.ι }
              hc.desc t
          fac := by
            intros; ext
            simp only [Pow_map, Functor.mapCocone_ι_app, biproduct.map_desc, IsColimit.fac,
              NatTrans.comp_app, biproduct.ι_desc]
          uniq := by
            intros; ext i
            simp only [biproduct.ι_desc]
            let t : cocone K :=
              { pt := s.X
                ι := {
                      app := fun j => show K.obj j ⟶ (K ⋙ Pow n).obj j from biproduct.ι _ i
                      naturality := by
                        intro X Y f <;> simp only [Functor.comp_map, Pow_map, biproduct.ι_map] } ≫
                    s.ι }
            refine' hc.uniq t (_ ≫ m) _
            intro j
            simp only [NatTrans.comp_app, ← w, Functor.mapCocone_ι_app, Pow_map,
              biproduct.ι_map_assoc] } }

instance (n : ℕ) : PreservesColimits (pow n : 𝒜 ⥤ 𝒜)
    where PreservesColimitsOfShape J hJ := by infer_instance

end Preadditive

end CategoryTheory

namespace Homotopy

variable {ι 𝒜 : Type _} [Category 𝒜] [Preadditive 𝒜] {c : ComplexShape ι}

variable {C D : HomologicalComplex 𝒜 c} {f g : C ⟶ D}

@[simps]
def congr (h : Homotopy f g) (f' g' : C ⟶ D) (hf : f = f') (hg : g = g') : Homotopy f' g' :=
  { h with comm := by simpa only [hf, hg] using h.comm }

end Homotopy

namespace BreenDeligne

open CategoryTheory.Preadditive

variable (BD : Data)

variable {𝒜 : Type _} [Category 𝒜] [Preadditive 𝒜] [HasFiniteBiproducts 𝒜]

variable (F : 𝒜 ⥤ 𝒜)

namespace BasicUniversalMap

variable {m n o : ℕ} (f : BasicUniversalMap m n) (g : BasicUniversalMap n o)

@[simps (config := { fullyApplied := false })]
def evalPow : (pow m : 𝒜 ⥤ 𝒜) ⟶ pow n
    where
  app A := biproduct.matrix fun i j => f j i • 𝟙 A
  naturality := by
    intros; ext i j
    simp only [Pow_map, biproduct.ι_map_assoc, Category.assoc, biproduct.matrix_π, biproduct.map_π,
      biproduct.ι_desc, biproduct.matrix_π_assoc, biproduct.ι_desc_assoc, comp_zsmul, zsmul_comp,
      Category.comp_id, Category.id_comp]

@[simp]
theorem evalPow_comp : @evalPow 𝒜 _ _ _ _ _ (comp g f) = f.evalPow ≫ g.evalPow :=
  by
  ext A i j
  simp only [eval_Pow_app, NatTrans.comp_app, Category.assoc, biproduct.ι_map_assoc,
    biproduct.matrix_π, biproduct.ι_matrix_assoc, biproduct.lift_desc, biproduct.map_π,
    biproduct.ι_desc, biproduct.matrix_π_assoc, biproduct.ι_desc_assoc, comp_zsmul, zsmul_comp,
    Category.comp_id, Category.id_comp]
  simp only [comp, AddMonoidHom.mk'_apply, HMul.hMul, Matrix.dotProduct, Finset.sum_smul, mul_smul]
  rw [Finset.sum_congr rfl]
  rintro j -
  rw [smul_comm]

end BasicUniversalMap

namespace UniversalMap

variable {m n o : ℕ} (f : UniversalMap m n) (g : UniversalMap n o)

/- Note: this definition is generalized in `eval1half.lean` for a functor
`F : A₁ ⥤ A₂`. This generalization is used in `apply_Pow.lean`. -/
def evalPow : UniversalMap m n →+ (pow m ⋙ F ⟶ pow n ⋙ F) :=
  FreeAbelianGroup.lift fun g : BasicUniversalMap m n => whiskerRight g.evalPow F

theorem evalPow_of (g : BasicUniversalMap m n) :
    evalPow F (FreeAbelianGroup.of g) = whiskerRight g.evalPow F :=
  FreeAbelianGroup.lift.of _ _

@[simp]
theorem evalPow_zero : evalPow F (0 : UniversalMap m n) = 0 :=
  AddMonoidHom.map_zero _

theorem evalPow_zero_app (A : 𝒜) : (evalPow F (0 : UniversalMap m n)).app A = 0 := by
  rw [eval_Pow_zero, zero_app]

theorem evalPow_comp : evalPow F (UniversalMap.comp g f) = evalPow F f ≫ evalPow F g :=
  by
  rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.comp_apply,
    eq_comm, ← CategoryTheory.Preadditive.compHom_apply_apply, ← AddMonoidHom.flip_apply, ←
    AddMonoidHom.comp_apply, ← AddMonoidHom.compHom_apply_apply, ←
    AddMonoidHom.flip_apply _ _ (eval_Pow F), ← AddMonoidHom.comp_apply, ←
    AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.comp_apply, ← AddMonoidHom.compHom_apply_apply]
  congr 2
  clear f g
  ext g f : 2
  simp only [AddMonoidHom.compHom_apply_apply, AddMonoidHom.comp_apply, AddMonoidHom.flip_apply,
    CategoryTheory.Preadditive.compHom_apply_apply, comp_of, eval_Pow_of, whisker_right_comp,
    BasicUniversalMap.evalPow_comp]

theorem evalPow_comp_app (A : 𝒜) :
    (evalPow F (UniversalMap.comp g f)).app A = (evalPow F f).app A ≫ (evalPow F g).app A := by
  rw [eval_Pow_comp, NatTrans.comp_app]

@[simps (config := { fullyApplied := false })]
def evalPowFunctor : FreeMat ⥤ 𝒜 ⥤ 𝒜 where
  obj n := pow n ⋙ F
  map m n f := evalPow F f
  map_id n := by
    refine' (eval_Pow_of F _).trans _
    ext A : 2; dsimp
    rw [← F.map_id]; congr 1
    ext i j : 2
    simp only [biproduct.ι_matrix, Category.comp_id, biproduct.lift_π, BasicUniversalMap.id]
    rw [biproduct.ι_π]
    split_ifs with hij
    · cases hij; rw [Matrix.one_apply_eq, one_smul, CategoryTheory.eqToHom_refl]
    · rw [Matrix.one_apply_ne, zero_smul]; dsimp; rintro rfl; exact hij rfl
  map_comp m n o f g := evalPow_comp F _ _

instance evalPowFunctor_additive : (evalPowFunctor F).Additive
    where map_add' m n f g := by dsimp [eval_Pow]; rw [AddMonoidHom.map_add]

end UniversalMap

namespace Data

open UniversalMap

@[simps (config := { fullyApplied := false })]
def evalFunctor' : Data ⥤ ChainComplex (𝒜 ⥤ 𝒜) ℕ :=
  (evalPowFunctor F).mapHomologicalComplex _

@[simps (config := { fullyApplied := false })]
def evalFunctor : Data ⥤ 𝒜 ⥤ ChainComplex 𝒜 ℕ :=
  evalFunctor' F ⋙ HomologicalComplex.functorEval.flip

-- generalize to arbitrary homological complexes
instance HomologicalComplex.functorEvalFlipPreservesColimitsOfShape (J : Type _) [Category J]
    (F : ChainComplex (𝒜 ⥤ 𝒜) ℕ) [∀ i, PreservesColimitsOfShape J (F.pt i)] :
    PreservesColimitsOfShape J (HomologicalComplex.functorEval.flip.obj F)
    where PreservesColimit K :=
    {
      preserves := fun c hc =>
        let t :
          ∀ (s : Cocone (K ⋙ HomologicalComplex.functorEval.flip.obj F)) (i : ℕ),
            Cocone (K ⋙ F.pt i) :=
          fun s i =>
          { pt := s.pt.pt i
            ι :=
              { app := fun j => show (K ⋙ F.pt i).obj j ⟶ s.pt.pt i from (s.ι.app j).f i
                naturality := by
                  intro a b φ; have := s.ι.naturality φ; dsimp at this ⊢
                  simp only [Category.comp_id] at this ⊢
                  rw [← this]; rfl } }
        let u :
          ∀ (s : Cocone (K ⋙ HomologicalComplex.functorEval.flip.obj F)) (i j : ℕ),
            Cocone (K ⋙ F.pt i) :=
          fun s i j =>
          { pt := s.pt.pt j
            ι :=
              { app := fun k =>
                  show (K ⋙ F.pt i).obj k ⟶ s.pt.pt j from
                    (whiskerLeft K (F.d i j)).app k ≫ (s.ι.app k).f j
                naturality := by
                  intro a b φ; have := s.ι.naturality φ; dsimp at this ⊢
                  simp only [Category.comp_id] at this ⊢
                  rw [← this, (F.d i j).naturality_assoc]; rfl } }
        { desc := fun s =>
            { f := fun i => (isColimitOfPreserves (F.pt i) hc).desc (t s i)
              comm' := by
                intro i j h; dsimp
                have := (CategoryTheory.Limits.isColimitOfPreserves (F.X i) hc).uniq (u s i j)
                refine' (this _ _).trans (this _ _).symm
                · intro j'; dsimp
                  erw [(CategoryTheory.Limits.isColimitOfPreserves (F.X i) hc).fac_assoc]
                  apply (s.ι.app j').comm
                · intro j'; dsimp
                  rw [NatTrans.naturality_assoc]
                  erw [(CategoryTheory.Limits.isColimitOfPreserves (F.X j) hc).fac] }
          fac := by intros; ext i; dsimp; erw [(CategoryTheory.Limits.isColimitOfPreserves (F.X i) hc).fac]
          uniq := by
            intros; ext i
            exact
              (CategoryTheory.Limits.isColimitOfPreserves (F.X i) hc).uniq (t s i) (m.f i) fun j =>
                HomologicalComplex.congr_hom (w j) i } }

instance evalFunctorPreservesColimitsOfShape (BD : Data) (J : Type _) [Category J]
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J ((evalFunctor F).obj BD) :=
  by
  refine'
    @HomologicalComplex.functorEvalFlipPreservesColimitsOfShape _ _ _ _ J _
      ((BreenDeligne.Data.evalFunctor' F).obj BD) (id _)
  intro i
  show preserves_colimits_of_shape J (Pow (BD.X i) ⋙ F)
  infer_instance

instance evalFunctorPreservesFilteredColimits (BD : Data) [PreservesFilteredColimits F] :
    PreservesFilteredColimits ((evalFunctor F).obj BD)
    where PreservesFilteredColimits := by intros <;> infer_instance

-- @[simps]
-- def eval_functor.obj (M : 𝒜) : chain_complex 𝒜 ℕ :=
-- { X := λ n, (Pow (BD.X n) ⋙ F).obj M,
--   d := λ m n, (eval_Pow F (BD.d m n)).app M,
--   shape' := λ i j h, by rw [BD.shape i j h, universal_map.eval_Pow_zero_app],
--   d_comp_d' := λ i j k hij hjk, begin
--     rw [← universal_map.eval_Pow_comp_app],
--     have := BD.d_comp_d i j k,
--     convert universal_map.eval_Pow_zero_app _ _ using 3,
--   end }
-- @[simps {fully_applied := ff}]
-- def eval_functor : 𝒜 ⥤ chain_complex 𝒜 ℕ :=
-- { obj := eval_functor.obj BD F,
--   map := λ A B f,
--   { f := λ n, (Pow (BD.X n) ⋙ F).map f,
--     comm' := λ m n h, by simp only [eval_functor.obj_d, nat_trans.naturality] },
--   map_id' := λ A, by { ext n, exact category_theory.functor.map_id _ _ },
--   map_comp' := λ A B C f g, by { ext n, exact category_theory.functor.map_comp _ _ _ } }
-- @[simps {fully_applied := ff}]
-- def map_eval_functor {BD₁ BD₂ : data} (φ : BD₁ ⟶ BD₂) :
--   BD₁.eval_functor F ⟶ BD₂.eval_functor F :=
-- { app := λ A,
--   { f := λ i, (universal_map.eval_Pow F (φ.f i)).app A,
--     comm' := by { intros, dsimp only [eval_functor_obj, eval_functor.obj_d],
--       simp only [← nat_trans.comp_app, ← eval_Pow_comp F], congr' 2, apply φ.comm } },
--   naturality' := λ A B f, by { ext i : 2, apply nat_trans.naturality } }
end Data

namespace Package

open UniversalMap

variable (BD' : Package) (A : 𝒜)

def evalHomotopy :=
  (evalPowFunctor F).mapHomotopy BD'.Homotopy

def evalHomotopy' (A : 𝒜) :=
  (evalPowFunctor F ⋙ (evaluation _ _).obj A).mapHomotopy BD'.Homotopy

attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts

@[simps]
def biprod : 𝒜 ⥤ 𝒜 where
  obj A := A ⊞ A
  map A B f := biprod.map f f
  map_id A := by
    ext <;> simp only [biprod.inl_map, biprod.inr_map, Category.id_comp, Category.comp_id]
  map_comp A B C f g := by
    ext <;> simp only [biprod.inl_map_assoc, biprod.inr_map_assoc, Category.assoc]

@[simps (config := { fullyApplied := false })]
def biprodIsoPowTwoComponents (A : 𝒜) : A ⊞ A ≅ (pow 2).obj A
    where
  hom := biprod.desc (biproduct.ι (fun i : Fin 2 => A) 0) (biproduct.ι (fun i : Fin 2 => A) 1)
  inv := biprod.lift (biproduct.π _ 0) (biproduct.π _ 1)
  hom_inv_id := by
    ext <;>
              simp only [biprod.lift_fst, biprod.lift_snd, biprod.inl_desc_assoc,
                biprod.inr_desc_assoc, biproduct.ι_π_self, Category.assoc] <;>
            erw [Category.id_comp] <;>
          simp only [biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd] <;>
        rw [biproduct.ι_π_ne] <;>
      decide
  inv_hom_id := by
    ext i j
    erw [Category.comp_id]
    simp only [add_comp, comp_add, biprod.lift_desc, Category.assoc]
    fin_cases i with [0, 1] <;> rw [biproduct.ι_π_self_assoc, biproduct.ι_π_ne_assoc, zero_comp]
    swap; · decide
    pick_goal 3; · decide
    · rw [add_zero]
    · rw [zero_add]

@[simps (config := { fullyApplied := false })]
def biprodIsoPowTwo : (biprod : 𝒜 ⥤ 𝒜) ≅ pow 2 :=
  NatIso.ofComponents biprodIsoPowTwoComponents fun A B f => by
    ext ⟨i⟩ <;>
      simp only [biproduct.ι_map, Biprod_iso_Pow_two_components_hom, Biprod_map, Pow_map,
        biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc_assoc,
        biprod.inr_map, Category.assoc, biprod.inr_desc]

@[simps]
def powCompPowComponents (m n : ℕ) (A : 𝒜) : (pow n).obj ((pow m).obj A) ≅ (pow (m * n)).obj A
    where
  hom :=
    biproduct.desc fun j =>
      biproduct.desc fun i => biproduct.ι (fun i : Fin _ => A) (finProdFinEquiv (i, j))
  inv :=
    biproduct.lift fun j =>
      biproduct.lift fun i => biproduct.π (fun i : Fin _ => A) (finProdFinEquiv (i, j))
  hom_inv_id := by
    ext j i j' i' : 4
    erw [biproduct.ι_desc_assoc, Category.comp_id]
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π]
    by_cases hj : j = j'
    · subst hj; rw [biproduct.ι_π_self_assoc]
      by_cases hi : i = i'
      · subst hi; rw [biproduct.ι_π_self, biproduct.ι_π_self]
      · rw [biproduct.ι_π_ne, biproduct.ι_π_ne]
        · exact hi
        ·
          simpa only [Equiv.apply_eq_iff_eq, and_true_iff, Prod.mk.inj_iff, eq_self_iff_true,
            Ne.def] using hi
    · rw [biproduct.ι_π_ne, biproduct.ι_π_ne_assoc, zero_comp, comp_zero]
      · exact hj
      · simp only [Equiv.apply_eq_iff_eq, Prod.mk.inj_iff, Ne.def, hj, not_false_iff, and_false_iff]
  inv_hom_id := by
    ext k k' : 2
    erw [Category.comp_id]
    simp only [Category.assoc, biproduct.lift_desc, sum_comp, comp_sum]
    by_cases h : k = k'
    · subst h
      rw [biproduct.ι_π_self, Finset.sum_eq_single ((fin_prod_fin_equiv.symm k).snd : Fin _),
        Finset.sum_eq_single ((fin_prod_fin_equiv.symm k).fst : Fin _)]
      · rw [Prod.mk.eta, Equiv.apply_symm_apply, biproduct.ι_π_self, biproduct.ι_π_self_assoc]
      · rintro ⟨i⟩ - hi
        rw [biproduct.ι_π_ne_assoc, zero_comp]
        dsimp [-finProdFinEquiv_symm_apply]
        simp only [Ne.def, ← Equiv.symm_apply_eq, Prod.ext_iff, not_and_or] at hi ⊢
        exact Or.inl (Ne.symm hi)
      · intro h; exact (h (Finset.mem_univ _)).elim
      · rintro ⟨j⟩ - hj
        rw [Finset.sum_eq_zero]
        rintro ⟨i⟩ -
        rw [biproduct.ι_π_ne_assoc, zero_comp]
        dsimp [-finProdFinEquiv_symm_apply]
        simp only [Ne.def, ← Equiv.symm_apply_eq, Prod.ext_iff, not_and_or] at hj ⊢
        exact Or.inr (Ne.symm hj)
      · intro h; exact (h (Finset.mem_univ _)).elim
    · rw [biproduct.ι_π_ne, Finset.sum_eq_zero]
      · rintro j -
        rw [Finset.sum_eq_zero]
        rintro i -
        by_cases hk : k = finProdFinEquiv (i, j)
        · subst hk
          rw [biproduct.ι_π_self_assoc, biproduct.ι_π_ne]
          simpa only [Ne.def] using h
        · rw [biproduct.ι_π_ne_assoc, zero_comp]
          dsimp [-finProdFinEquiv_symm_apply]
          simpa only [Ne.def] using h
      · rw [Ne.def]; exact h

@[simps (config := { fullyApplied := false })]
def powCompPow (m n : ℕ) : (pow m ⋙ pow n : 𝒜 ⥤ 𝒜) ≅ pow (m * n) :=
  NatIso.ofComponents (powCompPowComponents m n) fun A B f =>
    by
    ext ⟨j⟩ ⟨i⟩ ⟨k⟩
    simp only [biproduct.ι_map, Pow_comp_Pow_components_hom, Pow_map, Functor.comp_map,
      biproduct.ι_map_assoc, Category.assoc, biproduct.map_π, biproduct.ι_desc_assoc]

theorem FreeAbelianGroup.eq_zero_induction {α M : Type _} [AddGroup M] (f : FreeAbelianGroup α → M)
    (h1 : ∀ a, f (FreeAbelianGroup.of a) = 0) (h2 : ∀ x y, f (x + y) = f x + f y) : ∀ x, f x = 0 :=
  by
  let F := AddMonoidHom.mk' f h2
  have hF : ∀ x, F x = f x := fun _ => rfl
  intro x
  refine' FreeAbelianGroup.induction_on x _ h1 _ _
  · exact F.map_zero
  · intros; show F _ = 0; rw [F.map_neg, hF, h1, neg_zero]
  · intro x y hx hy; show F _ = 0; rw [F.map_add, hF, hF, hx, hy, add_zero]

theorem aux' (m n : ℕ) (f : UniversalMap m n) :
    F.map ((powCompPow 2 m).inv.app A ≫ (pow m).map (biprodIsoPowTwo.inv.app A)) ≫
        ((evalPowFunctor F).map f).app (biprod.obj A) =
      ((evalPowFunctor F).map ((mul 2) f)).app A ≫
        F.map ((powCompPow 2 n).inv.app A ≫ (pow n).map (biprodIsoPowTwo.inv.app A)) :=
  by
  rw [← sub_eq_zero]
  refine' FreeAbelianGroup.eq_zero_induction _ _ _ f <;> clear f
  · intro f
    rw [sub_eq_zero]
    dsimp only [eval_Pow_functor]
    rw [mul_of, eval_Pow_of, eval_Pow_of]
    dsimp only [CategoryTheory.whiskerRight_app, BasicUniversalMap.evalPow_app]
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    dsimp only [Pow_comp_Pow, Biprod_iso_Pow_two]
    erw [NatIso.ofComponents_inv_app, NatIso.ofComponents_inv_app,
      NatIso.ofComponents_inv_app]
    dsimp only [Pow_comp_Pow_components_inv, Biprod_iso_Pow_two_components_inv, Pow_map]
    apply CategoryTheory.Limits.biproduct.hom_ext
    rintro ⟨j⟩
    apply CategoryTheory.Limits.biproduct.hom_ext'
    refine' fin_prod_fin_equiv.forall_congr_left.mp _
    rintro ⟨b, i⟩
    rw [biproduct.lift_map, biproduct.lift_matrix, biproduct.lift_π, comp_sum, biproduct.lift_map,
      Category.assoc, biproduct.ι_matrix_assoc, biproduct.lift_π]
    rw [Finset.sum_eq_single i]
    · rw [Category.assoc]
      ext <;>
                rw [Category.assoc, Category.assoc, comp_zsmul, zsmul_comp, comp_zsmul, comp_zsmul,
                  Category.comp_id, Category.assoc, Category.assoc] <;>
              [rw [biprod.lift_fst]; rw [biprod.lift_snd]] <;>
            rw [biproduct.lift_π, biproduct.lift_π, biproduct.lift_π, biproduct.ι_π,
              BasicUniversalMap.hMul_apply, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
              Matrix.submatrix_apply, Matrix.kroneckerMap, Equiv.symm_apply_apply,
              Equiv.symm_apply_apply] <;>
          simp only [dite_eq_ite, Equiv.apply_eq_iff_eq, and_true_iff, Prod.mk.inj_iff,
            eq_self_iff_true, CategoryTheory.eqToHom_refl, Matrix.one_apply, ite_mul, ite_smul, one_mul,
            MulZeroClass.zero_mul, zero_smul, @eq_comm _ b, smul_ite, smul_zero] <;>
        congr 1
    · rintro i' - hi'
      rw [Ne.def, eq_comm] at hi' 
      rw [Category.assoc]
      ext <;>
              rw [Category.assoc, Category.assoc, comp_zsmul, zsmul_comp, comp_zsmul, comp_zsmul,
                Category.comp_id, zero_comp] <;>
            [rw [biprod.lift_fst]; rw [biprod.lift_snd]] <;>
          rw [biproduct.lift_π, biproduct.ι_π] <;>
        simp only [dite_eq_ite, Equiv.apply_eq_iff_eq, and_true_iff, Prod.mk.inj_iff,
          eq_self_iff_true, CategoryTheory.eqToHom_refl, Equiv.uLift_symm_apply, eq_false hi', and_false_iff,
          if_false, smul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro x y
    simp only [AddMonoidHom.map_add, Functor.map_add, comp_add, add_comp, NatTrans.app_add]
    abel

@[simps (config := { fullyApplied := false })]
def aux :
    (Data.evalFunctor F).obj ((Data.mul 2).obj BD'.data) ≅
      biprod ⋙ (Data.evalFunctor F).obj BD'.data :=
  NatIso.ofComponents
    (fun A =>
      HomologicalComplex.Hom.isoOfComponents
        (fun i => by
          refine' F.map_iso _
          refine' (Pow_comp_Pow 2 (BD'.data.X i)).symm.app A ≪≫ _
          refine' (Pow _).mapIso (Biprod_iso_Pow_two.symm.app A))
        fun i j hij => aux' F A (BD'.data.pt i) (BD'.data.pt j) (BD'.data.d i j))
    fun A B f => by
    ext i
    dsimp only [Data.evalFunctor, Data.evalFunctor', eval_Pow, eval_Pow_functor_obj,
      Functor.mapIso_hom, Functor.comp_obj, Functor.comp_map, Functor.flip_obj_map, Iso.trans_hom,
      Iso.symm_hom, NatIso.app_hom, functor.map_homological_complex_obj_X,
      HomologicalComplex.functorEval_map_app_f, HomologicalComplex.comp_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f]
    rw [← F.map_comp, ← F.map_comp, ← Category.assoc, NatTrans.naturality, Category.assoc,
      Category.assoc, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp,
      NatTrans.naturality]

-- move this up
theorem quux (n : ℕ) {N : ℕ} (k : Fin N) (A : 𝒜) :
    (BasicUniversalMap.proj n k).evalPow.app A =
      biproduct.matrix fun i j => if i = finProdFinEquiv (k, j) then 𝟙 A else 0 :=
  by
  apply CategoryTheory.Limits.biproduct.hom_ext
  rintro ⟨j⟩
  apply CategoryTheory.Limits.biproduct.hom_ext'
  refine' fin_prod_fin_equiv.forall_congr_left.mp _
  rintro ⟨l, i⟩
  dsimp only [BasicUniversalMap.evalPow_app]
  rw [biproduct.matrix_π, biproduct.matrix_π, biproduct.ι_desc, biproduct.ι_desc]
  dsimp only [BasicUniversalMap.proj, BasicUniversalMap.projAux,
    Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix, Matrix.kroneckerMap,
    Matrix.of_apply]
  simp only [ite_mul, ite_smul, one_mul, one_smul, MulZeroClass.zero_mul, zero_smul,
    Matrix.one_apply]
  rw [← ite_and]
  congr 1
  apply propext
  rw [← Equiv.symm_apply_eq, Prod.ext_iff]
  apply and_congr Iff.rfl
  dsimp only [Equiv.punitProd_symm_apply]
  rw [eq_comm]

-- move this up
theorem evalPow_add {m n : ℕ} (f g : BasicUniversalMap m n) (A : 𝒜) :
    (f + g).evalPow.app A = f.evalPow.app A + g.evalPow.app A :=
  by
  dsimp [BasicUniversalMap.evalPow_app]
  ext ⟨i⟩ ⟨j⟩
  simp only [biproduct.ι_matrix, biproduct.lift_π, comp_add, add_comp, add_zsmul]

def evalFunctorHomotopy (A : 𝒜) :
    Homotopy (((Data.evalFunctor F).obj BD'.data).map (biprod.fst + biprod.snd : A ⊞ A ⟶ A))
      (((Data.evalFunctor F).obj BD'.data).map (biprod.fst : A ⊞ A ⟶ A) +
        ((Data.evalFunctor F).obj BD'.data).map (biprod.snd : A ⊞ A ⟶ A)) :=
  by
  refine' ((BreenDeligne.Package.evalHomotopy' F BD' A).symm.compLeft ((aux F BD').inv.app A)).congr _ _ _ _
  · ext i
    rw [HomologicalComplex.comp_f, aux_inv_app_f, Functor.mapHomologicalComplex_map_f,
      Functor.comp_map, eval_Pow_functor_map, evaluation_obj_map, Data.evalFunctor_obj_map_f]
    dsimp only [Data.sum, UniversalMap.sum]
    rw [eval_Pow_of, CategoryTheory.whiskerRight_app, ← F.map_comp, Fin.sum_univ_two, eval_Pow_add, quux, quux]
    congr 1
    apply CategoryTheory.Limits.biproduct.hom_ext'; rintro m
    rw [biproduct.ι_desc_assoc, biproduct.ι_map, Category.assoc]
    apply CategoryTheory.Limits.biproduct.hom_ext; rintro n
    rw [Category.assoc]
    apply CategoryTheory.Limits.biprod.hom_ext' <;> [rw [biprod.inl_desc_assoc];
          rw [biprod.inr_desc_assoc]] <;>
        rw [Category.assoc, biproduct.ι_desc_assoc, add_comp, comp_add, biproduct.matrix_π,
          biproduct.matrix_π, biproduct.ι_desc, biproduct.ι_desc, Category.assoc, add_comp,
          comp_add] <;>
      simp only [biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_fst_assoc,
        biprod.inr_snd_assoc, zero_comp, add_zero, zero_add, true_and_iff, Equiv.apply_eq_iff_eq,
        Prod.mk.inj_iff, one_ne_zero, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, eq_self_iff_true,
        if_false, false_and_iff]
    all_goals
      by_cases hmn : m = n
      · cases hmn; rw [if_pos rfl, biproduct.ι_π_self]
      · rw [if_neg, biproduct.ι_π_ne] <;> [rw [Ne.def]; skip] <;> exact hmn
  · ext i
    rw [HomologicalComplex.comp_f, aux_inv_app_f, Functor.mapHomologicalComplex_map_f,
      Functor.comp_map, eval_Pow_functor_map, evaluation_obj_map, HomologicalComplex.add_f_apply,
      Data.evalFunctor_obj_map_f, Data.evalFunctor_obj_map_f]
    dsimp only [Data.proj, proj]
    rw [AddMonoidHom.map_sum, Fin.sum_univ_two, eval_Pow_of, eval_Pow_of, NatTrans.app_add,
      CategoryTheory.whiskerRight_app, CategoryTheory.whiskerRight_app, comp_add, ← F.map_comp, ← F.map_comp, quux, quux]
    congr 2 <;>
      · apply CategoryTheory.Limits.biproduct.hom_ext; rintro n
        rw [biproduct.map_π, Category.assoc, biproduct.matrix_π]
        apply CategoryTheory.Limits.biproduct.hom_ext'; rintro m
        rw [biproduct.ι_desc_assoc, Category.assoc]
        apply CategoryTheory.Limits.biprod.hom_ext' <;> [rw [biprod.inl_desc_assoc];
          rw [biprod.inr_desc_assoc]]
        all_goals
          rw [biproduct.ι_desc_assoc, biproduct.ι_desc] <;>
              simp only [true_and_iff, Equiv.apply_eq_iff_eq, Prod.mk.inj_iff, eq_self_iff_true] <;>
            by_cases hmn : m = n
          · cases hmn
            simp only [biproduct.ι_π_self_assoc, eq_self_iff_true, if_true, if_false,
              biprod.inl_fst, biprod.inr_fst, biprod.inl_snd, biprod.inr_snd, zero_ne_one,
              one_ne_zero, false_and_iff, Fin.one_eq_zero_iff, Fin.zero_eq_one_iff]
          · rw [biproduct.ι_π_ne_assoc]; swap; · rw [Ne.def]; exact hmn
            simp only [hmn, if_false, and_false_iff, zero_comp, comp_zero]

end Package

end BreenDeligne

