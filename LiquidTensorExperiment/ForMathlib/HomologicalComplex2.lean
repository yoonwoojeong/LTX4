import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.FunctorCategory
import LiquidTensorExperiment.ForMathlib.HomologyLiftDesc
import LiquidTensorExperiment.ForMathlib.HasHomology
import LiquidTensorExperiment.ForMathlib.ExactFunctor

#align_import for_mathlib.homological_complex2

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

section

variable {ι X 𝒜 : Type _} [Category X] [Category 𝒜] [Preadditive 𝒜] {c : ComplexShape ι}

instance evaluation_additive (x : X) : ((evaluation X 𝒜).obj x).Additive
    where map_add' F G f g := by simp only [evaluation_obj_map, nat_trans.app_add]

@[simps]
def FunctorEval.obj (x : X) : HomologicalComplex (X ⥤ 𝒜) c ⥤ HomologicalComplex 𝒜 c :=
  ((evaluation X 𝒜).obj x).mapHomologicalComplex _

@[simps]
def functorEval : X ⥤ HomologicalComplex (X ⥤ 𝒜) c ⥤ HomologicalComplex 𝒜 c
    where
  obj x := FunctorEval.obj x
  map x y f :=
    { app := fun C =>
        { f := fun i => (C.pt i).map f
          comm' := fun _ _ _ => NatTrans.naturality _ _ }
      naturality' := fun _ _ _ => by ext i; symm; apply nat_trans.naturality }
  map_id' := by intros; ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp' := by intros; ext; dsimp; rw [CategoryTheory.Functor.map_comp]

@[simps]
def EvalFunctor.obj (F : X ⥤ HomologicalComplex 𝒜 c) : HomologicalComplex (X ⥤ 𝒜) c
    where
  pt i := F ⋙ HomologicalComplex.eval _ _ i
  d i j :=
    whiskerLeft _ <|
      { app := fun T => T.d _ _
        naturality' := by intros; dsimp; rw [f.comm] }
  shape' := by intros; ext; apply shape; assumption
  d_comp_d' := by intros; ext; apply d_comp_d

@[simps]
def evalFunctor : (X ⥤ HomologicalComplex 𝒜 c) ⥤ HomologicalComplex (X ⥤ 𝒜) c
    where
  obj F := EvalFunctor.obj F
  map F G η :=
    { f := fun i => whiskerRight η _
      comm' := by intros; ext; dsimp; rw [(η.app _).comm] }
  map_id' := by intros; ext; rfl
  map_comp' := by intros; ext; rfl

def evalFunctorEquiv : X ⥤ HomologicalComplex 𝒜 c ≌ HomologicalComplex (X ⥤ 𝒜) c :=
  Equivalence.mk evalFunctor functorEval.flip
    (NatIso.ofComponents
      (fun F =>
        NatIso.ofComponents
          (fun x =>
            Hom.isoOfComponents (fun i => Iso.refl _)
              (by intros; simp only [iso.refl_hom, category.id_comp, category.comp_id]; rfl))
          (by intros; ext; dsimp; simp only [category.id_comp, category.comp_id]))
      (by intros; ext; dsimp; simp only [category.id_comp, category.comp_id]))
    (NatIso.ofComponents
      (fun T =>
        Hom.isoOfComponents
          (fun i =>
            NatIso.ofComponents (fun x => Iso.refl _)
              (by intros; simp only [iso.refl_hom, category.id_comp, category.comp_id]; rfl))
          (by intros; ext; dsimp; simp only [category.id_comp, category.comp_id]))
      (by intros; ext; dsimp; simp only [category.id_comp, category.comp_id]))

end

universe v u w

variable {ι : Type} {X : Type max u v} {𝒜 : Type w} [Category.{u} X] [Category.{max u v} 𝒜]
  [Abelian 𝒜] {c : ComplexShape ι}

noncomputable section

instance (x : X) : PreservesFiniteLimits ((evaluation X 𝒜).obj x) :=
  ⟨by intro J; intro; intro; apply limits.evaluation_preserves_limits_of_shape⟩

instance (x : X) : PreservesFiniteColimits ((evaluation X 𝒜).obj x) :=
  ⟨by intro J; intro; intro; apply limits.evaluation_preserves_colimits_of_shape⟩

def functorEvalHomologyIso (G : HomologicalComplex (X ⥤ 𝒜) c) (i) :
    G.homology' i ≅ functorEval.flip.obj G ⋙ homology'Functor _ c i :=
  NatIso.ofComponents (fun x => (Functor.homology'FunctorIso ((evaluation X 𝒜).obj x) c i).app G)
    fun x y f => Functor.naturality_homology'FunctorIso_hom_app ((evaluation X 𝒜).map f) G i

def evalFunctorHomologyIso (F : X ⥤ HomologicalComplex 𝒜 c) (i) :
    F ⋙ homology'Functor _ c i ≅ (EvalFunctor.obj F).homology' i :=
  isoWhiskerRight (evalFunctorEquiv.unitIso.app F) (homology'Functor 𝒜 c i) ≪≫
    (functorEvalHomologyIso ((@evalFunctor _ X 𝒜 _ _ _ c).obj F) i).symm

@[simps]
def functorEvalHomologyNatIso (i : ι) :
    homology'Functor (X ⥤ 𝒜) c i ≅
      functorEval.flip ⋙ (whiskeringRight _ _ _).obj (homology'Functor 𝒜 c i) :=
  NatIso.ofComponents (fun G => functorEvalHomologyIso G i) fun G₁ G₂ φ =>
    by
    apply nat_trans.ext
    ext1 x
    dsimp only [functor_eval_homology_iso, nat_iso.of_components]
    simp only [iso.app_hom, nat_trans.comp_app, functor.comp_map]
    exact (((evaluation X 𝒜).obj x).homology'FunctorIso c i).Hom.naturality φ

end HomologicalComplex

