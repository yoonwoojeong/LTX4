import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

#align_import for_mathlib.homological_complex_abelian

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe w' w v v' u u'

variable {V : Type u} [Category.{v} V] {J : Type w} [Category.{w'} J]

variable {ι : Type u'} {c : ComplexShape ι}

--move this
theorem congr_f [HasZeroMorphisms V] {X Y : HomologicalComplex V c} {f g : X ⟶ Y} (h : f = g)
    (x : ι) : f.f x = g.f x :=
  congr_arg _ h

section Limits

noncomputable section

variable [HasZeroMorphisms V] (F : J ⥤ HomologicalComplex V c)

@[simps]
def liftOfIsLimitEval (t : Cone F) (h : ∀ i, IsLimit <| (eval V c i).mapCone t) (s : Cone F) :
    s.pt ⟶ t.pt := by
  refine' ⟨fun i => is_limit.lift (h i) ⟨_, _⟩, _⟩
  refine' ⟨fun x => (s.π.app x).f i, _⟩
  · intro x y f; dsimp; rw [category.id_comp, ← comp_f]; congr; exact (cone.w s f).symm
  · intro i j r
    apply (h j).hom_ext
    intro x
    dsimp
    rw [category.assoc, category.assoc]
    erw [← (t.π.app x).comm, (h j).fac _ x, (h i).fac_assoc _ x, (s.π.app x).comm]
    rfl

/-- `eval` jointly reflects (actually creates) limits -/
def isLimitOfIsLimitEval (t : Cone F) (h : ∀ i, IsLimit <| (eval V c i).mapCone t) : IsLimit t
    where
  lift := liftOfIsLimitEval F t h
  fac := by intro s j; ext; dsimp; exact (h x).fac _ j
  uniq := by
    intro s m w; ext; apply (h x).hom_ext
    intro j; dsimp; erw [(h x).fac _ j]; exact congr_f (w j) x

variable [∀ i : ι, HasLimit (F ⋙ eval V c i)]

@[simps]
def limitComplex : HomologicalComplex V c :=
  by
  refine' ⟨fun i => limit (F ⋙ eval V c i), fun i j => limit.lift _ ⟨_, _⟩, _, _⟩
  refine' ⟨fun k => limit.π (F ⋙ eval V c i) k ≫ (F.obj k).d i j, _⟩
  · intro x y f
    dsimp
    rw [category.id_comp, category.assoc, ← hom.comm, ← category.assoc]
    congr 1
    exact (limit.w _ _).symm
  · intro i j r
    ext k
    rw [limit.lift_π, zero_comp]
    dsimp only
    rw [(F.obj k).shape _ _ r, comp_zero]
  · intro i j k r r'; ext; simp

@[simps]
def limitComplexCone : Cone F where
  pt := limitComplex F
  π :=
    { app := fun x => { f := fun i => limit.π (F ⋙ eval V c i) x }
      naturality' := fun X Y f => by ext; dsimp; rw [category.id_comp]; exact (limit.w _ _).symm }

def limitComplexConeIsLimit : IsLimit (limitComplexCone F) :=
  isLimitOfIsLimitEval _ _
    (by
      intro i
      apply (limit.is_limit _).ofIsoLimit
      exact cones.ext (iso.refl _) fun _ => (category.id_comp _).symm)

def evalMapLimitComplexCone (i : ι) :
    (eval V c i).mapCone (limitComplexCone F) ≅ (getLimitCone (F ⋙ eval V c i)).1 :=
  Cones.ext (Iso.refl _) fun j => by dsimp; simpa

instance (i : ι) : PreservesLimit F (eval V c i) :=
  preservesLimitOfPreservesLimitCone (limitComplexConeIsLimit F)
    ((limit.isLimit _).ofIsoLimit (evalMapLimitComplexCone F i).symm)

instance : HasLimit F :=
  ⟨⟨⟨_, limitComplexConeIsLimit F⟩⟩⟩

instance [HasLimitsOfShape J V] : HasLimitsOfShape J (HomologicalComplex V c) where

instance [HasLimitsOfSize.{w', w} V] : HasLimitsOfSize.{w', w} (HomologicalComplex V c) :=
  ⟨⟩

instance [HasLimitsOfShape J V] (i : ι) : PreservesLimitsOfShape J (eval V c i) where

instance [HasLimitsOfSize.{w', w} V] (i : ι) : PreservesLimitsOfSize.{w', w} (eval V c i) where

end Limits

section Colimits

noncomputable section

variable [HasZeroMorphisms V] (F : J ⥤ HomologicalComplex V c)

@[simps]
def descOfIsColimitEval (t : Cocone F) (h : ∀ i, IsColimit <| (eval V c i).mapCocone t)
    (s : Cocone F) : t.pt ⟶ s.pt :=
  by
  refine' ⟨fun i => is_colimit.desc (h i) ⟨_, _⟩, _⟩
  refine' ⟨fun x => (s.ι.app x).f i, _⟩
  · intro x y f; dsimp; rw [category.comp_id, ← comp_f]; congr; exact cocone.w s f
  · intro i j r
    apply (h i).hom_ext
    intro x
    dsimp
    erw [(t.ι.app x).comm_assoc, (h j).fac _ x, (h i).fac_assoc _ x, (s.ι.app x).comm]

/-- `eval` jointly reflects (actually creates) colimits -/
def isColimitOfIsColimitEval (t : Cocone F) (h : ∀ i, IsColimit <| (eval V c i).mapCocone t) :
    IsColimit t where
  desc := descOfIsColimitEval F t h
  fac := by intro s j; ext; dsimp; exact (h x).fac _ j
  uniq := by
    intro s m w; ext; apply (h x).hom_ext
    intro j; dsimp; erw [(h x).fac _ j]; exact congr_f (w j) x

variable [∀ i : ι, HasColimit (F ⋙ eval V c i)]

@[simps]
def colimitComplex : HomologicalComplex V c :=
  by
  refine' ⟨fun i => colimit (F ⋙ eval V c i), fun i j => colimit.desc _ ⟨_, _⟩, _, _⟩
  refine' ⟨fun x => (F.obj x).d i j ≫ colimit.ι (F ⋙ eval V c j) x, _⟩
  · intro x y f
    dsimp
    rw [category.comp_id, hom.comm_assoc]
    congr 1
    exact colimit.w (F ⋙ eval V c j) _
  · intro i j r
    ext x
    rw [colimit.ι_desc, comp_zero]
    dsimp only
    rw [(F.obj x).shape _ _ r, zero_comp]
  · intro i j k r r'; ext; simp

@[simps]
def colimitComplexCocone : Cocone F
    where
  pt := colimitComplex F
  ι :=
    { app := fun x => { f := fun i => colimit.ι (F ⋙ eval V c i) x }
      naturality' := fun X Y f => by ext; dsimp; rw [category.comp_id];
        exact colimit.w (F ⋙ eval V c x) _ }

def colimitComplexCoconeIsColimit : IsColimit (colimitComplexCocone F) :=
  isColimitOfIsColimitEval _ _
    (by
      intro i
      apply (colimit.is_colimit _).ofIsoColimit
      exact cocones.ext (iso.refl _) fun _ => category.comp_id _)

def evalMapColimitComplexCocone (i : ι) :
    (eval V c i).mapCocone (colimitComplexCocone F) ≅ (getColimitCocone (F ⋙ eval V c i)).1 :=
  Cocones.ext (Iso.refl _) fun j => by dsimp; simpa

instance (i : ι) : PreservesColimit F (eval V c i) :=
  preservesColimitOfPreservesColimitCocone (colimitComplexCoconeIsColimit F)
    ((colimit.isColimit _).ofIsoColimit (evalMapColimitComplexCocone F i).symm)

instance : HasColimit F :=
  ⟨⟨⟨_, colimitComplexCoconeIsColimit F⟩⟩⟩

instance [HasColimitsOfShape J V] : HasColimitsOfShape J (HomologicalComplex V c) where

instance [HasColimitsOfSize.{w', w} V] : HasColimitsOfSize.{w', w} (HomologicalComplex V c) where

instance [HasColimitsOfShape J V] (i : ι) : PreservesColimitsOfShape J (eval V c i) where

instance [HasColimitsOfSize.{w', w} V] (i : ι) : PreservesColimitsOfSize.{w', w} (eval V c i) where

end Colimits

section Biproduct

variable [HasZeroMorphisms V] [HasBinaryBiproducts V] {X Y Z : HomologicalComplex V c}

@[simps]
def biproduct (X Y : HomologicalComplex V c) : HomologicalComplex V c
    where
  pt i := X.pt i ⊞ Y.pt i
  d i j := biprod.map (X.d i j) (Y.d i j)
  shape' i j r := by ext <;> simp [X.shape _ _ r, Y.shape _ _ r]

@[simps]
def biproduct.inl : X ⟶ biproduct X Y where f i := biprod.inl

@[simps]
def biproduct.inr : Y ⟶ biproduct X Y where f i := biprod.inr

@[simps]
def biproduct.fst : biproduct X Y ⟶ X where f i := biprod.fst

@[simps]
def biproduct.snd : biproduct X Y ⟶ Y where f i := biprod.snd

@[simps]
def biproduct.lift (f : X ⟶ Y) (g : X ⟶ Z) : X ⟶ biproduct Y Z
    where f i := biprod.lift (f.f i) (g.f i)

@[simps]
def biproduct.desc (f : X ⟶ Z) (g : Y ⟶ Z) : biproduct X Y ⟶ Z
    where f i := biprod.desc (f.f i) (g.f i)

variable (X Y)

@[simps]
def biproductBicone : BinaryBicone X Y
    where
  pt := biproduct X Y
  fst := biproduct.fst
  snd := biproduct.snd
  inl := biproduct.inl
  inr := biproduct.inr

attribute [local tidy] tactic.case_bash

def biproductBiconeIsProd : IsLimit (biproductBicone X Y).toCone
    where
  lift := fun Z : BinaryFan _ _ => biproduct.lift Z.fst Z.snd
  uniq := by intros; delta binary_fan.fst binary_fan.snd; ext <;> simp [← w]

def biproductBiconeIsCoprod : IsColimit (biproductBicone X Y).toCocone
    where
  desc := fun Z : BinaryCofan _ _ => biproduct.desc Z.inl Z.inr
  uniq := by intros; delta binary_cofan.inl binary_cofan.inr; ext <;> simp [← w]

def biproductIsBiprod : BinaryBiproductData X Y
    where
  Bicone := biproductBicone X Y
  IsBilimit := ⟨biproductBiconeIsProd X Y, biproductBiconeIsCoprod X Y⟩

instance : HasBinaryBiproducts (HomologicalComplex V c) :=
  ⟨fun X Y => ⟨⟨biproductIsBiprod X Y⟩⟩⟩

end Biproduct

instance [HasZeroMorphisms V] [HasFiniteProducts V] : HasFiniteProducts (HomologicalComplex V c) :=
  ⟨fun J _ => inferInstance⟩

-- instance [has_zero_morphisms V] [has_kernels V] : has_kernels (homological_complex V c) :=
-- begin
--   constructor,
--   intros X Y f,
--   apply_with homological_complex.category_theory.limits.has_limit { instances := ff },
--   intro i,
--   let : walking_parallel_pair_op_equiv.{v v}.functor ⋙ walking_parallel_pair_op_equiv.inverse ⋙
--     parallel_pair f 0 ⋙ eval V c i ≅ parallel_pair (f.f i) 0 :=
--     nat_iso.of_components (λ i, eq_to_iso $ by cases i; refl)
--       (by { rintros _ _ (_|_|_); dsimp; simp }),
--   have := has_limit_of_iso this.symm,
--   exact @@has_limit_of_equivalence_comp _ _ _
--     (walking_parallel_pair_op_equiv.{v v}.trans walking_parallel_pair_op_equiv.symm) this
-- end
-- instance [has_zero_morphisms V] [has_cokernels V] :
--   has_cokernels (homological_complex V c) :=
-- begin
--   constructor,
--   intros X Y f,
--   apply_with homological_complex.category_theory.limits.has_colimit { instances := ff },
--   intro i,
--   let : walking_parallel_pair_op_equiv.{v v}.functor ⋙ walking_parallel_pair_op_equiv.inverse ⋙
--     parallel_pair f 0 ⋙ eval V c i ≅ parallel_pair (f.f i) 0 :=
--     nat_iso.of_components (λ i, eq_to_iso $ by cases i; refl)
--       (by { rintros _ _ (_|_|_); dsimp; simp }),
--   have := has_colimit_of_iso this,
--   exact @@has_colimit_of_equivalence_comp _ _ _
--     (walking_parallel_pair_op_equiv.{v v}.trans walking_parallel_pair_op_equiv.symm) this
-- end
section Kernel

variable [HasZeroMorphisms V] {X Y : HomologicalComplex V c}

variable (f : X ⟶ Y) [∀ i, HasKernel (f.f i)]

@[simps]
def kernelComplex : HomologicalComplex V c
    where
  pt i := kernel (f.f i)
  d i j := kernel.map _ _ _ _ (f.comm i j)
  shape' := by introv r; ext; simp [X.shape _ _ r]

@[simps]
def kernelComplexι : kernelComplex f ⟶ X where f i := kernel.ι (f.f i)

@[simps]
def kernelComplexFork : KernelFork f :=
  KernelFork.ofι (kernelComplexι f) (by ext; simp)

@[simps]
def kernelComplexLift (s : KernelFork f) : s.pt ⟶ kernelComplex f
    where f i := kernel.lift _ (s.ι.f i) (by rw [← comp_f, kernel_fork.condition]; rfl)

def kernelComplexIsKernel : IsLimit (kernelComplexFork f) :=
  by
  apply is_limit_aux (kernel_complex_fork f) (kernel_complex_lift f)
  · intro s; ext; delta fork.ι; dsimp; simp only [kernel.lift_ι]
  · intro s m h; ext; apply_fun fun f => hom.f f x at h 
    delta fork.ι at h ; dsimp at h ⊢; simp [h, kernel.lift_ι]

instance : HasKernel f :=
  ⟨⟨⟨_, kernelComplexIsKernel f⟩⟩⟩

instance [HasKernels V] : HasKernels (HomologicalComplex V c) where

end Kernel

section Cokernel

variable [HasZeroMorphisms V] {X Y : HomologicalComplex V c}

variable (f : X ⟶ Y) [∀ i, HasCokernel (f.f i)]

@[simps]
def cokernelComplex : HomologicalComplex V c
    where
  pt i := cokernel (f.f i)
  d i j := cokernel.map _ _ _ _ (f.comm i j)
  shape' := by introv r; ext; simp [Y.shape _ _ r]

@[simps]
def cokernelComplexπ : Y ⟶ cokernelComplex f where f i := cokernel.π (f.f i)

@[simps]
def cokernelComplexCofork : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelComplexπ f) (by ext; simp)

@[simps]
def cokernelComplexDesc (s : CokernelCofork f) : cokernelComplex f ⟶ s.pt
    where f i := cokernel.desc _ (s.π.f i) (by rw [← comp_f, cokernel_cofork.condition]; rfl)

def cokernelComplexIsCokernel : IsColimit (cokernelComplexCofork f) :=
  by
  apply is_colimit_aux (cokernel_complex_cofork f) (cokernel_complex_desc f)
  · intro s; ext; delta cofork.π; dsimp; simp only [cokernel.π_desc]
  · intro s m h; ext; apply_fun fun f => hom.f f x at h 
    delta cofork.π at h ; dsimp at h ⊢; simp only [h, cokernel.π_desc]

instance : HasCokernel f :=
  ⟨⟨⟨_, cokernelComplexIsCokernel f⟩⟩⟩

instance [HasCokernels V] : HasCokernels (HomologicalComplex V c) where

end Cokernel

section NormalMono

variable [Abelian V] {X Y Z : HomologicalComplex V c}

variable (f : X ⟶ Y)

def isKernelOfEval (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : ∀ i, IsLimit (KernelFork.ofι (f.f i) (congr_f w i))) : IsLimit (KernelFork.ofι f w) :=
  by
  refine' is_limit.of_iso_limit (kernel_complex_is_kernel g) _
  fapply cones.ext
  fapply hom.iso_of_components
  intro i; exact limit.iso_limit_cone ⟨_, h i⟩
  · intro i j r; dsimp; rw [← iso.comp_inv_eq, category.assoc, ← iso.eq_inv_comp]; ext; simp
  · rintro (_ | _)
    · ext; dsimp; rw [← iso.inv_comp_eq]; simp
    · ext; dsimp; simp [show f.f x ≫ g.f x = _ from congr_f w x]

def isCokernelOfEval (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : ∀ i, IsColimit (CokernelCofork.ofπ (g.f i) (congr_f w i))) :
    IsColimit (CokernelCofork.ofπ g w) :=
  by
  refine' is_colimit.of_iso_colimit (cokernel_complex_is_cokernel f) _
  fapply cocones.ext
  fapply hom.iso_of_components
  intro i; exact colimit.iso_colimit_cocone ⟨_, h i⟩
  · intro i j r; ext; dsimp; simp
  · rintro (_ | _)
    · ext; dsimp; simpa using (congr_arg (fun f => hom.f f x) w).symm
    · ext; dsimp; simp

instance [Mono f] (i : ι) : Mono (f.f i) :=
  by
  change mono ((eval V c i).map f)
  infer_instance

theorem mono_of_eval [∀ i, Mono (f.f i)] : Mono f :=
  by
  constructor
  intro Z g h r
  ext i
  rw [← cancel_mono (f.f i)]
  exact congr_f r i

theorem mono_iff_eval : Mono f ↔ ∀ i, Mono (f.f i) :=
  ⟨fun _ i => inferInstance, fun _ => mono_of_eval f⟩

instance [Epi f] (i : ι) : Epi (f.f i) :=
  by
  change epi ((eval V c i).map f)
  infer_instance

theorem epi_of_eval [∀ i, Epi (f.f i)] : Epi f :=
  by
  constructor
  intro Z g h r
  ext i
  rw [← cancel_epi (f.f i)]
  exact congr_f r i

theorem epi_iff_eval : Epi f ↔ ∀ i, Epi (f.f i) :=
  ⟨fun _ i => inferInstance, fun _ => epi_of_eval f⟩

def normalMono [Mono f] : NormalMono f
    where
  z := cokernelComplex f
  g := cokernelComplexπ f
  w := by ext; simp
  IsLimit := by
    apply is_kernel_of_eval
    intro i
    exact abelian.mono_is_kernel_of_cokernel _ (colimit.is_colimit _)

def normalEpi [Epi f] : NormalEpi f where
  w := kernelComplex f
  g := kernelComplexι f
  w := by ext; simp
  IsColimit := by
    apply is_cokernel_of_eval
    intro i
    exact abelian.epi_is_cokernel_of_kernel _ (limit.is_limit _)

end NormalMono

instance [Abelian V] : Abelian (HomologicalComplex V c)
    where
  normalMonoOfMono _ _ := normalMono
  normalEpiOfEpi _ _ := normalEpi

end HomologicalComplex

