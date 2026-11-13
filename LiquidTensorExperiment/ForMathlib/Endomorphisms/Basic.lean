import Mathlib.CategoryTheory.Abelian.Projective
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import LiquidTensorExperiment.ForMathlib.AbelianCategory

#align_import for_mathlib.endomorphisms.basic

noncomputable section

universe v v' u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- `endomorphisms C` is the category whose objects are an object of `C` equipped with an
endomorphism. Morphisms are morphisms between objects which intertwine the endomorphisms. -/
structure Endomorphisms (C : Type u) [Category.{v} C] where
  pt : C
  e : End pt

namespace Endomorphisms

section Category

variable {C : Type u} [Category.{v} C]

@[ext]
protected structure Hom (X Y : Endomorphisms C) where
  f : X.pt ⟶ Y.pt
  comm : X.e ≫ f = f ≫ Y.e

attribute [reassoc, simp] Hom.comm

instance (C : Type u) [Category.{v} C] : Quiver (Endomorphisms C) where Hom X Y := Endomorphisms.Hom X Y

-- Porting note: Lean 3's `ext` saw through `X ⟶ Y`; in Lean 4 the extensionality lemma
-- has to be stated for `X ⟶ Y` explicitly.
@[ext]
theorem hom_ext {X Y : Endomorphisms C} (f g : X ⟶ Y) (h : f.f = g.f) : f = g :=
  Hom.ext _ _ h

theorem f_injective (X Y : Endomorphisms C) :
    Function.Injective (Hom.f : (X ⟶ Y) → (X.pt ⟶ Y.pt)) := by intro f g h; ext; exact h

protected def id (X : Endomorphisms C) : X ⟶ X
    where
  f := 𝟙 _
  comm := by rw [Category.comp_id, Category.id_comp]

protected def comp {X Y Z : Endomorphisms C} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z
    where
  f := f.f ≫ g.f
  comm := by simp only [Hom.comm, Hom.comm_assoc, Category.assoc]

instance (C : Type u) [Category.{v} C] : CategoryStruct (Endomorphisms C)
    where
  id X := X.id
  comp f g := Endomorphisms.comp f g

@[simp]
theorem id_f (X : Endomorphisms C) : Hom.f (𝟙 X) = 𝟙 X.pt :=
  rfl

@[simps]
def endOfE (X : Endomorphisms C) : X ⟶ X :=
  ⟨X.e, rfl⟩

theorem endOfE_comm {X Y : Endomorphisms C} (g : X ⟶ Y) : X.endOfE ≫ g = g ≫ Y.endOfE := by
  ext
  apply Endomorphisms.Hom.comm

@[simp, reassoc]
theorem comp_f {X Y Z : Endomorphisms C} (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.f (f ≫ g) = f.f ≫ g.f :=
  rfl

instance (C : Type u) [Category.{v} C] : Category (Endomorphisms C)
    where
  id_comp f := by ext1; simp only [comp_f, id_f, Category.id_comp]
  comp_id f := by ext1; simp only [comp_f, id_f, Category.comp_id]
  assoc f g h := by ext1; simp only [comp_f, Category.assoc]

theorem congr_f {X Y : Endomorphisms C} (f₁ f₂ : X ⟶ Y) (h : f₁ = f₂) : f₁.f = f₂.f := by rw [h]

@[simp, reassoc]
theorem pow_comm {X Y : Endomorphisms C} (f : X ⟶ Y) (n : ℕ) :
    (X.e ^ n : End X.pt) ≫ f.f = f.f ≫ (Y.e ^ n : End Y.pt) :=
  by
  induction' n with n ih
  · simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
  · simp only [Nat.succ_eq_add_one, pow_succ, End.mul_def, Category.assoc, Hom.comm, reassoc_of% ih]

@[simps]
protected def forget (C : Type u) [Category.{v} C] : Endomorphisms C ⥤ C
    where
  obj X := X.pt
  map f := f.f
  map_id _ := rfl
  map_comp _ _ := rfl

instance forget_faithful : Faithful (Endomorphisms.forget C)
    where map_injective := by intro X Y f g h; ext; exact h

theorem epi_of_epi_f {X Y : Endomorphisms C} (f : X ⟶ Y) [Epi f.f] : Epi f :=
  { left_cancellation := fun g h w => by ext; rw [← cancel_epi f.f, ← comp_f, w, comp_f] }

def mkIso {X Y : Endomorphisms C} (e : X.pt ≅ Y.pt) (h : X.e ≫ e.hom = e.hom ≫ Y.e) : X ≅ Y
    where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by rw [e.comp_inv_eq, Category.assoc, e.eq_inv_comp, h]⟩
  hom_inv_id := by ext; simp only [comp_f, Iso.hom_inv_id, id_f]
  inv_hom_id := by ext; simp only [comp_f, Iso.inv_hom_id, id_f]

end Category

section Limits

variable {C : Type u} [Category.{v} C]

variable {J : Type v'} [SmallCategory J]

@[simps]
def twistCone {K : J ⥤ Endomorphisms C} (S : Cone (K ⋙ Endomorphisms.forget C)) :
    Cone (K ⋙ Endomorphisms.forget C) where
  pt := S.pt
  π :=
    { app := fun j => S.π.app j ≫ (K.obj j).e
      naturality := by
        intro i j f
        dsimp
        simp only [Category.id_comp, Category.assoc, Hom.comm]
        erw [S.w_assoc] }

abbrev coneE {K : J ⥤ Endomorphisms C} (S : Cone (K ⋙ Endomorphisms.forget C)) (hS : IsLimit S) :
    S.pt ⟶ S.pt :=
  @IsLimit.lift J _ C _ (K ⋙ Endomorphisms.forget C) S hS (twistCone S)

@[simps]
protected def cone {K : J ⥤ Endomorphisms C} (S : Cone (K ⋙ Endomorphisms.forget C))
    (hS : IsLimit S) : Cone K
    where
  pt :=
    { pt := S.pt
      e := coneE S hS }
  π :=
    { app := fun j =>
        { f := S.π.app _
          comm := by dsimp; simp }
      naturality := fun i j f => by ext; dsimp; simp; erw [S.w] }

@[simps]
protected def isLimitCone {K : J ⥤ Endomorphisms C} (S : Cone (K ⋙ Endomorphisms.forget C))
    (hS : IsLimit S) : IsLimit (Endomorphisms.cone S hS)
    where
  lift S :=
    { f :=
        hS.lift
          ⟨S.pt.pt,
            { app := fun j => (S.π.app _).f
              naturality := by
                intro i j f
                dsimp
                simp [← comp_f] }⟩
      comm := by apply hS.hom_ext; dsimp; simp }
  fac := by intro s j; ext; dsimp; simp
  uniq := by
    intro s m hm; ext; apply hS.hom_ext
    intro j; specialize hm j; apply_fun fun e => e.f at hm 
    dsimp at *; simp [hm]

protected def coneIso {K : J ⥤ Endomorphisms C} (S : Cone K)
    (hS : IsLimit ((Endomorphisms.forget C).mapCone S)) : Endomorphisms.cone _ hS ≅ S :=
  Cones.ext
    { hom :=
        { f := 𝟙 _
          comm := by apply hS.hom_ext; intro j; dsimp; simp; erw [hS.fac]; dsimp }
      inv :=
        { f := 𝟙 _
          comm := by apply hS.hom_ext; intro j; dsimp; simp; erw [hS.fac]; dsimp }
      hom_inv_id := by ext; dsimp; simp
      inv_hom_id := by ext; dsimp; simp }
    (by
      intro j; ext
      dsimp; simp)

protected def coneIso' {K : J ⥤ Endomorphisms C} (S : Cone (K ⋙ Endomorphisms.forget C))
    (hS : IsLimit S) : (Endomorphisms.forget C).mapCone (Endomorphisms.cone S hS) ≅ S :=
  Cones.ext (Iso.refl _)
    (by
      intro j
      dsimp
      simp)

instance hasLimit (K : J ⥤ Endomorphisms C) [HasLimit (K ⋙ Endomorphisms.forget C)] : HasLimit K :=
  ⟨⟨⟨_, Endomorphisms.isLimitCone _ (limit.isLimit _)⟩⟩⟩

instance hasLimitsOfShape [HasLimitsOfShape J C] : HasLimitsOfShape J (Endomorphisms C) :=
  ⟨fun _ => inferInstance⟩

instance hasLimits [HasLimits C] : HasLimits (Endomorphisms C) :=
  ⟨fun _ _ => inferInstance⟩

instance createsLimit (K : J ⥤ Endomorphisms C) : CreatesLimit K (Endomorphisms.forget _)
    where
  reflects {S} hS := IsLimit.ofIsoLimit (Endomorphisms.isLimitCone _ _) (Endomorphisms.coneIso _ hS)
  lifts S hS :=
    { liftedCone := Endomorphisms.cone _ hS
      validLift := Endomorphisms.coneIso' _ _ }

instance preservesLimit (K : J ⥤ Endomorphisms C) [HasLimit (K ⋙ Endomorphisms.forget C)] :
    PreservesLimit K (Endomorphisms.forget C) :=
  CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit K (Endomorphisms.forget C)

instance preservesLimitsOfShape [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (Endomorphisms.forget C) :=
  ⟨inferInstance⟩

instance preservesLimits [HasLimits C] : PreservesLimits (Endomorphisms.forget C) :=
  ⟨inferInstance⟩

instance [HasFiniteLimits C] : PreservesFiniteLimits (Endomorphisms.forget C) :=
  by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{v}
  intro J hJ1 hJ2; infer_instance

end Limits

section Colimits

variable {C : Type u} [Category.{v} C]

variable {J : Type v} [SmallCategory J]

@[simps]
def twistCocone {K : J ⥤ Endomorphisms C} (S : Cocone (K ⋙ Endomorphisms.forget C)) :
    Cocone (K ⋙ Endomorphisms.forget C) where
  pt := S.pt
  ι :=
    { app := fun j => (K.obj j).e ≫ S.ι.app j
      naturality := by
        intro i j f
        dsimp
        simp only [Category.comp_id, ← Hom.comm_assoc]
        erw [S.w] }

abbrev coconeE {K : J ⥤ Endomorphisms C} (S : Cocone (K ⋙ Endomorphisms.forget C))
    (hS : IsColimit S) : S.pt ⟶ S.pt :=
  @IsColimit.desc J _ C _ (K ⋙ Endomorphisms.forget C) S hS (twistCocone S)

@[simps]
protected def cocone {K : J ⥤ Endomorphisms C} (S : Cocone (K ⋙ Endomorphisms.forget C))
    (hS : IsColimit S) : Cocone K
    where
  pt :=
    { pt := S.pt
      e := coconeE S hS }
  ι :=
    { app := fun j =>
        { f := S.ι.app j
          comm := by dsimp; simp }
      naturality := fun i j f => by ext; dsimp; simp; erw [S.w] }

@[simps]
protected def isColimitCocone {K : J ⥤ Endomorphisms C} (S : Cocone (K ⋙ Endomorphisms.forget C))
    (hS : IsColimit S) : IsColimit (Endomorphisms.cocone S hS)
    where
  desc S :=
    { f :=
        hS.desc
          ⟨S.pt.pt,
            { app := fun j => (S.ι.app j).f
              naturality := by
                intro i j f
                dsimp
                simp [← comp_f] }⟩
      comm := by apply hS.hom_ext; dsimp; simp }
  fac := by intro s j; ext; dsimp; simp
  uniq := by
    intro s m hm; ext; apply hS.hom_ext
    intro j; specialize hm j; apply_fun fun e => e.f at hm 
    dsimp at *; simp [hm]

protected def coconeIso {K : J ⥤ Endomorphisms C} (S : Cocone K)
    (hS : IsColimit ((Endomorphisms.forget C).mapCocone S)) : Endomorphisms.cocone _ hS ≅ S :=
  Cocones.ext
    { hom :=
        { f := 𝟙 _
          comm := by
            apply hS.hom_ext; intro j; dsimp; simp; erw [hS.fac]; dsimp
            -- Porting note: Lean 3's `simp` closed this with `hom.comm`
            exact (S.ι.app j).comm }
      inv :=
        { f := 𝟙 _
          comm := by
            apply hS.hom_ext; intro j; dsimp; simp; erw [hS.fac]; dsimp
            exact ((S.ι.app j).comm).symm }
      hom_inv_id := by ext; dsimp; simp
      inv_hom_id := by ext; dsimp; simp }
    (by
      intro j; ext
      dsimp; simp)

protected def coconeIso' {K : J ⥤ Endomorphisms C} (S : Cocone (K ⋙ Endomorphisms.forget C))
    (hS : IsColimit S) : (Endomorphisms.forget C).mapCocone (Endomorphisms.cocone S hS) ≅ S :=
  Cocones.ext (Iso.refl _)
    (by
      intro j
      dsimp
      simp)

instance hasColimit (K : J ⥤ Endomorphisms C) [HasColimit (K ⋙ Endomorphisms.forget C)] :
    HasColimit K :=
  ⟨⟨⟨_, Endomorphisms.isColimitCocone _ (colimit.isColimit _)⟩⟩⟩

instance hasColimitsOfShape [HasColimitsOfShape J C] : HasColimitsOfShape J (Endomorphisms C) :=
  ⟨fun _ => inferInstance⟩

instance hasColimits [HasColimits C] : HasColimits (Endomorphisms C) :=
  ⟨fun _ _ => inferInstance⟩

instance createsColimit (K : J ⥤ Endomorphisms C) : CreatesColimit K (Endomorphisms.forget _)
    where
  reflects {S} hS :=
    IsColimit.ofIsoColimit (Endomorphisms.isColimitCocone _ _) (Endomorphisms.coconeIso _ hS)
  lifts S hS :=
    { liftedCocone := Endomorphisms.cocone _ hS
      validLift := Endomorphisms.coconeIso' _ _ }

instance preservesColimit (K : J ⥤ Endomorphisms C) [HasColimit (K ⋙ Endomorphisms.forget C)] :
    PreservesColimit K (Endomorphisms.forget C) :=
  CategoryTheory.preservesColimitOfCreatesColimitAndHasColimit K (Endomorphisms.forget C)

instance preservesColimitsOfShape [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (Endomorphisms.forget C) :=
  ⟨inferInstance⟩

instance preservesColimits [HasColimits C] : PreservesColimits (Endomorphisms.forget C) :=
  ⟨inferInstance⟩

instance [HasFiniteColimits C] : PreservesFiniteColimits (Endomorphisms.forget C) :=
  by
  apply preservesFiniteColimitsOfPreservesFiniteColimitsOfSize.{v}
  intro J hJ1 hJ2; infer_instance

end Colimits

section Projectives

variable {C : Type u} [Category.{v} C]

section free

variable [HasCoproductsOfShape (ULift.{v} ℕ) C]

/-- `free X` is ⨁ₙX, the direct sum over the naturals, equipped with the endomorphism
sending `(a : X)` in degree `n` to `a` in degree `n+1`. An alternative way to view `free X`
is `X ⨂_{ℤ} ℤ[T]` with the endomorphism given by multiplication by `T`. -/
@[simps]
def free (X : C) : Endomorphisms C
    where
  pt := ∐ fun i : ULift.{v} ℕ => X
  e := Sigma.desc fun i => Sigma.ι (fun i : ULift.{v} ℕ => X) ⟨i.down + 1⟩

@[reassoc]
theorem free.ι_comp_e (X : C) (i : ULift.{v} ℕ) :
    Sigma.ι (fun i : ULift.{v} ℕ => X) i ≫ (free X).e =
      Sigma.ι (fun i : ULift.{v} ℕ => X) ⟨i.down + 1⟩ :=
  by dsimp; simp only [colimit.ι_desc, Cofan.mk_ι_app]

@[ext]
theorem free.ext {X : C} {A : Endomorphisms C} (f g : free X ⟶ A)
    (w :
      Sigma.ι (fun i : ULift.{v} ℕ => X) ⟨0⟩ ≫ f.f = Sigma.ι (fun i : ULift.{v} ℕ => X) ⟨0⟩ ≫ g.f) :
    f = g := by
  -- Porting note: Lean 3's `ext ⟨⟨i⟩⟩` applied both extensionality lemmas at once.
  ext1; apply Sigma.hom_ext; rintro ⟨i⟩
  induction' i with i ih; · exact w
  apply_fun fun α => α ≫ A.e at ih 
  simp only [Category.assoc, ← Hom.comm, free.ι_comp_e_assoc] at ih 
  exact ih

/-- The map `free T ⟶ A` in `endomorphisms C` induced by a map `T ⟶ A.X` in `C`. Here `A.X`
is the forgetful functor forgetting the endomorphism. -/
@[simps]
def free.desc {X : C} {A : Endomorphisms C} (f : X ⟶ A.pt) : free X ⟶ A
    where
  f := Sigma.desc fun i => f ≫ (A.e ^ i.down : End A.pt)
  comm := by
    apply Sigma.hom_ext; rintro ⟨i⟩; dsimp
    simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, colimit.ι_desc, Category.assoc, pow_succ,
      End.mul_def]

theorem free.desc_comp {X : C} {A B : Endomorphisms C} (f : X ⟶ A.pt) (g : A ⟶ B) :
    free.desc f ≫ g = free.desc (f ≫ g.f) := by
  apply free.ext; dsimp
  simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, colimit.ι_desc, Category.assoc, pow_comm]

def free.map {X Y : C} (f : X ⟶ Y) : free X ⟶ free Y
    where
  f := Sigma.desc fun i => f ≫ Sigma.ι (fun i : ULift.{v} ℕ => Y) i
  comm := by
    apply Sigma.hom_ext; rintro ⟨i⟩
    dsimp
    simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, colimit.ι_desc, Category.assoc]

variable (C)

def Functor.free : C ⥤ Endomorphisms C where
  obj X := Endomorphisms.free X
  map f := Endomorphisms.free.map f
  map_id X := by
    ext; dsimp
    simp only [free.map, Category.id_comp, colimit.ι_desc, Cofan.mk_ι_app, Category.comp_id]
  map_comp f g := by
    ext; dsimp
    simp only [free.map, Category.assoc, colimit.ι_desc, Cofan.mk_ι_app, colimit.ι_desc_assoc]

end free

section Cofree

variable [HasProductsOfShape (ULift.{v} ℕ) C]

/-- `cofree X` is ∏ₙX, the product over the naturals, equipped with the endomorphism
sending `(a : X)` in degree `n` to `a` in degree `n+1`. -/
def cofree (X : C) : Endomorphisms C
    where
  pt := ∏ fun i : ULift.{v} ℕ => X
  e := Pi.lift fun i => Pi.π _ ⟨i.down + 1⟩

def cofree.lift {X : C} {A : Endomorphisms C} (f : A.pt ⟶ X) : A ⟶ cofree X
    where
  f := Pi.lift fun i => (A.e ^ i.down : End A.pt) ≫ f
  comm := by
    dsimp [cofree]
    apply Pi.hom_ext; rintro ⟨j⟩
    simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
    rw [← Category.assoc, pow_succ, ← End.mul_def]; congr 1
    induction' j with j hj
    · simp
    · simp only [End.mul_def, pow_succ] at *
      simp [reassoc_of% hj]

end Cofree

variable [HasProductsOfShape (ULift.{v} ℕ) C] [HasCoproductsOfShape (ULift.{v} ℕ) C]

theorem f_epi {X Y : Endomorphisms C} (f : X ⟶ Y) [Epi f] : Epi f.f :=
  {
    left_cancellation := fun {Z} g h w =>
      by
      let gg : Y ⟶ cofree Z := cofree.lift g
      let hh : Y ⟶ cofree Z := cofree.lift h
      have : f ≫ gg = f ≫ hh := by
        apply hom_ext; apply Pi.hom_ext; rintro ⟨j⟩; dsimp [gg, hh, cofree.lift]; simp
        simp_rw [← Category.assoc, ← pow_comm, Category.assoc, w]
      rw [cancel_epi] at this 
      apply_fun fun e => e.f ≫ Pi.π (fun i : ULift.{v} ℕ => Z) (ULift.up 0) at this 
      dsimp [gg, hh, cofree.lift] at this ; simpa using this }

theorem f_mono {X Y : Endomorphisms C} (f : X ⟶ Y) [Mono f] : Mono f.f :=
  {
    right_cancellation := fun {Z} g h w =>
      by
      let gg : free Z ⟶ X := free.desc g
      let hh : free Z ⟶ X := free.desc h
      have : gg ≫ f = hh ≫ f := by ext; dsimp [gg, hh, free.desc]; simpa
      rw [cancel_mono] at this 
      apply_fun fun e => Sigma.ι (fun i : ULift.{v} ℕ => Z) (ULift.up 0) ≫ e.f at this 
      dsimp [gg, hh, free.desc] at this ; simpa using this }

instance free.projective (X : C) [Projective X] : Projective (free X)
    where
  factors {E Y} f e he := by
    let φ : X ⟶ Y.pt := Sigma.ι (fun i : ULift.{v} ℕ => X) ⟨0⟩ ≫ f.f
    haveI : Epi e.f := f_epi _
    use free.desc (Projective.factorThru φ e.f)
    rw [free.desc_comp, Projective.factorThru_comp]
    apply free.ext; dsimp; simp only [colimit.ι_desc, Cofan.mk_ι_app, pow_zero, End.one_def, Category.comp_id]

def free.presentation [EnoughProjectives C] (A : Endomorphisms C) : ProjectivePresentation A
    where
  p := free (Projective.over A.pt)
  projective := inferInstance
  f := free.desc <| Projective.π _
  epi := by
    suffices Epi (free.desc (Projective.π A.pt)).f by apply epi_of_epi_f
    dsimp
    refine' @epi_of_epi _ _ _ _ _ (Sigma.ι _ _) _ (id _); · exact ⟨0⟩
    simp only [colimit.ι_desc, Cofan.mk_ι_app, pow_zero, End.one_def, Category.comp_id]
    infer_instance

instance [EnoughProjectives C] : EnoughProjectives (Endomorphisms C)
    where presentation A := ⟨free.presentation A⟩

-- generalize to colimits
instance projective_sigma {C ι : Type _} [Category C] (P : ι → C) [HasCoproduct P]
    [∀ i, Projective (P i)] : Projective (∐ P)
    where
  factors := by
    intro E X f e he
    let φ : ∐ P ⟶ E := Sigma.desc fun i => Projective.factorThru (Sigma.ι P i ≫ f) e
    refine' ⟨φ, _⟩
    apply Sigma.hom_ext; intro i
    simp only [φ, colimit.ι_desc_assoc, Cofan.mk_ι_app]
    -- Porting note: the projectivity instance must be given for `P i` explicitly
    exact @Projective.factorThru_comp _ _ (P i) _ _ _ (Sigma.ι P i ≫ f) e _

instance projective_x [EnoughProjectives C] (P : Endomorphisms C) [Projective P] :
    Projective P.pt :=
  ⟨fun {E X} f e he => by
    let F := free.presentation P
    haveI : Projective F.p.pt := Endomorphisms.projective_sigma _
    haveI : Epi F.f := F.epi
    let s : P ⟶ F.p := Projective.factorThru (𝟙 _) F.f
    have hsπ : s ≫ F.f = 𝟙 _ := Projective.factorThru_comp _ _
    let X' : Endomorphisms C := ⟨X, 𝟙 _⟩
    let E' : Endomorphisms C := ⟨E, 𝟙 _⟩
    let e' : E' ⟶ X' := ⟨e, by dsimp only; rw [Category.id_comp, Category.comp_id]⟩
    haveI he' : Epi e' := epi_of_epi_f e'
    let φ : F.p.pt ⟶ E := Projective.factorThru (F.f.f ≫ f) e
    refine' ⟨s.f ≫ φ, _⟩
    rw [Category.assoc, Projective.factorThru_comp, ← comp_f_assoc, hsπ, id_f, Category.id_comp]⟩

end Projectives

section Preadditive

open CategoryTheory.Preadditive

variable {𝓐 : Type u} [Category.{v} 𝓐] [Preadditive 𝓐]

variable (X Y : Endomorphisms 𝓐)

instance : Zero (X ⟶ Y) :=
  ⟨⟨0, by simp only [comp_zero, zero_comp, Hom.comm]⟩⟩

instance : Add (X ⟶ Y) :=
  ⟨fun f g => ⟨f.f + g.f, by simp only [comp_add, add_comp, Hom.comm]⟩⟩

instance : Sub (X ⟶ Y) :=
  ⟨fun f g => ⟨f.f - g.f, by simp only [comp_sub, sub_comp, Hom.comm]⟩⟩

instance : Neg (X ⟶ Y) :=
  ⟨fun f => ⟨-f.f, by simp only [comp_neg, neg_comp, Hom.comm]⟩⟩

instance hasNsmul : SMul ℕ (X ⟶ Y) :=
  ⟨fun n f => ⟨n • f.f, by simp only [comp_nsmul, nsmul_comp, Hom.comm]⟩⟩

instance hasZsmul : SMul ℤ (X ⟶ Y) :=
  ⟨fun n f => ⟨n • f.f, by simp only [comp_zsmul, zsmul_comp, Hom.comm]⟩⟩

instance : AddCommGroup (X ⟶ Y) :=
  (f_injective X Y).addCommGroup (fun f : X ⟶ Y => f.f) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[simp]
theorem zero_f : Hom.f (0 : X ⟶ Y) = 0 :=
  rfl

variable {X Y} (f g : X ⟶ Y)

@[simp]
theorem add_f : (f + g).f = f.f + g.f :=
  rfl

@[simp]
theorem sub_f : (f - g).f = f.f - g.f :=
  rfl

@[simp]
theorem neg_f : (-f).f = -f.f :=
  rfl

@[simp]
theorem nsmul_f (n : ℕ) (f : X ⟶ Y) : (n • f).f = n • f.f :=
  rfl

@[simp]
theorem zsmul_f (n : ℤ) (f : X ⟶ Y) : (n • f).f = n • f.f :=
  rfl

variable (𝓐)

instance : Preadditive (Endomorphisms 𝓐)
    where
  add_comp := by intros; ext; dsimp; rw [add_comp]
  comp_add := by intros; ext; dsimp; rw [comp_add]

instance forget_additive : (Endomorphisms.forget 𝓐).Additive where

instance Functor.free_additive [HasCoproductsOfShape (ULift.{v} ℕ) 𝓐] : (Functor.free 𝓐).Additive :=
  ⟨fun {X Y f g} => by
    apply free.ext
    simp [Functor.free, free.map]⟩

theorem isZero_x {X : Endomorphisms 𝓐} (h : IsZero X) : IsZero X.pt := by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero] at h ⊢; apply_fun fun a => a.f at h ; exact h

end Preadditive

section Abelian

variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐] {X Y : Endomorphisms 𝓐} (f : X ⟶ Y)

@[simps]
protected def kernelObj : Endomorphisms 𝓐
    where
  pt := kernel f.f
  e := kernel.lift _ (kernel.ι _ ≫ X.e) (by simp)

@[simps]
protected def kernelι : Endomorphisms.kernelObj f ⟶ X
    where
  f := kernel.ι _
  comm := by dsimp; simp

protected def kernelFork : KernelFork f :=
  KernelFork.ofι (Endomorphisms.kernelι f) <| by ext; dsimp; simp

@[simp]
protected theorem kernelFork_ι_f : (Endomorphisms.kernelFork f).ι.f = kernel.ι _ :=
  rfl

@[simps]
protected def kernelLift (s : KernelFork f) : s.pt ⟶ Endomorphisms.kernelObj f
    where
  f := kernel.lift _ s.ι.f <| by rw [← comp_f, s.condition, zero_f]
  comm := by apply equalizer.hom_ext; dsimp; simp

@[simps]
protected def isLimitKernelFork : IsLimit (Endomorphisms.kernelFork f) :=
  isLimitAux _ (fun s => Endomorphisms.kernelLift f s) (fun s => by ext; dsimp; simp) fun s m hm =>
    by apply_fun fun e => e.f at hm ; ext1; apply equalizer.hom_ext; dsimp at *; simp [hm]

instance hasKernels : HasKernels (Endomorphisms 𝓐) :=
  ⟨fun f => ⟨⟨⟨Endomorphisms.kernelFork _, Endomorphisms.isLimitKernelFork _⟩⟩⟩⟩

@[simps]
protected def cokernelObj : Endomorphisms 𝓐
    where
  pt := cokernel f.f
  e :=
    cokernel.desc _ (Y.e ≫ cokernel.π _) <| by
      simp only [← reassoc_of% f.comm, cokernel.condition, comp_zero]

@[simps]
protected def cokernelπ : Y ⟶ Endomorphisms.cokernelObj f
    where
  f := cokernel.π _
  comm := by simp

protected def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (Endomorphisms.cokernelπ f) <| by ext; dsimp; simp

@[simp]
protected theorem cokernelCofork_π_f : (Endomorphisms.cokernelCofork f).π.f = cokernel.π _ :=
  rfl

@[simps]
protected def cokernelDesc (s : CokernelCofork f) : Endomorphisms.cokernelObj f ⟶ s.pt
    where
  f := cokernel.desc _ s.π.f <| by rw [← comp_f, s.condition, zero_f]
  comm := by apply coequalizer.hom_ext; dsimp; simp

@[simps]
protected def isColimitCokernelCofork : IsColimit (Endomorphisms.cokernelCofork f) :=
  isColimitAux _ (fun s => Endomorphisms.cokernelDesc f s) (fun s => by ext; dsimp; simp)
    fun s m hm => by
      apply_fun fun e => e.f at hm ; ext1; apply coequalizer.hom_ext; dsimp at *; simp [hm]

instance hasCokernels : HasCokernels (Endomorphisms 𝓐) :=
  ⟨fun f => ⟨⟨⟨Endomorphisms.cokernelCofork _, Endomorphisms.isColimitCokernelCofork _⟩⟩⟩⟩

def kernelForkIso :
    Endomorphisms.kernelFork f ≅
      KernelFork.ofι (Endomorphisms.kernelι f) (Endomorphisms.kernelFork f).condition :=
  Cones.ext (Iso.refl _) (by rintro (_ | _) <;> aesop_cat)

def isLimitForkOfIsLimit (hF : IsLimit (Limits.KernelFork.ofι f.f (cokernel.condition _))) :
    IsLimit (Limits.KernelFork.ofι f (Endomorphisms.cokernelCofork _).condition) :=
  isLimitAux _
    (fun S =>
      { f :=
          hF.lift
            (KernelFork.ofι S.ι.f
              (by
                change _ ≫ (CategoryTheory.Endomorphisms.cokernelCofork _).π.f = _
                erw [← comp_f, S.condition, zero_f]))
        comm := by
          apply hF.hom_ext; rintro (_ | _)
          · dsimp; simp only [Category.assoc, Hom.comm]; erw [hF.fac _ CategoryTheory.Limits.WalkingParallelPair.zero]
            erw [hF.fac_assoc _ CategoryTheory.Limits.WalkingParallelPair.zero]
            dsimp; simp
          · dsimp; simp })
    (by
      intro S
      ext; dsimp; erw [hF.fac _ CategoryTheory.Limits.WalkingParallelPair.zero]; rfl)
    (by
      intro S m hm
      ext; dsimp; apply hF.hom_ext; rintro (_ | _)
      · apply_fun fun e => e.f at hm 
        dsimp at *
        simp only [hm]
        erw [hF.fac _ CategoryTheory.Limits.WalkingParallelPair.zero]; rfl
      · dsimp; simp)

def isColimitCoforkOfIsColimit
    (hF : IsColimit (Limits.CokernelCofork.ofπ f.f (kernel.condition _))) :
    IsColimit (Limits.CokernelCofork.ofπ f (Endomorphisms.kernelFork _).condition) :=
  isColimitAux _
    (fun S =>
      { f :=
          hF.desc
            (CokernelCofork.ofπ S.π.f
              (by
                change (CategoryTheory.Endomorphisms.kernelFork _).ι.f ≫ _ = _
                erw [← comp_f, S.condition, zero_f]))
        comm := by
          apply hF.hom_ext; rintro (_ | _)
          · dsimp; simp
          · dsimp; erw [hF.fac_assoc _ CategoryTheory.Limits.WalkingParallelPair.one]
            rw [← Hom.comm_assoc]
            erw [hF.fac _ CategoryTheory.Limits.WalkingParallelPair.one]
            dsimp; simp })
    (by
      intro S
      ext; dsimp; erw [hF.fac _ CategoryTheory.Limits.WalkingParallelPair.one]; rfl)
    (by
      intro S m hm
      ext; dsimp; apply hF.hom_ext; rintro (_ | _)
      · dsimp; simp
      · apply_fun fun e => e.f at hm 
        dsimp at *
        simp only [hm]
        erw [hF.fac _ CategoryTheory.Limits.WalkingParallelPair.one]; rfl)

instance [HasCoproductsOfShape (ULift.{v} ℕ) 𝓐] [HasProductsOfShape (ULift.{v} ℕ) 𝓐] :
    Abelian (Endomorphisms 𝓐) :=
  {-- WHY IS THIS NEEDED!?
    (_ :
      Preadditive
        (Endomorphisms
          𝓐)) with
    normalMonoOfMono := by
      intro X Y f _
      haveI := f_mono f
      let hE : IsLimit (KernelFork.ofι f.f _) :=
        CategoryTheory.Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
      fconstructor
      exact Endomorphisms.cokernelObj f
      exact Endomorphisms.cokernelπ f
      exact (Endomorphisms.cokernelCofork f).condition
      apply isLimitForkOfIsLimit _ hE
    normalEpiOfEpi := by
      intro X Y f _
      haveI := f_epi f
      let hE : IsColimit (CokernelCofork.ofπ f.f _) :=
        CategoryTheory.Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)
      fconstructor
      exact Endomorphisms.kernelObj f
      exact Endomorphisms.kernelι f
      exact (Endomorphisms.kernelFork f).condition
      apply isColimitCoforkOfIsColimit _ hE
    -- Porting note: mathlib4's `HasFiniteProducts` quantifies over `Fin n` rather than
    -- over all finite types `J`.
    has_finite_products := by
      constructor; intro n
      infer_instance }

end Abelian

end Endomorphisms

end CategoryTheory

