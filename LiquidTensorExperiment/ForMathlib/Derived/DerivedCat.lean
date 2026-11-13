import LiquidTensorExperiment.ForMathlib.Derived.KProjective

#align_import for_mathlib.derived.derived_cat

open CategoryTheory

variable (A : Type _) [Category A] [Abelian A] [EnoughProjectives A]

structure BoundedDerivedCategory where
  val : BoundedHomotopyCategory A
  [proj : HomotopyCategory.IsKProjective val.val]

variable {A}

@[ext]
structure BoundedDerivedCategoryHom (X Y : BoundedDerivedCategory A) where
  val : X.val ⟶ Y.val

namespace BoundedDerivedCategory

instance (X : BoundedDerivedCategory A) : HomotopyCategory.IsKProjective X.val.val :=
  X.proj

@[simps]
instance : Category (BoundedDerivedCategory A)
    where
  Hom X Y := BoundedDerivedCategoryHom X Y
  id X := ⟨𝟙 X.val⟩
  comp X Y Z f g := ⟨f.val ≫ g.val⟩
  id_comp' X Y f := by ext1; apply category.id_comp _
  comp_id' X Y f := by ext1; apply category.comp_id _
  assoc' X Y Z W f g h := by ext1; apply category.assoc _ _ _

variable (A)

def forget : BoundedDerivedCategory A ⥤ BoundedHomotopyCategory A
    where
  obj X := X.val
  map X Y f := f.val

variable {A}

@[simp]
theorem forget_map_mk {X Y : BoundedDerivedCategory A} (f : X.val ⟶ Y.val) :
    (forget A).map { val := f } = f :=
  rfl

instance : Faithful (forget A) where

instance : Full (forget A) where preimage X Y f := ⟨f⟩

variable {A}

@[simps]
def of (X : BoundedHomotopyCategory A) [HomotopyCategory.IsKProjective X.val] :
    BoundedDerivedCategory A where val := X

@[simp]
theorem forget_obj_of {X : BoundedHomotopyCategory A} [HomotopyCategory.IsKProjective X.val] :
    (forget A).obj (of X) = X :=
  rfl

@[simps]
def mkIso {X Y : BoundedDerivedCategory A} (i : (forget A).obj X ≅ (forget A).obj Y) : X ≅ Y
    where
  Hom := ⟨i.Hom⟩
  inv := ⟨i.inv⟩
  hom_inv_id' := by ext1; simp
  inv_hom_id' := by ext1; simp

variable (A)

@[simps]
noncomputable def localizationFunctor : BoundedHomotopyCategory A ⥤ BoundedDerivedCategory A
    where
  obj X := of <| X.replace
  map X Y f := ⟨BoundedHomotopyCategory.lift (X.π ≫ f) Y.π⟩
  map_id' := by
    intro X; symm; ext1; apply BoundedHomotopyCategory.lift_unique
    dsimp; simp only [category.id_comp, category.comp_id]
  map_comp' := by
    intro X Y Z f g
    symm; ext1; apply BoundedHomotopyCategory.lift_unique
    dsimp;
    simp only [category.assoc, BoundedHomotopyCategory.lift_lifts,
      BoundedHomotopyCategory.lift_lifts_assoc]

open HomotopyCategory

theorem isIso_localizationFunctor_map_of_isQuasiIso (X Y : BoundedHomotopyCategory A) (f : X ⟶ Y)
    [IsQuasiIso f] : IsIso ((localizationFunctor _).map f) :=
  by
  use BoundedHomotopyCategory.lift Y.π (X.π ≫ f)
  constructor
  · ext1; dsimp
    apply BoundedHomotopyCategory.lift_ext (X.π ≫ f)
    simp only [category.assoc, BoundedHomotopyCategory.lift_lifts, category.comp_id,
      category.id_comp]
    infer_instance
  · ext1; dsimp
    apply BoundedHomotopyCategory.lift_ext Y.π
    simp only [category.assoc, BoundedHomotopyCategory.lift_lifts, category.comp_id,
      category.id_comp]
    infer_instance

open scoped ZeroObject

open CategoryTheory.Limits

-- MOVE THIS
theorem zeroIsKProjective {X : BoundedHomotopyCategory A} (hX : IsZero X) : IsKProjective X.val :=
  by
  constructor
  intro Y _ f; apply (BoundedHomotopyCategory.zero_val hX).eq_of_src f

protected noncomputable def zero : BoundedDerivedCategory A
    where
  val := BoundedHomotopyCategory.zero
  proj := zeroIsKProjective _ <| BoundedHomotopyCategory.isZero_zero

protected theorem isZero_zero : Limits.IsZero (BoundedDerivedCategory.zero A) :=
  { unique_to := fun Y =>
      Nonempty.intro <|
        Unique.mk ⟨⟨0⟩⟩ fun a => by ext1; cases a;
          apply bounded_homotopy_category.is_zero_zero.eq_of_src
    unique_from := fun Y =>
      Nonempty.intro <|
        Unique.mk ⟨⟨0⟩⟩ fun a => by ext1; cases a;
          apply bounded_homotopy_category.is_zero_zero.eq_of_tgt }

instance hasZeroObject : Limits.HasZeroObject (BoundedDerivedCategory A) :=
  ⟨⟨BoundedDerivedCategory.zero A, BoundedDerivedCategory.isZero_zero A⟩⟩

@[simps]
def hasShiftFunctor (i : ℤ) : BoundedDerivedCategory A ⥤ BoundedDerivedCategory A
    where
  obj X :=
    { val := X.val⟦i⟧
      proj := by dsimp; infer_instance }
  map X Y f := ⟨f.val⟦i⟧'⟩
  map_id' X := by ext1; dsimp; apply CategoryTheory.Functor.map_id
  map_comp' X Y Z f g := by ext1; dsimp; apply CategoryTheory.Functor.map_comp

@[simps]
def hasShiftFunctorForget (m : ℤ) :
    hasShiftFunctor A m ⋙ forget A ≅ forget A ⋙ shiftFunctor (BoundedHomotopyCategory A) m :=
  by
  fapply nat_iso.of_components
  · exact fun X => BoundedHomotopyCategory.mkIso (by rfl)
  · intros
    erw [category.id_comp, category.comp_id]
    rfl

noncomputable instance : HasShift (BoundedDerivedCategory A) ℤ :=
  hasShiftOfFullyFaithful (forget A) (hasShiftFunctor A) (hasShiftFunctorForget A)

@[simp]
theorem shiftFunctor_val (m : ℤ) {X Y : BoundedDerivedCategory A} (f : X ⟶ Y) :
    ((shiftFunctor (BoundedDerivedCategory A) m).map f).val =
      (shiftFunctor (BoundedHomotopyCategory A) m).map f.val :=
  rfl

@[simps]
noncomputable def shiftFunctorForget (m : ℤ) :
    shiftFunctor (BoundedDerivedCategory A) m ⋙ forget A ≅
      forget A ⋙ shiftFunctor (BoundedHomotopyCategory A) m :=
  has_shift_of_fully_faithful_comm (forget A) (shiftFunctor (BoundedDerivedCategory A))
    (hasShiftFunctorForget A) m

@[simps]
noncomputable def shiftFunctorLocalizationFunctor (m : ℤ) :
    shiftFunctor (BoundedHomotopyCategory A) m ⋙ localizationFunctor A ≅
      localizationFunctor A ⋙ shiftFunctor (BoundedDerivedCategory A) m :=
  by
  fapply nat_iso.of_components
  · intros
    apply mk_iso
    refine' _ ≪≫ ((shift_functor_forget A m).app _).symm
    dsimp
    exact
      { Hom :=
          BoundedHomotopyCategory.lift ((shift_functor (BoundedHomotopyCategory A) m).obj X).π
            ((shift_functor (BoundedHomotopyCategory A) m).map X.π)
        inv :=
          BoundedHomotopyCategory.lift ((shift_functor (BoundedHomotopyCategory A) m).map X.π)
            ((shift_functor (BoundedHomotopyCategory A) m).obj X).π }
  · intros; ext; dsimp
    simp only [BoundedHomotopyCategory.lift_comp_lift_self_assoc, CategoryTheory.Category.assoc]
    erw [category.comp_id, category.id_comp]
    simp [BoundedHomotopyCategory.shiftFunctor_map_lift]

-- TODO replace this by pulling back a preadditive instance along `forget`?
@[simps]
instance preadditive : Preadditive (BoundedDerivedCategory A)
    where
  homGroup P Q :=
    { add := fun f g => ⟨f.val + g.val⟩
      add_assoc := by intros; ext; apply add_assoc
      zero := ⟨0⟩
      zero_add := by intros; ext; apply zero_add
      add_zero := by intros; ext; apply add_zero
      nsmul := fun n f => ⟨n • f.val⟩
      nsmul_zero := by intro f; ext; refine' AddCommMonoid.nsmul_zero' f.val
      nsmul_succ := by intro n f; ext; exact AddCommMonoid.nsmul_succ' _ f.val
      neg := fun f => ⟨-f.val⟩
      sub := fun f g => ⟨f.val - g.val⟩
      sub_eq_add_neg := by intros; ext; apply sub_eq_add_neg
      zsmul := fun n f => ⟨n • f.val⟩
      zsmul_zero' := by intro f; ext; apply AddCommGroup.zsmul_zero' f.val
      zsmul_succ' := by intro n f; ext; apply AddCommGroup.zsmul_succ' _ f.val
      zsmul_neg' := by intro n f; ext; apply AddCommGroup.zsmul_neg' _ f.val
      add_left_neg := by intros; ext; apply add_left_neg
      add_comm := by intros; ext; apply add_comm }
  add_comp := by intro P Q R f₁ f₂ g; ext; apply preadditive.add_comp _ _ _ f₁.val f₂.val g.val
  comp_add := by intro P Q R f g₁ g₂; ext; apply preadditive.comp_add _ _ _ f.val g₁.val g₂.val

instance additive (n : ℤ) : (shiftFunctor (BoundedDerivedCategory A) n).Additive
    where map_add' := by
    intro P Q f g
    ext1
    dsimp
    erw [← (shift_functor (BoundedHomotopyCategory A) n).map_add]

variable (A)

@[simps]
noncomputable def forgetTriangulatedFunctorStruct :
    triangulated.pretriangulated.triangulated_functor_struct (BoundedDerivedCategory A)
      (BoundedHomotopyCategory A)
    where
  toFunctor := forget A
  comm_shift := NatIso.ofComponents (fun X => by rfl) (by tidy)

variable {A}

@[simps]
def lift {C : Type _} [Category C] (F : BoundedHomotopyCategory A ⥤ C) :
    BoundedDerivedCategory A ⥤ C where
  obj X := F.obj X.val
  map X Y f := F.map f.val
  map_id' X := F.map_id _
  map_comp' X Y Z f g := F.map_comp _ _

noncomputable def localizeLift {C : Type _} [Category C] (F : BoundedHomotopyCategory A ⥤ C)
    [∀ (X Y : BoundedHomotopyCategory A) (f : X ⟶ Y) [h : IsQuasiIso f], IsIso (F.map f)] :
    localizationFunctor A ⋙ lift F ≅ F :=
  NatIso.ofComponents (fun X => asIso <| F.map X.π)
    (by
      intro X Y f
      dsimp
      simp only [← F.map_comp]
      congr 1
      rw [BoundedHomotopyCategory.lift_lifts])

@[simp, reassoc]
theorem π_lift_id_π (X : BoundedDerivedCategory A) :
    X.val.π ≫ BoundedHomotopyCategory.lift (𝟙 X.val) X.val.π = 𝟙 X.val.replace :=
  by
  refine' BoundedHomotopyCategory.lift_ext X.val.π _ _ _
  rw [category.assoc, BoundedHomotopyCategory.lift_lifts, category.id_comp, category.comp_id]

@[simps]
noncomputable def localizationIso (X : BoundedDerivedCategory A) :
    (localizationFunctor A).obj X.val ≅ X
    where
  Hom := ⟨X.val.π⟩
  inv := ⟨BoundedHomotopyCategory.lift (𝟙 _) X.val.π⟩

noncomputable def liftUnique {C : Type _} [Category C] (F : BoundedHomotopyCategory A ⥤ C)
    [∀ (X Y : BoundedHomotopyCategory A) (f : X ⟶ Y) [h : IsQuasiIso f], IsIso (F.map f)]
    (G : BoundedDerivedCategory A ⥤ C) (e : F ≅ localizationFunctor A ⋙ G) : lift F ≅ G :=
  NatIso.ofComponents (fun X => e.app X.val ≪≫ G.mapIso (localizationIso _))
    (by
      intro X Y f
      simp only [lift_map, iso.trans_hom, iso.app_hom, functor.map_iso_hom,
        nat_trans.naturality_assoc, functor.comp_map, category.assoc,
        nat_iso.cancel_nat_iso_hom_left]
      rw [← functor.map_comp, ← functor.map_comp]
      congr 1
      ext
      simp only [category_theory.category_comp_val, localization_functor_map_val,
        localization_iso_hom_val, BoundedHomotopyCategory.lift_lifts])

open CategoryTheory.Triangulated

variable {A}

@[simps obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
noncomputable def replaceTriangle (S : triangle (BoundedHomotopyCategory A)) :
    triangle (BoundedDerivedCategory A)
    where
  obj₁ := of <| S.obj₁.replace
  obj₂ := of <| S.obj₂.replace
  obj₃ := of <| S.obj₃.replace
  mor₁ := ⟨BoundedHomotopyCategory.lift (S.obj₁.π ≫ S.mor₁) S.obj₂.π⟩
  mor₂ := ⟨BoundedHomotopyCategory.lift (S.obj₂.π ≫ S.mor₂) S.obj₃.π⟩
  mor₃ :=
    haveI : is_quasi_iso ((shift_functor (BoundedHomotopyCategory A) (1 : ℤ)).map S.obj₁.π) := by
      change is_quasi_iso (S.obj₁.π⟦(1 : ℤ)⟧'); · infer_instance
    -- WAT?
    ⟨BoundedHomotopyCategory.lift (S.obj₃.π ≫ S.mor₃) (S.obj₁.π⟦(1 : ℤ)⟧')⟩

@[simps]
noncomputable def replaceTriangleMap {S T : triangle (BoundedHomotopyCategory A)} (f : S ⟶ T) :
    replaceTriangle S ⟶ replaceTriangle T
    where
  hom₁ := ⟨BoundedHomotopyCategory.lift (S.obj₁.π ≫ f.hom₁) T.obj₁.π⟩
  hom₂ := ⟨BoundedHomotopyCategory.lift (S.obj₂.π ≫ f.hom₂) T.obj₂.π⟩
  hom₃ := ⟨BoundedHomotopyCategory.lift (S.obj₃.π ≫ f.hom₃) T.obj₃.π⟩
  comm₁' := by ext; dsimp;
    simp only [triangle_morphism.comm₁, category.assoc, BoundedHomotopyCategory.lift_comp_lift_comp]
  comm₂' := by ext; dsimp;
    simp only [triangle_morphism.comm₂, category.assoc, BoundedHomotopyCategory.lift_comp_lift_comp]
  comm₃' := by
    ext; dsimp
    rw [BoundedHomotopyCategory.shiftFunctor_map_lift, CategoryTheory.Functor.map_comp,
      BoundedHomotopyCategory.lift_comp_lift_comp, BoundedHomotopyCategory.lift_comp_lift_comp,
      category.assoc, triangle_morphism.comm₃, category.assoc]

theorem replaceTriangleMap_id (X : triangle (BoundedHomotopyCategory A)) :
    replaceTriangleMap (𝟙 X) = 𝟙 (replaceTriangle X) := by tidy

theorem replaceTriangleMap_comp {X Y Z : triangle (BoundedHomotopyCategory A)} (f : X ⟶ Y)
    (g : Y ⟶ Z) : replaceTriangleMap (f ≫ g) = replaceTriangleMap f ≫ replaceTriangleMap g := by
  ext <;> tidy

noncomputable def replaceTriangle' :
    triangle (BoundedHomotopyCategory A) ⥤ triangle (BoundedDerivedCategory A)
    where
  obj := replaceTriangle
  map S T f := replaceTriangleMap f
  map_id' := replaceTriangleMap_id
  map_comp' X Y Z f g := replaceTriangleMap_comp f g

attribute [simps obj_obj₁ obj_obj₂ obj_obj₃ obj_mor₁ obj_mor₂ obj_mor₃] replace_triangle'

attribute [simps map_hom₁ map_hom₂ map_hom₃] replace_triangle'

noncomputable def replaceTriangleRotate (S : triangle (BoundedHomotopyCategory A)) :
    (replaceTriangle S).rotate ≅ replaceTriangle S.rotate :=
  by
  fapply triangle.iso.of_components
  exact iso.refl _
  exact iso.refl _
  exact ((shift_functor_localization_functor A 1).app S.obj₁).symm
  · ext; dsimp; simp
  · ext; dsimp; erw [category.id_comp, category.id_comp]; simp
  · ext; dsimp
    simp only [BoundedHomotopyCategory.lift_neg, BoundedHomotopyCategory.lift_comp_lift_comp,
      preadditive.comp_neg, preadditive.neg_comp, neg_inj, category.assoc,
      CategoryTheory.Functor.map_id]
    erw [category.id_comp, category.comp_id]
    simp [BoundedHomotopyCategory.shiftFunctor_map_lift]

@[simps]
noncomputable def forgetReplaceTriangle (S : triangle (BoundedHomotopyCategory A)) :
    (forgetTriangulatedFunctorStruct A).map_triangle.obj (replaceTriangle S) ≅
      BoundedHomotopyCategory.replaceTriangle S :=
  by
  fapply triangle.iso.of_components
  apply iso.refl _
  apply iso.refl _
  apply iso.refl _
  all_goals dsimp; simp

variable (A)

def pretriangulatedDistinguishedTriangles :=
  {T |
    ∃ (S : triangle (BoundedHomotopyCategory A)) (hS : S ∈ (dist_triang BoundedHomotopyCategory A))
      (f : T ≅ replaceTriangle S), True}

variable {A}

theorem isomorphic_distinguished (T₁ : triangle (BoundedDerivedCategory A))
    (m : T₁ ∈ pretriangulatedDistinguishedTriangles A) (T₂ : triangle (BoundedDerivedCategory A))
    (i : T₂ ≅ T₁) : T₂ ∈ pretriangulatedDistinguishedTriangles A :=
  by
  obtain ⟨S₁, hS₁, f₁, hf₁⟩ := m
  exact ⟨S₁, hS₁, i ≪≫ f₁, trivial⟩

theorem forget_replaceTriangle_distinguished (S : triangle (BoundedHomotopyCategory A))
    (m : S ∈ (dist_triang BoundedHomotopyCategory A)) :
    (forgetTriangulatedFunctorStruct A).map_triangle.obj (replaceTriangle S) ∈
      (dist_triang BoundedHomotopyCategory A) :=
  pretriangulated.isomorphic_distinguished _
    (BoundedHomotopyCategory.distinguished_replaceTriangle S m) _ (forgetReplaceTriangle S)

theorem forget_distinguished_of_distinguished {T : triangle (BoundedDerivedCategory A)}
    (m : T ∈ pretriangulatedDistinguishedTriangles A) :
    (forgetTriangulatedFunctorStruct A).map_triangle.obj T ∈
      (dist_triang BoundedHomotopyCategory A) :=
  by
  obtain ⟨S, hS, f, -⟩ := m
  exact
    pretriangulated.isomorphic_distinguished _ (forget_replace_triangle_distinguished _ hS) _
      ((forget_triangulated_functor_struct A).map_triangle.mapIso f)

theorem pretriangulated_contractible_distinguished (X : BoundedDerivedCategory A) :
    contractible_triangle (BoundedDerivedCategory A) X ∈ pretriangulatedDistinguishedTriangles A :=
  by
  refine'
    ⟨contractible_triangle _ X.val, pretriangulated.contractible_distinguished _, ⟨_, trivial⟩⟩
  symm
  fapply triangle.iso.of_components
  exact localization_iso X
  exact localization_iso X
  refine' _ ≪≫ localization_iso 0
  · dsimp
    refine' (localization_functor _).mapIso _
    refine' ⟨0, 0, _, _⟩
    simp only [eq_iff_true_of_subsingleton]
    simp only [zero_comp, autoParam_eq]
    erw [← (forget A).map_id]
    simp only [id_zero, functor.map_zero]
  · ext
    dsimp
    simp only [BoundedHomotopyCategory.lift_lifts]
  · ext
    dsimp
    simp only [BoundedHomotopyCategory.lift_lifts, category.assoc, comp_zero]
  · ext
    dsimp
    simp only [BoundedHomotopyCategory.lift_lifts, comp_zero]

@[simp]
theorem shiftFunctor_map_val (m : ℤ) {X Y : BoundedDerivedCategory A} (f : X ⟶ Y) :
    ((shiftFunctor (BoundedDerivedCategory A) m).map f).val =
      (shiftFunctor (BoundedHomotopyCategory A) m).map f.val :=
  rfl

theorem pretriangulated_distinguished_cocone_triangle {X Y : BoundedDerivedCategory A} (f : X ⟶ Y) :
    ∃ (Z : BoundedDerivedCategory A) (g : Y ⟶ Z) (h :
      Z ⟶ (shiftFunctor (BoundedDerivedCategory A) 1).obj X),
      triangle.mk (BoundedDerivedCategory A) f g h ∈ pretriangulatedDistinguishedTriangles A :=
  by
  obtain ⟨Z, g, h, m⟩ := pretriangulated.distinguished_cocone_triangle _ _ f.val
  use(localization_functor A).obj Z
  use(localization_iso Y).inv ≫ (localization_functor A).map g
  refine' ⟨(localization_functor A).map (h ≫ eq_to_hom (by rfl)) ≫ (localization_iso _).Hom, _⟩
  refine' ⟨_, m, ⟨_, trivial⟩⟩
  symm
  fapply triangle.iso.of_components
  · exact localization_iso _
  · exact localization_iso _
  · exact iso.refl _
  · ext; dsimp; simp only [BoundedHomotopyCategory.lift_lifts]
  · ext; dsimp
    simp only [category.comp_id, BoundedDerivedCategory.π_lift_id_π_assoc]
  · ext; dsimp
    simp only [category.comp_id, category.id_comp, BoundedHomotopyCategory.lift_lifts]

theorem rotate_distinguished_triangle (T : triangle (BoundedDerivedCategory A)) :
    T ∈ pretriangulatedDistinguishedTriangles A ↔
      T.rotate ∈ pretriangulatedDistinguishedTriangles A :=
  by
  constructor
  · rintro ⟨S, hS, f, -⟩
    use S.rotate
    refine' ⟨pretriangulated.rot_of_dist_triangle _ _ hS, _, trivial⟩
    exact (rotate _).mapIso f ≪≫ replace_triangle_rotate _
  · rintro ⟨S, hS, f, -⟩
    use S.inv_rotate
    refine' ⟨pretriangulated.inv_rot_of_dist_triangle _ _ hS, _, trivial⟩
    apply (iso_equiv_of_fully_faithful (rotate (BoundedDerivedCategory A))).invFun
    refine' f ≪≫ _ ≪≫ (replace_triangle_rotate _).symm
    apply replace_triangle'.map_iso
    exact (triangle_rotation _).counitIso.symm.app S

theorem complete_distinguished_triangle_morphism (T₁ T₂ : triangle (BoundedDerivedCategory A))
    (m₁ : T₁ ∈ pretriangulatedDistinguishedTriangles A)
    (m₂ : T₂ ∈ pretriangulatedDistinguishedTriangles A) (a : T₁.obj₁ ⟶ T₂.obj₁)
    (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
        T₁.mor₃ ≫ (shiftFunctor (BoundedDerivedCategory A) 1).map a = c ≫ T₂.mor₃ :=
  by
  -- We work formally, just using the fact this is true in the bounded homotopy category,
  -- without needing to care why.
  obtain ⟨c', h1, h2⟩ :=
    pretriangulated.complete_distinguished_triangle_morphism
      ((forget_triangulated_functor_struct A).map_triangle.obj T₁)
      ((forget_triangulated_functor_struct A).map_triangle.obj T₂)
      (forget_distinguished_of_distinguished m₁) (forget_distinguished_of_distinguished m₂)
      ((forget A).map a) ((forget A).map b) (congr_arg BoundedDerivedCategoryHom.val comm)
  use c'
  dsimp at h1 h2 
  constructor
  · apply (forget A).map_injective
    simpa only [(forget A).map_comp] using h1
  · apply (forget A).map_injective
    simp only [CategoryTheory.Category.comp_id] at h2 
    simp only [(forget A).map_comp]
    exact h2

variable (A)

instance pretriangulated : triangulated.pretriangulated (BoundedDerivedCategory A)
    where
  distinguishedTriangles := pretriangulatedDistinguishedTriangles A
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := pretriangulated_contractible_distinguished
  distinguished_cocone_triangle X Y f := pretriangulated_distinguished_cocone_triangle f
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

variable (A)

noncomputable def ext (n : ℤ) : (BoundedDerivedCategory A)ᵒᵖ ⥤ BoundedDerivedCategory A ⥤ Ab :=
  Functor.flip <| shiftFunctor _ n ⋙ preadditiveYoneda

@[simp]
theorem ext_obj_obj (n : ℤ) (X : (BoundedDerivedCategory A)ᵒᵖ) (Y : BoundedDerivedCategory A) :
    ((ext A n).obj X).obj Y = AddCommGroupCat.of (X.unop ⟶ Y⟦n⟧) :=
  rfl

@[simp]
theorem ext_map_app_apply (n : ℤ) {X Y : (BoundedDerivedCategory A)ᵒᵖ} (f : X ⟶ Y)
    (Z : BoundedDerivedCategory A) (e : ((ext A n).obj X).obj Z) :
    ((ext A n).map f).app Z e = f.unop ≫ e :=
  rfl

@[simp]
theorem ext_obj_map (n : ℤ) (X : (BoundedDerivedCategory A)ᵒᵖ) {Y Z : BoundedDerivedCategory A}
    (f : Y ⟶ Z) (e : ((ext A n).obj X).obj Y) : ((ext A n).obj X).map f e = e ≫ f⟦n⟧' :=
  rfl

end BoundedDerivedCategory

/-
0 → A → B → C → 0

A -f→ B → Cone(f) → A[1]

Canonical Cone(f) → C quasi iso

-/
