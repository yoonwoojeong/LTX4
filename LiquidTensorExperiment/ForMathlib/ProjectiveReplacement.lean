import Mathlib.CategoryTheory.Abelian.Projective
import LiquidTensorExperiment.ForMathlib.HomologicalComplexShift
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Homotopy
import LiquidTensorExperiment.ForMathlib.AbelianCategory

#align_import for_mathlib.projective_replacement

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

section ZeroObject

variable {V : Type _} [Category V] [HasZeroMorphisms V]

noncomputable theorem splitEpiOfIsZero {X Y : V} (f : X ⟶ Y) (h : IsZero Y) : SplitEpi f :=
  ⟨0, by simp [is_zero_iff_id_eq_zero.mp h]⟩

theorem epi_of_isZero {X Y : V} (f : X ⟶ Y) (h : IsZero Y) : Epi f :=
  @SplitEpi.epi _ (splitEpiOfIsZero f h)

noncomputable theorem splitMonoOfIsZero {X Y : V} (f : X ⟶ Y) (h : IsZero X) : SplitMono f :=
  ⟨0, by simp [is_zero_iff_id_eq_zero.mp h]⟩

theorem mono_of_isZero_object {X Y : V} (f : X ⟶ Y) (h : IsZero X) : Mono f :=
  @SplitMono.mono _ (splitMonoOfIsZero f h)

theorem isIso_of_isZero {X Y : V} (f : X ⟶ Y) (h₁ : IsZero X) (h₂ : IsZero Y) : IsIso f :=
  by
  use 0
  rw [is_zero_iff_id_eq_zero.mp h₁, is_zero_iff_id_eq_zero.mp h₂]
  constructor <;> simp

end ZeroObject

variable {V : Type _} [Category V] [Abelian V] [EnoughProjectives V] (X : CochainComplex V ℤ)

variable (a : ℤ) (H : ∀ (i) (h : a ≤ i), IsZero (X.pt i))

theorem comp_eqToHom_hEq_iff {C : Type _} [Category C] {X X' Y Y' Y'' : C} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (e : Y = Y'') : HEq (f ≫ eqToHom e) f' ↔ HEq f f' := by subst e;
  erw [category.comp_id]

theorem eqToHom_comp_hEq_iff {C : Type _} [Category C] {X X' Y Y' X'' : C} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (e : X'' = X) : HEq (eqToHom e ≫ f) f' ↔ HEq f f' := by subst e;
  erw [category.id_comp]

theorem hEq_eqToHom_comp_iff {C : Type _} [Category C] {X X' Y Y' X'' : C} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (e : X'' = X') : HEq f (eqToHom e ≫ f') ↔ HEq f f' := by subst e;
  erw [category.id_comp]

theorem hEq_comp_eqToHom_iff {C : Type _} [Category C] {X X' Y Y' Y'' : C} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (e : Y' = Y'') : HEq f (f' ≫ eqToHom e) ↔ HEq f f' := by subst e;
  erw [category.comp_id]

namespace CategoryTheory.Projective

noncomputable def replacementAux : ∀ n : ℕ, Σ f : Arrow V, f.left ⟶ X.pt (a - n)
  | 0 => ⟨⟨0, 0, 0⟩, 0⟩
  | n + 1 =>
    ⟨⟨over
          (pullback (X.d (a - n - 1) (a - n))
            (kernel.ι (replacement_aux n).1.Hom ≫ (replacement_aux n).2)),
        (replacement_aux n).1.left, π _ ≫ pullback.snd ≫ kernel.ι _⟩,
      π _ ≫ pullback.fst ≫ (X.xEqToIso (by norm_num; exact sub_sub _ _ _)).Hom⟩

theorem replacementAux_right_eq (n : ℕ) :
    (replacementAux X a H (n + 1)).1.right = (replacementAux X a H n).1.left := by
  delta replacement_aux; exact rfl

theorem replacementAux_hom_eq (n : ℕ) :
    (replacementAux X a H (n + 1)).1.Hom =
      eqToHom (by delta replacement_aux; exact rfl) ≫
        π
            (pullback (X.d (a - n - 1) (a - n))
              (kernel.ι (replacementAux X a H n).1.Hom ≫ (replacementAux X a H n).2)) ≫
          pullback.snd ≫
            kernel.ι (replacementAux X a H n).1.Hom ≫
              eqToHom (by delta replacement_aux; exact rfl) :=
  by delta replacement_aux; erw [category.id_comp, category.comp_id]; exact rfl

theorem replacementAux_snd_comm (n : ℕ) :
    (replacementAux X a H (n + 1)).1.Hom ≫
        eqToHom (replacementAux_right_eq X a H n) ≫ (replacementAux X a H n).2 =
      (replacementAux X a H (n + 1)).2 ≫ X.d _ _ :=
  by
  rw [replacement_aux_hom_eq]
  simp only [category.id_comp, eq_to_hom_refl, category.assoc, eq_to_hom_trans_assoc]
  delta replacement_aux
  rw [eq_to_hom_refl, category.id_comp, ← pullback.condition]
  erw [category.assoc, category.assoc, HomologicalComplex.xEqToIso_d]

noncomputable def replacement : CochainComplex V ℤ
    where
  pt i := if a < i then 0 else (replacementAux X a H ((a - i).natAbs + 1)).1.right
  d i j :=
    if h₁ : i + 1 = j then
      if h₂ : j > a then 0
      else
        eqToHom
            (by
              rw [if_neg, replacement_aux_right_eq, functor.id_obj]
              subst h₁
              suffices (a - i).natAbs = (a - (i + 1)).natAbs + 1 by rw [this]
              apply Int.ofNat.inj
              norm_num [← Int.abs_eq_natAbs]
              rw [abs_eq_self.mpr _, abs_eq_self.mpr _]
              all_goals linarith) ≫
          (replacementAux X a H ((a - j).natAbs + 1)).fst.Hom ≫ eqToHom (dif_neg h₂).symm
    else 0
  shape' _ _ e := dif_neg e
  d_comp_d' := by
    rintro i j k (rfl : i + 1 = j) (rfl : i + 1 + 1 = k)
    simp only [dif_pos, dif_ctx_congr]
    by_cases h : i + 1 + 1 > a
    · rw [dif_pos h, comp_zero]
    rw [dif_neg h, dif_neg]
    rw [← category.assoc, ← category.assoc, ← is_iso.eq_comp_inv]
    simp only [category.assoc, eq_to_hom_trans_assoc]
    rw [← is_iso.eq_inv_comp, zero_comp, comp_zero, replacement_aux_hom_eq]
    simp only [category.assoc, eq_to_hom_trans_assoc]
    iterate 3 convert comp_zero
    suffices (a - (i + 1)).natAbs = (a - (i + 1 + 1)).natAbs + 1
      by
      convert kernel.condition _ <;> try rw [this]; apply (eqToHom_comp_hEq_iff _ _ _).mpr
      congr <;> rw [this]
    apply Int.ofNat.inj
    norm_num [← Int.abs_eq_natAbs]
    rw [abs_eq_self.mpr _, abs_eq_self.mpr _]
    all_goals linarith

noncomputable def replacement.hom : replacement X a H ⟶ X
    where
  f i :=
    if h : a < i then 0
    else
      eqToHom (if_neg h) ≫
        eqToHom (by rw [replacement_aux_right_eq]) ≫
          (replacementAux X a H (a - i).natAbs).snd ≫
            (X.xEqToIso
                (by
                  rw [← Int.abs_eq_natAbs, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_comm,
                    abs_eq_self]
                  linarith)).Hom
  comm' := by
    rintro i j (rfl : i + 1 = j)
    split_ifs with h'
    · rw [zero_comp, comp_zero]
    · exfalso; linarith
    · rw [comp_zero]; apply (H _ (le_of_lt h)).eq_of_tgt
    · dsimp only [replacement]
      rw [dif_pos rfl, dif_neg h]
      simp only [← category.assoc, eq_to_hom_trans_assoc]
      rw [← is_iso.comp_inv_eq]
      simp only [HomologicalComplex.x_d_eq_to_iso, HomologicalComplex.xEqToIso_inv, category.assoc,
        HomologicalComplex.xEqToIso_d, eq_to_hom_trans, is_iso.iso.inv_hom]
      rw [← is_iso.inv_comp_eq, inv_eq_to_hom, eq_to_hom_trans_assoc]
      refine' Eq.trans _ (replacement_aux_snd_comm X a H _).symm
      suffices (a - (i + 1)).natAbs + 1 = (a - i).natAbs by rw [← heq_iff_eq];
        apply (eqToHom_comp_hEq_iff _ _ _).mpr; rw [this]
      apply Int.ofNat.inj
      norm_num [← Int.abs_eq_natAbs]
      rw [abs_eq_self.mpr _, abs_eq_self.mpr _]
      all_goals linarith

variable {V} {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)

variable {A' B' C' : V} {f' : A' ⟶ B'} {g' : B' ⟶ C'} (w' : f' ≫ g' = 0)

variable (α : Arrow.mk f ⟶ Arrow.mk f') (β : Arrow.mk g ⟶ Arrow.mk g')

variable (p : α.right = β.left)

instance : Epi (homology'.π f g w) := by delta homology'.π; infer_instance

instance : StrongEpi (factorThruImage f) :=
  strongEpi_factorThruImage_of_strongEpiMonoFactorisation <|
    Classical.choice <| HasStrongEpiMonoFactorisations.has_fac f

instance : Epi (factorThruImage f ≫ (imageSubobjectIso f).inv) :=
  epi_comp _ _

instance : Mono (homology'.ι f g w) := by delta homology'.ι; infer_instance

@[simp, reassoc]
theorem π_cokernelIsoOfEq {f₁ f₂ : A ⟶ B} (e : f₁ = f₂) :
    cokernel.π f₁ ≫ (cokernelIsoOfEq e).Hom = cokernel.π f₂ := by subst e;
  erw [has_colimit.iso_of_nat_iso_ι_hom]; exact category.id_comp _

@[simp, reassoc]
theorem Homology.π_iso_cokernel_lift_hom :
    homology'.π f g w ≫ (homology'IsoCokernelLift f g w).Hom =
      (kernelSubobjectIso _).Hom ≫ cokernel.π _ :=
  by
  simp only [limits.cokernel_epi_comp_inv, iso.symm_hom, homology'IsoCokernelLift, iso.trans_hom]
  erw [homology'.π_desc_assoc]
  simp only [cokernel.π_desc_assoc, category.assoc, iso.cancel_iso_hom_left, π_cokernel_iso_of_eq]

@[simp, reassoc]
theorem Homology.π'_ι : homology'.π' f g w ≫ homology'.ι f g w = kernel.ι g ≫ cokernel.π f := by
  delta homology'.π' homology'.ι homology'IsoKernelDesc; simp

@[simp, reassoc]
theorem Homology.π_ι :
    homology'.π f g w ≫ homology'.ι f g w = (kernelSubobject _).arrow ≫ cokernel.π _ := by
  rw [← homology'.π'_eq_π, category.assoc, homology'.π'_ι, kernel_subobject_arrow_assoc]

open scoped Pseudoelement

open CategoryTheory.Abelian

theorem mono_homology'_map_of_pseudoelement
    (H : ∀ (x : B) (y : A') (h₁ : g x = 0) (h₂ : f' y = α.right x), ∃ z : A, f z = x) :
    Mono (homology'.map w w' α β p) :=
  by
  apply pseudoelement.mono_of_zero_of_map_zero
  intro x e
  obtain ⟨x', rfl⟩ := pseudoelement.pseudo_surjective_of_epi (homology'.π f g w) x
  rw [← pseudoelement.comp_apply, homology'.π_map, pseudoelement.comp_apply] at e 
  obtain ⟨y, hy⟩ :=
    (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ (homology'.π f' g' w') (exact_cokernel _)).2
      _ e
  obtain ⟨y', rfl⟩ :=
    pseudoelement.pseudo_surjective_of_epi (factor_thru_image f' ≫ (image_subobject_iso _).inv) y
  obtain ⟨z, e'⟩ :=
    H ((kernel_subobject g).arrow x') y'
      (by rw [← pseudoelement.comp_apply, kernel_subobject_arrow_comp, pseudoelement.zero_apply])
      (by simpa [← pseudoelement.comp_apply, p] using congr_arg (kernel_subobject g').arrow hy)
  have :
    f =
      (factor_thru_image f ≫ (image_subobject_iso _).inv ≫ imageToKernel f g w) ≫
        (kernel_subobject g).arrow :=
    by simp
  rw [this, pseudoelement.comp_apply] at e' 
  have := pseudoelement.pseudo_injective_of_mono _ e'; subst this
  simp [← pseudoelement.comp_apply]

theorem mono_homology'_map_of_epi_pullback_lift
    (H :
      Epi
        (pullback.lift _ _ (show α.left ≫ f' = kernel.lift g f w ≫ kernel.ι _ ≫ α.right by simp))) :
    Mono (homology'.map w w' α β p) :=
  by
  apply mono_homology_map_of_pseudoelement
  intro x y e₁ e₂
  obtain ⟨x', rfl⟩ := (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ exact_kernel_ι).2 x e₁
  rw [← pseudoelement.comp_apply] at e₂ 
  obtain ⟨z, rfl, rfl⟩ := pseudoelement.pseudo_pullback e₂
  obtain ⟨z', rfl⟩ := @pseudoelement.pseudo_surjective_of_epi _ _ _ H z
  use z'
  simp [← pseudoelement.comp_apply]

theorem epi_homology'_map_of_pseudoelement
    (H :
      ∀ (x : B') (h : g' x = 0), ∃ y : B, g y = 0 ∧ (cokernel.π f') (α.right y) = cokernel.π f' x) :
    Epi (homology'.map w w' α β p) :=
  by
  apply pseudoelement.epi_of_pseudo_surjective
  intro x
  obtain ⟨x', rfl⟩ := pseudoelement.pseudo_surjective_of_epi (homology'.π f' g' w') x
  obtain ⟨y, e₁, e₂⟩ :=
    H ((kernel_subobject g').arrow x')
      (by rw [← pseudoelement.comp_apply, kernel_subobject_arrow_comp, pseudoelement.zero_apply])
  obtain ⟨y', rfl⟩ :=
    (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ exact_kernel_subobject_arrow).2 y e₁
  use homology'.π f g w y'
  apply pseudoelement.pseudo_injective_of_mono (homology'.ι f' g' w')
  simpa [← pseudoelement.comp_apply, p] using e₂

attribute [local instance] epi_comp mono_comp

noncomputable def pullbackCompMonoIso {X Y Z Z' : V} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ Z') [Mono h] :
    pullback (f ≫ h) (g ≫ h) ≅ pullback f g :=
  limit.isoLimitCone ⟨_, pullbackIsPullbackOfCompMono f g h⟩

@[simp, reassoc]
theorem pullbackCompMonoIso_fst {X Y Z Z' : V} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ Z') [Mono h] :
    (pullbackCompMonoIso f g h).Hom ≫ pullback.fst = pullback.fst :=
  limit.isoLimitCone_hom_π _ WalkingCospan.left

theorem kernel_ι_replacementAux_eq_zero (i : ℕ) :
    kernel.ι (replacementAux X a H i).fst.Hom ≫
        (replacementAux X a H i).snd ≫ X.d (a - i) (a - i + 1) =
      0 :=
  by
  cases i
  · dsimp [replacement_aux]; simp
  · have : a - i.succ + 1 = a - i := by norm_num [sub_add]
    rw [this, ← replacement_aux_snd_comm, kernel.condition_assoc, zero_comp]

instance replacement_kernel_map_epi (i : ℕ) :
    Epi
      (kernel.lift (X.d (a - i) (a - i + 1))
        (kernel.ι (replacementAux X a H i).fst.Hom ≫ (replacementAux X a H i).snd)
        (by rw [category.assoc, kernel_ι_replacement_aux_eq_zero])) :=
  by
  cases i
  · apply epi_of_isZero
    refine' is_zero_of_mono (kernel.ι _) _
    · apply H; simp
  · apply pseudoelement.epi_of_pseudo_surjective
    intro x
    obtain ⟨y, h₁, h₂⟩ :=
      @pseudoelement.pseudo_pullback _ _ _ _ _ _ _ (X.d (a - i - 1) (a - i))
        (kernel.ι (replacement_aux X a H i).fst.Hom ≫ (replacement_aux X a H i).snd)
        ((X.X_eq_to_iso (by norm_num [sub_sub])).Hom (kernel.ι (X.d _ _) x)) 0 _
    swap
    · simp only [← pseudoelement.comp_apply, category.assoc, HomologicalComplex.xEqToIso_d,
        pseudoelement.apply_zero]
      convert pseudoelement.zero_apply _ _
      have : a - ↑i = a - ↑(i + 1) + 1 := by norm_num [← sub_sub]
      convert kernel.condition _
    obtain ⟨z, rfl⟩ := pseudoelement.pseudo_surjective_of_epi (projective.π _) y
    apply_fun kernel.ι (replacement_aux X a H i).fst.Hom at h₂ 
    simp only [← pseudoelement.comp_apply, category.assoc, pseudoelement.apply_zero] at h₂ 
    obtain ⟨w, rfl⟩ := (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ exact_kernel_ι).2 z h₂
    dsimp [replacement_aux]
    use w
    simp only [← pseudoelement.comp_apply] at h₁ 
    apply
      pseudoelement.pseudo_injective_of_mono
        (kernel.ι (X.d (a - ↑(i + 1)) (a - ↑(i + 1) + 1)) ≫ (HomologicalComplex.xEqToIso X _).Hom)
    refine' Eq.trans _ h₁
    simp only [← pseudoelement.comp_apply, category.assoc]
    congr 1
    refine' (kernel.lift_ι_assoc _ _ _ _).trans _
    simpa
    infer_instance

instance (i : ℕ) : Epi (replacementAux X a H i).snd :=
  by
  cases i <;> dsimp [replacement_aux]
  · apply epi_of_isZero; apply H; simp
  · apply (config := { instances := false }) epi_comp
    · infer_instance
    apply (config := { instances := false }) epi_comp
    swap; · infer_instance
    let e :
      pullback (X.d (a - i - 1) (a - i))
          (kernel.ι (replacement_aux X a H i).fst.Hom ≫ (replacement_aux X a H i).snd) ≅
        pullback (kernel.lift (X.d (a - i) (a - i + 1)) _ _) (kernel.lift _ _ _) :=
      by
      refine'
        pullback.congr_hom (kernel.lift_ι _ _ (X.d_comp_d _ _ _)).symm (kernel.lift_ι _ _ _).symm ≪≫
          pullback_comp_mono_iso _ _ (kernel.ι _)
      rw [category.assoc, kernel_ι_replacement_aux_eq_zero]
    have : e.hom ≫ pullback.fst = pullback.fst := by simp
    refine' (eq_iff_iff.mp (congr_arg epi this)).mp _
    infer_instance

noncomputable def homologyFunctorObjIso (X) (i : ℤ) :
    (homology'Functor V (ComplexShape.up ℤ) i).obj X ≅
      homology' _ _ (X.d_comp_d (i - 1) i (i + 1)) :=
  homology'.mapIso _ _
    (Arrow.isoMk (X.xPrevIso (sub_add_cancel _ _)) (Iso.refl _) (by dsimp; simp [← X.d_to_eq]))
    (Arrow.isoMk (Iso.refl _) (X.xNextIso rfl) (by dsimp; simp)) (by dsimp; simp)

theorem homology'Functor_map_iso {X Y : CochainComplex V ℤ} (f : X ⟶ Y) (i : ℤ) :
    (homology'Functor V (ComplexShape.up ℤ) i).map f =
      (homologyFunctorObjIso X i).Hom ≫
        homology'.map _ _ (Arrow.homMk (f.comm _ _)) (Arrow.homMk (f.comm _ _)) rfl ≫
          (homologyFunctorObjIso Y i).inv :=
  by
  delta homology_functor_obj_iso homology'.mapIso
  simp only [homology'Functor_map, homology'.map_comp]
  congr <;> ext <;> dsimp
  · rw [HomologicalComplex.Hom.prev_eq]
  · simp only [category.comp_id, category.id_comp]
  · simp only [category.comp_id, category.id_comp]
  · rw [HomologicalComplex.Hom.next_eq]

theorem mono_homology'Functor_of_pseudoelement (i : ℤ) {X Y : CochainComplex V ℤ} (f : X ⟶ Y)
    (H :
      ∀ (x : X.pt i) (y : Y.pt (i - 1)),
        X.d i (i + 1) x = 0 → Y.d (i - 1) i y = f.f i x → ∃ z : X.pt (i - 1), X.d (i - 1) i z = x) :
    Mono ((homology'Functor V (ComplexShape.up ℤ) i).map f) :=
  by
  haveI :=
    mono_homology_map_of_pseudoelement _ _ (X.d_comp_d (i - 1) i (i + 1))
      (Y.d_comp_d (i - 1) i (i + 1)) (arrow.hom_mk (f.comm _ _)) (arrow.hom_mk (f.comm _ _)) rfl H
  rw [homology_functor_map_iso]
  infer_instance

attribute [local instance] pseudoelement.setoid

theorem Pseudoelement.id_apply {X : V} (x : X) : @coeFn _ Pseudoelement.homToFun (𝟙 X) x = x :=
  by
  apply Quot.inductionOn x
  intro a
  change ⟦over.mk _⟧ = ⟦a⟧
  erw [category.comp_id]
  rcases a with ⟨_, ⟨⟨⟩⟩, _⟩
  congr

theorem replacementAux_comp_eq_zero (i : ℕ) :
    (replacementAux X a H (i + 1)).fst.Hom ≫
        eqToHom (by dsimp [replacement_aux]; rfl) ≫ (replacementAux X a H i).fst.Hom =
      0 :=
  by
  dsimp [replacement_aux]
  simp only [category.assoc, category.id_comp]
  refine' (category.assoc _ _ _).symm.trans (Eq.trans _ comp_zero)
  pick_goal 3
  congr 1
  exact kernel.condition (replacement_aux X a H i).fst.Hom

noncomputable def replacementHomologyMap (i : ℕ) :
    homology' _ _ ((Category.assoc _ _ _).trans (replacementAux_comp_eq_zero X a H (i + 1))) ⟶
      homology' _ _ (X.d_comp_d (a - (i + 1 : ℕ) - 1) (a - (i + 1 : ℕ)) (a - i)) :=
  by
  refine' homology'.map _ _ _ (arrow.hom_mk (replacement_aux_snd_comm X a H i).symm) _
  · have := (replacement_aux_snd_comm X a H (i + 1)).symm.trans (category.assoc _ _ _).symm
    have hai : a - ↑(i + 2) = a - ↑(i + 1) - 1 := by push_cast; ring
    rw [← X.X_eq_to_iso_d hai, ← category.assoc] at this 
    exact arrow.hom_mk this
  · infer_instance; · rfl

instance (i : ℕ) : Mono (replacementHomologyMap X a H i) :=
  by
  apply mono_homology_map_of_epi_pullback_lift
  dsimp [replacement_aux]
  convert projective.π_epi _
  apply pullback.hom_ext
  ·
    simpa only [category.comp_id, category.assoc, arrow.hom_mk_left, X.X_eq_to_iso_trans,
      X.X_eq_to_iso_refl, pullback.lift_fst]
  · refine' (cancel_mono (kernel.ι _)).mp _
    simp only [category.comp_id, category.assoc, arrow.hom_mk_left, kernel.lift_ι,
      X.X_eq_to_iso_trans, pullback.lift_snd, X.X_eq_to_iso_refl]
    simp_rw [← category.assoc]
    exact category.comp_id _

theorem comp_left_epi_iff {V : Type _} [Category V] {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    Epi (f ≫ g) ↔ Epi g :=
  ⟨fun h => @epi_of_epi _ _ _ h, fun h => @epi_comp _ _ _ _ h⟩

theorem comp_right_epi_iff {V : Type _} [Category V] {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    Epi (f ≫ g) ↔ Epi f :=
  ⟨fun h => by simpa using @epi_comp _ (f ≫ g) h (inv g) _, fun h => @epi_comp _ _ h _ _⟩

instance replacement_kernel_map_epi' (i : ℕ) :
    Epi
      (kernel.lift (X.d (a - (i + 1)) (a - i))
        (kernel.ι (replacementAux X a H (i + 1)).fst.Hom ≫ (replacementAux X a H (i + 1)).snd)
        (by
          rw [category.assoc]
          convert kernel_ι_replacement_aux_eq_zero X a H _ <;> norm_num [sub_add])) :=
  by convert projective.replacement_kernel_map_epi X a H _ <;> norm_num [sub_add]

instance (i : ℕ) : Epi (replacementHomologyMap X a H i) :=
  by
  apply (config := { instances := false }) epi_of_epi (homology'.π _ _ _)
  erw [homology'.π_map]
  apply (config := { instances := false }) epi_comp
  swap; · infer_instance
  rw [← comp_left_epi_iff (kernel_subobject_iso _).inv, ←
    comp_right_epi_iff _ (kernel_subobject_iso _).Hom]
  convert projective.replacement_kernel_map_epi' X a H _ using 1
  refine' (cancel_mono (kernel.ι _)).mp _
  simp only [kernel_subobject_arrow'_assoc, category.assoc, kernel_subobject_map_arrow,
    kernel_subobject_arrow, arrow.hom_mk_left]
  erw [kernel.lift_ι]
  infer_instance

instance (i : ℕ) : IsIso (replacementHomologyMap X a H i) :=
  isIso_of_mono_of_epi _

theorem replacementAux_eq_of_eq (i j : ℕ) (e : i + 1 = j) :
    (replacementAux X a H j).1.right = (replacementAux X a H i).1.left :=
  by
  subst e
  dsimp [replacement_aux]
  rfl

theorem replacementAux_fst_hom_congr (i j : ℕ) (e : i = j) :
    HEq (replacementAux X a H i).1.Hom (replacementAux X a H j).1.Hom := by subst e

theorem replacementAux_snd_congr (i j : ℕ) (e : i = j) :
    HEq (replacementAux X a H i).2 (replacementAux X a H j).2 := by subst e

theorem replacement_homology'_eq (i : ℕ) :
    homology' _ _ ((replacement X a H).d_comp_d (a - ↑(i + 1) - 1) (a - ↑(i + 1)) (a - i)) =
      homology' _ _ (ReplacementHomologyMap._proof_4 X a H i) :=
  by
  dsimp only [replacement]
  have e₁ : a - (↑i + 1) - 1 + 1 = a - (↑i + 1) := by norm_num [sub_add]
  have e₂ : a - (↑i + 1) + 1 = a - ↑i := by norm_num [sub_add]
  have e₃ : ¬a < a - (↑i + 1) - 1 := by simp only [tsub_le_iff_right, not_lt]; linarith
  have e₄ : ¬a - (↑i + 1) > a := by simp only [gt_iff_lt, tsub_le_iff_right, not_lt]; linarith
  have e₅ : ¬a - i > a := by simp only [gt_iff_lt, tsub_le_iff_right, not_lt]; linarith
  have e₆ : (a - (a - (↑i + 1))).natAbs = i + 1 := by rw [← sub_add, sub_self, zero_add];
    exact Int.natAbs_ofNat_core _
  have e₇ : (a - (a - (↑i + 1) - 1)).natAbs = i + 1 + 1 := by
    rw [sub_sub, ← sub_add, sub_self, zero_add]; exact Int.natAbs_ofNat_core _
  have e₈ : (a - (a - i)).natAbs = i := by norm_num
  simp only [Nat.cast_add, Nat.cast_one, sub_add_cancel, eq_self_iff_true, gt_iff_lt, dif_pos,
    not_lt, sub_le_self_iff, Nat.cast_nonneg, dif_neg, eq_to_hom_refl, category.comp_id]
  simp only [dif_pos e₁, dif_pos e₂, dif_neg e₄, dif_neg e₅]
  congr 1
  · erw [if_neg e₃]; apply replacement_aux_eq_of_eq; erw [e₇]
  · erw [if_neg e₄]; apply replacement_aux_eq_of_eq; erw [e₆]
  · erw [if_neg e₅]; · congr; · ext; congr; exact e₈; · exact e₈
  · erw [eqToHom_comp_hEq_iff, comp_eqToHom_hEq_iff, e₆]
  · erw [eqToHom_comp_hEq_iff, comp_eqToHom_hEq_iff, e₈]

theorem replacement_hom_homology'_iso (i : ℕ) :
    homology'.map ((replacement X a H).d_comp_d _ _ _) (X.d_comp_d _ _ _)
        (Arrow.homMk ((replacement.hom X a H).comm _ _))
        (Arrow.homMk ((replacement.hom X a H).comm _ _)) rfl =
      eqToHom (replacement_homology'_eq X a H i) ≫ replacementHomologyMap X a H i :=
  by
  rw [← heq_iff_eq, hEq_eqToHom_comp_iff]
  delta replacement_homology_map
  dsimp [replacement]
  congr 3
  any_goals
    rw [if_neg]; apply replacement_aux_eq_of_eq
    · norm_num [← sub_add]; exact (Int.natAbs_ofNat_core _).symm
    · simp only [gt_iff_lt, tsub_le_iff_right, not_lt]; linarith
  any_goals
    rw [if_neg]; dsimp [replacement_aux]; congr; · ext; congr; norm_num; · norm_num
    · simp only [gt_iff_lt, tsub_le_iff_right, not_lt]; linarith
  any_goals rw [category.comp_id]
  any_goals rw [hEq_eqToHom_comp_iff]
  any_goals delta HomologicalComplex.xEqToIso; erw [hEq_comp_eqToHom_iff]
  any_goals
    dsimp [replacement.hom]
    rw [dif_neg, eqToHom_comp_hEq_iff, eqToHom_comp_hEq_iff]
    erw [comp_eqToHom_hEq_iff]
    · apply replacement_aux_snd_congr
      refine' Eq.trans _ (Int.natAbs_ofNat_core _)
      congr 1
      norm_num [sub_sub, sub_add]
    · simp only [gt_iff_lt, tsub_le_iff_right, not_lt]; linarith
  all_goals
    rw [dif_pos, dif_neg, eqToHom_comp_hEq_iff, comp_eqToHom_hEq_iff]
    apply replacement_aux_fst_hom_congr
    · congr 1
      refine' Eq.trans _ (Int.natAbs_ofNat_core _)
      congr 1
      norm_num [sub_sub, sub_add]
    · simp only [gt_iff_lt, tsub_le_iff_right, not_lt]; linarith
    · norm_num [sub_sub, sub_add]

theorem homology'Functor_map_iso' {X Y : CochainComplex V ℤ} (f : X ⟶ Y) (i j k : ℤ)
    (e₁ : i + 1 = j) (e₂ : j + 1 = k) :
    (homology'Functor V (ComplexShape.up ℤ) j).map f =
      (homologyFunctorObjIso X _).Hom ≫
        (eqToHom <| by have e₁ : i = j - 1 := by simp [← e₁]; substs e₁ e₂) ≫
          homology'.map (X.d_comp_d i j k) (Y.d_comp_d i j k) (Arrow.homMk (f.comm i j))
              (Arrow.homMk (f.comm j k)) rfl ≫
            (eqToHom <| by have e₁ : i = j - 1 := by simp [← e₁]; substs e₁ e₂) ≫
              (homologyFunctorObjIso Y _).inv :=
  by
  have e₁ : i = j - 1 := by simp [← e₁]; substs e₁ e₂
  erw [category.id_comp, category.id_comp]
  rw [homology_functor_map_iso]

theorem homology_isZero_of_bounded (i : ℤ) (e : a ≤ i) :
    IsZero ((homology'Functor V (ComplexShape.up ℤ) i).obj X) :=
  by
  apply is_zero_of_mono (homology'IsoCokernelImageToKernel' _ _ _).Hom
  apply is_zero_of_epi (cokernel.π _)
  apply is_zero_of_mono (kernel.ι _)
  apply H i e
  all_goals infer_instance

theorem replacement_is_projective (i : ℤ) : Projective ((replacement X a H).pt i) :=
  by
  dsimp [replacement]
  split_ifs
  · infer_instance
  · dsimp [replacement_aux]
    induction (a - i).natAbs <;> dsimp [replacement_aux] <;> infer_instance

instance (i : ℤ) : Epi ((replacement.hom X a H).f i) :=
  by
  dsimp [replacement.hom]
  split_ifs
  · apply epi_of_isZero; apply H; exact le_of_lt h
  · infer_instance

theorem replacement_is_bounded : ∀ (i) (h : a ≤ i), IsZero ((replacement X a H).pt i) :=
  by
  intro i h
  dsimp [replacement]
  split_ifs
  · exact is_zero_zero _
  · have : a = i := by linarith; subst this
    rw [sub_self, Int.natAbs_zero]
    dsimp [replacement_aux]
    exact is_zero_zero _

instance : QuasiIso' (replacement.hom X a H) :=
  by
  constructor
  intro i
  rw [← sub_add_cancel i a]
  induction' i - a with i i
  · apply isIso_of_isZero
    exact homology_is_zero_of_bounded _ a (replacement_is_bounded X a H) _ (by simp)
    exact homology_is_zero_of_bounded _ a H _ (by simp)
  · rw [show -[i+1] + a = a - ↑(i + 1) by rw [add_comm]; rfl]
    rw [homology_functor_map_iso' _ (a - ↑(i + 1) - 1) (a - ↑(i + 1)) (a - i)]
    · rw [replacement_hom_homology_iso X a H i]
      infer_instance
    · norm_num
    · norm_num [sub_add]
    infer_instance

@[simps]
def CochainComplex.asNatChainComplex (X : CochainComplex V ℤ) (a : ℤ) : ChainComplex V ℕ
    where
  pt i := X.pt (a - i)
  d i j := X.d _ _
  shape' i j r := by
    refine' X.shape _ _ fun e => r _; dsimp at e ⊢
    apply Int.ofNat.inj; push_cast; linarith
  d_comp_d' i j k _ _ := X.d_comp_d _ _ _

@[simps]
def CochainComplex.toNatChainComplex (a : ℤ) : CochainComplex V ℤ ⥤ ChainComplex V ℕ
    where
  obj X := X.asNatChainComplex a
  map X Y f := { f := fun i => f.f _ }

theorem isZero_iff_iso_zero (X : V) : IsZero X ↔ Nonempty (X ≅ 0) :=
  ⟨fun e => ⟨e.isoZero⟩, fun ⟨e⟩ => isZero_of_iso_of_zero (isZero_zero _) e.symm⟩

theorem Preadditive.exact_iff_homology'_isZero {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Exact f g ↔ ∃ w, IsZero (homology' f g w) :=
  by
  rw [preadditive.exact_iff_homology_zero]
  simp_rw [is_zero_iff_iso_zero]

noncomputable def nullHomotopicOfProjectiveToAcyclicAux {X Y : CochainComplex V ℤ} (f : X ⟶ Y)
    (a : ℤ) (h₁ : ∀ i, Projective (X.pt i)) (h₂ : ∀ i, a ≤ i → IsZero (X.pt i))
    (h₃ : ∀ i, IsZero ((homology'Functor _ _ i).obj Y)) :
    Homotopy ((CochainComplex.toNatChainComplex a).map f) 0 :=
  by
  have h₄ : ∀ i, a ≤ i → f.f i = 0 := by intro i e; apply (h₂ i e).eq_of_src
  fapply Homotopy.mkInductive _ 0
  · dsimp; rw [zero_comp]; apply h₄; push_cast; linarith
  all_goals dsimp
  · have := f.comm (a - (0 + 1)) a
    rw [h₄ _ (le_of_eq rfl), comp_zero] at this 
    refine' projective.factor_thru (kernel.lift _ _ this) _
    exact kernel.lift _ _ (Y.d_comp_d _ _ _)
    · apply (config := { instances := false }) kernel.lift.epi
      rw [preadditive.exact_iff_homology_is_zero]
      refine'
        ⟨Y.d_comp_d _ _ _, is_zero_of_iso_of_zero (h₃ (a - (0 + 1))) (homology_iso _ _ _ _ _ _)⟩
      all_goals dsimp; abel
  · rw [comp_zero]; conv_rhs => rw [zero_add]
    slice_rhs 2 3 => erw [← kernel.lift_ι _ _ (Y.d_comp_d (a - (0 + 1 + 1)) (a - (0 + 1)) a)]
    erw [← category.assoc, projective.factor_thru_comp, kernel.lift_ι]; rfl
  · rintro n ⟨g₁, g₂, e⟩; dsimp only
    have :
      X.d (a - (n + 1 + 1)) (a - (n + 1)) ≫
          (f.f (a - (↑n + 1)) - g₂ ≫ Y.d (a - (↑n + 1 + 1)) (a - (↑n + 1))) =
        0 :=
      by rw [← sub_eq_iff_eq_add] at e ; erw [e, X.d_comp_d_assoc, zero_comp]
    rw [preadditive.comp_sub, ← f.comm, ← category.assoc, ← preadditive.sub_comp] at this 
    fconstructor
    · refine' projective.factor_thru (kernel.lift _ _ this) _
      exact kernel.lift _ _ (Y.d_comp_d _ _ _)
      apply (config := { instances := false }) kernel.lift.epi
      rw [preadditive.exact_iff_homology_is_zero]
      refine' ⟨Y.d_comp_d _ _ _, is_zero_of_iso_of_zero (h₃ _) (homology_iso _ _ _ _ _ _)⟩
      all_goals dsimp; push_cast; abel
    · rw [← sub_eq_iff_eq_add']
      slice_rhs 2 3 =>
        erw [← kernel.lift_ι (Y.d (a - (n + 1 + 1)) (a - (n + 1))) _ (Y.d_comp_d _ _ _)]
      erw [← category.assoc, projective.factor_thru_comp, kernel.lift_ι]; rfl

noncomputable def nullHomotopicOfProjectiveToAcyclic {X Y : CochainComplex V ℤ} (f : X ⟶ Y) (a : ℤ)
    (h₁ : ∀ i, Projective (X.pt i)) (h₂ : ∀ i, a ≤ i → IsZero (X.pt i))
    (h₃ : ∀ i, IsZero ((homology'Functor _ _ i).obj Y)) : Homotopy f 0
    where
  Hom i j :=
    if h : i ≤ a ∧ j ≤ a then
      by
      refine'
        (X.X_eq_to_iso _).Hom ≫
          (null_homotopic_of_projective_to_acyclic_aux f a h₁ h₂ h₃).Hom (a - i).natAbs
              (a - j).natAbs ≫
            (Y.X_eq_to_iso _).Hom
      swap; symm
      all_goals
        rw [← Int.abs_eq_natAbs, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', abs_eq_self]
        cases h; rwa [sub_nonneg]
    else 0
  zero' := by
    intro i j e
    split_ifs
    · cases h
      rw [(null_homotopic_of_projective_to_acyclic_aux f a h₁ h₂ h₃).zero, zero_comp, comp_zero]
      intro e'; apply e
      dsimp at e' ⊢
      apply_fun (coe : ℕ → ℤ) at e' 
      rw [Int.ofNat_add, ← Int.abs_eq_natAbs, ← Int.abs_eq_natAbs, abs_eq_self.mpr _,
        abs_eq_self.mpr _, Int.ofNat_one, sub_add, sub_right_inj] at e' 
      rw [← e', sub_add_cancel]
      all_goals rwa [sub_nonneg]
    · rfl
  comm := by
    intro i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel _ _)]
    have e₁ : i + 1 ≤ a ∧ i ≤ a ↔ i + 1 ≤ a := by rw [and_iff_left_iff_imp]; intro e; linarith
    have e₂ : i ≤ a ∧ i ≤ a + 1 ↔ i ≤ a := by rw [and_iff_left_iff_imp]; intro e; linarith
    simp only [tsub_le_iff_right, HomologicalComplex.zero_f_apply, add_zero, e₁, e₂]
    by_cases H₁ : a ≤ i; · apply (h₂ _ H₁).eq_of_src
    replace H₁ : i + 1 ≤ a; · linarith only [H₁]
    have H₂ : i ≤ a := by linarith only [H₁]
    rw [dif_pos H₁, dif_pos H₂]
    have e : a - (a - i).natAbs = i :=
      by
      rw [← Int.abs_eq_natAbs, abs_eq_self.mpr _, ← sub_add, sub_self, zero_add]
      rwa [sub_nonneg]
    rw [← cancel_mono (Y.X_eq_to_iso e.symm).Hom, ← cancel_epi (X.X_eq_to_iso e).Hom]
    have := (null_homotopic_of_projective_to_acyclic_aux f a h₁ h₂ h₃).comm (a - i).natAbs
    dsimp [fromNext, toPrev] at this ⊢
    simp only [HomologicalComplex.x_d_eq_to_iso_assoc, category.comp_id, add_zero,
      HomologicalComplex.x_d_eq_to_iso, category.id_comp, HomologicalComplex.xEqToIso_d_assoc,
      HomologicalComplex.xEqToIso_trans_assoc, preadditive.comp_add, category.assoc,
      HomologicalComplex.xEqToIso_d, HomologicalComplex.xEqToIso_trans,
      HomologicalComplex.xEqToIso_f_assoc, HomologicalComplex.xEqToIso_refl,
      preadditive.add_comp] at this ⊢
    rw [this]; clear this
    delta HomologicalComplex.dFrom HomologicalComplex.dTo CochainComplex.asNatChainComplex
    dsimp only
    have aux₁ : (ComplexShape.down ℕ).next (a - i).natAbs = (a - (i + 1)).natAbs :=
      by
      apply ComplexShape.next_eq'
      show (a - (i + 1)).natAbs + 1 = (a - i).natAbs
      zify
      rw [← Int.abs_eq_natAbs, abs_eq_self.mpr _, ← Int.abs_eq_natAbs, abs_eq_self.mpr _]
      · ring
      all_goals linarith only [H₁, H₂]
    have aux₂ : (ComplexShape.down ℕ).prev (a - i).natAbs = (a - (i - 1)).natAbs :=
      by
      apply ComplexShape.prev_eq'
      show (a - i).natAbs + 1 = (a - (i - 1)).natAbs
      zify
      rw [← Int.abs_eq_natAbs, abs_eq_self.mpr _, ← Int.abs_eq_natAbs, abs_eq_self.mpr _]
      · ring
      all_goals linarith only [H₁, H₂]
    rw [← aux₁, ← aux₂]

end CategoryTheory.Projective

