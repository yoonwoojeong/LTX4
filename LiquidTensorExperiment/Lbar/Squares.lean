import LiquidTensorExperiment.ForMathlib.Commsq
import LiquidTensorExperiment.ForMathlib.SnakeLemmaNaturality2
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Pt
import LiquidTensorExperiment.ForMathlib.Bicartesian4
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.FunctorCategory
import LiquidTensorExperiment.SystemOfComplexes.ShiftSubId
import LiquidTensorExperiment.PseudoNormedGroup.SystemOfComplexes2

#align_import Lbar.squares

noncomputable section

universe u

open scoped NNReal

open Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

section Step1

variable {A B C : ℝ≥0ᵒᵖ ⥤ Ab.{u}} (f : A ⟶ B)

variable (ι : ULift.{u} ℕ → ℝ≥0)

def shiftSubId.commsq (hι : Monotone ι) :
    Commsq (shiftSubId A ι hι) (Pi.map fun _ => f.app _) (Pi.map fun _ => f.app _)
      (shiftSubId B ι hι) :=
  Commsq.ofEq
    (by
      simp only [shiftSubId, sub_comp, comp_sub, Category.id_comp, Category.comp_id,
        ShiftSubId.shift]
      congr 1
      apply limit.hom_ext
      intro j
      simp only [limit.lift_map, limit.lift_π, Cones.postcompose_obj_π, NatTrans.comp_app,
        Fan.mk_π_app, Discrete.natTrans_app, Category.assoc, NatTrans.naturality,
        lim_map_π_assoc])

end Step1

section Step2

variable {A B C : ULift.{u} ℕ → Ab.{u}} (f : ∀ k, A k ⟶ B k) (g : ∀ k, B k ⟶ C k)

theorem pi_map_exact (H : ∀ k, Exact (f k) (g k)) : Exact (Pi.map f) (Pi.map g) :=
  by
  simp only [AddCommGroupCat.exact_iff'] at H ⊢
  constructor
  · apply limit.hom_ext; intro j
    simp only [Category.assoc, lim_map_π, Discrete.natTrans_app, lim_map_π_assoc, zero_comp,
      (H j.1).1, comp_zero]
  intro x hx
  rw [AddMonoidHom.mem_ker, Ab.apply_eq_zero] at hx 
  have : ∀ k, Ab.pt (limit.π (Discrete.functor fun k => B k) k x) ≫ g k.1 = 0 :=
    by
    intro k
    suffices Ab.pt x ≫ Pi.map g ≫ pi.π _ k.1 = 0
      by
      cases k
      simpa [lim_map_π, Discrete.natTrans_app, ← Category.assoc, hx, Ab.pt_comp]
    rw [← Category.assoc, hx, zero_comp]
  simp only [← Ab.apply_eq_zero] at this 
  replace := fun k => (H k).2 (this ⟨k⟩)
  choose y hy using this
  refine' ⟨Pi.lift (fun k => Ab.pt (y k)) ⟨1⟩, _⟩
  rw [← CategoryTheory.comp_apply, ← Ab.pt_apply' x]
  congr 1
  apply limit.hom_ext
  rintro ⟨j⟩
  simp only [limit.lift_map, limit.lift_π, Cones.postcompose_obj_π, NatTrans.comp_app,
    Fan.mk_π_app, Discrete.natTrans_app, Ab.pt_comp, hy]

end Step2

section Step3

variable {A B C : ℝ≥0ᵒᵖ ⥤ CochainComplex Ab.{u} ℕ} (f : A ⟶ B) (g : B ⟶ C)

variable (ι : ULift.{u} ℕ → ℝ≥0) (n : ℕ)

def piHHom :
    (∏ fun x => (A.obj (op <| ι x)).homology' n) ⟶ ∏ fun x => (B.obj (op <| ι x)).homology' n :=
  Pi.map fun k => (homology'Functor _ _ _).map <| f.app _

def shiftSubId.δ (H : ∀ c n, ShortExact ((f.app c).f n) ((g.app c).f n)) :
    C ⋙ homology'Functor _ _ n ⟶ A ⋙ homology'Functor _ _ (n + 1)
    where
  app c := HomologicalComplex.δ (f.app _) (g.app _) (H _) _ _ rfl
  naturality c₁ c₂ h := by symm; apply HomologicalComplex.δ_natural

def piδ (H : ∀ c n, ShortExact ((f.app c).f n) ((g.app c).f n)) :
    (∏ fun x => (C.obj (op <| ι x)).homology' n) ⟶
      ∏ fun x => (A.obj (op <| ι x)).homology' (n + 1) :=
  Pi.map fun k => (shiftSubId.δ _ _ _ H).app _

theorem piH_les (H : ∀ c n, ShortExact ((f.app c).f n) ((g.app c).f n)) :
    ExactSeq Ab.{u} [piHHom f ι n, piHHom g ι n, piδ f g ι n H] :=
  by
  apply Exact.cons
  · apply pi_map_exact; intro k
    have := HomologicalComplex.six_term_exactSeq _ _ (H (op <| ι k)) n (n + 1) rfl
    exact this.pair
  apply Exact.exactSeq
  · apply pi_map_exact; intro k
    have := HomologicalComplex.six_term_exactSeq _ _ (H (op <| ι k)) n (n + 1) rfl
    exact (this.drop 1).pair

end Step3

section Step4

variable {A B C : SystemOfComplexes.{u}} (f : A.toAb ⟶ B.toAb) (g : B.toAb ⟶ C.toAb)

variable (n : ℕ) (ι : ULift.{u} ℕ → ℝ≥0) (hι : Monotone ι)

theorem shiftSubId.bicartesian (HA₁ : ShiftSubId.shift (A.toAbH n) ι hι = 0)
    (HA₂ : ShiftSubId.shift (A.toAbH (n + 1)) ι hι = 0)
    (H : ∀ c n, ShortExact ((f.app c).f n) ((g.app c).f n)) :
    (@shiftSubId.commsq (B.toAbH n) (C.toAbH n) (whiskerRight g _) ι hι).Bicartesian :=
  by
  rw [← Commsq.Bicartesian.symm_iff]
  let S1 := (@shiftSubId.commsq (A.to_AbH n) (B.to_AbH n) (whisker_right f _) ι hι).symm
  let S2 := (@shiftSubId.commsq (B.to_AbH n) (C.to_AbH n) (whisker_right g _) ι hι).symm
  let S3 := (@shiftSubId.commsq (C.to_AbH n) (A.to_AbH (n + 1)) (shiftSubId.δ _ _ _ H) ι hι).symm
  apply bicartesian_of_id_of_end_of_end_of_id (piH_les _ _ _ _ _) S1 S2 S3 <;> clear S1 S2 S3
  · rw [shiftSubId, HA₁, zero_sub]; rfl
  · rw [shiftSubId, HA₂, zero_sub]; rfl

end Step4

section Step5

variable {A B A' B' : ℝ≥0ᵒᵖ ⥤ Ab.{u}} (f : A ⟶ B) (f' : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B')

variable (ι : ULift.{u} ℕ → ℝ≥0) (hι : Monotone ι)

theorem shiftSubId.bicartesian_iso (w : f ≫ eB.hom = eA.hom ≫ f')
    (sq : (shiftSubId.commsq f ι hι).Bicartesian) : (shiftSubId.commsq f' ι hι).Bicartesian :=
  by
  let H : _ := _
  apply Commsq.Bicartesian.of_iso _ _ _ _ _ H H _ sq
  · refine' limits.lim.map_iso (Discrete.natIso fun k => eA.app _)
  · refine' limits.lim.map_iso (Discrete.natIso fun k => eB.app _)
  · apply shiftSubId.commsq
  · apply shiftSubId.commsq
  · apply Commsq.ofEq; delta Pi.map
    simp only [Functor.mapIso_hom, ← CategoryTheory.Limits.lim_map, ← CategoryTheory.Functor.map_comp]
    apply limit.hom_ext
    simp only [CategoryTheory.Limits.lim_map, lim_map_π, NatTrans.comp_app, Discrete.natTrans_app,
      Discrete.natIso_hom_app, Iso.app_hom]
    intro; simp only [← NatTrans.comp_app, w]

end Step5

