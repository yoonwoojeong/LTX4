import LiquidTensorExperiment.ForMathlib.Derived.Example
import LiquidTensorExperiment.ForMathlib.Derived.Les3

#align_import for_mathlib.derived.les_facts

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated HomotopyCategory Opposite

open BoundedHomotopyCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]

-- move me
instance isBoundedAboveShift {A : CochainComplex C ℤ} [IsBoundedAbove ⟨A⟩] (i : ℤ) :
    IsBoundedAbove { as := A⟦i⟧ } :=
  by
  obtain ⟨a, ha⟩ := IsBoundedAbove.cond ⟨A⟩
  refine' ⟨⟨a - i, _⟩⟩
  intro j hj
  rw [sub_le_iff_le_add] at hj 
  exact ha (j + i) hj

section

-- move me
instance HomologicalComplex.single_additive (i : ℤ) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) i).Additive
    where map_add' X Y f g := by
    ext n; dsimp; by_cases hn : n = i
    · subst n; rw [dif_pos rfl, dif_pos rfl, dif_pos rfl]
      simp only [Preadditive.add_comp, Preadditive.comp_add]
    · rw [dif_neg hn, dif_neg hn, dif_neg hn, add_zero]

-- move me
instance BoundedHomotopyCategory.single_additive (i : ℤ) :
    (BoundedHomotopyCategory.single C i).Additive
    where map_add' X Y f g := by
    delta BoundedHomotopyCategory.single
    dsimp
    rw [Functor.map_add]
    rfl

instance Ext.additive (i : ℤ) :
    (ext i : (BoundedHomotopyCategory C)ᵒᵖ ⥤ BoundedHomotopyCategory C ⥤ Ab).Additive
    where map_add' X Y f g := by
    ext B e
    dsimp [Ext]
    rw [Preadditive.comp_add, lift_add, Preadditive.add_comp]

-- move me
instance ext'.flip_additive (i : ℤ) (B : C) : ((ext' i).flip.obj B).Additive
    where map_add' X Y f g := by
    delta ext'
    dsimp
    rw [Functor.map_add, op_add, Functor.map_add]
    rfl

-- move me
instance ext'.additive (i : ℤ) (A : Cᵒᵖ) : ((ext' i).obj A).Additive
    where map_add' X Y f g := by
    delta ext'
    dsimp
    rw [Functor.map_add, Functor.map_add]

end

theorem isZero_iff_epi_and_isIso {A₁ A₂ A₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (B : C)
    (h : ShortExact f g) :
    (∀ i > 0, IsZero (((ext' i).obj (op A₃)).obj B)) ↔
      Epi (((ext' 0).map f.op).app B) ∧ ∀ i > 0, IsIso (((ext' i).map f.op).app B) :=
  by
  have LES := fun i => h.ext'_five_term_exactSeq B i
  constructor
  · intro H
    constructor
    · have := ((LES 0).drop 1).pair
      refine' this.epi_iff_eq_zero.mpr _
      refine' IsZero.eq_of_tgt _ _ _
      exact H 1 zero_lt_one
    · rintro i (hi : 0 < i)
      apply (LES i).isIso_of_zero_of_zero
      · refine' IsZero.eq_of_src _ _ _
        exact H i hi
      · refine' IsZero.eq_of_tgt _ _ _
        exact H (i + 1) (hi.trans <| lt_add_one _)
  · intro H i hi
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
    refine' CategoryTheory.Limits.isZero_of_exact_zero_zero' _ _ ((LES i).drop 2).pair _ _
    · refine' ((LES i).drop 1).pair.epi_iff_eq_zero.mp _
      rw [gt_iff_lt, Int.lt_add_one_iff] at hi 
      obtain rfl | hi := hi.eq_or_lt
      · exact H.1
      · exact @IsIso.epi_of_iso _ _ _ _ _ (H.2 _ hi)
    · refine' (LES (i + 1)).pair.mono_iff_eq_zero.mp _
      exact @IsIso.mono_of_iso _ _ _ _ _ (H.2 _ hi)

theorem epi_and_isIso_iff_of_isIso {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) (α₁ : X₁ ⟶ Y₁) (α₂ : X₂ ⟶ Y₂) (α₃ : X₃ ⟶ Y₃)
    (sq₁ : f₁ ≫ α₂ = α₁ ≫ g₁) (sq₂ : f₂ ≫ α₃ = α₂ ≫ g₂) (Z : C) (hf : ShortExact f₁ f₂)
    (hg : ShortExact g₁ g₂) (H : ∀ i, IsIso (((ext' i).map α₃.op).app Z)) :
    (Epi (((ext' 0).map α₁.op).app Z) ∧ ∀ i > 0, IsIso (((ext' i).map α₁.op).app Z)) ↔
      Epi (((ext' 0).map α₂.op).app Z) ∧ ∀ i > 0, IsIso (((ext' i).map α₂.op).app Z) :=
  by
  let E : ℤ → Cᵒᵖ ⥤ Ab := fun n => (ext' n).flip.obj Z
  have H1 := fun i => hf.ext'_five_term_exactSeq Z i
  have H2 := fun i => hg.ext'_five_term_exactSeq Z i
  have sq1 : ∀ i, (E i).map α₃.op ≫ (E i).map f₂.op = (E i).map g₂.op ≫ (E i).map α₂.op := by intro;
    simp only [← (E i).map_comp, ← op_comp, sq₂]
  have sq2 : ∀ i, (E i).map α₂.op ≫ (E i).map f₁.op = (E i).map g₁.op ≫ (E i).map α₁.op := by intro;
    simp only [← (E i).map_comp, ← op_comp, sq₁]
  have sq3 : ∀ i, (E i).map α₁.op ≫ ext'δ Z hf i = ext'δ Z hg i ≫ (E (i + 1)).map α₃.op := by
    apply ext'δ_natural f₁ f₂ g₁ g₂ α₁ α₂ α₃ sq₁ sq₂ Z hf hg
  constructor <;> rintro ⟨h1, h2⟩
  · constructor
    · show epi ((E 0).map α₂.op)
      refine'
        Abelian.epi_of_epi_of_epi_of_mono (sq1 0) (sq2 0) (sq3 0) ((H2 0).drop 1).pair
          ((H1 0).drop 0).pair ((H1 0).drop 1).pair _ h1 _
      · exact @IsIso.epi_of_iso _ _ _ _ _ (H 0)
      · exact @IsIso.mono_of_iso _ _ _ _ _ (H 1)
    · rintro i (hi : 0 < i)
      suffices mono ((E i).map α₂.op) ∧ epi ((E i).map α₂.op) by cases' this with aux1 aux2;
        refine' @is_iso_of_mono_of_epi _ _ _ _ _ _ aux1 aux2
      constructor
      · obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
        refine'
          Abelian.mono_of_epi_of_mono_of_mono (sq3 i) (sq1 (i + 1)) (sq2 (i + 1))
            ((H2 i).drop 2).pair ((H2 (i + 1)).drop 0).pair ((H1 i).drop 2).pair _ _ _
        · obtain rfl | hi' := eq_or_ne i 0
          · apply h1
          · refine' @IsIso.epi_of_iso _ _ _ _ _ (h2 _ _)
            rw [Int.lt_add_one_iff] at hi ; refine' lt_of_le_of_ne hi hi'.symm
        · exact @IsIso.mono_of_iso _ _ _ _ _ (H _)
        · exact @IsIso.mono_of_iso _ _ _ _ _ (h2 _ hi)
      · refine'
          Abelian.epi_of_epi_of_epi_of_mono (sq1 i) (sq2 i) (sq3 i) ((H2 i).drop 1).pair
            ((H1 i).drop 0).pair ((H1 i).drop 1).pair _ _ _
        · exact @IsIso.epi_of_iso _ _ _ _ _ (H _)
        · exact @IsIso.epi_of_iso _ _ _ _ _ (h2 _ hi)
        · exact @IsIso.mono_of_iso _ _ _ _ _ (H _)
  · constructor
    · refine'
        Abelian.epi_of_epi_of_epi_of_mono (sq2 0) (sq3 0) (sq1 1) ((H2 0).drop 2).pair
          ((H1 0).drop 1).pair ((H1 0).drop 2).pair h1 _ _
      · exact @IsIso.epi_of_iso _ _ _ _ _ (H 1)
      · exact @IsIso.mono_of_iso _ _ _ _ _ (h2 _ zero_lt_one)
    · intro i hi
      refine'
        Abelian.isIso_of_isIso_of_isIso_of_isIso_of_is_iso' (sq1 i) (sq2 i) (sq3 i)
          (sq1 (i + 1)) (H2 i).pair ((H2 i).drop 1).pair ((H2 i).drop 2).pair (H1 i).pair
          ((H1 i).drop 1).pair ((H1 i).drop 2).pair (H _) (h2 _ hi) (H _)
          (h2 _ (add_pos hi zero_lt_one))

