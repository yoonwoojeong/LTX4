import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.Data.Real.NNReal

#align_import for_mathlib.nnreal_to_nat_colimit

-- todo: minimize imports
-- todo: minimize imports
noncomputable section

open scoped NNReal

open CategoryTheory

namespace CategoryTheory.Limits

variable (ι : ℕ →o ℝ≥0) (hι : ∀ r : ℝ≥0, ∃ n : ℕ, r ≤ ι n)

def findNat (r : ℝ≥0) : ℕ :=
  (hι r).some

theorem findNat_spec (r : ℝ≥0) : r ≤ ι (findNat ι hι r) :=
  (hι r).choose_spec

def natToNnreal : ℕ ⥤ ℝ≥0 where
  obj i := ι i
  map i j h := homOfLE <| ι.Mono h.le

universe v u

variable {C : Type u} [Category.{v} C]

def restrictDiagram (F : AsSmall.{v} ℝ≥0 ⥤ C) : AsSmall.{v} ℕ ⥤ C :=
  (AsSmall.down ⋙ natToNnreal ι ⋙ AsSmall.up) ⋙ F

def restrictCocone {F : AsSmall.{v} ℝ≥0 ⥤ C} (S : Cocone F) : Cocone (restrictDiagram ι F) :=
  S.whisker _

def isColimitRestrictCocone {F : AsSmall.{v} ℝ≥0 ⥤ C} (S : Cocone F) (hS : IsColimit S) :
    IsColimit (restrictCocone ι S)
    where
  desc T :=
    hS.desc
      ⟨T.pt,
        { app := fun r =>
            F.map (AsSmall.up.map <| homOfLE <| findNat_spec ι hι (ULift.down r)) ≫
              T.ι.app (ULift.up (findNat ι hι (ULift.down r)))
          naturality' := by
            intro r s f
            dsimp
            let m := find_nat ι hι (ULift.down r) ⊔ find_nat ι hι (ULift.down s)
            let r' := as_small.up.obj (find_nat ι hι (ULift.down r))
            let s' := as_small.up.obj (find_nat ι hι (ULift.down s))
            let m' := as_small.up.obj m
            let ιr : r' ⟶ m' := as_small.up.map (hom_of_le <| le_sup_left)
            let ιs : s' ⟶ m' := as_small.up.map (hom_of_le <| le_sup_right)
            erw [← T.w ιr]
            erw [← T.w ιs]
            dsimp [restrict_diagram]
            simp only [category.comp_id, ← category.assoc, ← F.map_comp]
            rfl }⟩
  fac := by
    intro W j
    dsimp [restrict_cocone]
    rw [hS.fac]
    dsimp
    let r := (nat_to_nnreal ι).obj (ULift.down j)
    let k := find_nat ι hι r
    let l := ULift.down j ⊔ k
    let k' : AsSmall.{v} ℕ := as_small.up.obj k
    let l' : AsSmall.{v} ℕ := as_small.up.obj l
    let ιk : k' ⟶ l' := as_small.up.map (hom_of_le <| le_sup_right)
    let ιj : j ⟶ l' := as_small.up.map (hom_of_le <| le_sup_left)
    erw [← W.w ιk]
    erw [← W.w ιj]
    dsimp [restrict_diagram]
    simp only [← category.assoc, ← F.map_comp]
    rfl
  uniq := by
    intro W m hm
    apply hS.hom_ext; intro j
    specialize hm (as_small.up.obj (find_nat ι hι (ULift.down j)))
    dsimp [restrict_cocone] at hm 
    rw [hS.fac]
    dsimp
    erw [← hm, ← category.assoc, S.w]

end CategoryTheory.Limits

