import LiquidTensorExperiment.ForMathlib.Ab4
import LiquidTensorExperiment.ForMathlib.AddCommGroup

#align_import for_mathlib.AddCommGroup.ab4

open CategoryTheory

open CategoryTheory.Limits

namespace AddCommGroupCat

universe u

theorem injective_of_mono' {X Y : Ab.{u}} (f : X ⟶ Y) [Mono f] : Function.Injective f := by
  rwa [← AddCommGroupCat.mono_iff_injective]

open scoped Classical

noncomputable def cofan {α : Type u} (X : α → Ab.{u}) : Cofan X :=
  Cofan.mk (AddCommGroupCat.of <| Π₀ x, X x) fun a => DFinsupp.singleAddHom (fun x => X x) a

noncomputable def isColimitCofan {α : Type u} (X : α → Ab.{u}) : IsColimit (cofan X)
    where
  desc S :=
    DFinsupp.liftAddHom fun i =>
      let e : X i ⟶ S.pt := S.ι.app ⟨i⟩
      e
  fac S j := by
    cases j
    dsimp [cofan]; ext t
    simp only [comp_apply, DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single]
  uniq := by
    intro S m hm
    apply_fun dfinsupp.liftAddHom.symm
    swap; infer_instance
    dsimp
    erw [AddEquiv.symm_apply_apply]; ext1 a
    simp_rw [← hm]
    ext
    dsimp [cofan]
    simp only [comp_apply, DFinsupp.singleAddHom_apply]

instance aB4 : AB4 AddCommGroupCat.{u} := by
  constructor
  intro α X Y f hf
  let t := _; change mono t
  let eX : (∐ fun a : α => X a) ≅ (cofan X).pt :=
    (colimit.isColimit _).coconePointUniqueUpToIso (is_colimit_cofan X)
  let eY : (∐ fun a : α => Y a) ≅ (cofan Y).pt :=
    (colimit.isColimit _).coconePointUniqueUpToIso (is_colimit_cofan Y)
  let q : (cofan X).pt ⟶ (cofan Y).pt :=
    (is_colimit_cofan X).desc ⟨(cofan Y).pt, fun a => f a.1 ≫ (cofan Y).ι.app a, _⟩
  swap; · rintro ⟨i⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩; dsimp; simp; dsimp; simp
  have : mono q := by
    apply ConcreteCategory.mono_of_injective
    rintro (u v : Π₀ x, X x) h; ext w
    dsimp [q, is_colimit_cofan, cofan] at h 
    apply_fun fun e => (e : Π₀ w, Y w) w at h 
    simp_rw [DFinsupp.sumAddHom_apply] at h 
    apply_fun f w
    swap
    · rw [← AddCommGroupCat.mono_iff_injective]; infer_instance
    let q : ∀ i, Y i → Π₀ i, Y i := DFinsupp.single
    let qq : ∀ i, X i → Π₀ i, Y i := fun i => q i ∘ f i
    change u.sum (fun i => qq i) w = v.sum (fun i => qq i) w at h 
    rw [@DFinsupp.sum_apply α (fun i => Y i) α _ (fun i => X i) _ _ _ u qq w] at h 
    rw [@DFinsupp.sum_apply α (fun i => Y i) α _ (fun i => X i) _ _ _ v qq w] at h 
    simp only [DFinsupp.single_apply] at h 
    dsimp [DFinsupp.sum] at h 
    simp_rw [Finset.sum_dite_eq'] at h 
    convert h
    all_goals
      split_ifs with hh hh; · rfl
      simp only [DFinsupp.mem_support_toFun, Classical.not_not] at hh 
      simp only [hh, (f w).map_zero]
  suffices t = eX.hom ≫ q ≫ eY.inv by rw [this]; infer_instance
  dsimp [t, eX, q, eY]
  apply colimit.hom_ext
  rintro ⟨j⟩
  simp only [colimit.ι_desc, Cofan.mk_ι_app,
    IsColimit.coconePointUniqueUpToIso_hom_desc_assoc, colimit.isColimit_desc,
    colimit.ι_desc_assoc, Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_inv,
    colimit.cocone_ι, eq_self_iff_true, imp_true_iff]

end AddCommGroupCat

