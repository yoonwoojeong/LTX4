import LiquidTensorExperiment.FreePfpng.Basic
import LiquidTensorExperiment.PseudoNormedGroup.BoundedLimits
import LiquidTensorExperiment.Condensed.Adjunctions
import LiquidTensorExperiment.ForMathlib.AddCommGroup

#align_import free_pfpng.lemmas

universe u

-- Move this
namespace Profinite

def pt {S : Profinite} (x : S) : Profinite.of punit ⟶ S :=
  ⟨fun _ => x⟩

theorem discreteQuotient_separates_points_aux {S : Profinite} {x y : S} (h : x ≠ y) :
    ∃ T : DiscreteQuotient S, T.proj x ≠ T.proj y :=
  by
  contrapose! h
  let x' := Profinite.pt x
  let y' := Profinite.pt y
  suffices x' = y' by change x' PUnit.unit = y' PUnit.unit; rw [this]
  apply S.as_limit.hom_ext; intro T; specialize h T
  ext; exact h

theorem discreteQuotient_separates_points {α : Type _} [Fintype α] {S : Profinite} (f : α → S)
    (hf : Function.Injective f) : ∃ T : DiscreteQuotient S, Function.Injective (T.proj ∘ f) := by
  classical
  let e : ∀ (a b : α) (h : a ≠ b), {x : S × S | x.1 ≠ x.2} := fun a b h => ⟨⟨_, _⟩, hf.ne h⟩
  choose T hT using fun a b h => Profinite.discreteQuotient_separates_points_aux (e a b h).2
  obtain ⟨E, hE⟩ : ∃ E : DiscreteQuotient S, ∀ a b h, E ≤ T a b h :=
    by
    let E : DiscreteQuotient S :=
      (Finset.univ : Finset ↥{x : α × α | x.1 ≠ x.2}).inf fun x => T x.1.1 x.1.2 x.2
    use E; intro a b h
    let i : {x : α × α | x.1 ≠ x.2} := ⟨⟨a, b⟩, h⟩
    have hi : i ∈ Finset.univ := by refine' Finset.mem_univ i
    exact Finset.inf_le hi
  use E
  intro a b h
  specialize hT a b
  contrapose h
  intro c
  apply hT h
  apply_fun DiscreteQuotient.ofLE (hE a b h) at c 
  exact c

end Profinite

namespace FreePfpng

open CategoryTheory

theorem discreteQuotient_separates_points (S : Profinite.{u}) (t₁ t₂ : S.FreePfpng)
    (h : ∀ T : DiscreteQuotient S, S.freePfpngπ T t₁ = S.freePfpngπ T t₂) : t₁ = t₂ :=
  by
  let E :
    Limits.Cone
      ((S.fintype_diagram ⋙ freePfpngFunctor) ⋙ ProFiltPseuNormGrp₁.toPNG₁ ⋙ PseuNormGrp₁.toAb) :=
    Ab.explicitLimitCone.{u, u} _
  let hE : Limits.IsLimit E := Ab.explicitLimitConeIsLimit _
  let B := ProFiltPseuNormGrp₁.boundedCone ⟨E, hE⟩
  let hB : Limits.IsLimit B := ProFiltPseuNormGrp₁.boundedConeIsLimit ⟨E, hE⟩
  let II : Limits.limit.cone _ ≅ B := (Limits.limit.isLimit _).uniqueUpToIso hB
  let I : S.free_pfpng ≅ B.X := (Limits.Cones.forget _).mapIso II
  apply_fun I.hom; ext T : 3; exact h T
  intro x y hh; apply_fun fun e => I.inv e at hh 
  change (I.hom ≫ I.inv) x = (I.hom ≫ I.inv) y at hh 
  simpa only [Iso.hom_inv_id] using hh

end FreePfpng

namespace FreePfpng

open AddCommGroupCat

/-- If `t₁ t₂ : ℤ[S]` have the same image in `ℤ[T]` for every discrete quotient `T` of `S`,
then `t₁ = t₂`. Here `ℤ[-]` refers to the usual free abelian group of the *set* `S`.
-/
def discreteQuotient_separates_points' (S : Profinite.{u}) (t : free'.obj S)
    (h : ∀ T : DiscreteQuotient S, free'.map T.proj t = 0) : t = 0 :=
  by
  let A := t.support
  let e : A → ℤ := fun a => t.toFun a
  let ι : A → S := fun a => a
  have hι : Function.Injective ι := by intro x y h; ext; exact h
  obtain ⟨T, hT⟩ := Profinite.discreteQuotient_separates_points ι hι
  specialize h T
  let t' : A →₀ ℤ := t.comapDomain ι _
  swap; · apply hι.inj_on
  let q : T →₀ ℤ := free'.map T.proj t
  let π : A → T := T.proj ∘ ι
  let q' : A →₀ ℤ := q.comapDomain π _
  swap; · apply hT.inj_on
  suffices t' = q' by
    ext i; by_cases hi : i ∈ A
    swap; · rwa [Finsupp.not_mem_support_iff] at hi 
    let j : A := ⟨i, hi⟩; change t' j = 0; rw [this]
    let t : T := T.proj i; apply_fun fun e => e.toFun t at h 
    exact h
  classical
  ext a
  dsimp [t', q', ι, q, π, Finsupp.mapDomain]
  simp only [Finsupp.sum_apply]
  dsimp [Finsupp.sum, Finsupp.single]
  erw [Finset.sum_ite]
  simp
  convert (@Finset.sum_singleton ℤ S a t.toFun _).symm
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · rw [Finset.mem_filter]
    exact ⟨a.2, rfl⟩
  · intro x hx; rw [Finset.mem_filter] at hx 
    let x' : A := ⟨x, hx.1⟩
    change ι x' = ι a
    congr 1; apply hT; exact hx.2

end FreePfpng

