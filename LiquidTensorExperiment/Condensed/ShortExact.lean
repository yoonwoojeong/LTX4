import LiquidTensorExperiment.Condensed.Exact
import LiquidTensorExperiment.ForMathlib.SplitExact

#align_import condensed.short_exact

noncomputable section

universe u

open Opposite CategoryTheory

namespace Condensed

theorem mono_iff_extrDisc {A B : Condensed.{u} Ab.{u + 1}} (f : A ⟶ B) :
    Mono f ↔ ∀ S : ExtrDisc, Mono (f.1.app <| extrDiscToProfinite.op.obj (op S)) :=
  by
  constructor
  · intro H S
    erw [(abelian.tfae_mono (A.val.obj (op S.val)) (f.val.app (op S.val))).out 0 2]
    erw [(abelian.tfae_mono A f).out 0 2] at H 
    rw [Condensed.exact_iff_extrDisc] at H 
    apply H
  · intro H
    apply exact.mono_of_exact_zero_left; swap; exact A
    rw [Condensed.exact_iff_extrDisc]
    intro S; specialize H S
    show exact 0 _
    erw [(abelian.tfae_mono (A.val.obj (op S.val)) (f.val.app (op S.val))).out 2 0]
    exact H

theorem shortExact_iff_extrDisc {A B C : Condensed.{u} Ab.{u + 1}} (f : A ⟶ B) (g : B ⟶ C) :
    ShortExact f g ↔
      ∀ S : ExtrDisc,
        ShortExact (f.1.app <| extrDiscToProfinite.op.obj (op S))
          (g.1.app <| extrDiscToProfinite.op.obj (op S)) :=
  by
  constructor
  · intro H S
    apply (config := { instances := false }) short_exact.mk
    · revert S; rw [← mono_iff_ExtrDisc]; exact H.mono
    · rw [AddCommGroupCat.epi_iff_surjective]
      revert S; erw [← is_epi_iff_forall_surjective]; exact H.epi
    · revert S; rw [← Condensed.exact_iff_extrDisc]; exact H.exact
  · intro H
    apply (config := { instances := false }) short_exact.mk
    · rw [mono_iff_ExtrDisc]; intro S; exact (H S).Mono
    · simp only [is_epi_iff_forall_surjective, ← AddCommGroupCat.epi_iff_surjective]
      intro S; exact (H S).Epi
    · rw [Condensed.exact_iff_extrDisc]; intro S; exact (H S).exact

end Condensed

