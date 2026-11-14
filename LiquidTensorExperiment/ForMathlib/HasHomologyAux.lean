import LiquidTensorExperiment.ForMathlib.HasHomology
import LiquidTensorExperiment.ForMathlib.ComplexExtend
import LiquidTensorExperiment.ForMathlib.HomologyIsoDatum

#align_import for_mathlib.has_homology_aux

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

section

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable {ι : Type _} {c : ComplexShape ι}

variable (C : HomologicalComplex 𝓐 c)

def homologicalComplexHasHomology (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    HasHomology (C.d i j) (C.d j k) (C.homology' j) :=
  (HomologyIsoDatum.ofHomologicalComplex C i j k hij hjk).HasHomology

abbrev chainComplexNatHasHomology {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] (C : ChainComplex 𝓐 ℕ)
    (n : ℕ) : HasHomology (C.d (n + 1 + 1) (n + 1)) (C.d (n + 1) n) (C.homology' (n + 1)) :=
  homologicalComplexHasHomology C (n + 1 + 1) (n + 1) n rfl rfl

abbrev cochainComplexIntHasHomology {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] (C : CochainComplex 𝓐 ℤ)
    (n : ℤ) : HasHomology (C.d n (n + 1)) (C.d (n + 1) (n + 1 + 1)) (C.homology' (n + 1)) :=
  homologicalComplexHasHomology C n (n + 1) (n + 1 + 1) rfl rfl

end

def mapHomologicalComplexEmbed {𝓐 𝓑 : Type _} [Category 𝓐] [Abelian 𝓐] [Category 𝓑] [Abelian 𝓑]
    (F : 𝓐 ⥤ 𝓑) [F.Additive] :
    HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙ F.mapHomologicalComplex _ ≅
      F.mapHomologicalComplex _ ⋙ HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp :=
  NatIso.ofComponents
    (fun C =>
      HomologicalComplex.Hom.isoOfComponents
        (fun n => by
          rcases n with ((_ | n) | n)
          · exact iso.refl _
          · apply Functor.mapZeroObject
          · exact iso.refl _)
        (by
          rintro i j (rfl : _ = _); rcases i with (n | (_ | n))
          · apply IsZero.eq_of_tgt; apply is_zero_zero
          · erw [Category.id_comp, Category.comp_id]; rfl
          · erw [Category.id_comp, Category.comp_id]; rfl))
    (by
      intro C₁ C₂ f; ext ((_ | n) | n) : 2
      · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
        dsimp; erw [Category.id_comp, Category.comp_id]; rfl
      · apply IsZero.eq_of_tgt; apply is_zero_zero
      · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
        dsimp; erw [Category.id_comp, Category.comp_id])

