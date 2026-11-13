import Mathlib.Data.Matrix.Notation
import LiquidTensorExperiment.ForMathlib.ShortExactSequence

#align_import for_mathlib.homological_complex

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] [Abelian C]

variable {ι : Type _} {c : ComplexShape ι}

abbrev fst : ChainComplex (ShortExactSequence C) ℕ ⥤ HomologicalComplex C (ComplexShape.down ℕ) :=
  (ShortExactSequence.fst C).mapHomologicalComplex _

abbrev snd : ChainComplex (ShortExactSequence C) ℕ ⥤ HomologicalComplex C (ComplexShape.down ℕ) :=
  (ShortExactSequence.snd C).mapHomologicalComplex _

abbrev trd : ChainComplex (ShortExactSequence C) ℕ ⥤ HomologicalComplex C (ComplexShape.down ℕ) :=
  (ShortExactSequence.trd C).mapHomologicalComplex _

abbrev fstSnd : fst C ⟶ snd C :=
  NatTrans.mapHomologicalComplex (ShortExactSequence.fNat C) _

abbrev sndTrd : snd C ⟶ trd C :=
  NatTrans.mapHomologicalComplex (ShortExactSequence.gNat C) _

variable {C}

variable (A : ChainComplex (ShortExactSequence C) ℕ)

instance fstSnd_mono (n : ℕ) : Mono (((fstSnd C).app A).f n) :=
  (A.pt n).mono'

instance sndTrd_epi (n : ℕ) : Epi (((sndTrd C).app A).f n) :=
  (A.pt n).epi'

theorem fstSnd_trd_exact (n : ℕ) : Exact (((fstSnd C).app A).f n) (((sndTrd C).app A).f n) :=
  (A.pt n).exact'

end HomologicalComplex

