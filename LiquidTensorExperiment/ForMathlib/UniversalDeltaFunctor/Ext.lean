import LiquidTensorExperiment.ForMathlib.UniversalDeltaFunctor.Basic
import LiquidTensorExperiment.ForMathlib.Derived.Les3
import LiquidTensorExperiment.ForMathlib.Derived.LesFacts
import LiquidTensorExperiment.ForMathlib.Derived.ExtLemmas

#align_import for_mathlib.universal_delta_functor.Ext

open CategoryTheory

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable section

-- move me
/-- Get an SES in `A` from a SES in `Aᵒᵖ`. -/
def ShortExactSequence.unop (S : ShortExactSequence Aᵒᵖ) : ShortExactSequence A
    where
  fst := S.trd.unop
  snd := S.snd.unop
  trd := S.fst.unop
  f := S.g.unop
  g := S.f.unop
  mono' := inferInstance
  epi' := inferInstance
  exact' := S.exact'.unop

-- move me
theorem ShortExactSequence.shortExact (S : ShortExactSequence A) : ShortExact S.f S.g :=
  { exact := S.exact' }

variable (A) [EnoughProjectives A]

/-- `Ext' i (-, B)` as a δ-functor. -/
def extδFunctor (B : A) : Aᵒᵖ ⥤δ Ab.{v}
    where
  f i := (ext' i).flip.obj B
  Additive := inferInstance
  δ n :=
    { app := fun S => by
        apply ext'δ B (ShortExactSequence.shortExact <| ShortExactSequence.unop S) n
      naturality' := by
        intro S T f
        dsimp only [functor.comp_map]
        have :=
          ext'δ_natural _ _ _ _ ((short_exact_sequence.Trd Aᵒᵖ).map f).unop _
            ((short_exact_sequence.Fst Aᵒᵖ).map f).unop _ _ B
            (ShortExactSequence.shortExact <| ShortExactSequence.unop T)
            (ShortExactSequence.shortExact <| ShortExactSequence.unop S) n
        dsimp only [Quiver.Hom.op_unop] at this 
        exact this
        exact f.snd.unop
        dsimp only [ShortExactSequence.unop, ← unop_comp]; rw [f.sq2]; rfl
        dsimp only [ShortExactSequence.unop, ← unop_comp]; rw [← f.sq1]; rfl }
  Mono := by
    intro S
    let e := BoundedDerivedCategory.ext'ZeroFlipIso A B
    let t := _; change mono t
    have ht : t = e.hom.app _ ≫ CategoryTheory.Functor.map _ S.f ≫ e.inv.app _ :=
      by
      dsimp [t]
      erw [← e.hom.naturality_assoc]
      rw [← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app, category.comp_id]
      rfl
    rw [ht]; clear ht t
    apply (config := { instances := false }) mono_comp; infer_instance
    apply (config := { instances := false }) mono_comp; swap; infer_instance
    apply concrete_category.mono_of_injective; intro a b h
    dsimp at h 
    rwa [← cancel_epi S.f.unop]
  exact' := by
    intro n S
    have :=
      (short_exact.Ext'_five_term_exact_seq B
            (ShortExactSequence.shortExact <| ShortExactSequence.unop S) n).extract
        0 2
    rw [exact_iff_exact_seq]; exact this
  exact_δ := by
    intro n S
    have :=
      (short_exact.Ext'_five_term_exact_seq B
            (ShortExactSequence.shortExact <| ShortExactSequence.unop S) n).extract
        1 2
    rw [exact_iff_exact_seq]; exact this
  δ_exact := by
    intro n S
    have :=
      (short_exact.Ext'_five_term_exact_seq B
            (ShortExactSequence.shortExact <| ShortExactSequence.unop S) n).extract
        2 3
    rw [exact_iff_exact_seq]; exact this

instance (B : A) : DeltaFunctor.Tohoku.Effaceable (extδFunctor A B) :=
  by
  constructor; intro X n
  let P := projective.over X.unop
  let π : P ⟶ X.unop := projective.π _
  constructor
  refine' ⟨_, π.op, _⟩
  apply limits.is_zero.eq_of_tgt
  apply BoundedDerivedCategory.ext'_isZero_of_projective
  infer_instance
  norm_cast
  exact Nat.succ_pos n

instance (B : A) : DeltaFunctor.Universal (extδFunctor A B) :=
  DeltaFunctor.universalOfEffaceable _

