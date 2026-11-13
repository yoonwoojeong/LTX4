import LiquidTensorExperiment.ForMathlib.Endomorphisms.Basic
import LiquidTensorExperiment.ForMathlib.Derived.LesFacts
import LiquidTensorExperiment.ForMathlib.AdditiveFunctor
import LiquidTensorExperiment.ForMathlib.ExactFunctor
import LiquidTensorExperiment.ForMathlib.HomotopyCategoryOp
import LiquidTensorExperiment.ForMathlib.HasHomologyAux
import LiquidTensorExperiment.ForMathlib.HomSingleIso2
import LiquidTensorExperiment.ForMathlib.NatTrans

#align_import for_mathlib.endomorphisms.Ext

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

open BoundedHomotopyCategory

namespace HomologicalComplex

variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐]

variable {ι : Type _} {c : ComplexShape ι}

def e (X : HomologicalComplex (Endomorphisms 𝓐) c) :
    End (((Endomorphisms.forget 𝓐).mapHomologicalComplex c).obj X)
    where
  f i := (X.pt i).e
  comm' i j hij := (X.d i j).comm

def mkEnd (X : HomologicalComplex 𝓐 c) (f : X ⟶ X) : HomologicalComplex (Endomorphisms 𝓐) c
    where
  pt i := ⟨X.pt i, f.f i⟩
  d i j := ⟨X.d i j, f.comm i j⟩
  shape' := by intro i j h; ext; apply X.shape i j h
  d_comp_d' := by intros; ext; apply X.d_comp_d

end HomologicalComplex

namespace HomotopyCategory

variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐]

variable {𝓑 : Type _} [Category 𝓑] [Abelian 𝓑]

variable (F : 𝓐 ⥤ 𝓑) [Functor.Additive F]

instance mapHomotopyCategoryIsBoundedAbove (X : HomotopyCategory 𝓐 <| ComplexShape.up ℤ)
    [X.IsBoundedAbove] : ((F.mapHomotopyCategory _).obj X).IsBoundedAbove :=
  by
  obtain ⟨b, hb⟩ := is_bounded_above.cond X
  exact ⟨⟨b, fun i hi => CategoryTheory.Functor.map_isZero _ (hb i hi)⟩⟩

end HomotopyCategory

namespace BoundedHomotopyCategory

variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐]

variable [HasCoproductsOfShape (ULift.{v} ℕ) 𝓐]

variable [HasProductsOfShape (ULift.{v} ℕ) 𝓐]

variable (X : BoundedHomotopyCategory (Endomorphisms 𝓐))

/-- `unEnd` is the "forget the endomorphism" map from the category whose objects are complexes
of pairs `(Aⁱ,eⁱ)` with morphisms defined up to homotopy, to the category whose objects are
complexes of objects `Aⁱ` with morphisms defined up to homotopy.  -/
def unEnd : BoundedHomotopyCategory 𝓐 :=
  of <| ((Endomorphisms.forget _).mapHomotopyCategory _).obj X.val

def e : End X.unEnd :=
  (HomotopyCategory.quotient _ _).map <| X.val.as.e

end BoundedHomotopyCategory

namespace CategoryTheory

section

variable {C : Type _} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem IsIso.comp_right_iff [IsIso g] : IsIso (f ≫ g) ↔ IsIso f :=
  by
  constructor <;> intro h
  · have : is_iso ((f ≫ g) ≫ inv g) := by infer_instance
    simpa only [category.assoc, is_iso.hom_inv_id, category.comp_id]
  · infer_instance

theorem IsIso.comp_left_iff [IsIso f] : IsIso (f ≫ g) ↔ IsIso g :=
  by
  constructor <;> intro h
  · have : is_iso (inv f ≫ f ≫ g) := by infer_instance
    simpa only [category.assoc, is_iso.inv_hom_id_assoc]
  · infer_instance

end

namespace Endomorphisms

variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]

variable [HasCoproductsOfShape (ULift.{v} ℕ) 𝓐]

variable [HasProductsOfShape (ULift.{v} ℕ) 𝓐]

def mkBoHoCa' (X : CochainComplex 𝓐 ℤ)
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj X).IsBoundedAbove] (f : X ⟶ X) :
    BoundedHomotopyCategory (Endomorphisms 𝓐)
    where
  val :=
    {
      as :=
        { pt := fun i => ⟨X.pt i, f.f i⟩
          d := fun i j => ⟨X.d i j, f.comm _ _⟩
          shape' := fun i j h => by ext; exact X.shape i j h
          d_comp_d' := fun i j k hij hjk => by ext; apply HomologicalComplex.d_comp_d } }
  bdd :=
    by
    obtain ⟨a, ha⟩ :=
      HomotopyCategory.IsBoundedAbove.cond ((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj X)
    refine' ⟨⟨a, fun i hi => _⟩⟩
    rw [is_zero_iff_id_eq_zero]; ext; dsimp; rw [← is_zero_iff_id_eq_zero]
    exact ha i hi

def mkBoHoCa (X : BoundedHomotopyCategory 𝓐) (f : X ⟶ X) :
    BoundedHomotopyCategory (Endomorphisms 𝓐) :=
  @mkBoHoCa' _ _ _ _ _ _ X.val.as (by cases' X with X hX; cases X; exact hX) f.out

theorem quot_out_single_map {X Y : 𝓐} (f : X ⟶ Y) (i : ℤ) :
    ((HomotopyCategory.single 𝓐 i).map f).out = (HomologicalComplex.single 𝓐 _ i).map f :=
  by
  have h :=
    HomotopyCategory.homotopyOutMap ((HomologicalComplex.single 𝓐 (ComplexShape.up ℤ) i).map f)
  ext k
  erw [h.comm k]
  suffices (dNext k) h.hom + (prevD k) h.hom = 0 by rw [this, zero_add]
  obtain hki | rfl := ne_or_eq k i
  · apply limits.is_zero.eq_of_src
    show is_zero (ite (k = i) X _); rw [if_neg hki]; apply is_zero_zero
  · have hk1 : (ComplexShape.up ℤ).Rel (k - 1) k := sub_add_cancel _ _
    have hk2 : (ComplexShape.up ℤ).Rel k (k + 1) := rfl
    rw [prevD_eq _ hk1, dNext_eq _ hk2]
    have aux1 : h.hom (k + 1) k = 0 :=
      by
      apply limits.is_zero.eq_of_src; show is_zero (ite _ X _); rw [if_neg]; apply is_zero_zero
      linarith
    have aux2 : h.hom k (k - 1) = 0 :=
      by
      apply limits.is_zero.eq_of_tgt; show is_zero (ite _ Y _); rw [if_neg]; apply is_zero_zero
      linarith
    rw [aux1, aux2, comp_zero, zero_comp, add_zero]

def mkBoHaCa'Single (X : 𝓐) (f : X ⟶ X) :
    mkBoHoCa' ((HomologicalComplex.single _ _ 0).obj X) (Functor.map _ f) ≅
      (single _ 0).obj ⟨X, f⟩ :=
  BoundedHomotopyCategory.mkIso
    (by
      refine' (HomotopyCategory.quotient _ _).mapIso _
      refine' HomologicalComplex.Hom.isoOfComponents _ _
      · intro i
        refine' endomorphisms.mk_iso _ _
        · dsimp; split_ifs; · exact iso.refl _
          · refine' (is_zero_zero _).Iso _; apply endomorphisms.is_zero_X
            exact is_zero_zero (endomorphisms 𝓐)
        · dsimp; split_ifs with hi
          · subst i; dsimp; erw [iso.refl_hom]; simp only [category.id_comp, category.comp_id]
            convert rfl
          · apply is_zero.eq_of_src; rw [if_neg hi]; exact is_zero_zero _
      · rintro i j (rfl : _ = _)
        by_cases hi : i = 0
        · apply is_zero.eq_of_tgt; dsimp; rw [if_neg]; exact is_zero_zero _; linarith only [hi]
        · apply is_zero.eq_of_src; dsimp; rw [is_zero_iff_id_eq_zero]; ext; dsimp; rw [if_neg hi]
          apply (is_zero_zero _).eq_of_src)

def mkBoHaCaSingle (X : 𝓐) (f : X ⟶ X) :
    mkBoHoCa ((single _ 0).obj X) ((single _ 0).map f) ≅ (single _ 0).obj ⟨X, f⟩ :=
  BoundedHomotopyCategory.mkIso
    (by
      dsimp only [mk_bo_ho_ca, single]
      refine' (HomotopyCategory.quotient _ _).mapIso _
      refine' HomologicalComplex.Hom.isoOfComponents _ _
      · intro i
        refine' endomorphisms.mk_iso _ _
        · dsimp; split_ifs; · exact iso.refl _
          · refine' (is_zero_zero _).Iso _; apply endomorphisms.is_zero_X
            exact is_zero_zero (endomorphisms 𝓐)
        · dsimp; erw [quot_out_single_map]; dsimp; split_ifs with hi
          · subst i; dsimp; erw [iso.refl_hom]; simp only [category.id_comp, category.comp_id]
            convert rfl
          · apply is_zero.eq_of_src; rw [if_neg hi]; exact is_zero_zero _
      · rintro i j (rfl : _ = _)
        by_cases hi : i = 0
        · apply is_zero.eq_of_tgt; dsimp; rw [if_neg]; exact is_zero_zero _; linarith only [hi]
        · apply is_zero.eq_of_src; dsimp; rw [is_zero_iff_id_eq_zero]; ext; dsimp; rw [if_neg hi]
          apply (is_zero_zero _).eq_of_src)

instance {P Q : BoundedHomotopyCategory (Endomorphisms 𝓐)} (f : P ⟶ Q)
    [HomotopyCategory.IsQuasiIso f] :
    HomotopyCategory.IsQuasiIso ((Endomorphisms.forget _).mapBoundedHomotopyCategory.map f) :=
  (Endomorphisms.forget 𝓐).mapQuasiIsoOnHomotopyCategory f

instance forgetPreservesIsQuasiIso {P Q : BoundedHomotopyCategory 𝓐} (f : P ⟶ Q)
    [hf : HomotopyCategory.IsQuasiIso f] :
    HomotopyCategory.IsQuasiIso ((BoundedHomotopyCategory.forget 𝓐).map f) :=
  hf

instance forget_of_termwise_projective_is_termwise_projective
    {P : BoundedHomotopyCategory (Endomorphisms 𝓐)} (k : ℤ) [hP : Projective (P.val.as.pt k)] :
    Projective (((Endomorphisms.forget 𝓐).mapBoundedHomotopyCategory.obj P).val.as.pt k) := by
  dsimp [of]; infer_instance

def forgetMkEnd (X : ChainComplex 𝓐 ℕ) (f : X ⟶ X) :
    (Endomorphisms.forget 𝓐).mapBoundedHomotopyCategory.obj
        (ChainComplex.toBoundedHomotopyCategory.obj (HomologicalComplex.mkEnd X f)) ≅
      ChainComplex.toBoundedHomotopyCategory.obj X :=
  BoundedHomotopyCategory.mkIso <|
    (HomotopyCategory.quotient _ _).mapIso <|
      HomologicalComplex.Hom.isoOfComponents
        (fun m =>
          match m with
          | Int.ofNat 0 => Iso.refl _
          | Int.ofNat (i + 1) => IsZero.iso (Functor.map_isZero _ <| isZero_zero _) (isZero_zero _)
          | -[i+1] => Iso.refl _)
        (by
          rintro (i | (_ | i)) j (rfl : _ = _)
          · apply (is_zero_zero _).eq_of_tgt
          · erw [iso.refl_hom, iso.refl_hom, category.id_comp, category.comp_id]; rfl
          · erw [iso.refl_hom, iso.refl_hom, category.id_comp, category.comp_id]; rfl)

/-

Mathematical summary of the `Ext_is_zero_iff` proof according to kmb's
possibly flawed understanding:

The lemma will follow from the following things:

1) If X is a complex in the bounded homotopy category
and Y is an object, thought of as a `single`
complex, then Extⁱ(X,Y) is the homology of the complex
(Cᵢ) whose i'th term is Hom(Pⁱ,Y), where P is a projective
replacement of X. This applies to both the category 𝓐
and to the endomorphism category. The reason is
that Extⁱ(X,Y)=Hom(P,Y⟦i⟧).

2) For a cleverly chosen choice of Pⁱ (see `exists_K_projective_endomorphism_replacement`)
we have a short exact sequence of complexes
0 -> Hom_{endos}(Pⁱ,Y) -> Hom(Pⁱ,Y) -> Hom(Pⁱ,Y)->0
where the surjection is e(P) - e(Y), with e the endomorphism.
This can be checked to be surjective via an explicit construction;
the trick is that Pⁱ is going to be `free Q` for some object `Q : 𝓐`

-/
variable (Y : 𝓐) (g : Y ⟶ Y) (P : BoundedHomotopyCategory (Endomorphisms 𝓐))

def c₁ (Y : Endomorphisms 𝓐) (P : BoundedHomotopyCategory (Endomorphisms 𝓐)) :=
  ((preadditiveYoneda.obj Y).mapHomologicalComplex _).obj P.val.as.op

def c₂ (Y : 𝓐) (P : BoundedHomotopyCategory (Endomorphisms 𝓐)) :=
  ((preadditiveYoneda.obj Y).mapHomologicalComplex _).obj P.unEnd.val.as.op

def map₁ : c₁ ⟨Y, g⟩ P ⟶ c₂ Y P
    where
  f i :=
    { toFun := Endomorphisms.Hom.f
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  comm' i j h := rfl

open CategoryTheory.Preadditive

@[simps]
def map₂Left : c₂ Y P ⟶ c₂ Y P :=
  ((preadditiveYoneda.obj Y).mapHomologicalComplex _).map
    (HomologicalComplex.opFunctor.map (Quiver.Hom.op P.val.as.e))

@[simps]
def map₂Right : c₂ Y P ⟶ c₂ Y P :=
  (NatTrans.mapHomologicalComplex (preadditiveYoneda.map g) _).app P.unEnd.val.as.op

def map₂ : c₂ Y P ⟶ c₂ Y P :=
  map₂Left Y P - map₂Right Y g P

theorem map₁_mono (n : ℤ) : Mono ((map₁ Y g P).f n) :=
  by
  rw [AddCommGroupCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro φ hφ; ext; exact hφ

theorem map₂_epi {n : ℤ} (h : Projective (P.val.as.pt n)) : Epi ((map₂ Y g P).f n) :=
  by
  -- this is Joel Riou's argument, reduce to `free` and do an explicit calculation
  let F : (endomorphisms 𝓐)ᵒᵖ ⥤ AddCommGroupCat :=
    (endomorphisms.forget 𝓐).op ⋙ preadditive_yoneda.obj Y
  let τ : F ⟶ F :=
    { app := fun Q =>
        AddMonoidHom.mk' (fun ψ => Q.unop.e ≫ ψ - ψ ≫ g)
          (by
            intro a b
            simp only [comp_add, add_comp, sub_eq_add_neg, neg_add, add_assoc]
            congr 1; apply add_left_comm)
      naturality' := fun Q₁ Q₂ f => by
        ext
        simp only [functor.comp_map, functor.op_map, forget_map, comp_apply, AddMonoidHom.mk'_apply,
          map_sub]
        congr 1
        · dsimp; apply f.unop.comm_assoc
        · dsimp; rw [category.assoc] }
  suffices ∀ (Q : endomorphisms 𝓐) (hQ : projective Q), epi (τ.app (op Q)) by exact this _ h
  suffices ∀ (A : 𝓐) (hA : projective A), epi (τ.app (op (free A)))
    by
    intro Q
    intro
    haveI := this Q.X inferInstance
    let π := free.desc (𝟙 Q.X)
    haveI : epi π.f :=
      by
      refine' @epi_of_epi _ _ _ _ _ (sigma.ι _ (ULift.up 0)) _ (id _)
      simp only [free.desc_f, category.id_comp, colimit.ι_desc, cofan.mk_ι_app, pow_zero,
        End.one_def]
      infer_instance
    haveI : epi π := epi_of_epi_f _
    let s := projective.factor_thru (𝟙 Q) π
    have hs : s ≫ π = 𝟙 Q := projective.factor_thru_comp _ _
    constructor
    intro Z q₁ q₂ hq₀
    have hq₁ := congr_arg (fun q : _ ⟶ _ => F.map s.op ≫ q) hq₀
    simp only at hq₁ 
    rw [τ.naturality_assoc, τ.naturality_assoc, cancel_epi (τ.app (op (free Q.X)))] at hq₁ 
    simpa only [← F.map_comp_assoc, ← op_comp, hs, op_id, F.map_id, category.id_comp] using
      congr_arg (fun q : _ ⟶ _ => F.map π.op ≫ q) hq₁
  intro A hA
  rw [AddCommGroupCat.epi_iff_surjective]
  intro φ
  let ψ : (free A).pt ⟶ Y := by
    refine' sigma.desc _; rintro ⟨i⟩; refine' Nat.recOn i 0 fun j ψ => _
    refine' sigma.ι (fun i : ULift ℕ => A) (ULift.up j) ≫ φ + ψ ≫ g
  refine' ⟨ψ, _⟩
  ext ⟨⟨i⟩⟩
  dsimp only [τ, AddMonoidHom.mk'_apply, free, unop_op, op_unop, ψ]
  rw [comp_sub, sub_eq_iff_eq_add]
  simp only [colimit.ι_desc_assoc, colimit.ι_desc, limits.cofan.mk_ι_app]
  rfl

theorem map₁₂_exact {n : ℤ} (h : Projective (P.val.as.pt n)) :
    Exact ((map₁ Y g P).f n) ((map₂ Y g P).f n) :=
  by
  rw [AddCommGroupCat.exact_iff']; constructor
  · rw [map₂, HomologicalComplex.sub_f_apply, comp_sub]
    ext φ
    simp only [map₁, map₂_left_f_apply, map₂_right_f_apply, AddMonoidHom.sub_apply, comp_apply,
      AddCommGroupCat.zero_apply]
    erw [endomorphisms.hom.comm]; apply sub_self
  intro φ hφ
  refine' ⟨⟨φ, _⟩, _⟩
  ·
    simpa only [AddMonoidHom.mem_ker, map₂, map₂_left_f_apply, map₂_right_f_apply,
      HomologicalComplex.sub_f_apply, AddMonoidHom.sub_apply, sub_eq_zero] using hφ
  · rfl

theorem map₁₂_shortExact {n : ℤ} (h : Projective (P.val.as.pt n)) :
    ShortExact ((map₁ Y g P).f n) ((map₂ Y g P).f n) :=
  { Mono := map₁_mono _ _ _ _
    Epi := map₂_epi _ _ _ h
    exact := map₁₂_exact _ _ _ h }

theorem homology_isZero_iff_isIso (h : ∀ n, Projective (P.val.as.pt n)) :
    (∀ i, IsZero ((homology'Functor _ _ i).obj (c₁ ⟨Y, g⟩ P))) ↔
      ∀ j, IsIso ((homology'Functor _ _ j).map (map₂ Y g P)) :=
  by
  have LES :=
    HomologicalComplex.six_term_exactSeq (map₁ Y g P) (map₂ Y g P) fun n =>
      map₁₂_short_exact _ _ _ (h n)
  constructor
  · intro H i
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
    apply (LES (i + 1) i rfl).isIso_of_zero_of_zero
    · refine' (H (i + 1)).eq_of_src _ _
    · refine' (H i).eq_of_tgt _ _
  · intro H i
    refine' is_zero_of_exact_zero_zero' _ _ ((LES (i + 1) i rfl).drop 2).pair _ _
    · refine' ((LES (i + 1) i rfl).drop 1).pair.epi_iff_eq_zero.mp _
      exact @is_iso.epi_of_iso _ _ _ _ _ (H _)
    · refine' ((LES (i + 1) i rfl).drop 3).pair.mono_iff_eq_zero.mp _
      exact @is_iso.mono_of_iso _ _ _ _ _ (H _)

@[reassoc]
theorem flip_obj_map_comm {C D E : Type _} [Category C] [Category D] [Category E] (F : C ⥤ D ⥤ E)
    {c : C} {d : D} (f : c ⟶ c) (g : d ⟶ d) :
    (F.flip.obj d).map f ≫ (F.obj c).map g = (F.obj c).map g ≫ (F.flip.obj d).map f :=
  (NatTrans.naturality _ _).symm

@[reassoc]
theorem flip_map_app_comm {C D E : Type _} [Category C] [Category D] [Category E] (F : C ⥤ D ⥤ E)
    {c : C} {d : D} (f : c ⟶ c) (g : d ⟶ d) :
    (F.flip.map g).app c ≫ (F.map f).app d = (F.map f).app d ≫ (F.flip.map g).app c :=
  (NatTrans.naturality _ _).symm

theorem lift_unop_op {X Y : BoundedHomotopyCategory 𝓐} [HomotopyCategory.IsKProjective X.val]
    (g : X ⟶ Y) (f : Y ⟶ Y) :
    BoundedHomotopyCategory.lift g Y.π ≫
        BoundedHomotopyCategory.lift ((unop (op Y)).π ≫ f.op.unop) (unop (op Y)).π =
      lift (g ≫ f) Y.π ≫ eqToHom (by rfl) :=
  by
  erw [lift_comp_lift_comp]
  symm
  apply category.comp_id

theorem compatibility₁_aux {Y : 𝓐} {P₁ P₂ : BoundedHomotopyCategory 𝓐} (f : P₁ ⟶ P₂) :
    (HomotopyCategory.quotient AddCommGroupCat (ComplexShape.up ℤ).symm).map
        (HomologicalComplex.unopFunctor.map
          (((preadditiveYoneda.obj Y).rightOp.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (Quot.out f)).op) =
      (HomotopyCategory.quotient AddCommGroupCat (ComplexShape.up ℤ).symm).map
        (((-- show ((preadditive_yoneda.obj Y).map_homological_complex _).obj P₂.val.as.op ⟶
                    --     ((preadditive_yoneda.obj Y).map_homological_complex _).obj P₁.val.as.op, from
                    preadditiveYoneda.obj
                  Y).mapHomologicalComplex
              (ComplexShape.up
                  ℤ).symm).map <|-- show homological_complex.op_functor.obj (op P₂.val.as) ⟶
              --      homological_complex.op_functor.obj (op P₁.val.as), from
              HomologicalComplex.opFunctor.map
            f.out.op) :=
  rfl

theorem compatibility₁ {Y : 𝓐} {P₁ P₂ P₃ : BoundedHomotopyCategory 𝓐} (g : P₁ ⟶ P₃) (f : P₂ ⟶ P₃)
    (h : P₁.val.as ⟶ P₂.val.as) (H : (HomotopyCategory.quotient _ _).map h ≫ f = g) (i : ℤ) :
    (preadditiveYoneda.obj ((single 𝓐 i).obj Y)).map f.op ≫
        (P₂.homSingleIso Y i).Hom ≫
          (homology'Functor AddCommGroupCat _ i).map
            (((preadditiveYoneda.obj Y).mapHomologicalComplex _).map
              (HomologicalComplex.opFunctor.map (Quiver.Hom.op h))) =
      (preadditiveYoneda.obj ((single 𝓐 i).obj Y)).map g.op ≫ (P₁.homSingleIso Y i).Hom :=
  by
  rw [hom_single_iso_naturality]
  slice_lhs 1 2 => rw [hom_single_iso_naturality]
  simp only [category.assoc]
  congr 1
  dsimp only [functor.comp_map, functor.op]
  simp only [Quiver.Hom.unop_op, ← functor.map_comp, HomotopyCategory.homology'Functor_map_factors]
  congr 1
  simp only [functor.right_op_map, Quiver.Hom.unop_op, functor.map_comp, compatibility₁_aux]
  simp only [← functor.map_comp]
  apply HomotopyCategory.eq_of_homotopy
  apply functor.map_homotopy
  rw [← op_comp]
  apply HomologicalComplex.opFunctorMapHomotopy
  apply HomotopyCategory.homotopyOfEq
  simp only [functor.map_comp, HomotopyCategory.quotient_map_out]
  exact H

instance preadditiveYoneda_flip_additive : (preadditiveYoneda : 𝓐 ⥤ _).flip.Additive where

variable (𝓐)

@[simps]
def congrSingleFunctor {p q : ℤ} (h : p = q) : single 𝓐 p ≅ single 𝓐 q :=
  eqToIso (by subst h)

variable {𝓐}

@[reassoc]
theorem preadditiveYoneda_bifunctor_comm {C : Type _} [Category C] [Preadditive C] {X₁ X₂ : C}
    {Y₁ Y₂ : Cᵒᵖ} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (preadditiveYoneda.obj X₁).map g ≫ (preadditiveYoneda.map f).app Y₂ =
      (preadditiveYoneda.map f).app Y₁ ≫ (preadditiveYoneda.obj X₂).map g :=
  NatTrans.naturality _ _

theorem compatibility₂ {Y₁ Y₂ : 𝓐} (g : Y₁ ⟶ Y₂) {P₁ P₂ : BoundedHomotopyCategory 𝓐} (π : P₁ ⟶ P₂)
    (i : ℤ) :
    (preadditiveYoneda.map
              (((shiftSingleIso 0 (-i)).app Y₁).Hom ≫
                eqToHom
                  (show (single 𝓐 (0 - -i)).obj Y₁ = (single 𝓐 i).obj Y₁ by congr; linarith))).app
          (op P₂) ≫
        (preadditiveYoneda.obj ((single 𝓐 i).obj Y₁)).map π.op ≫
          (homSingleIso P₁ Y₁ i).Hom ≫
            (homology'Functor _ _ i).map
              ((NatTrans.mapHomologicalComplex (preadditiveYoneda.map g) _).app P₁.val.as.op) =
      (preadditiveYoneda.map
              ((shiftFunctor (BoundedHomotopyCategory 𝓐) (-i)).map ((single 𝓐 0).map g))).app
          (op P₂) ≫
        (preadditiveYoneda.map
                (((shiftSingleIso 0 (-i)).app Y₂).Hom ≫
                  eqToHom
                    (show (single 𝓐 (0 - -i)).obj Y₂ = (single 𝓐 i).obj Y₂ by congr; linarith))).app
            (op P₂) ≫
          (preadditiveYoneda.obj ((single 𝓐 i).obj Y₂)).map π.op ≫ (homSingleIso P₁ Y₂ i).Hom :=
  by
  let τiso := shift_single_iso 0 (-i) ≪≫ congr_single_functor 𝓐 (show 0 - -i = i by linarith)
  let τ := (shift_single_iso 0 (-i) ≪≫ congr_single_functor 𝓐 (show 0 - -i = i by linarith)).Hom
  have eq₁ :
    ∀ Y,
      eq_to_hom (show (single 𝓐 (0 - -i)).obj Y = (single 𝓐 i).obj Y by congr; linarith) =
        ((congr_single_functor _ (by linarith)).app Y).Hom :=
    fun Y => by simp only [iso.app_hom, congr_single_functor_hom, eq_to_hom_app]
  have eq₂ :
    shift_single_iso 0 (-i) ≪≫ congr_single_functor 𝓐 (show 0 - -i = i by linarith) = τiso := rfl
  have eq₃ : ∀ Y, (τiso.app Y).Hom = τ.app Y := fun Y => rfl
  simp only [eq₁, ← iso.trans_hom, ← nat_iso.trans_app, eq₂, eq₃]
  have eq₄ := preadditive_yoneda.congr_map (τ.naturality g)
  simp only [functor.map_comp] at eq₄ 
  have eq₅ := nat_trans.congr_app eq₄ (op P₂)
  simp only [nat_trans.comp_app] at eq₅ 
  slice_rhs 1 2 => erw [eq₅]
  simp only [category.assoc]
  congr 1
  rw [← preadditive_yoneda_bifunctor_comm_assoc]
  congr 1
  apply concrete_category.hom_ext
  intro x
  apply hom_single_iso_naturality_snd_var

--attribute [reassoc] nat_trans.comp_app
theorem ext_isZero_iff (X : ChainComplex 𝓐 ℕ) (Y : 𝓐) (f : X ⟶ X) (g : Y ⟶ Y) :
    (∀ i,
        IsZero
          (((ext i).obj (op <| ChainComplex.toBoundedHomotopyCategory.obj (X.mkEnd f))).obj <|
            (single _ 0).obj ⟨Y, g⟩)) ↔
      ∀ i,
        IsIso <|
          ((ext i).map (ChainComplex.toBoundedHomotopyCategory.map f).op).app _ -
            ((ext i).obj (op _)).map ((single _ 0).map g) :=
  by
  obtain ⟨P, _inst, fP, h1, h2⟩ :=
    exists_K_projective_replacement (chain_complex.to_bounded_homotopy_category.obj (X.mk_end f))
  let fP' :=
    (BoundedHomotopyCategory.forget _).map
      ((endomorphisms.forget _).mapBoundedHomotopyCategory.map fP ≫ (forget_mk_end X f).Hom)
  -- use that fP commutes with the given endomorphisms...
  have fP'_eq :
    fP' ≫ chain_complex.to_bounded_homotopy_category.map f =
      (HomotopyCategory.quotient _ _).map P.val.as.e ≫ fP' :=
    by
    dsimp only [ChainComplex.toBoundedHomotopyCategory_map, functor.comp_map]
    erw [← (HomotopyCategory.quotient _ _).map_comp]
    erw [← (HomotopyCategory.quotient _ _).map_comp]
    congr 1
    ext ((_ | i) | i)
    · dsimp only [forget_mk_end, HomologicalComplex.comp_f, endomorphisms.forget,
        functor.map_homological_complex_map_f, HomologicalComplex.Hom.isoOfComponents_hom_f]
      erw [iso.refl_hom, category.comp_id]
      erw [((Quot.out fP).f 0).comm]; rfl
    · apply limits.is_zero.eq_of_tgt; exact is_zero_zero _
    · dsimp only [forget_mk_end, HomologicalComplex.comp_f, endomorphisms.forget,
        functor.map_homological_complex_map_f, HomologicalComplex.Hom.isoOfComponents_hom_f]
      erw [iso.refl_hom, category.comp_id]
      erw [((Quot.out fP).f _).comm]; rfl
  skip
  have foo : ∀ h : ℤ → Prop, (∀ i, h i) ↔ ∀ i, h (-i) :=
    by
    intro h; constructor
    · intro h1 i; apply h1 (-i)
    · intro h1 i; specialize h1 (-i); rwa [neg_neg] at h1 
  convert homology_is_zero_iff_is_iso Y g P h2
  · apply propext
    rw [foo]
    apply forall_congr'
    intro i
    let this.1 :=
      Ext_iso (-i) P (chain_complex.to_bounded_homotopy_category.obj (HomologicalComplex.mkEnd X f))
        ((single (endomorphisms 𝓐) 0).obj
          { pt := Y
            e := g })
        fP
    rw [iso.is_zero_iff this]; clear this
    delta C₁
    apply iso.is_zero_iff
    let this.1 := hom_single_iso P ⟨Y, g⟩ i
    refine' iso.trans _ this; clear this
    let this.1 := (shift_single_iso 0 (-i) : single (endomorphisms 𝓐) 0 ⋙ _ ≅ _)
    change (preadditive_yoneda.flip.obj (op P)).obj _ ≅ (preadditive_yoneda.flip.obj (op P)).obj _
    apply (preadditive_yoneda.flip.obj (op P)).mapIso
    convert iso.app this ⟨Y, g⟩
    -- I ♥ you Lean, this just worked first time
    ring
  · apply propext
    rw [foo]
    apply forall_congr'
    intro i
    let j :
      ((Ext (-i)).obj (op (chain_complex.to_bounded_homotopy_category.obj X))).obj
          ((single 𝓐 0).obj Y) ≅
        (homology'Functor AddCommGroupCat (ComplexShape.up ℤ).symm i).obj (C₂ Y P) :=
      by
      -- need that post-composing with an iso sends quasi-isos to quasi-isos! More precisely:
      -- Above I sorried that if fP is a quasi-iso then so is
      -- ((endomorphisms.forget _).map_bounded_homotopy_category).map fP,
      -- however unfortunately we now need to post-compose with something
      -- which is close to, but not equal to, 𝟙.
      -- This should hopefully be straightforward
      have : HomotopyCategory.IsQuasiIso fP' := by dsimp only [fP']; rw [functor.map_comp];
        infer_instance
      refine' iso.trans (Ext_iso (-i) _ _ ((single 𝓐 0).obj Y) fP') _
      --      delta C₂,
      refine'
        iso.trans _ (hom_single_iso ((endomorphisms.forget 𝓐).mapBoundedHomotopyCategory.obj P) Y i)
      let this.1 := (shift_single_iso 0 (-i) : single 𝓐 0 ⋙ _ ≅ _)
      refine'
        (preadditive_yoneda.flip.obj
              (op ((endomorphisms.forget 𝓐).mapBoundedHomotopyCategory.obj P))).mapIso
          _
      let e := this.app Y
      refine' e ≪≫ eq_to_iso _
      ring_nf
    -- Goal is `is_iso f : A ⟶ A` iff `is_iso f' : A' ⟶ A'` and we have an
    -- iso `j : A ⟶ A'` so it suffices to prove that the square
    -- (with `j` on two sides) commutes.
    suffices
      j.hom ≫ (homology'Functor AddCommGroupCat (ComplexShape.up ℤ).symm i).map (map₂ Y g P) =
        (((Ext (-i)).map (chain_complex.to_bounded_homotopy_category.map f).op).app
              ((single 𝓐 0).obj Y) -
            ((Ext (-i)).obj (op (chain_complex.to_bounded_homotopy_category.obj X))).map
              ((single 𝓐 0).map g)) ≫
          j.hom
      by rw [← is_iso_iff_is_iso_comp_left j.hom, this, is_iso_iff_is_iso_comp_right]
    delta map₂
    rw [functor.map_sub, comp_sub, sub_comp]
    refine' congr_arg₂ _ _ _
    · dsimp only [j, iso.trans_hom, Ext_iso, Ext, Ext0, functor.map_iso_hom, functor.comp_map,
        whiskering_left_obj_map, whisker_left_app, functor.flip_obj_map, functor.flip_map_app,
        iso.op_hom]
      clear j
      simp only [nat_trans.naturality, nat_trans.naturality_assoc]
      erw [nat_trans.naturality_assoc, ← functor.map_comp_assoc]
      simp only [← op_comp, category.assoc]
      congr 1
      dsimp only [BoundedHomotopyCategory.replacementIso]
      rw [lift_unop_op]
      apply compatibility₁
      simp only [eq_to_hom_refl, category.comp_id]
      erw [fP'_eq]
      apply lift_unique
      erw [category.assoc]
      erw [BoundedHomotopyCategory.lift_lifts]
    · dsimp only [j, iso.trans_hom, Ext_iso, Ext, Ext0, functor.map_iso_hom, functor.comp_map,
        whiskering_left_obj_map, whisker_left_app, functor.flip_obj_map, functor.flip_map_app,
        iso.op_hom, functor.comp_obj, whiskering_left_obj_obj, unop_op, op_unop]
      clear j
      simp only [nat_trans.naturality, nat_trans.naturality_assoc, category.assoc, map₂_right]
      apply compatibility₂

open scoped ZeroObject

def singleUnEnd (X : Endomorphisms 𝓐) : ((single _ 0).obj X).unEnd ≅ (single _ 0).obj X.pt
    where
  Hom :=
    Quot.mk _
      { f := fun i =>
          show (ite (i = 0) X 0).pt ⟶ ite (i = 0) X.pt 0 from
            if hi : i = 0 then eqToHom (by simp only [if_pos hi]) else 0
        comm' := by
          rintro i j _
          change _ ≫ 0 = 0 ≫ _; simp }
  inv :=
    Quot.mk _
      { f := fun i =>
          show ite (i = 0) X.pt 0 ⟶ (ite (i = 0) X 0).pt from
            if hi : i = 0 then eqToHom (by simp only [if_pos hi]) else 0
        comm' := by
          rintro i j (rfl : _ = _)
          change _ ≫ 0 = 0 ≫ _; simp }
  hom_inv_id' := by
    change Quot.mk _ (_ ≫ _) = Quot.mk _ _
    apply congr_arg
    ext i
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    split_ifs
    · simp
    · rw [comp_zero, eq_comm, ← limits.is_zero.iff_id_eq_zero]
      change is_zero (ite (i = 0) X 0).pt
      rw [if_neg h]
      apply is_zero_X
      apply is_zero_zero
  inv_hom_id' := by
    change Quot.mk _ (_ ≫ _) = Quot.mk _ _
    apply congr_arg
    ext i
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    split_ifs
    · simp
    · rw [comp_zero, eq_comm, ← limits.is_zero.iff_id_eq_zero]
      change is_zero (ite (i = 0) X.X 0)
      rw [if_neg h]
      apply is_zero_zero

theorem singleUnEnd_e (X : Endomorphisms 𝓐) :
    (singleUnEnd X).Hom ≫ (single _ 0).map X.e = ((single _ 0).obj X).e ≫ (singleUnEnd X).Hom :=
  by
  change Quot.mk _ (_ ≫ _) = Quot.mk _ _
  apply congr_arg
  ext i
  change dite _ _ _ ≫ dite _ _ _ = _ ≫ dite _ _ _
  split_ifs
  · subst h
    rw [eq_to_hom_trans_assoc, ← category.assoc]
    congr
    simp
    rfl
  · simp

theorem single_e (X : Endomorphisms 𝓐) :
    (singleUnEnd X).Hom ≫ (single _ 0).map X.e ≫ (singleUnEnd X).inv = ((single _ 0).obj X).e := by
  rw [← category.assoc, iso.comp_inv_eq, single_unEnd_e]

open CategoryTheory.Preadditive

def embedSingle (X : 𝓐) :
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).obj
        ((HomologicalComplex.single 𝓐 (ComplexShape.down ℕ) 0).obj X) ≅
      (HomologicalComplex.single 𝓐 (ComplexShape.up ℤ) 0).obj X :=
  HomologicalComplex.Hom.isoOfComponents (by rintro ((_ | i) | i) <;> exact iso.refl _)
    (by
      rintro (i | i) j (rfl : _ = _)
      · apply is_zero.eq_of_tgt; exact is_zero_zero _
      · apply is_zero.eq_of_src; exact is_zero_zero _)

def toBoundedHomotopyCategorySingle (X : 𝓐) :
    ChainComplex.toBoundedHomotopyCategory.obj ((HomologicalComplex.single _ _ 0).obj X) ≅
      (single _ 0).obj X :=
  BoundedHomotopyCategory.mkIso <| (HomotopyCategory.quotient _ _).mapIso <| embedSingle X

theorem toBoundedHomotopyCategorySingle_naturality (X : 𝓐) (f : X ⟶ X) :
    (toBoundedHomotopyCategorySingle X).op.Hom ≫
        (ChainComplex.toBoundedHomotopyCategory.map
              ((HomologicalComplex.single 𝓐 (ComplexShape.down ℕ) 0).map f)).op ≫
          (toBoundedHomotopyCategorySingle X).op.inv =
      ((single _ 0).map f).op :=
  by
  dsimp only [iso.op]; simp only [← op_comp]; congr 1
  dsimp only [to_bounded_homotopy_category_single, ChainComplex.toBoundedHomotopyCategory,
    BoundedHomotopyCategory.mkIso, functor.comp_map, functor.map_iso, single,
    HomotopyCategory.single]
  erw [← functor.map_comp, ← functor.map_comp]; congr 1
  ext ((_ | i) | i)
  · simp only [category.assoc, HomologicalComplex.comp_f, HomologicalComplex.single_map_f,
      Int.ofNat_eq_coe, ZMod.nat_cast_self, eq_self_iff_true, eq_to_hom_refl, category.comp_id,
      category.id_comp, dite_eq_ite, if_true]
    dsimp only [embed_single, HomologicalComplex.Hom.isoOfComponents_hom_f, iso.refl_hom,
      HomologicalComplex.Hom.isoOfComponents_inv_f, iso.refl_inv]
    erw [category.comp_id, category.id_comp, HomologicalComplex.embed_nat_obj_down_up_zero_f]
    dsimp only [HomologicalComplex.single_map_f]
    simp only [eq_self_iff_true, eq_to_hom_refl, category.comp_id, category.id_comp, dite_eq_ite,
      if_true]
  · apply is_zero.eq_of_src; apply is_zero_zero
  · apply is_zero.eq_of_src; apply is_zero_zero

def toBoundedHomotopyCategoryMkEndSingle (X : 𝓐) (f : X ⟶ X) :
    ChainComplex.toBoundedHomotopyCategory.obj
        (((HomologicalComplex.single 𝓐 _ 0).obj X).mkEnd
          ((HomologicalComplex.single 𝓐 _ 0).map f)) ≅
      (single (Endomorphisms 𝓐) 0).obj ⟨X, f⟩ :=
  by
  refine' _ ≪≫ to_bounded_homotopy_category_single _
  apply functor.map_iso
  refine' HomologicalComplex.Hom.isoOfComponents _ _
  · rintro (_ | i) <;> refine' endomorphisms.mk_iso _ _
    · exact iso.refl _
    · dsimp [HomologicalComplex.mkEnd]
      simp only [category.id_comp, category.comp_id, if_pos rfl]; rfl
    · apply (is_zero_zero _).Iso; apply is_zero_X; apply is_zero_zero
    · apply (is_zero_zero _).eq_of_src
  · rintro _ i (rfl : _ = _); apply is_zero.eq_of_src; rw [is_zero_iff_id_eq_zero]; ext

theorem ext'_isZero_iff (X Y : 𝓐) (f : X ⟶ X) (g : Y ⟶ Y) :
    (∀ i, IsZero (((ext' i).obj (op <| Endomorphisms.mk X f)).obj <| Endomorphisms.mk Y g)) ↔
      ∀ i, IsIso <| ((ext' i).map f.op).app _ - ((ext' i).obj _).map g :=
  by
  convert Ext_is_zero_iff ((HomologicalComplex.single _ _ 0).obj X) Y (Functor.map _ f) g using 1
  · apply propext; apply forall_congr'; intro i
    apply iso.is_zero_iff; dsimp only [ext', functor.comp_obj, functor.flip_obj_obj]
    apply iso.app; apply functor.map_iso; dsimp only [functor.op_obj]; apply iso.op
    apply to_bounded_homotopy_category_mk_end_single
  · apply propext; apply forall_congr'; intro i
    let e := ((Ext i).mapIso (to_bounded_homotopy_category_single X).op).app ((single _ 0).obj Y)
    rw [← is_iso.comp_left_iff e.hom, ← is_iso.comp_right_iff _ e.inv]
    simp only [comp_sub, sub_comp, iso.app_hom, iso.app_inv, category.assoc, functor.map_iso_hom,
      functor.map_iso_inv, ← nat_trans.comp_app, ← functor.map_comp,
      to_bounded_homotopy_category_single_naturality]
    clear e
    dsimp only [ext', functor.comp_obj, functor.comp_map]
    congr 3
    rw [nat_trans.naturality, ← nat_trans.comp_app_assoc, ← functor.map_comp, iso.hom_inv_id,
      Functor.map_id, nat_trans.id_app, category.id_comp]
    rfl

end Endomorphisms

end CategoryTheory

