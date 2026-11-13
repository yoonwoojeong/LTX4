import Mathlib.CategoryTheory.Abelian.Projective
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Algebra.Group.ULift
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.Main
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact
import LiquidTensorExperiment.ForMathlib.Types
import LiquidTensorExperiment.Condensed.Adjunctions
import LiquidTensorExperiment.Condensed.TopComparison
import LiquidTensorExperiment.Condensed.FilteredColimits

#align_import condensed.ab

/-!
# Properties of the category of condensed abelian groups

-/


open CategoryTheory CategoryTheory.Limits

universe v u

-- Move this!
-- @[simps obj map {fully_applied := ff}] -- we probably don't want these as global simp lemmas
/-- `Ab.ulift.{v u}` is the universe lifting functor sending the category of abelian groups in
  universe `u` into those in universe `max v u`. -/
def Ab.ulift : Ab.{u} ⥤ Ab.{max v u}
    where
  obj M := AddCommGroupCat.of <| ULift.{v} M
  map M N f :=
    { toFun := fun x => ⟨f x.down⟩
      map_zero' := by ext1; apply f.map_zero
      map_add' := fun x y => by ext1; apply f.map_add }
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

@[simp]
theorem Ab.exact_ulift_map {A B C : Ab} (f : A ⟶ B) (g : B ⟶ C) :
    Exact (Ab.ulift.map f) (Ab.ulift.map g) ↔ Exact f g :=
  by
  let F := Ab.ulift.map f
  let G := Ab.ulift.map g
  change exact F G ↔ _
  rw [AddCommGroupCat.exact_iff]
  rw [AddCommGroupCat.exact_iff]
  constructor
  · intro h
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have : ULift.up (f x) ∈ F.range := ⟨⟨x⟩, rfl⟩
      rw [h] at this 
      change _ = _ at this 
      apply_fun fun e => e.down at this 
      exact this
    · rintro x hx; change _ = _ at hx 
      have : ULift.up x ∈ G.ker := by apply_fun ULift.up at hx ; exact hx
      rw [← h] at this 
      obtain ⟨y, hy⟩ := this
      apply_fun fun e => e.down at hy 
      rw [← hy]
      use y.down, rfl
  · intro h
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      ext
      change _ ∈ g.ker
      rw [← h]
      use x.down, rfl
    · intro x hx
      change _ = _ at hx 
      apply_fun fun e => e.down at hx 
      change _ ∈ g.ker at hx 
      rw [← h] at hx 
      obtain ⟨y, hy⟩ := hx
      use y
      ext
      exact hy

namespace Condensed

--instance : preadditive (Condensed Ab.{u+1}) := by admit
noncomputable section

-- Sanity check
example {J : Type (u + 1)} [SmallCategory J] [IsFiltered J] :
    Limits.PreservesColimitsOfShape J (forget Ab.{u + 1}) := by infer_instance

-- this is now available in `condensed/projective_resolutions.lean`...
--instance : enough_projectives (Condensed Ab.{u+1}) := by admit
instance : IsRightAdjoint (sheafToPresheaf _ _ : Condensed Ab.{u + 1} ⥤ _)
    where
  left := presheafToSheaf _ _
  adj := sheafificationAdjunction _ _

@[simps (config := { fullyApplied := false }) obj map]
def forgetToCondensedType : Condensed Ab.{u + 1} ⥤ CondensedSet
    where
  obj F :=
    ⟨F.val ⋙ forget _, by
      cases' F with F hF
      rwa [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab)] at hF 
      infer_instance⟩
  map A B f := ⟨whiskerRight f.val _⟩

instance : IsRightAdjoint forgetToCondensedType
    where
  left := condensedSetToCondensedAb
  adj := condensedAbCondensedSetAdjunction

section

variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [TopologicalAddGroup A]

def OfTopAb.presheaf : Profinite.{u}ᵒᵖ ⥤ Ab.{u}
    where
  obj S := ⟨C(S.unop, A)⟩
  map S₁ S₂ f := AddMonoidHom.mk' (fun g => g.comp f.unop) fun g₁ g₂ => rfl
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

/-- The condensed abelian group associated with a topological abelian group -/
def ofTopAb : Condensed.{u} Ab.{u + 1}
    where
  val := OfTopAb.presheaf A ⋙ Ab.ulift.{u + 1}
  cond := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab)]
    swap; infer_instance
    let B := TopCat.of A
    change presheaf.isSheaf _ B.to_Condensed.val
    exact B.to_Condensed.cond

variable {A} {B : Type u} [AddCommGroup B] [TopologicalSpace B] [TopologicalAddGroup B]

def ofTopAbMap (f : A →+ B) (hf : Continuous f) : ofTopAb A ⟶ ofTopAb B
    where val :=
    whiskerRight
      { app := fun S =>
          by
          refine'
            AddMonoidHom.mk' (fun g => ⟨f ∘ show C(↥(Opposite.unop S), A) from g, hf.comp _⟩) _
          · exact g.continuous
          · intros; ext; exact f.map_add _ _
        naturality := fun S T g => rfl } Ab.ulift.{u + 1}

end

end Condensed

namespace CompHausFiltPseuNormGrp

open scoped NNReal

open PseudoNormedGroup ComphausFilteredPseudoNormedGroup

def Presheaf (A : CompHausFiltPseuNormGrp.{u}) (S : Profinite.{u}) : Type u :=
  { f : S → A // ∃ (c : ℝ≥0) (f₀ : S → filtration A c), Continuous f₀ ∧ f = coe ∘ f₀ }

namespace Presheaf

variable (A : CompHausFiltPseuNormGrp.{u}) (S : Profinite.{u})

@[ext]
theorem ext {A : CompHausFiltPseuNormGrp} {S : Profinite} (f g : Presheaf A S) :
    f.1 = g.1 → f = g :=
  Subtype.ext

instance : Zero (Presheaf A S) :=
  ⟨⟨0, 0, 0, continuous_zero, rfl⟩⟩

instance : Neg (Presheaf A S) :=
  ⟨fun f =>
    ⟨-f.1, by
      obtain ⟨_, c, f, hf, rfl⟩ := f
      refine' ⟨c, fun s => -f s, _, rfl⟩
      exact (continuous_neg' c).comp hf⟩⟩

instance : Add (Presheaf A S) :=
  ⟨fun f g =>
    ⟨f.1 + g.1, by
      obtain ⟨_, cf, f, hf, rfl⟩ := f
      obtain ⟨_, cg, g, hg, rfl⟩ := g
      refine' ⟨cf + cg, fun s => ⟨f s + g s, add_mem_filtration (f s).2 (g s).2⟩, _, rfl⟩
      have aux := hf.prod_mk hg
      exact (continuous_add' cf cg).comp aux⟩⟩

instance : Sub (Presheaf A S) :=
  ⟨fun f g =>
    ⟨f.1 - g.1, by
      obtain ⟨_, cf, f, hf, rfl⟩ := f
      obtain ⟨_, cg, g, hg, rfl⟩ := g
      refine' ⟨cf + cg, fun s => ⟨f s - g s, sub_mem_filtration (f s).2 (g s).2⟩, _, rfl⟩
      have aux := hf.prod_mk ((continuous_neg' cg).comp hg)
      simp only [sub_eq_add_neg]
      exact (continuous_add' cf cg).comp aux⟩⟩

variable {A S}

protected def nsmul (n : ℕ) (f : Presheaf A S) : Presheaf A S :=
  ⟨n • f.1, by
    obtain ⟨_, c, f, hf, rfl⟩ := f
    refine' ⟨n * c, fun s => ⟨n • f s, nat_smul_mem_filtration _ _ _ (f s).2⟩, _, rfl⟩
    exact continuous_nsmul _ _ _ hf⟩

protected def zsmul (n : ℤ) (f : Presheaf A S) : Presheaf A S :=
  ⟨n • f.1, by
    obtain ⟨_, c, f, hf, rfl⟩ := f
    refine' ⟨n.natAbs * c, fun s => ⟨n • f s, int_smul_mem_filtration _ _ _ (f s).2⟩, _, rfl⟩
    exact continuous_zsmul _ _ _ hf⟩

variable (A S)

instance : AddCommGroup (Presheaf A S) :=
  { Presheaf.hasSub A S,
    Presheaf.hasNeg A S with
    zero := 0
    add := (· + ·)
    nsmul := Presheaf.nsmul
    zsmul := Presheaf.zsmul
    add_assoc := by intros; ext; exact add_assoc _ _ _
    zero_add := by intros; ext; exact zero_add _
    add_zero := by intros; ext; exact add_zero _
    add_comm := by intros; ext; exact add_comm _ _
    add_left_neg := by intros; ext; exact add_left_neg _
    sub_eq_add_neg := by intros; ext; exact sub_eq_add_neg _ _
    nsmul_zero := by intros; ext; exact zero_nsmul _
    nsmul_succ := by intros; ext; exact succ_nsmul _ _
    zsmul_zero' := by intros; ext; exact zero_zsmul _
    zsmul_succ' := by intros; ext; exact AddCommGroup.zsmul_succ' _ _
    zsmul_neg' := by intros; ext; exact AddCommGroup.zsmul_neg' _ _ }

@[simps (config := { fullyApplied := false }) apply]
def comap (A : CompHausFiltPseuNormGrp) {S T : Profinite} (φ : S ⟶ T) : Presheaf A T →+ Presheaf A S
    where
  toFun f :=
    ⟨f.1 ∘ φ, by
      obtain ⟨_, c, f, hf, rfl⟩ := f
      refine' ⟨c, f ∘ φ, hf.comp φ.continuous, rfl⟩⟩
  map_zero' := rfl
  map_add' := by intros; rfl

@[simps (config := { fullyApplied := false }) apply]
def map {A B : CompHausFiltPseuNormGrp} (φ : A ⟶ B) (S : Profinite) : Presheaf A S →+ Presheaf B S
    where
  toFun f :=
    ⟨φ ∘ f.1, by
      obtain ⟨_, c, f, hf, rfl⟩ := f
      obtain ⟨d, hd⟩ := φ.bound
      let e : filtration A c → filtration B (d * c) := fun t => ⟨φ t, hd t.2⟩
      have he : Continuous e := by apply φ.continuous; intros; rfl
      refine' ⟨d * c, e ∘ f, he.comp hf, rfl⟩⟩
  map_zero' := by ext; exact φ.map_zero
  map_add' := by intros; ext; exact φ.map_add _ _

end Presheaf

open Opposite

/-- Given `A : CompHausFiltPseuNormGrp`, this is the presheaf which sends a profinite set
`S` to the collection of functions `f : S → A` such that there exists some `r : ℝ≥0`
and some continuous map `g : S → A_{≤ r}`, where `f` is the composition of `g` with
the inclusion of `A_{≤ r}` into `A`.
This turns out to be a proetale sheaf, and thus defines a condensed abelian group.
See `to_Condensed` below.
-/
@[simps (config := { fullyApplied := false }) obj map]
def presheaf (A : CompHausFiltPseuNormGrp.{u}) : Profinite.{u}ᵒᵖ ⥤ Ab
    where
  obj S := ⟨Presheaf A (unop S)⟩
  map S T φ := Presheaf.comap A φ.unop
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

@[simps (config := { fullyApplied := false }) app]
def presheaf.map {A B : CompHausFiltPseuNormGrp} (φ : A ⟶ B) : presheaf A ⟶ presheaf B
    where
  app S := Presheaf.map φ (unop S)
  naturality := by intros; rfl

@[simp]
theorem presheaf.map_id (A : CompHausFiltPseuNormGrp) : presheaf.map (𝟙 A) = 𝟙 _ := by ext; rfl

@[simp]
theorem presheaf.map_comp {A B C : CompHausFiltPseuNormGrp} (f : A ⟶ B) (g : B ⟶ C) :
    presheaf.map (f ≫ g) = presheaf.map f ≫ presheaf.map g := by ext; rfl

--set_option pp.universes true
theorem presheaf_comp_ulift_is_sheaf_aux_equalizer (A : CompHausFiltPseuNormGrp.{u}) :
    (A.presheaf ⋙
        Ab.ulift.{u + 1, u} ⋙ forget.{u + 2, u + 1, u + 1} Ab.{u + 1}).EqualizerCondition :=
  by
  intro X B π hh
  constructor
  · rintro ⟨x⟩ ⟨y⟩ h
    ext t
    obtain ⟨t, rfl⟩ := hh t
    apply_fun fun e => e.val.down.val t at h 
    exact h
  · rintro ⟨⟨⟨t, c, t', ht', ht⟩⟩, h⟩
    let E : TopCat := TopCat.of (filtration A c)
    let t'' : Profinite.to_Top.obj X ⟶ E := ⟨t', ht'⟩
    have hw :
      Profinite.toTopCat.{u}.map (Profinite.pullback.fst.{u} π π) ≫ t'' =
        Profinite.toTopCat.{u}.map (Profinite.pullback.snd.{u} π π) ≫ t'' :=
      by
      dsimp at h 
      ext i
      dsimp [Profinite.pullback.fst, Profinite.pullback.snd]
      apply_fun fun e => e.down.val i at h 
      change (coe ∘ t') i.val.fst = (coe ∘ t') i.val.snd
      rw [← ht]
      exact h
    let w := Profinite.descendToTop π t'' hh hw
    refine' ⟨⟨⟨_, c, w, w.2, rfl⟩⟩, _⟩
    ext : 3
    dsimp
    rw [ht]
    ext i
    dsimp [CompHausFiltPseuNormGrp.presheaf, Ab.ulift, Functor.mapToEqualizer]
    have := Profinite.π_descendToTop π t'' hh hw
    apply_fun fun e => (e i).val at this ; exact this

theorem presheaf_comp_ulift_isSheaf (A : CompHausFiltPseuNormGrp.{u}) :
    Presheaf.IsSheaf proetaleTopology (presheaf A ⋙ Ab.ulift.{u + 1}) :=
  by
  rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab)]
  swap; infer_instance
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  erw [(Functor.isProetaleSheafOfTypes_tFAE (A.Presheaf ⋙ Ab.ulift.{u + 1} ⋙ forget _)).out 0 5]
  refine' ⟨_, _, _⟩
  · dsimp [Functor.EmptyCondition]
    constructor
    · intro a b h; ext ⟨⟩
    · intro x; dsimp
      refine' ⟨⟨⟨fun x => x.elim, 0, fun x => x.elim, by continuity, _⟩⟩, _⟩
      · ext ⟨⟩
      · cases x; rfl
  · intro X Y
    constructor
    · rintro ⟨x⟩ ⟨y⟩ h; dsimp at h 
      ext : 2
      dsimp
      ext (t | t)
      · apply_fun fun e => e.fst.down.val t at h ; exact h
      · apply_fun fun e => e.snd.down.val t at h ; exact h
    · rintro ⟨⟨f, c, f', hf', hf⟩, ⟨g, d, g', hg', hg⟩⟩
      let p : X.sum Y → A := fun t => Sum.recOn t f g
      let e : ℝ≥0 := c ⊔ d
      haveI : Fact (c ≤ e) := ⟨le_sup_left⟩
      haveI : Fact (d ≤ e) := ⟨le_sup_right⟩
      let p' : X.sum Y → filtration A e := fun t => Sum.recOn t (cast_le ∘ f') (cast_le ∘ g')
      have hp' : Continuous p' :=
        by
        have aux1 : p' ∘ Sum.inl = cast_le ∘ f' := by ext <;> rfl
        have aux2 : p' ∘ Sum.inr = cast_le ∘ g' := by ext <;> rfl
        simp only [continuous_sup_dom, continuous_coinduced_dom, aux1, aux2]
        exact ⟨(continuous_cast_le _ _).comp hf', (continuous_cast_le _ _).comp hg'⟩
      have hh : p = coe ∘ p' := by
        ext (a | a)
        · apply_fun fun u => u a at hf ; exact hf
        · apply_fun fun u => u a at hg ; exact hg
      refine' ⟨⟨⟨p, e, p', hp', hh⟩⟩, _⟩
      ext <;> rfl
  · apply Presheaf_comp_ulift_is_sheaf_aux_equalizer

/-- Given `A : CompHausFiltPseuNormGrp`, this is the condensed abeliian group
which, as a presheaf, sends a profinite set `S` to the collection of
functions `f : S → A` such that there exists some `r : ℝ≥0`
and some continuous map `g : S → A_{≤ r}`, where `f` is the composition of `g` with
the inclusion of `A_{≤ r}` into `A`.

NOTE: For silly universe reasons, we need to apply a `ulift` as well.
-/
@[simps (config := { fullyApplied := false }) obj map]
def toCondensed : CompHausFiltPseuNormGrp.{u} ⥤ Condensed.{u} Ab.{u + 1}
    where
  obj A :=
    { val := presheaf A ⋙ Ab.ulift.{u + 1}
      cond := presheaf_comp_ulift_isSheaf _ }
  map A B f := ⟨whiskerRight (presheaf.map f) _⟩
  map_id X := by ext : 2; dsimp; simp
  map_comp X Y Z f g := by ext : 2; dsimp; simp

section

-- #check Top.to_Condensed
variable (A : CompHausFiltPseuNormGrp.{u})

@[simps]
def level : ℝ≥0 ⥤ CompHaus.{u}
    where
  obj r := CompHaus.of <| filtration A r
  map r s h :=
    { toFun := castLe' h.le
      continuous_toFun :=
        letI : Fact (r ≤ s) := ⟨h.le⟩
        continuous_cast_le _ _ }
  map_id r := by ext; rfl
  map_comp r s t h1 h2 := by ext; rfl

@[simps]
def levelCondensedDiagram : ℝ≥0 ⥤ CondensedSet.{u} :=
  A.level ⋙ compHausToTop.{u} ⋙ topToCondensed.{u}

@[simps]
def levelCondensedDiagram' : AsSmall.{u + 1} ℝ≥0 ⥤ CondensedSet.{u} :=
  AsSmall.down ⋙ A.levelCondensedDiagram

def levelCondensedDiagramCocone : Cocone A.levelCondensedDiagram'
    where
  pt := condensedAbToCondensedSet.obj (toCondensed.obj A)
  ι :=
    { app := fun r =>
        Sheaf.Hom.mk <|
          { app := fun S f => ULift.up <| ⟨_, ULift.down r, f.down.1, f.down.2, rfl⟩
            naturality := fun S T f => by ext; rfl }
      naturality := fun r s h => by ext; rfl }

def colimitIsoCondensedObjAuxFun (X) :
    let E := A.levelCondensedDiagram' ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op X)
    (types.filteredColimitCocone E).pt → A.presheaf X :=
  let E := A.levelCondensedDiagram' ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op X)
  fun t =>
  @Quotient.liftOn' (Σ j : AsSmall.{u + 1} ℝ≥0, E.obj j) (A.presheaf X)
    (types.filteredColimitSetoid E) t (fun f => ⟨_, ULift.down f.1, f.2.down.1, f.2.down.2, rfl⟩)
    (by
      rintro ⟨i, x⟩ ⟨j, y⟩ ⟨e, u, v, h⟩
      ext q : 2
      dsimp [level_Condensed_diagram, level_Condensed_diagram'] at *
      apply_fun fun e => (e.down q).1 at h ; exact h)

theorem colimitIsoCondensedObjAuxFun_bijective (X) :
    Function.Bijective (colimitIsoCondensedObjAuxFun A X) :=
  by
  constructor
  · rintro ⟨⟨⟨i⟩, f⟩⟩ ⟨⟨⟨j⟩, g⟩⟩ h; dsimp [colimit_iso_Condensed_obj_aux_fun] at h ⊢
    simp only [Subtype.mk_eq_mk] at h 
    apply Quotient.sound'
    use⟨i ⊔ j⟩, ⟨le_sup_left⟩, ⟨le_sup_right⟩
    ext q
    dsimp [level_Condensed_diagram']; apply_fun fun e => e q at h ; exact h
  · rintro ⟨f, c, g, hg, hf⟩
    use Quotient.mk'' ⟨⟨c⟩, ⟨⟨g, hg⟩⟩⟩; ext tt; dsimp; rw [hf]; rfl

-- We would have to use `some` to define the inverse of this equiv, so we may as well just use
-- `equiv.of_bijective`
@[simps]
def colimitIsoCondensedObjAux (X) :
    let E := A.levelCondensedDiagram' ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op X)
    (types.filteredColimitCocone E).pt ≃ A.presheaf X :=
  Equiv.ofBijective (A.colimitIsoCondensedObjAuxFun X) (A.colimitIsoCondensedObjAuxFun_bijective X)

/-
let E := A.level_Condensed_diagram' ⋙ Sheaf_to_presheaf _ _ ⋙ (evaluation _ _).obj (op X) in
  (types.filtered_colimit_cocone E).X ≃ A.presheaf X :=
let E := A.level_Condensed_diagram' ⋙ Sheaf_to_presheaf _ _ ⋙ (evaluation _ _).obj (op X) in
equiv.of_bijective
(λ t, @quotient.lift_on' (Σ (j : as_small.{u+1} ℝ≥0), E.obj j) (A.presheaf X)
  (types.filtered_colimit_setoid E) t
  (λ f, ⟨_,ulift.down f.1, f.2.down.1, f.2.down.2, rfl⟩) begin
    rintros ⟨i,x⟩ ⟨j,y⟩ ⟨e,u,v,h⟩,
    ext q : 2,
    dsimp [level_Condensed_diagram, level_Condensed_diagram'] at *,
    apply_fun (λ e, (e.down q).1) at h, exact h
  end)
begin
  split,
  { rintros ⟨⟨⟨i⟩,f⟩⟩ ⟨⟨⟨j⟩,g⟩⟩ h, dsimp at h ⊢, apply quotient.sound',
    simp only [subtype.mk_eq_mk] at h, use [⟨i ⊔ j⟩, ⟨le_sup_left⟩, ⟨le_sup_right⟩],
    ext q,
    dsimp [level_Condensed_diagram'], apply_fun (λ e, e q) at h, exact h },
  { rintros ⟨f,c,g,hg,hf⟩,
    use quotient.mk' ⟨⟨c⟩,⟨⟨g,hg⟩⟩⟩, ext tt, dsimp, rw hf }
end
-/
def colimitIsoCondensedObjAuxNatIso :
    (filteredCocone.{u} A.levelCondensedDiagram').pt.val ≅
      (condensedAbToCondensedSet.{u}.obj (toCondensed.{u}.obj A)).val :=
  NatIso.ofComponents
    (fun X =>
      (isColimitOfPreserves ((evaluation _ _).obj X)
              (colimit.isColimit
                (A.levelCondensedDiagram' ⋙ sheafToPresheaf _ _))).coconePointUniqueUpToIso
          (colimit.isColimit _) ≪≫
        (colimit.isColimit _).coconePointUniqueUpToIso (types.filteredColimitCoconeIsColimit _) ≪≫
          Equiv.toIso ((A.colimitIsoCondensedObjAux X.unop).trans Equiv.ulift.symm))
    (by
      intro X Y f; dsimp [IsColimit.coconePointUniqueUpToIso]
      apply
        (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ (Type (u + 1))).obj X)
            (colimit.isColimit
              (A.level_Condensed_diagram' ⋙
                Sheaf_to_presheaf proetaleTopology (Type (u + 1))))).hom_ext
      intro j; simp only [Category.assoc]
      slice_lhs 0 1 =>
        dsimp
        rw [← NatTrans.naturality]
      slice_lhs 2 3 =>
        erw [(CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ (Type (u + 1))).obj Y)
              (colimit.isColimit
                (A.level_Condensed_diagram' ⋙
                  Sheaf_to_presheaf proetaleTopology (Type (u + 1))))).fac]
      slice_lhs 2 3 => erw [colimit.ι_desc]
      slice_rhs 1 2 =>
        erw [(CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ (Type (u + 1))).obj X)
              (colimit.isColimit
                (A.level_Condensed_diagram' ⋙
                  Sheaf_to_presheaf proetaleTopology (Type (u + 1))))).fac]
      slice_rhs 1 2 => erw [colimit.ι_desc]
      ext; rfl)

def colimitIsoCondensedObj :
    colimit A.levelCondensedDiagram' ≅ condensedAbToCondensedSet.obj (toCondensed.obj A) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (filteredCoconeIsColimit _) ≪≫
    Sheaf.Iso.mk _ (condensedAbToCondensedSet.{u}.obj (toCondensed.{u}.obj A))
      A.colimitIsoCondensedObjAuxNatIso

def colimitToCondensedObj :
    colimit A.levelCondensedDiagram' ⟶ condensedAbToCondensedSet.obj (toCondensed.obj A) :=
  colimit.desc _ A.levelCondensedDiagramCocone

instance isIso_colimitToCondensedObj : IsIso A.colimitToCondensedObj :=
  by
  suffices A.colimit_to_Condensed_obj = A.colimit_iso_Condensed_obj.hom by rw [this]; infer_instance
  dsimp [colimit_iso_Condensed_obj, colimit_to_Condensed_obj]
  apply colimit.hom_ext; intro i
  dsimp [IsColimit.coconePointUniqueUpToIso]
  rw [colimit.ι_desc, colimit.ι_desc_assoc]
  dsimp [Sheaf.Iso.mk]
  ext T : 3; dsimp
  rw [← NatTrans.comp_app]
  dsimp [colimit_iso_Condensed_obj_aux_nat_iso, NatIso.ofComponents]
  slice_rhs 1 2 =>
    erw [(CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ (Type (u + 1))).obj T)
          (colimit.isColimit
            (A.level_Condensed_diagram' ⋙ Sheaf_to_presheaf proetaleTopology (Type (u + 1))))).fac]
  slice_rhs 1 2 => erw [colimit.ι_desc]
  ext; rfl

end

end CompHausFiltPseuNormGrp

@[simps (config := { fullyApplied := false }) obj map]
def CompHausFiltPseuNormGrp₁.toCondensed :
    CompHausFiltPseuNormGrp₁.{u} ⥤ Condensed.{u} Ab.{u + 1} :=
  cHFPNG₁ToCHFPNGₑₗ ⋙ CompHausFiltPseuNormGrp.toCondensed

