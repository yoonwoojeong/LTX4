import LiquidTensorExperiment.CombinatorialLemma.ProfiniteSetup

#align_import combinatorial_lemma.profinite

section

open CategoryTheory

open CategoryTheory.Limits

open ProFiltPseuNormGrpWithTinv₁

open scoped NNReal BigOperators

noncomputable section

universe u

variable (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' < 1)] (Λ : Type u) [PolyhedralLattice Λ]
  (S : Profinite.{u})

namespace PseudoNormedGroup

def sum' {c₁ c₂ : ℝ≥0} {M : Type u} [PseudoNormedGroup M] (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
    (∀ i : Fin n, PseudoNormedGroup.filtration M c₁) → PseudoNormedGroup.filtration M c₂ := fun t =>
  ⟨∑ i : Fin n, (t i).1, by
    apply filtration_mono
    rotate_left
    apply PseudoNormedGroup.sum_mem_filtration
    intro i hi; exact (t i).2
    simpa⟩

@[simp]
theorem coe_sum' {c₁ c₂ : ℝ≥0} {M : Type u} [PseudoNormedGroup M] (n : ℕ) (h : ↑n * c₁ ≤ c₂)
    (t : ∀ i : Fin n, PseudoNormedGroup.filtration M c₁) :
    (sum' n h t : M) = ∑ i : Fin n, (t i : M) :=
  rfl

theorem sum'_zero {c₁ c₂ : ℝ≥0} {M : Type u} [PseudoNormedGroup M] (h : ↑0 * c₁ ≤ c₂) :
    (sum' 0 h :
        (∀ i : Fin 0, PseudoNormedGroup.filtration M c₁) → PseudoNormedGroup.filtration M c₂) =
      fun _ => 0 :=
  by
  ext t
  simp only [sum', Fintype.univ_of_isEmpty, Subtype.val_eq_coe, Finset.sum_empty, Subtype.coe_mk,
    filtration.coe_zero]

theorem sum'_succ {c₁ c₂ : ℝ≥0} {M : Type u} [PseudoNormedGroup M] (n : ℕ)
    (h : ↑(n + 1) * c₁ ≤ c₂) :
    (sum' (n + 1) h :
        (∀ i : Fin (n + 1), PseudoNormedGroup.filtration M c₁) →
          PseudoNormedGroup.filtration M c₂) =
      castLe' (by simpa [add_mul] using h) ∘ add' ∘ fun t => ⟨sum' n le_rfl (Fin.tail t), t 0⟩ :=
  by
  ext t
  simp only [sum', Subtype.val_eq_coe, Subtype.coe_mk, coe_cast_le', add'_eq]
  rw [Fin.sum_univ_succ, add_comm]
  rfl

end PseudoNormedGroup

namespace ComphausFilteredPseudoNormedGroup

open PseudoNormedGroup

theorem continuous_sum' {c₁ c₂ : ℝ≥0} {M : Type u} [ComphausFilteredPseudoNormedGroup M] (n : ℕ)
    (h : ↑n * c₁ ≤ c₂) :
    Continuous
      (PseudoNormedGroup.sum' n h :
        (∀ i : Fin n, PseudoNormedGroup.filtration M c₁) → PseudoNormedGroup.filtration M c₂) :=
  by
  have :
    @PseudoNormedGroup.sum' _ _ M _ n h =
      PseudoNormedGroup.castLe' h ∘ PseudoNormedGroup.sum' n le_rfl :=
    by ext; rfl
  rw [this]
  refine' (@ComphausFilteredPseudoNormedGroup.continuous_castLe _ _ _ _ ⟨h⟩).comp _
  clear this h c₂
  induction' n with n ih
  · rw [PseudoNormedGroup.sum'_zero]; exact continuous_const
  rw [PseudoNormedGroup.sum'_succ]
  haveI : Fact (↑n * c₁ + c₁ ≤ ↑n.succ * c₁) := by
    simp only [Nat.cast_succ, add_mul, one_mul] <;> infer_instance
  refine'
    (ComphausFilteredPseudoNormedGroup.continuous_castLe _ _).comp
      ((ComphausFilteredPseudoNormedGroup.continuous_add' _ _).comp _)
  refine' Continuous.prod_mk (ih.comp _) (continuous_apply _)
  exact continuous_pi fun i => continuous_apply _

end ComphausFilteredPseudoNormedGroup

/-
namespace Profinite

def pow (X : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
Profinite.product (λ i : fin n, X)

def map_pow {X Y : Profinite.{u}} (f : X ⟶ Y) (n : ℕ) :
  X.pow n ⟶ Y.pow n :=
Profinite.product.lift _ $ λ n, Profinite.product.π _ n ≫ f

end Profinite
-/
namespace ProFiltPseuNormGrpWithTinv₁

@[simps]
def level : ℝ≥0 ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ Profinite.{u}
    where
  obj c :=
    { obj := fun X => Profinite.of <| PseudoNormedGroup.filtration X c
      map := fun X Y f => ⟨f.level _, f.continuous' _⟩
      map_id' := fun M => by ext; rfl
      map_comp' := fun M₁ M₂ M₃ f g => by ext; rfl }
  map c₁ c₂ h :=
    { app := fun X =>
        ⟨PseudoNormedGroup.castLe' h.le,
          by
          haveI : Fact (c₁ ≤ c₂) := ⟨h.le⟩
          apply ComphausFilteredPseudoNormedGroup.continuous_castLe⟩
      naturality' := fun M₁ M₂ f => by ext; rfl }
  map_id' c := by ext; rfl
  map_comp' c₁ c₂ c₃ h₁₂ h₂₃ := by ext; rfl

instance (c) : PreservesLimits ((level r').obj c) :=
  by
  change preserves_limits (pFPNGT₁ToPFPNG₁ₑₗ.{u} r' ⋙ ProFiltPseuNormGrp₁.level.obj c)
  apply (config := { instances := false }) limits.comp_preserves_limits
  constructor; constructor; intro J _; constructor

-- <-- looks like we have `preserves_limit` and not `preserves_limits`, but
-- it should be trivial to add, if needed.
variable {r'}

abbrev lvl (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (c : ℝ≥0) : Profinite.{u} :=
  ((level r').obj c).obj X

abbrev mapLvl {X Y : ProFiltPseuNormGrpWithTinv₁.{u} r'} (f : X ⟶ Y) (c : ℝ≥0) :
    X.lvl c ⟶ Y.lvl c :=
  ((level r').obj c).map f

@[reassoc]
theorem mapLvl_comp {X Y Z : ProFiltPseuNormGrpWithTinv₁.{u} r'} (f : X ⟶ Y) (g : Y ⟶ Z) (c : ℝ≥0) :
    map_lvl f c ≫ map_lvl g c = map_lvl (f ≫ g) c := by ext; rfl

abbrev castLvl {c₁ c₂ : ℝ≥0} (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (h : c₁ ≤ c₂) :
    X.lvl c₁ ⟶ X.lvl c₂ :=
  ((level r').map h.Hom).app _

@[reassoc]
theorem mapLvl_castLvl_eq {X Y : ProFiltPseuNormGrpWithTinv₁.{u} r'} (f : X ⟶ Y) (c₁ c₂ : ℝ≥0)
    (h : c₁ ≤ c₂) : map_lvl f c₁ ≫ cast_lvl Y h = cast_lvl X h ≫ map_lvl f c₂ := by ext; rfl

def sum {c₁ c₂ : ℝ≥0} (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
    (X.lvl c₁).pow n ⟶ X.lvl c₂ :=
  ⟨PseudoNormedGroup.sum' _ h, ComphausFilteredPseudoNormedGroup.continuous_sum' _ _⟩

@[simp]
theorem coe_sum {c₁ c₂ : ℝ≥0} (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
    ⇑(X.Sum n h) = PseudoNormedGroup.sum' n h :=
  rfl

theorem le₁ (N : ℕ) [Fact (0 < N)] (c d : ℝ≥0) : ↑N * (c / ↑N + d) ≤ c + ↑N * d :=
  by
  apply Eq.le
  rw [mul_add, add_left_inj, mul_div_cancel']
  norm_cast
  exact ne_of_gt (Fact.out _)

theorem le₂ (N : ℕ) (c d : ℝ≥0) : c ≤ c + ↑N * d :=
  le_self_add

/-- Given a `N : ℕ`, `c : ℝ≥0`, an `X : ProFiltPseuNormGrpWithTinv₁ r'`, and a
  `t : Profinite.punit ⟶ X.lvl c`, this constructs the pullback of `t` along the 2nd projection
  `(X.lvl (c/N + d))^n ×_{X.lvl (c + N * d)} X.lvl c → X.lvl c`.
-/
def gadget (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (N : ℕ) [Fact (0 < N)] (c d : ℝ≥0)
    (t : Profinite.punit.{u} ⟶ X.lvl c) : Profinite.{u} :=
  Profinite.pullback (Profinite.pullback.snd (X.Sum N (le₁ N c d)) (X.castLvl (le₂ N c d))) t

def mapGadget {X Y : ProFiltPseuNormGrpWithTinv₁.{u} r'} (f : X ⟶ Y) (N : ℕ) [Fact (0 < N)]
    (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ X.lvl c) (t' : Profinite.punit.{u} ⟶ Y.lvl c)
    (w : t ≫ map_lvl f c = t') : X.gadget N c d t ⟶ Y.gadget N c d t' :=
  Profinite.pullback.lift _ _
    (Profinite.pullback.fst _ _ ≫
      Profinite.pullback.lift _ _
        (Profinite.pullback.fst _ _ ≫
          Profinite.product.lift _ fun i => Profinite.product.π _ i ≫ map_lvl f _)
        (Profinite.pullback.snd _ _ ≫ map_lvl f _)
        (by
          simp only [category.assoc, map_lvl_cast_lvl_eq, ← Profinite.pullback.condition_assoc]
          ext ⟨⟨x₁, x₂⟩, hx⟩
          simp only [category.assoc, Profinite.coe_comp, Function.comp_apply, nat_trans.naturality]
          dsimp [Profinite.pullback.fst, Profinite.pullback.snd]
          rw [f.map_sum, Finset.sum_congr rfl]
          rintro i -
          rfl))
    (Profinite.pullback.snd _ _)
    (by rw [category.assoc, Profinite.pullback.lift_snd, Profinite.pullback.condition_assoc, w])

theorem mapGadget_comp {X Y Z : ProFiltPseuNormGrpWithTinv₁.{u} r'} (f : X ⟶ Y) (g : Y ⟶ Z) (N : ℕ)
    [Fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ X.lvl c)
    (t' : Profinite.punit.{u} ⟶ Y.lvl c) (t'' : Profinite.punit.{u} ⟶ Z.lvl c)
    (w : t ≫ map_lvl f c = t') (w' : t' ≫ map_lvl g c = t'') :
    map_gadget f N c d t t' w ≫ map_gadget g N c d t' t'' w' =
      map_gadget (f ≫ g) N c d t t'' (by subst t''; subst t'; rw [category.assoc, map_lvl_comp]) :=
  by
  dsimp only [map_gadget]
  refine' Profinite.pullback.hom_ext _ _ _ _ _ _ <;>
    simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
      Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc]
  rfl

@[simps]
def gadgetDiagram {J : Type u} [SmallCategory J] {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'}
    (C : Cone K) (N : ℕ) [Fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.pt.lvl c) :
    J ⥤ Profinite.{u}
    where
  obj j := (K.obj j).gadget N c d (t ≫ map_lvl (C.π.app _) c)
  map i j f := map_gadget (K.map f) _ _ _ _ _ (by rw [category.assoc, map_lvl_comp, cone.w])
  map_id' i := by simp only [K.map_id]; ext <;> rfl
  map_comp' i j k h₁ h₂ := by simp only [K.map_comp]; ext <;> rfl

@[simps]
def gadgetDiagramFstSnd {J : Type u} [SmallCategory J] {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'}
    (C : Cone K) (N : ℕ) [Fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.pt.lvl c) :
    gadget_diagram C N c d t ⟶ K ⋙ (level r').obj c
    where
  app j := Profinite.pullback.fst _ _ ≫ Profinite.pullback.snd _ _
  naturality' i j h := by ext <;> rfl

@[simps]
def gadgetDiagramFstFst {J : Type u} [SmallCategory J] {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'}
    (C : Cone K) (N : ℕ) [Fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.pt.lvl c)
    (i : Fin N) : gadget_diagram C N c d t ⟶ K ⋙ (level r').obj (c / ↑N + d)
    where
  app j := Profinite.pullback.fst _ _ ≫ Profinite.pullback.fst _ _ ≫ Profinite.product.π _ i
  naturality' i j h := by ext <;> rfl

@[simps]
def gadgetCone {J : Type u} [SmallCategory J] {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : Cone K)
    (N : ℕ) [Fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.pt.lvl c) :
    Cone (gadget_diagram C N c d t)
    where
  pt := C.pt.gadget N c d t
  π :=
    { app := fun j => map_gadget (C.π.app _) _ _ _ _ _ rfl
      naturality' := fun i j h => by dsimp; rw [category.id_comp, map_gadget_comp]; congr;
        rw [cone.w] }

theorem gadget_cone_lift_fst_snd {J : Type u} [SmallCategory J]
    {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : Cone K)
    (hC : ∀ a : ℝ≥0, IsLimit (((level r').obj a).mapCone C)) (N : ℕ) [Fact (0 < N)] (c d : ℝ≥0)
    (t : Profinite.punit.{u} ⟶ C.pt.lvl c) (S : Cone (gadget_diagram C N c d t)) :
    (hC c).lift ((Cones.postcompose (gadget_diagram_fst_snd C N c d t)).obj S) =
      Profinite.punit.elim S.pt ≫ t :=
  by
  refine' ((hC c).uniq ((cones.postcompose (gadgetDiagramFstSnd.{u} C N c d t)).obj S) _ _).symm
  intro j
  simp only [functor.map_cone_π_app, cones.postcompose_obj_π, nat_trans.comp_app,
    gadget_diagram_fst_snd_app, Profinite.pullback.condition]
  simp only [← category.assoc]; congr 2; ext

theorem gadget_cone_lift_aux {J : Type u} [SmallCategory J] {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'}
    (C : Cone K) (hC : ∀ a : ℝ≥0, IsLimit (((level r').obj a).mapCone C)) (N : ℕ) [Fact (0 < N)]
    (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.pt.lvl c) (S : Cone (gadget_diagram C N c d t)) :
    let η i := gadget_diagram_fst_fst C N c d t i
    let γ := gadget_diagram_fst_snd C N c d t
    let S' i := (Cones.postcompose (η i)).obj S
    let F : ∀ i, S.pt ⟶ _ := fun i => (hC _).lift (S' i)
    let S'' := (Cones.postcompose γ).obj S
    Profinite.product.lift (fun i : Fin N => C.pt.lvl (c / ↑N + d)) F ≫ C.pt.Sum N (le₁ _ _ _) =
      (hC c).lift S'' ≫ C.pt.castLvl (le₂ _ _ _) :=
  by
  have h₁ := le₁ N c d
  have h₂ := le₂ N c d
  rintro η γ S' F S''
  let γ' : gadget_diagram C N c d t ⟶ K ⋙ (level r').obj (c + ↑N * d) :=
    γ ≫ whisker_left _ ((level r').map h₂.hom)
  let T'' := (cones.postcompose γ').obj S
  have : (hC c).lift S'' ≫ C.X.cast_lvl h₂ = (hC _).lift T'' :=
    by
    apply (hC _).uniq T''
    intro j
    have := (hC c).fac S'' j
    dsimp at this ⊢
    simp [category.assoc, ← reassoc_of this]
  rw [this]
  apply (hC (c + ↑N * d)).uniq T''
  intro j
  dsimp
  simp only [category.assoc]
  have :
    C.X.sum N h₁ ≫ ((level r').obj (c + ↑N * d)).map (C.π.app j) =
      (Profinite.product.lift _ fun i => Profinite.product.π _ i ≫ map_lvl (C.π.app _) _) ≫
        ProFiltPseuNormGrpWithTinv₁.sum _ N h₁ :=
    by
    ext x
    dsimp
    erw [(C.π.app j).toAddMonoidHom.map_sum]
    rfl
  rw [this]
  erw [← Profinite.pullback.condition]
  simp only [← category.assoc]
  congr 1
  apply Profinite.product.hom_ext
  intro a
  dsimp [F]
  simp only [category.assoc, Profinite.product.lift_π, Profinite.product.lift_π_assoc]
  erw [(hC (c / ↑N + d)).fac (S' a) j]
  rfl

-- lemma gadget_cone_lift_fst_fst {J : Type u} [small_category J]
--   {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
--   (hC : ∀ a : ℝ≥0, is_limit (((level r').obj a).map_cone C))
--   (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c)
--   (S : cone (gadget_diagram C N c d t)) (i : fin N) (j : J)
--   (g : ((K.obj j).lvl (c / ↑N + d)).pow N ⟶ (((level r').obj (c / ↑N + d)).map_cone C).X) :
--   (hC (c / N + d)).lift ((cones.postcompose (gadget_diagram_fst_fst C N c d t i)).obj S) =
--     S.π.app j ≫ Profinite.pullback.fst
--       (Profinite.pullback.snd ((K.obj j).sum N _) ((K.obj j).cast_lvl _))
--       (t ≫ map_lvl (C.π.app j) c) ≫
--         Profinite.pullback.fst ((K.obj j).sum N _) ((K.obj j).cast_lvl _) ≫ g :=
-- begin
--   refine ((hC _).uniq
--     ((cones.postcompose (gadget_diagram_fst_fst.{u} C N c d t i)).obj S) _ _).symm,
--   intro j,
--   have := (hC _).fac ((cones.postcompose (gadget_diagram_fst_fst.{u} C N c d t i)).obj S),
--   simp only [functor.map_cone_π_app, cones.postcompose_obj_π,
--     nat_trans.comp_app, gadget_diagram_fst_snd_app],
--   rw Profinite.pullback.condition,
--   simp only [← category.assoc], congr' 2, ext,
-- end
def gadgetConeIsLimit {J : Type u} [SmallCategory J] {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'}
    (C : Cone K) (hC : ∀ a : ℝ≥0, IsLimit (((level r').obj a).mapCone C)) (N : ℕ) [Fact (0 < N)]
    (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.pt.lvl c) : IsLimit (gadget_cone C N c d t)
    where
  lift S :=
    Profinite.pullback.lift _ _
      (Profinite.pullback.lift _ _
        (Profinite.product.lift _ fun i =>
          (hC _).lift ((Cones.postcompose (gadget_diagram_fst_fst C N c d t i)).obj S))
        ((hC _).lift ((Cones.postcompose (gadget_diagram_fst_snd C N c d t)).obj S))
        (gadget_cone_lift_aux _ _ _ _ _ _ _))
      (Profinite.punit.elim _)
      (by rw [Profinite.pullback.lift_snd, eq_comm, gadget_cone_lift_fst_snd])
  fac S j := by
    dsimp only [gadget_cone_π_app, map_gadget]
    apply Profinite.pullback.hom_ext <;>
      simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
        Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc]
    swap; · ext
    apply Profinite.pullback.hom_ext <;>
      simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
        Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc]
    · apply Profinite.product.hom_ext; intro i
      simp only [category.assoc, Profinite.product.lift_π, Profinite.product.lift_π_assoc]
      exact (hC _).fac ((cones.postcompose (gadgetDiagramFstFst.{u} C N c d t i)).obj S) j
    · rw [gadget_cone_lift_fst_snd, Profinite.pullback.condition]
      simp only [← category.assoc]; congr 2; ext
  uniq S f h :=
    by
    apply Profinite.pullback.hom_ext <;>
      simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
        Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc]
    swap; · ext
    apply Profinite.pullback.hom_ext <;>
      simp only [category.assoc, Profinite.pullback.lift_fst, Profinite.pullback.lift_snd,
        Profinite.pullback.lift_fst_assoc, Profinite.pullback.lift_snd_assoc]
    swap
    · rw [Profinite.pullback.condition, gadget_cone_lift_fst_snd, ← category.assoc]; congr 1; ext
    apply Profinite.product.hom_ext
    intro i
    rw [Profinite.product.lift_π]
    refine'
      (hC (c / N + d)).uniq ((cones.postcompose (gadgetDiagramFstFst.{u} C N c d t i)).obj S) _ _
    intro j
    dsimp
    rw [← h]
    dsimp [gadget_cone, map_gadget]
    simp

end ProFiltPseuNormGrpWithTinv₁

namespace Lem98

open ProFiltPseuNormGrpWithTinv₁

instance (c : ℝ≥0) : PreservesLimits (homFunctor.{u} r' Λ ⋙ (level r').obj c) :=
  by
  change preserves_limits (homFunctor r' Λ ⋙ pFPNGT₁ToPFPNG₁ₑₗ r' ⋙ ProFiltPseuNormGrp₁.level.obj c)
  infer_instance

def homDiagram : DiscreteQuotient S ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
  S.fintypeDiagram ⋙ fintypeLbar.{u, u} r' ⋙ homFunctor r' Λ

/-- The cone over `hom_diagram` whose cone point is defeq to `Hom(Λ, Lbar S)`.
See lemma below. -/
def homLbarCone : Cone (hom_diagram r' Λ S) :=
  (homFunctor r' Λ).mapCone (limit.cone (S.fintypeDiagram ⋙ fintypeLbar.{u, u} r'))

@[simp]
theorem homLbarCone_pt :
    (hom_Lbar_cone r' Λ S).pt = (homFunctor.{u} r' Λ).obj ((Lbar.functor.{u, u} r').obj S) :=
  rfl

/-- The cone with cone point `Hom(Λ, Lbar S)_{≤ c}` is indeed a limit cone. -/
def homLbarConeIsLimit (c) : IsLimit (((level r').obj c).mapCone (hom_Lbar_cone r' Λ S)) :=
  by
  let E := limit.cone (S.fintype_diagram ⋙ fintypeLbar.{u, u} r')
  change is_limit ((homFunctor.{u} r' Λ ⋙ (level r').obj c).mapCone E)
  apply is_limit_of_preserves (homFunctor.{u} r' Λ ⋙ (level r').obj c) (limit.is_limit _)
  infer_instance

-- This should follow from the finite case of lem98.
theorem gadget_nonempty (N : ℕ) [Fact (0 < N)] (T : DiscreteQuotient S) (c) (t) :
    Nonempty ((gadgetDiagram (hom_Lbar_cone r' Λ _) N c (d Λ N) t).obj T) :=
  by
  obtain ⟨h⟩ := lem98Finite Λ T N
  specialize h c
  let u : (hom_Lbar_cone r' Λ S).pt ⟶ (hom_diagram r' Λ S).obj T := (hom_Lbar_cone r' Λ S).π.app T
  let t' := t ≫ ((level r').obj c).map u
  specialize h (t' PUnit.unit).1 (t' PUnit.unit).2
  swap; infer_instance
  obtain ⟨e, he1, he2⟩ := h
  -- Now use `e`, `t'`, `he1` and `he2` to finish off the proof...
  refine' ⟨⟨⟨⟨(_, _), _⟩, _⟩, _⟩⟩
  · intro i; refine' ⟨e i, he2 i⟩
  · let x := t' PUnit.unit; exact ⟨x.1, x.2⟩
  · apply Subtype.ext; exact he1.symm
  · exact PUnit.unit
  · apply Subtype.ext; rfl

-- This should follow from Tychonoff and `gadget_nonempty`.
theorem key (N : ℕ) [Fact (0 < N)] (c) (t) :
    Nonempty (((homFunctor r' Λ).obj ((Lbar.functor.{u, u} r').obj S)).gadget N c (d Λ N) t) :=
  by
  let E := gadget_cone (hom_Lbar_cone r' Λ _) N c (d Λ N) t
  let hE : is_limit E := gadget_cone_is_limit _ _ _ _ _ _
  swap; · intro a; apply hom_Lbar_cone_is_limit
  let E' := Profinite.to_Top.map_cone E
  let hE' : is_limit E' := is_limit_of_preserves _ hE
  let G := gadget_diagram (hom_Lbar_cone r' Λ S) N c (d Λ N) t ⋙ Profinite.toTopCat
  let T : E'.X ≅ (TopCat.limitCone.{u, u} G).pt :=
    hE'.cone_point_unique_up_to_iso (TopCat.limitConeIsLimit G)
  suffices Nonempty (TopCat.limitCone.{u, u} G).pt by obtain ⟨a⟩ := this; exact ⟨T.inv a⟩
  apply (config := { instances := false }) TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system
  · infer_instance
  · intros; apply gadget_nonempty
  · intro j
    change CompactSpace ((gadget_diagram (hom_Lbar_cone r' Λ S) N c (d Λ N) t).obj j)
    infer_instance
  · intro j
    change T2Space ((gadget_diagram (hom_Lbar_cone r' Λ S) N c (d Λ N) t).obj j)
    infer_instance

/-- Lemma 9.8 of [Analytic], with somewhat restrictive universes -/
theorem main (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' < 1)] (Λ : Type u) [PolyhedralLattice Λ]
    (S : Profinite.{u}) (N : ℕ) [hN : Fact (0 < N)] :
    PseudoNormedGroup.Splittable (Λ →+ (Lbar.functor.{u, u} r').obj S) N (d Λ N) :=
  by
  constructor
  intro c u hu
  let t : Profinite.punit ⟶ ((homFunctor r' Λ).obj ((Lbar.functor.{u, u} r').obj S)).lvl c :=
    Profinite.fromPunit ⟨u, hu⟩
  obtain ⟨K, hK⟩ := key r' Λ S N c t
  rcases K with ⟨⟨⟨K₁, K₂⟩, hhK⟩, ⟨⟩⟩
  dsimp [t, Profinite.fromPunit, Profinite.pullback.snd] at hK 
  dsimp at hhK 
  use fun i => (K₁ i).1
  constructor
  · apply_fun fun e => e.val at hhK 
    change _ = K₂.val at hhK 
    apply_fun fun e => e.val at hK 
    rw [hK] at hhK 
    exact hhK.symm
  · intro i
    exact (K₁ i).2

end Lem98

-- A version with less restrictive universes. But we don't need that. Who cares about universes.
-- /-- Lemma 9.8 of [Analytic] -/
-- lemma lem98 (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
--   (Λ : Type*) [polyhedral_lattice Λ] (S : Profinite) (N : ℕ) [hN : fact (0 < N)] :
--   pseudo_normed_group.splittable (Λ →+ (Lbar.functor r').obj S) N (lem98.d Λ N) :=
-- begin
--   admit
-- end
end

