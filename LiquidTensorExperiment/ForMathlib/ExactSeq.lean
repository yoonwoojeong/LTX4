import Mathlib.Algebra.Homology.Exact
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Abelian.Pseudoelements

#align_import for_mathlib.exact_seq

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe w v u

namespace List

variable {α : Type _} (a : α) (L : List α) (m n : ℕ)

/-- Returns the sublist of `L` starting at index `m` of length `n`
(or shorter, if `L` is too short). -/
def extract :=
  (L.drop m).take n

@[simp]
theorem extract_nil : [].extract m n = ([] : List α) := by cases n; rfl; cases m; rfl; rfl

@[simp]
theorem extract_zero_right : L.extract m 0 = [] :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem extract_cons_succ_left : (a::L).extract m.succ n = L.extract m n :=
  rfl

end List

example : [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].extract 4 3 = [4, 5, 6] :=
  rfl

namespace CategoryTheory

variable (𝒞 : Type u) [Category.{v} 𝒞]

variable [HasZeroMorphisms 𝒞] [HasImages 𝒞] [HasKernels 𝒞]

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace Exact

-- move this
variable {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C)

def kernelOpIso : (kernel f.op).unop ≅ cokernel f
    where
  Hom :=
    (kernel.lift _ (cokernel.π f).op (by simp [← op_comp, limits.cokernel.condition])).unop ≫
      eqToHom (Opposite.unop_op (cokernel f))
  inv :=
    cokernel.desc _ (eqToHom (Opposite.unop_op B).symm ≫ (kernel.ι f.op).unop)
      (by
        dsimp
        rw [category.id_comp, ← f.unop_op, ← unop_comp, f.unop_op, kernel.condition]
        rfl)
  hom_inv_id' := by
    dsimp
    simp
    rw [← unop_id, ← (cokernel.desc f (kernel.ι f.op).unop _).unop_op, ← unop_comp]
    congr 1
    apply limits.equalizer.hom_ext
    dsimp
    simp [← op_comp]
  inv_hom_id' := by
    apply limits.coequalizer.hom_ext
    dsimp
    simp [← unop_comp]

def cokernelOpIso : (cokernel f.op).unop ≅ kernel f
    where
  Hom :=
    kernel.lift _ ((cokernel.π f.op).unop ≫ eqToHom (Opposite.unop_op _))
      (by
        simp only [eq_to_hom_refl, category.comp_id]
        rw [← f.unop_op, ← unop_comp, f.op.op_unop, cokernel.condition]
        rfl)
  inv :=
    eqToHom (Opposite.unop_op _).symm ≫ (cokernel.desc _ (kernel.ι f).op (by simp [← op_comp])).unop
  hom_inv_id' :=
    by
    simp only [category.id_comp, eq_to_hom_refl, category.comp_id, ← unop_id, ← unop_comp]
    rw [← (kernel.lift f (cokernel.π f.op).unop _).unop_op, ← unop_comp]
    congr 1
    apply limits.coequalizer.hom_ext
    dsimp
    simp [← op_comp]
  inv_hom_id' := by
    apply limits.equalizer.hom_ext
    dsimp
    simp [← unop_comp]

@[simp]
theorem Kernel.ι_op :
    (kernel.ι f.op).unop = eqToHom (Opposite.unop_op _) ≫ cokernel.π f ≫ (kernelOpIso f).inv :=
  by
  dsimp [kernel_op_iso]
  simp

@[simp]
theorem Cokernel.π_op :
    (cokernel.π f.op).unop =
      (cokernelOpIso f).Hom ≫ kernel.ι f ≫ eqToHom (Opposite.unop_op _).symm :=
  by
  dsimp [cokernel_op_iso]
  simp

variable {f g}

theorem op (h : Exact f g) : Exact g.op f.op :=
  by
  rw [abelian.exact_iff]
  refine' ⟨_, _⟩
  · simp only [← op_comp, h.w, op_zero]
  apply_fun Quiver.Hom.unop
  swap; · exact Quiver.Hom.unop_inj
  simp only [h, unop_comp, cokernel.π_op, eq_to_hom_refl, kernel.ι_op, category.id_comp,
    category.assoc, kernel_comp_cokernel_assoc, zero_comp, comp_zero, unop_zero]

variable (f g)

def kernelUnopIso {C B : 𝒜ᵒᵖ} (f : C ⟶ B) : Opposite.op (kernel f.unop) ≅ cokernel f
    where
  Hom :=
    (kernel.lift _ (cokernel.π f).unop (by simp [← unop_comp])).op ≫
      eqToHom (Opposite.op_unop (cokernel f))
  inv :=
    cokernel.desc _ (eqToHom (Opposite.op_unop _).symm ≫ (kernel.ι f.unop).op)
      (by
        dsimp
        rw [← f.op_unop, category.id_comp, ← op_comp, f.op_unop, kernel.condition]
        rfl)
  hom_inv_id' := by
    dsimp
    simp
    rw [← (cokernel.desc f (kernel.ι f.unop).op _).op_unop, ← op_comp, ← op_id]
    congr 1
    apply limits.equalizer.hom_ext
    dsimp
    simp [← unop_comp]
  inv_hom_id' := by
    apply limits.coequalizer.hom_ext
    dsimp
    simp [← op_comp]

def cokernelUnopIso {C B : 𝒜ᵒᵖ} (f : C ⟶ B) : Opposite.op (cokernel f.unop) ≅ kernel f
    where
  Hom :=
    kernel.lift _ ((cokernel.π f.unop).op ≫ eqToHom (Opposite.op_unop _))
      (by
        dsimp
        rw [← f.op_unop, category.comp_id, ← op_comp, f.op_unop, cokernel.condition]
        rfl)
  inv :=
    eqToHom (Opposite.op_unop _).symm ≫
      (cokernel.desc _ (kernel.ι f).unop (by simp [← unop_comp])).op
  hom_inv_id' := by
    dsimp
    rw [category.id_comp]
    rw [← (kernel.lift f ((cokernel.π f.unop).op ≫ 𝟙 C) _).op_unop, ← op_comp, ← op_id]
    congr 1
    apply limits.coequalizer.hom_ext
    dsimp
    simp [← unop_comp]
  inv_hom_id' := by
    apply limits.equalizer.hom_ext
    dsimp
    simp [← op_comp]

@[simp]
theorem Cokernel.π_unop {C B : 𝒜ᵒᵖ} (f : C ⟶ B) :
    (cokernel.π f.unop).op =
      (cokernelUnopIso f).Hom ≫ kernel.ι f ≫ eqToHom (Opposite.op_unop _).symm :=
  by
  dsimp [cokernel_unop_iso]
  simp

@[simp]
theorem Kernel.ι_unop {C B : 𝒜ᵒᵖ} (f : C ⟶ B) :
    (kernel.ι f.unop).op = eqToHom (Opposite.op_unop _) ≫ cokernel.π f ≫ (kernelUnopIso f).inv :=
  by
  dsimp [kernel_unop_iso]
  simp

theorem unop {C B A : 𝒜ᵒᵖ} {g : C ⟶ B} {f : B ⟶ A} (h : Exact g f) : Exact f.unop g.unop :=
  by
  rw [abelian.exact_iff]
  refine' ⟨by simp only [← unop_comp, h.w, unop_zero], _⟩
  apply_fun Quiver.Hom.op
  swap; · exact Quiver.Hom.op_inj
  simp [h]

end Exact

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A sequence `[f, g, ...]` of morphisms is exact if the pair `(f,g)` is exact,
and the sequence `[g, ...]` is exact.

Recall that the pair `(f,g)` is exact if `f ≫ g = 0`
and the natural map from the image of `f` to the kernel of `g` is an epimorphism
(equivalently, in abelian categories: isomorphism). -/
inductive ExactSeq : List (Arrow 𝒞) → Prop
  | nil : exact_seq []
  | single : ∀ f, exact_seq [f]
  |
  cons :
    ∀ {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (hfg : Exact f g) (L) (hgL : exact_seq (g::L)),
      exact_seq (f::g::L)

variable {𝒞}

theorem exact_iff_exactSeq {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : Exact f g ↔ ExactSeq 𝒞 [f, g] :=
  by
  constructor
  · intro h; exact exact_seq.cons f g h _ (exact_seq.single _)
  · rintro (_ | _ | ⟨A, B, C, f, g, hfg, _, _ | _ | _⟩); exact hfg

namespace ExactSeq

theorem extract : ∀ {L : List (Arrow 𝒞)} (h : ExactSeq 𝒞 L) (m n : ℕ), ExactSeq 𝒞 (L.extract m n)
  | L, nil, m, n => by rw [List.extract_nil]; exact nil
  | L, single f, m, 0 => nil
  | L, single f, 0, n + 1 => by cases n <;> exact single f
  | L, single f, m + 1, n + 1 => by cases m <;> exact nil
  | _, cons f g hfg L hL, m + 1, n => extract hL m n
  | _, cons f g hfg L hL, 0, 0 => nil
  | _, cons f g hfg L hL, 0, 1 => single f
  | _, cons f g hfg L hL, 0, n + 2 => cons f g hfg (L.take n) (extract hL 0 (n + 1))

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
inductive ArrowCongr : ∀ L L' : List (Arrow 𝒞), Prop
  | nil : arrow_congr [] []
  |
  cons :
    ∀ {A B : 𝒞} {f f' : A ⟶ B} {L L' : List (Arrow 𝒞)} (h : f = f') (H : arrow_congr L L'),
      arrow_congr (f::L) (f'::L')

theorem congr : ∀ {L L' : List (Arrow 𝒞)}, ExactSeq 𝒞 L → ArrowCongr L L' → ExactSeq 𝒞 L'
  | _, _, h, arrow_congr.nil => ExactSeq.nil
  | _, _, h, arrow_congr.cons h₁ arrow_congr.nil => ExactSeq.single _
  | _, _, h, arrow_congr.cons h₁ (arrow_congr.cons h₂ H) =>
    by
    substs h₁ h₂
    rcases h with (_ | _ | ⟨A, B, C, f, g, hfg, _, hL⟩)
    refine' exact_seq.cons _ _ hfg _ (congr hL (arrow_congr.cons rfl H))

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem append :
    ∀ {L₁ L₂ L₃ : List (Arrow 𝒞)} (h₁₂ : ExactSeq 𝒞 (L₁ ++ L₂)) (h₂₃ : ExactSeq 𝒞 (L₂ ++ L₃))
      (h₂ : L₂ ≠ []), ExactSeq 𝒞 (L₁ ++ L₂ ++ L₃)
  | L₁, [], L₃, h₁₂, h₂₃, h => (h rfl).elim
  | [], L₂, L₃, h₁₂, h₂₃, h => by rwa [List.nil_append]
  | _::[], _::L₂, L₃, cons f g hfg L hL, h₂₃, h => cons f g hfg _ h₂₃
  | _::_::L₁, L₂, L₃, cons f g hfg L hL, h₂₃, h =>
    suffices ExactSeq 𝒞 ([f] ++ ([g] ++ L₁ ++ L₂) ++ L₃) by simpa only [List.append_assoc]
    cons _ _ hfg _ <|
      suffices ExactSeq 𝒞 ((g::L₁) ++ L₂ ++ L₃) by simpa only [List.append_assoc]
      append (by simpa only using hL) h₂₃ h

end ExactSeq

namespace Arrow

open _Root_.Opposite

variable {C : Type _} [Category C]

@[simps]
def op (f : Arrow C) : Arrow Cᵒᵖ where
  left := op f.right
  right := op f.left
  Hom := f.Hom.op

@[simps]
def unop (f : Arrow Cᵒᵖ) : Arrow C where
  left := unop f.right
  right := unop f.left
  Hom := f.Hom.unop

@[simp]
theorem op_unop (f : Arrow C) : f.op.unop = f := by cases f; dsimp [op, unop]; rfl

@[simp]
theorem unop_op (f : Arrow Cᵒᵖ) : f.unop.op = f := by cases f; dsimp [op, unop]; rfl

@[simp]
theorem op_comp_unop : (op ∘ unop : Arrow Cᵒᵖ → Arrow Cᵒᵖ) = id := by ext; exact unop_op _

@[simp]
theorem unop_comp_op : (unop ∘ op : Arrow C → Arrow C) = id := by ext; exact op_unop _

end Arrow

namespace ExactSeq

theorem op : ∀ {L : List (Arrow 𝒜)}, ExactSeq 𝒜 L → ExactSeq 𝒜ᵒᵖ (L.reverse.map Arrow.op)
  | _, nil => nil
  | _, single f => single f.op
  | _, cons f g hfg L hL => by
    have := op hL
    simp only [List.reverse_cons, List.map_append] at this ⊢
    refine' this.append _ (List.cons_ne_nil _ _)
    exact cons _ _ hfg.op _ (single _)

theorem unop : ∀ {L : List (Arrow 𝒜ᵒᵖ)}, ExactSeq 𝒜ᵒᵖ L → ExactSeq 𝒜 (L.reverse.map Arrow.unop)
  | _, nil => nil
  | _, single f => single f.unop
  | _, cons f g hfg L hL => by
    have := unop hL
    simp only [List.reverse_cons, List.map_append] at this ⊢
    refine' this.append _ (List.cons_ne_nil _ _)
    exact cons _ _ hfg.unop _ (single _)

theorem of_op {L : List (Arrow 𝒜)} (h : ExactSeq 𝒜ᵒᵖ (L.reverse.map Arrow.op)) : ExactSeq 𝒜 L := by
  simpa only [List.map_reverse, List.reverse_reverse, List.map_map, arrow.unop_comp_op,
    List.map_id] using h.unop

theorem of_unop {L : List (Arrow 𝒜ᵒᵖ)} (h : ExactSeq 𝒜 (L.reverse.map Arrow.unop)) :
    ExactSeq 𝒜ᵒᵖ L := by
  simpa only [List.map_reverse, List.reverse_reverse, List.map_map, arrow.op_comp_unop,
    List.map_id] using h.op

end ExactSeq

end CategoryTheory

