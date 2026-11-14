import Mathlib.Algebra.Homology.HomologicalComplex

#align_import for_mathlib.chain_complex_cons

open CategoryTheory

namespace CochainComplex

variable {𝓐 : Type _} [Category 𝓐] [Preadditive 𝓐]

def Cons.x (C : CochainComplex 𝓐 ℕ) (A : 𝓐) : ℕ → 𝓐
  | 0 => A
  | n + 1 => C.X n

def Cons.d (C : CochainComplex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) :
    ∀ i j : ℕ, Cons.x C A i ⟶ Cons.x C A j
  | 0, 0 => 0
  | 0, 1 => d
  | 0, j + 2 => 0
  | i + 1, 0 => 0
  | i + 1, j + 1 => C.d i j

theorem Cons.shape (C : CochainComplex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) :
    ∀ i j : ℕ, ¬(ComplexShape.up ℕ).Rel i j → Cons.d C A d i j = 0
  | 0, 0, h => rfl
  | 0, 1, h => (h rfl).elim
  | 0, j + 2, h => rfl
  | i + 1, 0, h => rfl
  | i + 1, j + 1, h => C.shape i j <| mt (add_left_inj 1).mpr h

theorem Cons.d_comp_d (C : CochainComplex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) (h : d ≫ C.d 0 1 = 0) :
    ∀ i j k,
      (ComplexShape.up ℕ).Rel i j →
        (ComplexShape.up ℕ).Rel j k → Cons.d C A d i j ≫ Cons.d C A d j k = 0
  | 0, 1, 2, rfl, rfl => h
  | i + 1, _, _, rfl, rfl => C.d_comp_d _ _ _

def cons (C : CochainComplex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) (h : d ≫ C.d 0 1 = 0) :
    CochainComplex 𝓐 ℕ where
  X := Cons.x C A
  d := Cons.d C A d
  shape' := Cons.shape C A d
  d_comp_d' := Cons.d_comp_d C A d h

section SimpLemmas

variable (C : CochainComplex 𝓐 ℕ) (A : 𝓐) (d : A ⟶ C.X 0) (h : d ≫ C.d 0 1 = 0)

@[simp]
theorem cons_x_0 : (C.cons A d h).X 0 = A :=
  rfl

@[simp]
theorem cons_x_succ (n : ℕ) : (C.cons A d h).X (n + 1) = C.X n :=
  rfl

@[simp]
theorem cons_d_01 : (C.cons A d h).d 0 1 = d :=
  rfl

@[simp]
theorem cons_d_succ (n : ℕ) : (C.cons A d h).d (n + 1) (n + 2) = C.d n (n + 1) :=
  rfl

end SimpLemmas

namespace Hom

variable {C₁ C₂ : CochainComplex 𝓐 ℕ} {A₁ A₂ : 𝓐} {d₁ : A₁ ⟶ C₁.X 0} {d₂ : A₂ ⟶ C₂.X 0}
  (h₁ : d₁ ≫ C₁.d 0 1 = 0) (h₂ : d₂ ≫ C₂.d 0 1 = 0) (f : A₁ ⟶ A₂) (g : C₁ ⟶ C₂)

def Cons.f : ∀ i : ℕ, (C₁.cons A₁ d₁ h₁).pt i ⟶ (C₂.cons A₂ d₂ h₂).pt i
  | 0 => f
  | i + 1 => g.f i

theorem Cons.comm (w : f ≫ d₂ = d₁ ≫ g.f 0) :
    ∀ i j : ℕ,
      (ComplexShape.up ℕ).Rel i j →
        Cons.f h₁ h₂ f g i ≫ (C₂.cons A₂ d₂ h₂).d i j =
          (C₁.cons A₁ d₁ h₁).d i j ≫ Cons.f h₁ h₂ f g j
  | 0, 1, rfl => w
  | i + 1, _, rfl => g.comm i (i + 1)

def cons (w : f ≫ d₂ = d₁ ≫ g.f 0) : C₁.cons A₁ d₁ h₁ ⟶ C₂.cons A₂ d₂ h₂
    where
  f := Cons.f h₁ h₂ f g
  comm' := Cons.comm h₁ h₂ f g w

section SimpLemmas

variable (w : f ≫ d₂ = d₁ ≫ g.f 0)

@[simp]
theorem cons_f_0 : (cons h₁ h₂ f g w).f 0 = f :=
  rfl

@[simp]
theorem cons_f_succ (i : ℕ) : (cons h₁ h₂ f g w).f (i + 1) = g.f i :=
  rfl

end SimpLemmas

end Hom

end CochainComplex

