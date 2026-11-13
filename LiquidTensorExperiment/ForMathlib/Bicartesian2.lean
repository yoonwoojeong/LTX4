import LiquidTensorExperiment.ForMathlib.ChainComplexCons
import LiquidTensorExperiment.ForMathlib.MappingCone
import LiquidTensorExperiment.ForMathlib.ExactSeq3
import LiquidTensorExperiment.ForMathlib.Commsq
import LiquidTensorExperiment.ForMathlib.ComplexExtend
import LiquidTensorExperiment.ForMathlib.Derived.KProjective

#align_import for_mathlib.bicartesian2

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable {A₁₁ A₁₂ A₁₃ A₁₄ A₁₅ : 𝓐}

variable {A₂₁ A₂₂ A₂₃ A₂₄ A₂₅ : 𝓐}

variable {A₃₁ A₃₂ A₃₃ A₃₄ A₃₅ : 𝓐}

variable {A₄₁ A₄₂ A₄₃ A₄₄ A₄₅ : 𝓐}

variable {A₅₁ A₅₂ A₅₃ A₅₄ A₅₅ : 𝓐}

variable {f₁₁ : A₁₁ ⟶ A₁₂} {f₁₂ : A₁₂ ⟶ A₁₃} {f₁₃ : A₁₃ ⟶ A₁₄} {f₁₄ : A₁₄ ⟶ A₁₅}

variable {g₁₁ : A₁₁ ⟶ A₂₁} {g₁₂ : A₁₂ ⟶ A₂₂} {g₁₃ : A₁₃ ⟶ A₂₃} {g₁₄ : A₁₄ ⟶ A₂₄} {g₁₅ : A₁₅ ⟶ A₂₅}

variable {f₂₁ : A₂₁ ⟶ A₂₂} {f₂₂ : A₂₂ ⟶ A₂₃} {f₂₃ : A₂₃ ⟶ A₂₄} {f₂₄ : A₂₄ ⟶ A₂₅}

variable {g₂₁ : A₂₁ ⟶ A₃₁} {g₂₂ : A₂₂ ⟶ A₃₂} {g₂₃ : A₂₃ ⟶ A₃₃} {g₂₄ : A₂₄ ⟶ A₃₄} {g₂₅ : A₂₅ ⟶ A₃₅}

variable {f₃₁ : A₃₁ ⟶ A₃₂} {f₃₂ : A₃₂ ⟶ A₃₃} {f₃₃ : A₃₃ ⟶ A₃₄} {f₃₄ : A₃₄ ⟶ A₃₅}

variable {g₃₁ : A₃₁ ⟶ A₄₁} {g₃₂ : A₃₂ ⟶ A₄₂} {g₃₃ : A₃₃ ⟶ A₄₃} {g₃₄ : A₃₄ ⟶ A₄₄} {g₃₅ : A₃₅ ⟶ A₄₅}

variable {f₄₁ : A₄₁ ⟶ A₄₂} {f₄₂ : A₄₂ ⟶ A₄₃} {f₄₃ : A₄₃ ⟶ A₄₄} {f₄₄ : A₄₄ ⟶ A₄₅}

variable {g₄₁ : A₄₁ ⟶ A₅₁} {g₄₂ : A₄₂ ⟶ A₅₂} {g₄₃ : A₄₃ ⟶ A₅₃} {g₄₄ : A₄₄ ⟶ A₅₄} {g₄₅ : A₄₅ ⟶ A₅₅}

variable {f₅₁ : A₅₁ ⟶ A₅₂} {f₅₂ : A₅₂ ⟶ A₅₃} {f₅₃ : A₅₃ ⟶ A₅₄} {f₅₄ : A₅₄ ⟶ A₅₅}

namespace Bicartesian

def quatroCons (h : ExactSeq 𝓐 [f₁₁, f₁₂, f₁₃, f₁₄]) : CochainComplex 𝓐 ℕ :=
  ((((((CochainComplex.cons HomologicalComplex.zero (cokernel f₁₄) 0 zero_comp).cons _
                                  (cokernel.π _) comp_zero).cons
                              _ f₁₄ <|
                            cokernel.condition _).cons
                        _ f₁₃ <|
                      (h.drop 2).pair.w).cons
                  _ f₁₂ <|
                (h.drop 1).pair.w).cons
            _ f₁₁ <|
          (h.drop 0).pair.w).cons
      _ (kernel.ι _) <|
    kernel.condition _

open CochainComplex.Hom (cons)

def quatroConsHom (h₁ : ExactSeq 𝓐 [f₁₁, f₁₂, f₁₃, f₁₄]) (h₂ : ExactSeq 𝓐 [f₂₁, f₂₂, f₂₃, f₂₄])
    (sq₁ : Commsq f₁₁ g₁₁ g₁₂ f₂₁) (sq₂ : Commsq f₁₂ g₁₂ g₁₃ f₂₂) (sq₃ : Commsq f₁₃ g₁₃ g₁₄ f₂₃)
    (sq₄ : Commsq f₁₄ g₁₄ g₁₅ f₂₄) : quatroCons h₁ ⟶ quatroCons h₂ :=
  CochainComplex.Hom.cons _ _ (kernel.map _ _ _ _ sq₁.w)
      (cons _ _ g₁₁
        (cons _ _ g₁₂
          (cons _ _ g₁₃
            (cons _ _ g₁₄
                (cons _ _ g₁₅
                    (cons _ _ (cokernel.map _ _ _ _ sq₄.w) 0 <| comp_zero.trans comp_zero.symm) <|
                  (cokernel.π_desc _ _ _).symm) <|
              sq₄.w.symm)
            sq₃.w.symm)
          sq₂.w.symm)
        sq₁.w.symm) <|
    kernel.lift_ι _ _ _

variable (h₁ : ExactSeq 𝓐 [f₁₁, f₁₂, f₁₃, f₁₄]) (h₂ : ExactSeq 𝓐 [f₂₁, f₂₂, f₂₃, f₂₄])
  (sq₁ : Commsq f₁₁ g₁₁ g₁₂ f₂₁) (sq₂ : Commsq f₁₂ g₁₂ g₁₃ f₂₂) (sq₃ : Commsq f₁₃ g₁₃ g₁₄ f₂₃)
  (sq₄ : Commsq f₁₄ g₁₄ g₁₅ f₂₄)

def quatroCone : CochainComplex 𝓐 ℤ :=
  HomologicalComplex.cone <|
    (HomologicalComplex.embed ComplexShape.Embedding.natUpIntUp).map <|
      quatroConsHom h₁ h₂ sq₁ sq₂ sq₃ sq₄

@[simp]
theorem quatroCone_x_1 : (quatroCone h₁ h₂ sq₁ sq₂ sq₃ sq₄).pt 1 = (A₁₂ ⊞ A₂₁) :=
  rfl

@[simp]
theorem quatroCone_x_2 : (quatroCone h₁ h₂ sq₁ sq₂ sq₃ sq₄).pt 2 = (A₁₃ ⊞ A₂₂) :=
  rfl

@[simp]
theorem quatroCone_x_3 : (quatroCone h₁ h₂ sq₁ sq₂ sq₃ sq₄).pt 3 = (A₁₄ ⊞ A₂₃) :=
  rfl

-- move me
def Biprod.matrix (f₁₁ : A₁₁ ⟶ A₂₁) (f₂₁ : A₁₂ ⟶ A₂₁) (f₁₂ : A₁₁ ⟶ A₂₂) (f₂₂ : A₁₂ ⟶ A₂₂) :
    A₁₁ ⊞ A₁₂ ⟶ A₂₁ ⊞ A₂₂ :=
  biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂)

@[simp]
theorem quatroCone_d_12' :
    (quatroCone h₁ h₂ sq₁ sq₂ sq₃ sq₄).d 1 2 = Biprod.matrix (-f₁₂) 0 (g₁₂ ≫ 𝟙 _) f₂₁ :=
  rfl

@[simp]
theorem quatroCone_d_23' :
    (quatroCone h₁ h₂ sq₁ sq₂ sq₃ sq₄).d 2 3 = Biprod.matrix (-f₁₃) 0 (g₁₃ ≫ 𝟙 _) f₂₂ :=
  rfl

@[simp]
theorem quatroCone_d_34' :
    (quatroCone h₁ h₂ sq₁ sq₂ sq₃ sq₄).d 3 4 = Biprod.matrix (-f₁₄) 0 (g₁₄ ≫ 𝟙 _) f₂₃ :=
  rfl

section HomotopyCategory

open HomotopyCategory

instance quatroConsAcyclic :
    IsAcyclic <|
      (HomotopyCategory.quotient _ _).obj <|
        (HomologicalComplex.embed ComplexShape.Embedding.natUpIntUp).obj <| quatroCons h₁ :=
  by
  constructor
  intro n
  obtain ⟨n, rfl⟩ : ∃ k, k + 1 = n := ⟨n - 1, sub_add_cancel _ _⟩
  refine' IsZero.of_iso _ (homology_iso _ n (n + 1) (n + 1 + 1) rfl rfl)
  refine' Exact.homology'_isZero _ _ _
  rcases n with ((_ | _ | _ | _ | _ | _ | n) | (_ | n))
  · exact exact_kernel_ι
  · exact (h₁.drop 0).pair
  · exact (h₁.drop 1).pair
  · exact (h₁.drop 2).pair
  · exact Abelian.exact_cokernel _
  · show exact (cokernel.π _) _; exact exact_epi_zero _
  · exact exact_of_zero _ _
  · show exact _ (kernel.ι _); exact exact_zero_mono _
  · exact exact_of_zero _ _

instance quatroConsHomQuasiIso :
    IsQuasiIso <|
      (HomotopyCategory.quotient _ _).map <|
        (HomologicalComplex.embed ComplexShape.Embedding.natUpIntUp).map <|
          quatroConsHom h₁ h₂ sq₁ sq₂ sq₃ sq₄ :=
  by
  constructor
  intro n
  refine' IsZero.isIso _ _ _ <;> apply IsAcyclic.cond

instance quatroConeAcyclic :
    IsAcyclic <| (HomotopyCategory.quotient _ _).obj <| quatroCone h₁ h₂ sq₁ sq₂ sq₃ sq₄ :=
  by
  let f :=
    (HomologicalComplex.embed ComplexShape.Embedding.natUpIntUp).map
      (Bicartesian.quatroConsHom h₁ h₂ sq₁ sq₂ sq₃ sq₄)
  have := cone_triangleₕ_mem_distinguished_triangles _ _ f
  refine' (HomotopyCategory.isQuasiIso_iff_isAcyclic _ this).mp _
  apply Bicartesian.quatroConsHomQuasiIso

end HomotopyCategory

-- #check biprod.matrix (-f₁₂) 0 (g₁₂ ≫ 𝟙 _) f₂₁
end Bicartesian

