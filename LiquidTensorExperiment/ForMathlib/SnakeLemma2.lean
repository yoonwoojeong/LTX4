import LiquidTensorExperiment.ForMathlib.SnakeLemma
import LiquidTensorExperiment.ForMathlib.ExactSeq2

#align_import for_mathlib.snake_lemma2

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝒜 : Type _} [Category 𝒜] [Abelian 𝒜]

variable (A₀ B₀ C₀ : 𝒜)

variable (A₁ B₁ C₁ : 𝒜)

variable (A₂ B₂ C₂ : 𝒜)

variable (A₃ B₃ C₃ : 𝒜)

variable (f₀ : A₀ ⟶ B₀) (g₀ : B₀ ⟶ C₀)

variable (a₀ : A₀ ⟶ A₁) (b₀ : B₀ ⟶ B₁) (c₀ : C₀ ⟶ C₁)

variable (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)

variable (a₁ : A₁ ⟶ A₂) (b₁ : B₁ ⟶ B₂) (c₁ : C₁ ⟶ C₂)

variable (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)

variable (a₂ : A₂ ⟶ A₃) (b₂ : B₂ ⟶ B₃) (c₂ : C₂ ⟶ C₃)

variable (f₃ : A₃ ⟶ B₃) (g₃ : B₃ ⟶ C₃)

namespace CategoryTheory

local notation "kernel_map" => kernel.map _ _ _ _

local notation "cokernel_map" => cokernel.map _ _ _ _

structure Snake : Prop where
  row_exact₁ : Exact f₁ g₁
  row_exact₂ : Exact f₂ g₂
  [row_epi : Epi g₁]
  [row_mono : Mono f₂]
  col_exact_a : ExactSeq 𝒜 [a₀, a₁, a₂]
  col_exact_b : ExactSeq 𝒜 [b₀, b₁, b₂]
  col_exact_c : ExactSeq 𝒜 [c₀, c₁, c₂]
  [col_mono_a : Mono a₀]
  [col_mono_b : Mono b₀]
  [col_mono_c : Mono c₀]
  [col_epi_a : Epi a₂]
  [col_epi_b : Epi b₂]
  [col_epi_c : Epi c₂]
  sq_a₀ : a₀ ≫ f₁ = f₀ ≫ b₀
  sq_b₀ : b₀ ≫ g₁ = g₀ ≫ c₀
  sq_a₁ : a₁ ≫ f₂ = f₁ ≫ b₁
  sq_b₁ : b₁ ≫ g₂ = g₁ ≫ c₁
  sq_a₂ : a₂ ≫ f₃ = f₂ ≫ b₂
  sq_b₂ : b₂ ≫ g₃ = g₂ ≫ c₂

namespace Snake

theorem mk_of_sequence_hom (sq₁ : a₁ ≫ f₂ = f₁ ≫ b₁) (sq₂ : b₁ ≫ g₂ = g₁ ≫ c₁) (h₁ : Exact f₁ g₁)
    (h₂ : Exact f₂ g₂) [Epi g₁] [Mono f₂] :
    Snake (kernel a₁) (kernel b₁) (kernel c₁) A₁ B₁ C₁ A₂ B₂ C₂ (cokernel a₁) (cokernel b₁)
      (cokernel c₁) (kernel_map sq₁) (kernel_map sq₂) (kernel.ι _) (kernel.ι _) (kernel.ι _) f₁ g₁
      a₁ b₁ c₁ f₂ g₂ (cokernel.π _) (cokernel.π _) (cokernel.π _) (cokernel_map sq₁)
      (cokernel_map sq₂) :=
  { row_exact₁ := h₁
    row_exact₂ := h₂
    col_exact_a :=
      ExactSeq.cons _ _ exact_kernel_ι _ <| (exact_iff_exactSeq _ _).mp (Abelian.exact_cokernel _)
    col_exact_b :=
      ExactSeq.cons _ _ exact_kernel_ι _ <| (exact_iff_exactSeq _ _).mp (Abelian.exact_cokernel _)
    col_exact_c :=
      ExactSeq.cons _ _ exact_kernel_ι _ <| (exact_iff_exactSeq _ _).mp (Abelian.exact_cokernel _)
    sq_a₀ := (Limits.kernel.lift_ι _ _ _).symm
    sq_b₀ := (Limits.kernel.lift_ι _ _ _).symm
    sq_a₁ := sq₁
    sq_b₁ := sq₂
    sq_a₂ := cokernel.π_desc _ _ _
    sq_b₂ := cokernel.π_desc _ _ _ }

variable {A₀ B₀ C₀ A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ f₀ g₀ a₀ b₀ c₀ f₁ g₁ a₁ b₁ c₁ f₂ g₂ a₂ b₂ c₂ f₃ g₃}

variable
  (S : Snake A₀ B₀ C₀ A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ f₀ g₀ a₀ b₀ c₀ f₁ g₁ a₁ b₁ c₁ f₂ g₂ a₂ b₂ c₂ f₃ g₃)

variable ()

def snakeDiagram : SnakeDiagram ⥤ 𝒜 :=
  SnakeDiagram.mkFunctor ![![A₀, B₀, C₀], ![A₁, B₁, C₁], ![A₂, B₂, C₂], ![A₃, B₃, C₃]] f₀ g₀ a₀ b₀
    c₀ f₁ g₁ a₁ b₁ c₁ f₂ g₂ a₂ b₂ c₂ f₃ g₃ S.sq_a₀ S.sq_b₀ S.sq_a₁ S.sq_b₁ S.sq_a₂ S.sq_b₂

theorem isSnakeInput : IsSnakeInput S.SnakeDiagram :=
  { row_exact₁ := by dsimp only [snake_diagram]; simpa using S.row_exact₁
    row_exact₂ := by dsimp only [snake_diagram]; simpa using S.row_exact₂
    col_exact₁ := by
      intro j
      dsimp only [snake_diagram]
      fin_cases j with [0, 1, 2] <;> simp <;> rw [exact_iff_exact_seq]
      exacts [S.col_exact_a.extract 0 2, S.col_exact_b.extract 0 2, S.col_exact_c.extract 0 2]
    col_exact₂ := by
      intro j
      dsimp only [snake_diagram]
      fin_cases j with [0, 1, 2] <;> simp <;> rw [exact_iff_exact_seq]
      exacts [S.col_exact_a.extract 1 2, S.col_exact_b.extract 1 2, S.col_exact_c.extract 1 2]
    col_mono := by
      intro j
      dsimp only [snake_diagram]
      fin_cases j with [0, 1, 2] <;> simp
      exacts [S.col_mono_a, S.col_mono_b, S.col_mono_c]
    col_epi := by
      intro j
      dsimp only [snake_diagram]
      fin_cases j with [0, 1, 2] <;> simp
      exacts [S.col_epi_a, S.col_epi_b, S.col_epi_c]
    row_mono := by dsimp only [snake_diagram]; simp; exact S.row_mono
    row_epi := by dsimp only [snake_diagram]; simpa using S.row_epi }

def snakeInput : SnakeInput 𝒜 :=
  ⟨S.SnakeDiagram, S.IsSnakeInput⟩

def δ : C₀ ⟶ A₃ :=
  S.IsSnakeInput.δ

theorem six_term_exactSeq : ExactSeq 𝒜 [f₀, g₀, S.δ, f₃, g₃] :=
  by
  have := S.is_snake_input.six_term_exact_seq
  dsimp only [snake_diagram] at this 
  simpa only [snake_diagram.mk_functor_map_f0, snake_diagram.mk_functor_map_g0,
    snake_diagram.mk_functor_map_f3, snake_diagram.mk_functor_map_g3]

end Snake

theorem mono_of_exact_of_eq_zero (hfg : Exact f₁ g₁) (h : f₁ = 0) : Mono g₁ := by
  rwa [(abelian.tfae_mono A₁ g₁).out 0 2, ← h]

theorem Cokernel.map_mono_of_epi_of_mono (sq : f₁ ≫ b₁ = a₁ ≫ f₂) [Epi a₁] [Mono b₁] [Mono f₂] :
    Mono (cokernel.map f₁ f₂ a₁ b₁ sq) :=
  by
  have S :=
    snake.mk_of_sequence_hom A₁ B₁ (cokernel f₁) A₂ B₂ (cokernel f₂) f₁ (cokernel.π _) a₁ b₁
      (cokernel.map f₁ f₂ a₁ b₁ sq) f₂ (cokernel.π _) sq.symm (by simp) (abelian.exact_cokernel _)
      (abelian.exact_cokernel _)
  apply S.col_exact_c.pair.mono_of_isZero
  exact
    (S.six_term_exact_seq.drop 1).pair.isZero_of_isZero_isZero (is_zero_kernel_of_mono _)
      (is_zero_cokernel_of_epi _)

end CategoryTheory

