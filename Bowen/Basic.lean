import Mathlib
import Bowen.Bernoulli
import Bowen.Gibbs
import Bowen.Existence

open MeasureTheory

theorem gibbs_unique (φ : Bernoulli ℤ n → ℝ) [HolderLike φ] (μ : Measure (Bernoulli ℤ n)) [IsGibbs φ μ] :
  μ = μ_gibbs (φ' φ) := by rw [Uniqueness.gibbs_ergodic_unique φ (μ_gibbs (φ' φ)) μ]

theorem gibbs (φ : Bernoulli ℤ n → ℝ) [HolderLike φ] :
  ∃! μ : Measure (Bernoulli ℤ n), IsGibbs φ μ := by
    apply existsUnique_of_exists_of_unique;
    . use μ_gibbs (φ' φ)
      exact is_gibbs
    . intros μ μ' hμ hμ'
      have μ1 :  μ = μ_gibbs (φ' φ) := gibbs_unique φ μ
      have μ2 : μ' = μ_gibbs (φ' φ) := gibbs_unique φ μ'
      subst μ1 μ2
      simp only
