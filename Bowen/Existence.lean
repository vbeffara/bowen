import Mathlib
import Bowen.RPF
import Bowen.Bernoulli
import Bowen.Gibbs

open Set Filter Classical MeasureTheory
open Bernoulli

section Pos

variable {n : ℕ} (φ : Bernoulli ℕ n → ℝ) [HolderLike φ]

noncomputable def CZtoCN (f : C(Bernoulli ℤ n, ℝ)) : C(Bernoulli ℕ n, ℝ) :=
  {
    toFun := λ x : Bernoulli ℕ n =>
      sInf {v | ∀ y : Bernoulli ℤ n, ∀ i ∈ Ici 0, x i = y i ∧ v = f y}
    continuous_toFun := sorry
  }

noncomputable def μf_seq (f : C(Bernoulli ℤ n, ℝ)) (k : ℕ) : ℝ :=
  ∫ x, ((CZtoCN f) ∘ shift^[k]) x ∂(RPF.μ φ)

lemma cauchy_μf (f : C(Bernoulli ℤ n, ℝ)) : CauchySeq (μf_seq φ f) := sorry

lemma has_limit (f : C(Bernoulli ℤ n, ℝ)) :
  ∃ G : ℝ, Tendsto (μf_seq φ f) atTop (nhds G) := sorry

def Cpos_to_C (f : C(Bernoulli ℤ n, NNReal)) : C(Bernoulli ℤ n, ℝ) :=
  {
    toFun := fun x => f x
  }

lemma has_limit_pos (f : C(Bernoulli ℤ n, NNReal)) :
  ∃ Gp : NNReal, Tendsto (μf_seq φ (Cpos_to_C f)) atTop (nhds Gp) := sorry

def Ccpos_to_Cpos (f : CompactlySupportedContinuousMap (Bernoulli ℤ n) NNReal) :
  C(Bernoulli ℤ n, NNReal) :=
  {
    toFun := fun x : Bernoulli ℤ n => f x
  }

noncomputable def G : (CompactlySupportedContinuousMap (Bernoulli ℤ n) NNReal) →ₗ[NNReal] NNReal :=
  {
    toFun := fun f => choose (has_limit_pos φ (Ccpos_to_Cpos f)),
    map_add' := sorry,
    map_smul' := sorry
  }

def one : CompactlySupportedContinuousMap (Bernoulli ℤ n) NNReal :=
  {
    toFun := fun _ : Bernoulli ℤ n => 1,
    hasCompactSupport' := by simp only; sorry
  }

lemma G_one_eq_one : G φ one = 1 := sorry

noncomputable def μ_gibbs : Measure (Bernoulli ℤ n) := (rieszContent (G φ)).measure

instance prob : IsProbabilityMeasure (μ_gibbs φ) where
  measure_univ := sorry

instance invariant : InvariantProb (μ_gibbs φ) where
  invariant s := sorry

end Pos

variable {φ : Bernoulli ℤ n → ℝ} [HolderLike φ]

def φ_continuous (φ : Bernoulli ℤ n → ℝ) [HolderLike φ] : C(Bernoulli ℤ n, ℝ) :=
  {
    toFun := fun x => φ x,
    continuous_toFun := sorry
  }

noncomputable def φ' (φ : Bernoulli ℤ n → ℝ) [HolderLike φ] : Bernoulli ℕ n → ℝ :=
  CZtoCN (φ_continuous φ)

lemma var_summable (φ : Bernoulli ℤ n → ℝ) [HolderLike φ] : Summable (HolderLike.var φ) := sorry

noncomputable def var_sum (φ : Bernoulli ℤ n → ℝ) [HolderLike φ] : NNReal :=
  ∑' k, (HolderLike.var φ) k

lemma bikhoff_ineq (φ : Bernoulli ℤ n → ℝ) [HolderLike φ] (x y : Bernoulli ℤ n) (m : ℕ)
  (hxy : y ∈ cylinder x m) :
    |∑ k ∈ Ico 0 m, φ (shift^[k] x) - φ (shift^[k] y)| ≤ var_sum φ :=
  sorry

noncomputable instance holder_like : HolderLike (φ' φ) where
  α := sorry
  b := sorry
  isHolderLike := sorry

instance is_gibbs : IsGibbs φ (μ_gibbs (φ' φ)) where
  gibbs_prop := sorry

instance mu_mixing : IsMixing (μ_gibbs (φ' φ)) where
  mixing := sorry
