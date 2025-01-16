import Mathlib
import Bowen.Bernoulli

open Real MeasureTheory Set
open Bernoulli

structure InvariantProb (μ : Measure (Bernoulli n)) where
  prob : μ (Set.univ) = 1
  invariant : ∀ s, μ s = μ (preimage shift s)

def IsGibbs (φ : Bernoulli n → ℝ) (μ : Measure (Bernoulli n)) : Prop :=
  InvariantProb μ ∧
  ∃ P : ℝ, ∃ c₁ c₂ : NNReal, ∀ x : Bernoulli n, ∀ m : ℕ,
    μ (cylinder x m) / nnexp (- P * m + ∑ k < m, φ (shift^[k] x)) ∈ Icc (c₁ : ENNReal) (c₂: ENNReal)

structure Holder (φ : Bernoulli n → ℝ) where
  isHolder : ∃ b : NNReal, ∃ α ∈ Ioo 0 1, ∀ x y : Bernoulli n, ∀ k : ℕ,
    y ∈ cylinder x k → |φ x - φ y| ≤ b * α ^ k

