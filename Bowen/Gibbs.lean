import Mathlib
import Bowen.Bernoulli
import Bowen.RPF

open Real MeasureTheory Set Topology
open Filter
open Bernoulli

variable {n : ℕ}

structure InvariantProb (μ : Measure (Bernoulli n)) where
  prob : μ (Set.univ) = 1
  invariant : ∀ s, μ s = μ (preimage f s)

def IsGibbs (φ : Bernoulli n → ℝ) (μ : Measure (Bernoulli n)) : Prop :=
  InvariantProb μ ∧
  ∃ P : ℝ, ∃ c₁ c₂ : NNReal, ∀ x : Bernoulli n, ∀ m : ℕ,
    μ (cylinder x m) / nnexp (- P * m + ∑ k < m, φ (shift^[k] x)) ∈ Icc (c₁ : ENNReal) (c₂: ENNReal)

structure Holder (φ : Bernoulli n → ℝ) where
  isHolder : ∃ b : NNReal, ∃ α ∈ Ioo 0 1, ∀ x y : Bernoulli n, ∀ k : ℕ,
    y ∈ cylinder x k → |φ x - φ y| ≤ b * α ^ k

lemma holder_imp_continuous (φ : Bernoulli n → ℝ)
  : Holder φ → Continuous φ
  := by intro hφ; sorry

def IsErgodic (μ : Measure (Bernoulli n)) : Prop :=
  InvariantProb μ ∧
  ∀ s, preimage shift s = s → μ s = 0 ∨ μ s = 1

def IsMixing (μ : Measure (Bernoulli n)) : Prop :=
  InvariantProb μ ∧
  ∀ e f, Tendsto (fun n => μ (e ∩ preimage shift^[n] f)) atTop (nhds (μ e * μ f))

lemma mixing_imp_ergodic (μ : Measure (Bernoulli n))
  : IsMixing μ → IsErgodic μ
  := by sorry

lemma ergodic_shift_inv_imp_cst (μ : Measure (Bernoulli n)) (f : Bernoulli n → ℝ)
  : (InvariantProb μ ∧ IsErgodic μ ∧ μ {x | (f ∘ shift) x = f x} = 1 ∧ Integrable f μ)
      -> ∃ c, μ {x | f x = c} = 1
  := by sorry

namespace Uniqueness

  theorem gibbs_ergodic_unique (φ : Bernoulli n -> ℝ)
    : ∀ μ μ' : Measure (Bernoulli n), IsGibbs φ μ ∧ IsGibbs φ μ' ∧ IsErgodic μ → μ = μ'
    := sorry

end Uniqueness

namespace Equiv

  def equiv (f : Bernoulli n → ℝ) (g : Bernoulli n → ℝ) : Prop :=
    ∃ u : Bernoulli n → ℝ, Continuous u ∧ f = g - u + (u ∘ shift)

  theorem equiv_imp_eq_gibbs (φ ψ : Bernoulli n → ℝ) (μ ν : Measure (Bernoulli n))
    : Holder φ ∧ Holder ψ ∧ equiv φ ψ ∧ IsGibbs φ μ ∧ IsGibbs ψ ν → μ = ν
    := sorry

  def DependOnlyPosCoords (φ : Bernoulli n → ℝ) : Prop :=
    ∀ x y : Bernoulli n, (∀ i : ℕ, x i = y i) → φ x = φ y

  lemma equiv_pos_coords (φ : Bernoulli n → ℝ)
    : ∃ ψ : Bernoulli n → ℝ, DependOnlyPosCoords ψ ∧ equiv φ ψ
    := sorry

end Equiv
