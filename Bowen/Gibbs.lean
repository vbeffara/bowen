import Mathlib
import Bowen.Bernoulli
import Bowen.RPF

open Real MeasureTheory Set Topology
open Filter
open Bernoulli

variable {n : ℕ}

noncomputable def nnexp (x : ℝ) : NNReal := ⟨exp x, exp_nonneg x⟩

instance : ContainN ℤ where
  fromNat x := ↑x
  shift x := x + 1
  cylinder_supp k := Icc (-k) k

class InvariantProb (μ : Measure (Bernoulli ℤ n)) extends IsProbabilityMeasure μ where
  invariant : ∀ s, μ s = μ (f ⁻¹' s)

class IsGibbs (φ : Bernoulli ℤ n → ℝ) (μ : Measure (Bernoulli ℤ n)) extends InvariantProb μ where
  gibbs_prop : ∃ P : ℝ, ∃ c₁ c₂ : NNReal, ∀ x : Bernoulli ℤ n, ∀ m : ℕ,
    μ (cylinder x m) / nnexp (- P * m + ∑ k < m, φ (shift^[k] x)) ∈ Icc (c₁ : ENNReal) (c₂: ENNReal)

class IsErgodic (μ : Measure (Bernoulli ℤ n)) extends InvariantProb μ where
  ergodicity : ∀ s, f⁻¹' s = s → μ s = 0 ∨ μ s = 1

class IsMixing (μ : Measure (Bernoulli ℤ n)) extends InvariantProb μ where
  mixing : ∀ e f, Tendsto (fun n => μ (e ∩ preimage shift^[n] f)) atTop (nhds (μ e * μ f))

instance mixing_imp_ergodic (μ : Measure (Bernoulli ℤ n)) [IsMixing μ] : IsErgodic μ where
  ergodicity := by
    intros f s hs
    have intersect_trivial : ∀ n, s ∩ (shift^[n])⁻¹' s = s := sorry
    have lim : Tendsto (fun _ : ℕ => μ s) atTop (nhds (μ s * μ s)) := by sorry
    have lim2 : Tendsto (fun _ : ℕ => μ s) atTop (nhds (μ s)) := by exact tendsto_const_nhds
    have eq : μ s * μ s = μ s := by exact tendsto_nhds_unique lim lim2
    sorry

lemma ergodic_shift_inv_imp_cst (μ : Measure (Bernoulli ℤ n)) [IsErgodic μ] (f : Bernoulli ℤ n → ℝ)
  (hf : Integrable f μ) (hμ : μ {x | (f ∘ shift) x = f x} = 1) :
    ∃ c, μ (f⁻¹' {c}) = 1 := by sorry

namespace Uniqueness

  theorem gibbs_ergodic_unique (φ : Bernoulli ℤ n -> ℝ) (μ μ' : Measure (Bernoulli ℤ n))
    [IsGibbs φ μ] [IsGibbs φ μ'] [IsErgodic μ] :
      μ = μ' := sorry

end Uniqueness

namespace Equiv

  def equiv (f g : Bernoulli ℤ n → ℝ) : Prop :=
    ∃ u : Bernoulli ℤ n → ℝ, Continuous u ∧ f = g - u + (u ∘ shift)

  theorem equiv_imp_eq_gibbs (φ ψ : Bernoulli ℤ n → ℝ) (μ ν : Measure (Bernoulli ℤ n))
    [HolderLike φ] [HolderLike ψ] [IsGibbs φ μ] [IsGibbs ψ ν] (h_equiv : equiv φ ψ) :
    μ = ν := sorry

  def DependOnlyPosCoords (φ : Bernoulli ℤ n → ℝ) : Prop :=
    ∀ x y : Bernoulli ℤ n, (∀ i : ℕ, x i = y i) → φ x = φ y

  lemma equiv_pos_coords (φ : Bernoulli ℤ n → ℝ) :
    ∃ ψ : Bernoulli ℤ n → ℝ, DependOnlyPosCoords ψ ∧ equiv φ ψ := sorry

end Equiv
