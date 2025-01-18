import Mathlib

open Set Real

namespace RPF

  abbrev PBernoulli (n : ℕ) := ℕ → Fin n

  variable {n : ℕ} {x y z : PBernoulli n}

  instance : MetricSpace (Fin n) where
    dist x y := if x = y then 0 else 1
    dist_self x := by simp
    dist_comm x y := by simp [dist]; congr 1; simp [eq_comm]
    dist_triangle x y z := by
      simp_all [dist]
      by_cases h1 : x = z <;> simp_all [h1]
      . by_cases h2 : y = z <;> simp_all [h2, eq_comm]
      . by_cases h2 : x = y <;> simp_all [h2]
        by_cases h3 : y = z <;> simp_all [h3]
    eq_of_dist_eq_zero := by
      intro x y h
      simp [dist] at h
      exact h

  noncomputable instance : MetricSpace (PBernoulli n) := PiCountable.metricSpace

  def cylinder (x : PBernoulli n) (k : ℕ) : Set (PBernoulli n) := {y | ∀ i ∈ Ico 0 k, x i = y i}

  structure Holder (φ : PBernoulli n → ℝ) where
    isHolder : ∃ b : NNReal, ∃ α ∈ Ioo 0 1, ∀ x y : PBernoulli n, ∀ k : ℕ,
      y ∈ cylinder x k → |φ x - φ y| ≤ b * α ^ k

  def shift (x : PBernoulli n) : PBernoulli n := fun i => x (i + 1)

  instance : Fintype (preimage shift {x}) := sorry

  noncomputable def transfert (φ : PBernoulli n → ℝ) (f : PBernoulli n → ℝ) : PBernoulli n → ℝ :=
    fun x => ∑ y ∈ preimage shift {x}, f y * exp (φ y)

end RPF
