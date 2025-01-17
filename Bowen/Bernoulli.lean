import Mathlib

open Real MeasureTheory Set

abbrev Bernoulli (n : ℕ) := ℤ → Fin n

noncomputable def nnexp (x : ℝ) : NNReal := ⟨exp x, exp_nonneg x⟩

namespace Bernoulli

  variable {n : ℕ} (x y z : Bernoulli n) {φ : Bernoulli n → ℝ}

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

  noncomputable instance : MetricSpace (Bernoulli n) := PiCountable.metricSpace

  instance : CompactSpace (Fin n) := Finite.compactSpace
  instance : CompactSpace (Bernoulli n) := Pi.compactSpace -- or Function.compactSpace

  theorem bernoulli_is_compact : IsCompact (Set.univ : Set (Bernoulli n)) :=
    by exact Pi.compactSpace.isCompact_univ

  def cylinder (x : Bernoulli n) (m : ℕ) : Set (Bernoulli n) :=
    {y : Bernoulli n | ∀ i ∈ Ico 0 m, x i = y i}

  def shift (x : Bernoulli n) : Bernoulli n := fun i => x (i + 1)

end Bernoulli
