import Mathlib

open Real MeasureTheory Set

abbrev Bernoulli (n : ℕ) := ℤ → Fin n

noncomputable def nnexp (x : ℝ) : NNReal := ⟨exp x, exp_nonneg x⟩

namespace Bernoulli

  variable {n : ℕ} (x y z : Bernoulli n) {φ : Bernoulli n → ℝ} {a : Fin n}

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

  def finite_bernoulli (a : Fin n) (m : ℕ) : Set (Bernoulli n) := {x | ∀ i : ℤ, |i| > m → x i = a}

  instance : T2Space (Bernoulli n) where
    t2 := by
      intro x y hneq
      sorry

  lemma bernoulli_is_T2 : T2Space (Bernoulli n) := by infer_instance

  def ball (x : Bernoulli n) (m : ℕ) : Set (Bernoulli n)
    := {y | ∀ i ∈ Icc ((-m) : ℤ) m, x i = y i}

  lemma ball_open : ∀ x : Bernoulli n, ∀ m, IsOpen (ball x m)
    := by sorry

  lemma open_iff_countable_ball_union (s : Set (Bernoulli n))
    : IsOpen s ↔ ∃ b : ℕ → Bernoulli n, ∃ r : ℕ → ℕ, s = sUnion {ball (b i) (r i) | i : ℕ}
    := by sorry

end Bernoulli
