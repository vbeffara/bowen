import Mathlib

open Real MeasureTheory Set

abbrev Bernoulli (n : ℕ) := ℤ → Fin n

noncomputable def nnexp (x : ℝ) : NNReal := ⟨exp x, exp_nonneg x⟩

namespace Bernoulli

  variable {n : ℕ} (x y z : Bernoulli n) {φ : Bernoulli n → ℝ}

  noncomputable def diff (x y : Bernoulli n) : ℤ → NNReal :=
    Set.indicator {i | x i ≠ y i} (fun i => nnexp (- |i|))

  @[simp] lemma summable : Summable fun i => (x.diff y i : ℝ) := by
    simp [diff]
    apply Summable.indicator
    apply Summable.of_nat_of_neg <;> simpa using Real.summable_exp_neg_nat

  noncomputable def dist (x y : Bernoulli n) : ℝ := ∑' i, diff x y i

  @[simp] lemma dist_self : dist x x = 0 := by simp [dist, diff]

  lemma dist_comm : x.dist y = y.dist x := by
    simp [dist] ; congr ; ext i
    simp [diff] ; congr ; ext i ; exact ne_comm

  lemma dist_triangle : dist x z ≤ dist x y + dist y z := by
    simp [dist, ← tsum_add]
    apply tsum_mono (by simp) (by simp [Summable.add])
    intro i ; dsimp ; norm_cast
    by_cases h1 : x i = z i <;> simp [diff, h1]
    by_cases h2 : x i = y i <;> simp [h2]
    have h3 : ¬y i = z i := by simpa [← h2]
    simp [h3]

  noncomputable instance : MetricSpace (Bernoulli n) := by
    apply MetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle
    · sorry
    · sorry

  def cylinder (x : Bernoulli n) (m : ℕ) : Set (Bernoulli n) :=
    {y : Bernoulli n | ∀ i ∈ Ico 0 m, x i = y i}

  def shift (x : Bernoulli n) : Bernoulli n := fun i => x (i + 1)

end Bernoulli
