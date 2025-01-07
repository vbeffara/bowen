import Mathlib

open Real MeasureTheory Set

abbrev Bernoulli (n: ℕ) := ℤ → Fin n

variable {n : ℕ} {φ : Bernoulli n → ℝ}

noncomputable def nnexp (x : ℝ) : NNReal := ⟨exp x, exp_nonneg x⟩

noncomputable def diff (x y : Bernoulli n) : ℤ → NNReal :=
  Set.indicator {i | x i ≠ y i} (fun i => nnexp (- |i|))

noncomputable instance : PseudoEMetricSpace (Bernoulli n) where
  edist x y := ∑' i, diff x y i
  edist_self x := by simp [diff]
  edist_comm x y := by simp [diff] ; congr ; ext i ; congr ; ext k ; exact ne_comm
  edist_triangle x y z := by
    simp [← tsum_add]
    apply tsum_mono (by simp) (by simp)
    intro i
    by_cases h1 : x i = z i <;> simp [diff, h1]
    by_cases h2 : x i = y i <;> simp [h2]
    have h3 : ¬y i = z i := by simpa [← h2]
    simp [h3]

#synth CompactSpace (Bernoulli n)

def shift (x : Bernoulli n) : Bernoulli n := fun i => x (i + 1)

def IsGibbs (φ : Bernoulli n → ℝ) (μ : Measure (Bernoulli n)) : Prop :=
  ∃ P : ℝ, ∃ c₁ c₂ : ENNReal, ∀ x : Bernoulli n, ∀ m : ℕ,
    μ {y | EqOn x y (Ico 0 m)} / nnexp (- P * m + ∑ k < m, φ (shift^[k] x)) ∈ Icc c₁ c₂
