import Mathlib

open Set Real MeasureTheory


/-- Schauder-Tychonoff Theorem: A compact convex subset of a locally convex linear
topological space has the fixed point property. -/
theorem schauder_tychonoff
  {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {K : Set E} (hK : IsCompact K) (hK_convex : Convex ℝ K) (f : E → E) :
  ContinuousOn f K ∧ (f '' K ⊆ K) → ∃ x ∈ K, f x = x := sorry

noncomputable def pullback_aux {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] (L : C(X, NNReal) → C(X, NNReal)) (μ : ProbabilityMeasure X) :
  CompactlySupportedContinuousMap X NNReal →ₗ[NNReal] NNReal :=
    { toFun := fun f => ⟨∫ x, L f x ∂μ, sorry⟩,
      map_add' := sorry,
      map_smul' := sorry
    }

noncomputable def pullback_measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [OpensMeasurableSpace X] [CompactSpace X] [BorelSpace X]
  (L : C(X, NNReal) → C(X, NNReal)) (μ : ProbabilityMeasure X) :
  Measure X :=
    (rieszContent (pullback_aux L μ)).measure

noncomputable def pullback {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [OpensMeasurableSpace X] [CompactSpace X] [BorelSpace X]
  (L : C(X, NNReal) → C(X, NNReal)) (μ : ProbabilityMeasure X) :
  ProbabilityMeasure X :=
    ⟨pullback_measure L μ, sorry⟩

namespace RPF

  abbrev PBernoulli (n : ℕ) := ℕ → Fin n

  variable {n : ℕ} {x y z : PBernoulli n} {φ : PBernoulli n → ℝ} {b : NNReal} {α : Ioo 0 1}

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

  structure Holder (φ : PBernoulli n → ℝ) (b : NNReal) (α : Ioo 0 1) where
    isHolder : ∀ x y : PBernoulli n, ∀ k : ℕ,
      y ∈ cylinder x k → |φ x - φ y| ≤ b * α ^ k

  def shift (x : PBernoulli n) : PBernoulli n := fun i => x (i + 1)

  instance : Fintype (preimage shift {x}) := sorry

  noncomputable def transfert (φ : PBernoulli n → ℝ) (f : PBernoulli n → ℝ) : PBernoulli n → ℝ :=
    fun x => ∑ y ∈ preimage shift {x}, f y * exp (φ y)

  theorem im_transfert_continuous (hφ : Continuous φ)
    : Continuous (transfert φ)
    := by sorry

  variable {hφ : Holder φ b α}

  -- theorem rpf1 (hφ : Holder φ b α)

  -- noncomputable def B (m : ℕ) := exp (∑' k ∈ {k : ℕ | k > m}, 2 * b * α^k)

end RPF
