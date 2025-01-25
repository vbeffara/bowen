import Mathlib

open Set Real MeasureTheory Classical


/-- Schauder-Tychonoff Theorem: A compact convex subset of a locally convex linear
topological space has the fixed point property. -/
theorem schauder_tychonoff
  {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {K : Set E} (hK : IsCompact K) (hK_convex : Convex ℝ K) (f : E → E) :
  ContinuousOn f K ∧ (f '' K ⊆ K) → ∃ x ∈ K, f x = x := sorry

noncomputable def pullback_aux {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] (L : C(X, NNReal) →ₗ[NNReal] C(X, NNReal)) (μ : Measure X) :
  CompactlySupportedContinuousMap X NNReal →ₗ[NNReal] NNReal :=
    { toFun := fun f => ⟨∫ x, L f x ∂μ, sorry⟩,
      map_add' := sorry,
      map_smul' := sorry
    }

noncomputable def pullback_measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [OpensMeasurableSpace X] [CompactSpace X] [BorelSpace X]
  (L : C(X, NNReal) →ₗ[NNReal] C(X, NNReal)) (μ : Measure X) :
  Measure X :=
    (rieszContent (pullback_aux L μ)).measure

noncomputable def pullback {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [OpensMeasurableSpace X] [CompactSpace X] [BorelSpace X]
  (L : C(X, NNReal) →ₗ[NNReal] C(X, NNReal)) (μ : Measure X) :
  Measure X :=
    pullback_measure L μ

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

  structure Holder (n : ℕ) (b : NNReal) (α : Ioo 0 1) where
    toFun : PBernoulli n → ℝ
    isHolder : ∀ x y : PBernoulli n, ∀ k : ℕ,
      y ∈ cylinder x k → |toFun x - toFun y| ≤ b * α ^ k

  def shift (x : PBernoulli n) : PBernoulli n := fun i => x (i + 1)

  -- Définition de l'opérateur de transfert
  instance : Fintype (preimage shift {x}) := sorry

  noncomputable def transfert (φ : PBernoulli n → ℝ) (f : PBernoulli n → ℝ) : PBernoulli n → ℝ :=
    fun x => ∑ y ∈ preimage shift {x}, f y * exp (φ y)

  theorem im_transfert_continuous (f : C(PBernoulli n, ℝ)) :
    Continuous (transfert φ f) :=
      by sorry


  variable {b : NNReal} {α : Ioo 0 1}

  noncomputable def L (φ : Holder n b α):
    C(PBernoulli n, ℝ) →ₗ[ℝ] C(PBernoulli n, ℝ) :=
    {
      toFun := λ f : C(PBernoulli n, ℝ) => {
        toFun := transfert φ.toFun f,
        continuous_toFun := im_transfert_continuous f
      }
      map_add' := sorry,
      map_smul' := sorry
    }

  -- TODO: Essayer de split en plusieurs lemmes intermédiaires pour plus comprehensible.
  noncomputable def Lpos (φ : Holder n b α) :
    C(PBernoulli n, NNReal) →ₗ[NNReal] C(PBernoulli n, NNReal) :=
    {
      toFun := λ f : C(PBernoulli n, NNReal) => {
        toFun := λ x : PBernoulli n => ⟨L φ ⟨(λ y : PBernoulli n => (f y).toReal), sorry⟩ x, sorry⟩,
        continuous_toFun := by sorry
      },
      map_add' := sorry,
      map_smul' := sorry
    }

  /-- Définition de la mesure pullback par l'opérateur de transfert associé au potentiel holdérien φ -/
  noncomputable def Lpb (φ : Holder n b α) :
    Measure (PBernoulli n) → Measure (PBernoulli n) :=
      λ μ => pullback (Lpos φ) μ

  /-- Partie 1 du théorème de Ruelle de Perron-Frobenius -/
  theorem RPF1 (φ : Holder n b α) :
    ∃ ν : ProbabilityMeasure (PBernoulli n), ∃ a : NNReal, a > 0 ∧ Lpb φ ν.toMeasure = a • ν.toMeasure :=
    sorry

  noncomputable def ν (φ : Holder n b α) : ProbabilityMeasure (PBernoulli n) := choose (RPF1 φ)

  noncomputable def a (φ : Holder n b α) : NNReal := choose (choose_spec (RPF1 φ))

  theorem RPF1_explicit (φ : Holder n b α) :
    (a φ) > 0 ∧ Lpb φ (ν φ) = (a φ) • (ν φ) :=
    by exact choose_spec (choose_spec (RPF1 φ))

  noncomputable def logBm (_ : Holder n b α) : ℕ → ℝ :=
    λ m => 2 * b * ∑' k, if k > m then (α : ℝ)^k else 0

  noncomputable def Bm (φ : Holder n b α) : ℕ → NNReal :=
    λ m => ⟨exp (logBm φ m), exp_nonneg (logBm φ m)⟩

end RPF
