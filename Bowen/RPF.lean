import Mathlib

open Set Real MeasureTheory Classical Filter


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

  -- TODO: A revoir pour que cette structure soit inclus dans C_c
  structure Holder (n : ℕ) (b : NNReal) (α : Ioo 0 1) where
    toFun : CompactlySupportedContinuousMap (PBernoulli n) ℝ
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

  /-- RPF1 -/

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

  /-- RPF2 -/

  noncomputable def logBm (_ : Holder n b α) : ℕ → ℝ :=
    λ m => 2 * b * tsum (fun k : Ioi m => (α : ℝ)^(k : ℕ))

  noncomputable def Bm (φ : Holder n b α) : ℕ → NNReal :=
    λ m => ⟨exp (logBm φ m), exp_nonneg (logBm φ m)⟩

  /-- Norme infinie d'une fonction holderienne -/
  noncomputable def holderNorm (φ : Holder n b α) : NNReal := sSup {|φ.toFun x| | x : PBernoulli n}

  noncomputable def K (φ : Holder n b α) : NNReal :=
    (a φ) * (Bm φ 0) * ⟨exp (holderNorm φ), exp_nonneg (holderNorm φ)⟩

  def IsBmBounded (φ : Holder n b α) (f : C(PBernoulli n, ℝ)) : Prop :=
    ∀ m : ℕ, ∀ x x': PBernoulli n, x' ∈ cylinder x m → f x ≤ (Bm φ m) * f x'

  noncomputable def Λ (φ : Holder n b α) : Set (C(PBernoulli n, ℝ)) :=
    {f : C(PBernoulli n, ℝ) | f ≥ 0 ∧ ∫ x, f x ∂(ν φ) = 1 ∧ IsBmBounded φ f}

  def one : C(PBernoulli n, ℝ) :=
    {
      toFun := λ x => 1,
      continuous_toFun := sorry
    }

  lemma Lambda_one (φ : Holder n b α) : one ∈ Λ φ := sorry

  lemma Lf_ge_invK (φ : Holder n b α) (f : C(PBernoulli n, ℝ)) :
    ∀ x : PBernoulli n, K φ * (L φ f) x ≥ a φ := sorry

  lemma Lambda_IsCompact (φ : Holder n b α) : IsCompact (Λ φ) := sorry

  theorem RPF2 (φ : Holder n b α) :
    ∃ h : C(PBernoulli n, ℝ), h ∈ Λ φ ∧ h > 0 ∧ ∫ x, h x ∂(ν φ) = 1 ∧ (L φ h) = (a φ) • h := sorry

  noncomputable def h (φ : Holder n b α) : C(PBernoulli n, ℝ) := choose (RPF2 φ)

  theorem RPF2_explicit (φ : Holder n b α) :
    (h φ) ∈ Λ φ ∧ (h φ) > 0 ∧ ∫ x, (h φ) x ∂(ν φ) = 1 ∧ (L φ (h φ)) = (a φ) • (h φ) :=
    by exact choose_spec (RPF2 φ)

  noncomputable def h_pos (φ : Holder n b α) : C(PBernoulli n, NNReal) :=
    {
      toFun := λ x => ⟨(h φ) x, sorry⟩,
      continuous_toFun := sorry
    }

  /-- RPF3 -/

  def decomp (φ : Holder n b α) (η : ℝ) (f : C(PBernoulli n, ℝ)) : Prop :=
    ∃ f' : C(PBernoulli n, ℝ), f' ∈ (Λ φ) ∧
      (a φ) • (L φ f) = η • (h φ) + (1 - η) • f'

  lemma Lf_decomp (φ : Holder n b α) :
    ∃ η : ℝ, η > 0 ∧ ∀ f : C(PBernoulli n, ℝ), f ∈ (Λ φ) ∧ decomp φ η f := sorry

  noncomputable def η (φ : Holder n b α) : ℝ := choose (Lf_decomp φ)

  lemma Lf_decomp_explicit (φ : Holder n b α) :
    (η φ) > 0 ∧ ∀ f, f ∈ (Λ φ) ∧ decomp φ (η φ) f :=
    by exact choose_spec (Lf_decomp φ)

  noncomputable def norm (f : C(PBernoulli n, ℝ)) : NNReal := sSup {|f x| | x : PBernoulli n}

  noncomputable def norm_Lf_sub_h (φ : Holder n b α) (f : C(PBernoulli n, ℝ)) : ℕ → NNReal :=
    λ k => norm ((1 / (a φ)^k) • (L φ)^[k] f - (h φ))

  lemma conv_expo (φ : Holder n b α) :
    ∃ A β : ℝ, A > 0 ∧ β ∈ Ioo 0 1 ∧ ∀ k : ℕ, ∀ f : C(PBernoulli n, ℝ), f ∈ (Λ φ) →
      norm_Lf_sub_h φ f k ≤ A * β ^ k :=
    sorry

  noncomputable def var_k (φ : C(PBernoulli n, ℝ)) : ℕ → NNReal :=
    λ k => sSup { d | ∀ x y : PBernoulli n, x ∈ cylinder y k ∧ d = |φ x - φ y|}

  /-- Fonction en escaliers à n^r étages -/
  noncomputable def C_r : ℕ → Set (C(PBernoulli n, ℝ)) :=
    λ r => {f | var_k f r = 0}

  /-- Ensemble des fonctions en escaliers -/
  noncomputable def C : Set (C(PBernoulli n, ℝ)) := ⋃ r, C_r r

  lemma stab_mul_Cr (φ : Holder n b α) (F f : C(PBernoulli n, ℝ)) (r : ℕ) :
    f ∈ C_r r ∧ F ∈ Λ φ ∧ f * F ≠ 0 ∧ f ≥ 0 →
      (1 / ((a φ : ℝ) * (∫ x, ((f * F) x) ∂(ν φ)))) • (L φ)^[r] (f * F) ∈ Λ φ :=
    sorry

  noncomputable def norm_Lf_sub_nu_h (φ : Holder n b α) (f: C(PBernoulli n, ℝ)) : ℕ → NNReal :=
    λ k => norm ((1 / (a φ)^k) • (L φ)^[k] f - (∫ x, f x ∂(ν φ)) • (h φ))

  lemma RPF3_Lam_Cr (φ : Holder n b α) (r : ℕ) :
    ∃ A β : ℝ, A > 0 ∧ β ∈ Ioo 0 1 ∧
      ∀ f F : C(PBernoulli n, ℝ), f ∈ C_r r ∧ F ∈ (Λ φ) →
        norm_Lf_sub_h φ (f * F) (n + r) ≤ A * (β ^ n) * (∫ x, |(f * F) x|∂(ν φ)) :=
    sorry

  lemma C_strong_density :
    ∀ f : C(PBernoulli n, ℝ), ∀ ε > 0, ∃ g₁ g₂ : C(PBernoulli n, ℝ),
      g₁ ∈ C ∧ g₂ ∈ C ∧
      norm (g₁ - g₂) ≤ ε ∧
      g₁ ≤ f ≤ g₂ :=
    sorry

  theorem RPF3 (φ : Holder n b α) :
    ∀ f : C(PBernoulli n, ℝ), Tendsto (norm_Lf_sub_nu_h φ f) atTop (nhds 0) :=
    sorry

  noncomputable def μ (φ : Holder n b α) : Measure (PBernoulli n) :=
    (ν φ).toMeasure.withDensity (λ x => h_pos φ x)

  lemma mu_prob (φ : Holder n b α) : IsProbabilityMeasure (μ φ) := sorry

  lemma mu_shift_inv (φ : Holder n b α) : (μ φ).map shift = μ φ := sorry

end RPF
