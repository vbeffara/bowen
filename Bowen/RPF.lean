import Mathlib
import Bowen.Bernoulli

open Set Real MeasureTheory Classical Filter
open Bernoulli

/-- Schauder-Tychonoff Theorem: A compact convex subset of a locally convex linear
topological space has the fixed point property. -/
theorem schauder_tychonoff
  {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {K : Set E} (hK : IsCompact K) (hK_convex : Convex ℝ K) (f : E → E)
  (hf_cont : ContinuousOn f K) (hK : f '' K ⊆ K) :
    ∃ x ∈ K, f x = x := sorry

noncomputable def pullback_aux {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] (L : C(X, NNReal) →ₗ[NNReal] C(X, NNReal)) (μ : Measure X) :
  CompactlySupportedContinuousMap X NNReal →ₗ[NNReal] NNReal :=
    { toFun := fun f => ⟨∫ x, L f x ∂μ, sorry⟩,
      map_add' := sorry,
      map_smul' := sorry
    }

noncomputable def pullback {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [OpensMeasurableSpace X] [CompactSpace X] [BorelSpace X]
  (L : C(X, NNReal) →ₗ[NNReal] C(X, NNReal)) (μ : Measure X) :
  Measure X :=
    (rieszContent (pullback_aux L μ)).measure

namespace RPF

  instance : ContainN ℕ where
    fromNat x := x
    var_supp x := Ico 0 x
    shift x := x + 1

  variable {n : ℕ} {x y z : Bernoulli ℕ n}

  -- TODO: A revoir pour que cette structure soit inclus dans C_c
  /- structure Holder (n : ℕ) (b : NNReal) (α : Ioo 0 1) where -/
  /-   toFun : CompactlySupportedContinuousMap (Bernoulli ℕ n) ℝ -/
  /-   isHolder : ∀ x y : Bernoulli ℕ n, ∀ k : ℕ, -/
  /-     y ∈ cylinder x k → |toFun x - toFun y| ≤ b * α ^ k -/

  /- def shift (x : Bernoulli ℕ n) : Bernoulli ℕ n := fun i => x (i + 1) -/

  -- Définition de l'opérateur de transfert
  instance : Fintype (preimage shift {x}) := sorry

  noncomputable def transfert (φ : Bernoulli ℕ n → ℝ) (f : Bernoulli ℕ n → ℝ) : Bernoulli ℕ  n → ℝ :=
    fun x => ∑ y ∈ preimage shift {x}, f y * exp (φ y)

  theorem im_transfert_continuous (f : C(Bernoulli ℕ n, ℝ)) :
    Continuous (transfert φ f) :=
      by sorry

  variable (φ : Bernoulli ℕ n → ℝ) [HolderLike φ]

  /-- RPF1 -/

  noncomputable def L :
    C(Bernoulli ℕ  n, ℝ) →ₗ[ℝ] C(Bernoulli ℕ n, ℝ) :=
    {
      toFun := λ f : C(Bernoulli ℕ n, ℝ) => {
        toFun := transfert φ f,
        continuous_toFun := im_transfert_continuous f
      }
      map_add' := sorry,
      map_smul' := sorry
    }

  -- TODO: Essayer de split en plusieurs lemmes intermédiaires pour plus comprehensible.
  noncomputable def Lpos :
    C(Bernoulli ℕ n, NNReal) →ₗ[NNReal] C(Bernoulli ℕ n, NNReal) :=
    {
      toFun := λ f : C(Bernoulli ℕ n, NNReal) => {
        toFun := λ x : Bernoulli ℕ n => ⟨L φ ⟨(λ y : Bernoulli ℕ n => (f y).toReal), sorry⟩ x, sorry⟩,
        continuous_toFun := by sorry
      },
      map_add' := sorry,
      map_smul' := sorry
    }

  /-- Définition de la mesure pullback par l'opérateur de transfert associé au potentiel holdérien φ -/
  noncomputable def Lpb :
    Measure (Bernoulli ℕ n) → Measure (Bernoulli ℕ n) :=
      λ μ => pullback (Lpos φ) μ

  /-- Partie 1 du théorème de Ruelle de Perron-Frobenius -/
  theorem RPF1 :
    ∃ ν : ProbabilityMeasure (Bernoulli ℕ n), ∃ a : NNReal, a > 0 ∧ Lpb φ ν.toMeasure = a • ν.toMeasure :=
    sorry

  noncomputable def ν : ProbabilityMeasure (Bernoulli ℕ n) := choose (RPF1 φ)

  noncomputable def a : NNReal := choose (choose_spec (RPF1 φ))

  theorem RPF1_explicit (φ : Bernoulli ℕ n → ℝ) [HolderLike φ]:
    a φ > 0 ∧ Lpb φ (ν φ) = a φ • ν φ :=
    by exact choose_spec (choose_spec (RPF1 φ))

  /-- RPF2 -/

  noncomputable def logBm : ℕ → ℝ :=
    λ m => 2 * HolderLike.b φ * tsum (fun k : Ioi m => (HolderLike.α φ : ℝ)^(k : ℕ))

  noncomputable def Bm : ℕ → NNReal :=
    λ m => ⟨exp (logBm φ m), exp_nonneg (logBm φ m)⟩

  /-- Norme infinie d'une fonction holderienne -/
  /- noncomputable def holderNorm (φ : Holder n b α) : NNReal := sSup {|φ.toFun x| | x : Bernoulli ℕ n} -/

  noncomputable def K : NNReal :=
    (a φ) * (Bm φ 0) * ⟨exp (HolderLike.norm φ), exp_nonneg (HolderLike.norm φ)⟩

  def IsBmBounded (f : C(Bernoulli ℕ n, ℝ)) : Prop :=
    ∀ m : ℕ, ∀ x x': Bernoulli ℕ n, x' ∈ cylinder x m → f x ≤ (Bm φ m) * f x'

  noncomputable def Λ : Set (C(Bernoulli ℕ n, ℝ)) :=
    {f : C(Bernoulli ℕ n, ℝ) | f ≥ 0 ∧ ∫ x, f x ∂(ν φ) = 1 ∧ IsBmBounded φ f}

  def one : C(Bernoulli ℕ n, ℝ) :=
    {
      toFun := λ _ => 1,
      continuous_toFun := continuous_const
    }

  lemma Lambda_one : one ∈ (Λ φ) := by sorry

  lemma Lf_ge_invK (f : C(Bernoulli ℕ n, ℝ)) (x : Bernoulli ℕ n) : K φ * (L φ f) x ≥ a φ := sorry

  lemma Lambda_IsCompact : IsCompact (Λ φ) := sorry

  theorem RPF2 :
    ∃ h : C(Bernoulli ℕ n, ℝ), h ∈ Λ φ ∧ h > 0 ∧ ∫ x, h x ∂(ν φ) = 1 ∧ (L φ h) = (a φ) • h := sorry

  noncomputable def h : C(Bernoulli ℕ n, ℝ) := choose (RPF2 φ)

  theorem RPF2_explicit :
    h φ ∈ Λ φ ∧ (h φ) > 0 ∧ ∫ x, (h φ) x ∂(ν φ) = 1 ∧ (L φ (h φ)) = (a φ) • (h φ) :=
    by exact choose_spec (RPF2 φ)

  noncomputable def h_pos : C(Bernoulli ℕ n, NNReal) :=
    {
      toFun := λ x => ⟨(h φ) x, sorry⟩,
      continuous_toFun := sorry
    }

  /-- RPF3 -/

  def decomp (η : ℝ) (f : C(Bernoulli ℕ n, ℝ)) : Prop :=
    ∃ f' : C(Bernoulli ℕ n, ℝ), f' ∈ Λ φ ∧
      (a φ) • (L φ f) = η • (h φ) + (1 - η) • f'

  lemma Lf_decomp :
    ∃ η : ℝ, η > 0 ∧ ∀ f : C(Bernoulli ℕ n, ℝ), f ∈ Λ φ ∧ decomp φ η f := sorry

  noncomputable def η : ℝ := choose (Lf_decomp φ)

  lemma Lf_decomp_explicit : (η φ) > 0 ∧ ∀ f, f ∈ Λ φ ∧ decomp φ (η φ) f :=
    choose_spec (Lf_decomp φ)

  noncomputable def norm (f : C(Bernoulli ℕ n, ℝ)) : NNReal := sSup {|f x| | x : Bernoulli ℕ n}

  noncomputable def norm_Lf_sub_h (f : C(Bernoulli ℕ n, ℝ)) : ℕ → NNReal :=
    λ k => norm ((1 / (a φ)^k) • (L φ)^[k] f - (h φ))

  lemma conv_expo :
    ∃ A β : ℝ, A > 0 ∧ β ∈ Ioo 0 1 ∧ ∀ k : ℕ, ∀ f : C(Bernoulli ℕ n, ℝ), f ∈ Λ φ →
      norm_Lf_sub_h φ f k ≤ A * β ^ k :=
    sorry

  noncomputable def var_k (φ : C(Bernoulli ℕ n, ℝ)) : ℕ → NNReal :=
    λ k => sSup { d | ∀ x y : Bernoulli ℕ n, x ∈ cylinder y k ∧ d = |φ x - φ y|}

  /-- Fonction en escaliers à n^r étages -/
  noncomputable def C_r : ℕ → Set (C(Bernoulli ℕ n, ℝ)) :=
    λ r => {f | var_k f r = 0}

  /-- Ensemble des fonctions en escaliers -/
  noncomputable def C : Set (C(Bernoulli ℕ n, ℝ)) := ⋃ r, C_r r

  lemma stab_mul_Cr (F f : C(Bernoulli ℕ n, ℝ)) (r : ℕ)
    (hf : f ∈ C_r r) (hF : Λ φ F) (hfF : f * F ≠ 0) (hf_pos : f ≥ 0):
      ((1 / ((a φ : ℝ) * (∫ x, ((f * F) x) ∂(ν φ)))) • (L φ)^[r] (f * F)) ∈ Λ φ :=
    sorry

  noncomputable def norm_Lf_sub_nu_h (f: C(Bernoulli ℕ n, ℝ)) : ℕ → NNReal :=
    λ k => norm ((1 / (a φ)^k) • (L φ)^[k] f - (∫ x, f x ∂(ν φ)) • (h φ))

  lemma RPF3_Lam_Cr (r : ℕ) :
    ∃ A β : ℝ, A > 0 ∧ β ∈ Ioo 0 1 ∧
      ∀ f F : C(Bernoulli ℕ n, ℝ), f ∈ C_r r ∧ F ∈ Λ φ →
        norm_Lf_sub_h φ (f * F) (n + r) ≤ A * (β ^ n) * (∫ x, |(f * F) x|∂(ν φ)) :=
    sorry

  lemma C_strong_density (f : C(Bernoulli ℕ n, ℝ)) (ε : NNReal) (hε : ε > 0):
    ∃ g₁ g₂ : C(Bernoulli ℕ n, ℝ),
      g₁ ∈ C ∧ g₂ ∈ C ∧
      norm (g₁ - g₂) ≤ ε ∧
      g₁ ≤ f ≤ g₂ :=
    sorry

  theorem RPF3 (f : C(Bernoulli ℕ n, ℝ)):
    Tendsto (norm_Lf_sub_nu_h φ f) atTop (nhds 0) :=
    sorry

  noncomputable def μ : Measure (Bernoulli ℕ n) :=
    (ν φ).toMeasure.withDensity (λ x => h_pos φ x)

  lemma mu_prob : IsProbabilityMeasure (μ φ) := sorry

  lemma mu_shift_inv : (μ φ).map shift = μ φ := sorry

end RPF
