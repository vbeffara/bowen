import Mathlib

/-- Schauder-Tychonoff Theorem: A compact convex subset of a locally convex linear
topological space has the fixed point property. -/
theorem schauder_tychonoff
  {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {K : Set E} (hK : IsCompact K) (hK_convex : Convex NNReal K) (f : E → E)
  (hf_cont : ContinuousOn f K) (hK : f '' K ⊆ K) :
    ∃ x ∈ K, f x = x := sorry
