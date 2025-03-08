import Mathlib

open TopologicalSpace Metric Set Classical

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

lemma metric_space_topological_basis {X : Type*} [PseudoMetricSpace X] :
    IsTopologicalBasis {b : Set X | ∃ x r, b = ball x r} := by
  have h_open : ∀ o ∈ {b : Set X | ∃ x r, b = ball x r}, IsOpen o := by
    intros b hb
    simp_all only [mem_setOf_eq]
    obtain ⟨x, r, b_eq_ball⟩ := hb
    rw [b_eq_ball]
    exact isOpen_ball
  have h_nhds : ∀ (x : X) (u : Set X), x ∈ u → IsOpen u →
    ∃ v ∈ {b : Set X | ∃ x r, b = ball x r}, x ∈ v ∧ v ⊆ u := by
    intros x u hx_in_u hu_open
    rw [isOpen_iff] at hu_open
    obtain ⟨r, r_pos, h_ball_sub⟩ := hu_open x hx_in_u
    use ball x r
    split_ands
    . simp_all
    . simp_all
    . exact h_ball_sub
  exact isTopologicalBasis_of_isOpen_of_nhds h_open h_nhds

lemma open_eq_union_ball' {X : Type*} [PseudoMetricSpace X] (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ {b : Set X | ∃ x r, b = ball x r}, O = ⋃₀ s := by
      exact IsTopologicalBasis.open_eq_sUnion metric_space_topological_basis hO

def rel (U : Set (Set X)) (u v : Set X) : Prop :=
  ∃ w ∈ U, u ⊆ w ∧ v ⊆ w

instance (O : Set X) (U : Set (Set X)) : IsEquiv U (fun u v => rel U u v) where
  refl u := by simp [rel]; use u; simp_all
  symm u v := by
    intro huv
    simp_all only [rel]
    obtain ⟨w, hwU, huw, hvw⟩ := huv
    exact ⟨w, hwU, hvw, huw⟩
  trans u v w := by
    intros huv hvw
    simp_all only [rel]
    obtain ⟨s, sU, u_sub_s, v_sub_s⟩ := huv
    obtain ⟨t, tU, v_sub_t, w_sub_t⟩ := hvw
    sorry
  -- FIX : Peut-etre changer U par l'ensemble des boules pour avoir trans

theorem open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ {b : Set X | ∃ x r, b = ball x r}, O = ⋃₀ s ∧ s.PairwiseDisjoint id := by
  sorry

/- lemma open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) : -/
/-   ∃ C : Set X, ∃ r : X → ℝ, -/
/-     (∀ x ∈ O, r x > 0) ∧ -/
/-     O = ⋃ x ∈ C, ball x (r x) ∧ -/
/-     PairwiseDisjoint C (fun x => ball x (r x)) := by -/
/-   rw [exists_swap] -/
/-   let r := choose (open_eq_union_ball O hO) -/
/-   have r_pos (x : X) (hx : x ∈ O) : r x > 0 := (choose_spec (open_eq_union_ball O hO)).left x hx -/
/-   have r_iUnion : O = ⋃ x ∈ O, ball x (r x) := (choose_spec (open_eq_union_ball O hO)).right -/
/-   use r -/
/-   simp only [exists_and_left] -/
/-   constructor -/
/-   . exact r_pos -/
/-   . sorry -/
