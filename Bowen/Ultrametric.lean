import Mathlib

open TopologicalSpace Metric Set Classical

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

lemma metric_space_topological_basis {X : Type*} [PseudoMetricSpace X] :
    IsTopologicalBasis {b : Set X | ∃ x r, 0 < r ∧ b = ball x r} := by
  have h_open : ∀ o ∈ {b : Set X | ∃ x r, 0 < r ∧ b = ball x r}, IsOpen o := by
    intros b hb
    simp_all only [mem_setOf_eq]
    obtain ⟨x, r, r_pos, b_eq_ball⟩ := hb
    rw [b_eq_ball]
    exact isOpen_ball
  have h_nhds : ∀ (x : X) (u : Set X), x ∈ u → IsOpen u →
      ∃ v ∈ {b : Set X | ∃ x r, 0 < r ∧ b = ball x r}, x ∈ v ∧ v ⊆ u := by
    intros x u hx_in_u hu_open
    rw [isOpen_iff] at hu_open
    obtain ⟨r, r_pos, h_ball_sub⟩ := hu_open x hx_in_u
    use ball x r
    split_ands
    . simp_all
      exact ⟨x, r, r_pos, rfl⟩
    . simp_all
    . exact h_ball_sub
  exact isTopologicalBasis_of_isOpen_of_nhds h_open h_nhds

lemma open_eq_union_ball {X : Type*} [PseudoMetricSpace X] (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ {b : Set X | ∃ x r, 0 < r ∧ b = ball x r}, O = ⋃₀ s := by
      exact IsTopologicalBasis.open_eq_sUnion metric_space_topological_basis hO

def rel (u v : Set X) : Prop :=
  ∃ w ∈ {b : Set X | ∃ x r, 0 < r ∧ b = ball x r}, u ⊆ w ∧ v ⊆ w

instance : IsEquiv {b : Set X | ∃ x r, 0 < r ∧ b = ball x r} (fun ⟨u, hu⟩ ⟨v, hv⟩ => rel u v) where
  refl u := by
    obtain ⟨u', hu⟩ := u
    simp_all only [rel, mem_setOf_eq, and_self]
    use u'
    simp_all only [mem_setOf_eq, subset_refl, and_self]
  symm u v := by
    intro huv
    simp_all only [rel]
    obtain ⟨w, hwU, huw, hvw⟩ := huv
    exact ⟨w, hwU, hvw, huw⟩
  trans u v w := by
    obtain ⟨u, xu, ru, ru_pos, u_ball⟩ := u
    obtain ⟨v, xv, rv, rv_pos, v_ball⟩ := v
    obtain ⟨w, xw, rw, rw_pos, w_ball⟩ := w
    intros huv hvw
    simp_all only [rel]
    obtain ⟨s, ⟨xs, rs, rs_pos, s_ball⟩, u_sub_s, v_sub_s⟩ := huv
    obtain ⟨t, ⟨xt, rt, rt_pos, t_ball⟩, v_sub_t, w_sub_t⟩ := hvw
    simp_all
    have v_sub_inter : v ⊆ s ∩ t := by simp_all only [subset_inter_iff, and_self]
    have s_sub_or_t_sub : s ⊆ t ∨ t ⊆ s := by
      rw [s_ball, t_ball]
      rcases IsUltrametricDist.ball_subset_trichotomy xs xt rs rt with s_sub | t_sub | dis
      . left; exact s_sub
      . right; exact t_sub
      . sorry
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
