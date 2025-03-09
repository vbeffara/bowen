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

def rel (U : Set (Set X)) (u v : Set X) : Prop :=
  ∃ w ∈ {b : Set X | ∃ x r, 0 < r ∧ b = ball x r} ∩ U, u ⊆ w ∧ v ⊆ w

-- Transitivite vient de la distance ultrametrique
lemma rel_equiv (U : Set (Set X)) :
    Equivalence (fun (u v : {b : Set X | ∃ x r, 0 < r ∧ b = ball x r ∧ b ∈ U}) => rel U u v) where
  refl := by
    intro u
    obtain ⟨u, xu, ru, ru_pos, u_ball, u_in_U⟩ := u
    simp_all only [rel, mem_setOf_eq, and_self]
    use u
    simp_all only [mem_inter_iff, mem_setOf_eq, subset_refl, and_true]
    exact ⟨xu, ⟨ru, ru_pos, rfl⟩⟩
  symm := by
    intros u v huv
    simp_all only [rel]
    obtain ⟨w, hwU, huw, hvw⟩ := huv
    exact ⟨w, hwU, hvw, huw⟩
  trans := by
    intros u v w
    obtain ⟨u, xu, ru, ru_pos, u_ball, u_in_U⟩ := u
    obtain ⟨v, xv, rv, rv_pos, v_ball, v_in_U⟩ := v
    obtain ⟨w, xw, rw, rw_pos, w_ball, w_in_U⟩ := w
    intros huv hvw
    simp_all only [rel, mem_inter_iff]
    obtain ⟨s, ⟨⟨xs, rs, rs_pos, s_ball⟩, hsU⟩, u_sub_s, v_sub_s⟩ := huv
    obtain ⟨t, ⟨⟨xt, rt, rt_pos, t_ball⟩, htU⟩, v_sub_t, w_sub_t⟩ := hvw
    have v_sub_inter : v ⊆ s ∩ t := by simp_all only [subset_inter_iff, and_self]
    have v_nonempty : v ≠ ∅ := by simp_all
    have inter_nonempty : s ∩ t ≠ ∅ := by
      intro is_empty
      exact v_nonempty (subset_eq_empty v_sub_inter is_empty)
    have s_sub_or_t_sub : s ⊆ t ∨ t ⊆ s := by
      rw [s_ball, t_ball]
      rcases IsUltrametricDist.ball_subset_trichotomy xs xt rs rt with s_sub | t_sub | dis
      . left; exact s_sub
      . right; exact t_sub
      . rw [← s_ball, ← t_ball, disjoint_iff_inter_eq_empty] at dis
        simp at inter_nonempty
        exfalso
        exact inter_nonempty dis

    rcases s_sub_or_t_sub with s_sub | t_sub
    . use t
      split_ands
      . exact ⟨xt, rt, rt_pos, t_ball⟩
      . exact htU
      . exact subset_trans u_sub_s s_sub
      . exact w_sub_t
    . use s
      split_ands
      . exact ⟨xs, rs, rs_pos, s_ball⟩
      . exact hsU
      . exact u_sub_s
      . exact subset_trans w_sub_t t_sub

instance balls_U (U : Set (Set X)) : Setoid {b | ∃ x r, 0 < r ∧ b = ball x r ∧ b ∈ U} where
  r := fun u v => rel U u v
  iseqv := rel_equiv U

def Urepr (U : Set (Set X)) : Set (Set X) := {x | ∃ (q : Quotient (balls_U U)), Quotient.out q = x}

lemma has_max (U : Set (Set X)) (u : Quotient (balls_U U)) :
    ∃ v : {b : Set X | ∃ x r, 0 < r ∧ b = ball x r ∧ b ∈ U},
      Maximal (fun w => ⟦w⟧ = u) v := sorry
  -- TODO : Verfier que c'est vrai
  -- Piste : Lemme de Zorn

theorem open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ {b : Set X | ∃ x r, b = ball x r}, O = ⋃₀ s ∧ s.PairwiseDisjoint id := by
  sorry

