import Mathlib

open TopologicalSpace Metric Set Classical

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

def balls (X : Type*) [PseudoMetricSpace X] : Set (Set X) := {b | ∃ x r, 0 < r ∧ b = ball x r}

lemma metric_space_topological_basis {X : Type*} [PseudoMetricSpace X] :
    IsTopologicalBasis (balls X) := by
  have h_open : ∀ o ∈ balls X, IsOpen o := by
    rintro s ⟨x, r, -, rfl⟩
    exact isOpen_ball
  have h_nhds x u (hx_in_u : x ∈ u) (hu_open : IsOpen u) : ∃ v ∈ balls X, x ∈ v ∧ v ⊆ u := by
    rw [isOpen_iff] at hu_open
    obtain ⟨r, r_pos, h_ball_sub⟩ := hu_open x hx_in_u
    refine ⟨ball x r, ⟨x, r, r_pos, rfl⟩, mem_ball_self r_pos, h_ball_sub⟩
  exact isTopologicalBasis_of_isOpen_of_nhds h_open h_nhds

lemma open_eq_union_ball {X : Type*} [PseudoMetricSpace X] (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ balls X, O = ⋃₀ s :=
  IsTopologicalBasis.open_eq_sUnion metric_space_topological_basis hO

def rel (U : Set (Set X)) (u v : Set X) : Prop := ∃ w ∈ balls X ∩ U, u ⊆ w ∧ v ⊆ w

-- Transitivite vient de la distance ultrametrique
lemma rel_equiv (U : Set (Set X)) :
    Equivalence (fun (u v : {b ∈ balls X | b ∈ U}) => rel U u v) where
  refl s := ⟨s, by simp⟩
  symm {u v} huv := by
    obtain ⟨w, hwU, huw, hvw⟩ := huv
    exact ⟨w, hwU, hvw, huw⟩
  trans := by
    rintro ⟨u, ⟨⟨xu, ru, ru_pos, rfl⟩, u_in_U⟩⟩
    rintro ⟨v, ⟨⟨xv, rv, rv_pos, rfl⟩, v_in_U⟩⟩
    rintro ⟨w, ⟨⟨xw, rw, rw_pos, rfl⟩, w_in_U⟩⟩
    rintro ⟨s, ⟨⟨xs, rs, rs_pos, rfl⟩, hsU⟩, u_sub_s, v_sub_s⟩
    rintro ⟨t, ⟨⟨xt, rt, rt_pos, rfl⟩, htU⟩, v_sub_t, w_sub_t⟩

    have v_sub_inter : ball xv rv ⊆ ball xs rs ∩ ball xt rt := by
      intro z hz
      exact ⟨v_sub_s hz, v_sub_t hz⟩
    have inter_nonempty : Set.Nonempty (ball xs rs ∩ ball xt rt) := by
      refine ⟨xv, v_sub_s (mem_ball_self rv_pos), v_sub_t (mem_ball_self rv_pos)⟩

    rcases IsUltrametricDist.ball_subset_trichotomy xs xt rs rt with s_sub | t_sub | dis
    · exact ⟨ball xt rt, ⟨⟨xt, rt, rt_pos, rfl⟩, htU⟩, subset_trans u_sub_s s_sub, w_sub_t⟩
    · exact ⟨ball xs rs, ⟨⟨xs, rs, rs_pos, rfl⟩, hsU⟩, u_sub_s, subset_trans w_sub_t t_sub⟩
    · rw [disjoint_iff_inter_eq_empty] at dis
      simp [dis] at inter_nonempty

instance balls_U (U : Set (Set X)) : Setoid {b ∈ balls X | b ∈ U} where
  r := fun u v => rel U u v
  iseqv := rel_equiv U

-- def Urepr (U : Set (Set X)) : Set (Set X) := {x | ∃ (q : Quotient (balls_U U)), Quotient.out q = x}

lemma has_max (U : Set (Set X)) (u : Quotient (balls_U U)) :
    ∃ v : {b ∈ balls X | b ∈ U}, Maximal (fun w => ⟦w⟧ = u) v := sorry
  -- TODO : Verfier que c'est vrai
  -- Piste : Lemme de Zorn

theorem open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ balls X, O = ⋃₀ s ∧ s.PairwiseDisjoint id := by
  sorry
