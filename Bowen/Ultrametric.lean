import Mathlib

open TopologicalSpace Metric Set Classical

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

def balls (X : Type*) [PseudoMetricSpace X] : Set (Set X) := {b | ∃ x, ∃ r > 0, b = ball x r}

lemma metric_space_topological_basis {X : Type*} [PseudoMetricSpace X] :
    IsTopologicalBasis (balls X) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  . rintro s ⟨x, r, _, rfl⟩
    exact isOpen_ball
  . intros x u hx_in_u hu_open
    rw [isOpen_iff] at hu_open
    obtain ⟨r, r_pos, h_ball_sub⟩ := hu_open x hx_in_u
    refine ⟨ball x r, ⟨x, r, r_pos, rfl⟩, mem_ball_self r_pos, h_ball_sub⟩

lemma open_eq_union_ball {X : Type*} [PseudoMetricSpace X] (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ balls X, O = ⋃₀ s :=
  IsTopologicalBasis.open_eq_sUnion metric_space_topological_basis hO

def rel (U : Set (balls X)) (u v : U) : Prop := ∃ w ∈ U, u.1.1 ⊆ w ∧ v.1.1 ⊆ w

-- Transitivite vient de la distance ultrametrique
lemma rel_equiv {U : Set (balls X)} : Equivalence (rel U) where
  refl s := ⟨s, by simp⟩
  symm {u v} := by
    rintro ⟨w, hw1, hw⟩
    exact ⟨w, hw1, hw.symm⟩
  trans {u v w} := by
    rintro ⟨s, sU, u_sub_s, v_sub_s⟩ ⟨t, tU, v_sub_t, w_sub_t⟩
    have key : s.1 ⊆ t.1 ∨ t.1 ⊆ s.1 ∨ Disjoint s.1 t.1 := by
      obtain ⟨s, xs, rs, rs_pos, rfl, hsU⟩ := s
      obtain ⟨t, xt, rt, rt_pos, rfl, htU⟩ := t
      apply IsUltrametricDist.ball_subset_trichotomy
    rcases key with s_sub | t_sub | dis
    · exact ⟨t, tU, u_sub_s.trans s_sub, w_sub_t⟩
    · exact ⟨s, sU, u_sub_s, w_sub_t.trans t_sub⟩
    · contrapose dis
      apply Nonempty.not_disjoint
      rcases v with ⟨⟨v, xv, rv, rv_pos, rfl⟩, hvU⟩
      have : xv ∈ ball xv rv := mem_ball_self rv_pos
      exact ⟨xv, v_sub_s this, v_sub_t this⟩

instance balls_U (U : Set (balls X)) : Setoid U := ⟨rel U, rel_equiv⟩

lemma union_mem_balls {ι : Type*} [Nonempty ι] (C : ι → X) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    {x : X} (h1 : ∀ i, x ∈ ball (C i) (R i)) (h2 : BddAbove (range R)) :
    ⋃ i, ball (C i) (R i) ∈ balls X := by
  refine ⟨x, iSup R, ?_, ?_⟩
  · let i₀ : ι := Nonempty.some inferInstance
    have h1 := hR i₀
    have h2 := le_ciSup h2 i₀
    linarith
  · have (i) : ball (C i) (R i) = ball x (R i) := IsUltrametricDist.ball_eq_of_mem (h1 i)
    ext z
    symm
    simpa [this] using lt_ciSup_iff h2

-- def Urepr (U : Set (Set X)) : Set (Set X) := {x | ∃ (q : Quotient (balls_U U)), Quotient.out q = x}

lemma has_max (U : Set (balls X)) (u : Quotient (balls_U U)) :
    ∃ v : U, Maximal (fun w => ⟦w⟧ = u) v := sorry
  -- TODO : Verfier que c'est vrai
  -- Piste : Lemme de Zorn

theorem open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ balls X, O = ⋃₀ s ∧ s.PairwiseDisjoint id := by
  sorry
