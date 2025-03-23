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

instance quot_U (U : Set (balls X)) : Setoid U := ⟨rel U, rel_equiv⟩

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

lemma union_balls_mem_balls (U : Set (balls X)) :
    ⋃₀ U ∈ balls X := by
  simp only [sUnion_image]
  let C (a : U) := choose a.1.2.out
  let r (a : U) := choose (choose_spec a.1.2.out)
  have Cr_prop (a : U) := choose_spec (choose_spec a.1.2.out)
  sorry

def equiv_class (U : Set (balls X)) (u : U) : Set U := {v : U | rel U u v}

-- FIX : réécrire les hyp : IsUltrametricDist pas utilisé
lemma union_class_eq (U : Set (balls X)) (u : U) :
    ⋃ (v ∈ equiv_class U u), v = ⋃ v ∈ {w : U | u.1.1 ⊆ w.1.1}, v.1.1 := by
  apply subset_antisymm
  all_goals rw [subset_def]
  all_goals intros w hw
  all_goals simp_all only [mem_iUnion, exists_prop, mem_setOf_eq]
  . obtain ⟨v, ⟨s, hsU, hu_sub_s, hv_sub_s⟩, hw_mem_v⟩ := hw
    use ⟨s, hsU⟩
    simp only
    exact ⟨hu_sub_s, mem_of_mem_of_subset hw_mem_v hv_sub_s⟩
  . obtain ⟨v, u_sub_v, w_mem_v⟩ := hw
    refine ⟨v, ?_, w_mem_v⟩
    simp [equiv_class, rel]
    use v
    simp [exists_prop]
    exact u_sub_v

lemma union_class_mem_balls (U : Set (balls X)) (u : U) :
    ⋃ (v ∈ equiv_class U u), v ∈ balls X := by
  have v_ball (v : U) (hv : v ∈ equiv_class U u) : v.1.1 ∈ balls X := sorry
  sorry

theorem open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ balls X, O = ⋃₀ s ∧ s.PairwiseDisjoint id := by
  sorry
