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
  have key (a : U) : ∃ x, ∃ r > 0, a.1.1 = ball x r := a.1.2
  choose C r hr hCr using key
  simp only [sUnion_image, biUnion_eq_iUnion, hCr]
  have hU : Nonempty U := sorry
  obtain ⟨x, hx⟩ : ∃ x, ∀ i, x ∈ ball (C i) (r i) := sorry
  apply union_mem_balls C r hr hx
  sorry

def equiv_class (U : Set (balls X)) (u : U) : Set U := {v : U | rel U u v}

-- FIX : réécrire les hyp : IsUltrametricDist pas utilisé
lemma union_class_eq (U : Set (balls X)) (u : U) :
    ⋃ (v : equiv_class U u), v = ⋃ v : {w : U // u.1.1 ⊆ w.1.1}, v.1.1.1 := by
  apply subset_antisymm
  all_goals rw [subset_def]
  all_goals intros w hw
  all_goals simp_all only [mem_iUnion, exists_prop, mem_setOf_eq]
  all_goals simp
  . obtain ⟨⟨v, ⟨s, s_mem_U, u_sub_s, v_sub_s⟩⟩, w_mem_v⟩ := hw
    refine ⟨s, u_sub_s, ?_⟩
    simp
    exact ⟨s_mem_U, mem_of_mem_of_subset w_mem_v v_sub_s⟩
  . obtain ⟨⟨v, u_sub_v⟩, hv⟩ := hw
    refine ⟨v, ?_, hv⟩
    simp [equiv_class, rel]
    use v
    simpa

lemma union_class_mem_balls (U : Set (balls X)) (u : U) (hu : u.1.1.Nonempty)
  (Ubdd : ∃ (x: X), ∃ r > 0, ⋃₀ U ⊆ ball x r) : -- Hypothèse gratuite si l'ouvert est borné
    ⋃ (v : equiv_class U u), v ∈ balls X := by
  have key (v : {w : U // u.1.1 ⊆ w.1.1}) := v.1.1.2.out
  choose C r r_pos v_ball using key

  have union_ball :
    ⋃ v : {w : U // u.1.1 ⊆ w.1.1}, v = ⋃ v : {w : U // u.1.1 ⊆ w.1.1}, ball (C v) (r v) := by
    simp only [v_ball]
  rw [union_class_eq U u, union_ball]

  obtain ⟨x, x_mem_u⟩ := hu
  have h1 (v : {w : U // u.1.1 ⊆ w.1.1}) : x ∈ ball (C v) (r v) := by
    rw [← v_ball v]
    obtain ⟨v, u_sub_v⟩ := v
    exact mem_of_mem_of_subset x_mem_u u_sub_v
  have sU_nonempty : Nonempty {w : U // u.1.1 ⊆ w.1.1} := ⟨u, by simp⟩
  refine union_mem_balls C r r_pos h1 ?_

  rw [bddAbove_def]
  obtain ⟨x, R, R_pos, U_union_sub_ball⟩ := Ubdd
  use R
  intros rb rb_range
  simp only [range, mem_setOf_eq] at rb_range
  obtain ⟨w, rb_eq⟩ := rb_range
  have w_sub_ball : w.1.1.1 ⊆ ball x R := by
    refine subset_trans ?_ U_union_sub_ball
    simp only [sUnion_image]
    apply subset_iUnion_of_subset ⟨w.1.1, w.1.1.2⟩
    simp
  rw [v_ball w] at w_sub_ball
  have ball_eq_ballC : ball x R = ball (C w) R := by
    refine IsUltrametricDist.ball_eq_of_mem ?_
    apply mem_of_subset_of_mem w_sub_ball
    exact mem_ball_self (r_pos w)
  rw [ball_eq_ballC, rb_eq] at w_sub_ball
  -- FIX : Missing lemma in Mathlib : w_sub_ball → rb ≤ R
  sorry

theorem open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ balls X, O = ⋃₀ s ∧ s.PairwiseDisjoint id := by
  sorry
