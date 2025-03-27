import Mathlib

open TopologicalSpace Metric Set Classical

variable {X : Type*} [PseudoMetricSpace X] [hX : IsUltrametricDist X]

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

def equiv_class (U : Set (balls X)) (u : U) : Set U := {v : U | rel U u v}

-- FIX : réécrire les hyp : IsUltrametricDist pas utilisé
omit hX in
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

lemma union_class_mem_balls (U : Set (balls X)) (u : U)
  (Ubdd : ∃ (x: X), ∃ r > 0, ⋃₀ U ⊆ ball x r) : -- Hypothèse gratuite si l'ouvert est borné
    ⋃ (v : equiv_class U u), v ∈ balls X := by
  have key (v : {w : U // u.1.1 ⊆ w.1.1}) := v.1.1.2.out
  choose C r r_pos v_ball using key

  obtain ⟨x, R, R_pos, U_union_sub_ball⟩ := Ubdd
  let ra (w : {w : U // u.1.1 ⊆ w.1.1}) : ℝ := if r w ≥ R then R else r w
  have ra_pos (w : {w : U // u.1.1 ⊆ w.1.1}) : ra w > 0 := by
    by_cases h : r w ≥ R
    all_goals simp [ra, h]
    . exact R_pos
    . exact r_pos w

  have U_ball_eq (w : {w : U // u.1.1 ⊆ w.1.1}) : ball x R = ball (C w) R := by
    refine IsUltrametricDist.ball_eq_of_mem ?_
    refine mem_of_mem_of_subset (mem_ball_self (r_pos w)) ?_
    refine subset_trans ?_ U_union_sub_ball
    rw [←v_ball w]
    simp only [sUnion_image]
    apply subset_iUnion_of_subset ⟨w.1.1, w.1.1.2⟩
    simp

  have ball_r_eq_ra (w : {w : U // u.1.1 ⊆ w.1.1}) : ball (C w) (r w) = ball (C w) (ra w) := by
    by_cases h : r w ≥ R
    all_goals simp [ra, h]
    refine subset_antisymm ?_ (ball_subset_ball h)
    rw [←U_ball_eq w]
    refine subset_trans ?_ U_union_sub_ball
    rw [← v_ball w]
    simp only [sUnion_image]
    apply subset_iUnion_of_subset ⟨w.1.1, w.1.1.2⟩
    simp

  have union_ball :
      ⋃ v : {w : U // u.1.1 ⊆ w.1.1}, v = ⋃ v : {w : U // u.1.1 ⊆ w.1.1}, ball (C v) (ra v) := by
    simp only [v_ball]; exact iUnion_congr ball_r_eq_ra
  rw [union_class_eq U u, union_ball]

  have h1 (w : {w : U // u.1.1 ⊆ w.1.1}) : (C ⟨u, subset_rfl⟩) ∈ ball (C w) (ra w) := by
    rw [←ball_r_eq_ra w, ←v_ball w]
    refine mem_of_mem_of_subset ?_ w.2
    set u' : {w : U // u.1.1 ⊆ w.1.1} := ⟨u, subset_rfl⟩
    rw [v_ball u']
    exact mem_ball_self (r_pos u')

  have sU_nonempty : Nonempty {w : U // u.1.1 ⊆ w.1.1} := ⟨u, by simp⟩
  refine union_mem_balls C ra ra_pos h1 ?_
  rw [bddAbove_def]
  use R
  intro rw hrw
  simp only [range, mem_setOf_eq] at hrw
  obtain ⟨w, rw_eq⟩ := hrw
  rw [← rw_eq]
  simp [ra]
  by_cases h : R ≤ r w
  all_goals simp [h]
  push_neg at h
  exact le_of_lt h


theorem open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) :
    ∃ s ⊆ balls X, O = ⋃₀ s ∧ s.PairwiseDisjoint id := by
  sorry
