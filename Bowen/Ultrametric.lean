import Mathlib

open TopologicalSpace Metric Set Classical Topology Function

def balls (X : Type*) [PseudoMetricSpace X] : Set (Set X) := {b | ∃ x, ∃ r > 0, b = ball x r}

variable {X : Type*} [PseudoMetricSpace X] [hX : IsUltrametricDist X] {O : Set X}
  {U : Set (balls X)} {u : U}

omit hX in
lemma metric_space_topological_basis : IsTopologicalBasis (balls X) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  . rintro s ⟨x, r, _, rfl⟩
    exact isOpen_ball
  . intros x u hx_in_u hu_open
    rw [isOpen_iff] at hu_open
    obtain ⟨r, r_pos, h_ball_sub⟩ := hu_open x hx_in_u
    refine ⟨ball x r, ⟨x, r, r_pos, rfl⟩, mem_ball_self r_pos, h_ball_sub⟩

omit hX in
lemma open_eq_union_ball (hO : IsOpen O) : ∃ s : Set (balls X), O = ⋃₀ s := by
  /- #check IsTopologicalBasis.open_eq_sUnion metric_space_topological_basis hO -/
  obtain ⟨s, s_sub_balls, o_eq_union_s⟩ :=
    IsTopologicalBasis.open_eq_sUnion metric_space_topological_basis hO
  let s' : Set (balls X) := {⟨u.1, mem_of_mem_of_subset u.2 s_sub_balls⟩ | u : s}
  use s'
  rw [o_eq_union_s]
  simp [sUnion_image, sUnion_eq_iUnion]
  ext x
  constructor
  all_goals intro x_mem
  . simp_all [s']
    obtain ⟨b, b_mem_s, x_mem_b⟩ := x_mem
    use b
    exact ⟨b_mem_s, mem_of_mem_of_subset b_mem_s s_sub_balls, x_mem_b⟩
  . simp_all [s']
    obtain ⟨b, b_mem_s, b_mem_balls, x_mem_b⟩ := x_mem
    exact ⟨b, b_mem_s, x_mem_b⟩

def ballsIn (O : Set X) : Set (balls X) := {b | ↑b ⊆ O}

omit hX in
@[simp] lemma open_eq_union_ball' (hO : IsOpen O) : ⋃ b ∈ ballsIn O, ↑b = O := by
  ext x
  rw [mem_iUnion₂]
  constructor
  · rintro ⟨b, hb1, hb2⟩
    exact hb1 hb2
  · intro hx
    have h1 := Metric.nhds_basis_ball (x := x)
    have h3 : O ∈ 𝓝 x := hO.mem_nhds hx
    obtain ⟨r, hr1, hr2⟩:= h1.mem_iff.1 h3
    refine ⟨⟨_, x, r, hr1, rfl⟩, hr2, mem_ball_self hr1⟩

omit hX in
@[simp] lemma sUnion_ballsIn_of_isOpen (hO : IsOpen O) : ⋃₀ ballsIn O = O := by
  simp only [sUnion_image, open_eq_union_ball' hO]

def rel (U : Set (balls X)) (u v : U) : Prop := ∃ w ∈ U, u.1.1 ⊆ w ∧ v.1.1 ⊆ w

-- Transitivite vient de la distance ultrametrique
instance rel_equiv : Equivalence (rel U) where
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

def equiv_class (u : U) : Set U := {v : U | rel U u v}

-- FIX : réécrire les hyp : IsUltrametricDist pas utilisé
omit hX in
lemma union_class_eq (u : U) :
    ⋃ (v : equiv_class u), v = ⋃ v : {w : U // u.1.1 ⊆ w.1.1}, v.1.1.1 := by
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

lemma union_class_mem_balls (Ubdd : ∃ (x: X), ∃ r > 0, ⋃₀ U ⊆ ball x r) (u : U) :
    ⋃ (v : equiv_class u), v ∈ balls X := by
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
  rw [union_class_eq u, union_ball]

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

def repr_set (U : Set (balls X)) : Set U :=
  {b | ∃ rb : Quotient (quot_U U), rb.out = b}

example (U : Set (balls X)) : repr_set U = Set.range (Quotient.out : Quotient (quot_U U) → _) := by
  ext u; simp [repr_set]

def max_ball (Ubdd : ∃ (x : X), ∃ r > 0, ⋃₀ U ⊆ ball x r) (u : U) : balls X :=
  ⟨⋃ (v : equiv_class u), v, union_class_mem_balls Ubdd u⟩

lemma equiv_iff {X : Type*} {R : X → X → Prop} (hR : Equivalence R) {x y : X} (h : R x y) {z : X} :
    R x z ↔ R y z :=
  ⟨hR.trans (hR.symm h), hR.trans h⟩

def iBall (Ubdd : ∃ (x : X), ∃ r > 0, ⋃₀ U ⊆ ball x r) : Quotient (quot_U U) → balls X := by
  apply Quotient.lift (max_ball Ubdd)
  rintro a b hab
  have : equiv_class a = equiv_class b := by
    ext v
    exact equiv_iff rel_equiv hab
  simp [max_ball, this]

lemma partition_union (U : Set (balls X)) (Ubdd : ∃ (x : X), ∃ r > 0, ⋃₀ U ⊆ ball x r) :
    ⋃ u ∈ U, u = ⋃ (u ∈ repr_set U), (max_ball Ubdd u).1 := by
  ext x
  constructor
  all_goals intro x_mem
  all_goals simp_all
  . obtain ⟨u, ⟨u_balls, u_mem_U⟩, x_mem_u⟩ := x_mem
    let u : U := ⟨⟨u, u_balls⟩, u_mem_U⟩
    let ur : U := @Quotient.out U (quot_U U) ⟦u⟧ -- quot_U ne peut pas être deviné
    have ur_is_repr : ur ∈ repr_set U := by simp [repr_set]

    refine ⟨ur, ur.1.2, ?_⟩
    simp [max_ball]
    split_ands
    . exact ur_is_repr
    . refine ⟨u, ?hu, x_mem_u⟩
      refine ⟨u.1.2, u.2, ?_⟩
      simp [equiv_class, ur]
      exact Quotient.mk_out u
  . obtain ⟨u, u_balls, ⟨u_in_U, u_repr, x_mem_max_ball⟩⟩ := x_mem
    simp [max_ball] at x_mem_max_ball
    obtain ⟨w, ⟨w_balls, ⟨w_mem_u, w_mem_equiv_u⟩⟩, x_mem_w⟩ := x_mem_max_ball
    exact ⟨w, ⟨w_balls, w_mem_u⟩, x_mem_w⟩

omit hX in
lemma sUnion_ballsIn : ⋃₀ ballsIn O ⊆ O := by
  apply sUnion_subset
  rintro _ ⟨b, hb, rfl⟩
  exact hb

omit hX in
lemma Obdd (O_bdd : ∃ (x : X), ∃ r > 0, O ⊆ ball x r) :
    ∃ x : X, ∃ r > 0, ⋃₀ ballsIn O ⊆ ball x r := by
  obtain ⟨xo, ro, ro_pos, o_sub_ball⟩ := O_bdd
  exact ⟨xo, ro, ro_pos, sUnion_ballsIn.trans o_sub_ball⟩

theorem partition (hO : IsOpen O) (O_bdd : ∃ (x : X), ∃ r > 0, O ⊆ ball x r) :
    let Φ := iBall (Obdd O_bdd)
    ⋃ s, Φ s = O ∧ Pairwise (onFun Disjoint (fun s => (Φ s).1)) := by
  intro Φ ; simp [Φ] ; constructor
  · change ⋃ s, (_ ∘ _) s = O
    rw [← sUnion_range, range_comp, iBall, range_quotient_lift, sUnion_image]
    apply subset_antisymm
    · apply iUnion₂_subset
      rintro b ⟨c, rfl⟩
      simp [max_ball]
      exact fun i i_1 i_2 i => i_2
    · simp (config := { singlePass := true }) [← sUnion_ballsIn_of_isOpen hO]
      rintro x ⟨b, h1, rfl⟩
      apply subset_iUnion_of_subset ⟨b, h1⟩
      dsimp [max_ball]
      refine subset_iUnion_of_subset ⟨_, rel_equiv.refl _⟩ subset_rfl
  · apply Quotient.ind ; rintro b1
    apply Quotient.ind ; rintro b2
    simp [disjoint_iff, iBall, quot_U]
    contrapose!
    rintro hx
    set B1 := max_ball (Obdd O_bdd) b1 with hB1
    set B2 := max_ball (Obdd O_bdd) b2 with hB2
    rcases B1 with ⟨β1, x1, r1, hr1, rfl⟩
    rcases B2 with ⟨β2, x2, r2, hr2, rfl⟩
    dsimp at hx
    have := IsUltrametricDist.ball_subset_trichotomy x1 x2 r1 r2
    rcases this with case_1 | case_2 | case_3
    · refine ⟨⟨ball x2 r2, x2, r2, hr2, rfl⟩, ?_, ?_, ?_⟩
      · unfold max_ball at hB2
        simp at hB2
        simp [hB2]
        apply iUnion₂_subset
        rintro s hs
        apply iUnion₂_subset
        rintro h1 -
        exact h1
      · refine subset_trans ?_ case_1
        unfold max_ball at hB1
        simp at hB1
        simp [hB1]
        apply subset_iUnion_of_subset ↑b1
        simp [equiv_class, rel_equiv.refl]
      · rw [hB2]
        intro x hx
        refine ⟨b2, ?_, hx⟩
        · simp [mem_range, equiv_class]
          exact rel_equiv.refl _
    · refine ⟨⟨ball x1 r1, x1, r1, hr1, rfl⟩, ?_, ?_, ?_⟩
      · unfold max_ball at hB1
        simp at hB1
        simp [hB1]
        apply iUnion₂_subset
        rintro s hs
        apply iUnion₂_subset
        rintro h1 -
        exact h1
      · rw [hB1]
        intro x hx
        refine ⟨b1, ?_, hx⟩
        · simp [mem_range, equiv_class]
          exact rel_equiv.refl _
      · refine subset_trans ?_ case_2
        unfold max_ball at hB2
        simp at hB2
        simp [hB2]
        apply subset_iUnion_of_subset ↑b2
        simp [equiv_class, rel_equiv.refl]
    · simp [disjoint_iff] at case_3
      simp [nonempty_iff_ne_empty] at hx
      contradiction

theorem open_eq_disjoint_union_ball
  (O : Set X) (hO : IsOpen O) (O_bdd : ∃ (x : X), ∃ r > 0, O ⊆ ball x r) :
    ∃ s ⊆ balls X, O = ⋃₀ s ∧ s.PairwiseDisjoint id := by
  obtain ⟨xo, ro, ro_pos, o_sub_ball⟩ := O_bdd
  obtain ⟨U, o_eq_U_union⟩ := open_eq_union_ball hO

  have Ubdd : ∃ (x : X), ∃ r > 0, ⋃₀ U ⊆ ball x r := by
    refine ⟨xo, ro, ro_pos, ?_⟩
    rw [← o_eq_U_union]
    exact o_sub_ball

  let max_balls : Set (balls X) := {max_ball Ubdd u | u ∈ repr_set U}

  have max_balls_sub_balls : ↑max_balls ⊆ balls X := by simp
  have o_eq_union_max_balls : O = ⋃₀ max_balls := by
    rw [o_eq_U_union]
    simp only [sUnion_image]
    rw [partition_union U Ubdd]
    simp only [max_balls, mem_setOf_eq, iUnion_exists]
    sorry

  refine ⟨max_balls, max_balls_sub_balls, o_eq_union_max_balls, ?disjoint⟩

  sorry
