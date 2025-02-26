import Mathlib

open Metric Set Classical

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

lemma open_eq_disjoint_union_ball0 (O : Set X) (h : IsOpen O) :
    ∃ C : Set X, ∃ r : X → NNReal,
      O = ⋃ x ∈ C, ball x (r x) ∧ PairwiseDisjoint C (fun x => ball x (r x)) := by
    have open_eq_union_ball : ∃ r : X → NNReal, O = ⋃ x ∈ O, ball x (r x) := by
      rw [isOpen_iff] at h
      let r (x : X) (hx : x ∈ O) : NNReal := ⟨choose (h x hx), sorry⟩
      have ball_included (x : X) (hx : x ∈ O) : ball x (r x hx) ⊆ O := (choose_spec (h x hx)).right
      sorry
    sorry

 lemma open_eq_union_ball {X : Type*} [PseudoMetricSpace X] (O : Set X) (hO : IsOpen O) :
    ∃ r : X → ℝ, (∀ x ∈ O, r x > 0) ∧ O = ⋃ x ∈ O, ball x (r x) := by
  rw [isOpen_iff] at hO
  -- FIX : remplacer le let et les have par un obtain si possible ?
  let r (x : X) : ℝ := if hx : x ∈ O then choose (hO x hx) else 0
  use r
  have r_pos (x : X) (hx : x ∈ O) : r x > 0 := by
    simp [r, hx]
    exact (choose_spec (hO x hx)).left
  have r_sub (x : X) (hx : x ∈ O) : ball x (r x) ⊆ O := by
    simp [r, hx]
    exact (choose_spec (hO x hx)).right
  split_ands
  . intro x hx
    exact r_pos x hx
  . apply eq_of_subset_of_subset
    intro y hy
    simp only [Set.mem_iUnion, mem_ball, exists_prop]
    . use y
      exact ⟨hy, by simp_all⟩
    . simp only [iUnion_subset_iff]
      intro i hi
      exact r_sub i hi

def rel (r : X → ℝ) (x y : X) : Prop :=
  ball x (r x) ∩ ball y (r y) ≠ ∅

lemma sub (O : Set X) (r : X → ℝ) (x y : O)
  (h_equiv : rel r x y) :
    ball x (r x) ⊆ ball y (r y) ∨ ball y (r y) ⊆ ball x (r x) := by
  rcases IsUltrametricDist.ball_subset_trichotomy x y (r x) (r y) with x_sub_y | y_sub_x | dis
  . left; exact x_sub_y
  . right; exact y_sub_x
  . rw [Set.disjoint_iff_inter_eq_empty] at dis
    simp [rel] at h_equiv
    sorry
    -- exact h_equiv dis -- FIX : Fonctionne pas a cause d'une coercion

instance (O : Set X) (r : X → ℝ) (hr : ∀ x ∈ O, r x > 0) : IsEquiv O (rel (fun x => r x)) where
  refl x := by simp_all [rel]
  symm x y := by intro hxy; simp_all only [rel]; rwa [Set.inter_comm]
  trans x y z := by
    intros hxy hyz
    simp_all only [rel]
    have incl (x y : O) (h_equiv : rel r x y) :
        ball x (r x) ⊆ ball y (r y) ∨ ball y (r y) ⊆ ball x (r x) := by exact sub O r x y h_equiv
    sorry


lemma open_eq_disjoint_union_ball (O : Set X) (hO : IsOpen O) :
  ∃ C : Set X, ∃ r : X → ℝ,
    (∀ x ∈ O, r x > 0) ∧
    O = ⋃ x ∈ C, ball x (r x) ∧
    PairwiseDisjoint C (fun x => ball x (r x)) := by
  rw [exists_swap]
  let r := choose (open_eq_union_ball O hO)
  have r_pos (x : X) (hx : x ∈ O) : r x > 0 := (choose_spec (open_eq_union_ball O hO)).left x hx
  have r_iUnion : O = ⋃ x ∈ O, ball x (r x) := (choose_spec (open_eq_union_ball O hO)).right
  use r
  simp only [exists_and_left]
  constructor
  . exact r_pos
  . sorry
