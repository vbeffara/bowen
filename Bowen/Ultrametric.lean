import Mathlib

open Metric Set Classical

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

lemma open_eq_disjoint_union_ball (O : Set X) (h : IsOpen O) :
    ∃ C : Set X, ∃ r : X → NNReal,
      O = ⋃ x ∈ C, ball x (r x) ∧ PairwiseDisjoint C (fun x => ball x (r x)) := by
    have open_eq_union_ball : ∃ r : X → NNReal, O = ⋃ x ∈ O, ball x (r x) := by
      rw [isOpen_iff] at h
      let r (x : X) (hx : x ∈ O) : NNReal := ⟨choose (h x hx), sorry⟩
      have ball_included (x : X) (hx : x ∈ O) : ball x (r x hx) ⊆ O := (choose_spec (h x hx)).right

