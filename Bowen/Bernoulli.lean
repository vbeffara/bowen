import Mathlib

open Real MeasureTheory Set

class ContainN (X : Type*) extends Encodable X where
  fromNat : ℕ → X
  shift : X → X
  var_supp : ℕ -> Set X

variable {X : Type*} [ContainN X]

abbrev Bernoulli (X : Type*) [ContainN X] (n : ℕ) := X → Fin n

namespace Bernoulli

  variable {n : ℕ} (x y z : Bernoulli X n) {φ : Bernoulli X n → ℝ} {a : Fin n}

  instance (X : Type*) [DecidableEq X] : MetricSpace X where
    dist x y := if x = y then 0 else 1
    dist_self x := by simp
    dist_comm x y := by simp [dist]; congr 1; simp [eq_comm]
    dist_triangle x y z := by
      simp_all [dist]
      by_cases h1 : x = z <;> simp_all [h1]
      . by_cases h2 : y = z <;> simp_all [h2, eq_comm]
      . by_cases h2 : x = y <;> simp_all [h2]
        by_cases h3 : y = z <;> simp_all [h3]
    eq_of_dist_eq_zero := by
      intro x y h
      simp [dist] at h
      exact h

  noncomputable instance : MetricSpace (Bernoulli X n) := PiCountable.metricSpace

  -- instance bernoulli_is_compact : CompactSpace (Bernoulli X n) := Pi.compactSpace

  def cylinder (x : Bernoulli X n) (m : ℕ) : Set (Bernoulli X n) :=
    {y | EqOn x y (ContainN.fromNat '' Ico 0 m)}
    -- {y | EqOn x y {ContainN.fromNat i | i ∈ Ico 0 m}}
    -- c'est pas à ça que servirait `var_supp` ?

  def shift (x : Bernoulli X n) : Bernoulli X n := x ∘ ContainN.shift

  -- instance : TopologicalSpace.SeparableSpace (Bernoulli X n) :=
  --   TopologicalSpace.instSeparableSpaceForallOfCountable

  instance : ContainN ℤ where
    fromNat n := ↑n
    shift n := n + 1
    var_supp n := Icc (-n) n

  -- Valide sur Z, peut-être ailleurs également
  lemma open_iff_disjoint_union_ball (O : Set (Bernoulli ℤ n)) :
    IsOpen O ↔ ∃ b : ℕ → Bernoulli ℤ n, ∃ r : ℕ → NNReal,
      O = ⋃ i : ℕ, (Metric.ball (b i) (r i) : Set (Bernoulli ℤ n)) ∧
      Pairwise (Function.onFun Disjoint (λ i => Metric.ball (b i) (r i))):=
    sorry
    -- https://math.stackexchange.com/a/194200/135190
    -- `IsUltrametricDist` et

end Bernoulli

class HolderLike {X : Type*} [ContainN X] (φ : Bernoulli X n → ℝ) where
  α : {x : ℝ // x ∈ Ioo 0 1}
  b : NNReal
  var : ℕ → NNReal := λ k => sSup {diff | ∀ x y, EqOn x y (ContainN.var_supp k) ∧ diff = |φ x - φ y|}
  isHolderLike : ∀ k : ℕ, var k ≤ b * (α : ℝ)^k
  norm : NNReal := sSup {|φ x| | x : Bernoulli X n}
  -- faut vraiment m'expliquer pourquoi ce n'est pas `HolderWith`

-- Le `:=` ne veut pas dire ce qu'on pense c'est une valeur par défaut
class Toto where
  x : ℕ := 1
instance toto1 : Toto where
instance toto2 : Toto where x := 2
#eval toto1.x -- 1
#eval toto2.x -- 2

noncomputable example (φ : Bernoulli X n → ℝ) : HolderLike φ where
  α := ⟨1/2, by { simp ; norm_num }⟩
  b := 0
  var _ := 0
  norm := 0
  isHolderLike k := by simp

lemma holder_imp_continuous (φ : Bernoulli X n → ℝ) [HolderLike φ] : Continuous φ := sorry
