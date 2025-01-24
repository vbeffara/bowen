# Bowen

Formalisation du théorème d'existence et d'unicité des mesures de Gibbs pour des potentiels holderiens.
La preuve de ce théorème est dûe à R. Bowen.

## Accès

Blueprint : https://daurrian.github.io/bowen/blueprint/index.html

## TODO

Completer la structure du code lean pour pouvoir écrire la preuve du théorème sans les preuves des lemmes intermédiaires.

## FIX

La première définition a un problème de syntaxe à cause de la preuve de la linéarité qui est manquante.

```lean
    noncomputable def pullback_aux {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] (L : C(X, NNReal) → C(X, NNReal)) (μ : ProbabilityMeasure X) :
  CompactlySupportedContinuousMap X NNReal →ₗ[NNReal] NNReal :=
    fun f => ⟨∫ (x : X), (L f) x ∂μ, sorry⟩

noncomputable def pullback_measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [OpensMeasurableSpace X] [CompactSpace X] [BorelSpace X]
  (L : C(X, NNReal) → C(X, NNReal)) (μ : ProbabilityMeasure X) :
  Measure X :=
    (rieszContent (pullback_aux L μ)).measure

noncomputable def pullback {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [OpensMeasurableSpace X] [CompactSpace X] [BorelSpace X]
  (L : C(X, NNReal) → C(X, NNReal)) (μ : ProbabilityMeasure X) :
  ProbabilityMeasure X :=
    ⟨pullback_measure L μ, sorry ⟩
```
