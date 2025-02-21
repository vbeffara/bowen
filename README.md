# Bowen

Formalisation du théorème d'existence et d'unicité des mesures de Gibbs pour des potentiels holderiens.
La preuve de ce théorème est dûe à R. Bowen.

## Accès

Blueprint : https://daurrian.github.io/bowen/blueprint/index.html

## TODO

Completer la structure du code lean pour pouvoir écrire la preuve du théorème sans les preuves des lemmes intermédiaires.

Ajouter la preuve du fait que dans un espace ultramétrique, tout ouvert est une union disjointe de boules.
De plus, si l'espace est séparable alors l'union est dénombrable.

## Problemes

- Comment prouver `example (r : ENNReal) (hr : r - 1 = 0) : r = 1 := by sorry` ?

- RPF1 : Schauder-Tychonoff nécessite d'avoir un espace vectoriel mais un ensemble de mesures n'est
pas un espace vectoriel.

- `ergodic_shift_inv_imp_cst` : Vérifier l'énoncé (peut-être faux)
