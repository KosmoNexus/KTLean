import KTLean.SevenForcingPairOrbit

/-!
# Normal Forms for Rotation–Reversal Pair Orbits

## Formal status

**Level 2 — Consequence of global triadic closure.**

Every distinct ordered pair reachable from a seed by repeated rotation
and reversal has one of six canonical forms:

1. `seed`;
2. `rotate seed`;
3. `rotate² seed`;
4. `reverse seed`;
5. `rotate (reverse seed)`;
6. `rotate² (reverse seed)`.

This module proves exhaustiveness of those six forms. The subsequent
cardinality module will prove that the six forms are pairwise distinct.
-/

namespace SevenForcingPairOrbitNormalForm

universe u

variable {Point : Type u}

open SevenForcingDistinctPairs
open SevenForcingPairOrbit

/--
The six canonical presentations associated with a distinct ordered-pair
seed.
-/
inductive PairNormalForm
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    DistinctPair (Point := Point) →
      Prop

  | base :
      PairNormalForm S seed seed

  | rotateOnce :
      PairNormalForm S seed
        (rotate S seed)

  | rotateTwice :
      PairNormalForm S seed
        (rotate S (rotate S seed))

  | reverseBase :
      PairNormalForm S seed
        (reverse seed)

  | reverseRotateOnce :
      PairNormalForm S seed
        (rotate S (reverse seed))

  | reverseRotateTwice :
      PairNormalForm S seed
        (rotate S (rotate S (reverse seed)))

/--
The six normal forms are closed under rotation.
-/
theorem pairNormalForm_rotate
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed pair : DistinctPair (Point := Point))
    (hpair : PairNormalForm S seed pair) :
    PairNormalForm S seed (rotate S pair) := by

  cases hpair with

  | base =>
      exact PairNormalForm.rotateOnce

  | rotateOnce =>
      exact PairNormalForm.rotateTwice

  | rotateTwice =>
      rw [rotate_three S seed]
      exact PairNormalForm.base

  | reverseBase =>
      exact PairNormalForm.reverseRotateOnce

  | reverseRotateOnce =>
      exact PairNormalForm.reverseRotateTwice

  | reverseRotateTwice =>
      rw [rotate_three S (reverse seed)]
      exact PairNormalForm.reverseBase

/--
The six normal forms are closed under reversal.
-/
theorem pairNormalForm_reverse
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed pair : DistinctPair (Point := Point))
    (hpair : PairNormalForm S seed pair) :
    PairNormalForm S seed (reverse pair) := by

  cases hpair with

  | base =>
      exact PairNormalForm.reverseBase

  | rotateOnce =>
      rw [SevenForcingPairOrbit.reverse_rotate S seed]
      exact PairNormalForm.reverseRotateTwice

  | rotateTwice =>
      rw [SevenForcingPairOrbit.reverse_rotate_rotate S seed]
      exact PairNormalForm.reverseRotateOnce

  | reverseBase =>
      rw [reverse_involutive seed]
      exact PairNormalForm.base

  | reverseRotateOnce =>
      rw [SevenForcingPairOrbit.reverse_rotate_reverse S seed]
      exact PairNormalForm.rotateTwice

  | reverseRotateTwice =>
      rw [
        SevenForcingPairOrbit.reverse_rotate_rotate
          S
          (reverse seed)
      ]
      rw [reverse_involutive seed]
      exact PairNormalForm.rotateOnce

/--
Every pair in the rotation–reversal orbit of a seed has one of the six
canonical normal forms.
-/
theorem inPairOrbit_has_normalForm
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed pair : DistinctPair (Point := Point))
    (hpair : InPairOrbit S seed pair) :
    PairNormalForm S seed pair := by

  induction hpair with

  | seed_mem =>
      exact PairNormalForm.base

  | rotate_mem hmem inductionHypothesis =>
      exact
        pairNormalForm_rotate
          S
          seed
          _
          inductionHypothesis

  | reverse_mem hmem inductionHypothesis =>
      exact
        pairNormalForm_reverse
          S
          seed
          _
          inductionHypothesis

/--
Every element of the orbit subtype has a six-form normal
representation.
-/
theorem pairOrbit_element_has_normalForm
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point))
    (pair : PairOrbit S seed) :
    PairNormalForm S seed pair.1 := by

  exact
    inPairOrbit_has_normalForm
      S
      seed
      pair.1
      pair.2

end SevenForcingPairOrbitNormalForm

#check SevenForcingPairOrbitNormalForm.PairNormalForm
#check SevenForcingPairOrbitNormalForm.pairNormalForm_rotate
#check SevenForcingPairOrbitNormalForm.pairNormalForm_reverse
#check SevenForcingPairOrbitNormalForm.inPairOrbit_has_normalForm
#check SevenForcingPairOrbitNormalForm.pairOrbit_element_has_normalForm
