import KTLean.SevenForcingDistinctPairs

/-!
# Rotation–Reversal Orbits of Distinct Ordered Pairs

## Formal status

**Level 2 — Consequence of global triadic closure.**

A distinct ordered pair generates an orbit under two operations:

1. rotation around its triad;
2. reversal of orientation.

Rotation has order three and reversal has order two. Their interaction
satisfies the dihedral relation

    reverse ∘ rotate = rotate² ∘ reverse.

This module defines the generated orbit and proves its basic closure
properties. The subsequent cardinality module will show that every such
orbit contains exactly six distinct ordered presentations of one
three-point block.

No minimality assumption and no cardinality-seven conclusion enters
this module.
-/

namespace SevenForcingPairOrbit

universe u

variable {Point : Type u}

open SevenForcingDistinctPairs

/--
Membership in the orbit generated from a selected distinct ordered pair
under rotation and reversal.
-/
inductive InPairOrbit
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    DistinctPair (Point := Point) →
      Prop

  | seed_mem :
      InPairOrbit S seed seed

  | rotate_mem
      {pair : DistinctPair (Point := Point)} :
      InPairOrbit S seed pair →
        InPairOrbit S seed (rotate S pair)

  | reverse_mem
      {pair : DistinctPair (Point := Point)} :
      InPairOrbit S seed pair →
        InPairOrbit S seed (reverse pair)

/--
The subtype of distinct ordered pairs reachable from a selected seed by
rotation and reversal.
-/
def PairOrbit
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :=
  {
    pair : DistinctPair (Point := Point) //
      InPairOrbit S seed pair
  }

/--
The seed belongs to its generated pair orbit.
-/
theorem seed_mem
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    InPairOrbit S seed seed := by

  exact InPairOrbit.seed_mem

/--
Pair-orbit membership is preserved by rotation.
-/
theorem rotate_mem
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed pair : DistinctPair (Point := Point))
    (hpair : InPairOrbit S seed pair) :
    InPairOrbit S seed (rotate S pair) := by

  exact InPairOrbit.rotate_mem hpair

/--
Pair-orbit membership is preserved by reversal.
-/
theorem reverse_mem
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed pair : DistinctPair (Point := Point))
    (hpair : InPairOrbit S seed pair) :
    InPairOrbit S seed (reverse pair) := by

  exact InPairOrbit.reverse_mem hpair

/--
Reversing after one rotation is the same as reversing first and then
rotating twice:

    reverse (rotate (x,y))
      =
    rotate² (reverse (x,y)).
-/
theorem reverse_rotate
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    reverse (rotate S pair) =
      rotate S (rotate S (reverse pair)) := by

  apply Subtype.ext

  rw [rotate_rotate_value S (reverse pair)]

  apply Prod.ext

  · change
      pair.third S =
        S.complete pair.right pair.left

    exact
      S.complete_comm
        pair.left
        pair.right

  · rfl

/--
Reversing after two rotations is the same as rotating once after
reversal:

    reverse (rotate² p)
      =
    rotate (reverse p).
-/
theorem reverse_rotate_rotate
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    reverse (rotate S (rotate S pair)) =
      rotate S (reverse pair) := by

  apply Subtype.ext
  apply Prod.ext

  · change
      S.complete pair.right (pair.third S) =
        pair.left

    exact complete_right_third S pair

  · change
      pair.third S =
        S.complete pair.right pair.left

    exact
      S.complete_comm
        pair.left
        pair.right

/--
Reversal conjugates rotation to its inverse.
-/
theorem reverse_rotate_reverse
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    reverse (rotate S (reverse pair)) =
      rotate S (rotate S pair) := by

  calc
    reverse (rotate S (reverse pair)) =
        rotate S (rotate S (reverse (reverse pair))) := by
      exact reverse_rotate S (reverse pair)

    _ = rotate S (rotate S pair) := by
      rw [reverse_involutive pair]

/--
One rotation of the seed belongs to its orbit.
-/
theorem rotate_seed_mem
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    InPairOrbit S seed (rotate S seed) := by

  exact
    InPairOrbit.rotate_mem
      InPairOrbit.seed_mem

/--
Two rotations of the seed belong to its orbit.
-/
theorem rotate_rotate_seed_mem
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    InPairOrbit S seed (rotate S (rotate S seed)) := by

  exact
    InPairOrbit.rotate_mem
      (
        InPairOrbit.rotate_mem
          InPairOrbit.seed_mem
      )

/--
The reversed seed belongs to its orbit.
-/
theorem reverse_seed_mem
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    InPairOrbit S seed (reverse seed) := by

  exact
    InPairOrbit.reverse_mem
      InPairOrbit.seed_mem

/--
The reversal of the first rotation belongs to the generated orbit.
-/
theorem reverse_rotate_seed_mem
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    InPairOrbit S seed (reverse (rotate S seed)) := by

  exact
    InPairOrbit.reverse_mem
      (
        InPairOrbit.rotate_mem
          InPairOrbit.seed_mem
      )

/--
The reversal of the second rotation belongs to the generated orbit.
-/
theorem reverse_rotate_rotate_seed_mem
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    InPairOrbit S seed
      (reverse (rotate S (rotate S seed))) := by

  exact
    InPairOrbit.reverse_mem
      (
        InPairOrbit.rotate_mem
          (
            InPairOrbit.rotate_mem
              InPairOrbit.seed_mem
          )
      )

end SevenForcingPairOrbit

#check SevenForcingPairOrbit.InPairOrbit
#check SevenForcingPairOrbit.PairOrbit
#check SevenForcingPairOrbit.seed_mem
#check SevenForcingPairOrbit.rotate_mem
#check SevenForcingPairOrbit.reverse_mem
#check SevenForcingPairOrbit.reverse_rotate
#check SevenForcingPairOrbit.reverse_rotate_rotate
#check SevenForcingPairOrbit.reverse_rotate_reverse
#check SevenForcingPairOrbit.rotate_seed_mem
#check SevenForcingPairOrbit.rotate_rotate_seed_mem
#check SevenForcingPairOrbit.reverse_seed_mem
