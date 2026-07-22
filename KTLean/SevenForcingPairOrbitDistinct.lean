import KTLean.SevenForcingPairOrbitCoordinates

/-!
# Distinctness of the Six Pair-Orbit Normal Forms

## Formal status

**Level 2 — Consequence of global triadic closure.**

For a distinct ordered seed `(x,y)`, write

    z = complete x y.

The six canonical pair-orbit presentations are

    (x,y), (y,z), (z,x),
    (y,x), (x,z), (z,y).

Because `x`, `y`, and `z` are pairwise distinct, these six ordered
pairs are pairwise distinct.

This module packages the six presentations into a finite position type
and proves that the corresponding map into the distinct-pair carrier is
injective.
-/

namespace SevenForcingPairOrbitDistinct

universe u

variable {Point : Type u}

open SevenForcingDistinctPairs
open SevenForcingPairOrbitCoordinates

/--
The six canonical positions in a rotation–reversal orbit.
-/
inductive PairPosition where

  | base
  | rotateOnce
  | rotateTwice
  | reverseBase
  | reverseRotateOnce
  | reverseRotateTwice

  deriving DecidableEq

/--
The distinct ordered pair represented by a canonical orbit position.
-/
def pairAt
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    PairPosition →
      DistinctPair (Point := Point)

  | PairPosition.base =>
      seed

  | PairPosition.rotateOnce =>
      rotate S seed

  | PairPosition.rotateTwice =>
      rotate S (rotate S seed)

  | PairPosition.reverseBase =>
      reverse seed

  | PairPosition.reverseRotateOnce =>
      rotate S (reverse seed)

  | PairPosition.reverseRotateTwice =>
      rotate S (rotate S (reverse seed))

/--
The base position represents the seed.
-/
@[simp]
theorem pairAt_base
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    pairAt S seed PairPosition.base =
      seed := by

  rfl

/--
The first rotation position represents one rotation of the seed.
-/
@[simp]
theorem pairAt_rotateOnce
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    pairAt S seed PairPosition.rotateOnce =
      rotate S seed := by

  rfl

/--
The second rotation position represents two rotations of the seed.
-/
@[simp]
theorem pairAt_rotateTwice
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    pairAt S seed PairPosition.rotateTwice =
      rotate S (rotate S seed) := by

  rfl

/--
The reversed-base position represents the reversed seed.
-/
@[simp]
theorem pairAt_reverseBase
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    pairAt S seed PairPosition.reverseBase =
      reverse seed := by

  rfl

/--
The first reversed rotation position represents one rotation of the
reversed seed.
-/
@[simp]
theorem pairAt_reverseRotateOnce
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    pairAt S seed PairPosition.reverseRotateOnce =
      rotate S (reverse seed) := by

  rfl

/--
The second reversed rotation position represents two rotations of the
reversed seed.
-/
@[simp]
theorem pairAt_reverseRotateTwice
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    pairAt S seed PairPosition.reverseRotateTwice =
      rotate S (rotate S (reverse seed)) := by

  rfl

/--
The explicit ordered-pair coordinates represented by each canonical
position.
-/
def pairCoordinates
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    PairPosition →
      Point × Point

  | PairPosition.base =>
      (seed.left, seed.right)

  | PairPosition.rotateOnce =>
      (seed.right, seed.third S)

  | PairPosition.rotateTwice =>
      (seed.third S, seed.left)

  | PairPosition.reverseBase =>
      (seed.right, seed.left)

  | PairPosition.reverseRotateOnce =>
      (seed.left, seed.third S)

  | PairPosition.reverseRotateTwice =>
      (seed.third S, seed.right)

/--
The underlying value of `pairAt` has the corresponding explicit
coordinates.
-/
theorem pairAt_value
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point))
    (position : PairPosition) :
    (pairAt S seed position).1 =
      pairCoordinates S seed position := by

  cases position with

  | base =>
      exact seed_value seed

  | rotateOnce =>
      exact rotate_seed_value S seed

  | rotateTwice =>
      exact rotate_rotate_seed_value S seed

  | reverseBase =>
      exact reverse_seed_value seed

  | reverseRotateOnce =>
      exact rotate_reverse_seed_value S seed

  | reverseRotateTwice =>
      exact rotate_rotate_reverse_seed_value S seed

/--
The six canonical pair presentations are pairwise distinct.
-/
theorem pairAt_injective
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    Function.Injective
      (pairAt S seed) := by

  intro first second hpairs

  have hxy :
      seed.left ≠ seed.right :=
    seed.2

  have hyx :
      seed.right ≠ seed.left :=
    Ne.symm hxy

  have hzx :
      seed.third S ≠ seed.left :=
    third_ne_left S seed

  have hxz :
      seed.left ≠ seed.third S :=
    Ne.symm hzx

  have hzy :
      seed.third S ≠ seed.right :=
    third_ne_right S seed

  have hyz :
      seed.right ≠ seed.third S :=
    Ne.symm hzy

  have hcoordinates :
      pairCoordinates S seed first =
        pairCoordinates S seed second := by

    calc
      pairCoordinates S seed first =
          (pairAt S seed first).1 := by
        exact (pairAt_value S seed first).symm

      _ = (pairAt S seed second).1 := by
        exact congrArg Subtype.val hpairs

      _ = pairCoordinates S seed second := by
        exact pairAt_value S seed second

  cases first <;> cases second <;>
    simp [
      pairCoordinates,
      hxy,
      hyx,
      hzx,
      hxz,
      hzy,
      hyz
    ] at hcoordinates ⊢
/--
Different canonical positions determine different ordered pairs.
-/
theorem pairAt_ne
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point))
    {first second : PairPosition}
    (hpositions : first ≠ second) :
    pairAt S seed first ≠
      pairAt S seed second := by

  intro hpairs

  apply hpositions

  exact
    pairAt_injective
      S
      seed
      hpairs

end SevenForcingPairOrbitDistinct

#check SevenForcingPairOrbitDistinct.PairPosition
#check SevenForcingPairOrbitDistinct.pairAt
#check SevenForcingPairOrbitDistinct.pairAt_injective
#check SevenForcingPairOrbitDistinct.pairAt_ne
