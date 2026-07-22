import KTLean.SevenForcingPairOrbitNormalForm

/-!
# Coordinates of the Six Pair-Orbit Normal Forms

## Formal status

**Level 2 — Consequence of global triadic closure.**

For a distinct ordered seed `(x,y)`, let

    z = complete x y.

The six rotation–reversal normal forms have coordinates

    (x,y), (y,z), (z,x),
    (y,x), (x,z), (z,y).

The three supporting points `x`, `y`, and `z` are pairwise distinct.

This module exposes those coordinates explicitly. The subsequent
distinctness module will use them to prove that the six normal forms are
pairwise distinct.
-/

namespace SevenForcingPairOrbitCoordinates

universe u

variable {Point : Type u}

open SevenForcingDistinctPairs

/--
The third point differs from the right endpoint of a distinct seed.
-/
theorem third_ne_right
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    seed.third S ≠ seed.right := by

  exact S.complete_ne_right seed.2

/--
The third point differs from the left endpoint of a distinct seed.
-/
theorem third_ne_left
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    seed.third S ≠ seed.left := by

  intro hthird

  apply
    S.complete_ne_right
      (Ne.symm seed.2)

  calc
    S.complete seed.right seed.left =
        seed.third S := by
      exact
        S.complete_comm
          seed.right
          seed.left

    _ = seed.left := hthird

/--
The seed has coordinates `(x,y)`.
-/
@[simp]
theorem seed_value
    (seed : DistinctPair (Point := Point)) :
    seed.1 =
      (
        seed.left,
        seed.right
      ) := by

  rfl

/--
The reversed seed has coordinates `(y,x)`.
-/
@[simp]
theorem reverse_seed_value
    (seed : DistinctPair (Point := Point)) :
    (reverse seed).1 =
      (
        seed.right,
        seed.left
      ) := by

  rfl

/--
The first rotation has coordinates `(y,z)`.
-/
@[simp]
theorem rotate_seed_value
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    (rotate S seed).1 =
      (
        seed.right,
        seed.third S
      ) := by

  rfl

/--
The second rotation has coordinates `(z,x)`.
-/
@[simp]
theorem rotate_rotate_seed_value
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    (rotate S (rotate S seed)).1 =
      (
        seed.third S,
        seed.left
      ) := by

  exact
    rotate_rotate_value
      S
      seed

/--
Rotating the reversed seed once gives coordinates `(x,z)`.
-/
@[simp]
theorem rotate_reverse_seed_value
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    (rotate S (reverse seed)).1 =
      (
        seed.left,
        seed.third S
      ) := by

  apply Prod.ext

  · rfl

  · change
      S.complete seed.right seed.left =
        seed.third S

    exact
      S.complete_comm
        seed.right
        seed.left

/--
Rotating the reversed seed twice gives coordinates `(z,y)`.
-/
@[simp]
theorem rotate_rotate_reverse_seed_value
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    (rotate S (rotate S (reverse seed))).1 =
      (
        seed.third S,
        seed.right
      ) := by

  rw [
    rotate_rotate_value
      S
      (reverse seed)
  ]

  apply Prod.ext

  · change
      S.complete seed.right seed.left =
        seed.third S

    exact
      S.complete_comm
        seed.right
        seed.left

  · rfl

end SevenForcingPairOrbitCoordinates

#check SevenForcingPairOrbitCoordinates.third_ne_right
#check SevenForcingPairOrbitCoordinates.third_ne_left
#check SevenForcingPairOrbitCoordinates.seed_value
#check SevenForcingPairOrbitCoordinates.reverse_seed_value
#check SevenForcingPairOrbitCoordinates.rotate_seed_value
#check SevenForcingPairOrbitCoordinates.rotate_rotate_seed_value
#check SevenForcingPairOrbitCoordinates.rotate_reverse_seed_value
#check SevenForcingPairOrbitCoordinates.rotate_rotate_reverse_seed_value
