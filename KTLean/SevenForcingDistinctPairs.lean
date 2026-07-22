import KTLean.SevenForcingOddCardinality

/-!
# Distinct Ordered Pairs in Global Triadic Closure

## Formal status

**Level 2 — Consequence of global triadic closure.**

A distinct ordered pair `(x,y)` determines the third point

    complete x y.

Rotating around the resulting triad sends

    (x,y) ↦ (y, complete x y).

This rotation has order three. Reversing an ordered pair has order two.

These operations will later generate the six ordered presentations of
one three-point block and provide the factor of six in the global pair
count.

No minimality assumption and no cardinality-seven conclusion enters
this module.
-/

namespace SevenForcingDistinctPairs

universe u

variable {Point : Type u}

/--
An ordered pair of distinct points.
-/
abbrev DistinctPair :=
  { pair : Point × Point // pair.1 ≠ pair.2 }

/--
The first point of a distinct ordered pair.
-/
def DistinctPair.left
    (pair : DistinctPair (Point := Point)) :
    Point :=
  pair.1.1

/--
The second point of a distinct ordered pair.
-/
def DistinctPair.right
    (pair : DistinctPair (Point := Point)) :
    Point :=
  pair.1.2

/--
The third point completing a distinct ordered pair.
-/
def DistinctPair.third
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    Point :=
  S.complete pair.left pair.right

/--
Rotate an ordered pair once around its generated triad:

    (x,y) ↦ (y, complete x y).
-/
def rotate
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    DistinctPair (Point := Point) :=

  ⟨
    (
      pair.right,
      pair.third S
    ),
    by
      exact
        Ne.symm
          (
            S.complete_ne_right
              pair.2
          )
  ⟩

/--
Reverse an ordered pair.
-/
def reverse
    (pair : DistinctPair (Point := Point)) :
    DistinctPair (Point := Point) :=

  ⟨
    (
      pair.right,
      pair.left
    ),
    Ne.symm pair.2
  ⟩

/--
Reversal is involutive.
-/
theorem reverse_involutive :
    Function.Involutive
      (reverse :
        DistinctPair (Point := Point) →
          DistinctPair (Point := Point)) := by

  intro pair

  apply Subtype.ext

  cases pair with
  | mk value hvalue =>
      cases value
      rfl

/--
One rotation has the expected coordinates.
-/
@[simp]
theorem rotate_value
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    (rotate S pair).1 =
      (
        pair.right,
        pair.third S
      ) := by
  rfl

/--
The completion of the second and third points recovers the first.
-/
theorem complete_right_third
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    S.complete pair.right (pair.third S) =
      pair.left := by

  exact
    (
      S.block_recovery
        pair.left
        pair.right
    ).2

/--
The completion of the third and first points recovers the second.
-/
theorem complete_third_left
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    S.complete (pair.third S) pair.left =
      pair.right := by

  calc
    S.complete (pair.third S) pair.left =
        S.complete pair.left (pair.third S) := by
      exact S.complete_comm _ _

    _ = pair.right := by
      exact
        S.complete_left
          pair.left
          pair.right

/--
Two rotations send `(x,y)` to `(complete x y,x)`.
-/
theorem rotate_rotate_value
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    (rotate S (rotate S pair)).1 =
      (
        pair.third S,
        pair.left
      ) := by

  apply Prod.ext

  · rfl

  · exact complete_right_third S pair

/--
Three rotations return the original ordered pair.
-/
theorem rotate_three
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    rotate S (rotate S (rotate S pair)) =
      pair := by

  apply Subtype.ext

  rw [rotate_rotate_value S (rotate S pair)]

  apply Prod.ext

  · change
      S.complete pair.right (pair.third S) =
        pair.left

    exact complete_right_third S pair

  · rfl



/--
Rotation is a permutation of the distinct ordered-pair carrier.
-/
def rotateEquiv
    (S : SevenForcing.GlobalTriadicClosure Point) :
    DistinctPair (Point := Point) ≃
      DistinctPair (Point := Point) where

  toFun :=
    rotate S

  invFun :=
    rotate S ∘ rotate S

  left_inv := by
    intro pair

    change
      rotate S
          (rotate S
            (rotate S pair)) =
        pair

    exact rotate_three S pair

  right_inv := by
    intro pair

    change
      rotate S
          (rotate S
            (rotate S pair)) =
        pair

    exact rotate_three S pair

/--
Reversal as a permutation.
-/
def reverseEquiv :
    DistinctPair (Point := Point) ≃
      DistinctPair (Point := Point) where

  toFun :=
    reverse

  invFun :=
    reverse

  left_inv :=
    reverse_involutive

  right_inv :=
    reverse_involutive

end SevenForcingDistinctPairs

#check SevenForcingDistinctPairs.DistinctPair
#check SevenForcingDistinctPairs.DistinctPair.left
#check SevenForcingDistinctPairs.DistinctPair.right
#check SevenForcingDistinctPairs.DistinctPair.third
#check SevenForcingDistinctPairs.rotate
#check SevenForcingDistinctPairs.reverse
#check SevenForcingDistinctPairs.reverse_involutive
#check SevenForcingDistinctPairs.rotate_rotate_value
#check SevenForcingDistinctPairs.rotate_three
#check SevenForcingDistinctPairs.rotateEquiv
#check SevenForcingDistinctPairs.reverseEquiv
