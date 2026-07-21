import KTLean.SevenForcingCounting

/-!
# Pairing Outside a Distinguished Point

## Formal status

**Level 2 — Consequence of global triadic closure.**

Fix a point `x`. Left completion

    y ↦ complete x y

fixes `x` and pairs every other point with a distinct partner. This
module restricts the operation to the complement of `x` and proves that
the resulting permutation is an involution with no fixed points.

The later counting module will convert this pairing into the parity
statement that the number of points outside `x` is even.
-/

namespace SevenForcingPairing

universe u

variable {Point : Type u}

/--
The carrier consisting of all points other than `x`.
-/
abbrev PointComplement
    (x : Point) :=
  { y : Point // y ≠ x }

/--
Left completion by `x` preserves the complement of `x`.
-/
def complementCompletion
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (y : PointComplement x) :
    PointComplement x :=

  ⟨
    S.complete x y.1,
    by
      exact
        S.complete_ne_left
          (Ne.symm y.2)
  ⟩

/--
Completion on the complement is involutive.
-/
theorem complementCompletion_involutive
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Function.Involutive
      (complementCompletion S x) := by

  intro y

  apply Subtype.ext

  exact S.complete_left x y.1

/--
The complement pairing as a permutation.
-/
def complementCompletionEquiv
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    PointComplement x ≃ PointComplement x where

  toFun :=
    complementCompletion S x

  invFun :=
    complementCompletion S x

  left_inv :=
    complementCompletion_involutive S x

  right_inv :=
    complementCompletion_involutive S x

/--
No point outside `x` is fixed by completion with `x`.
-/
theorem complementCompletion_ne_self
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (y : PointComplement x) :
    complementCompletion S x y ≠ y := by

  intro hfixed

  have hvalue :
      S.complete x y.1 = y.1 := by
    exact congrArg Subtype.val hfixed

  have hnot :
      S.complete x y.1 ≠ y.1 :=
    S.complete_ne_right
      (Ne.symm y.2)

  exact hnot hvalue

/--
The complement permutation has no fixed points.
-/
theorem complementCompletionEquiv_fixedPointFree
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    ∀ y : PointComplement x,
      complementCompletionEquiv S x y ≠ y := by

  intro y
  exact complementCompletion_ne_self S x y

end SevenForcingPairing

#check SevenForcingPairing.PointComplement
#check SevenForcingPairing.complementCompletion
#check SevenForcingPairing.complementCompletion_involutive
#check SevenForcingPairing.complementCompletionEquiv
#check SevenForcingPairing.complementCompletionEquiv_fixedPointFree
