import KTLean.SevenForcing

/-!
# Counting Constraints for Global Triadic Closure

## Formal status

**Level 2 — Consequences of the frozen closure interface.**

For a fixed point `x`, the map

    y ↦ complete x y

is an involution of the entire finite carrier. Its unique fixed point is
`x`; every other point therefore belongs to a two-cycle.

This is the local combinatorial mechanism behind the parity equation

    |Point| = 2r + 1.

The cardinality equation itself is proved in later stages.
-/

namespace SevenForcingCounting

universe u

variable {Point : Type u}

/--
Left completion by a fixed point is involutive.
-/
theorem leftCompletion_involutive
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Function.Involutive (fun y => S.complete x y) := by

  intro y
  exact S.complete_left x y

/--
Left completion by `x` as a permutation of the complete carrier.
-/
def leftCompletionEquiv
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Point ≃ Point where

  toFun :=
    fun y => S.complete x y

  invFun :=
    fun y => S.complete x y

  left_inv :=
    S.complete_left x

  right_inv :=
    S.complete_left x

/--
The distinguished point `x` is fixed by left completion.
-/
@[simp]
theorem leftCompletionEquiv_self
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    leftCompletionEquiv S x x = x := by

  exact S.complete_self x

/--
A point is fixed by left completion with `x` exactly when it is `x`.

Thus `x` is the unique fixed point of the involution.
-/
theorem leftCompletion_fixed_iff
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x y : Point) :
    leftCompletionEquiv S x y = y ↔
      y = x := by

  constructor

  · intro hfixed

    by_contra hyx

    have hne :
        S.complete x y ≠ y :=
      S.complete_ne_right (Ne.symm hyx)


    exact hne hfixed

  · intro hyx
    subst y
    exact leftCompletionEquiv_self S x

/--
Left completion has exactly one fixed point.
-/
theorem existsUnique_leftCompletion_fixed
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    ∃! y : Point,
      leftCompletionEquiv S x y = y := by

  refine ⟨x, leftCompletionEquiv_self S x, ?_⟩

  intro y hy
  exact
    (leftCompletion_fixed_iff S x y).1 hy

end SevenForcingCounting

#check SevenForcingCounting.leftCompletion_involutive
#check SevenForcingCounting.leftCompletionEquiv
#check SevenForcingCounting.leftCompletion_fixed_iff
#check SevenForcingCounting.existsUnique_leftCompletion_fixed
