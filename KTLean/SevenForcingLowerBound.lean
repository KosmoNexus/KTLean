import KTLean.SevenForcingCongruence

/-!
# Seven-Point Lower Bound for Nondegenerate Global Triadic Closure

## Formal status

**Level 2 — Consequence of global triadic closure and nondegeneracy.**

Nondegeneracy already implies that the finite point carrier has more
than three elements.

The global pair-orbit argument further proves that the point
cardinality is congruent to `1` or `3` modulo six.

The only natural numbers greater than three and smaller than seven are

    4, 5, 6,

and none is congruent to `1` or `3` modulo six. Therefore every finite
nondegenerate global triadic-closure system has at least seven points.

This module proves only the lower bound

    7 ≤ card Point.

It does not assume minimality and does not yet conclude equality with
seven.
-/

namespace SevenForcingLowerBound

noncomputable section

universe u

variable {Point : Type u}

open SevenForcingCongruence

/--
A finite nondegenerate global triadic-closure carrier has at least
seven points.
-/
theorem seven_le_card
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (hNondegenerate : SevenForcing.Nondegenerate S)
    (x : Point) :
    7 ≤ Fintype.card Point := by

  have hthree :
      3 < Fintype.card Point :=
    SevenForcing.three_lt_card
      hNondegenerate

  rcases
    card_mod_six_eq_one_or_three
      S
      x
    with hone | hthreeMod

  · omega

  · omega

/--
Equivalent formulation: a nondegenerate carrier cannot have fewer than
seven points.
-/
theorem not_card_lt_seven
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (hNondegenerate : SevenForcing.Nondegenerate S)
    (x : Point) :
    ¬ Fintype.card Point < 7 := by

  exact
    Nat.not_lt_of_ge
      (
        seven_le_card
          S
          hNondegenerate
          x
      )

end

end SevenForcingLowerBound

#check SevenForcingLowerBound.seven_le_card
#check SevenForcingLowerBound.not_card_lt_seven
