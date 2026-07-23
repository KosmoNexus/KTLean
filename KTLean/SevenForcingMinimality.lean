import KTLean.SevenForcingLowerBound

/-!
# Cardinal Minimality for Nondegenerate Global Triadic Closure

## Formal status

**Level 3 — Consequence of global triadic closure, nondegeneracy, and
an explicit cardinal-minimality hypothesis.**

The preceding modules prove that every finite nondegenerate global
triadic-closure system has at least seven points.

This module formalizes the additional statement that a selected system
has no larger cardinality than any other finite nondegenerate system.
If a seven-point nondegenerate witness exists, cardinal minimality and
the previously proved lower bound together force exact cardinality
seven.

The existence and structural identification of the seven-point witness
are not assumed silently. They remain explicit inputs here and will be
constructed in subsequent Fano modules.
-/

namespace SevenForcingMinimality

noncomputable section

universe u

variable {Point : Type u}

open SevenForcingLowerBound

/--
A finite global triadic-closure system is cardinal-minimal among all
finite nondegenerate global triadic-closure systems in the same
universe.
-/
def CardinalityMinimalNondegenerate
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point) :
    Prop :=
  SevenForcing.Nondegenerate S ∧
    ∀ {Other : Type u}
      [Fintype Other]
      [DecidableEq Other],
      (T : SevenForcing.GlobalTriadicClosure Other) →
      SevenForcing.Nondegenerate T →
      Fintype.card Point ≤
        Fintype.card Other

/--
A cardinal-minimal nondegenerate system still satisfies the universal
seven-point lower bound.
-/
theorem seven_le_card_of_minimal
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (hMinimal : CardinalityMinimalNondegenerate S)
    (x : Point) :
    7 ≤ Fintype.card Point := by

  exact
    seven_le_card
      S
      hMinimal.1
      x

/--
A cardinal-minimal nondegenerate system has exactly seven points once
a finite seven-point nondegenerate witness is supplied.
-/
theorem card_eq_seven_of_minimal_and_witness
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (hMinimal : CardinalityMinimalNondegenerate S)
    (x : Point)
    {SevenPoint : Type u}
    [Fintype SevenPoint]
    [DecidableEq SevenPoint]
    (T : SevenForcing.GlobalTriadicClosure SevenPoint)
    (hTNondegenerate : SevenForcing.Nondegenerate T)
    (hSevenCard :
      Fintype.card SevenPoint = 7) :
    Fintype.card Point = 7 := by

  have hlower :
      7 ≤ Fintype.card Point :=
    seven_le_card_of_minimal
      S
      hMinimal
      x

  have hupperWitness :
      Fintype.card Point ≤
        Fintype.card SevenPoint :=
    hMinimal.2
      T
      hTNondegenerate

  have hupper :
      Fintype.card Point ≤ 7 := by
    rw [hSevenCard] at hupperWitness
    exact hupperWitness

  exact
    Nat.le_antisymm
      hupper
      hlower

end

end SevenForcingMinimality

#check SevenForcingMinimality.CardinalityMinimalNondegenerate
#check SevenForcingMinimality.seven_le_card_of_minimal
#check SevenForcingMinimality.card_eq_seven_of_minimal_and_witness
