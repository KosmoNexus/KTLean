import KTLean.PascalForcingExistingControlBridge

/-!
# Identification of Forced Propagation with Binomial Recursion

## Formal status

**Level 2 — Consequence of the seed condition, closed triadic
addition, and the local two-parent update rule.**

This module defines the binomial-control field

    binomialField n k = decode (Nat.choose n k).

It proves that this field:

1. has the same single positive seed row;
2. obeys the same inactive boundary convention;
3. satisfies the same local two-parent update rule.

By the previously proved uniqueness theorem, the recursively forced
triadic field is therefore exactly the binomial field.

This is the point at which Pascal structure is identified as the
unique global solution of the local additive propagation law.
-/

namespace PascalForcingBinomialIdentification

open PascalMod3
open PascalForcingTriadicAddition
open PascalForcingTriadicResidues
open PascalForcingPropagation
open PascalForcingPropagationUniqueness
open PascalForcingExistingControlBridge

/--
The binomial coefficient field interpreted through the canonical
triadic residue decoder.
-/
def binomialField
    (rowIndex position : Nat) :
    Control :=

  decode
    (
      Nat.choose
        rowIndex
        position
    )

/--
Decoding converts addition of natural numbers into triadic addition.
-/
theorem decode_add
    (first second : Nat) :
    decode (first + second) =
      add
        (decode first)
        (decode second) := by

  apply encode_injective

  rw [
    encode_decode,
    encode_add,
    encode_decode,
    encode_decode
  ]

  exact
    Nat.add_mod
      first
      second
      3

/--
Outside a binomial row, the binomial coefficient is zero and therefore
already represents the inactive state.

Consequently, applying the explicit bounded-value convention does not
change the binomial field.
-/
theorem boundedValue_binomialField
    (rowIndex position : Nat) :
    boundedValue
        (binomialField rowIndex)
        rowIndex
        position =
      binomialField
        rowIndex
        position := by

  unfold boundedValue

  by_cases hInside :
      position ≤ rowIndex

  · simp [hInside]

  · have hOutside :
        rowIndex < position := by
      exact
        Nat.lt_of_not_ge
          hInside

    have hChoose :
        Nat.choose rowIndex position =
          0 := by
      exact
        Nat.choose_eq_zero_of_lt
          hOutside

    simp [
      hInside,
      binomialField,
      hChoose,
      decode
    ]

/--
The binomial-control field has the required single-seed initial row.
-/
theorem binomialField_seed
    (position : Nat) :
    binomialField 0 position =
      seedRow position := by

  cases position with

  | zero =>
      rfl

  | succ position =>
      rfl

/--
At the left boundary, the binomial-control field obeys the local
two-parent update rule.
-/
theorem binomialField_successor_zero
    (rowIndex : Nat) :
    binomialField
        (rowIndex + 1)
        0 =
      nextRowValue
        (binomialField rowIndex)
        rowIndex
        0 := by

  simp [
    binomialField,
    nextRowValue,
    boundedValue,
    decode,
    add
  ]

/--
At every positive position, the binomial-control field obeys the local
two-parent update rule by Pascal's binomial recurrence.
-/
theorem binomialField_successor_positive
    (rowIndex previous : Nat) :
    binomialField
        (rowIndex + 1)
        (previous + 1) =
      nextRowValue
        (binomialField rowIndex)
        rowIndex
        (previous + 1) := by

  change
    binomialField
        (rowIndex + 1)
        (previous + 1) =
      add
        (
          boundedValue
            (binomialField rowIndex)
            rowIndex
            previous
        )
        (
          boundedValue
            (binomialField rowIndex)
            rowIndex
            (previous + 1)
        )

  rw [
    boundedValue_binomialField,
    boundedValue_binomialField
  ]

  unfold binomialField

  rw [Nat.choose_succ_succ']

  exact
    decode_add
      (Nat.choose rowIndex previous)
      (Nat.choose rowIndex (previous + 1))
/--
The binomial-control field satisfies the successor update rule at every
position.
-/
theorem binomialField_successor
    (rowIndex position : Nat) :
    binomialField
        (rowIndex + 1)
        position =
      nextRowValue
        (binomialField rowIndex)
        rowIndex
        position := by

  cases position with

  | zero =>
      exact
        binomialField_successor_zero
          rowIndex

  | succ previous =>
      exact
        binomialField_successor_positive
          rowIndex
          previous

/--
The binomial-control field satisfies the complete propagation
specification.
-/
theorem binomialField_satisfies :
    SatisfiesPropagation binomialField where

  seed :=
    binomialField_seed

  successor :=
    binomialField_successor

/--
The uniquely forced propagation field is exactly the binomial-control
field.
-/
theorem propagate_eq_binomialField :
    propagate =
      binomialField := by

  exact
    (
      field_eq_propagate
        binomialField
        binomialField_satisfies
    ).symm

/--
At every address, forced propagation equals the decoded binomial
coefficient.
-/
theorem propagate_eq_decode_choose
    (rowIndex position : Nat) :
    propagate rowIndex position =
      decode
        (
          Nat.choose
            rowIndex
            position
        ) := by

  exact
    congrFun
      (
        congrFun
          propagate_eq_binomialField
          rowIndex
      )
      position

/--
The forced propagation field is exactly the existing
`PascalMod3.control` field.
-/
theorem propagate_eq_existing_control
    (rowIndex position : Nat) :
    propagate rowIndex position =
      PascalMod3.control
        rowIndex
        position := by

  rw [
    propagate_eq_decode_choose,
    control_eq_decode_choose
  ]

/--
The existing Pascal modulo-three control field is the unique field
satisfying the single-seed two-parent propagation specification.
-/
theorem existing_control_is_unique_propagation :
    ∃! field : Nat → Nat → Control,
      SatisfiesPropagation field
        ∧
      field =
        PascalMod3.control := by

  have hControl :
      PascalMod3.control =
        propagate := by

    funext rowIndex position

    exact
      (
        propagate_eq_existing_control
          rowIndex
          position
      ).symm

  refine
    ⟨
      PascalMod3.control,
      ?_,
      ?_
    ⟩

  · constructor

    · rw [hControl]

      exact
        propagate_satisfies

    · rfl

  · intro field hField

    exact
      hField.2

end PascalForcingBinomialIdentification

#check PascalForcingBinomialIdentification.binomialField
#check PascalForcingBinomialIdentification.decode_add
#check PascalForcingBinomialIdentification.boundedValue_binomialField
#check PascalForcingBinomialIdentification.binomialField_seed
#check PascalForcingBinomialIdentification.binomialField_successor
#check PascalForcingBinomialIdentification.binomialField_satisfies
#check PascalForcingBinomialIdentification.propagate_eq_binomialField
#check PascalForcingBinomialIdentification.propagate_eq_decode_choose
#check PascalForcingBinomialIdentification.propagate_eq_existing_control
