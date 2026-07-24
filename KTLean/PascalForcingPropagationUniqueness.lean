import KTLean.PascalForcingPropagation

/-!
# Uniqueness of Triadic Two-Parent Propagation

## Formal status

**Level 2 — Consequence of the seed row and local two-parent update
rule.**

The preceding module constructs one triangular field by:

* starting from the single positive seed row;
* using inactive values outside each finite row;
* updating every new position from its two parents.

This module proves that the construction is unique.

Any field with the same initial row and the same local update rule is
equal at every address to `PascalForcingPropagation.propagate`.

No binomial coefficients and no pre-existing Pascal theorem enter this
argument.
-/

namespace PascalForcingPropagationUniqueness

open PascalMod3
open PascalForcingTriadicAddition
open PascalForcingPropagation

/--
A field satisfies the propagation specification when:

1. row zero is exactly `seedRow`;
2. every successor row is obtained by `nextRowValue`.
-/
structure SatisfiesPropagation
    (field : Nat → Nat → Control) :
    Prop where

  seed :
    ∀ position : Nat,
      field 0 position =
        seedRow position

  successor :
    ∀ rowIndex position : Nat,
      field (rowIndex + 1) position =
        nextRowValue
          (field rowIndex)
          rowIndex
          position

/--
The constructed propagation field satisfies the initial seed
condition.
-/
theorem propagate_satisfies_seed
    (position : Nat) :
    propagate 0 position =
      seedRow position := by

  cases position <;>
    rfl

/--
The constructed propagation field satisfies the successor update
condition.
-/
theorem propagate_satisfies_successor
    (rowIndex position : Nat) :
    propagate (rowIndex + 1) position =
      nextRowValue
        (propagate rowIndex)
        rowIndex
        position := by

  exact
    propagate_successor
      rowIndex
      position

/--
The recursively constructed field satisfies the full propagation
specification.
-/
theorem propagate_satisfies :
    SatisfiesPropagation propagate where

  seed :=
    propagate_satisfies_seed

  successor :=
    propagate_satisfies_successor

/--
Any field satisfying the propagation specification has each row equal
to the corresponding recursively generated row.
-/
theorem row_eq_propagatedRow
    (field : Nat → Nat → Control)
    (hField : SatisfiesPropagation field)
    (rowIndex : Nat) :
    field rowIndex =
      propagatedRow rowIndex := by

  induction rowIndex with

  | zero =>
      funext position

      exact
        hField.seed
          position

  | succ rowIndex inductionHypothesis =>
      funext position

      rw [
        hField.successor
          rowIndex
          position
      ]

      change
        nextRowValue
            (field rowIndex)
            rowIndex
            position =
          nextRowValue
            (propagatedRow rowIndex)
            rowIndex
            position

      rw [inductionHypothesis]

/--
Any field satisfying the seed and local update rule agrees pointwise
with the constructed propagation field.
-/
theorem field_eq_propagate
    (field : Nat → Nat → Control)
    (hField : SatisfiesPropagation field) :
    field =
      propagate := by

  funext rowIndex position

  have hRow :
      field rowIndex =
        propagatedRow rowIndex :=
    row_eq_propagatedRow
      field
      hField
      rowIndex

  exact
    congrFun
      hRow
      position

/--
The propagation specification has at most one solution.
-/
theorem propagation_unique
    (firstField secondField : Nat → Nat → Control)
    (hFirst : SatisfiesPropagation firstField)
    (hSecond : SatisfiesPropagation secondField) :
    firstField =
      secondField := by

  calc
    firstField =
        propagate := by
      exact
        field_eq_propagate
          firstField
          hFirst

    _ =
        secondField := by
      exact
        (
          field_eq_propagate
            secondField
            hSecond
        ).symm

/--
There exists exactly one field satisfying the propagation
specification.
-/
theorem existsUnique_propagation :
    ∃! field : Nat → Nat → Control,
      SatisfiesPropagation field := by

  refine
    ⟨
      propagate,
      propagate_satisfies,
      ?_
    ⟩

  intro field hField

  exact
    field_eq_propagate
      field
      hField

end PascalForcingPropagationUniqueness

#check PascalForcingPropagationUniqueness.SatisfiesPropagation
#check PascalForcingPropagationUniqueness.propagate_satisfies
#check PascalForcingPropagationUniqueness.row_eq_propagatedRow
#check PascalForcingPropagationUniqueness.field_eq_propagate
#check PascalForcingPropagationUniqueness.propagation_unique
#check PascalForcingPropagationUniqueness.existsUnique_propagation
