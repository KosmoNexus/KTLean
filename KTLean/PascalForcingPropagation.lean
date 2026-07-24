import KTLean.PascalForcingTriadicResidues

/-!
# Two-Parent Propagation on the Triadic Alphabet

## Formal status

**Level 1 — Concrete propagation witness.**

This module defines a triangular state field generated from:

* one positive seed at row zero;
* inactive values outside each finite row;
* the local two-parent rule

      next = leftParent + rightParent.

The recursion is structural in the row number. No binomial
coefficients or pre-existing Pascal construction are used.
-/

namespace PascalForcingPropagation

open PascalMod3
open PascalForcingTriadicAddition

/--
A row is a total function on natural-number positions.

Only positions at or below the row index are regarded as internal.
-/
abbrev Row :=
  Nat → Control

/--
The single-seed initial row.
-/
def seedRow :
    Row

  | 0 =>
      .positive

  | _ + 1 =>
      .inactive

/--
Read a row using the inactive boundary convention.
-/
def boundedValue
    (row : Row)
    (rowIndex position : Nat) :
    Control :=

  if position ≤ rowIndex then
    row position
  else
    .inactive

/--
One two-parent update.

At position zero the nonexistent left parent is inactive.
At every positive position, the parents are the preceding and current
positions of the previous row.
-/
def nextRowValue
    (row : Row)
    (rowIndex position : Nat) :
    Control :=

  match position with

  | 0 =>
      add
        .inactive
        (boundedValue row rowIndex 0)

  | previous + 1 =>
      add
        (boundedValue row rowIndex previous)
        (boundedValue row rowIndex (previous + 1))

/--
The recursively generated sequence of rows.
-/
def propagatedRow :
    Nat → Row

  | 0 =>
      seedRow

  | rowIndex + 1 =>
      fun position =>
        nextRowValue
          (propagatedRow rowIndex)
          rowIndex
          position

/--
The propagated triangular field.
-/
def propagate
    (rowIndex position : Nat) :
    Control :=

  propagatedRow rowIndex position

/--
The initial seed is positive.
-/
@[simp]
theorem propagate_zero_zero :
    propagate 0 0 =
      .positive := by

  rfl

/--
All positive positions in row zero are inactive.
-/
@[simp]
theorem propagate_zero_successor
    (position : Nat) :
    propagate 0 (position + 1) =
      .inactive := by

  rfl

/--
The propagated field obeys the two-parent update rule.
-/
theorem propagate_successor
    (rowIndex position : Nat) :
    propagate (rowIndex + 1) position =
      nextRowValue
        (propagatedRow rowIndex)
        rowIndex
        position := by

  rfl

/--
The value at the left edge of the first generated row is positive.
-/
theorem propagate_one_zero :
    propagate 1 0 =
      .positive := by

  rfl

/--
The value at the right edge of the first generated row is positive.
-/
theorem propagate_one_one :
    propagate 1 1 =
      .positive := by

  rfl

/--
The first generated row is `[positive, positive]`.
-/
theorem row_one_values :
    propagate 1 0 = .positive
      ∧
    propagate 1 1 = .positive := by

  exact
    ⟨
      propagate_one_zero,
      propagate_one_one
    ⟩

/--
The second generated row is `[positive, negative, positive]`.
-/
theorem row_two_values :
    propagate 2 0 = .positive
      ∧
    propagate 2 1 = .negative
      ∧
    propagate 2 2 = .positive := by

  constructor

  · rfl

  · constructor <;>
      rfl

/--
The third generated row is
`[positive, inactive, inactive, positive]`.
-/
theorem row_three_values :
    propagate 3 0 = .positive
      ∧
    propagate 3 1 = .inactive
      ∧
    propagate 3 2 = .inactive
      ∧
    propagate 3 3 = .positive := by

  constructor

  · rfl

  · constructor

    · rfl

    · constructor <;>
        rfl

/--
The fourth generated row is
`[positive, positive, inactive, positive, positive]`.
-/
theorem row_four_values :
    propagate 4 0 = .positive
      ∧
    propagate 4 1 = .positive
      ∧
    propagate 4 2 = .inactive
      ∧
    propagate 4 3 = .positive
      ∧
    propagate 4 4 = .positive := by

  constructor

  · rfl

  · constructor

    · rfl

    · constructor

      · rfl

      · constructor <;>
          rfl

end PascalForcingPropagation

#check PascalForcingPropagation.Row
#check PascalForcingPropagation.seedRow
#check PascalForcingPropagation.boundedValue
#check PascalForcingPropagation.nextRowValue
#check PascalForcingPropagation.propagatedRow
#check PascalForcingPropagation.propagate
#check PascalForcingPropagation.propagate_successor
#check PascalForcingPropagation.row_one_values
#check PascalForcingPropagation.row_two_values
#check PascalForcingPropagation.row_three_values
#check PascalForcingPropagation.row_four_values
