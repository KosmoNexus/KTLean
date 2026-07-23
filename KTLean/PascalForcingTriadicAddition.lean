import KTLean.PascalMod3

/-!
# Explicit Addition on the Triadic Control Alphabet

## Formal status

**Level 1 — Concrete additive witness.**

This module defines the complete balanced-ternary addition table on the
existing three-state control alphabet:

    inactive = 0
    positive = +1
    negative = -1.

No modular arithmetic, equivalence, external classification theorem, or
noncomputable construction is used here.

The purpose of this module is to isolate the finite additive object
cleanly before proving that it is forced and before identifying it with
addition modulo three.
-/

namespace PascalForcingTriadicAddition

open PascalMod3

/--
Explicit closed addition on the triadic control alphabet.
-/
def add :
    Control → Control → Control

  | .inactive, .inactive =>
      .inactive

  | .inactive, .positive =>
      .positive

  | .inactive, .negative =>
      .negative

  | .positive, .inactive =>
      .positive

  | .positive, .positive =>
      .negative

  | .positive, .negative =>
      .inactive

  | .negative, .inactive =>
      .negative

  | .negative, .positive =>
      .inactive

  | .negative, .negative =>
      .positive

/--
Explicit additive inverse on the triadic control alphabet.
-/
def neg :
    Control → Control

  | .inactive =>
      .inactive

  | .positive =>
      .negative

  | .negative =>
      .positive

/--
The full triadic addition table.
-/
theorem add_table
    (first second : Control) :
    add first second =
      match first, second with
      | .inactive, .inactive =>
          .inactive
      | .inactive, .positive =>
          .positive
      | .inactive, .negative =>
          .negative
      | .positive, .inactive =>
          .positive
      | .positive, .positive =>
          .negative
      | .positive, .negative =>
          .inactive
      | .negative, .inactive =>
          .negative
      | .negative, .positive =>
          .inactive
      | .negative, .negative =>
          .positive := by

  cases first <;>
    cases second <;>
    rfl

/--
Inactive is the additive identity on the left.
-/
@[simp]
theorem add_inactive_left
    (state : Control) :
    add .inactive state =
      state := by

  cases state <;>
    rfl

/--
Inactive is the additive identity on the right.
-/
@[simp]
theorem add_inactive_right
    (state : Control) :
    add state .inactive =
      state := by

  cases state <;>
    rfl

/--
Two positive states sum to the negative state.
-/
@[simp]
theorem add_positive_positive :
    add .positive .positive =
      .negative := by

  rfl

/--
Positive and negative cancel.
-/
@[simp]
theorem add_positive_negative :
    add .positive .negative =
      .inactive := by

  rfl

/--
Negative and positive cancel.
-/
@[simp]
theorem add_negative_positive :
    add .negative .positive =
      .inactive := by

  rfl

/--
Two negative states sum to the positive state.
-/
@[simp]
theorem add_negative_negative :
    add .negative .negative =
      .positive := by

  rfl

/--
Triadic addition is commutative.
-/
theorem add_commutative
    (first second : Control) :
    add first second =
      add second first := by

  cases first <;>
    cases second <;>
    rfl

/--
Triadic addition is associative.
-/
theorem add_associative
    (first second third : Control) :
    add (add first second) third =
      add first (add second third) := by

  cases first <;>
    cases second <;>
    cases third <;>
    rfl

/--
Inactive is its own inverse.
-/
@[simp]
theorem neg_inactive :
    neg .inactive =
      .inactive := by

  rfl

/--
Positive and negative are additive inverses.
-/
@[simp]
theorem neg_positive :
    neg .positive =
      .negative := by

  rfl

/--
Negative and positive are additive inverses.
-/
@[simp]
theorem neg_negative :
    neg .negative =
      .positive := by

  rfl

/--
Negation is involutive.
-/
@[simp]
theorem neg_neg
    (state : Control) :
    neg (neg state) =
      state := by

  cases state <;>
    rfl

/--
Every state cancels with its additive inverse on the right.
-/
@[simp]
theorem add_neg_right
    (state : Control) :
    add state (neg state) =
      .inactive := by

  cases state <;>
    rfl

/--
Every state cancels with its additive inverse on the left.
-/
@[simp]
theorem add_neg_left
    (state : Control) :
    add (neg state) state =
      .inactive := by

  cases state <;>
    rfl

/--
Negation reverses a sum.

Because the operation is commutative, this is equivalent to the usual
additive-group identity.
-/
theorem neg_add
    (first second : Control) :
    neg (add first second) =
      add (neg first) (neg second) := by

  cases first <;>
    cases second <;>
    rfl

end PascalForcingTriadicAddition

#check PascalForcingTriadicAddition.add
#check PascalForcingTriadicAddition.neg
#check PascalForcingTriadicAddition.add_table
#check PascalForcingTriadicAddition.add_inactive_left
#check PascalForcingTriadicAddition.add_inactive_right
#check PascalForcingTriadicAddition.add_commutative
#check PascalForcingTriadicAddition.add_associative
#check PascalForcingTriadicAddition.neg_neg
#check PascalForcingTriadicAddition.add_neg_right
#check PascalForcingTriadicAddition.add_neg_left
#check PascalForcingTriadicAddition.neg_add
