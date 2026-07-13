import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic

/-!
# Pascal Triangle Modulo Three

This module formalizes Pascal's triangle reduced modulo 3
as a finite routing and admissibility instruction layer.

Each binomial coefficient is reduced to one of three states:

    0 mod 3  → inactive
    1 mod 3  → positive
    2 mod 3  → negative

Under the balanced-ternary interpretation these states carry
the values

    0, +1, -1.

The ternary instruction also admits a two-bit decomposition:

    inactive → active = false, negative = false
    positive → active = true,  negative = false
    negative → active = true,  negative = true

Thus Pascal modulo 3 supplies both:

1. a support mask determining whether a route exists;
2. an orientation bit determining its sign.

No quaternionic or Fano structure is assumed in this module.
Those structures will consume this control data later.
-/

namespace PascalMod3


/--
The three routing states produced by Pascal coefficients
reduced modulo three.
-/
inductive Control
  | inactive
  | positive
  | negative
  deriving DecidableEq, Repr


/--
The balanced-ternary numerical value carried by a
Pascal control state.
-/
def balancedValue :
    Control → Int
  | .inactive => 0
  | .positive => 1
  | .negative => -1


@[simp]
theorem balancedValue_inactive :
    balancedValue Control.inactive = 0 := by
  rfl


@[simp]
theorem balancedValue_positive :
    balancedValue Control.positive = 1 := by
  rfl


@[simp]
theorem balancedValue_negative :
    balancedValue Control.negative = -1 := by
  rfl


/--
The Pascal coefficient at row `n`, position `k`,
reduced modulo three.
-/
def residue
    (n k : Nat) :
    Nat :=
  Nat.choose n k % 3


/--
Every Pascal residue lies in the three-element set
`{0,1,2}`.
-/
theorem residue_lt_three
    (n k : Nat) :
    residue n k < 3 := by

  exact
    Nat.mod_lt
      (Nat.choose n k)
      (by decide)


/--
Interpret a residue as a routing instruction.

The input is reduced modulo three internally, so this
function is total on all natural numbers.
-/
def controlOfNat
    (r : Nat) :
    Control :=
  if r % 3 = 0 then
    .inactive
  else if r % 3 = 1 then
    .positive
  else
    .negative


@[simp]
theorem controlOfNat_zero :
    controlOfNat 0 = .inactive := by
  rfl


@[simp]
theorem controlOfNat_one :
    controlOfNat 1 = .positive := by
  rfl


@[simp]
theorem controlOfNat_two :
    controlOfNat 2 = .negative := by
  rfl


/--
The Pascal routing instruction at row `n`,
position `k`.
-/
def control
    (n k : Nat) :
    Control :=
  controlOfNat (Nat.choose n k)


/--
Pascal control is inactive exactly when the
corresponding binomial coefficient vanishes modulo three.
-/
@[simp]
theorem control_eq_inactive_iff
    (n k : Nat) :
    control n k = .inactive ↔
      residue n k = 0 := by

  unfold control
  unfold residue
  unfold controlOfNat

  by_cases h0 :
      Nat.choose n k % 3 = 0

  · simp [h0]

  · by_cases h1 :
        Nat.choose n k % 3 = 1

    · simp [h1]

    · simp [h0, h1]


/--
A Pascal route is active exactly when its coefficient
is nonzero modulo three.
-/
theorem control_ne_inactive_iff
    (n k : Nat) :
    control n k ≠ .inactive ↔
      residue n k ≠ 0 := by

  simp


/--
The two binary control bits extracted from one
balanced-ternary Pascal instruction.

`active` determines support.

`negative` determines orientation when the route
is active.
-/
structure ControlBits where
  active : Bool
  negative : Bool
  deriving DecidableEq, Repr


/--
Encode a ternary Pascal instruction as support and
orientation bits.
-/
def controlBits :
    Control → ControlBits
  | .inactive =>
      ⟨false, false⟩
  | .positive =>
      ⟨true, false⟩
  | .negative =>
      ⟨true, true⟩


@[simp]
theorem controlBits_inactive :
    controlBits .inactive =
      ⟨false, false⟩ := by
  rfl


@[simp]
theorem controlBits_positive :
    controlBits .positive =
      ⟨true, false⟩ := by
  rfl


@[simp]
theorem controlBits_negative :
    controlBits .negative =
      ⟨true, true⟩ := by
  rfl


/--
The binary encoding loses no ternary information.
-/
theorem controlBits_injective :
    Function.Injective controlBits := by

  intro x y h

  cases x <;>
    cases y <;>
    simp [controlBits] at h ⊢


/--
The complete binary instruction generated at a
Pascal address.
-/
def instruction
    (n k : Nat) :
    ControlBits :=
  controlBits (control n k)


/--
The finite list of routing instructions in Pascal row `n`.
-/
def row
    (n : Nat) :
    List Control :=
  (List.range (n + 1)).map
    (control n)


/--
Pascal row `n` contains exactly `n+1` instructions.
-/
@[simp]
theorem row_length
    (n : Nat) :
    (row n).length = n + 1 := by

  simp [row]


/--
The active support of Pascal row `n`.
-/
def support
    (n : Nat) :
    Finset Nat :=
  (Finset.range (n + 1)).filter
    (fun k =>
      control n k ≠ .inactive)


/--
Membership in the support means both that the address
lies in the row and that its residue is nonzero.
-/
@[simp]
theorem mem_support
    {n k : Nat} :
    k ∈ support n ↔
      k < n + 1 ∧
      residue n k ≠ 0 := by

  simp [support]


/-!
## Initial rows

These finite computations certify that the control field
is the Pascal triangle modulo three, interpreted in
balanced-ternary form.
-/

theorem row_zero :
    row 0 =
      [.positive] := by
  decide


theorem row_one :
    row 1 =
      [
        .positive,
        .positive
      ] := by
  decide


theorem row_two :
    row 2 =
      [
        .positive,
        .negative,
        .positive
      ] := by
  decide


theorem row_three :
    row 3 =
      [
        .positive,
        .inactive,
        .inactive,
        .positive
      ] := by
  decide


theorem row_four :
    row 4 =
      [
        .positive,
        .positive,
        .inactive,
        .positive,
        .positive
      ] := by
  decide


theorem row_five :
    row 5 =
      [
        .positive,
        .negative,
        .positive,
        .positive,
        .negative,
        .positive
      ] := by
  decide


end PascalMod3


#check PascalMod3.Control
#check PascalMod3.balancedValue
#check PascalMod3.residue
#check PascalMod3.residue_lt_three
#check PascalMod3.controlOfNat
#check PascalMod3.control
#check PascalMod3.control_eq_inactive_iff
#check PascalMod3.control_ne_inactive_iff
#check PascalMod3.ControlBits
#check PascalMod3.controlBits
#check PascalMod3.controlBits_injective
#check PascalMod3.instruction
#check PascalMod3.row
#check PascalMod3.row_length
#check PascalMod3.support
#check PascalMod3.mem_support
#check PascalMod3.row_zero
#check PascalMod3.row_one
#check PascalMod3.row_two
#check PascalMod3.row_three
#check PascalMod3.row_four
#check PascalMod3.row_five
