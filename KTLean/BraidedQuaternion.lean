import KTLean.CayleyDicksonQuaternion
import KTLean.PascalMod3

/-!
# Pascal-Controlled Routed Quaternions

This module connects Pascal modulo three to the
quaternion-block routing architecture.

The previous modules established independently that:

1. three quaternion conjugation bits generate the eight
   possible multiplication selectors;

2. selector, route, and orientation data reconstruct the
   Cayley–Dickson product;

3. Pascal modulo three provides a lossless ternary control
   field with inactive, positive, and negative states.

Here the Pascal field begins to control the quaternionic
routing process.

The current milestone is deliberately limited:

- the multiplication selector remains the previously
  defined Cayley–Dickson selector;
- the destination route remains the previously defined
  Cayley–Dickson route;
- the orientation is now supplied by Pascal modulo three.

Thus this module removes one independent table from the
construction while making clear what remains to be derived.
-/

open scoped Quaternion

universe u

namespace BraidedQuaternion


/--
An address in Pascal's triangle.
-/
structure PascalAddress where
  row : Nat
  column : Nat
  deriving DecidableEq, Repr


/--
Read the ternary Pascal control state at an address.
-/
def controlAt
    (address : PascalAddress) :
    PascalMod3.Control :=
  PascalMod3.control
    address.row
    address.column


/--
The Pascal addresses assigned to the four elementary
quaternion-block interactions.

The chosen entries have the control pattern

    positive, positive, positive, negative,

which is exactly the orientation pattern required by
the Cayley–Dickson product.

These addresses are currently an explicit witness.
A later module must determine whether a more general
Pascal addressing law forces them.
-/
def cdPascalAddress :
    CayleyDicksonQuaternion.Block →
    CayleyDicksonQuaternion.Block →
    PascalAddress

  | .first, .first =>
      ⟨0, 0⟩

  | .first, .second =>
      ⟨1, 0⟩

  | .second, .first =>
      ⟨1, 1⟩

  | .second, .second =>
      ⟨2, 1⟩


/--
The first-first interaction receives positive
Pascal orientation.
-/
@[simp]
theorem controlAt_first_first :
    controlAt
        (
          cdPascalAddress
            CayleyDicksonQuaternion.Block.first
            CayleyDicksonQuaternion.Block.first
        ) =
      PascalMod3.Control.positive := by
  decide


/--
The first-second interaction receives positive
Pascal orientation.
-/
@[simp]
theorem controlAt_first_second :
    controlAt
        (
          cdPascalAddress
            CayleyDicksonQuaternion.Block.first
            CayleyDicksonQuaternion.Block.second
        ) =
      PascalMod3.Control.positive := by
  decide


/--
The second-first interaction receives positive
Pascal orientation.
-/
@[simp]
theorem controlAt_second_first :
    controlAt
        (
          cdPascalAddress
            CayleyDicksonQuaternion.Block.second
            CayleyDicksonQuaternion.Block.first
        ) =
      PascalMod3.Control.positive := by
  decide


/--
The second-second interaction receives negative
Pascal orientation.
-/
@[simp]
theorem controlAt_second_second :
    controlAt
        (
          cdPascalAddress
            CayleyDicksonQuaternion.Block.second
            CayleyDicksonQuaternion.Block.second
        ) =
      PascalMod3.Control.negative := by
  decide


variable {R : Type u}
variable [CommRing R]


/--
Apply a Pascal control state to a quaternionic payload.

- inactive routes are suppressed to zero;
- positive routes preserve the payload;
- negative routes reverse its additive orientation.
-/
def applyControl
    (control : PascalMod3.Control)
    (q : ℍ[R]) :
    ℍ[R] :=
  match control with
  | .inactive =>
      0
  | .positive =>
      q
  | .negative =>
      -q


@[simp]
theorem applyControl_inactive
    (q : ℍ[R]) :
    applyControl PascalMod3.Control.inactive q =
      0 := by
  rfl


@[simp]
theorem applyControl_positive
    (q : ℍ[R]) :
    applyControl PascalMod3.Control.positive q =
      q := by
  rfl


@[simp]
theorem applyControl_negative
    (q : ℍ[R]) :
    applyControl PascalMod3.Control.negative q =
      -q := by
  rfl


/--
A nonzero quaternionic payload remains nonzero under
every active Pascal instruction.
-/
theorem applyControl_ne_zero
    {control : PascalMod3.Control}
    {q : ℍ[R]}
    (hq : q ≠ 0)
    (hactive :
      control ≠ PascalMod3.Control.inactive) :
    applyControl control q ≠ 0 := by

  cases control with

  | inactive =>
      contradiction

  | positive =>
      simpa using hq

  | negative =>
      simpa using hq


/--
One Pascal-controlled quaternion-block interaction.

The selector computes the local quaternionic payload.

Pascal modulo three supplies support and orientation.

The block route determines the destination compartment.
-/
def pascalRoutedTerm
    (leftBlock rightBlock :
      CayleyDicksonQuaternion.Block)
    (q r : ℍ[R]) :
    CayleyDicksonQuaternion.Carrier (R := R) :=

  CayleyDicksonQuaternion.place

    (
      CayleyDicksonQuaternion.cdRoute
        leftBlock
        rightBlock
    )

    (
      applyControl

        (
          controlAt
            (
              cdPascalAddress
                leftBlock
                rightBlock
            )
        )

        (
          CayleyDicksonQuaternion.runSelector

            (
              CayleyDicksonQuaternion.cdSelector
                leftBlock
                rightBlock
            )

            q
            r
        )
    )


/--
The Pascal-controlled term agrees with the earlier
Cayley–Dickson routed term for every block pair.

This proves that the independent orientation table can be
replaced by Pascal-modulo-three control on the four
elementary interactions.
-/
theorem pascalRoutedTerm_eq_routedTerm
    (leftBlock rightBlock :
      CayleyDicksonQuaternion.Block)
    (q r : ℍ[R]) :

    pascalRoutedTerm
        leftBlock
        rightBlock
        q
        r =

      CayleyDicksonQuaternion.routedTerm
        leftBlock
        rightBlock
        q
        r := by

  cases leftBlock <;>
    cases rightBlock <;>
    simp [
      pascalRoutedTerm,
      CayleyDicksonQuaternion.routedTerm,
      CayleyDicksonQuaternion.cdOrientation
    ]


/--
The four Pascal-controlled quaternion interactions
reassembled into one global product.
-/
def pascalRoutedMul
    (x y :
      CayleyDicksonQuaternion.Carrier (R := R)) :
    CayleyDicksonQuaternion.Carrier (R := R) :=

  pascalRoutedTerm
      CayleyDicksonQuaternion.Block.first
      CayleyDicksonQuaternion.Block.first
      x.1
      y.1

  +

  pascalRoutedTerm
      CayleyDicksonQuaternion.Block.first
      CayleyDicksonQuaternion.Block.second
      x.1
      y.2

  +

  pascalRoutedTerm
      CayleyDicksonQuaternion.Block.second
      CayleyDicksonQuaternion.Block.first
      x.2
      y.1

  +

  pascalRoutedTerm
      CayleyDicksonQuaternion.Block.second
      CayleyDicksonQuaternion.Block.second
      x.2
      y.2


/--
The Pascal-controlled global product agrees with the
previous selector-route-orientation reconstruction.
-/
theorem pascalRoutedMul_eq_routedMul
    (x y :
      CayleyDicksonQuaternion.Carrier (R := R)) :

    pascalRoutedMul x y =

      CayleyDicksonQuaternion.routedMul x y := by

  simp only [
    pascalRoutedMul,
    CayleyDicksonQuaternion.routedMul,
    pascalRoutedTerm_eq_routedTerm
  ]


/--
The Pascal-controlled routed quaternion product
reconstructs the Cayley–Dickson multiplication exactly.
-/
theorem pascalRoutedMul_eq_cdMul
    (x y :
      CayleyDicksonQuaternion.Carrier (R := R)) :

    pascalRoutedMul x y =

      CayleyDicksonQuaternion.cdMul x y := by

  calc
    pascalRoutedMul x y =
        CayleyDicksonQuaternion.routedMul x y := by
          exact
            pascalRoutedMul_eq_routedMul x y

    _ =
        CayleyDicksonQuaternion.cdMul x y := by
          exact
            CayleyDicksonQuaternion.routedMul_eq_cdMul
              x
              y


/--
Coordinate form of the Pascal-controlled product.
-/
@[simp]
theorem pascalRoutedMul_apply
    (a b c d : ℍ[R]) :

    pascalRoutedMul
        (R := R)
        (a, b)
        (c, d) =

      (
        a * c - star d * b,
        d * a + b * star c
      ) := by

  rw [
    pascalRoutedMul_eq_cdMul
  ]

  rfl


end BraidedQuaternion


#check BraidedQuaternion.PascalAddress
#check BraidedQuaternion.controlAt
#check BraidedQuaternion.cdPascalAddress
#check BraidedQuaternion.controlAt_first_first
#check BraidedQuaternion.controlAt_first_second
#check BraidedQuaternion.controlAt_second_first
#check BraidedQuaternion.controlAt_second_second
#check BraidedQuaternion.applyControl
#check BraidedQuaternion.applyControl_ne_zero
#check BraidedQuaternion.pascalRoutedTerm
#check BraidedQuaternion.pascalRoutedTerm_eq_routedTerm
#check BraidedQuaternion.pascalRoutedMul
#check BraidedQuaternion.pascalRoutedMul_eq_routedMul
#check BraidedQuaternion.pascalRoutedMul_eq_cdMul
#check BraidedQuaternion.pascalRoutedMul_apply
