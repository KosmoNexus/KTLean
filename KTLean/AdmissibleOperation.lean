import KTLean.Fano
import KTLean.RoutedTokenization
import Mathlib.Data.Fintype.Card

/-!
# Admissible Local Operations

This module constructs the first finite candidate space from
the structural coordinates already present in KT:

1. one of seven Fano line addresses;
2. one of three roles within the local triad;
3. one of two orientations.

The resulting coordinate space contains exactly

    7 × 3 × 2 = 42

distinct admissible local operations.

This is not yet a global classification theorem saying that
every lawful KT operation must possess this form. It is the
construction of the finite normal-form candidate on which
that later theorem can be built.
-/

namespace AdmissibleOperation


/-
## Triadic role
-/

/--
The three distinguishable positions within one oriented
local Fano triad.
-/
inductive TriadicRole where

  /-- The line-address point itself. -/
  | anchor

  /-- The first directed neighbor. -/
  | successor

  /-- The remaining point completing the triad. -/
  | completion

  deriving
    DecidableEq,
    Repr


/--
Explicit finite enumeration of the three triadic roles.
-/
instance triadicRoleFintype :
    Fintype TriadicRole where

  elems :=
    {
      TriadicRole.anchor,
      TriadicRole.successor,
      TriadicRole.completion
    }

  complete := by

    intro role

    cases role <;>
      simp
/--
The triadic role space contains exactly three elements.
-/
theorem triadicRole_card :

    Fintype.card TriadicRole = 3 := by

  native_decide


/-
## Orientation
-/

/--
The pre-existing KT orientation type has exactly two
elements.
-/
instance orientationFintype :
    Fintype Orientation where

  elems :=
    {
      Orientation.cw,
      Orientation.ccw
    }

  complete := by

    intro orientation

    cases orientation <;>
      simp


/--
The orientation space contains exactly two elements.
-/
theorem orientation_card :

    Fintype.card Orientation = 2 := by

  native_decide


/-
## Structural coordinates
-/

/--
The complete local coordinate data for one admissible
operation.

The three factors are:

- Fano address;
- role within the addressed triad;
- orientation of traversal.
-/
structure Coordinates where

  address :
    Fano.Point

  role :
    TriadicRole

  orientation :
    Orientation

  deriving
    DecidableEq,
    Repr


/--
At this stage an admissible operation is exactly one
structural coordinate triple.

A later classification module must prove that every lawful
local KT action possesses a unique coordinate triple of
this form.
-/
abbrev Operation :=
  Coordinates


/--
The raw product coordinate type.
-/
abbrev CoordinateProduct :=

  Fano.Point ×
    TriadicRole ×
      Orientation


/--
Convert a structured coordinate into product form.
-/
def toProduct
    (operation : Operation) :
    CoordinateProduct :=

  (
    operation.address,
    operation.role,
    operation.orientation
  )


/--
Construct an operation from product-form coordinates.
-/
def ofProduct
    (coordinates : CoordinateProduct) :
    Operation where

  address :=
    coordinates.1

  role :=
    coordinates.2.1

  orientation :=
    coordinates.2.2


/--
Product conversion followed by reconstruction returns the
original operation.
-/
@[simp]
theorem ofProduct_toProduct
    (operation : Operation) :

    ofProduct
        (toProduct operation) =
      operation := by

  cases operation

  rfl


/--
Reconstruction followed by product conversion returns the
original coordinate product.
-/
@[simp]
theorem toProduct_ofProduct
    (coordinates : CoordinateProduct) :

    toProduct
        (ofProduct coordinates) =
      coordinates := by

  rcases coordinates with
    ⟨address, role, orientation⟩

  rfl


/--
Admissible operations are equivalent to the explicit
prime-factor coordinate product.
-/
def coordinateEquiv :

    Operation ≃ CoordinateProduct where

  toFun :=
    toProduct

  invFun :=
    ofProduct

  left_inv :=
    ofProduct_toProduct

  right_inv :=
    toProduct_ofProduct

/--
The operation space is finite because it is equivalent to
the finite product of Fano address, triadic role, and
orientation.
-/
instance operationFintype :
    Fintype Operation :=

  Fintype.ofEquiv
    CoordinateProduct
    coordinateEquiv.symm
/-
## Oriented Fano readout
-/

/--
The anchor point of the Fano line addressed by `address`.
-/
def anchorPoint
    (address : Fano.Point) :
    Fano.Point :=

  address


/--
The cyclic neighbor used to generate the addressed Fano
line.
-/
def successorPoint
    (address : Fano.Point) :
    Fano.Point :=

  address + 1


/--
The third point on the addressed Fano line.
-/
def completionPoint
    (address : Fano.Point) :
    Fano.Point :=

  Fano.complete
    address
    (address + 1)


/--
Read the Fano point selected by a role and orientation.

Clockwise traversal orders the local triad as:

    anchor, successor, completion

Counterclockwise traversal reverses the two non-anchor
roles:

    anchor, completion, successor
-/
def selectedPoint
    (operation : Operation) :
    Fano.Point :=

  match
    operation.orientation,
    operation.role
  with

  | Orientation.cw,
      TriadicRole.anchor =>

      anchorPoint operation.address

  | Orientation.cw,
      TriadicRole.successor =>

      successorPoint operation.address

  | Orientation.cw,
      TriadicRole.completion =>

      completionPoint operation.address

  | Orientation.ccw,
      TriadicRole.anchor =>

      anchorPoint operation.address

  | Orientation.ccw,
      TriadicRole.successor =>

      completionPoint operation.address

  | Orientation.ccw,
      TriadicRole.completion =>

      successorPoint operation.address


@[simp]
theorem selectedPoint_cw_anchor
    (address : Fano.Point) :

    selectedPoint
        {
          address := address
          role := TriadicRole.anchor
          orientation := Orientation.cw
        } =

      anchorPoint address := by

  rfl


@[simp]
theorem selectedPoint_cw_successor
    (address : Fano.Point) :

    selectedPoint
        {
          address := address
          role := TriadicRole.successor
          orientation := Orientation.cw
        } =

      successorPoint address := by

  rfl


@[simp]
theorem selectedPoint_cw_completion
    (address : Fano.Point) :

    selectedPoint
        {
          address := address
          role := TriadicRole.completion
          orientation := Orientation.cw
        } =

      completionPoint address := by

  rfl


@[simp]
theorem selectedPoint_ccw_anchor
    (address : Fano.Point) :

    selectedPoint
        {
          address := address
          role := TriadicRole.anchor
          orientation := Orientation.ccw
        } =

      anchorPoint address := by

  rfl


@[simp]
theorem selectedPoint_ccw_successor
    (address : Fano.Point) :

    selectedPoint
        {
          address := address
          role := TriadicRole.successor
          orientation := Orientation.ccw
        } =

      completionPoint address := by

  rfl


@[simp]
theorem selectedPoint_ccw_completion
    (address : Fano.Point) :

    selectedPoint
        {
          address := address
          role := TriadicRole.completion
          orientation := Orientation.ccw
        } =

      successorPoint address := by

  rfl


/-
## Coordinate rigidity
-/

/--
Two operations are equal when all three structural
coordinates agree.
-/
theorem ext
    {left right : Operation}
    (haddress :
      left.address =
        right.address)
    (hrole :
      left.role =
        right.role)
    (horientation :
      left.orientation =
        right.orientation) :

    left = right := by

  cases left

  cases right

  simp_all


/--
Equality of operations forces equality of their Fano
addresses.
-/
theorem address_eq_of_operation_eq
    {left right : Operation}
    (hoperation :
      left = right) :

    left.address =
      right.address := by

  exact
    congrArg Coordinates.address
      hoperation


/--
Equality of operations forces equality of their triadic
roles.
-/
theorem role_eq_of_operation_eq
    {left right : Operation}
    (hoperation :
      left = right) :

    left.role =
      right.role := by

  exact
    congrArg Coordinates.role
      hoperation


/--
Equality of operations forces equality of their
orientations.
-/
theorem orientation_eq_of_operation_eq
    {left right : Operation}
    (hoperation :
      left = right) :

    left.orientation =
      right.orientation := by

  exact
    congrArg Coordinates.orientation
      hoperation


/--
Changing the Fano address changes the operation.
-/
theorem ne_of_address_ne
    {left right : Operation}
    (haddress :
      left.address ≠
        right.address) :

    left ≠ right := by

  intro hoperation

  exact
    haddress
      (
        address_eq_of_operation_eq
          hoperation
      )


/--
Changing the triadic role changes the operation.
-/
theorem ne_of_role_ne
    {left right : Operation}
    (hrole :
      left.role ≠
        right.role) :

    left ≠ right := by

  intro hoperation

  exact
    hrole
      (
        role_eq_of_operation_eq
          hoperation
      )


/--
Changing orientation changes the operation.
-/
theorem ne_of_orientation_ne
    {left right : Operation}
    (horientation :
      left.orientation ≠
        right.orientation) :

    left ≠ right := by

  intro hoperation

  exact
    horientation
      (
        orientation_eq_of_operation_eq
          hoperation
      )


/-
## Enumeration
-/

/--
The Fano address space contains seven elements.
-/
theorem fanoPoint_card :

    Fintype.card Fano.Point = 7 := by

  native_decide


/--
The admissible-operation coordinate space has exactly
forty-two elements.
-/
theorem operation_card :

    Fintype.card Operation = 42 := by

  native_decide


/--
The cardinality factors according to the three independent
structural coordinates.
-/
theorem operation_card_prime_factorization :

    Fintype.card Operation =

      Fintype.card Fano.Point
        *
      Fintype.card TriadicRole
        *
      Fintype.card Orientation := by

  native_decide


/--
The explicit cardinality is the prime product

    7 × 3 × 2.
-/
theorem operation_card_eq_seven_times_three_times_two :

    Fintype.card Operation =
      7 * 3 * 2 := by

  native_decide


/--
There are exactly forty-two distinct structural normal
forms in the present admissible-operation candidate.
-/
theorem forty_two_candidate_operations :

    Fintype.card Operation = 42 := by

  exact operation_card


end AdmissibleOperation


#check AdmissibleOperation.TriadicRole
#check AdmissibleOperation.triadicRole_card
#check AdmissibleOperation.orientation_card
#check AdmissibleOperation.Coordinates
#check AdmissibleOperation.Operation
#check AdmissibleOperation.CoordinateProduct
#check AdmissibleOperation.toProduct
#check AdmissibleOperation.ofProduct
#check AdmissibleOperation.coordinateEquiv
#check AdmissibleOperation.anchorPoint
#check AdmissibleOperation.successorPoint
#check AdmissibleOperation.completionPoint
#check AdmissibleOperation.selectedPoint
#check AdmissibleOperation.ext
#check AdmissibleOperation.ne_of_address_ne
#check AdmissibleOperation.ne_of_role_ne
#check AdmissibleOperation.ne_of_orientation_ne
#check AdmissibleOperation.fanoPoint_card
#check AdmissibleOperation.operation_card
#check AdmissibleOperation.operation_card_prime_factorization
#check AdmissibleOperation.operation_card_eq_seven_times_three_times_two
#check AdmissibleOperation.forty_two_candidate_operations
