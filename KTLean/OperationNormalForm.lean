import KTLean.AdmissibleOperation

/-!
# Lawful Operation Normal Form

`AdmissibleOperation` constructed 42 coordinate triples:

    Fano address × triadic role × orientation.

This module gives those coordinates an independent semantic
interpretation.

A lawful framed operation contains:

1. a Fano line address;
2. an oriented frame assigning the three triadic roles to
   the three points of that line;
3. one active role within that frame.

The orientation is not stored explicitly. It is recovered
from the ordering of the two non-anchor points.

The principal result is an equivalence:

    LawfulFramedOperation ≃ AdmissibleOperation.Operation

Thus every operation satisfying the framed Fano law has one
unique normal form among the 42 coordinate triples.

This remains a classification relative to the explicit
framed Fano law defined here. It is not yet a theorem that
every conceivable KT-local process must satisfy that law.
-/

namespace OperationNormalForm


open AdmissibleOperation


/-
## Oriented Fano frames
-/

/--
The point occupying a given triadic role in an oriented
Fano frame.
-/
def framePoint
    (address : Fano.Point)
    (orientation : Orientation)
    (role : TriadicRole) :
    Fano.Point :=

  selectedPoint
    {
      address := address
      role := role
      orientation := orientation
    }


@[simp]
theorem framePoint_cw_anchor
    (address : Fano.Point) :

    framePoint
        address
        Orientation.cw
        TriadicRole.anchor =

      anchorPoint address := by

  rfl


@[simp]
theorem framePoint_cw_successor
    (address : Fano.Point) :

    framePoint
        address
        Orientation.cw
        TriadicRole.successor =

      successorPoint address := by

  rfl


@[simp]
theorem framePoint_cw_completion
    (address : Fano.Point) :

    framePoint
        address
        Orientation.cw
        TriadicRole.completion =

      completionPoint address := by

  rfl


@[simp]
theorem framePoint_ccw_anchor
    (address : Fano.Point) :

    framePoint
        address
        Orientation.ccw
        TriadicRole.anchor =

      anchorPoint address := by

  rfl


@[simp]
theorem framePoint_ccw_successor
    (address : Fano.Point) :

    framePoint
        address
        Orientation.ccw
        TriadicRole.successor =

      completionPoint address := by

  rfl


@[simp]
theorem framePoint_ccw_completion
    (address : Fano.Point) :

    framePoint
        address
        Orientation.ccw
        TriadicRole.completion =

      successorPoint address := by

  rfl


/--
The cyclic successor and Fano completion points are always
distinct.
-/
theorem successor_ne_completion :

    ∀ address : Fano.Point,

      successorPoint address ≠
        completionPoint address := by

  native_decide


/-
## Semantic lawful operations
-/

/--
A lawful framed local operation.

The frame contains the three points of one addressed Fano
line. The anchor is fixed. The two non-anchor roles occur
in exactly one of the two possible orders.

The active role specifies which position of the oriented
frame is currently selected.
-/
structure LawfulFramedOperation where

  address :
    Fano.Point

  frame :
    TriadicRole → Fano.Point

  activeRole :
    TriadicRole

  anchor_law :
    frame TriadicRole.anchor =
      anchorPoint address

  nonAnchor_order :

      (
        frame TriadicRole.successor =
            successorPoint address
          ∧
        frame TriadicRole.completion =
            completionPoint address
      )

      ∨

      (
        frame TriadicRole.successor =
            completionPoint address
          ∧
        frame TriadicRole.completion =
            successorPoint address
      )


/--
Two lawful framed operations are equal when their address,
frame, and active role agree.

The law proofs then agree by proof irrelevance.
-/
theorem LawfulFramedOperation.ext
    {left right : LawfulFramedOperation}
    (haddress :
      left.address =
        right.address)
    (hframe :
      left.frame =
        right.frame)
    (hrole :
      left.activeRole =
        right.activeRole) :

    left = right := by

  cases left with
  | mk leftAddress leftFrame leftRole
      leftAnchor leftOrder =>

      cases right with
      | mk rightAddress rightFrame rightRole
          rightAnchor rightOrder =>

          cases haddress
          cases hframe
          cases hrole

          rfl


/-
## Recovering orientation from the frame
-/

/--
Recover orientation from the ordering of the non-anchor
points.

The frame law guarantees that only the two lawful cases are
possible.
-/
noncomputable def orientationOf
    (operation : LawfulFramedOperation) :
    Orientation :=

  if
    operation.frame TriadicRole.successor =
      successorPoint operation.address
  then
    Orientation.cw
  else
    Orientation.ccw


/--
The first lawful non-anchor ordering yields clockwise
orientation.
-/
theorem orientationOf_eq_cw
    (operation : LawfulFramedOperation)
    (horder :

      operation.frame TriadicRole.successor =
          successorPoint operation.address
        ∧

      operation.frame TriadicRole.completion =
          completionPoint operation.address) :

    orientationOf operation =
      Orientation.cw := by

  simp [
    orientationOf,
    horder.1
  ]


/--
The reversed lawful non-anchor ordering yields
counterclockwise orientation.
-/
theorem orientationOf_eq_ccw
    (operation : LawfulFramedOperation)
    (horder :

      operation.frame TriadicRole.successor =
          completionPoint operation.address
        ∧

      operation.frame TriadicRole.completion =
          successorPoint operation.address) :

    orientationOf operation =
      Orientation.ccw := by

  have hne :

      operation.frame TriadicRole.successor ≠
        successorPoint operation.address := by

    rw [horder.1]

    exact
      (
        successor_ne_completion
          operation.address
      ).symm

  simp [
    orientationOf,
    hne
  ]


/--
Every lawful frame is exactly the canonical frame generated
by its recovered orientation.
-/
theorem frame_eq_framePoint
    (operation : LawfulFramedOperation) :

    operation.frame =

      framePoint
        operation.address
        (orientationOf operation) := by

  funext role

  rcases operation.nonAnchor_order with
    hclockwise |
    hcounterclockwise

  · have horientation :
        orientationOf operation =
          Orientation.cw :=

      orientationOf_eq_cw
        operation
        hclockwise

    cases role with

    | anchor =>
        rw [
          operation.anchor_law,
          horientation
        ]

        rfl

    | successor =>
        rw [
          hclockwise.1,
          horientation
        ]

        rfl

    | completion =>
        rw [
          hclockwise.2,
          horientation
        ]

        rfl

  · have horientation :
        orientationOf operation =
          Orientation.ccw :=

      orientationOf_eq_ccw
        operation
        hcounterclockwise

    cases role with

    | anchor =>
        rw [
          operation.anchor_law,
          horientation
        ]

        rfl

    | successor =>
        rw [
          hcounterclockwise.1,
          horientation
        ]

        rfl

    | completion =>
        rw [
          hcounterclockwise.2,
          horientation
        ]

        rfl


/-
## Normal-form encoding
-/

/--
Extract the unique admissible coordinate triple from a
lawful framed operation.
-/
noncomputable def coordinatesOf
    (operation : LawfulFramedOperation) :
    AdmissibleOperation.Operation where

  address :=
    operation.address

  role :=
    operation.activeRole

  orientation :=
    orientationOf operation


/--
Construct the semantic lawful operation represented by one
admissible coordinate triple.
-/
def operationOf
    (coordinates :
      AdmissibleOperation.Operation) :
    LawfulFramedOperation where

  address :=
    coordinates.address

  frame :=
    framePoint
      coordinates.address
      coordinates.orientation

  activeRole :=
    coordinates.role

  anchor_law := by

    cases coordinates.orientation <;>
      rfl

  nonAnchor_order := by

    cases coordinates.orientation with

    | cw =>
        exact
          Or.inl
            ⟨rfl, rfl⟩

    | ccw =>
        exact
          Or.inr
            ⟨rfl, rfl⟩


/--
The orientation recovered from a canonical clockwise frame
is clockwise.
-/
@[simp]
theorem orientationOf_operationOf_cw
    (address : Fano.Point)
    (role : TriadicRole) :

    orientationOf
        (
          operationOf
            {
              address := address
              role := role
              orientation := Orientation.cw
            }
        ) =

      Orientation.cw := by

  simp [
    orientationOf,
    operationOf,
    framePoint
  ]


/--
The orientation recovered from a canonical
counterclockwise frame is counterclockwise.
-/
@[simp]
theorem orientationOf_operationOf_ccw
    (address : Fano.Point)
    (role : TriadicRole) :

    orientationOf
        (
          operationOf
            {
              address := address
              role := role
              orientation := Orientation.ccw
            }
        ) =

      Orientation.ccw := by

  have hne :

      completionPoint address ≠
        successorPoint address :=

    (
      successor_ne_completion
        address
    ).symm

  simp [
    orientationOf,
    operationOf,
    framePoint,
    hne
  ]


/--
Extracting coordinates from a canonically constructed
operation returns the original coordinates.
-/
@[simp]
theorem coordinatesOf_operationOf
    (coordinates :
      AdmissibleOperation.Operation) :

    coordinatesOf
        (operationOf coordinates) =
      coordinates := by

  cases coordinates with
  | mk address role orientation =>

      cases orientation with

      | cw =>
          apply AdmissibleOperation.ext

          · rfl

          · rfl

          · exact
              orientationOf_operationOf_cw
                address
                role

      | ccw =>
          apply AdmissibleOperation.ext

          · rfl

          · rfl

          · exact
              orientationOf_operationOf_ccw
                address
                role


/--
Constructing an operation from its extracted coordinates
returns the original lawful framed operation.
-/
@[simp]
theorem operationOf_coordinatesOf
    (operation : LawfulFramedOperation) :

    operationOf
        (coordinatesOf operation) =
      operation := by

  apply
    LawfulFramedOperation.ext

  · rfl

  · symm

    exact
      frame_eq_framePoint
        operation

  · rfl


/--
Lawful framed operations are equivalent to the 42
admissible coordinate normal forms.
-/
noncomputable def normalFormEquiv :

    LawfulFramedOperation ≃
      AdmissibleOperation.Operation where

  toFun :=
    coordinatesOf

  invFun :=
    operationOf

  left_inv :=
    operationOf_coordinatesOf

  right_inv :=
    coordinatesOf_operationOf


/-
## Uniqueness and cardinality
-/

/--
The extracted normal form is injective.
-/
theorem coordinatesOf_injective :

    Function.Injective coordinatesOf := by

  intro left right hequal

  have hconstructed :=
    congrArg operationOf hequal

  simpa using hconstructed


/--
Every admissible coordinate triple is realized by one
lawful framed operation.
-/
theorem coordinatesOf_surjective :

    Function.Surjective coordinatesOf := by

  intro coordinates

  exact
    ⟨
      operationOf coordinates,
      coordinatesOf_operationOf coordinates
    ⟩


/--
Every lawful framed operation has one unique admissible
coordinate normal form.
-/
theorem unique_normal_form
    (operation : LawfulFramedOperation) :

    ∃! coordinates :
        AdmissibleOperation.Operation,

      operationOf coordinates =
        operation := by

  refine
    ⟨
      coordinatesOf operation,
      operationOf_coordinatesOf operation,
      ?_
    ⟩

  intro coordinates hcoordinates

  have hnormal :=
    congrArg coordinatesOf
      hcoordinates

  simpa using hnormal


/--
The lawful framed-operation space is finite.
-/
noncomputable instance lawfulFramedOperationFintype :

    Fintype LawfulFramedOperation :=

  Fintype.ofEquiv
    AdmissibleOperation.Operation
    normalFormEquiv.symm


/--
There are exactly 42 lawful framed local operations.
-/
theorem lawful_operation_card :
    Fintype.card LawfulFramedOperation = 42 := by

  rw [Fintype.card_congr normalFormEquiv]

  exact AdmissibleOperation.operation_card


/--
The 42 lawful operations factor into the prime structural
coordinates 7, 3, and 2.
-/
theorem lawful_operation_card_prime_structure :
    Fintype.card LawfulFramedOperation = 7 * 3 * 2 := by

  rw [Fintype.card_congr normalFormEquiv]

  exact
    AdmissibleOperation.operation_card_eq_seven_times_three_times_two


end OperationNormalForm
