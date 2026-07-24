import KTLean.GlyphSpectralSpecialFunctionOperations
import KTLean.GlyphSpectralFrobeniusBoundary
import KTLean.SpinorOrbit
import Mathlib.Tactic

/-!
# The Spinorial Frobenius Boundary Line

## Formal status

**Level 2 — Unified reconstruction of the six terminal glyph values
from the forced Frobenius orbit and its two-sheet orientation cover.**

## Developmental predecessor

`GlyphSpectralSpecialFunctionOperations`

The final six glyphs are not six unrelated exceptional integers. They
are the evaluations of one boundary line:

    boundary × Frobenius step × spinor sheet.

The forced Frobenius orbit has three steps:

    1, 2, 4.

The forced reversible orientation has two sheets:

    forward, reverse.

Their product gives the six terminal addresses:

    (1, forward), (1, reverse),
    (2, forward), (2, reverse),
    (4, forward), (4, reverse).

The existing boundary derivations identify their values as:

    21, 42,
    23, 46,
    147, 137.

The first two Frobenius rows display oriented doubling directly. At the
terminal stride, the two sheets bifurcate into the geometric closure
boundary `147` and the reversible projection boundary `137`.

This module also realizes the orientation carrier as a concrete spinor
system: one traversal reaches the partner sheet, while two traversals
return to the initial sheet.
-/

namespace GlyphSpectralSpinorialBoundary

open GlyphForcingOrientation
open GlyphSpectralBoundaryCombinatorics
open GlyphSpectralFrobeniusBoundary
open GlyphSpectralAlphaBoundary

/-
## The two-sheet spinor carrier
-/

/--
Exchange the two sheets of the boundary orientation cover.
-/
def boundarySheetFlip :
    ForcedOrientation →
      ForcedOrientation

  | .forward =>
      .reverse

  | .reverse =>
      .forward

/--
The sheet exchange is involutive.
-/
theorem boundarySheetFlip_involutive :
    Function.Involutive
      boundarySheetFlip := by

  intro orientation

  cases orientation <;>
    rfl

/--
The initial sheet differs from its partner.
-/
theorem forward_ne_boundary_partner :
    ForcedOrientation.forward ≠
      boundarySheetFlip
        ForcedOrientation.forward := by

  decide

/--
The two-sheet boundary carrier as a concrete spinor system.
-/
def boundarySpinorSystem :
    SpinorOrbit.System where

  State :=
    ForcedOrientation

  step :=
    boundarySheetFlip

  base :=
    .forward

  deck :=
    boundarySheetFlip

  deck_involutive :=
    boundarySheetFlip_involutive

  base_ne_deck :=
    forward_ne_boundary_partner

  step_deck_commute := by
    intro orientation
    cases orientation <;>
      rfl

/--
One sheet traversal is a spinorial half-closure.
-/
def boundaryHalfClosure :
    boundarySpinorSystem.HalfClosure where

  halfPeriod :=
    1

  positive := by
    decide

  reaches_deck := by
    rfl

/--
The boundary orientation is a genuine double cover:

* one traversal reaches the partner sheet;
* one traversal does not return to the base sheet;
* two traversals return to the base sheet.
-/
theorem boundary_spinor_double_cover :
    boundarySpinorSystem.ReachesDeckAt 1
      ∧
    ¬ boundarySpinorSystem.ReturnsAt 1
      ∧
    boundarySpinorSystem.ReturnsAt 2 := by

  have hSeparation :=
    SpinorOrbit.System.double_cover_separation
      boundaryHalfClosure

  exact
    ⟨
      by
        simpa [
          boundaryHalfClosure
        ] using
          hSeparation.1,
      by
        simpa [
          boundaryHalfClosure
        ] using
          hSeparation.2.1,
      by
        simpa [
          boundaryHalfClosure,
          SpinorOrbit.System.HalfClosure.fullPeriod
        ] using
          hSeparation.2.2
    ⟩

/-
## One boundary evaluator
-/

/--
Evaluate the terminal boundary line at one Frobenius step and one
spinor sheet.
-/
def spinorialBoundaryValue :
    FrobeniusOrbit.Step →
      ForcedOrientation →
        Nat

  | .one, .forward =>
      visiblePairCount

  | .one, .reverse =>
      orientedPairCount

  | .two, .forward =>
      frobeniusBoundaryPrime

  | .two, .reverse =>
      compositeResonance

  | .four, .forward =>
      sevenfoldClosureDepth

  | .four, .reverse =>
      usableProjectionChannels

/--
The first Frobenius step on the forward sheet yields `21`.
-/
@[simp]
theorem spinorialBoundaryValue_one_forward :
    spinorialBoundaryValue
        .one
        .forward =
      21 := by

  exact
    visiblePairCount_eq_twentyOne

/--
The first Frobenius step on the reverse sheet yields `42`.
-/
@[simp]
theorem spinorialBoundaryValue_one_reverse :
    spinorialBoundaryValue
        .one
        .reverse =
      42 := by

  exact
    orientedPairCount_eq_fortyTwo

/--
The middle Frobenius step on the forward sheet yields `23`.
-/
@[simp]
theorem spinorialBoundaryValue_two_forward :
    spinorialBoundaryValue
        .two
        .forward =
      23 := by

  exact
    frobeniusBoundaryPrime_eq_twentyThree

/--
The middle Frobenius step on the reverse sheet yields `46`.
-/
@[simp]
theorem spinorialBoundaryValue_two_reverse :
    spinorialBoundaryValue
        .two
        .reverse =
      46 := by

  exact
    compositeResonance_eq_fortySix

/--
The terminal Frobenius step on the forward sheet yields the geometric
closure boundary `147`.
-/
@[simp]
theorem spinorialBoundaryValue_four_forward :
    spinorialBoundaryValue
        .four
        .forward =
      147 := by

  exact
    sevenfoldClosureDepth_eq_oneFortySeven

/--
The terminal Frobenius step on the reverse sheet yields the reversible
projection boundary `137`.
-/
@[simp]
theorem spinorialBoundaryValue_four_reverse :
    spinorialBoundaryValue
        .four
        .reverse =
      137 := by

  exact
    usableProjectionChannels_eq_oneThirtySeven

/-
## The complete three-by-two boundary line
-/

/--
The six addresses of the terminal Frobenius boundary line.
-/
def spinorialBoundaryAddresses :
    List
      (
        FrobeniusOrbit.Step
          ×
        ForcedOrientation
      ) :=
  [
    (.one, .forward),
    (.one, .reverse),
    (.two, .forward),
    (.two, .reverse),
    (.four, .forward),
    (.four, .reverse)
  ]

/--
Evaluate all six boundary addresses in canonical order.
-/
def evaluatedSpinorialBoundaryLine :
    List Nat :=

  spinorialBoundaryAddresses.map
    (
      fun address =>
        spinorialBoundaryValue
          address.1
          address.2
    )

/--
The single boundary evaluator produces exactly the six terminal values.
-/
theorem evaluatedSpinorialBoundaryLine_eq :
    evaluatedSpinorialBoundaryLine =
      [
        21,
        42,
        23,
        46,
        147,
        137
      ] := by

  simp [
    evaluatedSpinorialBoundaryLine,
    spinorialBoundaryAddresses
  ]

/--
The first two Frobenius rows display the oriented double cover
arithmetically.
-/
theorem lower_boundary_rows_are_oriented_doubles :
    spinorialBoundaryValue
        .one
        .reverse =
      2 *
        spinorialBoundaryValue
          .one
          .forward
      ∧
    spinorialBoundaryValue
        .two
        .reverse =
      2 *
        spinorialBoundaryValue
          .two
          .forward := by

  norm_num

/--
At the terminal Frobenius step, the two sheets resolve into distinct
geometric and projection boundaries.
-/
theorem terminal_boundary_bifurcation :
    spinorialBoundaryValue
        .four
        .forward =
      147
      ∧
    spinorialBoundaryValue
        .four
        .reverse =
      137
      ∧
    spinorialBoundaryValue
        .four
        .forward ≠
      spinorialBoundaryValue
        .four
        .reverse := by

  norm_num

/-
## Canonical spectral registration
-/

/--
The canonical symbolic boundary block.
-/
def spinorialBoundaryBlock :
    List GlyphSpectrum.SpectralValue :=
  [
    .natural 21,
    .natural 42,
    .natural 23,
    .natural 46,
    .natural 147,
    .natural 137
  ]

/--
Convert the evaluated numerical boundary line into symbolic spectral
values.
-/
def evaluatedSpinorialBoundaryBlock :
    List GlyphSpectrum.SpectralValue :=

  evaluatedSpinorialBoundaryLine.map
    GlyphSpectrum.SpectralValue.natural

/--
The numerical evaluator and symbolic boundary block agree exactly.
-/
theorem evaluatedSpinorialBoundaryBlock_eq :
    evaluatedSpinorialBoundaryBlock =
      spinorialBoundaryBlock := by

  simp [
    evaluatedSpinorialBoundaryBlock,
    evaluatedSpinorialBoundaryLine_eq,
    spinorialBoundaryBlock
  ]

/--
Glyph positions 37 through 42 are exactly the spinorial Frobenius
boundary block.
-/
theorem registered_spinorial_boundary_block :
    (GlyphSpectrum.values.drop 36).take 6 =
      spinorialBoundaryBlock := by

  native_decide

/--
Capstone theorem.

The terminal glyph family is one three-by-two Frobenius–spinor boundary
line. The orientation carrier is a genuine double cover, its six
evaluations are exactly `21, 42, 23, 46, 147, 137`, the first two rows
show oriented doubling, the final row bifurcates into geometric and
projection closure, and the complete evaluator agrees with the
registered canonical boundary block.
-/
theorem spinorial_boundary_line_emerges :
    (
      boundarySpinorSystem.ReachesDeckAt 1
        ∧
      ¬ boundarySpinorSystem.ReturnsAt 1
        ∧
      boundarySpinorSystem.ReturnsAt 2
    )
      ∧
    evaluatedSpinorialBoundaryLine =
      [
        21,
        42,
        23,
        46,
        147,
        137
      ]
      ∧
    (
      spinorialBoundaryValue
          .one
          .reverse =
        2 *
          spinorialBoundaryValue
            .one
            .forward
        ∧
      spinorialBoundaryValue
          .two
          .reverse =
        2 *
          spinorialBoundaryValue
            .two
            .forward
    )
      ∧
    (
      spinorialBoundaryValue
          .four
          .forward =
        147
        ∧
      spinorialBoundaryValue
          .four
          .reverse =
        137
        ∧
      spinorialBoundaryValue
          .four
          .forward ≠
        spinorialBoundaryValue
          .four
          .reverse
    )
      ∧
    (GlyphSpectrum.values.drop 36).take 6 =
      spinorialBoundaryBlock := by

  exact
    ⟨
      boundary_spinor_double_cover,
      evaluatedSpinorialBoundaryLine_eq,
      lower_boundary_rows_are_oriented_doubles,
      terminal_boundary_bifurcation,
      registered_spinorial_boundary_block
    ⟩

end GlyphSpectralSpinorialBoundary

#check GlyphSpectralSpinorialBoundary.boundarySheetFlip
#check GlyphSpectralSpinorialBoundary.boundarySpinorSystem
#check GlyphSpectralSpinorialBoundary.boundaryHalfClosure
#check GlyphSpectralSpinorialBoundary.boundary_spinor_double_cover
#check GlyphSpectralSpinorialBoundary.spinorialBoundaryValue
#check GlyphSpectralSpinorialBoundary.evaluatedSpinorialBoundaryLine
#check GlyphSpectralSpinorialBoundary.evaluatedSpinorialBoundaryLine_eq
#check GlyphSpectralSpinorialBoundary.lower_boundary_rows_are_oriented_doubles
#check GlyphSpectralSpinorialBoundary.terminal_boundary_bifurcation
#check GlyphSpectralSpinorialBoundary.spinorialBoundaryBlock
#check GlyphSpectralSpinorialBoundary.evaluatedSpinorialBoundaryBlock_eq
#check GlyphSpectralSpinorialBoundary.registered_spinorial_boundary_block
#check GlyphSpectralSpinorialBoundary.spinorial_boundary_line_emerges
