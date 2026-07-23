import KTLean.SevenForcingFanoFrameRotate
import KTLean.SevenForcingFanoFrameCanonicalBijection

/-!
# Transporting Seven-Point Completion to Canonical Positions

## Formal status

**Level 2 — Consequence of global triadic closure, a selected
noncollinear frame, and exact seven-point cardinality.**

A seven-point system is equivalent to the seven canonical positions

    first
    second
    lineThird
    external
    firstExternalThird
    secondExternalThird
    lineThirdExternalThird.

This module transports the ambient completion operation across that
equivalence, producing a Steiner triple system directly on
`CanonicalPosition`.

The transported operation contains no new assumption and no chosen
table. It is exactly the original completion operation expressed in
canonical coordinates.

The subsequent module will prove that this transported operation has
the forced Fano completion table.
-/

namespace SevenForcingFanoFrameCanonicalTransport

noncomputable section

universe u

open SevenForcingFanoFrame
open SevenForcingFanoFrameCanonicalInjective
open SevenForcingFanoFrameCanonicalBijection

variable {Point : Type u}
variable [Fintype Point]
variable [DecidableEq Point]

/--
The canonical equivalence associated with a seven-point frame.
-/
abbrev canonicalEquiv
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    CanonicalPosition ≃ Point :=

  canonicalPositionEquivPoint
    frame
    hCard

/--
The ambient completion operation transported to the seven canonical
frame positions.
-/
def transportedComplete
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPosition secondPosition : CanonicalPosition) :
    CanonicalPosition :=

  (canonicalEquiv frame hCard).symm
    (
      S.complete
        (canonicalEquiv frame hCard firstPosition)
        (canonicalEquiv frame hCard secondPosition)
    )

/--
Transporting a canonical completion back to the ambient carrier gives
the original ambient completion.
-/
@[simp]
theorem canonicalEquiv_transportedComplete
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPosition secondPosition : CanonicalPosition) :
    canonicalEquiv frame hCard
        (
          transportedComplete
            frame
            hCard
            firstPosition
            secondPosition
        ) =
      S.complete
        (canonicalEquiv frame hCard firstPosition)
        (canonicalEquiv frame hCard secondPosition) := by

  exact
    (canonicalEquiv frame hCard).apply_symm_apply
      (
        S.complete
          (canonicalEquiv frame hCard firstPosition)
          (canonicalEquiv frame hCard secondPosition)
      )

/--
The transported operation is idempotent.
-/
theorem transportedComplete_self
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (position : CanonicalPosition) :
    transportedComplete
        frame
        hCard
        position
        position =
      position := by

  apply
    (canonicalEquiv frame hCard).injective

  rw [canonicalEquiv_transportedComplete]

  exact
    S.complete_self
      (canonicalEquiv frame hCard position)

/--
The transported operation is commutative.
-/
theorem transportedComplete_comm
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPosition secondPosition : CanonicalPosition) :
    transportedComplete
        frame
        hCard
        firstPosition
        secondPosition =
      transportedComplete
        frame
        hCard
        secondPosition
        firstPosition := by

  apply
    (canonicalEquiv frame hCard).injective

  rw [
    canonicalEquiv_transportedComplete,
    canonicalEquiv_transportedComplete
  ]

  exact
    S.complete_comm
      (canonicalEquiv frame hCard firstPosition)
      (canonicalEquiv frame hCard secondPosition)

/--
The transported operation satisfies Steiner recovery.
-/
theorem transportedComplete_left
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPosition secondPosition : CanonicalPosition) :
    transportedComplete
        frame
        hCard
        firstPosition
        (
          transportedComplete
            frame
            hCard
            firstPosition
            secondPosition
        ) =
      secondPosition := by

  apply
    (canonicalEquiv frame hCard).injective

  rw [
    canonicalEquiv_transportedComplete,
    canonicalEquiv_transportedComplete
  ]

  exact
    S.complete_left
      (canonicalEquiv frame hCard firstPosition)
      (canonicalEquiv frame hCard secondPosition)

/--
The ambient seven-point closure geometry, expressed as a Steiner
triple system on the canonical-position carrier.
-/
def canonicalSystem
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    Steiner.TripleSystem CanonicalPosition where

  complete :=
    transportedComplete
      frame
      hCard

  complete_self :=
    transportedComplete_self
      frame
      hCard

  complete_comm :=
    transportedComplete_comm
      frame
      hCard

  complete_left :=
    transportedComplete_left
      frame
      hCard

/--
The completion operation of the transported canonical system is
definitionally the transported completion operation.
-/
@[simp]
theorem canonicalSystem_complete
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPosition secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        firstPosition
        secondPosition =
      transportedComplete
        frame
        hCard
        firstPosition
        secondPosition := by

  rfl

/--
The canonical-position equivalence preserves completion.
-/
theorem canonicalEquiv_preserves_complete
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPosition secondPosition : CanonicalPosition) :
    canonicalEquiv frame hCard
        (
          (canonicalSystem frame hCard).complete
            firstPosition
            secondPosition
        ) =
      S.complete
        (canonicalEquiv frame hCard firstPosition)
        (canonicalEquiv frame hCard secondPosition) := by

  exact
    canonicalEquiv_transportedComplete
      frame
      hCard
      firstPosition
      secondPosition

/--
The concrete map `pointAt` preserves the transported canonical
completion operation.
-/
theorem pointAt_preserves_complete
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPosition secondPosition : CanonicalPosition) :
    pointAt frame
        (
          (canonicalSystem frame hCard).complete
            firstPosition
            secondPosition
        ) =
      S.complete
        (pointAt frame firstPosition)
        (pointAt frame secondPosition) := by

  simpa only [
    canonicalEquiv,
    canonicalPositionEquivPoint_apply
  ] using
    canonicalEquiv_preserves_complete
      frame
      hCard
      firstPosition
      secondPosition

end

end SevenForcingFanoFrameCanonicalTransport

#check SevenForcingFanoFrameCanonicalTransport.transportedComplete
#check SevenForcingFanoFrameCanonicalTransport.canonicalEquiv_transportedComplete
#check SevenForcingFanoFrameCanonicalTransport.transportedComplete_self
#check SevenForcingFanoFrameCanonicalTransport.transportedComplete_comm
#check SevenForcingFanoFrameCanonicalTransport.transportedComplete_left
#check SevenForcingFanoFrameCanonicalTransport.canonicalSystem
#check SevenForcingFanoFrameCanonicalTransport.canonicalEquiv_preserves_complete
#check SevenForcingFanoFrameCanonicalTransport.pointAt_preserves_complete
