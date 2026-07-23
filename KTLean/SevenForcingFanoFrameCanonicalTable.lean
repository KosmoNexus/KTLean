import KTLean.SevenForcingFanoFrameCanonicalTransport

/-!
# The Forced Canonical Completion Table

## Formal status

**Level 2 — Consequence of global triadic closure, a selected
noncollinear frame, and exact seven-point cardinality.**

The seven canonical positions are written

    x = first
    y = second
    z = lineThird
    p = external
    a = firstExternalThird
    b = secondExternalThird
    c = lineThirdExternalThird.

The seven forced lines are

    {x,y,z}
    {x,p,a}
    {y,p,b}
    {z,p,c}
    {x,b,c}
    {y,a,c}
    {z,a,b}.

This module records the resulting complete operation table and proves
that the transported abstract closure operation agrees with it on
every pair of canonical positions.

The proof is organized row by row. Each row explicitly identifies the
Steiner line or recovery theorem responsible for its seven entries.
-/

namespace SevenForcingFanoFrameCanonicalTable

noncomputable section

universe u

open SevenForcingFanoFrame
open SevenForcingFanoFrameGenerated
open SevenForcingFanoFrameCanonicalInjective
open SevenForcingFanoFrameCanonicalTransport

/--
The completion table forced on the seven canonical frame positions.

The constructor order is

    first,
    second,
    lineThird,
    external,
    firstExternalThird,
    secondExternalThird,
    lineThirdExternalThird.
-/
def canonicalCompletionTable :
    CanonicalPosition →
      CanonicalPosition →
        CanonicalPosition

  | CanonicalPosition.first,
      CanonicalPosition.first =>
      CanonicalPosition.first

  | CanonicalPosition.first,
      CanonicalPosition.second =>
      CanonicalPosition.lineThird

  | CanonicalPosition.first,
      CanonicalPosition.lineThird =>
      CanonicalPosition.second

  | CanonicalPosition.first,
      CanonicalPosition.external =>
      CanonicalPosition.firstExternalThird

  | CanonicalPosition.first,
      CanonicalPosition.firstExternalThird =>
      CanonicalPosition.external

  | CanonicalPosition.first,
      CanonicalPosition.secondExternalThird =>
      CanonicalPosition.lineThirdExternalThird

  | CanonicalPosition.first,
      CanonicalPosition.lineThirdExternalThird =>
      CanonicalPosition.secondExternalThird

  | CanonicalPosition.second,
      CanonicalPosition.first =>
      CanonicalPosition.lineThird

  | CanonicalPosition.second,
      CanonicalPosition.second =>
      CanonicalPosition.second

  | CanonicalPosition.second,
      CanonicalPosition.lineThird =>
      CanonicalPosition.first

  | CanonicalPosition.second,
      CanonicalPosition.external =>
      CanonicalPosition.secondExternalThird

  | CanonicalPosition.second,
      CanonicalPosition.firstExternalThird =>
      CanonicalPosition.lineThirdExternalThird

  | CanonicalPosition.second,
      CanonicalPosition.secondExternalThird =>
      CanonicalPosition.external

  | CanonicalPosition.second,
      CanonicalPosition.lineThirdExternalThird =>
      CanonicalPosition.firstExternalThird

  | CanonicalPosition.lineThird,
      CanonicalPosition.first =>
      CanonicalPosition.second

  | CanonicalPosition.lineThird,
      CanonicalPosition.second =>
      CanonicalPosition.first

  | CanonicalPosition.lineThird,
      CanonicalPosition.lineThird =>
      CanonicalPosition.lineThird

  | CanonicalPosition.lineThird,
      CanonicalPosition.external =>
      CanonicalPosition.lineThirdExternalThird

  | CanonicalPosition.lineThird,
      CanonicalPosition.firstExternalThird =>
      CanonicalPosition.secondExternalThird

  | CanonicalPosition.lineThird,
      CanonicalPosition.secondExternalThird =>
      CanonicalPosition.firstExternalThird

  | CanonicalPosition.lineThird,
      CanonicalPosition.lineThirdExternalThird =>
      CanonicalPosition.external

  | CanonicalPosition.external,
      CanonicalPosition.first =>
      CanonicalPosition.firstExternalThird

  | CanonicalPosition.external,
      CanonicalPosition.second =>
      CanonicalPosition.secondExternalThird

  | CanonicalPosition.external,
      CanonicalPosition.lineThird =>
      CanonicalPosition.lineThirdExternalThird

  | CanonicalPosition.external,
      CanonicalPosition.external =>
      CanonicalPosition.external

  | CanonicalPosition.external,
      CanonicalPosition.firstExternalThird =>
      CanonicalPosition.first

  | CanonicalPosition.external,
      CanonicalPosition.secondExternalThird =>
      CanonicalPosition.second

  | CanonicalPosition.external,
      CanonicalPosition.lineThirdExternalThird =>
      CanonicalPosition.lineThird

  | CanonicalPosition.firstExternalThird,
      CanonicalPosition.first =>
      CanonicalPosition.external

  | CanonicalPosition.firstExternalThird,
      CanonicalPosition.second =>
      CanonicalPosition.lineThirdExternalThird

  | CanonicalPosition.firstExternalThird,
      CanonicalPosition.lineThird =>
      CanonicalPosition.secondExternalThird

  | CanonicalPosition.firstExternalThird,
      CanonicalPosition.external =>
      CanonicalPosition.first

  | CanonicalPosition.firstExternalThird,
      CanonicalPosition.firstExternalThird =>
      CanonicalPosition.firstExternalThird

  | CanonicalPosition.firstExternalThird,
      CanonicalPosition.secondExternalThird =>
      CanonicalPosition.lineThird

  | CanonicalPosition.firstExternalThird,
      CanonicalPosition.lineThirdExternalThird =>
      CanonicalPosition.second

  | CanonicalPosition.secondExternalThird,
      CanonicalPosition.first =>
      CanonicalPosition.lineThirdExternalThird

  | CanonicalPosition.secondExternalThird,
      CanonicalPosition.second =>
      CanonicalPosition.external

  | CanonicalPosition.secondExternalThird,
      CanonicalPosition.lineThird =>
      CanonicalPosition.firstExternalThird

  | CanonicalPosition.secondExternalThird,
      CanonicalPosition.external =>
      CanonicalPosition.second

  | CanonicalPosition.secondExternalThird,
      CanonicalPosition.firstExternalThird =>
      CanonicalPosition.lineThird

  | CanonicalPosition.secondExternalThird,
      CanonicalPosition.secondExternalThird =>
      CanonicalPosition.secondExternalThird

  | CanonicalPosition.secondExternalThird,
      CanonicalPosition.lineThirdExternalThird =>
      CanonicalPosition.first

  | CanonicalPosition.lineThirdExternalThird,
      CanonicalPosition.first =>
      CanonicalPosition.secondExternalThird

  | CanonicalPosition.lineThirdExternalThird,
      CanonicalPosition.second =>
      CanonicalPosition.firstExternalThird

  | CanonicalPosition.lineThirdExternalThird,
      CanonicalPosition.lineThird =>
      CanonicalPosition.external

  | CanonicalPosition.lineThirdExternalThird,
      CanonicalPosition.external =>
      CanonicalPosition.lineThird

  | CanonicalPosition.lineThirdExternalThird,
      CanonicalPosition.firstExternalThird =>
      CanonicalPosition.second

  | CanonicalPosition.lineThirdExternalThird,
      CanonicalPosition.secondExternalThird =>
      CanonicalPosition.first

  | CanonicalPosition.lineThirdExternalThird,
      CanonicalPosition.lineThirdExternalThird =>
      CanonicalPosition.lineThirdExternalThird

variable {Point : Type u}
variable [Fintype Point]
variable [DecidableEq Point]

/--
The row of the canonical table beginning at `first`.
-/
theorem canonical_row_first
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        CanonicalPosition.first
        secondPosition =
      canonicalCompletionTable
        CanonicalPosition.first
        secondPosition := by

  apply pointAt_injective frame

  rw [
    pointAt_preserves_complete
      frame
      hCard
      CanonicalPosition.first
      secondPosition
  ]

  cases secondPosition

  · simp only [pointAt, canonicalCompletionTable]
    exact S.complete_self frame.first

  · rfl

  · simp only [pointAt, canonicalCompletionTable]
    exact
      S.complete_left
        frame.first
        frame.second

  · rfl

  · simp only [pointAt, canonicalCompletionTable]
    exact
      Frame.complete_first_firstExternalThird
        frame

  · simp only [pointAt, canonicalCompletionTable]
    exact
      SevenForcingFanoFrameForcedCompletion.Frame.complete_first_secondExternalThird
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]
    exact
      SevenForcingFanoFrameForcedCompletion.Frame.complete_first_lineThirdExternalThird
        frame
        hCard

/--
The row of the canonical table beginning at `second`.
-/
theorem canonical_row_second
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        CanonicalPosition.second
        secondPosition =
      canonicalCompletionTable
        CanonicalPosition.second
        secondPosition := by

  apply pointAt_injective frame

  rw [
    pointAt_preserves_complete
      frame
      hCard
      CanonicalPosition.second
      secondPosition
  ]

  cases secondPosition

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete frame.second frame.first =
          S.complete frame.first frame.second := by
        exact
          S.complete_comm
            frame.second
            frame.first

      _ = frame.lineThird := by
        rfl

  · simp only [pointAt, canonicalCompletionTable]
    exact S.complete_self frame.second

  · simp only [pointAt, canonicalCompletionTable]

    exact
      (
        S.block_recovery
          frame.first
          frame.second
      ).2

  · rfl

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameSwap.Frame.complete_second_firstExternalThird
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    exact
      Frame.complete_second_secondExternalThird
        frame

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameSwap.Frame.complete_second_lineThirdExternalThird
        frame
        hCard

/--
The row of the canonical table beginning at `lineThird`.
-/
theorem canonical_row_lineThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        CanonicalPosition.lineThird
        secondPosition =
      canonicalCompletionTable
        CanonicalPosition.lineThird
        secondPosition := by

  apply pointAt_injective frame

  rw [
    pointAt_preserves_complete
      frame
      hCard
      CanonicalPosition.lineThird
      secondPosition
  ]

  cases secondPosition

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete frame.lineThird frame.first =
          S.complete frame.first frame.lineThird := by
        exact
          S.complete_comm
            frame.lineThird
            frame.first

      _ = frame.second := by
        exact
          S.complete_left
            frame.first
            frame.second

  · simp only [pointAt, canonicalCompletionTable]

    exact
      S.complete_right
        frame.first
        frame.second

  · simp only [pointAt, canonicalCompletionTable]
    exact S.complete_self frame.lineThird

  · rfl

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameRotate.Frame.complete_lineThird_firstExternalThird
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameRotate.Frame.complete_lineThird_secondExternalThird
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    exact
      Frame.complete_lineThird_lineThirdExternalThird
        frame

/--
The row of the canonical table beginning at `external`.
-/
theorem canonical_row_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        CanonicalPosition.external
        secondPosition =
      canonicalCompletionTable
        CanonicalPosition.external
        secondPosition := by

  apply pointAt_injective frame

  rw [
    pointAt_preserves_complete
      frame
      hCard
      CanonicalPosition.external
      secondPosition
  ]

  cases secondPosition

  · simp only [pointAt, canonicalCompletionTable]

    exact
      S.complete_comm
        frame.external
        frame.first

  · simp only [pointAt, canonicalCompletionTable]

    exact
      S.complete_comm
        frame.external
        frame.second

  · simp only [pointAt, canonicalCompletionTable]

    exact
      S.complete_comm
        frame.external
        frame.lineThird

  · simp only [pointAt, canonicalCompletionTable]
    exact S.complete_self frame.external

  · simp only [pointAt, canonicalCompletionTable]

    exact
      Frame.complete_external_firstExternalThird
        frame

  · simp only [pointAt, canonicalCompletionTable]

    exact
      Frame.complete_external_secondExternalThird
        frame

  · simp only [pointAt, canonicalCompletionTable]

    exact
      Frame.complete_external_lineThirdExternalThird
        frame

/--
The row of the canonical table beginning at `firstExternalThird`.
-/
theorem canonical_row_firstExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        CanonicalPosition.firstExternalThird
        secondPosition =
      canonicalCompletionTable
        CanonicalPosition.firstExternalThird
        secondPosition := by

  apply pointAt_injective frame

  rw [
    pointAt_preserves_complete
      frame
      hCard
      CanonicalPosition.firstExternalThird
      secondPosition
  ]

  cases secondPosition

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.firstExternalThird frame)
          frame.first =
          S.complete
            frame.first
            (Frame.firstExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.firstExternalThird frame)
            frame.first

      _ = frame.external := by
        exact
          Frame.complete_first_firstExternalThird
            frame

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameSwap.Frame.complete_firstExternalThird_second
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameRotate.Frame.complete_firstExternalThird_lineThird
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.firstExternalThird frame)
          frame.external =
          S.complete
            frame.external
            (Frame.firstExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.firstExternalThird frame)
            frame.external

      _ = frame.first := by
        exact
          Frame.complete_external_firstExternalThird
            frame

  · simp only [pointAt, canonicalCompletionTable]

    exact
      S.complete_self
        (Frame.firstExternalThird frame)

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameRotate.Frame.complete_firstExternalThird_secondExternalThird
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameSwap.Frame.complete_firstExternalThird_lineThirdExternalThird
        frame
        hCard

/--
The row of the canonical table beginning at `secondExternalThird`.
-/
theorem canonical_row_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        CanonicalPosition.secondExternalThird
        secondPosition =
      canonicalCompletionTable
        CanonicalPosition.secondExternalThird
        secondPosition := by

  apply pointAt_injective frame

  rw [
    pointAt_preserves_complete
      frame
      hCard
      CanonicalPosition.secondExternalThird
      secondPosition
  ]

  cases secondPosition

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameForcedCompletion.Frame.complete_secondExternalThird_first
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.secondExternalThird frame)
          frame.second =
          S.complete
            frame.second
            (Frame.secondExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.secondExternalThird frame)
            frame.second

      _ = frame.external := by
        exact
          Frame.complete_second_secondExternalThird
            frame

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.secondExternalThird frame)
          frame.lineThird =
          S.complete
            frame.lineThird
            (Frame.secondExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.secondExternalThird frame)
            frame.lineThird

      _ =
          Frame.firstExternalThird frame := by
        exact
          SevenForcingFanoFrameRotate.Frame.complete_lineThird_secondExternalThird
            frame
            hCard

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.secondExternalThird frame)
          frame.external =
          S.complete
            frame.external
            (Frame.secondExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.secondExternalThird frame)
            frame.external

      _ = frame.second := by
        exact
          Frame.complete_external_secondExternalThird
            frame

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.secondExternalThird frame)
          (Frame.firstExternalThird frame) =
          S.complete
            (Frame.firstExternalThird frame)
            (Frame.secondExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.secondExternalThird frame)
            (Frame.firstExternalThird frame)

      _ = frame.lineThird := by
        exact
          SevenForcingFanoFrameRotate.Frame.complete_firstExternalThird_secondExternalThird
            frame
            hCard

  · simp only [pointAt, canonicalCompletionTable]

    exact
      S.complete_self
        (Frame.secondExternalThird frame)

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameForcedCompletion.Frame.complete_secondExternalThird_lineThirdExternalThird
        frame
        hCard

/--
The row of the canonical table beginning at
`lineThirdExternalThird`.
-/
theorem canonical_row_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        CanonicalPosition.lineThirdExternalThird
        secondPosition =
      canonicalCompletionTable
        CanonicalPosition.lineThirdExternalThird
        secondPosition := by

  apply pointAt_injective frame

  rw [
    pointAt_preserves_complete
      frame
      hCard
      CanonicalPosition.lineThirdExternalThird
      secondPosition
  ]

  cases secondPosition

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameForcedCompletion.Frame.complete_lineThirdExternalThird_first
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.lineThirdExternalThird frame)
          frame.second =
          S.complete
            frame.second
            (Frame.lineThirdExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.lineThirdExternalThird frame)
            frame.second

      _ =
          Frame.firstExternalThird frame := by
        exact
          SevenForcingFanoFrameSwap.Frame.complete_second_lineThirdExternalThird
            frame
            hCard

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.lineThirdExternalThird frame)
          frame.lineThird =
          S.complete
            frame.lineThird
            (Frame.lineThirdExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.lineThirdExternalThird frame)
            frame.lineThird

      _ = frame.external := by
        exact
          Frame.complete_lineThird_lineThirdExternalThird
            frame

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.lineThirdExternalThird frame)
          frame.external =
          S.complete
            frame.external
            (Frame.lineThirdExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.lineThirdExternalThird frame)
            frame.external

      _ = frame.lineThird := by
        exact
          Frame.complete_external_lineThirdExternalThird
            frame

  · simp only [pointAt, canonicalCompletionTable]

    calc
      S.complete
          (Frame.lineThirdExternalThird frame)
          (Frame.firstExternalThird frame) =
          S.complete
            (Frame.firstExternalThird frame)
            (Frame.lineThirdExternalThird frame) := by
        exact
          S.complete_comm
            (Frame.lineThirdExternalThird frame)
            (Frame.firstExternalThird frame)

      _ = frame.second := by
        exact
          SevenForcingFanoFrameSwap.Frame.complete_firstExternalThird_lineThirdExternalThird
            frame
            hCard

  · simp only [pointAt, canonicalCompletionTable]

    exact
      SevenForcingFanoFrameForcedCompletion.Frame.complete_lineThirdExternalThird_secondExternalThird
        frame
        hCard

  · simp only [pointAt, canonicalCompletionTable]

    exact
      S.complete_self
        (Frame.lineThirdExternalThird frame)

/--
The transported completion operation agrees with the forced canonical
completion table on every ordered pair.
-/
theorem canonicalSystem_complete_eq_table
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPosition secondPosition : CanonicalPosition) :
    (canonicalSystem frame hCard).complete
        firstPosition
        secondPosition =
      canonicalCompletionTable
        firstPosition
        secondPosition := by

  cases firstPosition

  · exact
      canonical_row_first
        frame
        hCard
        secondPosition

  · exact
      canonical_row_second
        frame
        hCard
        secondPosition

  · exact
      canonical_row_lineThird
        frame
        hCard
        secondPosition

  · exact
      canonical_row_external
        frame
        hCard
        secondPosition

  · exact
      canonical_row_firstExternalThird
        frame
        hCard
        secondPosition

  · exact
      canonical_row_secondExternalThird
        frame
        hCard
        secondPosition

  · exact
      canonical_row_lineThirdExternalThird
        frame
        hCard
        secondPosition

/--
The full canonical system is completely determined by the explicit
forced table.
-/
theorem canonicalSystem_complete_ext
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    (canonicalSystem frame hCard).complete =
      canonicalCompletionTable := by

  funext firstPosition secondPosition

  exact
    canonicalSystem_complete_eq_table
      frame
      hCard
      firstPosition
      secondPosition

/--
The forced canonical table is idempotent.
-/
theorem canonicalCompletionTable_self
    (position : CanonicalPosition) :
    canonicalCompletionTable
        position
        position =
      position := by

  cases position <;>
    rfl

/--
The forced canonical table is commutative.
-/
theorem canonicalCompletionTable_comm
    (firstPosition secondPosition : CanonicalPosition) :
    canonicalCompletionTable
        firstPosition
        secondPosition =
      canonicalCompletionTable
        secondPosition
        firstPosition := by

  cases firstPosition <;>
    cases secondPosition <;>
    rfl

/--
The forced canonical table satisfies Steiner recovery.
-/
theorem canonicalCompletionTable_left
    (firstPosition secondPosition : CanonicalPosition) :
    canonicalCompletionTable
        firstPosition
        (
          canonicalCompletionTable
            firstPosition
            secondPosition
        ) =
      secondPosition := by

  cases firstPosition <;>
    cases secondPosition <;>
    rfl

/--
The explicitly forced canonical table itself forms a Steiner triple
system.
-/
def forcedCanonicalSystem :
    Steiner.TripleSystem CanonicalPosition where

  complete :=
    canonicalCompletionTable

  complete_self :=
    canonicalCompletionTable_self

  complete_comm :=
    canonicalCompletionTable_comm

  complete_left :=
    canonicalCompletionTable_left

/--
The transported canonical system and the explicitly forced canonical
system have identical completion operations.
-/
theorem canonicalSystem_eq_forcedCanonicalSystem
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    canonicalSystem frame hCard =
      forcedCanonicalSystem := by

  cases hCanonical :
      canonicalSystem frame hCard with

  | mk canonicalComplete
      canonicalSelf
      canonicalComm
      canonicalLeft =>

      have hComplete :=
        canonicalSystem_complete_ext
          frame
          hCard

      rw [hCanonical] at hComplete

      unfold forcedCanonicalSystem

      cases hComplete

      rfl

end

end SevenForcingFanoFrameCanonicalTable

#check SevenForcingFanoFrameCanonicalTable.canonicalCompletionTable
#check SevenForcingFanoFrameCanonicalTable.canonical_row_first
#check SevenForcingFanoFrameCanonicalTable.canonical_row_second
#check SevenForcingFanoFrameCanonicalTable.canonical_row_lineThird
#check SevenForcingFanoFrameCanonicalTable.canonical_row_external
#check SevenForcingFanoFrameCanonicalTable.canonical_row_firstExternalThird
#check SevenForcingFanoFrameCanonicalTable.canonical_row_secondExternalThird
#check SevenForcingFanoFrameCanonicalTable.canonical_row_lineThirdExternalThird
#check SevenForcingFanoFrameCanonicalTable.canonicalSystem_complete_eq_table
#check SevenForcingFanoFrameCanonicalTable.canonicalSystem_complete_ext
#check SevenForcingFanoFrameCanonicalTable.canonicalCompletionTable_self
#check SevenForcingFanoFrameCanonicalTable.canonicalCompletionTable_comm
#check SevenForcingFanoFrameCanonicalTable.canonicalCompletionTable_left
#check SevenForcingFanoFrameCanonicalTable.forcedCanonicalSystem
#check SevenForcingFanoFrameCanonicalTable.canonicalSystem_eq_forcedCanonicalSystem
