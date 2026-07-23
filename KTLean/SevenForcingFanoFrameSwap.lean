import KTLean.SevenForcingFanoFrameForcedCompletion

/-!
# Swapping a Noncollinear Fano Frame

## Formal status

**Level 2 — Consequence of global triadic closure, a selected
noncollinear frame, and exact seven-point cardinality.**

Interchanging the first two points of a noncollinear frame preserves
the generated line and the external point.

Applying the previously forced cross-line completion to the swapped
frame yields a second forced Fano line:

    complete second firstExternalThird
      =
    lineThirdExternalThird.

Commutativity and Steiner recovery provide all orientations of this
line.
-/

namespace SevenForcingFanoFrameSwap

noncomputable section

universe u

open SevenForcingFanoFrame
open SevenForcingFanoFrameGenerated

section SwapDefinitions

variable {Point : Type u}
variable [DecidableEq Point]

/--
Swap the first two selected points of a noncollinear frame.
-/
def swap
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame S :=

  ⟨
    (
      frame.second,
      frame.first,
      frame.external
    ),
    by
      constructor

      · exact Ne.symm frame.first_ne_second

      · simpa only [
          S.block_comm
            frame.second
            frame.first
        ] using
          frame.external_not_mem_block
  ⟩

/--
The first point of the swapped frame is the original second point.
-/
@[simp]
theorem swap_first
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    (swap frame).first =
      frame.second := by

  rfl

/--
The second point of the swapped frame is the original first point.
-/
@[simp]
theorem swap_second
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    (swap frame).second =
      frame.first := by

  rfl

/--
The external point is unchanged by swapping.
-/
@[simp]
theorem swap_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    (swap frame).external =
      frame.external := by

  rfl

/--
The third point on the original generated line is unchanged by
swapping its first two points.
-/
@[simp]
theorem swap_lineThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    (swap frame).lineThird =
      frame.lineThird := by

  change
    S.complete frame.second frame.first =
      S.complete frame.first frame.second

  exact
    S.complete_comm
      frame.second
      frame.first

/--
The first external completion of the swapped frame is the original
second external completion.
-/
@[simp]
theorem swap_firstExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird (swap frame) =
      Frame.secondExternalThird frame := by

  rfl

/--
The second external completion of the swapped frame is the original
first external completion.
-/
@[simp]
theorem swap_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.secondExternalThird (swap frame) =
      Frame.firstExternalThird frame := by

  rfl

/--
The line-third external completion is unchanged by swapping.
-/
@[simp]
theorem swap_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.lineThirdExternalThird (swap frame) =
      Frame.lineThirdExternalThird frame := by

  unfold Frame.lineThirdExternalThird

  rw [swap_lineThird, swap_external]

end SwapDefinitions

section ForcedSecondCrossLine

variable {Point : Type u}
variable [Fintype Point]
variable [DecidableEq Point]

/--
The second forced cross-line completion:

    complete second firstExternalThird
      =
    lineThirdExternalThird.
-/
theorem Frame.complete_second_firstExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        frame.second
        (Frame.firstExternalThird frame) =
      Frame.lineThirdExternalThird frame := by

  have hswap :=
    SevenForcingFanoFrameForcedCompletion.Frame.complete_first_secondExternalThird
      (frame := swap frame)
      hCard

  simpa only [
    swap_first,
    swap_secondExternalThird,
    swap_lineThirdExternalThird
  ] using hswap

/--
The symmetric orientation of the second forced cross-line.
-/
theorem Frame.complete_firstExternalThird_second
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        (Frame.firstExternalThird frame)
        frame.second =
      Frame.lineThirdExternalThird frame := by

  calc
    S.complete
        (Frame.firstExternalThird frame)
        frame.second =
        S.complete
          frame.second
          (Frame.firstExternalThird frame) := by
      exact
        S.complete_comm
          (Frame.firstExternalThird frame)
          frame.second

    _ =
        Frame.lineThirdExternalThird frame := by
      exact
        Frame.complete_second_firstExternalThird
          frame
          hCard

/--
Completing `second` with `lineThirdExternalThird` recovers
`firstExternalThird`.
-/
theorem Frame.complete_second_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        frame.second
        (Frame.lineThirdExternalThird frame) =
      Frame.firstExternalThird frame := by

  rw [
    ← Frame.complete_second_firstExternalThird
      frame
      hCard
  ]

  exact
    S.complete_left
      frame.second
      (Frame.firstExternalThird frame)

/--
Completing the two generated points of the second forced cross-line
recovers `second`.
-/
theorem Frame.complete_firstExternalThird_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        (Frame.firstExternalThird frame)
        (Frame.lineThirdExternalThird frame) =
      frame.second := by

  rw [
    ← Frame.complete_second_firstExternalThird
      frame
      hCard
  ]

  exact
    (
      S.block_recovery
        frame.second
        (Frame.firstExternalThird frame)
    ).2

end ForcedSecondCrossLine

end

end SevenForcingFanoFrameSwap

#check SevenForcingFanoFrameSwap.swap
#check SevenForcingFanoFrameSwap.swap_lineThird
#check SevenForcingFanoFrameSwap.Frame.complete_second_firstExternalThird
#check SevenForcingFanoFrameSwap.Frame.complete_firstExternalThird_second
#check SevenForcingFanoFrameSwap.Frame.complete_second_lineThirdExternalThird
#check SevenForcingFanoFrameSwap.Frame.complete_firstExternalThird_lineThirdExternalThird
