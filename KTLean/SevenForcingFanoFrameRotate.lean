import KTLean.SevenForcingFanoFrameSwap

/-!
# Rotating a Noncollinear Fano Frame

## Formal status

**Level 2 — Consequence of global triadic closure, a selected
noncollinear frame, and exact seven-point cardinality.**

For a frame

    x = first
    y = second
    z = complete x y
    p = external,

the cyclically rotated frame is

    first    := z
    second   := x
    external := p.

Its generated line-third point is `y`.

Applying the first forced cross-line completion to this rotated frame
forces the final independent Fano line:

    complete lineThird firstExternalThird
      =
    secondExternalThird.

In the conventional shorthand, this is

    complete z a = b.

Commutativity and Steiner recovery provide all orientations of this
line.
-/

namespace SevenForcingFanoFrameRotate

noncomputable section

universe u

open SevenForcingFanoFrame
open SevenForcingFanoFrameGenerated

section RotateDefinitions

variable {Point : Type u}
variable [DecidableEq Point]

/--
Cyclically rotate the three points on the original generated line:

    (first, second, lineThird)
      ↦
    (lineThird, first, second).

The external point remains fixed.
-/
def rotate
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame S :=

  ⟨
    (
      frame.lineThird,
      frame.first,
      frame.external
    ),
    by
      constructor

      · exact frame.lineThird_ne_first

      · intro hmem

        have hblock :
            S.block frame.lineThird frame.first =
              S.block frame.first frame.second := by

          ext q

          simp [
            Steiner.TripleSystem.block,
            Frame.lineThird,
            S.complete_comm,
            S.complete_left,
            or_comm,
            or_assoc
          ]

        rw [hblock] at hmem

        exact
          frame.external_not_mem_block
            hmem
  ⟩

/--
The first point of the rotated frame is the original line-third point.
-/
@[simp]
theorem rotate_first
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    (rotate frame).first =
      frame.lineThird := by

  rfl

/--
The second point of the rotated frame is the original first point.
-/
@[simp]
theorem rotate_second
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    (rotate frame).second =
      frame.first := by

  rfl

/--
The external point is unchanged by rotation.
-/
@[simp]
theorem rotate_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    (rotate frame).external =
      frame.external := by

  rfl

/--
The generated line-third point of the rotated frame is the original
second point.
-/
@[simp]
theorem rotate_lineThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    (rotate frame).lineThird =
      frame.second := by

  change
    S.complete frame.lineThird frame.first =
      frame.second

  calc
    S.complete frame.lineThird frame.first =
        S.complete frame.first frame.lineThird := by
      exact
        S.complete_comm
          frame.lineThird
          frame.first

    _ =
        frame.second := by
      unfold Frame.lineThird

      exact
        S.complete_left
          frame.first
          frame.second

/--
The first external completion of the rotated frame is the original
line-third external completion.
-/
@[simp]
theorem rotate_firstExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird (rotate frame) =
      Frame.lineThirdExternalThird frame := by

  rfl

/--
The second external completion of the rotated frame is the original
first external completion.
-/
@[simp]
theorem rotate_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.secondExternalThird (rotate frame) =
      Frame.firstExternalThird frame := by

  rfl

/--
The line-third external completion of the rotated frame is the
original second external completion.
-/
@[simp]
theorem rotate_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.lineThirdExternalThird (rotate frame) =
      Frame.secondExternalThird frame := by

  unfold Frame.lineThirdExternalThird

  rw [rotate_lineThird, rotate_external]

  rfl

end RotateDefinitions

section ForcedThirdCrossLine

variable {Point : Type u}
variable [Fintype Point]
variable [DecidableEq Point]

/--
The third and final independent forced cross-line completion:

    complete lineThird firstExternalThird
      =
    secondExternalThird.
-/
theorem Frame.complete_lineThird_firstExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        frame.lineThird
        (Frame.firstExternalThird frame) =
      Frame.secondExternalThird frame := by

  have hrotate :=
    SevenForcingFanoFrameForcedCompletion.Frame.complete_first_secondExternalThird
      (frame := rotate frame)
      hCard

  simpa only [
    rotate_first,
    rotate_secondExternalThird,
    rotate_lineThirdExternalThird
  ] using hrotate

/--
The symmetric orientation of the third forced cross-line.
-/
theorem Frame.complete_firstExternalThird_lineThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        (Frame.firstExternalThird frame)
        frame.lineThird =
      Frame.secondExternalThird frame := by

  calc
    S.complete
        (Frame.firstExternalThird frame)
        frame.lineThird =
        S.complete
          frame.lineThird
          (Frame.firstExternalThird frame) := by
      exact
        S.complete_comm
          (Frame.firstExternalThird frame)
          frame.lineThird

    _ =
        Frame.secondExternalThird frame := by
      exact
        Frame.complete_lineThird_firstExternalThird
          frame
          hCard

/--
Completing `lineThird` with `secondExternalThird` recovers
`firstExternalThird`.
-/
theorem Frame.complete_lineThird_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        frame.lineThird
        (Frame.secondExternalThird frame) =
      Frame.firstExternalThird frame := by

  rw [
    ← Frame.complete_lineThird_firstExternalThird
      frame
      hCard
  ]

  exact
    S.complete_left
      frame.lineThird
      (Frame.firstExternalThird frame)

/--
Completing the two generated points of the third forced cross-line
recovers `lineThird`.
-/
theorem Frame.complete_firstExternalThird_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        (Frame.firstExternalThird frame)
        (Frame.secondExternalThird frame) =
      frame.lineThird := by

  rw [
    ← Frame.complete_lineThird_firstExternalThird
      frame
      hCard
  ]

  exact
    (
      S.block_recovery
        frame.lineThird
        (Frame.firstExternalThird frame)
    ).2

end ForcedThirdCrossLine

end

end SevenForcingFanoFrameRotate

#check SevenForcingFanoFrameRotate.rotate
#check SevenForcingFanoFrameRotate.rotate_lineThird
#check SevenForcingFanoFrameRotate.Frame.complete_lineThird_firstExternalThird
#check SevenForcingFanoFrameRotate.Frame.complete_firstExternalThird_lineThird
#check SevenForcingFanoFrameRotate.Frame.complete_lineThird_secondExternalThird
#check SevenForcingFanoFrameRotate.Frame.complete_firstExternalThird_secondExternalThird
