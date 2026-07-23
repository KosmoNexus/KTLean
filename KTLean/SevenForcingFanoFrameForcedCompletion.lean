import KTLean.SevenForcingFanoFrameCanonicalBijection

/-!
# A Forced Cross-Line Completion in Seven-Point Systems

## Formal status

**Level 2 — Consequence of global triadic closure, a selected
noncollinear frame, and exact seven-point cardinality.**

For a frame, write

    x = first
    y = second
    z = complete x y
    p = external
    a = complete x p
    b = complete y p
    c = complete z p.

The seven canonical points exhaust any seven-point ambient carrier.

This module proves the first cross-line identity

    complete x b = c.

Every other canonical candidate is excluded using the Steiner recovery
identities and the pairwise distinctness already established.

Commutativity and recovery then supply the remaining orientations of
the same generated line:

    complete b x = c
    complete x c = b
    complete c x = b
    complete b c = x
    complete c b = x.
-/

namespace SevenForcingFanoFrameForcedCompletion

noncomputable section

universe u

variable {Point : Type u}
variable [Fintype Point]
variable [DecidableEq Point]

open SevenForcingFanoFrame
open SevenForcingFanoFrameGenerated
open SevenForcingFanoFrameCrossDistinct
open SevenForcingFanoFrameCanonicalInjective
open SevenForcingFanoFrameCanonicalBijection

/--
In a seven-point system, completing `first` with
`secondExternalThird` produces `lineThirdExternalThird`.
-/
theorem Frame.complete_first_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        frame.first
        (Frame.secondExternalThird frame) =
      Frame.lineThirdExternalThird frame := by

  obtain ⟨position, hposition⟩ :=
    canonical_points_exhaust
      frame
      hCard
      (
        S.complete
          frame.first
          (Frame.secondExternalThird frame)
      )

  cases position with

  | first =>
      exfalso
      change
        frame.first =
          S.complete
            frame.first
            (Frame.secondExternalThird frame)
        at hposition

      exact
        (
          S.complete_ne_left
            (
              Ne.symm
                (
                  Frame.secondExternalThird_ne_first
                    frame
                )
            )
        )
          hposition.symm

  | second =>
      exfalso
      change
        frame.second =
          S.complete
            frame.first
            (Frame.secondExternalThird frame)
        at hposition

      have hlineThird_eq_secondExternalThird :
          frame.lineThird =
            Frame.secondExternalThird frame := by

        calc
          frame.lineThird =
              S.complete
                frame.first
                frame.second := by
            rfl

          _ =
              S.complete
                frame.first
                (
                  S.complete
                    frame.first
                    (Frame.secondExternalThird frame)
                ) := by
            exact
              congrArg
                (fun point =>
                  S.complete frame.first point)
                hposition

          _ =
              Frame.secondExternalThird frame := by
            exact
              S.complete_left
                frame.first
                (Frame.secondExternalThird frame)

      exact
        (
          Frame.secondExternalThird_ne_lineThird
            frame
        )
          hlineThird_eq_secondExternalThird.symm

  | lineThird =>
      exfalso
      change
        frame.lineThird =
          S.complete
            frame.first
            (Frame.secondExternalThird frame)
        at hposition

      have hsecond_eq_secondExternalThird :
          frame.second =
            Frame.secondExternalThird frame := by

        calc
          frame.second =
              S.complete
                frame.first
                frame.lineThird := by
            exact
              (
                S.complete_left
                  frame.first
                  frame.second
              ).symm

          _ =
              S.complete
                frame.first
                (
                  S.complete
                    frame.first
                    (Frame.secondExternalThird frame)
                ) := by
            exact
              congrArg
                (fun point =>
                  S.complete frame.first point)
                hposition

          _ =
              Frame.secondExternalThird frame := by
            exact
              S.complete_left
                frame.first
                (Frame.secondExternalThird frame)

      exact
        (
          Frame.secondExternalThird_ne_second
            frame
        )
          hsecond_eq_secondExternalThird.symm

  | external =>
      exfalso
      change
        frame.external =
          S.complete
            frame.first
            (Frame.secondExternalThird frame)
        at hposition

      have hfirstExternalThird_eq_secondExternalThird :
          Frame.firstExternalThird frame =
            Frame.secondExternalThird frame := by

        calc
          Frame.firstExternalThird frame =
              S.complete
                frame.first
                frame.external := by
            rfl

          _ =
              S.complete
                frame.first
                (
                  S.complete
                    frame.first
                    (Frame.secondExternalThird frame)
                ) := by
            exact
              congrArg
                (fun point =>
                  S.complete frame.first point)
                hposition

          _ =
              Frame.secondExternalThird frame := by
            exact
              S.complete_left
                frame.first
                (Frame.secondExternalThird frame)

      exact
        (
          Frame.firstExternalThird_ne_secondExternalThird
            frame
        )
          hfirstExternalThird_eq_secondExternalThird

  | firstExternalThird =>
      exfalso
      change
        Frame.firstExternalThird frame =
          S.complete
            frame.first
            (Frame.secondExternalThird frame)
        at hposition

      have hexternal_eq_secondExternalThird :
          frame.external =
            Frame.secondExternalThird frame := by

        calc
          frame.external =
              S.complete
                frame.first
                (Frame.firstExternalThird frame) := by
            exact
              (
                Frame.complete_first_firstExternalThird
                  frame
              ).symm

          _ =
              S.complete
                frame.first
                (
                  S.complete
                    frame.first
                    (Frame.secondExternalThird frame)
                ) := by
            exact
              congrArg
                (fun point =>
                  S.complete frame.first point)
                hposition

          _ =
              Frame.secondExternalThird frame := by
            exact
              S.complete_left
                frame.first
                (Frame.secondExternalThird frame)

      exact
        (
          Frame.secondExternalThird_ne_external
            frame
        )
          hexternal_eq_secondExternalThird.symm

  | secondExternalThird =>
      exfalso
      change
        Frame.secondExternalThird frame =
          S.complete
            frame.first
            (Frame.secondExternalThird frame)
        at hposition

      exact
        (
          S.complete_ne_right
            (
              Ne.symm
                (
                  Frame.secondExternalThird_ne_first
                    frame
                )
            )
        )
          hposition.symm

  | lineThirdExternalThird =>
      change
        Frame.lineThirdExternalThird frame =
          S.complete
            frame.first
            (Frame.secondExternalThird frame)
        at hposition

      exact hposition.symm

/--
The symmetric orientation of the first forced cross-line completion.
-/
theorem Frame.complete_secondExternalThird_first
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        (Frame.secondExternalThird frame)
        frame.first =
      Frame.lineThirdExternalThird frame := by

  calc
    S.complete
        (Frame.secondExternalThird frame)
        frame.first =
        S.complete
          frame.first
          (Frame.secondExternalThird frame) := by
      exact
        S.complete_comm
          (Frame.secondExternalThird frame)
          frame.first

    _ =
        Frame.lineThirdExternalThird frame := by
      exact
        Frame.complete_first_secondExternalThird
          frame
          hCard

/--
Completing `first` with `lineThirdExternalThird` recovers
`secondExternalThird`.
-/
theorem Frame.complete_first_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        frame.first
        (Frame.lineThirdExternalThird frame) =
      Frame.secondExternalThird frame := by

  rw [
    ← Frame.complete_first_secondExternalThird
      frame
      hCard
  ]

  exact
    S.complete_left
      frame.first
      (Frame.secondExternalThird frame)

/--
The symmetric orientation recovering `secondExternalThird`.
-/
theorem Frame.complete_lineThirdExternalThird_first
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        (Frame.lineThirdExternalThird frame)
        frame.first =
      Frame.secondExternalThird frame := by

  calc
    S.complete
        (Frame.lineThirdExternalThird frame)
        frame.first =
        S.complete
          frame.first
          (Frame.lineThirdExternalThird frame) := by
      exact
        S.complete_comm
          (Frame.lineThirdExternalThird frame)
          frame.first

    _ =
        Frame.secondExternalThird frame := by
      exact
        Frame.complete_first_lineThirdExternalThird
          frame
          hCard

/--
Completing the other two points of the forced cross-line recovers
`first`.
-/
theorem Frame.complete_secondExternalThird_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        (Frame.secondExternalThird frame)
        (Frame.lineThirdExternalThird frame) =
      frame.first := by

  rw [
    ← Frame.complete_first_secondExternalThird
      frame
      hCard
  ]

  exact
    (
      S.block_recovery
        frame.first
        (Frame.secondExternalThird frame)
    ).2

/--
The symmetric orientation recovering `first`.
-/
theorem Frame.complete_lineThirdExternalThird_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    S.complete
        (Frame.lineThirdExternalThird frame)
        (Frame.secondExternalThird frame) =
      frame.first := by

  calc
    S.complete
        (Frame.lineThirdExternalThird frame)
        (Frame.secondExternalThird frame) =
        S.complete
          (Frame.secondExternalThird frame)
          (Frame.lineThirdExternalThird frame) := by
      exact
        S.complete_comm
          (Frame.lineThirdExternalThird frame)
          (Frame.secondExternalThird frame)

    _ = frame.first := by
      exact
        Frame.complete_secondExternalThird_lineThirdExternalThird
          frame
          hCard

end

end SevenForcingFanoFrameForcedCompletion

#check SevenForcingFanoFrameForcedCompletion.Frame.complete_first_secondExternalThird
#check SevenForcingFanoFrameForcedCompletion.Frame.complete_secondExternalThird_first
#check SevenForcingFanoFrameForcedCompletion.Frame.complete_first_lineThirdExternalThird
#check SevenForcingFanoFrameForcedCompletion.Frame.complete_lineThirdExternalThird_first
#check SevenForcingFanoFrameForcedCompletion.Frame.complete_secondExternalThird_lineThirdExternalThird
#check SevenForcingFanoFrameForcedCompletion.Frame.complete_lineThirdExternalThird_secondExternalThird
