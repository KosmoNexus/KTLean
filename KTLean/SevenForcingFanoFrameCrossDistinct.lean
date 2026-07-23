import KTLean.SevenForcingFanoFrameGenerated

/-!
# Cross-Distinctness of Generated Fano-Frame Points

## Formal status

**Level 2 — Consequence of global triadic closure and a selected
noncollinear frame.**

For a frame with canonical points

    x = first
    y = second
    z = complete x y
    p = external
    a = complete x p
    b = complete y p
    c = complete z p,

the preceding modules establish the local distinctness relations inside
each generated triad.

This module proves the remaining cross-relations:

    a ≠ y, z
    b ≠ x, z
    c ≠ x, y
    a ≠ b, c
    b ≠ c.

Together with the earlier frame and local-completion results, these
relations imply that all seven canonical frame expressions are
pairwise distinct.
-/

namespace SevenForcingFanoFrameCrossDistinct

universe u

variable {Point : Type u}
variable [DecidableEq Point]

open SevenForcingFanoFrame
open SevenForcingFanoFrameGenerated

/--
The completion of `first` and `external` differs from `second`.
-/
theorem Frame.firstExternalThird_ne_second
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird frame ≠
      frame.second := by

  intro h

  have hrecover :
      S.complete frame.first frame.second =
        frame.external := by

    calc
      S.complete frame.first frame.second =
          S.complete frame.first
            (Frame.firstExternalThird frame) := by
        rw [h]

      _ = frame.external := by
        exact
          Frame.complete_first_firstExternalThird
            frame

  apply frame.external_ne_lineThird

  exact hrecover.symm

/--
The completion of `first` and `external` differs from the original
line-third point.
-/
theorem Frame.firstExternalThird_ne_lineThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird frame ≠
      frame.lineThird := by

  intro h

  have hrecover :
      S.complete frame.first frame.lineThird =
        frame.external := by

    calc
      S.complete frame.first frame.lineThird =
          S.complete frame.first
            (Frame.firstExternalThird frame) := by
        rw [h]

      _ = frame.external := by
        exact
          Frame.complete_first_firstExternalThird
            frame

  have hexternalSecond :
      frame.external =
        frame.second := by

    calc
      frame.external =
          S.complete frame.first frame.lineThird := by
        exact hrecover.symm

      _ = frame.second := by
        exact
          S.complete_left
            frame.first
            frame.second

  exact
    frame.external_ne_second
      hexternalSecond

/--
The completion of `second` and `external` differs from `first`.
-/
theorem Frame.secondExternalThird_ne_first
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.secondExternalThird frame ≠
      frame.first := by

  intro h

  have hrecover :
      S.complete frame.second frame.first =
        frame.external := by

    calc
      S.complete frame.second frame.first =
          S.complete frame.second
            (Frame.secondExternalThird frame) := by
        rw [h]

      _ = frame.external := by
        exact
          Frame.complete_second_secondExternalThird
            frame

  apply frame.external_ne_lineThird

  calc
    frame.external =
        S.complete frame.second frame.first := by
      exact hrecover.symm

    _ = S.complete frame.first frame.second := by
      exact
        S.complete_comm
          frame.second
          frame.first

/--
The completion of `second` and `external` differs from the original
line-third point.
-/
theorem Frame.secondExternalThird_ne_lineThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.secondExternalThird frame ≠
      frame.lineThird := by

  intro h

  have hrecover :
      S.complete frame.second frame.lineThird =
        frame.external := by

    calc
      S.complete frame.second frame.lineThird =
          S.complete frame.second
            (Frame.secondExternalThird frame) := by
        rw [h]

      _ = frame.external := by
        exact
          Frame.complete_second_secondExternalThird
            frame

  have hexternalFirst :
      frame.external =
        frame.first := by

    calc
      frame.external =
          S.complete frame.second frame.lineThird := by
        exact hrecover.symm

      _ = frame.first := by
        exact
          (
            S.block_recovery
              frame.first
              frame.second
          ).2

  exact
    frame.external_ne_first
      hexternalFirst

/--
The completion of `lineThird` and `external` differs from `first`.
-/
theorem Frame.lineThirdExternalThird_ne_first
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.lineThirdExternalThird frame ≠
      frame.first := by

  intro h

  have hrecover :
      S.complete frame.lineThird frame.first =
        frame.external := by

    calc
      S.complete frame.lineThird frame.first =
          S.complete frame.lineThird
            (Frame.lineThirdExternalThird frame) := by
        rw [h]

      _ = frame.external := by
        exact
          Frame.complete_lineThird_lineThirdExternalThird
            frame

  have hexternalSecond :
      frame.external =
        frame.second := by

    calc
      frame.external =
          S.complete frame.lineThird frame.first := by
        exact hrecover.symm

      _ = S.complete frame.first frame.lineThird := by
        exact
          S.complete_comm
            frame.lineThird
            frame.first

      _ = frame.second := by
        exact
          S.complete_left
            frame.first
            frame.second

  exact
    frame.external_ne_second
      hexternalSecond

/--
The completion of `lineThird` and `external` differs from `second`.
-/
theorem Frame.lineThirdExternalThird_ne_second
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.lineThirdExternalThird frame ≠
      frame.second := by

  intro h

  have hrecover :
      S.complete frame.lineThird frame.second =
        frame.external := by

    calc
      S.complete frame.lineThird frame.second =
          S.complete frame.lineThird
            (Frame.lineThirdExternalThird frame) := by
        rw [h]

      _ = frame.external := by
        exact
          Frame.complete_lineThird_lineThirdExternalThird
            frame

  have hexternalFirst :
      frame.external =
        frame.first := by

    calc
      frame.external =
          S.complete frame.lineThird frame.second := by
        exact hrecover.symm

      _ = frame.first := by
        exact
          S.complete_right
            frame.first
            frame.second

  exact
    frame.external_ne_first
      hexternalFirst

/--
The first and second external-completion points are distinct.
-/
theorem Frame.firstExternalThird_ne_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird frame ≠
      Frame.secondExternalThird frame := by

  intro h

  apply frame.first_ne_second

  calc
    frame.first =
        S.complete frame.external
          (Frame.firstExternalThird frame) := by
      exact
        (
          Frame.complete_external_firstExternalThird
            frame
        ).symm

    _ =
        S.complete frame.external
          (Frame.secondExternalThird frame) := by
      rw [h]

    _ = frame.second := by
      exact
        Frame.complete_external_secondExternalThird
          frame

/--
The first and line-third external-completion points are distinct.
-/
theorem Frame.firstExternalThird_ne_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird frame ≠
      Frame.lineThirdExternalThird frame := by

  intro h

  apply
    Ne.symm frame.lineThird_ne_first

  calc
    frame.first =
        S.complete frame.external
          (Frame.firstExternalThird frame) := by
      exact
        (
          Frame.complete_external_firstExternalThird
            frame
        ).symm

    _ =
        S.complete frame.external
          (Frame.lineThirdExternalThird frame) := by
      rw [h]

    _ = frame.lineThird := by
      exact
        Frame.complete_external_lineThirdExternalThird
          frame

/--
The second and line-third external-completion points are distinct.
-/
theorem Frame.secondExternalThird_ne_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.secondExternalThird frame ≠
      Frame.lineThirdExternalThird frame := by

  intro h

  apply
    Ne.symm frame.lineThird_ne_second

  calc
    frame.second =
        S.complete frame.external
          (Frame.secondExternalThird frame) := by
      exact
        (
          Frame.complete_external_secondExternalThird
            frame
        ).symm

    _ =
        S.complete frame.external
          (Frame.lineThirdExternalThird frame) := by
      rw [h]

    _ = frame.lineThird := by
      exact
        Frame.complete_external_lineThirdExternalThird
          frame

/--
All remaining cross-distinctness relations among the seven canonical
frame expressions.
-/
theorem Frame.generated_cross_distinctness
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird frame ≠ frame.second
      ∧ Frame.firstExternalThird frame ≠ frame.lineThird
      ∧ Frame.secondExternalThird frame ≠ frame.first
      ∧ Frame.secondExternalThird frame ≠ frame.lineThird
      ∧ Frame.lineThirdExternalThird frame ≠ frame.first
      ∧ Frame.lineThirdExternalThird frame ≠ frame.second
      ∧ Frame.firstExternalThird frame ≠
          Frame.secondExternalThird frame
      ∧ Frame.firstExternalThird frame ≠
          Frame.lineThirdExternalThird frame
      ∧ Frame.secondExternalThird frame ≠
          Frame.lineThirdExternalThird frame := by

  exact
    ⟨
      Frame.firstExternalThird_ne_second frame,
      Frame.firstExternalThird_ne_lineThird frame,
      Frame.secondExternalThird_ne_first frame,
      Frame.secondExternalThird_ne_lineThird frame,
      Frame.lineThirdExternalThird_ne_first frame,
      Frame.lineThirdExternalThird_ne_second frame,
      Frame.firstExternalThird_ne_secondExternalThird frame,
      Frame.firstExternalThird_ne_lineThirdExternalThird frame,
      Frame.secondExternalThird_ne_lineThirdExternalThird frame
    ⟩

end SevenForcingFanoFrameCrossDistinct

#check SevenForcingFanoFrameCrossDistinct.Frame.firstExternalThird_ne_second
#check SevenForcingFanoFrameCrossDistinct.Frame.firstExternalThird_ne_lineThird
#check SevenForcingFanoFrameCrossDistinct.Frame.secondExternalThird_ne_first
#check SevenForcingFanoFrameCrossDistinct.Frame.secondExternalThird_ne_lineThird
#check SevenForcingFanoFrameCrossDistinct.Frame.lineThirdExternalThird_ne_first
#check SevenForcingFanoFrameCrossDistinct.Frame.lineThirdExternalThird_ne_second
#check SevenForcingFanoFrameCrossDistinct.Frame.firstExternalThird_ne_secondExternalThird
#check SevenForcingFanoFrameCrossDistinct.Frame.firstExternalThird_ne_lineThirdExternalThird
#check SevenForcingFanoFrameCrossDistinct.Frame.secondExternalThird_ne_lineThirdExternalThird
#check SevenForcingFanoFrameCrossDistinct.Frame.generated_cross_distinctness
