import KTLean.SevenForcingFanoFrame

/-!
# Points Generated from a Noncollinear Frame

## Formal status

**Level 2 — Consequence of global triadic closure and a selected
noncollinear frame.**

Given a frame with points

    x = first
    y = second
    z = complete x y
    p = external,

this module defines three further points:

    a = complete x p
    b = complete y p
    c = complete z p.

These are the remaining canonical expressions expected in a
seven-point Fano realization:

    x, y, z, p, a, b, c.

This module proves the local distinctness and recovery identities for
the three newly generated points. Full pairwise distinctness of all
seven canonical expressions is deferred to the next module.
-/

namespace SevenForcingFanoFrameGenerated

universe u

variable {Point : Type u}
variable [DecidableEq Point]

open SevenForcingFanoFrame

/--
The completion of the first frame point with the external point.
-/
def Frame.firstExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Point :=
  S.complete frame.first frame.external

/--
The completion of the second frame point with the external point.
-/
def Frame.secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Point :=
  S.complete frame.second frame.external

/--
The completion of the original line-third point with the external
point.
-/
def Frame.lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Point :=
  S.complete frame.lineThird frame.external

/--
The first frame point and the external point are distinct.
-/
theorem Frame.first_ne_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    frame.first ≠ frame.external := by

  exact Ne.symm frame.external_ne_first

/--
The second frame point and the external point are distinct.
-/
theorem Frame.second_ne_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    frame.second ≠ frame.external := by

  exact Ne.symm frame.external_ne_second

/--
The original line-third point and the external point are distinct.
-/
theorem Frame.lineThird_ne_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    frame.lineThird ≠ frame.external := by

  exact Ne.symm frame.external_ne_lineThird

/--
The completion of `first` and `external` differs from `first`.
-/
theorem Frame.firstExternalThird_ne_first
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird frame ≠ frame.first := by

  exact
    S.complete_ne_left
      (Frame.first_ne_external frame)
/--
The completion of `first` and `external` differs from `external`.
-/
theorem Frame.firstExternalThird_ne_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.firstExternalThird frame ≠ frame.external := by

  exact
    S.complete_ne_right
      (Frame.first_ne_external frame)

/--
The completion of `second` and `external` differs from `second`.
-/
theorem Frame.secondExternalThird_ne_second
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.secondExternalThird frame ≠ frame.second := by

  exact
    S.complete_ne_left
      (Frame.second_ne_external frame)

/--
The completion of `second` and `external` differs from `external`.
-/
theorem Frame.secondExternalThird_ne_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.secondExternalThird frame ≠ frame.external := by

  exact
    S.complete_ne_right
      (Frame.second_ne_external frame)
/--
The completion of `lineThird` and `external` differs from
`lineThird`.
-/
theorem Frame.lineThirdExternalThird_ne_lineThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.lineThirdExternalThird frame ≠ frame.lineThird := by

  exact
    S.complete_ne_left
      (Frame.lineThird_ne_external frame)

/--
The completion of `lineThird` and `external` differs from `external`.
-/
theorem Frame.lineThirdExternalThird_ne_external
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Frame.lineThirdExternalThird frame ≠ frame.external := by

  exact
    S.complete_ne_right
      (Frame.lineThird_ne_external frame)
/--
Completing `first` with `firstExternalThird` recovers `external`.
-/
theorem Frame.complete_first_firstExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    S.complete frame.first
        (Frame.firstExternalThird frame) =
      frame.external := by

  exact
    S.complete_left
      frame.first
      frame.external

/--
Completing `external` with `firstExternalThird` recovers `first`.
-/
theorem Frame.complete_external_firstExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    S.complete frame.external
        (Frame.firstExternalThird frame) =
      frame.first := by

  exact
    (
      S.block_recovery
        frame.first
        frame.external
    ).2
/--
Completing `second` with `secondExternalThird` recovers `external`.
-/
theorem Frame.complete_second_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    S.complete frame.second
        (Frame.secondExternalThird frame) =
      frame.external := by

  exact
    S.complete_left
      frame.second
      frame.external

/--
Completing `external` with `secondExternalThird` recovers `second`.
-/
theorem Frame.complete_external_secondExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    S.complete frame.external
        (Frame.secondExternalThird frame) =
      frame.second := by

  exact
    (
      S.block_recovery
        frame.second
        frame.external
    ).2

/--
Completing `lineThird` with `lineThirdExternalThird` recovers
`external`.
-/
theorem Frame.complete_lineThird_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    S.complete
        frame.lineThird
        (Frame.lineThirdExternalThird frame) =
      frame.external := by

  exact
    S.complete_left
      frame.lineThird
      frame.external
/--
Completing `external` with `lineThirdExternalThird` recovers the
original line-third point.
-/

theorem Frame.complete_external_lineThirdExternalThird
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    S.complete
        frame.external
        (Frame.lineThirdExternalThird frame) =
      frame.lineThird := by

  exact
    (
      S.block_recovery
        frame.lineThird
        frame.external
    ).2

/--
The seven canonical frame expressions, recorded as a function from
`Fin 7`.
-/
def Frame.canonicalPoint
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S) :
    Fin 7 →
      Point

  | 0 =>
      frame.first

  | 1 =>
      frame.second

  | 2 =>
      frame.lineThird

  | 3 =>
      frame.external

  | 4 =>
      Frame.firstExternalThird frame

  | 5 =>
      Frame.secondExternalThird frame

  | 6 =>
      Frame.lineThirdExternalThird frame

end SevenForcingFanoFrameGenerated

#check SevenForcingFanoFrameGenerated.Frame.firstExternalThird
#check SevenForcingFanoFrameGenerated.Frame.secondExternalThird
#check SevenForcingFanoFrameGenerated.Frame.lineThirdExternalThird
#check SevenForcingFanoFrameGenerated.Frame.complete_first_firstExternalThird
#check SevenForcingFanoFrameGenerated.Frame.complete_external_firstExternalThird
#check SevenForcingFanoFrameGenerated.Frame.complete_second_secondExternalThird
#check SevenForcingFanoFrameGenerated.Frame.complete_external_secondExternalThird
#check SevenForcingFanoFrameGenerated.Frame.complete_lineThird_lineThirdExternalThird
#check SevenForcingFanoFrameGenerated.Frame.complete_external_lineThirdExternalThird
