import KTLean.GlyphForcingTriadicRole

/-!
# Forcing and Testing the Binary Orientation

## Formal status

**Level 1 — Canonical orientation carrier, its action on triadic
roles, and identification with the existing implementation.**

A local three-channel traversal with a fixed anchor has two possible
directions:

    forward
    reverse.

The reversal fixes the anchor and exchanges the two non-anchor roles.

This module introduces the canonical two-element orientation carrier
and identifies it with the existing KT orientation type:

    forward ↦ cw
    reverse ↦ ccw.

It then proves an important structural fact:

The two orientations act identically on the anchor role, but
differently on both non-anchor roles.

Thus orientation is a genuine binary coordinate of the full oriented
operation, but it cannot be recovered from the selected local point
when the active role is the anchor.

This is not yet a glyph-cardinality theorem.
-/

namespace GlyphForcingOrientation

open AdmissibleOperation
open GlyphForcingTriadicRole

/--
The canonical carrier of the two reversible traversal directions.
-/
inductive ForcedOrientation where

  | forward
  | reverse

  deriving
    DecidableEq,
    Repr

/--
Explicit finite enumeration of the forced orientations.
-/
instance forcedOrientationFintype :
    Fintype ForcedOrientation where

  elems :=
    {
      ForcedOrientation.forward,
      ForcedOrientation.reverse
    }

  complete := by
    intro orientation
    cases orientation <;>
      simp

/--
Interpret the canonical traversal direction as the existing KT
orientation.
-/
def toExistingOrientation :
    ForcedOrientation →
      Orientation

  | .forward =>
      .cw

  | .reverse =>
      .ccw

/--
Recover the canonical direction represented by an existing KT
orientation.
-/
def fromExistingOrientation :
    Orientation →
      ForcedOrientation

  | .cw =>
      .forward

  | .ccw =>
      .reverse

/--
Recovering a canonical orientation after interpretation returns the
original orientation.
-/
@[simp]
theorem fromExistingOrientation_toExistingOrientation
    (orientation : ForcedOrientation) :
    fromExistingOrientation
        (toExistingOrientation orientation) =
      orientation := by

  cases orientation <;>
    rfl

/--
Interpreting a recovered existing orientation returns the original
existing orientation.
-/
@[simp]
theorem toExistingOrientation_fromExistingOrientation
    (orientation : Orientation) :
    toExistingOrientation
        (fromExistingOrientation orientation) =
      orientation := by

  cases orientation <;>
    rfl

/--
The forced binary traversal carrier is equivalent to the existing KT
orientation implementation.
-/
def forcedOrientationEquivExisting :
    ForcedOrientation ≃
      Orientation where

  toFun :=
    toExistingOrientation

  invFun :=
    fromExistingOrientation

  left_inv :=
    fromExistingOrientation_toExistingOrientation

  right_inv :=
    toExistingOrientation_fromExistingOrientation

/--
The forced orientation carrier contains exactly two elements.
-/
theorem card_forcedOrientation :
    Fintype.card ForcedOrientation =
      2 := by

  decide

/--
The existing orientation carrier has two elements because it is
equivalent to the forced reversible-direction carrier.
-/
theorem card_existingOrientation_from_forced :
    Fintype.card Orientation =
      2 := by

  calc
    Fintype.card Orientation =
        Fintype.card ForcedOrientation := by
      exact
        Fintype.card_congr
          forcedOrientationEquivExisting.symm

    _ =
        2 := by
      exact
        card_forcedOrientation

/--
Reversal acts on the canonical triadic roles by fixing the anchor and
exchanging successor with completion.
-/
def actOnRole :
    ForcedOrientation →
      ForcedRole →
        ForcedRole

  | .forward, role =>
      role

  | .reverse, 0 =>
      0

  | .reverse, 1 =>
      2

  | .reverse, 2 =>
      1

/--
The corresponding action on the existing triadic-role implementation.
-/
def actOnExistingRole :
    Orientation →
      TriadicRole →
        TriadicRole

  | .cw, role =>
      role

  | .ccw, .anchor =>
      .anchor

  | .ccw, .successor =>
      .completion

  | .ccw, .completion =>
      .successor

/--
The forced role and orientation interpretations commute with the
orientation action.
-/
theorem interpretation_preserves_action
    (orientation : ForcedOrientation)
    (role : ForcedRole) :
    toExistingRole
        (
          actOnRole
            orientation
            role
        ) =
      actOnExistingRole
        (toExistingOrientation orientation)
        (toExistingRole role) := by

  cases orientation <;>
    fin_cases role <;>
    rfl

/--
Forward traversal leaves every role unchanged.
-/
@[simp]
theorem forward_actOnRole
    (role : ForcedRole) :
    actOnRole
        .forward
        role =
      role := by

  rfl

/--
Reverse traversal fixes the anchor.
-/
@[simp]
theorem reverse_anchor :
    actOnRole
        .reverse
        0 =
      0 := by

  rfl

/--
Reverse traversal sends successor to completion.
-/
@[simp]
theorem reverse_successor :
    actOnRole
        .reverse
        1 =
      2 := by

  rfl

/--
Reverse traversal sends completion to successor.
-/
@[simp]
theorem reverse_completion :
    actOnRole
        .reverse
        2 =
      1 := by

  rfl

/--
Reversing twice restores every triadic role.
-/
theorem reverse_involutive :
    Function.Involutive
      (actOnRole .reverse) := by

  intro role

  fin_cases role <;>
    rfl

/--
The two orientations act identically exactly at the anchor role.
-/
theorem forward_eq_reverse_iff_anchor
    (role : ForcedRole) :
    actOnRole .forward role =
        actOnRole .reverse role
      ↔
    role = 0 := by

  fin_cases role <;>
    decide

/--
Orientation is distinguishable at the successor role.
-/
theorem orientations_distinct_at_successor :
    actOnRole .forward 1 ≠
      actOnRole .reverse 1 := by

  decide

/--
Orientation is distinguishable at the completion role.
-/
theorem orientations_distinct_at_completion :
    actOnRole .forward 2 ≠
      actOnRole .reverse 2 := by

  decide

/--
Orientation is not distinguishable from the active-role projection at
the anchor.
-/
theorem orientations_coincide_at_anchor :
    actOnRole .forward 0 =
      actOnRole .reverse 0 := by

  rfl

/--
For every non-anchor role, the two orientations select different
roles.
-/
theorem orientations_distinct_of_nonanchor
    (role : ForcedRole)
    (hNonanchor : role ≠ 0) :
    actOnRole .forward role ≠
      actOnRole .reverse role := by

  intro hEqual

  have hAnchor :
      role = 0 :=
    (
      forward_eq_reverse_iff_anchor
        role
    ).1
      hEqual

  exact
    hNonanchor
      hAnchor

/--
The orientation action has exactly one fixed canonical role: the
anchor.
-/
theorem reverse_fixed_iff_anchor
    (role : ForcedRole) :
    actOnRole .reverse role =
        role
      ↔
    role = 0 := by

  fin_cases role <;>
    decide

/--
The existing clockwise and counterclockwise actions coincide exactly
on the existing anchor role.
-/
theorem existing_orientations_agree_iff_anchor
    (role : TriadicRole) :
    actOnExistingRole .cw role =
        actOnExistingRole .ccw role
      ↔
    role = .anchor := by

  cases role <;>
    decide

end GlyphForcingOrientation

#check GlyphForcingOrientation.ForcedOrientation
#check GlyphForcingOrientation.toExistingOrientation
#check GlyphForcingOrientation.fromExistingOrientation
#check GlyphForcingOrientation.forcedOrientationEquivExisting
#check GlyphForcingOrientation.card_forcedOrientation
#check GlyphForcingOrientation.card_existingOrientation_from_forced
#check GlyphForcingOrientation.actOnRole
#check GlyphForcingOrientation.actOnExistingRole
#check GlyphForcingOrientation.interpretation_preserves_action
#check GlyphForcingOrientation.reverse_involutive
#check GlyphForcingOrientation.forward_eq_reverse_iff_anchor
#check GlyphForcingOrientation.orientations_coincide_at_anchor
#check GlyphForcingOrientation.orientations_distinct_of_nonanchor
#check GlyphForcingOrientation.reverse_fixed_iff_anchor
#check GlyphForcingOrientation.existing_orientations_agree_iff_anchor
