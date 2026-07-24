import KTLean.GlyphForcingVisibleStructure
import KTLean.GlyphAddressFrobenius

/-!
# Frobenius Identification of the Forced Glyph Roles

## Formal status

**Level 2 — Dynamical identification, not cardinality
reconstruction.**

The glyph forcing chain independently established:

* a three-element forced local-role carrier;
* a seven-by-three intrinsic visible quotient;
* a binary framed lift producing 42 glyphs.

This module now identifies the forced three-role carrier with the
canonical Frobenius orbit

    1 → 2 → 4 → 1  modulo 7.

The identification is not merely a bijection of three-element sets.
The canonical role advance is proved to intertwine with the Frobenius
`next` map, whose numerical action is multiplication by two modulo
seven.

Thus Frobenius structure is recovered as the intrinsic cyclic dynamics
of the forced local-role carrier. It is not assumed in order to obtain
the glyph count.
-/

namespace GlyphForcingFrobeniusIdentification

open GlyphForcingTriadicRole
open GlyphForcingPrimitiveWalk
open GlyphForcingNormalForm
open GlyphForcingVisibleQuotient
open GlyphForcingVisibleStructure

/--
Advance once through the three forced local roles.
-/
def nextRole :
    ForcedRole →
      ForcedRole

  | 0 =>
      1

  | 1 =>
      2

  | 2 =>
      0

/--
Interpret one forced role as its canonical Frobenius step.
-/
def stepOfForcedRole :
    ForcedRole →
      FrobeniusOrbit.Step

  | 0 =>
      .one

  | 1 =>
      .two

  | 2 =>
      .four

/--
Recover the forced role represented by a Frobenius step.
-/
def forcedRoleOfStep :
    FrobeniusOrbit.Step →
      ForcedRole

  | .one =>
      0

  | .two =>
      1

  | .four =>
      2

/--
Recovering a forced role after Frobenius interpretation returns the
original role.
-/
@[simp]
theorem forcedRoleOfStep_stepOfForcedRole
    (role : ForcedRole) :
    forcedRoleOfStep
        (stepOfForcedRole role) =
      role := by

  fin_cases role <;>
    rfl

/--
Interpreting a recovered Frobenius step returns the original step.
-/
@[simp]
theorem stepOfForcedRole_forcedRoleOfStep
    (step : FrobeniusOrbit.Step) :
    stepOfForcedRole
        (forcedRoleOfStep step) =
      step := by

  cases step <;>
    rfl

/--
The forced local-role carrier is canonically equivalent to the
Frobenius orbit.
-/
def forcedRoleEquivFrobenius :
    ForcedRole ≃
      FrobeniusOrbit.Step where

  toFun :=
    stepOfForcedRole

  invFun :=
    forcedRoleOfStep

  left_inv :=
    forcedRoleOfStep_stepOfForcedRole

  right_inv :=
    stepOfForcedRole_forcedRoleOfStep

/--
The canonical forced-role advance agrees exactly with Frobenius
advance.
-/
theorem stepOfForcedRole_nextRole
    (role : ForcedRole) :
    stepOfForcedRole
        (nextRole role) =
      FrobeniusOrbit.next
        (stepOfForcedRole role) := by

  fin_cases role <;>
    rfl

/--
The inverse interpretation also intertwines Frobenius advance with the
forced-role cycle.
-/
theorem forcedRoleOfStep_next
    (step : FrobeniusOrbit.Step) :
    forcedRoleOfStep
        (FrobeniusOrbit.next step) =
      nextRole
        (forcedRoleOfStep step) := by

  cases step <;>
    rfl

/--
Advancing three times returns every forced role to itself.
-/
theorem nextRole_three
    (role : ForcedRole) :
    nextRole
        (nextRole
          (nextRole role)) =
      role := by

  fin_cases role <;>
    rfl

/--
One forced-role advance fixes no role.
-/
theorem nextRole_ne_self
    (role : ForcedRole) :
    nextRole role ≠
      role := by

  fin_cases role <;>
    decide

/--
Two forced-role advances also fix no role.
-/
theorem nextRole_next_ne_self
    (role : ForcedRole) :
    nextRole
        (nextRole role) ≠
      role := by

  fin_cases role <;>
    decide

/--
The numerical value of the next forced role is multiplication by two
modulo seven after Frobenius interpretation.
-/
theorem forcedRole_value_next
    (role : ForcedRole) :
    (
      stepOfForcedRole
        (nextRole role)
    ).value =
      (
        stepOfForcedRole role
      ).value * 2 := by

  calc
    (
      stepOfForcedRole
        (nextRole role)
    ).value =
        (
          FrobeniusOrbit.next
            (stepOfForcedRole role)
        ).value := by

      rw [
        stepOfForcedRole_nextRole
      ]

    _ =
        (
          stepOfForcedRole role
        ).value * 2 := by

      exact
        FrobeniusOrbit.value_next
          (stepOfForcedRole role)

/--
The forced role values are exactly the canonical Frobenius orbit
`1, 2, 4`.
-/
theorem forcedRole_values :
    [
      (stepOfForcedRole 0).value,
      (stepOfForcedRole 1).value,
      (stepOfForcedRole 2).value
    ] =
      [1, 2, 4] := by

  rfl

/--
The forced-role interpretation agrees with the pre-existing
role-to-Frobenius bridge.
-/
theorem agrees_with_existing_role_bridge
    (role : ForcedRole) :
    GlyphAddressFrobenius.stepOfRole
        (toExistingRole role) =
      stepOfForcedRole role := by

  fin_cases role <;>
    rfl

/--
The inverse forced-role interpretation agrees with the pre-existing
Frobenius-to-role bridge.
-/
theorem existing_role_bridge_agrees
    (step : FrobeniusOrbit.Step) :
    fromExistingRole
        (GlyphAddressFrobenius.roleOfStep step) =
      forcedRoleOfStep step := by

  cases step <;>
    rfl

/--
The intrinsic visible glyph quotient in Frobenius coordinates.
-/
abbrev VisibleFrobeniusAddress :=
  Fano.Point × FrobeniusOrbit.Step

/--
Convert one intrinsic visible quotient point into its canonical
Fano-address/Frobenius-step representation.
-/
noncomputable def visibleToFrobenius
    (visible : GlyphObservationQuotient) :
    VisibleFrobeniusAddress :=

  (
    visibleAddress visible,
    stepOfForcedRole
      (visibleRole visible)
  )

/--
Recover an intrinsic visible quotient point from a Fano address and
Frobenius step.
-/
noncomputable def frobeniusToVisible
    (address : VisibleFrobeniusAddress) :
    GlyphObservationQuotient :=

  ofAddressRole
    address.1
    (
      forcedRoleOfStep
        address.2
    )

/--
Visible-to-Frobenius conversion followed by reconstruction returns the
original quotient point.
-/
@[simp]
theorem frobeniusToVisible_visibleToFrobenius
    (visible : GlyphObservationQuotient) :
    frobeniusToVisible
        (visibleToFrobenius visible) =
      visible := by

  unfold frobeniusToVisible
  unfold visibleToFrobenius

  rw [
    forcedRoleOfStep_stepOfForcedRole
  ]

  exact
    ofAddressRole_visibleCoordinates
      visible

/--
Frobenius reconstruction followed by coordinate recovery returns the
original address.
-/
@[simp]
theorem visibleToFrobenius_frobeniusToVisible
    (address : VisibleFrobeniusAddress) :
    visibleToFrobenius
        (frobeniusToVisible address) =
      address := by

  rcases address with
    ⟨line, step⟩

  apply Prod.ext

  · exact
      visibleAddress_ofAddressRole
        line
        (forcedRoleOfStep step)

  · simp [
      visibleToFrobenius,
      frobeniusToVisible
    ]

/--
The intrinsic 21-state visible quotient is canonically equivalent to
seven Fano addresses times the three-step Frobenius orbit.
-/
noncomputable def visibleQuotientEquivFrobenius :
    GlyphObservationQuotient ≃
      VisibleFrobeniusAddress where

  toFun :=
    visibleToFrobenius

  invFun :=
    frobeniusToVisible

  left_inv :=
    frobeniusToVisible_visibleToFrobenius

  right_inv :=
    visibleToFrobenius_frobeniusToVisible

/--
The intrinsic visible quotient cardinality factors as seven Fano
addresses times three Frobenius steps.
-/
theorem card_visible_frobenius :
    Fintype.card GlyphObservationQuotient =
      Fintype.card Fano.Point
        *
      Fintype.card FrobeniusOrbit.Step := by

  calc
    Fintype.card GlyphObservationQuotient =
        Fintype.card VisibleFrobeniusAddress := by

      exact
        Fintype.card_congr
          visibleQuotientEquivFrobenius

    _ =
        Fintype.card Fano.Point
          *
        Fintype.card FrobeniusOrbit.Step := by

      exact
        Fintype.card_prod
          Fano.Point
          FrobeniusOrbit.Step

/--
The intrinsic visible quotient therefore has cardinality
`7 × 3 = 21`.
-/
theorem card_visible_frobenius_twenty_one :
    Fintype.card GlyphObservationQuotient =
      21 := by

  exact
    card_glyphObservationQuotient

/--
Capstone theorem.

The forced three-role carrier is dynamically the Frobenius orbit, and
the intrinsic visible glyph quotient is canonically the product of the
forced Fano carrier with that orbit.
-/
theorem frobenius_is_forced_role_dynamics :
    Nonempty
      (
        ForcedRole ≃
          FrobeniusOrbit.Step
      )
      ∧
    (∀ role,
      stepOfForcedRole
          (nextRole role) =
        FrobeniusOrbit.next
          (stepOfForcedRole role))
      ∧
    Nonempty
      (
        GlyphObservationQuotient ≃
          Fano.Point × FrobeniusOrbit.Step
      )
      ∧
    Fintype.card GlyphObservationQuotient =
        21 := by

  exact
    ⟨
      ⟨forcedRoleEquivFrobenius⟩,
      stepOfForcedRole_nextRole,
      ⟨visibleQuotientEquivFrobenius⟩,
      card_visible_frobenius_twenty_one
    ⟩

end GlyphForcingFrobeniusIdentification

#check GlyphForcingFrobeniusIdentification.nextRole
#check GlyphForcingFrobeniusIdentification.stepOfForcedRole
#check GlyphForcingFrobeniusIdentification.forcedRoleOfStep
#check GlyphForcingFrobeniusIdentification.forcedRoleEquivFrobenius
#check GlyphForcingFrobeniusIdentification.stepOfForcedRole_nextRole
#check GlyphForcingFrobeniusIdentification.forcedRole_value_next
#check GlyphForcingFrobeniusIdentification.forcedRole_values
#check GlyphForcingFrobeniusIdentification.agrees_with_existing_role_bridge
#check GlyphForcingFrobeniusIdentification.VisibleFrobeniusAddress
#check GlyphForcingFrobeniusIdentification.visibleQuotientEquivFrobenius
#check GlyphForcingFrobeniusIdentification.card_visible_frobenius
#check GlyphForcingFrobeniusIdentification.frobenius_is_forced_role_dynamics
