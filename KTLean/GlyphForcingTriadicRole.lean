import KTLean.YangBaxterForcingCapstone
import KTLean.AdmissibleOperation
import Mathlib.Tactic.FinCases

/-!
# Forcing the Three Local Triadic Roles

## Formal status

**Level 1 — Canonical role carrier and identification with the
existing role implementation.**

The forced Fano–Pascal weave acts locally on a three-channel state.

Before assigning any semantic names, the local operation has exactly
three possible active sites:

    position 0
    position 1
    position 2.

This module takes `Fin 3` as the canonical carrier of those positions
and proves that it is equivalent to the existing role implementation

    anchor
    successor
    completion.

The threefold multiplicity is therefore inherited from the arity of
the local woven state. It is not introduced here by the glyph
definition.

No orientation and no glyph count enters this module.
-/

namespace GlyphForcingTriadicRole

open AdmissibleOperation

/--
The canonical carrier of active positions in a three-channel local
operation.
-/
abbrev ForcedRole :=
  Fin 3

/--
Interpret a canonical three-channel position as an existing triadic
role.
-/
def toExistingRole :
    ForcedRole →
      TriadicRole

  | 0 =>
      .anchor

  | 1 =>
      .successor

  | 2 =>
      .completion

/--
Recover the canonical position represented by an existing triadic
role.
-/
def fromExistingRole :
    TriadicRole →
      ForcedRole

  | .anchor =>
      0

  | .successor =>
      1

  | .completion =>
      2

/--
Recovering a canonical position after interpreting it as an existing
role returns the original position.
-/
@[simp]
theorem fromExistingRole_toExistingRole
    (role : ForcedRole) :
    fromExistingRole
        (toExistingRole role) =
      role := by

  fin_cases role <;>
    rfl

/--
Interpreting a recovered existing role returns the original role.
-/
@[simp]
theorem toExistingRole_fromExistingRole
    (role : TriadicRole) :
    toExistingRole
        (fromExistingRole role) =
      role := by

  cases role <;>
    rfl

/--
The canonical three-channel role carrier is equivalent to the existing
triadic-role implementation.
-/
def forcedRoleEquivExisting :
    ForcedRole ≃
      TriadicRole where

  toFun :=
    toExistingRole

  invFun :=
    fromExistingRole

  left_inv :=
    fromExistingRole_toExistingRole

  right_inv :=
    toExistingRole_fromExistingRole

/--
The forward map of the equivalence is the explicit role
interpretation.
-/
@[simp]
theorem forcedRoleEquivExisting_apply
    (role : ForcedRole) :
    forcedRoleEquivExisting role =
      toExistingRole role := by

  rfl

/--
The canonical active-position carrier has exactly three elements.
-/
theorem card_forcedRole :
    Fintype.card ForcedRole =
      3 := by

  exact
    Fintype.card_fin 3

/--
The existing triadic-role carrier has three elements because it is
equivalent to the canonical three-channel position carrier.
-/
theorem card_existingRole_from_forced :
    Fintype.card TriadicRole =
      3 := by

  calc
    Fintype.card TriadicRole =
        Fintype.card ForcedRole := by
      exact
        Fintype.card_congr
          forcedRoleEquivExisting.symm

    _ =
        3 := by
      exact
        card_forcedRole

/--
The canonical role interpretation is injective.
-/
theorem toExistingRole_injective :
    Function.Injective
      toExistingRole := by

  exact
    forcedRoleEquivExisting.injective

/--
Every existing triadic role is represented by one canonical
three-channel position.
-/
theorem toExistingRole_surjective :
    Function.Surjective
      toExistingRole := by

  exact
    forcedRoleEquivExisting.surjective

/--
Every existing triadic role has a unique canonical active position.
-/
theorem existsUnique_forcedRole
    (role : TriadicRole) :
    ∃! forcedRole : ForcedRole,
      toExistingRole forcedRole =
        role := by

  refine
    ⟨
      fromExistingRole role,
      ?_,
      ?_
    ⟩

  · exact
      toExistingRole_fromExistingRole
        role

  · intro otherRole hOther

    exact
      toExistingRole_injective
        (
          hOther.trans
            (
              toExistingRole_fromExistingRole
                role
            ).symm
        )

/--
The three canonical roles are pairwise distinct after interpretation.
-/
theorem forced_roles_distinct :
    toExistingRole 0 ≠ toExistingRole 1
      ∧
    toExistingRole 0 ≠ toExistingRole 2
      ∧
    toExistingRole 1 ≠ toExistingRole 2 := by

  decide

/--
There are no local active-site roles beyond the three canonical
positions.
-/
theorem existing_role_exhausted
    (role : TriadicRole) :
    role = toExistingRole 0
      ∨
    role = toExistingRole 1
      ∨
    role = toExistingRole 2 := by

  cases role

  · exact Or.inl rfl

  · exact Or.inr (Or.inl rfl)

  · exact Or.inr (Or.inr rfl)

end GlyphForcingTriadicRole

#check GlyphForcingTriadicRole.ForcedRole
#check GlyphForcingTriadicRole.toExistingRole
#check GlyphForcingTriadicRole.fromExistingRole
#check GlyphForcingTriadicRole.forcedRoleEquivExisting
#check GlyphForcingTriadicRole.card_forcedRole
#check GlyphForcingTriadicRole.card_existingRole_from_forced
#check GlyphForcingTriadicRole.toExistingRole_injective
#check GlyphForcingTriadicRole.toExistingRole_surjective
#check GlyphForcingTriadicRole.existsUnique_forcedRole
#check GlyphForcingTriadicRole.forced_roles_distinct
#check GlyphForcingTriadicRole.existing_role_exhausted
