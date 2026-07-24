import KTLean.GlyphForcingOrientation

/-!
# The Six Oriented Local Roles

## Formal status

**Level 1 — Derived six-state framed carrier and its observable
two-to-one projection.**

The preceding modules forced:

* three active positions in a local woven triad;
* two reversible traversal directions.

Their product therefore contains six framed local states.

This module proves something stronger than the cardinality statement.

The selected-role observable forgets part of the frame. Every visible
role has exactly two framed realizations. These realizations are paired
by simultaneously:

1. reversing the triadic role;
2. reversing the traversal orientation.

Thus the six oriented roles form a fixed-point-free double cover of
the three visible local sites.

This is the first indication that the glyph's orientation coordinate
is not merely an independent label. It is part of a hidden framing
whose observable projection has a canonical two-element fiber.
-/

namespace GlyphForcingOrientedRole

open GlyphForcingTriadicRole
open GlyphForcingOrientation

/--
A fully framed local role consists of one forced triadic position and
one forced traversal orientation.
-/
abbrev OrientedRole :=
  ForcedRole × ForcedOrientation

/--
Reverse the traversal direction.
-/
def reverseOrientation :
    ForcedOrientation →
      ForcedOrientation

  | .forward =>
      .reverse

  | .reverse =>
      .forward

/--
The visible role selected by a framed local state.
-/
def selectedRole
    (state : OrientedRole) :
    ForcedRole :=

  actOnRole
    state.2
    state.1

/--
The canonical hidden companion of an oriented role.

Both the underlying role and the orientation are reversed.
-/
def companion
    (state : OrientedRole) :
    OrientedRole :=

  (
    actOnRole
      .reverse
      state.1,
    reverseOrientation
      state.2
  )

/--
Orientation reversal is involutive.
-/
theorem reverseOrientation_involutive :
    Function.Involutive
      reverseOrientation := by

  intro orientation
  cases orientation <;>
    rfl

/--
The companion operation is involutive.
-/
theorem companion_involutive :
    Function.Involutive
      companion := by

  intro state

  rcases state with
    ⟨role, orientation⟩

  cases orientation <;>
    fin_cases role <;>
    rfl

/--
No framed local state is its own companion.
-/
theorem companion_ne
    (state : OrientedRole) :
    companion state ≠
      state := by

  rcases state with
    ⟨role, orientation⟩

  cases orientation <;>
    fin_cases role <;>
    decide

/--
Companion states have the same visible selected role.
-/
theorem selectedRole_companion
    (state : OrientedRole) :
    selectedRole
        (companion state) =
      selectedRole
        state := by

  rcases state with
    ⟨role, orientation⟩

  cases orientation <;>
    fin_cases role <;>
    rfl

/--
Two framed states have the same selected role exactly when they are
equal or are canonical companions.
-/
theorem selectedRole_eq_iff
    (left right : OrientedRole) :
    selectedRole left =
        selectedRole right
      ↔
    right = left
      ∨
    right = companion left := by

  rcases left with
    ⟨leftRole, leftOrientation⟩

  rcases right with
    ⟨rightRole, rightOrientation⟩

  cases leftOrientation <;>
    cases rightOrientation <;>
    fin_cases leftRole <;>
    fin_cases rightRole <;>
    decide

/--
Every selected-role fiber consists exactly of one framed state and its
companion.
-/
theorem selectedRole_fiber
    (state candidate : OrientedRole) :
    selectedRole candidate =
        selectedRole state
      ↔
    candidate = state
      ∨
    candidate = companion state := by

  constructor

  · intro hSelected

    have h :=
      (
        selectedRole_eq_iff
          state
          candidate
      ).1
        hSelected.symm

    rcases h with
      hSame | hCompanion

    · exact
        Or.inl
          hSame

    · exact
        Or.inr
          hCompanion

  · intro hCandidate

    rcases hCandidate with
      hSame | hCompanion

    · subst candidate
      rfl

    · subst candidate

      exact
        selectedRole_companion
          state

/--
The selected-role projection is surjective.
-/
theorem selectedRole_surjective :
    Function.Surjective
      selectedRole := by

  intro role

  exact
    ⟨
      (role, .forward),
      rfl
    ⟩

/--
The selected-role projection is not injective.
-/
theorem selectedRole_not_injective :
    ¬ Function.Injective
        selectedRole := by

  intro hInjective

  let state : OrientedRole :=
    (0, .forward)

  have hEqual :
      selectedRole
          (companion state) =
        selectedRole
          state :=
    selectedRole_companion
      state

  have hState :
      companion state =
        state :=
    hInjective
      hEqual

  exact
    companion_ne state
      hState

/--
The oriented-role carrier contains six elements.
-/
theorem card_orientedRole :
    Fintype.card OrientedRole =
      6 := by

  calc
    Fintype.card OrientedRole =
        Fintype.card ForcedRole
          *
        Fintype.card ForcedOrientation := by
      exact
        Fintype.card_prod
          ForcedRole
          ForcedOrientation

    _ =
        3 * 2 := by
      rw [
        card_forcedRole,
        card_forcedOrientation
      ]

    _ =
        6 := by
      decide

/--
Each framed state and its companion are distinct members of the same
observable fiber.
-/
theorem companion_pair_in_fiber
    (state : OrientedRole) :
    state ≠ companion state
      ∧
    selectedRole state =
      selectedRole
        (companion state) := by

  exact
    ⟨
      (companion_ne state).symm,
      (selectedRole_companion state).symm
    ⟩

/--
Every visible role has at least two distinct framed realizations.
-/
theorem every_role_has_two_frames
    (role : ForcedRole) :
    ∃ first second : OrientedRole,
      first ≠ second
        ∧
      selectedRole first =
        role
        ∧
      selectedRole second =
        role := by

  let first : OrientedRole :=
    (role, .forward)

  let second : OrientedRole :=
    companion first

  refine
    ⟨
      first,
      second,
      ?_,
      ?_,
      ?_
    ⟩

  · exact
      (companion_ne first).symm

  · rfl

  · calc
      selectedRole second =
          selectedRole first := by
        exact
          selectedRole_companion
            first

      _ =
          role := by
        rfl

/--
Capstone statement for the local sixfold structure.

The six framed states form a fixed-point-free involutive double cover
of the three visible roles.
-/
theorem oriented_roles_form_double_cover :
    Fintype.card OrientedRole =
        6
      ∧
    Function.Involutive companion
      ∧
    (∀ state, companion state ≠ state)
      ∧
    (∀ state,
      selectedRole (companion state) =
        selectedRole state)
      ∧
    Function.Surjective selectedRole
      ∧
    ¬ Function.Injective selectedRole := by

  exact
    ⟨
      card_orientedRole,
      companion_involutive,
      companion_ne,
      selectedRole_companion,
      selectedRole_surjective,
      selectedRole_not_injective
    ⟩

end GlyphForcingOrientedRole

#check GlyphForcingOrientedRole.OrientedRole
#check GlyphForcingOrientedRole.reverseOrientation
#check GlyphForcingOrientedRole.selectedRole
#check GlyphForcingOrientedRole.companion
#check GlyphForcingOrientedRole.companion_involutive
#check GlyphForcingOrientedRole.companion_ne
#check GlyphForcingOrientedRole.selectedRole_companion
#check GlyphForcingOrientedRole.selectedRole_eq_iff
#check GlyphForcingOrientedRole.selectedRole_surjective
#check GlyphForcingOrientedRole.selectedRole_not_injective
#check GlyphForcingOrientedRole.card_orientedRole
#check GlyphForcingOrientedRole.every_role_has_two_frames
#check GlyphForcingOrientedRole.oriented_roles_form_double_cover
