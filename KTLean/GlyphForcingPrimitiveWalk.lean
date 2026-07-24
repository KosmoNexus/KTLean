import KTLean.GlyphForcingOrientedRole

/-!
# Forced Primitive Fano Walks

## Formal status

**Level 1 — The forced 42-state framed carrier and its 21-state
observable quotient.**

The preceding forcing chain established:

* seven forced Fano addresses;
* three local active positions;
* a binary reversible orientation;
* six oriented roles forming a fixed-point-free double cover of the
  three visible roles.

A primitive framed local walk consists of:

    Fano address × oriented role.

Its full carrier therefore contains

    7 × 6 = 42

states.

However, forgetting the hidden frame produces only

    Fano address × visible role,

which contains

    7 × 3 = 21

observable states.

Every observable state has exactly two framed realizations related by
the canonical companion involution.

Thus the forced 42-state carrier is naturally a double cover of a
21-state visible operation space.
-/

namespace GlyphForcingPrimitiveWalk

open AdmissibleOperation
open GlyphForcingTriadicRole
open GlyphForcingOrientation
open GlyphForcingOrientedRole

/--
A primitive framed local walk consists of a forced Fano address and
one oriented local role.
-/
abbrev PrimitiveWalk :=
  Fano.Point × OrientedRole

/--
The observable part of a primitive walk retains its Fano address and
selected visible role, but forgets the hidden frame.
-/
abbrev VisibleWalk :=
  Fano.Point × ForcedRole

/--
Forget the hidden framing of a primitive walk.
-/
def observe
    (walk : PrimitiveWalk) :
    VisibleWalk :=

  (
    walk.1,
    selectedRole walk.2
  )

/--
Apply the canonical companion involution while retaining the same Fano
address.
-/
def companion
    (walk : PrimitiveWalk) :
    PrimitiveWalk :=

  (
    walk.1,
    GlyphForcingOrientedRole.companion walk.2
  )

/--
The primitive-walk companion operation is involutive.
-/
theorem companion_involutive :
    Function.Involutive
      companion := by

  intro walk

  rcases walk with
    ⟨address, state⟩

  apply Prod.ext

  · rfl

  · exact
      GlyphForcingOrientedRole.companion_involutive
        state

/--
No primitive walk is equal to its companion.
-/
theorem companion_ne
    (walk : PrimitiveWalk) :
    companion walk ≠
      walk := by

  intro hEqual

  have hState :
      GlyphForcingOrientedRole.companion walk.2 =
        walk.2 :=
    congrArg
      Prod.snd
      hEqual

  exact
    GlyphForcingOrientedRole.companion_ne
      walk.2
      hState

/--
A primitive walk and its companion have the same observable readout.
-/
theorem observe_companion
    (walk : PrimitiveWalk) :
    observe
        (companion walk) =
      observe
        walk := by

  apply Prod.ext

  · rfl

  · exact
      selectedRole_companion
        walk.2

/--
Two primitive walks have equal observable readout exactly when one is
the other or its canonical companion.
-/
theorem observe_eq_iff
    (left right : PrimitiveWalk) :
    observe left =
        observe right
      ↔
    right = left
      ∨
    right = companion left := by

  constructor

  · intro hObserved

    have hAddress :
        right.1 =
          left.1 := by
      exact
        (
          congrArg
            Prod.fst
            hObserved
        ).symm

    have hRole :
        selectedRole right.2 =
          selectedRole left.2 := by
      exact
        (
          congrArg
            Prod.snd
            hObserved
        ).symm

    have hFrames :=
      (
        selectedRole_eq_iff
          left.2
          right.2
      ).1
        hRole.symm

    rcases hFrames with
      hSame | hCompanion

    · exact
        Or.inl
          (
            Prod.ext
              hAddress
              hSame
          )

    · exact
        Or.inr
          (
            Prod.ext
              hAddress
              hCompanion
          )

  · intro hWalks

    rcases hWalks with
      hSame | hCompanion

    · subst right
      rfl

    · subst right

      exact
        (
          observe_companion
            left
        ).symm

/--
Every visible walk has a primitive framed realization.
-/
theorem observe_surjective :
    Function.Surjective
      observe := by

  intro visible

  exact
    ⟨
      (
        visible.1,
        (
          visible.2,
          ForcedOrientation.forward
        )
      ),
      rfl
    ⟩

/--
The observable projection is not injective.
-/
theorem observe_not_injective :
    ¬ Function.Injective
        observe := by

  intro hInjective

  let walk : PrimitiveWalk :=
    (
      0,
      (
        0,
        ForcedOrientation.forward
      )
    )

  have hEqual :
      observe
          (companion walk) =
        observe
          walk :=
    observe_companion
      walk

  have hWalk :
      companion walk =
        walk :=
    hInjective
      hEqual

  exact
    companion_ne walk
      hWalk

/--
The forced primitive-walk carrier contains exactly 42 states.
-/
theorem card_primitiveWalk :
    Fintype.card PrimitiveWalk =
      42 := by

  calc
    Fintype.card PrimitiveWalk =
        Fintype.card Fano.Point
          *
        Fintype.card OrientedRole := by
      exact
        Fintype.card_prod
          Fano.Point
          OrientedRole

    _ =
        7 * 6 := by
      rw [
        AdmissibleOperation.fanoPoint_card,
        card_orientedRole
      ]

    _ =
        42 := by
      decide

/--
The visible address–site carrier contains exactly 21 states.
-/
theorem card_visibleWalk :
    Fintype.card VisibleWalk =
      21 := by

  calc
    Fintype.card VisibleWalk =
        Fintype.card Fano.Point
          *
        Fintype.card ForcedRole := by
      exact
        Fintype.card_prod
          Fano.Point
          ForcedRole

    _ =
        7 * 3 := by
      rw [
        AdmissibleOperation.fanoPoint_card,
        card_forcedRole
      ]

    _ =
        21 := by
      decide

/--
Each primitive walk and its companion are distinct members of the same
observable fiber.
-/
theorem companion_pair_in_fiber
    (walk : PrimitiveWalk) :
    walk ≠ companion walk
      ∧
    observe walk =
      observe
        (companion walk) := by

  exact
    ⟨
      (companion_ne walk).symm,
      (observe_companion walk).symm
    ⟩

/--
Every visible walk has two distinct primitive framed realizations.
-/
theorem every_visibleWalk_has_two_frames
    (visible : VisibleWalk) :
    ∃ first second : PrimitiveWalk,
      first ≠ second
        ∧
      observe first =
        visible
        ∧
      observe second =
        visible := by

  let first : PrimitiveWalk :=
    (
      visible.1,
      (
        visible.2,
        ForcedOrientation.forward
      )
    )

  let second : PrimitiveWalk :=
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
      observe second =
          observe first := by
        exact
          observe_companion
            first

      _ =
          visible := by
        rfl

/--
The fiber of the observable projection consists exactly of a primitive
walk and its companion.
-/
theorem observe_fiber
    (walk candidate : PrimitiveWalk) :
    observe candidate =
        observe walk
      ↔
    candidate = walk
      ∨
    candidate = companion walk := by

  constructor

  · intro hObserved

    exact
      (
        observe_eq_iff
          walk
          candidate
      ).1
        hObserved.symm

  · intro hCandidate

    have h :=
      (
        observe_eq_iff
          walk
          candidate
      ).2
        hCandidate

    exact
      h.symm

/--
The 42 primitive framed walks form a fixed-point-free double cover of
the 21 visible address–site operations.
-/
theorem primitive_walks_form_double_cover :
    Fintype.card PrimitiveWalk =
        42
      ∧
    Fintype.card VisibleWalk =
        21
      ∧
    Function.Involutive companion
      ∧
    (∀ walk, companion walk ≠ walk)
      ∧
    (∀ walk,
      observe (companion walk) =
        observe walk)
      ∧
    Function.Surjective observe
      ∧
    ¬ Function.Injective observe := by

  exact
    ⟨
      card_primitiveWalk,
      card_visibleWalk,
      companion_involutive,
      companion_ne,
      observe_companion,
      observe_surjective,
      observe_not_injective
    ⟩

end GlyphForcingPrimitiveWalk

#check GlyphForcingPrimitiveWalk.PrimitiveWalk
#check GlyphForcingPrimitiveWalk.VisibleWalk
#check GlyphForcingPrimitiveWalk.observe
#check GlyphForcingPrimitiveWalk.companion
#check GlyphForcingPrimitiveWalk.companion_involutive
#check GlyphForcingPrimitiveWalk.companion_ne
#check GlyphForcingPrimitiveWalk.observe_companion
#check GlyphForcingPrimitiveWalk.observe_eq_iff
#check GlyphForcingPrimitiveWalk.observe_surjective
#check GlyphForcingPrimitiveWalk.observe_not_injective
#check GlyphForcingPrimitiveWalk.card_primitiveWalk
#check GlyphForcingPrimitiveWalk.card_visibleWalk
#check GlyphForcingPrimitiveWalk.every_visibleWalk_has_two_frames
#check GlyphForcingPrimitiveWalk.observe_fiber
#check GlyphForcingPrimitiveWalk.primitive_walks_form_double_cover
