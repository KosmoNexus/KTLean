import KTLean.DirectedTkairos

/-!
# A Concrete Moving Directed-Tkairos Witness

`DirectedTkairos` proved that temporal direction is
recoverable from event orientation whenever a routed token
moves.

This module constructs one explicit moving token and proves
that all four temporal-information views are realized
distinctly at that witness.

The four views are:

    forward  × visible
    forward  × escrow
    recovered × visible
    recovered × escrow

The current involutive state map still uses the same
operation for step and recovery. Their distinction is
carried by the orientation of the directed event.
-/

namespace DirectedTkairosWitness


/-
## Concrete visible packets
-/

/--
A concrete visible packet in the first Cayley-Dickson
block carrying Fano point zero.
-/
def leftVisible :
    TkairosLocality.VisiblePacket :=

  (
    CayleyDicksonQuaternion.Block.first,
    (0 : Fano.Point)
  )


/--
A distinct concrete visible packet in the second
Cayley-Dickson block carrying Fano point one.
-/
def rightVisible :
    TkairosLocality.VisiblePacket :=

  (
    CayleyDicksonQuaternion.Block.second,
    (1 : Fano.Point)
  )


/--
The two visible packets are distinct.
-/
theorem leftVisible_ne_rightVisible :

    leftVisible ≠ rightVisible := by

  decide


/-
## Concrete escrow addresses
-/

/--
The first concrete Pascal route address.
-/
def leftAddress :
    BraidedQuaternion.PascalAddress where

  row := 0
  column := 0


/--
The second concrete Pascal route address.
-/
def rightAddress :
    BraidedQuaternion.PascalAddress where

  row := 1
  column := 0


/--
The two route addresses are distinct.
-/
theorem leftAddress_ne_rightAddress :

    leftAddress ≠ rightAddress := by

  decide


/-
## Concrete moving token
-/

/--
A concrete routed token with distinct visible packets and
distinct escrow addresses.
-/
def movingToken :
    RoutedTokenization.Token :=

  (
    (
      leftVisible,
      rightVisible
    ),

    (
      leftAddress,
      rightAddress
    )
  )


/--
One token step exchanges both the visible packets and the
escrow addresses.
-/
theorem tokenStep_movingToken :

    RoutedTokenization.tokenStep movingToken =

      (
        (
          rightVisible,
          leftVisible
        ),

        (
          rightAddress,
          leftAddress
        )
      ) := by

  rfl


/--
The explicit token is not a fixed point.
-/
theorem movingToken_isMoving :

    DirectedTkairos.IsMoving movingToken := by

  unfold DirectedTkairos.IsMoving

  rw [tokenStep_movingToken]

  intro hequal

  have hvisible :
      rightVisible =
        leftVisible :=

    congrArg
      (fun token => token.1.1)
      hequal

  exact
    leftVisible_ne_rightVisible
      hvisible.symm


/--
The routed witness contains at least one moving token.
-/
theorem moving_token_exists :

    ∃ token : RoutedTokenization.Token,

      DirectedTkairos.IsMoving token := by

  exact
    ⟨
      movingToken,
      movingToken_isMoving
    ⟩


/-
## Directed temporal realization
-/

/--
Forward and recovered events are distinct at the concrete
moving token.
-/
theorem concrete_forward_ne_recovered :

    DirectedTkairos.forwardEvent movingToken ≠

      DirectedTkairos.recoveredEvent movingToken := by

  exact
    DirectedTkairos.forwardEvent_ne_recoveredEvent
      movingToken
      movingToken_isMoving


/--
Temporal direction is injectively represented by event
orientation at the concrete moving token.
-/
theorem concrete_direction_injective :

    Function.Injective
      (
        fun direction =>
          DirectedTkairos.eventOfDirection
            direction
            movingToken
      ) := by

  exact
    DirectedTkairos.direction_injective_at_moving_token
      movingToken
      movingToken_isMoving


/-
## Realized fourfold views
-/

/--
A realized view records:

1. the oriented event selected by temporal direction;
2. the selected information phase.

The phase remains explicit because it determines whether
the visible or escrow component is read from the event.
-/
abbrev RealizedView :=

  DirectedTkairos.Event ×
    GlyphState.InformationPhase
/--
Realize one abstract four-state view at a token.
-/
def realizeView
    (token : RoutedTokenization.Token)
    (view : DirectedTkairos.View) :
    RealizedView :=

  (
    DirectedTkairos.eventOfDirection
      view.direction
      token,

    view.phase
  )


/--
A directed view is determined by its temporal direction
and information phase.
-/
theorem View.ext
    {left right : DirectedTkairos.View}
    (hdirection :
      left.direction =
        right.direction)
    (hphase :
      left.phase =
        right.phase) :

    left = right := by

  cases left

  cases right

  cases hdirection
  cases hphase

  rfl


/--
At any moving token, realization of the four semantic
views is injective.
-/
theorem realizeView_injective_at_moving
    (token : RoutedTokenization.Token)
    (hmoving :
      DirectedTkairos.IsMoving token) :

    Function.Injective
      (realizeView token) := by

  intro left right hrealized

  have hevent :

      DirectedTkairos.eventOfDirection
          left.direction
          token =

        DirectedTkairos.eventOfDirection
          right.direction
          token :=

    congrArg Prod.fst hrealized

  have hphase :
      left.phase =
        right.phase :=

    congrArg Prod.snd hrealized

  have hdirection :
      left.direction =
        right.direction :=

    DirectedTkairos.direction_injective_at_moving_token
      token
      hmoving
      hevent

  exact
    View.ext
      hdirection
      hphase


/--
All four views are distinctly realized at the concrete
moving token.
-/
theorem concrete_realizeView_injective :

    Function.Injective
      (realizeView movingToken) := by

  exact
    realizeView_injective_at_moving
      movingToken
      movingToken_isMoving


/--
The realized-view image at the concrete token contains
exactly four elements.
-/
noncomputable def realizedViews :
    Finset RealizedView := by

  classical

  exact
    Finset.univ.image
      (realizeView movingToken)

/--
The concrete moving token realizes exactly four distinct
directed information views.
-/
theorem realizedViews_card :

    realizedViews.card = 4 := by

  classical

  unfold realizedViews

  rw [
    Finset.card_image_of_injective
      _
      concrete_realizeView_injective
  ]

  exact
    DirectedTkairos.view_card


/-
## Explicit canonical views
-/

/--
Forward-visible view.
-/
def forwardVisibleView :
    DirectedTkairos.View where

  direction :=
    GlyphState.TemporalDirection.forward

  phase :=
    GlyphState.InformationPhase.visible


/--
Forward-escrow view.
-/
def forwardEscrowView :
    DirectedTkairos.View where

  direction :=
    GlyphState.TemporalDirection.forward

  phase :=
    GlyphState.InformationPhase.escrow


/--
Recovered-visible view.
-/
def recoveredVisibleView :
    DirectedTkairos.View where

  direction :=
    GlyphState.TemporalDirection.recovered

  phase :=
    GlyphState.InformationPhase.visible


/--
Recovered-escrow view.
-/
def recoveredEscrowView :
    DirectedTkairos.View where

  direction :=
    GlyphState.TemporalDirection.recovered

  phase :=
    GlyphState.InformationPhase.escrow


/--
The four canonical abstract views are pairwise separated
through their concrete realization.
-/
theorem canonical_views_distinct :

    realizeView movingToken forwardVisibleView ≠
        realizeView movingToken forwardEscrowView
      ∧

    realizeView movingToken forwardVisibleView ≠
        realizeView movingToken recoveredVisibleView
      ∧

    realizeView movingToken forwardVisibleView ≠
        realizeView movingToken recoveredEscrowView
      ∧

    realizeView movingToken forwardEscrowView ≠
        realizeView movingToken recoveredVisibleView
      ∧

    realizeView movingToken forwardEscrowView ≠
        realizeView movingToken recoveredEscrowView
      ∧

    realizeView movingToken recoveredVisibleView ≠
        realizeView movingToken recoveredEscrowView := by

  constructor

  · intro hequal

    have hphase :=
      congrArg Prod.snd hequal

    change
      GlyphState.InformationPhase.visible =
        GlyphState.InformationPhase.escrow
      at hphase

    cases hphase

  constructor

  · intro hequal

    have hevent :=
      congrArg Prod.fst hequal

    exact
      concrete_forward_ne_recovered
        hevent

  constructor

  · intro hequal

    have hevent :=
      congrArg Prod.fst hequal

    exact
      concrete_forward_ne_recovered
        hevent

  constructor

  · intro hequal

    have hevent :=
      congrArg Prod.fst hequal

    exact
      concrete_forward_ne_recovered
        hevent

  constructor

  · intro hequal

    have hevent :=
      congrArg Prod.fst hequal

    exact
      concrete_forward_ne_recovered
        hevent

  · intro hequal

    have hphase :=
      congrArg Prod.snd hequal

    change
      GlyphState.InformationPhase.visible =
        GlyphState.InformationPhase.escrow
      at hphase

    cases hphase

/-
## Formal conclusion
-/

/--
The four-state semantic fiber is concretely realized:

- two temporal orientations are distinguished by directed
  event order;
- two information phases are distinguished by their phase
  tags;
- their product gives four distinct realized views.
-/
theorem fourfold_semantic_realization :

    ∃ token : RoutedTokenization.Token,

      DirectedTkairos.IsMoving token
        ∧

      Function.Injective
        (realizeView token)
        ∧

      realizedViews.card = 4 := by

  exact
    ⟨
      movingToken,
      movingToken_isMoving,
      concrete_realizeView_injective,
      realizedViews_card
    ⟩


end DirectedTkairosWitness
