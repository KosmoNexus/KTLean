import KTLean.GlyphStateDynamics

/-!
# Directed Tkairos Transitions

For the current routed witness, forward step and recovery
are the same state map because token evolution is
involutive.

Temporal orientation nevertheless survives at the level
of directed transitions:

    forward event:
        token → tokenStep token

    recovered event:
        tokenStep token → token

These ordered transitions are distinct whenever the token
is not a fixed point.

Thus temporal direction should be carried by oriented
Tkairos events rather than inferred solely from the
underlying involutive state map.
-/

namespace DirectedTkairos


/-
## Directed token events
-/

/--
A directed token event is an ordered source-target pair.
-/
abbrev Event :=

  RoutedTokenization.Token ×
    RoutedTokenization.Token


/--
The forward Tkairos event beginning at a token.
-/
def forwardEvent
    (token : RoutedTokenization.Token) :
    Event :=

  (
    token,
    RoutedTokenization.tokenStep token
  )


/--
The recovered Tkairos event traversing the same transition
in the opposite direction.
-/
def recoveredEvent
    (token : RoutedTokenization.Token) :
    Event :=

  (
    RoutedTokenization.tokenStep token,
    token
  )


/--
Reverse the orientation of a directed event.
-/
def reverseEvent
    (event : Event) :
    Event :=

  (
    event.2,
    event.1
  )


/--
Event reversal is involutive.
-/
theorem reverseEvent_involutive :

    Function.Involutive reverseEvent := by

  intro event

  rcases event with
    ⟨source, target⟩

  rfl


/--
The recovered event is exactly the reversal of the
forward event.
-/
theorem recoveredEvent_eq_reverse_forwardEvent
    (token : RoutedTokenization.Token) :

    recoveredEvent token =

      reverseEvent
        (forwardEvent token) := by

  rfl


/--
The forward event is exactly the reversal of the recovered
event.
-/
theorem forwardEvent_eq_reverse_recoveredEvent
    (token : RoutedTokenization.Token) :

    forwardEvent token =

      reverseEvent
        (recoveredEvent token) := by

  rfl


/-
## Lawfulness
-/

/--
A directed event follows one lawful forward token step.
-/
def IsForwardLawful
    (event : Event) :
    Prop :=

  event.2 =
    RoutedTokenization.tokenStep event.1


/--
A directed event follows one lawful recovered token step.
-/
def IsRecoveredLawful
    (event : Event) :
    Prop :=

  event.1 =
    RoutedTokenization.tokenStep event.2


/--
Every canonical forward event is forward-lawful.
-/
theorem forwardEvent_lawful
    (token : RoutedTokenization.Token) :

    IsForwardLawful
      (forwardEvent token) := by

  rfl


/--
Every canonical recovered event is recovered-lawful.
-/
theorem recoveredEvent_lawful
    (token : RoutedTokenization.Token) :

    IsRecoveredLawful
      (recoveredEvent token) := by

  rfl


/--
Because token evolution is involutive, every canonical
forward event is also lawful when read backward.
-/
theorem forwardEvent_recoveredLawful
    (token : RoutedTokenization.Token) :

    IsRecoveredLawful
      (forwardEvent token) := by

  change
    token =
      RoutedTokenization.tokenStep
        (
          RoutedTokenization.tokenStep token
        )

  exact
    (
      RoutedTokenization.tokenStep_involutive
        token
    ).symm


/--
Because token evolution is involutive, every canonical
recovered event is also lawful when read forward.
-/
theorem recoveredEvent_forwardLawful
    (token : RoutedTokenization.Token) :

    IsForwardLawful
      (recoveredEvent token) := by

  change
    token =
      RoutedTokenization.tokenStep
        (
          RoutedTokenization.tokenStep token
        )

  exact
    (
      RoutedTokenization.tokenStep_involutive
        token
    ).symm


/-
## Temporal distinction
-/

/--
A token is moving when one lawful step changes it.
-/
def IsMoving
    (token : RoutedTokenization.Token) :
    Prop :=

  RoutedTokenization.tokenStep token ≠
    token


/--
At every moving token, the forward and recovered directed
events are distinct.
-/
theorem forwardEvent_ne_recoveredEvent
    (token : RoutedTokenization.Token)
    (hmoving : IsMoving token) :

    forwardEvent token ≠
      recoveredEvent token := by

  intro hevents

  have hsource :

      token =
        RoutedTokenization.tokenStep token :=

    congrArg Prod.fst hevents

  exact
    hmoving
      hsource.symm


/--
At a fixed token, forward and recovered events collapse to
the same stationary event.
-/
theorem forwardEvent_eq_recoveredEvent_of_fixed
    (token : RoutedTokenization.Token)
    (hfixed :

      RoutedTokenization.tokenStep token =
        token) :

    forwardEvent token =
      recoveredEvent token := by

  unfold forwardEvent
  unfold recoveredEvent

  rw [hfixed]


/--
Forward and recovered events are equal exactly at fixed
points.
-/
theorem forwardEvent_eq_recoveredEvent_iff
    (token : RoutedTokenization.Token) :

    forwardEvent token =
        recoveredEvent token
      ↔

    RoutedTokenization.tokenStep token =
        token := by

  constructor

  · intro hevents

    have hsource :
        token =
          RoutedTokenization.tokenStep token :=

      congrArg Prod.fst hevents

    exact hsource.symm

  · intro hfixed

    exact
      forwardEvent_eq_recoveredEvent_of_fixed
        token
        hfixed


/-
## Temporal event selected by direction
-/

/--
Select the oriented event associated with a temporal
direction.
-/
def eventOfDirection
    (direction :
      GlyphState.TemporalDirection)
    (token :
      RoutedTokenization.Token) :
    Event :=

  match direction with

  | GlyphState.TemporalDirection.forward =>
      forwardEvent token

  | GlyphState.TemporalDirection.recovered =>
      recoveredEvent token


@[simp]
theorem eventOfDirection_forward
    (token : RoutedTokenization.Token) :

    eventOfDirection
        GlyphState.TemporalDirection.forward
        token =

      forwardEvent token := by

  rfl


@[simp]
theorem eventOfDirection_recovered
    (token : RoutedTokenization.Token) :

    eventOfDirection
        GlyphState.TemporalDirection.recovered
        token =

      recoveredEvent token := by

  rfl


/--
Temporal direction is recoverable from the directed event
whenever the token moves.
-/
theorem direction_injective_at_moving_token
    (token : RoutedTokenization.Token)
    (hmoving : IsMoving token) :

    Function.Injective
      (
        fun direction =>
          eventOfDirection direction token
      ) := by

  intro left right hevents

  cases left with

  | forward =>

      cases right with

      | forward =>
          rfl

      | recovered =>
          exact False.elim
            (
              forwardEvent_ne_recoveredEvent
                token
                hmoving
                hevents
            )

  | recovered =>

      cases right with

      | forward =>
          exact False.elim
            (
              forwardEvent_ne_recoveredEvent
                token
                hmoving
                hevents.symm
            )

      | recovered =>
          rfl


/-
## Information-phase readout on directed events
-/

/--
Read one information phase at the source of an event.
-/
def sourcePhaseRead
    (phase :
      GlyphState.InformationPhase)
    (event : Event) :
    GlyphStateDynamics.PhaseData :=

  GlyphStateDynamics.phaseRead
    phase
    event.1


/--
Read one information phase at the target of an event.
-/
def targetPhaseRead
    (phase :
      GlyphState.InformationPhase)
    (event : Event) :
    GlyphStateDynamics.PhaseData :=

  GlyphStateDynamics.phaseRead
    phase
    event.2


/--
The target of a forward event contains the evolved visible
component.
-/
theorem forward_target_visible
    (token : RoutedTokenization.Token) :

    targetPhaseRead
        GlyphState.InformationPhase.visible
        (forwardEvent token) =

      Sum.inl
        (
          MemoryEscrowRouted.visibleStep
            token.1
        ) := by

  rfl


/--
The target of a forward event contains the evolved escrow
component.
-/
theorem forward_target_escrow
    (token : RoutedTokenization.Token) :

    targetPhaseRead
        GlyphState.InformationPhase.escrow
        (forwardEvent token) =

      Sum.inr
        (
          MemoryEscrowRouted.escrowStep
            token.2
        ) := by

  rfl


/--
Visible and escrow readouts remain distinct at the source
of every directed event.
-/
theorem source_visible_ne_escrow
    (event : Event) :

    sourcePhaseRead
        GlyphState.InformationPhase.visible
        event ≠

      sourcePhaseRead
        GlyphState.InformationPhase.escrow
        event := by

  exact
    GlyphStateDynamics.visible_read_ne_escrow_read
      event.1


/--
Visible and escrow readouts remain distinct at the target
of every directed event.
-/
theorem target_visible_ne_escrow
    (event : Event) :

    targetPhaseRead
        GlyphState.InformationPhase.visible
        event ≠

      targetPhaseRead
        GlyphState.InformationPhase.escrow
        event := by

  exact
    GlyphStateDynamics.visible_read_ne_escrow_read
      event.2


/-
## Four semantic views
-/

/--
One semantic view of a routed Tkairos event is determined
by temporal direction and information phase.
-/
structure View where

  direction :
    GlyphState.TemporalDirection

  phase :
    GlyphState.InformationPhase


/--
The semantic view space is equivalent to the four-state
glyph fiber.
-/
def viewEquivFiber :

    View ≃ GlyphState.Fiber where

  toFun :=
    fun view =>
      (
        view.direction,
        view.phase
      )

  invFun :=
    fun fiber =>
      {
        direction := fiber.1
        phase := fiber.2
      }

  left_inv := by

    intro view

    cases view

    rfl

  right_inv := by

    intro fiber

    rcases fiber with
      ⟨direction, phase⟩

    rfl


/--
The directed semantic view space has four elements.
-/
noncomputable instance viewFintype :
    Fintype View :=

  Fintype.ofEquiv
    GlyphState.Fiber
    viewEquivFiber.symm


theorem view_card :

    Fintype.card View = 4 := by

  rw [
    Fintype.card_congr
      viewEquivFiber
  ]

  exact
    GlyphState.fiber_card


/--
Interpret one temporal-information view at a token.

Temporal direction chooses an oriented event. Information
phase chooses which token component is read at its target.
-/
def interpretView
    (view : View)
    (token : RoutedTokenization.Token) :
    GlyphStateDynamics.PhaseData :=

  targetPhaseRead
    view.phase
    (
      eventOfDirection
        view.direction
        token
    )


/--
At a moving token, temporal direction is genuinely encoded
by event orientation, while information phase remains
genuinely encoded by the visible-versus-escrow sum branch.
-/
theorem temporal_orientation_realized
    (token : RoutedTokenization.Token)
    (hmoving : IsMoving token) :

    eventOfDirection
        GlyphState.TemporalDirection.forward
        token ≠

      eventOfDirection
        GlyphState.TemporalDirection.recovered
        token := by

  exact
    forwardEvent_ne_recoveredEvent
      token
      hmoving


end DirectedTkairos
