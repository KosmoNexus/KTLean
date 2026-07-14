import KTLean.GlyphState
import KTLean.RoutedTokenization

/-!
# Dynamics of the Four-State Glyph Fiber

`GlyphState` constructed a four-element candidate fiber:

    temporal direction × information phase.

This module tests whether those coordinates are dynamically
realized by the current routed Tkairos witness.

The result is precise:

1. visible and escrow phases correspond to two genuinely
   distinct projections of a routed token;

2. forward and recovered are two semantic interfaces to
   reversible evolution;

3. in the current routed exchange, forward and recovery
   maps coincide because the transition is involutive.

Therefore the four-state fiber is structurally valid, but
the present routed witness does not yet prove four
independent dynamical orbits.

This is a useful rigidity result rather than a failure:
additional dynamics are required before the four-state
fiber can be canonically named a monad.
-/

namespace GlyphStateDynamics


/-
## Temporal action on routed tokens
-/

/--
Apply routed-token evolution according to temporal
direction.

`forward` uses the reversible forward step.

`recovered` uses the reversible recovery map.
-/
def temporalAction
    (direction :
      GlyphState.TemporalDirection)
    (token :
      RoutedTokenization.Token) :
    RoutedTokenization.Token :=

  match direction with

  | GlyphState.TemporalDirection.forward =>

      RoutedTokenization.reversibleToken.step
        token

  | GlyphState.TemporalDirection.recovered =>

      RoutedTokenization.reversibleToken.recover
        token


/--
Forward temporal action is the token step.
-/
@[simp]
theorem temporalAction_forward
    (token :
      RoutedTokenization.Token) :

    temporalAction
        GlyphState.TemporalDirection.forward
        token =

      RoutedTokenization.tokenStep
        token := by

  rfl


/--
Recovered temporal action is also the token step in the
current involutive routed witness.
-/
@[simp]
theorem temporalAction_recovered
    (token :
      RoutedTokenization.Token) :

    temporalAction
        GlyphState.TemporalDirection.recovered
        token =

      RoutedTokenization.tokenStep
        token := by

  rfl


/--
The forward and recovered temporal interfaces induce the
same map in the current routed witness.

This equality follows because routed token evolution is
involutive and was packaged with identical step and
recovery functions.
-/
theorem forward_action_eq_recovered_action :

    temporalAction
        GlyphState.TemporalDirection.forward =

      temporalAction
        GlyphState.TemporalDirection.recovered := by

  funext token

  rfl


/--
Every temporal action is involutive.
-/
theorem temporalAction_involutive
    (direction :
      GlyphState.TemporalDirection) :

    Function.Involutive
      (temporalAction direction) := by

  intro token

  cases direction <;>

    exact
      RoutedTokenization.tokenStep_involutive
        token


/--
Applying the same temporal interface twice returns the
original token.
-/
theorem temporalAction_twice
    (direction :
      GlyphState.TemporalDirection)
    (token :
      RoutedTokenization.Token) :

    temporalAction direction
        (
          temporalAction direction token
        ) =

      token := by

  exact
    temporalAction_involutive
      direction
      token


/-
## Information-phase readout
-/

/--
The data visible in one information phase.

The two branches have different semantic types:

- visible projected data;
- hidden escrow record.
-/
abbrev PhaseData :=

  Sum
    MemoryEscrowRouted.VisibleState
    MemoryEscrowRouted.EscrowRecord


/--
Read one component of a routed token according to
information phase.
-/
def phaseRead
    (phase :
      GlyphState.InformationPhase)
    (token :
      RoutedTokenization.Token) :
    PhaseData :=

  match phase with

  | GlyphState.InformationPhase.visible =>

      Sum.inl token.1

  | GlyphState.InformationPhase.escrow =>

      Sum.inr token.2


/--
Visible phase reads the projected component.
-/
@[simp]
theorem phaseRead_visible
    (token :
      RoutedTokenization.Token) :

    phaseRead
        GlyphState.InformationPhase.visible
        token =

      Sum.inl token.1 := by

  rfl


/--
Escrow phase reads the hidden route record.
-/
@[simp]
theorem phaseRead_escrow
    (token :
      RoutedTokenization.Token) :

    phaseRead
        GlyphState.InformationPhase.escrow
        token =

      Sum.inr token.2 := by

  rfl


/--
Visible and escrow phase readouts are always distinct
because they inhabit opposite branches of the sum type.
-/
theorem visible_read_ne_escrow_read
    (token :
      RoutedTokenization.Token) :

    phaseRead
        GlyphState.InformationPhase.visible
        token ≠

      phaseRead
        GlyphState.InformationPhase.escrow
        token := by

  simp [
    phaseRead
  ]


/-
## Compatibility of phase readout with token evolution
-/

/--
Visible information evolves by the routed visible step.
-/
theorem visible_read_after_step
    (token :
      RoutedTokenization.Token) :

    phaseRead
        GlyphState.InformationPhase.visible
        (
          RoutedTokenization.tokenStep token
        ) =

      Sum.inl
        (
          MemoryEscrowRouted.visibleStep
            token.1
        ) := by

  rfl


/--
Escrow information evolves by the routed escrow step.
-/
theorem escrow_read_after_step
    (token :
      RoutedTokenization.Token) :

    phaseRead
        GlyphState.InformationPhase.escrow
        (
          RoutedTokenization.tokenStep token
        ) =

      Sum.inr
        (
          MemoryEscrowRouted.escrowStep
            token.2
        ) := by

  rfl


/--
Phase readout after a temporal action agrees with the
appropriate routed component evolution.
-/
theorem phaseRead_after_temporalAction
    (direction :
      GlyphState.TemporalDirection)
    (phase :
      GlyphState.InformationPhase)
    (token :
      RoutedTokenization.Token) :

    phaseRead phase
        (
          temporalAction direction token
        ) =

      phaseRead phase
        (
          RoutedTokenization.tokenStep token
        ) := by

  cases direction <;>
    rfl


/-
## Fiber transformations
-/

/--
Reverse the temporal label while preserving information
phase.
-/
def reverseTemporal
    (fiber :
      GlyphState.Fiber) :
    GlyphState.Fiber :=

  match fiber.1 with

  | GlyphState.TemporalDirection.forward =>

      (
        GlyphState.TemporalDirection.recovered,
        fiber.2
      )

  | GlyphState.TemporalDirection.recovered =>

      (
        GlyphState.TemporalDirection.forward,
        fiber.2
      )


/--
Exchange visible and escrow phase while preserving
temporal direction.
-/
def exchangePhase
    (fiber :
      GlyphState.Fiber) :
    GlyphState.Fiber :=

  match fiber.2 with

  | GlyphState.InformationPhase.visible =>

      (
        fiber.1,
        GlyphState.InformationPhase.escrow
      )

  | GlyphState.InformationPhase.escrow =>

      (
        fiber.1,
        GlyphState.InformationPhase.visible
      )


/--
Temporal reversal is involutive.
-/
theorem reverseTemporal_involutive :

    Function.Involutive reverseTemporal := by

  intro fiber

  rcases fiber with
    ⟨direction, phase⟩

  cases direction <;>
    rfl


/--
Phase exchange is involutive.
-/
theorem exchangePhase_involutive :

    Function.Involutive exchangePhase := by

  intro fiber

  rcases fiber with
    ⟨direction, phase⟩

  cases phase <;>
    rfl


/--
Temporal reversal and phase exchange commute.
-/
theorem reverseTemporal_exchangePhase_commute
    (fiber :
      GlyphState.Fiber) :

    reverseTemporal
        (exchangePhase fiber) =

      exchangePhase
        (reverseTemporal fiber) := by

  rcases fiber with
    ⟨direction, phase⟩

  cases direction <;>
    cases phase <;>
    rfl


/--
The four canonical fiber states are generated from the
forward-visible state by the two commuting involutions.
-/
theorem canonical_fiber_generation :

    GlyphState.forwardVisible =
        GlyphState.forwardVisible
      ∧

    exchangePhase
        GlyphState.forwardVisible =
        GlyphState.forwardEscrow
      ∧

    reverseTemporal
        GlyphState.forwardVisible =
        GlyphState.recoveredVisible
      ∧

    reverseTemporal
        (
          exchangePhase
            GlyphState.forwardVisible
        ) =
        GlyphState.recoveredEscrow := by

  decide


/-
## Lifted transformations over glyphs
-/

/--
Apply temporal-label reversal to a glyph state without
changing the glyph or phase.
-/
def reverseStateTemporal
    (state :
      GlyphState.State) :
    GlyphState.State where

  glyph :=
    state.glyph

  direction :=
    (reverseTemporal
      (
        state.direction,
        state.phase
      )
    ).1

  phase :=
    state.phase


/--
Apply phase exchange to a glyph state without changing the
glyph or temporal label.
-/
def exchangeStatePhase
    (state :
      GlyphState.State) :
    GlyphState.State where

  glyph :=
    state.glyph

  direction :=
    state.direction

  phase :=
    (exchangePhase
      (
        state.direction,
        state.phase
      )
    ).2


/--
Temporal reversal preserves the underlying glyph.
-/
@[simp]
theorem reverseStateTemporal_glyph
    (state :
      GlyphState.State) :

    (reverseStateTemporal state).glyph =
      state.glyph := by

  rfl


/--
Phase exchange preserves the underlying glyph.
-/
@[simp]
theorem exchangeStatePhase_glyph
    (state :
      GlyphState.State) :

    (exchangeStatePhase state).glyph =
      state.glyph := by

  rfl


/--
Temporal reversal on glyph states is involutive.
-/
theorem reverseStateTemporal_involutive :

    Function.Involutive
      reverseStateTemporal := by

  intro state

  cases state with
  | mk glyph direction phase =>

      cases direction <;>
        rfl


/--
Phase exchange on glyph states is involutive.
-/
theorem exchangeStatePhase_involutive :

    Function.Involutive
      exchangeStatePhase := by

  intro state

  cases state with
  | mk glyph direction phase =>

      cases phase <;>
        rfl


/--
The lifted temporal and phase transformations commute.
-/
theorem state_transformations_commute
    (state :
      GlyphState.State) :

    reverseStateTemporal
        (
          exchangeStatePhase state
        ) =

      exchangeStatePhase
        (
          reverseStateTemporal state
        ) := by

  cases state with
  | mk glyph direction phase =>

      cases direction <;>
        cases phase <;>
        simp [
          reverseStateTemporal,
          exchangeStatePhase,
          reverseTemporal,
          exchangePhase
        ]


/-
## Diagnostic conclusion
-/

/--
The information-phase distinction is dynamically visible:
the two phases read distinct components of every token.
-/
theorem information_phase_is_semantically_distinct
    (token :
      RoutedTokenization.Token) :

    phaseRead
        GlyphState.InformationPhase.visible
        token ≠

      phaseRead
        GlyphState.InformationPhase.escrow
        token := by

  exact
    visible_read_ne_escrow_read
      token


/--
The temporal labels are not dynamically separated by the
current routed involution: they induce identical token
maps.
-/
theorem temporal_direction_collapses_in_current_witness :

    temporalAction
        GlyphState.TemporalDirection.forward =

      temporalAction
        GlyphState.TemporalDirection.recovered := by

  exact
    forward_action_eq_recovered_action


end GlyphStateDynamics
