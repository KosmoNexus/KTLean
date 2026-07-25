import KTLean.OMBTMonadEmergence
import KTLean.GlyphStateDynamics
import Mathlib.Tactic

/-!
# OMBT Monad Dynamics

## Formal status

**Level 2 — Reversible dynamics of the fourfold monad fiber generated
by temporal orientation and information phase.**

## Developmental predecessor

`OMBTMonadEmergence`

The preceding development proves that every one of the 42 glyphs carries
four OMBT-derived monads:

    forward   × visible
    forward   × escrow
    recovered × visible
    recovered × escrow.

This module proves how those four states transform.

Two commuting involutions generate the fiber:

* temporal reversal exchanges `forward` and `recovered`;
* phase exchange exchanges `visible` and `escrow`.

Both preserve the underlying glyph. Their action therefore moves within
the four-state monad fiber over one fixed glyph.

The current routed token transition is itself involutive. Consequently,
forward and recovery use the same token map. Their temporal distinction
is retained by directed-event orientation rather than by two different
state-transition functions.

This is not a defect. It is the precise reversible structure already
derived by the OMBT chain.
-/

namespace OMBTMonadDynamics

/-
## Monad transformations
-/

/--
Reverse the temporal orientation of a monad while preserving its glyph
and information phase.
-/
def reverseTemporal
    (monad : KTMonad.Monad) :
    KTMonad.Monad :=

  GlyphStateDynamics.reverseStateTemporal monad

/--
Exchange visible and escrow information phase while preserving the glyph
and temporal orientation.
-/
def exchangePhase
    (monad : KTMonad.Monad) :
    KTMonad.Monad :=

  GlyphStateDynamics.exchangeStatePhase monad

/--
Temporal reversal preserves the underlying glyph.
-/
@[simp]
theorem reverseTemporal_glyph
    (monad : KTMonad.Monad) :
    (reverseTemporal monad).glyph =
      monad.glyph := by

  exact
    GlyphStateDynamics.reverseStateTemporal_glyph monad

/--
Phase exchange preserves the underlying glyph.
-/
@[simp]
theorem exchangePhase_glyph
    (monad : KTMonad.Monad) :
    (exchangePhase monad).glyph =
      monad.glyph := by

  exact
    GlyphStateDynamics.exchangeStatePhase_glyph monad

/--
Temporal reversal is involutive.
-/
theorem reverseTemporal_involutive :
    Function.Involutive reverseTemporal := by

  exact
    GlyphStateDynamics.reverseStateTemporal_involutive

/--
Phase exchange is involutive.
-/
theorem exchangePhase_involutive :
    Function.Involutive exchangePhase := by

  exact
    GlyphStateDynamics.exchangeStatePhase_involutive

/--
Temporal reversal and phase exchange commute.
-/
theorem transformations_commute
    (monad : KTMonad.Monad) :
    reverseTemporal
        (exchangePhase monad) =
      exchangePhase
        (reverseTemporal monad) := by

  exact
    GlyphStateDynamics.state_transformations_commute monad

/-
## Explicit coordinate behavior
-/

/--
Temporal reversal exchanges forward and recovered labels.
-/
theorem reverseTemporal_coordinates
    (glyph : KTGlyph.Glyph)
    (phase : GlyphState.InformationPhase) :
    reverseTemporal
        (KTMonad.mk
          glyph
          .forward
          phase) =
      KTMonad.mk
        glyph
        .recovered
        phase
      ∧
    reverseTemporal
        (KTMonad.mk
          glyph
          .recovered
          phase) =
      KTMonad.mk
        glyph
        .forward
        phase := by

  constructor <;>
    cases phase <;>
    rfl

/--
Phase exchange swaps visible and escrow labels.
-/
theorem exchangePhase_coordinates
    (glyph : KTGlyph.Glyph)
    (direction : GlyphState.TemporalDirection) :
    exchangePhase
        (KTMonad.mk
          glyph
          direction
          .visible) =
      KTMonad.mk
        glyph
        direction
        .escrow
      ∧
    exchangePhase
        (KTMonad.mk
          glyph
          direction
          .escrow) =
      KTMonad.mk
        glyph
        direction
        .visible := by

  constructor <;>
    cases direction <;>
    rfl

/-
## Four-state orbit over a glyph
-/

/--
The canonical forward-visible monad over one glyph.
-/
def baseMonad
    (glyph : KTGlyph.Glyph) :
    KTMonad.Monad :=

  KTMonad.mk
    glyph
    .forward
    .visible

/--
The four transformations generated from the base monad.
-/
def generatedFiber
    (glyph : KTGlyph.Glyph) :
    List KTMonad.Monad :=
  [
    baseMonad glyph,
    exchangePhase
      (baseMonad glyph),
    reverseTemporal
      (baseMonad glyph),
    reverseTemporal
      (
        exchangePhase
          (baseMonad glyph)
      )
  ]

/--
The generated fiber is exactly the four canonical monads over a glyph.
-/
theorem generatedFiber_eq
    (glyph : KTGlyph.Glyph) :
    generatedFiber glyph =
      [
        KTMonad.mk
          glyph
          .forward
          .visible,
        KTMonad.mk
          glyph
          .forward
          .escrow,
        KTMonad.mk
          glyph
          .recovered
          .visible,
        KTMonad.mk
          glyph
          .recovered
          .escrow
      ] := by

  rfl

/--
The generated monad fiber contains four entries.
-/
theorem generatedFiber_length
    (glyph : KTGlyph.Glyph) :
    (generatedFiber glyph).length =
      4 := by

  simp [generatedFiber]

/--
The four generated monads are pairwise distinct.
-/
theorem generatedFiber_nodup
    (glyph : KTGlyph.Glyph) :
    (generatedFiber glyph).Nodup := by

  simp [
    generatedFiber,
    baseMonad,
    reverseTemporal,
    exchangePhase,
    GlyphStateDynamics.reverseStateTemporal,
    GlyphStateDynamics.exchangeStatePhase,
    GlyphStateDynamics.reverseTemporal,
    GlyphStateDynamics.exchangePhase,
    KTMonad.mk
  ]

/--
The generated fiber remains entirely over its original glyph.
-/
theorem generatedFiber_preserves_glyph
    (glyph : KTGlyph.Glyph) :
    ∀ monad ∈ generatedFiber glyph,
      monad.glyph = glyph := by

  intro monad hMember

  simp [
    generatedFiber,
    baseMonad
  ] at hMember

  rcases hMember with
    h | h | h | h

  · subst monad
    rfl

  · subst monad
    simp

  · subst monad
    simp

  · subst monad
    simp

/-
## Compatibility with OMBT monad coordinates
-/

/--
Temporal reversal acts only on the directed-view coordinate of the OMBT
monad product.
-/
def reverseProductTemporal
    (data :
      OMBTMonadEmergence.OMBTMonadProduct) :
    OMBTMonadEmergence.OMBTMonadProduct :=

  (
    data.1,
    {
      direction :=
        match data.2.direction with
        | .forward =>
            .recovered
        | .recovered =>
            .forward

      phase :=
        data.2.phase
    }
  )

/--
Phase exchange acts only on the directed-view coordinate of the OMBT
monad product.
-/
def exchangeProductPhase
    (data :
      OMBTMonadEmergence.OMBTMonadProduct) :
    OMBTMonadEmergence.OMBTMonadProduct :=

  (
    data.1,
    {
      direction :=
        data.2.direction

      phase :=
        match data.2.phase with
        | .visible =>
            .escrow
        | .escrow =>
            .visible
    }
  )

/--
Realization intertwines product temporal reversal with monad temporal
reversal.
-/
theorem realizeMonad_reverseTemporal
    (data :
      OMBTMonadEmergence.OMBTMonadProduct) :
    OMBTMonadEmergence.realizeMonad
        (reverseProductTemporal data) =
      reverseTemporal
        (
          OMBTMonadEmergence.realizeMonad data
        ) := by

  rcases data with
    ⟨glyph, view⟩

  cases view with
  | mk direction phase =>
      cases direction <;>
        cases phase <;>
        rfl

/--
Realization intertwines product phase exchange with monad phase
exchange.
-/
theorem realizeMonad_exchangePhase
    (data :
      OMBTMonadEmergence.OMBTMonadProduct) :
    OMBTMonadEmergence.realizeMonad
        (exchangeProductPhase data) =
      exchangePhase
        (
          OMBTMonadEmergence.realizeMonad data
        ) := by

  rcases data with
    ⟨glyph, view⟩

  cases view with
  | mk direction phase =>
      cases direction <;>
        cases phase <;>
        rfl

/-
## Token-level semantic realization
-/

/--
Read the information selected by a monad after applying its temporal
interface to a projected token.
-/
def monadRead
    (monad : KTMonad.Monad)
    (token :
      OMBTDirectedEvent.ProjectedToken) :
    GlyphStateDynamics.PhaseData :=

  GlyphStateDynamics.phaseRead
    monad.phase
    (
      GlyphStateDynamics.temporalAction
        monad.direction
        token
    )

/--
Monad readout agrees with phase readout after the lawful projected-token
step.
-/
theorem monadRead_eq_phaseRead_after_step
    (monad : KTMonad.Monad)
    (token :
      OMBTDirectedEvent.ProjectedToken) :
    monadRead monad token =
      GlyphStateDynamics.phaseRead
        monad.phase
        (
          OMBTDirectedEvent.projectedTokenStep token
        ) := by

  unfold monadRead
  unfold OMBTDirectedEvent.projectedTokenStep

  exact
    GlyphStateDynamics.phaseRead_after_temporalAction
      monad.direction
      monad.phase
      token

/--
Visible and escrow monads over the same glyph and temporal orientation
produce distinct semantic readouts.
-/
theorem visible_escrow_reads_distinct
    (glyph : KTGlyph.Glyph)
    (direction :
      GlyphState.TemporalDirection)
    (token :
      OMBTDirectedEvent.ProjectedToken) :
    monadRead
        (KTMonad.mk
          glyph
          direction
          .visible)
        token
      ≠
    monadRead
        (KTMonad.mk
          glyph
          direction
          .escrow)
        token := by

  unfold monadRead

  cases direction <;>
    exact
      GlyphStateDynamics.visible_read_ne_escrow_read
        (
          OMBTDirectedEvent.projectedTokenStep token
        )

/--
In the current involutive routed witness, forward and recovered temporal
interfaces induce the same token map.
-/
theorem forward_recovered_token_map_coincide :
    GlyphStateDynamics.temporalAction
        .forward =
      GlyphStateDynamics.temporalAction
        .recovered := by

  exact
    GlyphStateDynamics.temporal_direction_collapses_in_current_witness

/--
Nevertheless, at the moving OMBT token, forward and recovered events are
distinguished by event orientation.
-/
theorem forward_recovered_events_remain_distinct :
    OMBTDirectedEvent.forwardEvent
        OMBTDirectedEvent.movingProjectedToken
      ≠
    OMBTDirectedEvent.recoveredEvent
        OMBTDirectedEvent.movingProjectedToken := by

  exact
    OMBTDirectedEvent.concrete_forward_ne_recovered

/-
## Capstone
-/

/--
Capstone theorem.

Each OMBT-derived monad remains over one fixed glyph while two commuting
involutions generate its complete four-state fiber. Temporal reversal
exchanges forward with recovered; phase exchange exchanges visible with
escrow.

The visible and escrow phases produce genuinely distinct readouts.
Because the present routed transition is involutive, forward and recovery
use the same token map, while directed-event orientation retains their
temporal distinction.

Thus the 168 monads carry lawful reversible dynamics without sacrificing
glyph identity, escrow provenance, or event direction.
-/
theorem ombt_monad_dynamics_emerge :
    Function.Involutive reverseTemporal
      ∧
    Function.Involutive exchangePhase
      ∧
    (
      ∀ monad : KTMonad.Monad,
        reverseTemporal
            (exchangePhase monad) =
          exchangePhase
            (reverseTemporal monad)
    )
      ∧
    (
      ∀ glyph : KTGlyph.Glyph,
        (generatedFiber glyph).length = 4
          ∧
        (generatedFiber glyph).Nodup
          ∧
        ∀ monad ∈ generatedFiber glyph,
          monad.glyph = glyph
    )
      ∧
    (
      ∀
        (glyph : KTGlyph.Glyph)
        (direction :
          GlyphState.TemporalDirection)
        (token :
          OMBTDirectedEvent.ProjectedToken),
        monadRead
            (KTMonad.mk
              glyph
              direction
              .visible)
            token
          ≠
        monadRead
            (KTMonad.mk
              glyph
              direction
              .escrow)
            token
    )
      ∧
    GlyphStateDynamics.temporalAction
        .forward =
      GlyphStateDynamics.temporalAction
        .recovered
      ∧
    OMBTDirectedEvent.forwardEvent
        OMBTDirectedEvent.movingProjectedToken
      ≠
    OMBTDirectedEvent.recoveredEvent
        OMBTDirectedEvent.movingProjectedToken := by

  refine
    ⟨
      reverseTemporal_involutive,
      exchangePhase_involutive,
      ?_,
      ?_,
      visible_escrow_reads_distinct,
      forward_recovered_token_map_coincide,
      forward_recovered_events_remain_distinct
    ⟩

  · intro monad

    exact
      transformations_commute monad

  · intro glyph

    refine
      ⟨
        generatedFiber_length glyph,
        generatedFiber_nodup glyph,
        ?_
      ⟩

    intro monad hMember

    exact
      generatedFiber_preserves_glyph
        glyph
        monad
        hMember

end OMBTMonadDynamics

#check OMBTMonadDynamics.reverseTemporal
#check OMBTMonadDynamics.exchangePhase
#check OMBTMonadDynamics.transformations_commute
#check OMBTMonadDynamics.generatedFiber
#check OMBTMonadDynamics.generatedFiber_eq
#check OMBTMonadDynamics.generatedFiber_nodup
#check OMBTMonadDynamics.realizeMonad_reverseTemporal
#check OMBTMonadDynamics.realizeMonad_exchangePhase
#check OMBTMonadDynamics.monadRead
#check OMBTMonadDynamics.visible_escrow_reads_distinct
#check OMBTMonadDynamics.forward_recovered_token_map_coincide
#check OMBTMonadDynamics.forward_recovered_events_remain_distinct
#check OMBTMonadDynamics.ombt_monad_dynamics_emerge
