import KTLean.OMBTLocalityGeneration
import KTLean.DirectedTkairosWitness
import Mathlib.Tactic

/-!
# OMBT Directed Events

## Formal status

**Level 2 — Directed event emergence from projected locality,
escrow-preserving tokenization, and reversible Tkairos evolution.**

## Developmental predecessor

`OMBTLocalityGeneration`

The OMBT has already produced:

* a visible local state;
* an escrow state preserving hidden routing information;
* exact reconstruction of the complete state;
* lawful parallel evolution of visible and escrow components.

The next developmental event is temporal direction.

A projected token is the pair

    local visible state × escrow state.

For a moving token, the ordered transition

    source → successor

is distinct from its recovered orientation

    successor → source.

These two temporal orientations combine with the two information phases

    visible
    escrow

to produce four distinct directed-information views:

    forward   × visible
    forward   × escrow
    recovered × visible
    recovered × escrow.

This module does not yet attach those four views to every glyph. It proves
that the projection-and-escrow dynamics lawfully generate the fourfold
event fiber from which the monads will emerge.
-/

namespace OMBTDirectedEvent

/-
## Projected tokens
-/

/--
An OMBT projected token consists of one visible local state together with
the escrow record required for complete reconstruction.
-/
abbrev ProjectedToken :=
  RoutedTokenization.Token

/--
Encode a complete routed source state as an OMBT projected token.
-/
def encodeProjectedToken
    (source :
      MemoryEscrowRouted.CompleteState) :
    ProjectedToken :=

  OMBTProjectionInterface.routedOMBT.decompose source

/--
Decode an OMBT projected token into its complete routed source state.
-/
def decodeProjectedToken
    (token : ProjectedToken) :
    MemoryEscrowRouted.CompleteState :=

  OMBTProjectionInterface.routedOMBT.reconstruct token

/--
The projected-token encoding is the established routed tokenization.
-/
theorem encodeProjectedToken_eq_routedEncode
    (source :
      MemoryEscrowRouted.CompleteState) :
    encodeProjectedToken source =
      RoutedTokenization.encode source := by

  rfl

/--
The projected-token decoding is the established routed decoding.
-/
theorem decodeProjectedToken_eq_routedDecode
    (token : ProjectedToken) :
    decodeProjectedToken token =
      RoutedTokenization.decode token := by

  rfl

/--
A projected token is exactly the visible local state paired with its
escrow state.
-/
theorem projectedToken_eq_visible_escrow
    (source :
      MemoryEscrowRouted.CompleteState) :
    encodeProjectedToken source =
      (
        OMBTProjectionInterface.routedOMBT.visible source,
        OMBTProjectionInterface.routedOMBT.escrow source
      ) := by

  rfl

/--
Decoding an encoded projected token recovers the complete source state.
-/
theorem decode_encodeProjectedToken
    (source :
      MemoryEscrowRouted.CompleteState) :
    decodeProjectedToken
        (encodeProjectedToken source) =
      source := by

  exact
    OMBTProjectionInterface.routedOMBT_reconstructs_complete_state
      source

/--
Encoding a decoded projected token returns the same projected token.
-/
theorem encode_decodeProjectedToken
    (token : ProjectedToken) :
    encodeProjectedToken
        (decodeProjectedToken token) =
      token := by

  exact
    MemoryEscrowRouted.decompose_reconstruct
      token

/--
Complete source states are equivalent to projected local-plus-escrow
tokens.
-/
def completeEquivProjectedToken :
    MemoryEscrowRouted.CompleteState ≃
      ProjectedToken :=

  OMBTLocalityGeneration.completeEquivLocalEscrow

/-
## Token evolution
-/

/--
The lawful projected-token successor evolves locality and escrow in
parallel.
-/
def projectedTokenStep :
    ProjectedToken →
      ProjectedToken :=

  RoutedTokenization.tokenStep

/--
Encoding complete evolution produces projected-token evolution.
-/
theorem encode_completeStep
    (source :
      MemoryEscrowRouted.CompleteState) :
    encodeProjectedToken
        (
          MemoryEscrowRouted.completeStep source
        ) =
      projectedTokenStep
        (
          encodeProjectedToken source
        ) := by

  exact
    RoutedTokenization.encode_completeStep
      source

/--
Decoding projected-token evolution produces complete evolution.
-/
theorem decode_projectedTokenStep
    (token : ProjectedToken) :
    decodeProjectedToken
        (
          projectedTokenStep token
        ) =
      MemoryEscrowRouted.completeStep
        (
          decodeProjectedToken token
        ) := by

  exact
    RoutedTokenization.decode_tokenStep
      token

/--
Projected-token evolution explicitly advances the visible and escrow
components together.
-/
theorem projectedTokenStep_components
    (token : ProjectedToken) :
    projectedTokenStep token =
      (
        MemoryEscrowRouted.visibleStep token.1,
        MemoryEscrowRouted.escrowStep token.2
      ) := by

  rfl

/-
## Directed events
-/

/--
The forward directed event associated with one projected token.
-/
def forwardEvent
    (token : ProjectedToken) :
    DirectedTkairos.Event :=

  DirectedTkairos.forwardEvent token

/--
The recovered directed event associated with one projected token.
-/
def recoveredEvent
    (token : ProjectedToken) :
    DirectedTkairos.Event :=

  DirectedTkairos.recoveredEvent token

/--
A projected token is moving when its lawful successor differs from the
token itself.
-/
def IsMoving
    (token : ProjectedToken) :
    Prop :=

  DirectedTkairos.IsMoving token

/--
The established concrete routed token is an OMBT projected token.
-/
def movingProjectedToken :
    ProjectedToken :=

  DirectedTkairosWitness.movingToken

/--
The concrete projected token moves.
-/
theorem movingProjectedToken_isMoving :
    IsMoving movingProjectedToken := by

  exact
    DirectedTkairosWitness.movingToken_isMoving

/--
At a moving projected token, the forward and recovered event
orientations are distinct.
-/
theorem forward_ne_recovered_at_moving
    (token : ProjectedToken)
    (hMoving :
      IsMoving token) :
    forwardEvent token ≠
      recoveredEvent token := by

  exact
    DirectedTkairos.forwardEvent_ne_recoveredEvent
      token
      hMoving

/--
The concrete projected witness has distinct forward and recovered
events.
-/
theorem concrete_forward_ne_recovered :
    forwardEvent movingProjectedToken ≠
      recoveredEvent movingProjectedToken := by

  exact
    DirectedTkairosWitness.concrete_forward_ne_recovered

/--
At a moving projected token, temporal direction is injectively encoded by
event orientation.
-/
theorem temporal_direction_is_event_orientation
    (token : ProjectedToken)
    (hMoving :
      IsMoving token) :
    Function.Injective
      (
        fun direction =>
          DirectedTkairos.eventOfDirection
            direction
            token
      ) := by

  exact
    DirectedTkairos.direction_injective_at_moving_token
      token
      hMoving

/-
## Four directed-information views
-/

/--
A directed-information view combines temporal orientation with selection
of either the visible or escrow information phase.
-/
abbrev DirectedView :=
  DirectedTkairos.View

/--
A realized projected view consists of an oriented event and its selected
information phase.
-/
abbrev RealizedProjectedView :=
  DirectedTkairosWitness.RealizedView

/--
Realize one directed-information view at a projected token.
-/
def realizeProjectedView
    (token : ProjectedToken)
    (view : DirectedView) :
    RealizedProjectedView :=

  DirectedTkairosWitness.realizeView
    token
    view

/--
At every moving projected token, the four abstract views are realized
injectively.
-/
theorem realizeProjectedView_injective_at_moving
    (token : ProjectedToken)
    (hMoving :
      IsMoving token) :
    Function.Injective
      (
        realizeProjectedView token
      ) := by

  exact
    DirectedTkairosWitness.realizeView_injective_at_moving
      token
      hMoving

/--
The concrete moving projected token realizes all four views distinctly.
-/
theorem concrete_realizeProjectedView_injective :
    Function.Injective
      (
        realizeProjectedView movingProjectedToken
      ) := by

  exact
    DirectedTkairosWitness.concrete_realizeView_injective

/--
The four canonical directed-information views.
-/
def canonicalViews :
    List DirectedView :=
  [
    DirectedTkairosWitness.forwardVisibleView,
    DirectedTkairosWitness.forwardEscrowView,
    DirectedTkairosWitness.recoveredVisibleView,
    DirectedTkairosWitness.recoveredEscrowView
  ]

/--
The canonical view list contains exactly four entries.
-/
theorem canonicalViews_length :
    canonicalViews.length =
      4 := by

  native_decide

/--
The four canonical projected views are pairwise distinct when realized at
the moving projected token.
-/
theorem canonical_projected_views_distinct :
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.forwardVisibleView
      ≠
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.forwardEscrowView
      ∧
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.forwardVisibleView
      ≠
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.recoveredVisibleView
      ∧
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.forwardVisibleView
      ≠
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.recoveredEscrowView
      ∧
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.forwardEscrowView
      ≠
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.recoveredVisibleView
      ∧
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.forwardEscrowView
      ≠
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.recoveredEscrowView
      ∧
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.recoveredVisibleView
      ≠
    realizeProjectedView
        movingProjectedToken
        DirectedTkairosWitness.recoveredEscrowView := by

  exact
    DirectedTkairosWitness.canonical_views_distinct

/--
The realized projected-view image contains exactly four elements.
-/
theorem realized_projected_views_card :
    DirectedTkairosWitness.realizedViews.card =
      4 := by

  exact
    DirectedTkairosWitness.realizedViews_card

/-
## Locality, escrow, and temporal direction
-/

/--
The fourfold event fiber arises only after locality and escrow have both
been retained:

* locality supplies the visible information phase;
* escrow supplies the hidden information phase;
* directed event orientation supplies forward and recovered time.
-/
theorem fourfold_view_factorization :
    Fintype.card GlyphState.TemporalDirection =
        2
      ∧
    Fintype.card GlyphState.InformationPhase =
        2
      ∧
    Fintype.card DirectedView =
        4 := by

  exact
    ⟨
      GlyphState.temporalDirection_card,
      GlyphState.informationPhase_card,
      DirectedTkairos.view_card
    ⟩

/--
The OMBT locality remains non-injective, but the projected token retains
complete information and supports four distinct directed views.
-/
theorem locality_escrow_direction_package :
    OMBTLocalityGeneration.ombtVisibleProjection.HasResidue
      ∧
    ¬ Function.Injective
        OMBTLocalityGeneration.ombtVisibleProjection.observe
      ∧
    Function.Injective encodeProjectedToken
      ∧
    IsMoving movingProjectedToken
      ∧
    Function.Injective
      (
        realizeProjectedView movingProjectedToken
      )
      ∧
    DirectedTkairosWitness.realizedViews.card =
      4 := by

  exact
    ⟨
      OMBTLocalityGeneration.ombt_visible_projection_has_residue,
      OMBTLocalityGeneration.ombt_visible_projection_not_injective,
      OMBTProjectionInterface.routedOMBT_decompose_injective,
      movingProjectedToken_isMoving,
      concrete_realizeProjectedView_injective,
      realized_projected_views_card
    ⟩

/-
## Capstone
-/

/--
Capstone theorem.

The OMBT projected state is exactly local visible information paired with
escrow. Its evolution advances both components lawfully and remains
equivalent to complete routed evolution.

At a moving projected token, event orientation distinguishes forward from
recovered time. Combining those two temporal orientations with the two
information phases—visible and escrow—produces exactly four distinct
directed-information views.

This fourfold event fiber is the immediate developmental parent of the
four monadic realizations over each of the 42 glyphs.
-/
theorem ombt_directed_event_emerges :
    (
      ∀ source :
          MemoryEscrowRouted.CompleteState,
        encodeProjectedToken source =
          (
            OMBTProjectionInterface.routedOMBT.visible source,
            OMBTProjectionInterface.routedOMBT.escrow source
          )
    )
      ∧
    (
      ∀ source :
          MemoryEscrowRouted.CompleteState,
        encodeProjectedToken
            (
              MemoryEscrowRouted.completeStep source
            ) =
          projectedTokenStep
            (
              encodeProjectedToken source
            )
    )
      ∧
    IsMoving movingProjectedToken
      ∧
    forwardEvent movingProjectedToken ≠
      recoveredEvent movingProjectedToken
      ∧
    Function.Injective
      (
        realizeProjectedView movingProjectedToken
      )
      ∧
    DirectedTkairosWitness.realizedViews.card =
      4
      ∧
    (
      Fintype.card GlyphState.TemporalDirection =
          2
        ∧
      Fintype.card GlyphState.InformationPhase =
          2
        ∧
      Fintype.card DirectedView =
          4
    ) := by

  exact
    ⟨
      projectedToken_eq_visible_escrow,
      encode_completeStep,
      movingProjectedToken_isMoving,
      concrete_forward_ne_recovered,
      concrete_realizeProjectedView_injective,
      realized_projected_views_card,
      fourfold_view_factorization
    ⟩

end OMBTDirectedEvent

#check OMBTDirectedEvent.ProjectedToken
#check OMBTDirectedEvent.encodeProjectedToken
#check OMBTDirectedEvent.completeEquivProjectedToken
#check OMBTDirectedEvent.projectedTokenStep
#check OMBTDirectedEvent.movingProjectedToken
#check OMBTDirectedEvent.forward_ne_recovered_at_moving
#check OMBTDirectedEvent.realizeProjectedView
#check OMBTDirectedEvent.canonicalViews
#check OMBTDirectedEvent.canonical_projected_views_distinct
#check OMBTDirectedEvent.fourfold_view_factorization
#check OMBTDirectedEvent.locality_escrow_direction_package
#check OMBTDirectedEvent.ombt_directed_event_emerges
