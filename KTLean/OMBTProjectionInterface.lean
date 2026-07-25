import KTLean.GlyphSpectralCompleteEmergence
import KTLean.MemoryEscrowRouted
import Mathlib.Tactic

/-!
# OMBT Projection Interface

## Formal status

**Level 2 — Abstract projection-with-escrow interface, together with a
concrete routed realization already present in KTLean.**

## Developmental predecessor

`GlyphSpectralCompleteEmergence`

The canonical 42-glyph spectrum is complete before locality and spacetime
exist. The next developmental event is projection.

The Octonionic Ballot Matrix Transform is represented here first by its
essential informational obligation:

    complete source state
          ↓
    visible projection + escrow record.

Projection is not permitted to destroy information. A complete state must
be exactly reconstructible from its visible projection together with the
corresponding escrow record.

Thus the OMBT interface consists of:

* a complete pre-projection state;
* a visible projected state;
* an escrow state;
* a decomposition map;
* a reconstruction map;
* exact reconstruction in both directions.

This module does not yet claim that the complete concrete octonionic ballot
matrix has been derived. It isolates the interface that any lawful OMBT
realization must satisfy and proves that the existing routed-memory system
provides a concrete witness.

The central equivalence is:

    CompleteState ≃ VisibleState × EscrowState.
-/

universe u v w

namespace OMBTProjectionInterface

/-
## Abstract projection-with-escrow interface
-/

/--
A lawful OMBT projection interface.

The complete source state is decomposed into a visible component and an
escrow component. Reconstruction must recover the source state exactly,
and every lawful visible-plus-escrow pair must correspond to one complete
state.
-/
structure Interface where

  SourceState :
    Type u

  VisibleState :
    Type v

  EscrowState :
    Type w

  decompose :
    SourceState →
      VisibleState × EscrowState

  reconstruct :
    VisibleState × EscrowState →
      SourceState

  reconstruct_decompose :
    ∀ source : SourceState,
      reconstruct (decompose source) =
        source

  decompose_reconstruct :
    ∀ data : VisibleState × EscrowState,
      decompose (reconstruct data) =
        data

namespace Interface

/-
## Visible and escrow projections
-/

/--
Extract the visible component of a complete source state.
-/
def visible
    (I : Interface)
    (source : I.SourceState) :
    I.VisibleState :=

  (I.decompose source).1

/--
Extract the escrow component of a complete source state.
-/
def escrow
    (I : Interface)
    (source : I.SourceState) :
    I.EscrowState :=

  (I.decompose source).2

/--
The full decomposition is exactly the pair of its visible and escrow
readouts.
-/
theorem decompose_eq_visible_escrow
    (I : Interface)
    (source : I.SourceState) :
    I.decompose source =
      (
        I.visible source,
        I.escrow source
      ) := by

  rfl

/--
Reconstruction from the visible projection and escrow record recovers the
complete source state.
-/
theorem reconstruct_visible_escrow
    (I : Interface)
    (source : I.SourceState) :
    I.reconstruct
        (
          I.visible source,
          I.escrow source
        ) =
      source := by

  exact
    I.reconstruct_decompose source

/-
## Informational preservation
-/

/--
The complete visible-plus-escrow projection is injective.

Two source states with the same visible state and the same escrow record
are the same complete state.
-/
theorem decompose_injective
    (I : Interface) :
    Function.Injective I.decompose := by

  intro left right hEqual

  have hReconstructed :
      I.reconstruct (I.decompose left) =
        I.reconstruct (I.decompose right) :=
    congrArg I.reconstruct hEqual

  simpa [
    I.reconstruct_decompose
  ] using hReconstructed

/--
Equality of both the visible and escrow components forces equality of the
complete source states.
-/
theorem source_eq_of_visible_eq_and_escrow_eq
    (I : Interface)
    {left right : I.SourceState}
    (hVisible :
      I.visible left =
        I.visible right)
    (hEscrow :
      I.escrow left =
        I.escrow right) :
    left =
      right := by

  apply I.decompose_injective

  rw [
    I.decompose_eq_visible_escrow,
    I.decompose_eq_visible_escrow,
    hVisible,
    hEscrow
  ]

/--
A lawful OMBT interface gives an equivalence between complete source
states and visible-plus-escrow states.
-/
def sourceEquivVisibleEscrow
    (I : Interface) :
    I.SourceState ≃
      I.VisibleState × I.EscrowState where

  toFun :=
    I.decompose

  invFun :=
    I.reconstruct

  left_inv :=
    I.reconstruct_decompose

  right_inv :=
    I.decompose_reconstruct

/--
The OMBT decomposition is surjective onto its lawful visible-plus-escrow
state space.
-/
theorem decompose_surjective
    (I : Interface) :
    Function.Surjective I.decompose := by

  intro data

  refine
    ⟨
      I.reconstruct data,
      ?_
    ⟩

  exact
    I.decompose_reconstruct data

/--
The OMBT reconstruction map is injective.
-/
theorem reconstruct_injective
    (I : Interface) :
    Function.Injective I.reconstruct := by

  intro left right hEqual

  have hDecomposed :
      I.decompose (I.reconstruct left) =
        I.decompose (I.reconstruct right) :=
    congrArg I.decompose hEqual

  simpa [
    I.decompose_reconstruct
  ] using hDecomposed

/--
Projection with escrow preserves complete information exactly.
-/
theorem projection_with_escrow_preserves_information
    (I : Interface) :
    Function.Injective I.decompose
      ∧
    Function.Surjective I.decompose
      ∧
    (
      ∀ source : I.SourceState,
        I.reconstruct
            (
              I.visible source,
              I.escrow source
            ) =
          source
    ) := by

  exact
    ⟨
      I.decompose_injective,
      I.decompose_surjective,
      I.reconstruct_visible_escrow
    ⟩

end Interface

/-
## Concrete routed OMBT witness
-/

/--
The existing routed-memory construction provides a concrete realization
of the OMBT informational interface.

Its source state is the complete routed Tkairos state. Its visible state
omits Pascal route addresses, while the escrow state retains those hidden
addresses.
-/
def routedOMBT :
    Interface where

  SourceState :=
    MemoryEscrowRouted.CompleteState

  VisibleState :=
    MemoryEscrowRouted.VisibleState

  EscrowState :=
    MemoryEscrowRouted.EscrowRecord

  decompose :=
    MemoryEscrowRouted.decompose

  reconstruct :=
    MemoryEscrowRouted.reconstruct

  reconstruct_decompose :=
    MemoryEscrowRouted.reconstruct_decompose

  decompose_reconstruct :=
    MemoryEscrowRouted.decompose_reconstruct

/--
The abstract visible readout of the routed OMBT is the established routed
visible projection.
-/
theorem routedOMBT_visible
    (source :
      MemoryEscrowRouted.CompleteState) :
    routedOMBT.visible source =
      TkairosLocality.observeRoutedPair source := by

  rfl

/--
The abstract escrow readout of the routed OMBT is the established routed
escrow record.
-/
theorem routedOMBT_escrow
    (source :
      MemoryEscrowRouted.CompleteState) :
    routedOMBT.escrow source =
      MemoryEscrowRouted.escrow source := by

  rfl

/--
The routed OMBT reconstructs every complete routed state from its visible
projection and escrow record.
-/
theorem routedOMBT_reconstructs_complete_state
    (source :
      MemoryEscrowRouted.CompleteState) :
    routedOMBT.reconstruct
        (
          routedOMBT.visible source,
          routedOMBT.escrow source
        ) =
      source := by

  exact
    routedOMBT.reconstruct_visible_escrow source

/--
The routed OMBT decomposition is exactly the established equivalence
between complete routed states and visible-plus-escrow data.
-/
theorem routedOMBT_decompose_injective :
    Function.Injective routedOMBT.decompose := by

  exact
    routedOMBT.decompose_injective

/--
The routed realization preserves complete information under projection.
-/
theorem routedOMBT_preserves_complete_information :
    Function.Injective routedOMBT.decompose
      ∧
    Function.Surjective routedOMBT.decompose
      ∧
    (
      ∀ source :
          MemoryEscrowRouted.CompleteState,
        routedOMBT.reconstruct
            (
              routedOMBT.visible source,
              routedOMBT.escrow source
            ) =
          source
    ) := by

  exact
    routedOMBT.projection_with_escrow_preserves_information

/-
## Compatibility with routed evolution
-/

/--
One complete routed step decomposes into the corresponding visible step
and escrow step.
-/
theorem routedOMBT_decompose_step
    (source :
      MemoryEscrowRouted.CompleteState) :
    routedOMBT.decompose
        (
          MemoryEscrowRouted.completeStep source
        ) =
      (
        MemoryEscrowRouted.visibleStep
          (routedOMBT.visible source),
        MemoryEscrowRouted.escrowStep
          (routedOMBT.escrow source)
      ) := by

  exact
    MemoryEscrowRouted.decompose_completeStep source

/--
Reconstruction commutes with one visible-plus-escrow evolution step.
-/
theorem routedOMBT_reconstruct_step
    (data :
      MemoryEscrowRouted.VisibleState
        ×
      MemoryEscrowRouted.EscrowRecord) :
    routedOMBT.reconstruct
        (
          MemoryEscrowRouted.visibleStep data.1,
          MemoryEscrowRouted.escrowStep data.2
        ) =
      MemoryEscrowRouted.completeStep
        (
          routedOMBT.reconstruct data
        ) := by

  exact
    MemoryEscrowRouted.reconstruct_step data

/--
The routed OMBT transports visible and escrow information lawfully while
retaining exact reconstructibility.
-/
theorem routedOMBT_evolution_preserves_information :
    (
      ∀ source :
          MemoryEscrowRouted.CompleteState,
        routedOMBT.decompose
            (
              MemoryEscrowRouted.completeStep source
            ) =
          (
            MemoryEscrowRouted.visibleStep
              (routedOMBT.visible source),
            MemoryEscrowRouted.escrowStep
              (routedOMBT.escrow source)
          )
    )
      ∧
    (
      ∀ data :
          MemoryEscrowRouted.VisibleState
            ×
          MemoryEscrowRouted.EscrowRecord,
        routedOMBT.reconstruct
            (
              MemoryEscrowRouted.visibleStep data.1,
              MemoryEscrowRouted.escrowStep data.2
            ) =
          MemoryEscrowRouted.completeStep
            (
              routedOMBT.reconstruct data
            )
    ) := by

  exact
    ⟨
      routedOMBT_decompose_step,
      routedOMBT_reconstruct_step
    ⟩

/-
## Developmental bridge from the completed glyph spectrum
-/

/--
The complete canonical glyph spectrum exists before the projection
interface is applied.
-/
theorem canonical_spectrum_precedes_projection :
    GlyphSpectralCompleteEmergence.emergentSpectrum =
      GlyphSpectrum.values := by

  exact
    GlyphSpectralCompleteEmergence.emergentSpectrum_eq_canonical

/--
The pre-geometric spectrum already retains a spinorial double cover before
the OMBT projection stage.
-/
theorem spinorial_closure_precedes_projection :
    GlyphSpectralSpinorialBoundary.boundarySpinorSystem.ReachesDeckAt 1
      ∧
    ¬ GlyphSpectralSpinorialBoundary.boundarySpinorSystem.ReturnsAt 1
      ∧
    GlyphSpectralSpinorialBoundary.boundarySpinorSystem.ReturnsAt 2 := by

  exact
  GlyphSpectralCompleteEmergence.completed_spectrum_retains_spinorial_double_cover

/-
## Capstone
-/

/--
Capstone theorem.

The canonical 42-glyph spectrum is complete before projection. Its
terminal family already carries a two-sheet spinorial closure. The routed
OMBT then decomposes a complete state into visible and escrow components,
reconstructs the complete state exactly, and transports both components
lawfully under routed Tkairos evolution.

Thus projection does not erase hidden information. It changes the mode in
which that information is carried:

    complete state
        ≃
    visible projected state × escrow state.
-/
theorem ombt_projection_interface_emerges :
    GlyphSpectralCompleteEmergence.emergentSpectrum =
        GlyphSpectrum.values
      ∧
    (
      GlyphSpectralSpinorialBoundary.boundarySpinorSystem.ReachesDeckAt 1
        ∧
      ¬ GlyphSpectralSpinorialBoundary.boundarySpinorSystem.ReturnsAt 1
        ∧
      GlyphSpectralSpinorialBoundary.boundarySpinorSystem.ReturnsAt 2
    )
      ∧
    (
      Function.Injective routedOMBT.decompose
        ∧
      Function.Surjective routedOMBT.decompose
        ∧
      (
        ∀ source :
            MemoryEscrowRouted.CompleteState,
          routedOMBT.reconstruct
              (
                routedOMBT.visible source,
                routedOMBT.escrow source
              ) =
            source
      )
    )
      ∧
    (
      ∀ source :
          MemoryEscrowRouted.CompleteState,
        routedOMBT.decompose
            (
              MemoryEscrowRouted.completeStep source
            ) =
          (
            MemoryEscrowRouted.visibleStep
              (routedOMBT.visible source),
            MemoryEscrowRouted.escrowStep
              (routedOMBT.escrow source)
          )
    ) := by

  exact
    ⟨
      canonical_spectrum_precedes_projection,
      spinorial_closure_precedes_projection,
      routedOMBT_preserves_complete_information,
      routedOMBT_decompose_step
    ⟩

end OMBTProjectionInterface

#check OMBTProjectionInterface.Interface
#check OMBTProjectionInterface.Interface.visible
#check OMBTProjectionInterface.Interface.escrow
#check OMBTProjectionInterface.Interface.sourceEquivVisibleEscrow
#check OMBTProjectionInterface.Interface.projection_with_escrow_preserves_information
#check OMBTProjectionInterface.routedOMBT
#check OMBTProjectionInterface.routedOMBT_reconstructs_complete_state
#check OMBTProjectionInterface.routedOMBT_preserves_complete_information
#check OMBTProjectionInterface.routedOMBT_decompose_step
#check OMBTProjectionInterface.routedOMBT_reconstruct_step
#check OMBTProjectionInterface.canonical_spectrum_precedes_projection
#check OMBTProjectionInterface.spinorial_closure_precedes_projection
#check OMBTProjectionInterface.ombt_projection_interface_emerges
