import KTLean.MemoryEscrowRouted
import KTLean.AdmissibleProjection
import KTLean.ProjectionDynamics

namespace KTLean

/-
This module connects the abstract projection/provenance framework to
the concrete routed Memory Escrow construction already present in KT.

The complete routed state consists exactly of:

  visible routed data × Pascal-address escrow.

Nothing is added as an auxiliary hidden variable.
-/

namespace RoutedProjectionProvenance

/--
The routed Memory Escrow system, expressed as an exact provenance
decomposition.
-/
def routedProvenance :
    Provenance
      MemoryEscrowRouted.CompleteState
      MemoryEscrowRouted.VisibleState
      MemoryEscrowRouted.EscrowRecord where

  view :=
    {
      observe :=
        TkairosLocality.observeRoutedPair
    }

  residue :=
    MemoryEscrowRouted.escrow

  rebuild :=
    fun visible residue =>
      MemoryEscrowRouted.reconstruct
        (visible, residue)

  observe_rebuild := by
    intro visible residue

    have h :=
      MemoryEscrowRouted.decompose_reconstruct
        (visible, residue)

    exact congrArg Prod.fst h

  residue_rebuild := by
    intro visible residue

    have h :=
      MemoryEscrowRouted.decompose_reconstruct
        (visible, residue)

    exact congrArg Prod.snd h

  rebuild_parts := by
    intro complete

    exact
      MemoryEscrowRouted.reconstruct_decompose
        complete

/--
The concrete routed system is an admissible projection: everything
omitted from the visible state is explicitly carried by provenance.
-/
def routedAdmissibleProjection :
    AdmissibleProjection
      MemoryEscrowRouted.CompleteState
      MemoryEscrowRouted.VisibleState
      MemoryEscrowRouted.EscrowRecord where

  provenance :=
    routedProvenance

/--
The complete routed exchange, packaged as projection dynamics.
-/
def routedProjectionDynamics :
    ProjectionDynamics
      MemoryEscrowRouted.CompleteState
      MemoryEscrowRouted.VisibleState
      MemoryEscrowRouted.EscrowRecord where

  projection :=
    routedAdmissibleProjection

  completeStep :=
    MemoryEscrowRouted.completeStep

/--
The abstract observation map agrees definitionally with the concrete
routed observation map.
-/
theorem routed_observe_eq
    (complete :
      MemoryEscrowRouted.CompleteState) :

    routedAdmissibleProjection.observe complete =
      TkairosLocality.observeRoutedPair complete := by

  rfl

/--
The abstract provenance residue agrees definitionally with the concrete
Pascal-address escrow record.
-/
theorem routed_residue_eq
    (complete :
      MemoryEscrowRouted.CompleteState) :

    routedAdmissibleProjection.residue complete =
      MemoryEscrowRouted.escrow complete := by

  rfl

/--
The abstract decomposition is exactly the pre-existing routed
visible-plus-escrow decomposition.
-/
theorem routed_decompose_eq
    (complete :
      MemoryEscrowRouted.CompleteState) :

    routedProvenance.decompose complete =
      MemoryEscrowRouted.decompose complete := by

  rfl

/--
The abstract reconstruction is exactly the pre-existing routed
reconstruction.
-/
theorem routed_reconstruct_eq
    (data :
      MemoryEscrowRouted.VisibleState ×
        MemoryEscrowRouted.EscrowRecord) :

    routedProvenance.reconstruct data =
      MemoryEscrowRouted.reconstruct data := by

  rfl

/--
The concrete routed visible step commutes with complete routed
evolution.
-/
theorem routed_visibleStep_commutes :
    routedProjectionDynamics.CommutesWithProjection
      MemoryEscrowRouted.visibleStep := by

  intro complete

  exact
    MemoryEscrowRouted.observe_completeStep
      complete

/--
The present routed exchange has closed visible dynamics.
-/
theorem routed_visiblyClosed :
    routedProjectionDynamics.VisiblyClosed := by

  exact
    ⟨
      MemoryEscrowRouted.visibleStep,
      routed_visibleStep_commutes
    ⟩

/--
Observationally equivalent routed states remain observationally
equivalent after the present exchange step.
-/
theorem routed_observationalEquivalence_preserved
    {
      x y :
        MemoryEscrowRouted.CompleteState
    }
    (hxy :
      routedAdmissibleProjection.ObservationallyEquivalent
        x y) :

    routedAdmissibleProjection.ObservationallyEquivalent
      (MemoryEscrowRouted.completeStep x)
      (MemoryEscrowRouted.completeStep y) := by

  exact
    ProjectionDynamics.observationalEquivalence_preserved
      routedProjectionDynamics
      MemoryEscrowRouted.visibleStep
      routed_visibleStep_commutes
      hxy

/--
No hidden dynamical split occurs under the current routed exchange.

The complete state contains provenance, but this particular evolution
merely exchanges the two packets, so the next visible state is already
determined by the present visible state.
-/
theorem no_hiddenDynamicalSplit
    {
      x y :
        MemoryEscrowRouted.CompleteState
    } :

    ¬ routedProjectionDynamics.HiddenDynamicalSplit
        x y := by

  intro hsplit

  exact
    (ProjectionDynamics.not_visiblyClosed_of_hiddenDynamicalSplit
      routedProjectionDynamics
      hsplit)
      routed_visiblyClosed

/--
The current routed exchange is not residue-sensitive in the formal
sense of `ProjectionDynamics.ResidueSensitive`.
-/
theorem routed_not_residueSensitive :
    ¬ routedProjectionDynamics.ResidueSensitive := by

  intro hsensitive

  exact
    (ProjectionDynamics.not_visiblyClosed_of_residueSensitive
      routedProjectionDynamics
      hsensitive)
      routed_visiblyClosed

/--
Every difference between two complete routed states appears either in
the visible routed state or in the Pascal-address escrow record.
-/
theorem routed_visible_or_escrow_differs
    {
      x y :
        MemoryEscrowRouted.CompleteState
    }
    (hxy : x ≠ y) :

    TkairosLocality.observeRoutedPair x ≠
        TkairosLocality.observeRoutedPair y
      ∨
    MemoryEscrowRouted.escrow x ≠
        MemoryEscrowRouted.escrow y := by

  exact
    routedProvenance.visible_or_residue_differs
      hxy

end RoutedProjectionProvenance

end KTLean
