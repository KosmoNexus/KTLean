import KTLean.RoutedProjectionProvenance
import KTLean.QuasiStochastic

namespace KTLean

namespace RoutedResidueSensitive

open RoutedProjectionProvenance

/-
The ordinary routed exchange preserves provenance but does not use it
to determine the next visible state.

Here we introduce a minimal address-sensitive interaction. The Pascal
control carried by each packet determines whether its visible
Cayley–Dickson block is preserved or switched.

The address remains absent from the local view, but it has an explicit
and lawful effect on later visible evolution.
-/

/--
Switch between the two Cayley–Dickson blocks.
-/
def switchBlock :
    CayleyDicksonQuaternion.Block →
      CayleyDicksonQuaternion.Block
  | .first =>
      .second
  | .second =>
      .first

/--
Use a Pascal control state to update a visible block.

* positive control preserves the block;
* negative control switches the block;
* inactive control preserves the block.

The inactive case is deliberately conservative in this first witness.
-/
def applyControlToBlock
    (control : PascalMod3.Control)
    (block : CayleyDicksonQuaternion.Block) :
    CayleyDicksonQuaternion.Block :=
  match control with
  | .inactive =>
      block
  | .positive =>
      block
  | .negative =>
      switchBlock block

/--
One address-sensitive step on a routed packet.

The Pascal address and payload are retained, while the visible block is
updated according to the control state derived from the address.
-/
def packetStep
    (packet : FanoRecovery.PointPacket) :
    FanoRecovery.PointPacket where

  block :=
    applyControlToBlock
      (BraidedQuaternion.controlAt packet.address)
      packet.block

  address :=
    packet.address

  payload :=
    packet.payload

/--
Apply the address-sensitive packet step to both packets in a complete
routed state.
-/
def completeStep
    (complete : MemoryEscrowRouted.CompleteState) :
    MemoryEscrowRouted.CompleteState :=
  (
    packetStep complete.1,
    packetStep complete.2
  )

/--
The address-sensitive interaction, packaged using the already-proved
routed admissible projection.
-/
def dynamics :
    ProjectionDynamics
      MemoryEscrowRouted.CompleteState
      MemoryEscrowRouted.VisibleState
      MemoryEscrowRouted.EscrowRecord where

  projection :=
    routedAdmissibleProjection

  completeStep :=
    completeStep

/-
## Explicit witness states
-/

/--
An address carrying positive Pascal control.
-/
def positiveAddress :
    BraidedQuaternion.PascalAddress :=
  ⟨0, 0⟩

/--
An address carrying negative Pascal control.
-/
def negativeAddress :
    BraidedQuaternion.PascalAddress :=
  ⟨2, 1⟩

@[simp]
theorem positiveAddress_control :
    BraidedQuaternion.controlAt positiveAddress =
      PascalMod3.Control.positive := by
  rfl

@[simp]
theorem negativeAddress_control :
    BraidedQuaternion.controlAt negativeAddress =
      PascalMod3.Control.negative := by
  rfl

/--
The two witness states use the same visible packet data but different
Pascal-address provenance in the first packet.
-/
def witnessPositive :
    MemoryEscrowRouted.CompleteState :=
  (
    {
      block :=
        CayleyDicksonQuaternion.Block.first
      address :=
        positiveAddress
      payload :=
        (0 : Fano.Point)
    },
    {
      block :=
        CayleyDicksonQuaternion.Block.first
      address :=
        positiveAddress
      payload :=
        (1 : Fano.Point)
    }
  )

/--
The second witness has exactly the same visible block-and-payload data,
but the first packet carries negative rather than positive Pascal
control.
-/
def witnessNegative :
    MemoryEscrowRouted.CompleteState :=
  (
    {
      block :=
        CayleyDicksonQuaternion.Block.first
      address :=
        negativeAddress
      payload :=
        (0 : Fano.Point)
    },
    {
      block :=
        CayleyDicksonQuaternion.Block.first
      address :=
        positiveAddress
      payload :=
        (1 : Fano.Point)
    }
  )

/--
The witness complete states are distinct.
-/
theorem witness_states_ne :
    witnessPositive ≠ witnessNegative := by
  intro h

  have haddress :
      witnessPositive.1.address =
        witnessNegative.1.address := by
    exact congrArg
      (fun state =>
        state.1.address)
      h

  change positiveAddress = negativeAddress at haddress

  cases haddress

/--
The witness states are identical under the local visible projection.
-/
theorem witness_observations_eq :
    dynamics.observe witnessPositive =
      dynamics.observe witnessNegative := by
  rfl

/--
The witness states are observationally equivalent.
-/
theorem witness_observationallyEquivalent :
    dynamics.projection.ObservationallyEquivalent
      witnessPositive
      witnessNegative := by
  rfl

/--
The witness states have different explicit provenance residues.
-/
theorem witness_residues_ne :
    dynamics.residue witnessPositive ≠
      dynamics.residue witnessNegative := by
  decide

/--
Positive Pascal control preserves the first packet's visible block.
-/
theorem witnessPositive_next_first_block :
    (
      dynamics.observe
        (dynamics.completeStep witnessPositive)
    ).1.1 =
      CayleyDicksonQuaternion.Block.first := by
  rfl

/--
Negative Pascal control switches the first packet's visible block.
-/
theorem witnessNegative_next_first_block :
    (
      dynamics.observe
        (dynamics.completeStep witnessNegative)
    ).1.1 =
      CayleyDicksonQuaternion.Block.second := by
  rfl

/--
The two presently indistinguishable witness states produce different
next visible observations.
-/
theorem witness_next_observations_ne :
    dynamics.observe
        (dynamics.completeStep witnessPositive)
      ≠
    dynamics.observe
        (dynamics.completeStep witnessNegative) := by
  decide

/-
## Concrete residue sensitivity
-/

/--
The address-sensitive routed dynamics has a non-injective local view.
-/
theorem dynamics_noninjectiveView :
    dynamics.NoninjectiveView := by
  exact
    ⟨
      witnessPositive,
      witnessNegative,
      witness_states_ne,
      witness_observations_eq
    ⟩

/--
The address-sensitive routed dynamics is residue-sensitive.
-/
theorem dynamics_residueSensitive :
    dynamics.ResidueSensitive := by
  exact
    ⟨
      witnessPositive,
      witnessNegative,
      witness_observationallyEquivalent,
      witness_residues_ne,
      witness_next_observations_ne
    ⟩

/--
The address-sensitive routed KT dynamics is quasi-stochastic.

Complete evolution is a deterministic function, but the current local
visible state does not suffice to determine the next visible state.
-/
theorem dynamics_quasiStochastic :
    dynamics.QuasiStochastic := by
  exact
    ⟨
      dynamics_noninjectiveView,
      dynamics_residueSensitive
    ⟩

/--
No closed evolution law on the present visible state alone can reproduce
the address-sensitive routed dynamics.
-/
theorem dynamics_not_visiblyClosed :
    ¬ dynamics.VisiblyClosed := by
  exact
    ProjectionDynamics.not_visiblyClosed_of_quasiStochastic
      dynamics
      dynamics_quasiStochastic

/--
No proposed visible-state transition reproduces the next observation
for every complete routed state.
-/
theorem no_complete_visibleStep :
    ∀ visibleStep :
        MemoryEscrowRouted.VisibleState →
          MemoryEscrowRouted.VisibleState,
      ¬ dynamics.CommutesWithProjection visibleStep := by
  exact
    ProjectionDynamics.no_visibleStep_of_quasiStochastic
      dynamics
      dynamics_quasiStochastic

/--
Despite quasi-stochastic visible behavior, each complete state still
has one explicitly determined complete successor.
-/
theorem complete_successor_is_determined
    (complete : MemoryEscrowRouted.CompleteState) :
    ∃ next : MemoryEscrowRouted.CompleteState,
      next = dynamics.completeStep complete := by
  exact
    ⟨dynamics.completeStep complete, rfl⟩

end RoutedResidueSensitive

end KTLean
