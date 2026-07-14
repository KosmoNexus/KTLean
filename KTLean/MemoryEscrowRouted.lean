import KTLean.MemoryEscrow
import KTLean.TkairosLocality
import KTLean.TkairosDynamicZero

/-!
# Routed Memory Escrow

This module gives a concrete routed realization of Memory
Escrow.

The complete routed state contains:

1. visible block-and-payload data;
2. hidden Pascal route addresses.

The visible projection alone is not injective. However, the
visible state together with its escrow record reconstructs
the complete routed state exactly.

The routed exchange preserves both components lawfully:

    complete routed evolution
          ↓
    visible evolution + escrow evolution

Because routed exchange is involutive, the complete prior
state is recoverable at arbitrary finite depth.

Thus hidden routing information is not merely residual. It
is an explicit recoverable record accompanying Tkairos
evolution.
-/

namespace MemoryEscrowRouted


/-
## Complete, visible, and escrow state
-/

/--
The complete routed state used by the Tkairos locality
witness.
-/
abbrev CompleteState :=
  TkairosLocality.RoutedPair


/--
The visible state obtained after omitting Pascal addresses.
-/
abbrev VisibleState :=
  TkairosLocality.VisiblePair


/--
The hidden routing record carried by a complete pair.

Each component is the Pascal address of one routed packet.
-/
abbrev EscrowRecord :=
  BraidedQuaternion.PascalAddress ×
    BraidedQuaternion.PascalAddress


/--
Extract the route-address escrow record from a complete
routed state.
-/
def escrow
    (complete : CompleteState) :
    EscrowRecord :=

  (
    complete.1.address,
    complete.2.address
  )


/--
Decompose a complete routed state into its visible state
and hidden escrow record.
-/
def decompose
    (complete : CompleteState) :
    VisibleState × EscrowRecord :=

  (
    TkairosLocality.observeRoutedPair complete,
    escrow complete
  )


/--
Reconstruct one routed packet from visible block-payload
data and a Pascal route address.
-/
def reconstructPacket
    (visible : TkairosLocality.VisiblePacket)
    (address :
      BraidedQuaternion.PascalAddress) :
    FanoRecovery.PointPacket where

  block :=
    visible.1

  address :=
    address

  payload :=
    visible.2


/--
Reconstruct a complete routed state from its visible state
and escrow record.
-/
def reconstruct
    (data :
      VisibleState × EscrowRecord) :
    CompleteState :=

  (
    reconstructPacket
      data.1.1
      data.2.1,

    reconstructPacket
      data.1.2
      data.2.2
  )


/--
Reconstructing one packet from its visible projection and
route address returns the original packet.
-/
theorem reconstructPacket_observable_address
    (packet : FanoRecovery.PointPacket) :

    reconstructPacket
        (
          YangBaxterRouting.RoutedPacket.observable
            packet
        )
        packet.address =

      packet := by

  cases packet
  rfl


/--
Decomposing and then reconstructing a complete routed state
returns the original complete state.
-/
theorem reconstruct_decompose
    (complete : CompleteState) :

    reconstruct
        (decompose complete) =

      complete := by

  rcases complete with
    ⟨left, right⟩

  change
    (
      reconstructPacket
        (
          YangBaxterRouting.RoutedPacket.observable
            left
        )
        left.address,

      reconstructPacket
        (
          YangBaxterRouting.RoutedPacket.observable
            right
        )
        right.address
    ) =
    (left, right)

  rw [
    reconstructPacket_observable_address,
    reconstructPacket_observable_address
  ]


/--
Reconstructing and then decomposing visible-plus-escrow
data returns the original data.
-/
theorem decompose_reconstruct
    (data :
      VisibleState × EscrowRecord) :

    decompose
        (reconstruct data) =

      data := by

  rcases data with
    ⟨visible, addresses⟩

  rcases visible with
    ⟨leftVisible, rightVisible⟩

  rcases addresses with
    ⟨leftAddress, rightAddress⟩

  rcases leftVisible with
    ⟨leftBlock, leftPayload⟩

  rcases rightVisible with
    ⟨rightBlock, rightPayload⟩

  rfl


/--
Visible state plus escrow record uniquely determines the
complete routed state.
-/
theorem decompose_injective :

    Function.Injective decompose := by

  intro x y hxy

  have hreconstructed :
      reconstruct (decompose x) =
        reconstruct (decompose y) :=

    congrArg reconstruct hxy

  rw [
    reconstruct_decompose,
    reconstruct_decompose
  ] at hreconstructed

  exact hreconstructed


/--
The decomposition is a bijection between complete routed
states and visible-plus-escrow data.
-/
def completeEquivVisibleEscrow :

    CompleteState ≃
      VisibleState × EscrowRecord where

  toFun :=
    decompose

  invFun :=
    reconstruct

  left_inv :=
    reconstruct_decompose

  right_inv :=
    decompose_reconstruct


/-
## Routed Tkairos evolution
-/

/--
The complete routed Tkairos step.
-/
def completeStep :
    CompleteState → CompleteState :=

  YangBaxterRouting.routedExchange


/--
The visible routed successor.
-/
def visibleStep :
    VisibleState → VisibleState :=

  TkairosLocality.visibleExchange


/--
The escrow record evolves by exchanging its two route
addresses.
-/
def escrowStep :
    EscrowRecord → EscrowRecord :=

  YangBaxterRouting.crossing


@[simp]
theorem completeStep_pair
    (left right :
      FanoRecovery.PointPacket) :

    completeStep
        (left, right) =

      (right, left) := by

  rfl


@[simp]
theorem escrowStep_pair
    (left right :
      BraidedQuaternion.PascalAddress) :

    escrowStep
        (left, right) =

      (right, left) := by

  rfl


/--
The complete routed step is involutive.
-/
theorem completeStep_involutive :

    Function.Involutive completeStep := by

  intro complete

  exact
    YangBaxterRouting.routedExchange_involutive
      complete


/--
The escrow evolution is involutive.
-/
theorem escrowStep_involutive :

    Function.Involutive escrowStep := by

  intro record

  rcases record with
    ⟨left, right⟩

  rfl


/--
The visible evolution is involutive.
-/
theorem visibleStep_involutive :

    Function.Involutive visibleStep := by

  intro visible

  rcases visible with
    ⟨left, right⟩

  rfl


/--
One complete routed step decomposes into one visible step
and one escrow step.

This is the central preservation theorem.
-/
theorem decompose_completeStep
    (complete : CompleteState) :

    decompose
        (completeStep complete) =

      (
        visibleStep
          (decompose complete).1,

        escrowStep
          (decompose complete).2
      ) := by

  rcases complete with
    ⟨left, right⟩

  rfl


/--
The visible component of complete evolution follows the
visible routed exchange.
-/
theorem observe_completeStep
    (complete : CompleteState) :

    TkairosLocality.observeRoutedPair
        (completeStep complete) =

      visibleStep
        (
          TkairosLocality.observeRoutedPair
            complete
        ) := by

  exact
    TkairosLocality.routed_realizes_visibleExchange
      complete


/--
The escrow component travels lawfully with complete routed
evolution.
-/
theorem escrow_completeStep
    (complete : CompleteState) :

    escrow
        (completeStep complete) =

      escrowStep
        (escrow complete) := by

  rcases complete with
    ⟨left, right⟩

  rfl


/--
Reconstruction commutes with visible-plus-escrow
evolution.
-/
theorem reconstruct_step
    (data :
      VisibleState × EscrowRecord) :

    reconstruct
        (
          visibleStep data.1,
          escrowStep data.2
        ) =

      completeStep
        (reconstruct data) := by

  rcases data with
    ⟨visible, addresses⟩

  rcases visible with
    ⟨leftVisible, rightVisible⟩

  rcases addresses with
    ⟨leftAddress, rightAddress⟩

  rfl


/-
## Reversible Tkairos package
-/

/--
Complete routed evolution as a reversible state transition.

Because exchange is involutive, the forward and recovery
operations are the same.
-/
def reversibleComplete :
    ReversibleStep CompleteState :=

  ReversibleStep.ofInvolution
    completeStep
    completeStep_involutive


@[simp]
theorem reversibleComplete_step
    (complete : CompleteState) :

    reversibleComplete.step complete =
      completeStep complete := by

  rfl


@[simp]
theorem reversibleComplete_recover
    (complete : CompleteState) :

    reversibleComplete.recover complete =
      completeStep complete := by

  rfl


/--
The reversible routed history is exactly the complete
Tkairos history already defined by the locality module.
-/
theorem reversible_history_eq_tkairos_history
    (initial : CompleteState) :

    reversibleComplete.history initial =

      TkairosLocality.LocalSystem.completeHistory
        TkairosLocality.routedLocalSystem
        initial := by

  rfl


/--
One recovery operation reconstructs the immediately prior
complete routed state.
-/
theorem recovers_previous_complete
    (initial : CompleteState)
    (n : Nat) :

    reversibleComplete.recover
        (
          reversibleComplete.history
            initial
            (Nat.succ n)
        ) =

      reversibleComplete.history
        initial
        n := by

  exact
    reversibleComplete.history_recovers_previous
      initial
      n


/--
Finite-depth recovery reconstructs any earlier complete
state in the routed Tkairos history.
-/
theorem recovers_after
    (initial : CompleteState)
    (n k : Nat) :

    ReversibleStep.recoverN
        reversibleComplete
        k
        (
          reversibleComplete.history
            initial
            (n + k)
        ) =

      reversibleComplete.history
        initial
        n := by

  exact
    ReversibleStep.history_recovers_after
      reversibleComplete
      initial
      n
      k


/--
Recovering from the kth routed state returns the initial
complete routed state.
-/
theorem recovers_initial
    (initial : CompleteState)
    (k : Nat) :

    ReversibleStep.recoverN
        reversibleComplete
        k
        (
          reversibleComplete.history
            initial
            k
        ) =

      initial := by

  exact
    ReversibleStep.history_recovers_initial
      reversibleComplete
      initial
      k


/-
## Escrow history
-/

/--
The escrow record carried at each stage of complete routed
Tkairos history.
-/
def escrowHistory
    (initial : CompleteState) :
    Nat → EscrowRecord :=

  fun n =>
    escrow
      (
        reversibleComplete.history
          initial
          n
      )


@[simp]
theorem escrowHistory_zero
    (initial : CompleteState) :

    escrowHistory initial 0 =
      escrow initial := by

  rfl


/--
The escrow record evolves at every successor step by the
lawful escrow exchange.
-/
theorem escrowHistory_succ
    (initial : CompleteState)
    (n : Nat) :

    escrowHistory
        initial
        (Nat.succ n) =

      escrowStep
        (
          escrowHistory
            initial
            n
        ) := by

  unfold escrowHistory

  rw [
    ReversibleStep.history_succ
  ]

  exact
    escrow_completeStep
      (
        reversibleComplete.history
          initial
          n
      )


/--
The escrow record can be recovered one step backward by
applying the same escrow exchange.
-/
theorem escrowHistory_recovers_previous
    (initial : CompleteState)
    (n : Nat) :

    escrowStep
        (
          escrowHistory
            initial
            (Nat.succ n)
        ) =

      escrowHistory
        initial
        n := by

  rw [
    escrowHistory_succ
  ]

  exact
    escrowStep_involutive
      (
        escrowHistory
          initial
          n
      )


/-
## Visible state alone versus visible state plus escrow
-/

/--
The visible projection alone does not determine the
complete routed state.
-/
theorem visible_not_injective :

    ¬ Function.Injective
        TkairosLocality.observeRoutedPair := by

  exact
    TkairosLocality.routed_observe_not_injective


/--
Visible state plus escrow does determine the complete
state.
-/
theorem visible_with_escrow_injective :

    Function.Injective decompose := by

  exact decompose_injective


/--
There exist distinct complete states with the same visible
projection, but decomposition with escrow distinguishes
them.
-/
theorem escrow_distinguishes_hidden_residue :

    ∃ x y : CompleteState,

      x ≠ y
      ∧

      TkairosLocality.observeRoutedPair x =
        TkairosLocality.observeRoutedPair y
      ∧

      escrow x ≠
        escrow y := by

  let left :=
    FanoRecovery.liftA
      CayleyDicksonQuaternion.Block.first
      0

  let right :=
    FanoRecovery.liftB
      CayleyDicksonQuaternion.Block.first
      0

  refine
    ⟨
      (left, left),
      (right, left),
      ?_,
      ?_,
      ?_
    ⟩

  · intro hpairs

    have hfirst :
        left = right :=

      congrArg Prod.fst hpairs

    exact
      FanoRecovery.liftA_ne_liftB
        CayleyDicksonQuaternion.Block.first
        0
        hfirst

  · change
      (
        YangBaxterRouting.RoutedPacket.observable
          left,
        YangBaxterRouting.RoutedPacket.observable
          left
      ) =
      (
        YangBaxterRouting.RoutedPacket.observable
          right,
        YangBaxterRouting.RoutedPacket.observable
          left
      )

    rw [
      FanoRecovery.observable_liftA,
      FanoRecovery.observable_liftB
    ]

  · change
      (
        FanoRecovery.routeA,
        FanoRecovery.routeA
      ) ≠
      (
        FanoRecovery.routeB,
        FanoRecovery.routeA
      )

    intro hrecords

    have hfirst :
        FanoRecovery.routeA =
          FanoRecovery.routeB :=

      congrArg Prod.fst hrecords

    exact
      FanoRecovery.routeA_ne_routeB
        hfirst


/--
The complete state is equivalent to visible data paired
with its escrow record.
-/
theorem complete_state_exactly_visible_plus_escrow :

    Nonempty
      (
        CompleteState ≃
          VisibleState × EscrowRecord
      ) := by

  exact
    ⟨completeEquivVisibleEscrow⟩


end MemoryEscrowRouted


#check MemoryEscrowRouted.CompleteState
#check MemoryEscrowRouted.VisibleState
#check MemoryEscrowRouted.EscrowRecord
#check MemoryEscrowRouted.escrow
#check MemoryEscrowRouted.decompose
#check MemoryEscrowRouted.reconstructPacket
#check MemoryEscrowRouted.reconstruct
#check MemoryEscrowRouted.reconstruct_decompose
#check MemoryEscrowRouted.decompose_reconstruct
#check MemoryEscrowRouted.decompose_injective
#check MemoryEscrowRouted.completeEquivVisibleEscrow
#check MemoryEscrowRouted.completeStep
#check MemoryEscrowRouted.visibleStep
#check MemoryEscrowRouted.escrowStep
#check MemoryEscrowRouted.decompose_completeStep
#check MemoryEscrowRouted.observe_completeStep
#check MemoryEscrowRouted.escrow_completeStep
#check MemoryEscrowRouted.reconstruct_step
#check MemoryEscrowRouted.reversibleComplete
#check MemoryEscrowRouted.recovers_previous_complete
#check MemoryEscrowRouted.recovers_after
#check MemoryEscrowRouted.recovers_initial
#check MemoryEscrowRouted.escrowHistory
#check MemoryEscrowRouted.escrowHistory_succ
#check MemoryEscrowRouted.escrowHistory_recovers_previous
#check MemoryEscrowRouted.visible_not_injective
#check MemoryEscrowRouted.visible_with_escrow_injective
#check MemoryEscrowRouted.escrow_distinguishes_hidden_residue
#check MemoryEscrowRouted.complete_state_exactly_visible_plus_escrow
