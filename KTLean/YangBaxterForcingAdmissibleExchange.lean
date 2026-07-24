import KTLean.YangBaxterForcingIntertwinedOperation

/-!
# Admissible Exchanges of Woven Fano–Pascal Packets

## Formal status

**Level 1 — Abstract admissibility interface and consequences.**

The preceding modules constructed one concrete woven exchange:
ordinary crossing of complete packets.

This module separates the properties used by that construction from
the construction itself.

An exchange of woven packets is admissible when:

1. it is reversible;
2. its two minimal three-channel histories agree;
3. the joint Fano–Pascal packet state is exchanged without alteration;
4. the payloads are exchanged without alteration.

From these operational conditions we derive:

* the Yang–Baxter relation;
* transport of Fano addresses;
* transport of Pascal controls;
* invariance of the joint Fano–Pascal interaction value.

This is an interface theorem, not yet a uniqueness theorem. A later
classification module may ask whether every admissible exchange is
extensionally equal to ordinary crossing.
-/

namespace YangBaxterForcingAdmissibleExchange

universe u

open YangBaxterRouting
open YangBaxterForcingCoherence
open YangBaxterForcingWovenPacket
open YangBaxterForcingWovenProjections
open YangBaxterForcingIntertwinedOperation

/--
A local exchange of woven packets.
-/
abbrev Exchange
    (Payload : Type u) :=
  WovenPacket Payload × WovenPacket Payload →
    WovenPacket Payload × WovenPacket Payload

/--
Project a pair of woven packets to their joint structural states.
-/
def projectPacketStates
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    StructuralState × StructuralState :=

  (
    packetState pair.1,
    packetState pair.2
  )

/--
Project a pair of woven packets to their payloads.
-/
def projectPayloads
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    Payload × Payload :=

  (
    pair.1.payload,
    pair.2.payload
  )

/--
Operational admissibility for a woven-packet exchange.

The structural and payload projections are required to behave exactly
as an adjacent exchange: the right packet moves left and the left
packet moves right, with their internal data unchanged.
-/
structure Admissible
    {Payload : Type u}
    (exchange : Exchange Payload) :
    Prop where

  reversible :
    Function.Involutive exchange

  coherent :
    ThreeChannelCoherent exchange

  packetStates_exchange :
    ∀ pair,
      projectPacketStates
          (exchange pair) =
        crossing
          (
            projectPacketStates
              pair
          )

  payloads_exchange :
    ∀ pair,
      projectPayloads
          (exchange pair) =
        crossing
          (
            projectPayloads
              pair
          )

/--
The concrete woven exchange is admissible.
-/
theorem wovenExchange_admissible
    {Payload : Type u} :
    Admissible
      (@wovenExchange Payload) where

  reversible :=
    wovenExchange_involutive

  coherent :=
    wovenExchange_threeChannelCoherent

  packetStates_exchange := by
    intro pair

    exact
      packetState_projection_commutes
        pair

  payloads_exchange := by
    intro pair

    rcases pair with ⟨left, right⟩

    rfl

/--
Every admissible woven exchange satisfies the Yang–Baxter relation.
-/
theorem admissible_satisfies_yangBaxter
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange) :
    SatisfiesYangBaxter exchange := by

  exact
    coherence_forces_yangBaxter
      hAdmissible.coherent

/--
Every admissible exchange is reversible.
-/
theorem admissible_involutive
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange) :
    Function.Involutive exchange :=

  hAdmissible.reversible

/--
An admissible exchange swaps the two joint structural packet states.
-/
theorem admissible_packetStates
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange)
    (left right : WovenPacket Payload) :
    projectPacketStates
        (exchange (left, right)) =
      (
        packetState right,
        packetState left
      ) := by

  simpa [
    projectPacketStates,
    crossing
  ] using
    hAdmissible.packetStates_exchange
      (left, right)

/--
An admissible exchange swaps the Fano addresses.
-/
theorem admissible_fanoAddresses
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange)
    (left right : WovenPacket Payload) :
    (
      (exchange (left, right)).1.fanoAddress,
      (exchange (left, right)).2.fanoAddress
    ) =
      (
        right.fanoAddress,
        left.fanoAddress
      ) := by

  have hStates :=
    admissible_packetStates
      hAdmissible
      left
      right

  exact
    congrArg
      (fun pair =>
        (
          pair.1.1,
          pair.2.1
        ))
      hStates

/--
An admissible exchange swaps the forced Pascal controls.
-/
theorem admissible_pascalControls
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange)
    (left right : WovenPacket Payload) :
    (
      (exchange (left, right)).1.pascalControl,
      (exchange (left, right)).2.pascalControl
    ) =
      (
        right.pascalControl,
        left.pascalControl
      ) := by

  have hStates :=
    admissible_packetStates
      hAdmissible
      left
      right

  exact
    congrArg
      (fun pair =>
        (
          pair.1.2,
          pair.2.2
        ))
      hStates

/--
An admissible exchange swaps the payloads.
-/
theorem admissible_payloads
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange)
    (left right : WovenPacket Payload) :
    (
      (exchange (left, right)).1.payload,
      (exchange (left, right)).2.payload
    ) =
      (
        right.payload,
        left.payload
      ) := by

  simpa [
    projectPayloads,
    crossing
  ] using
    hAdmissible.payloads_exchange
      (left, right)

/--
The joint structural interaction value of an arbitrary packet pair.
-/
def pairInteractionValue
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    StructuralState :=

  combine
    (packetState pair.1)
    (packetState pair.2)

/--
Every admissible exchange preserves the combined Fano–Pascal
interaction value.
-/
theorem admissible_preserves_interaction
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange)
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    pairInteractionValue
        (exchange pair) =
      pairInteractionValue
        pair := by

  have hStates :
      projectPacketStates
          (exchange pair) =
        crossing
          (
            projectPacketStates
              pair
          ) :=
    hAdmissible.packetStates_exchange
      pair

  have hCombined :=
    congrArg
      (fun states =>
        combine
          states.1
          states.2)
      hStates

  change
    combine
        (packetState (exchange pair).1)
        (packetState (exchange pair).2) =
      combine
        (packetState pair.1)
        (packetState pair.2)

  calc
    combine
        (packetState (exchange pair).1)
        (packetState (exchange pair).2) =
      combine
        (packetState pair.2)
        (packetState pair.1) := by

      simpa [
        projectPacketStates,
        crossing
      ] using hCombined

    _ =
      combine
        (packetState pair.1)
        (packetState pair.2) := by

      exact
        combine_commutative
          (packetState pair.2)
          (packetState pair.1)

/--
Every admissible exchange preserves the Fano component of the joint
interaction.
-/
theorem admissible_preserves_fanoInteraction
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange)
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    (
      pairInteractionValue
        (exchange pair)
    ).1 =
      (
        pairInteractionValue
          pair
      ).1 := by

  exact
    congrArg
      Prod.fst
      (
        admissible_preserves_interaction
          hAdmissible
          pair
      )

/--
Every admissible exchange preserves the Pascal component of the joint
interaction.
-/
theorem admissible_preserves_pascalInteraction
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange)
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    (
      pairInteractionValue
        (exchange pair)
    ).2 =
      (
        pairInteractionValue
          pair
      ).2 := by

  exact
    congrArg
      Prod.snd
      (
        admissible_preserves_interaction
          hAdmissible
          pair
      )

/--
For every admissible exchange, the two minimal exchange histories
agree and both forced interaction components are invariant.
-/
theorem admissibility_forces_coherent_intertwining
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hAdmissible : Admissible exchange) :
    ThreeChannelCoherent exchange
      ∧
    (
      ∀ pair,
        (
          pairInteractionValue
            (exchange pair)
        ).1 =
          (
            pairInteractionValue
              pair
          ).1
    )
      ∧
    (
      ∀ pair,
        (
          pairInteractionValue
            (exchange pair)
        ).2 =
          (
            pairInteractionValue
              pair
          ).2
    ) := by

  refine
    ⟨
      hAdmissible.coherent,
      ?_,
      ?_
    ⟩

  · intro pair

    exact
      admissible_preserves_fanoInteraction
        hAdmissible
        pair

  · intro pair

    exact
      admissible_preserves_pascalInteraction
        hAdmissible
        pair

end YangBaxterForcingAdmissibleExchange

#check YangBaxterForcingAdmissibleExchange.Exchange
#check YangBaxterForcingAdmissibleExchange.projectPacketStates
#check YangBaxterForcingAdmissibleExchange.projectPayloads
#check YangBaxterForcingAdmissibleExchange.Admissible
#check YangBaxterForcingAdmissibleExchange.wovenExchange_admissible
#check YangBaxterForcingAdmissibleExchange.admissible_satisfies_yangBaxter
#check YangBaxterForcingAdmissibleExchange.admissible_packetStates
#check YangBaxterForcingAdmissibleExchange.admissible_fanoAddresses
#check YangBaxterForcingAdmissibleExchange.admissible_pascalControls
#check YangBaxterForcingAdmissibleExchange.admissible_payloads
#check YangBaxterForcingAdmissibleExchange.pairInteractionValue
#check YangBaxterForcingAdmissibleExchange.admissible_preserves_interaction
#check YangBaxterForcingAdmissibleExchange.admissibility_forces_coherent_intertwining
