import KTLean.YangBaxterForcingAdmissibleExchange

/-!
# Faithful Exchange Forces Ordinary Crossing

## Formal status

**Level 2 — Classification under full-state transport.**

The earlier admissibility interface preserves:

* the Fano address;
* the derived Pascal control;
* the payload.

That interface intentionally does not yet preserve the full Pascal
address. Since multiple Pascal addresses may carry the same control,
those conditions alone do not determine an exchange uniquely.

This module removes that residual freedom.

A faithful exchange transports:

1. the complete Fano–Pascal address;
2. the payload;

with each packet unchanged internally.

Under these requirements, the local exchange is extensionally forced
to be ordinary crossing of complete woven packets.

Reversibility and Yang–Baxter coherence then follow as consequences,
rather than additional choices.
-/

namespace YangBaxterForcingFaithfulExchange

universe u

open YangBaxterRouting
open YangBaxterForcingCoherence
open YangBaxterForcingWovenPacket
open YangBaxterForcingWovenProjections
open YangBaxterForcingIntertwinedOperation
open YangBaxterForcingAdmissibleExchange

/--
The complete structural address of a woven packet.
-/
abbrev FullAddress :=
  Fano.Point × PascalAddress

/--
Project a pair of woven packets to their complete structural
addresses.
-/
def projectFullAddresses
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    FullAddress × FullAddress :=

  (
    pair.1.address,
    pair.2.address
  )

/--
A faithful exchange transports the complete structural address and
payload of each packet without internal alteration.
-/
structure Faithful
    {Payload : Type u}
    (exchange : Exchange Payload) :
    Prop where

  addresses_exchange :
    ∀ pair,
      projectFullAddresses
          (exchange pair) =
        crossing
          (
            projectFullAddresses
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
A woven packet is determined by its complete structural address and
payload.
-/
theorem wovenPacket_eq_of_address_payload
    {Payload : Type u}
    {first second : WovenPacket Payload}
    (hAddress :
      first.address =
        second.address)
    (hPayload :
      first.payload =
        second.payload) :
    first =
      second := by

  cases first with

  | mk firstFano firstPascal firstPayload =>

      cases second with

      | mk secondFano secondPascal secondPayload =>

          simp only [
            WovenPacket.address
          ] at hAddress

          have hFano :
              firstFano =
                secondFano :=
            congrArg
              Prod.fst
              hAddress

          have hPascal :
              firstPascal =
                secondPascal :=
            congrArg
              Prod.snd
              hAddress

          cases hFano
          cases hPascal
          cases hPayload

          rfl

/--
The concrete woven exchange is faithful.
-/
theorem wovenExchange_faithful
    {Payload : Type u} :
    Faithful
      (@wovenExchange Payload) where

  addresses_exchange := by
    intro pair

    rcases pair with ⟨left, right⟩

    rfl

  payloads_exchange := by
    intro pair

    rcases pair with ⟨left, right⟩

    rfl

/--
A faithful exchange sends the first output packet to the original
right packet.
-/
theorem faithful_first_output
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange)
    (left right : WovenPacket Payload) :
    (exchange (left, right)).1 =
      right := by

  have hAddresses :=
    hFaithful.addresses_exchange
      (left, right)

  have hPayloads :=
    hFaithful.payloads_exchange
      (left, right)

  have hAddressFirst :
      (exchange (left, right)).1.address =
        right.address := by

    exact
      congrArg
        Prod.fst
        hAddresses

  have hPayloadFirst :
      (exchange (left, right)).1.payload =
        right.payload := by

    exact
      congrArg
        Prod.fst
        hPayloads

  exact
    wovenPacket_eq_of_address_payload
      hAddressFirst
      hPayloadFirst

/--
A faithful exchange sends the second output packet to the original
left packet.
-/
theorem faithful_second_output
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange)
    (left right : WovenPacket Payload) :
    (exchange (left, right)).2 =
      left := by

  have hAddresses :=
    hFaithful.addresses_exchange
      (left, right)

  have hPayloads :=
    hFaithful.payloads_exchange
      (left, right)

  have hAddressSecond :
      (exchange (left, right)).2.address =
        left.address := by

    exact
      congrArg
        Prod.snd
        hAddresses

  have hPayloadSecond :
      (exchange (left, right)).2.payload =
        left.payload := by

    exact
      congrArg
        Prod.snd
        hPayloads

  exact
    wovenPacket_eq_of_address_payload
      hAddressSecond
      hPayloadSecond

/--
Every faithful exchange is pointwise ordinary crossing.
-/
theorem faithful_exchange_pair
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange)
    (left right : WovenPacket Payload) :
    exchange (left, right) =
      (right, left) := by

  apply Prod.ext

  · exact
      faithful_first_output
        hFaithful
        left
        right

  · exact
      faithful_second_output
        hFaithful
        left
        right

/--
Every faithful exchange is extensionally equal to the concrete woven
exchange.
-/
theorem faithful_exchange_eq_wovenExchange
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange) :
    exchange =
      @wovenExchange Payload := by

  funext pair

  rcases pair with ⟨left, right⟩

  exact
    faithful_exchange_pair
      hFaithful
      left
      right

/--
Every faithful exchange is involutive.
-/
theorem faithful_involutive
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange) :
    Function.Involutive exchange := by

  rw [
    faithful_exchange_eq_wovenExchange
      hFaithful
  ]

  exact
    wovenExchange_involutive

/--
Every faithful exchange satisfies the Yang–Baxter relation.
-/
theorem faithful_satisfies_yangBaxter
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange) :
    SatisfiesYangBaxter exchange := by

  rw [
    faithful_exchange_eq_wovenExchange
      hFaithful
  ]

  exact
    wovenExchange_satisfies_yangBaxter

/--
Every faithful exchange is three-channel coherent.
-/
theorem faithful_threeChannelCoherent
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange) :
    ThreeChannelCoherent exchange := by

  exact
    yangBaxter_gives_coherence
      (
        faithful_satisfies_yangBaxter
          hFaithful
      )

/--
Every faithful exchange satisfies the earlier admissibility
interface.
-/
theorem faithful_admissible
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange) :
    Admissible exchange := by

  rw [
    faithful_exchange_eq_wovenExchange
      hFaithful
  ]

  exact
    wovenExchange_admissible

/--
There exists exactly one faithful exchange, namely ordinary crossing
of complete woven packets.
-/
theorem existsUnique_faithful_exchange
    {Payload : Type u} :
    ∃! exchange : Exchange Payload,
      Faithful exchange := by

  refine
    ⟨
      @wovenExchange Payload,
      wovenExchange_faithful,
      ?_
    ⟩

  intro exchange hFaithful

  exact
    faithful_exchange_eq_wovenExchange
      hFaithful

/--
Full-state transport forces reversible Yang–Baxter weaving and joint
Fano–Pascal preservation.
-/
theorem faithful_transport_forces_weave
    {Payload : Type u}
    {exchange : Exchange Payload}
    (hFaithful : Faithful exchange) :
    exchange =
        @wovenExchange Payload
      ∧
    Function.Involutive exchange
      ∧
    SatisfiesYangBaxter exchange
      ∧
    Admissible exchange := by

  exact
    ⟨
      faithful_exchange_eq_wovenExchange hFaithful,
      faithful_involutive hFaithful,
      faithful_satisfies_yangBaxter hFaithful,
      faithful_admissible hFaithful
    ⟩

end YangBaxterForcingFaithfulExchange

#check YangBaxterForcingFaithfulExchange.FullAddress
#check YangBaxterForcingFaithfulExchange.projectFullAddresses
#check YangBaxterForcingFaithfulExchange.Faithful
#check YangBaxterForcingFaithfulExchange.wovenPacket_eq_of_address_payload
#check YangBaxterForcingFaithfulExchange.wovenExchange_faithful
#check YangBaxterForcingFaithfulExchange.faithful_first_output
#check YangBaxterForcingFaithfulExchange.faithful_second_output
#check YangBaxterForcingFaithfulExchange.faithful_exchange_pair
#check YangBaxterForcingFaithfulExchange.faithful_exchange_eq_wovenExchange
#check YangBaxterForcingFaithfulExchange.faithful_involutive
#check YangBaxterForcingFaithfulExchange.faithful_satisfies_yangBaxter
#check YangBaxterForcingFaithfulExchange.faithful_admissible
#check YangBaxterForcingFaithfulExchange.existsUnique_faithful_exchange
#check YangBaxterForcingFaithfulExchange.faithful_transport_forces_weave
