import KTLean.YangBaxterForcingCoherence
import KTLean.SevenForcingFanoEquivalence

/-!
# Packets Carrying Forced Fano and Pascal Data

## Formal status

**Level 1 — Concrete woven carrier and coherent exchange witness.**

The preceding forcing chains established:

1. the minimal nondegenerate multiplicative completion geometry is the
   Fano plane;
2. the unique single-seed two-parent triadic additive field is Pascal
   modulo three;
3. three-channel path independence is exactly the Yang–Baxter
   coherence condition.

This module packages the two forced structures into one routed object.

A woven packet carries:

* an explicit Fano address;
* a Pascal row and position;
* a payload.

Its Pascal control state is not stored independently. It is derived
from the forced field `PascalMod3.control`.

The elementary woven exchange swaps complete packets. Therefore the
Fano address, Pascal address, derived Pascal control, and payload move
together. The exchange is reversible and three-channel coherent.

This module supplies a concrete coherent witness. It does not yet prove
that every admissible Fano–Pascal intertwining must be this exchange.
-/

namespace YangBaxterForcingWovenPacket

universe u

open YangBaxterRouting
open YangBaxterForcingCoherence

/--
An address in the forced Pascal modulo-three field.
-/
structure PascalAddress where

  row :
    Nat

  position :
    Nat

  deriving DecidableEq, Repr

/--
The forced Pascal control state at an address.
-/
def PascalAddress.control
    (address : PascalAddress) :
    PascalMod3.Control :=

  PascalMod3.control
    address.row
    address.position

/--
A woven packet carrying the forced multiplicative and additive
addresses together with an arbitrary payload.
-/
structure WovenPacket
    (Payload : Type u) where

  fanoAddress :
    Fano.Point

  pascalAddress :
    PascalAddress

  payload :
    Payload

/--
The forced Pascal control carried by a woven packet.
-/
def WovenPacket.pascalControl
    {Payload : Type u}
    (packet : WovenPacket Payload) :
    PascalMod3.Control :=

  packet.pascalAddress.control

/--
The structural Fano–Pascal address of a woven packet.
-/
def WovenPacket.address
    {Payload : Type u}
    (packet : WovenPacket Payload) :
    Fano.Point × PascalAddress :=

  (
    packet.fanoAddress,
    packet.pascalAddress
  )

/--
The visible Fano address and payload, omitting the Pascal routing
history.
-/
def WovenPacket.observable
    {Payload : Type u}
    (packet : WovenPacket Payload) :
    Fano.Point × Payload :=

  (
    packet.fanoAddress,
    packet.payload
  )

/--
Exchange two complete woven packets.

All structural and payload data travel together.
-/
def wovenExchange
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    WovenPacket Payload ×
      WovenPacket Payload :=

  crossing pair

/--
Woven exchange swaps two complete packets.
-/
@[simp]
theorem wovenExchange_pair
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    wovenExchange (left, right) =
      (right, left) := by

  rfl

/--
Woven exchange is reversible.
-/
theorem wovenExchange_involutive
    {Payload : Type u} :
    Function.Involutive
      (@wovenExchange Payload) := by

  intro pair

  cases pair

  rfl

/--
The Fano addresses travel with their packets.
-/
@[simp]
theorem wovenExchange_fanoAddresses
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    (
      (wovenExchange (left, right)).1.fanoAddress,
      (wovenExchange (left, right)).2.fanoAddress
    ) =
      (
        right.fanoAddress,
        left.fanoAddress
      ) := by

  rfl

/--
The Pascal addresses travel with their packets.
-/
@[simp]
theorem wovenExchange_pascalAddresses
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    (
      (wovenExchange (left, right)).1.pascalAddress,
      (wovenExchange (left, right)).2.pascalAddress
    ) =
      (
        right.pascalAddress,
        left.pascalAddress
      ) := by

  rfl

/--
The forced Pascal control states travel with their packets.
-/
@[simp]
theorem wovenExchange_pascalControls
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    (
      WovenPacket.pascalControl
        (wovenExchange (left, right)).1,
      WovenPacket.pascalControl
        (wovenExchange (left, right)).2
    ) =
      (
        WovenPacket.pascalControl right,
        WovenPacket.pascalControl left
      ) := by

  rfl

/--
The complete Fano–Pascal addresses travel together.
-/
@[simp]
theorem wovenExchange_addresses
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    (
      WovenPacket.address
        (wovenExchange (left, right)).1,
      WovenPacket.address
        (wovenExchange (left, right)).2
    ) =
      (
        WovenPacket.address right,
        WovenPacket.address left
      ) := by

  rfl

/--
The payloads travel with their packets.
-/
@[simp]
theorem wovenExchange_payloads
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    (
      (wovenExchange (left, right)).1.payload,
      (wovenExchange (left, right)).2.payload
    ) =
      (
        right.payload,
        left.payload
      ) := by

  rfl

/--
The observable projection commutes with woven exchange.
-/
theorem observable_projection_commutes
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    mapPair
        WovenPacket.observable
        (wovenExchange pair) =
      crossing
        (
          mapPair
            WovenPacket.observable
            pair
        ) := by

  exact
    mapPair_crossing
      WovenPacket.observable
      pair

/--
The complete structural-address projection commutes with woven
exchange.
-/
theorem address_projection_commutes
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    mapPair
        WovenPacket.address
        (wovenExchange pair) =
      crossing
        (
          mapPair
            WovenPacket.address
            pair
        ) := by

  exact
    mapPair_crossing
      WovenPacket.address
      pair

/--
Woven exchange satisfies the Yang–Baxter relation.
-/
theorem wovenExchange_satisfies_yangBaxter
    {Payload : Type u} :
    SatisfiesYangBaxter
      (@wovenExchange Payload) := by

  exact
    crossing_satisfies_yang_baxter

/--
Woven exchange is three-channel coherent.
-/
theorem wovenExchange_threeChannelCoherent
    {Payload : Type u} :
    ThreeChannelCoherent
      (@wovenExchange Payload) := by

  exact
    yangBaxter_gives_coherence
      wovenExchange_satisfies_yangBaxter

/--
The two admissible three-exchange histories agree for every triple of
woven packets.
-/
theorem woven_histories_agree
    {Payload : Type u}
    (triple :
      Triple (WovenPacket Payload)) :
    firstExchangeHistory
        (@wovenExchange Payload)
        triple =
      secondExchangeHistory
        (@wovenExchange Payload)
        triple := by

  exact
    wovenExchange_threeChannelCoherent
      triple

/--
Both coherent histories reverse the exterior woven packets while
preserving the middle packet.
-/
theorem woven_coherent_outcome
    {Payload : Type u}
    (first second third : WovenPacket Payload) :
    firstExchangeHistory
        (@wovenExchange Payload)
        {
          first := first
          second := second
          third := third
        } =
      {
        first := third
        second := second
        third := first
      }
      ∧
    secondExchangeHistory
        (@wovenExchange Payload)
        {
          first := first
          second := second
          third := third
        } =
      {
        first := third
        second := second
        third := first
      } := by

  constructor <;>
    rfl

end YangBaxterForcingWovenPacket

#check YangBaxterForcingWovenPacket.PascalAddress
#check YangBaxterForcingWovenPacket.PascalAddress.control
#check YangBaxterForcingWovenPacket.WovenPacket
#check YangBaxterForcingWovenPacket.WovenPacket.pascalControl
#check YangBaxterForcingWovenPacket.WovenPacket.address
#check YangBaxterForcingWovenPacket.wovenExchange
#check YangBaxterForcingWovenPacket.wovenExchange_involutive
#check YangBaxterForcingWovenPacket.wovenExchange_fanoAddresses
#check YangBaxterForcingWovenPacket.wovenExchange_pascalControls
#check YangBaxterForcingWovenPacket.address_projection_commutes
#check YangBaxterForcingWovenPacket.wovenExchange_satisfies_yangBaxter
#check YangBaxterForcingWovenPacket.wovenExchange_threeChannelCoherent
#check YangBaxterForcingWovenPacket.woven_histories_agree
#check YangBaxterForcingWovenPacket.woven_coherent_outcome
