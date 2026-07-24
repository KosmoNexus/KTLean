import KTLean.YangBaxterForcingWovenPacket

/-!
# Projection Laws for the Coherent Fano–Pascal Weave

## Formal status

**Level 1 — Structural preservation by the concrete woven exchange.**

A woven packet carries:

* a forced Fano address;
* a forced Pascal address and derived control;
* a payload.

The preceding module proved that one local exchange transports all of
these data together.

This module lifts those preservation laws from one crossing to the two
minimal three-crossing histories.

It proves that:

1. the Fano projection commutes with each braid history;
2. the Pascal-address projection commutes with each braid history;
3. the forced Pascal-control projection commutes with each history;
4. the combined Fano–Pascal address projection commutes with each
   history;
5. the two histories therefore remain equal after every structural
   projection.

No data component is discarded in establishing coherence.
-/

namespace YangBaxterForcingWovenProjections

universe u v

open YangBaxterRouting
open YangBaxterForcingCoherence
open YangBaxterForcingWovenPacket

/--
Map a function over all three members of a triple.
-/
def mapTriple
    {α : Type u}
    {β : Type v}
    (f : α → β)
    (triple : Triple α) :
    Triple β :=

  {
    first := f triple.first
    second := f triple.second
    third := f triple.third
  }

/--
Pointwise projection commutes with the first adjacent action whenever
the pair projection commutes with the local exchange.
-/
theorem mapTriple_act12_crossing
    {α : Type u}
    {β : Type v}
    (f : α → β)
    (triple : Triple α) :
    mapTriple f
        (act12 (@crossing α) triple) =
      act12
        (@crossing β)
        (mapTriple f triple) := by

  cases triple

  rfl

/--
Pointwise projection commutes with the second adjacent action.
-/
theorem mapTriple_act23_crossing
    {α : Type u}
    {β : Type v}
    (f : α → β)
    (triple : Triple α) :
    mapTriple f
        (act23 (@crossing α) triple) =
      act23
        (@crossing β)
        (mapTriple f triple) := by

  cases triple

  rfl

/--
Pointwise projection commutes with the first three-exchange history.
-/
theorem mapTriple_firstExchangeHistory
    {α : Type u}
    {β : Type v}
    (f : α → β)
    (triple : Triple α) :
    mapTriple f
        (
          firstExchangeHistory
            (@crossing α)
            triple
        ) =
      firstExchangeHistory
        (@crossing β)
        (mapTriple f triple) := by

  cases triple

  rfl

/--
Pointwise projection commutes with the second three-exchange history.
-/
theorem mapTriple_secondExchangeHistory
    {α : Type u}
    {β : Type v}
    (f : α → β)
    (triple : Triple α) :
    mapTriple f
        (
          secondExchangeHistory
            (@crossing α)
            triple
        ) =
      secondExchangeHistory
        (@crossing β)
        (mapTriple f triple) := by

  cases triple

  rfl

/--
Project a woven packet to its Fano address.
-/
def fanoProjection
    {Payload : Type u}
    (packet : WovenPacket Payload) :
    Fano.Point :=

  packet.fanoAddress

/--
Project a woven packet to its Pascal address.
-/
def pascalAddressProjection
    {Payload : Type u}
    (packet : WovenPacket Payload) :
    PascalAddress :=

  packet.pascalAddress

/--
Project a woven packet to its forced Pascal control.
-/
def pascalControlProjection
    {Payload : Type u}
    (packet : WovenPacket Payload) :
    PascalMod3.Control :=

  packet.pascalControl

/--
Project a woven packet to its complete forced structural address.
-/
def structuralProjection
    {Payload : Type u}
    (packet : WovenPacket Payload) :
    Fano.Point × PascalAddress :=

  packet.address

/--
The Fano projection commutes with the first woven history.
-/
theorem fanoProjection_firstHistory
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple fanoProjection
        (
          firstExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      firstExchangeHistory
        (@crossing Fano.Point)
        (
          mapTriple
            fanoProjection
            triple
        ) := by

  cases triple

  rfl

/--
The Fano projection commutes with the second woven history.
-/
theorem fanoProjection_secondHistory
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple fanoProjection
        (
          secondExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      secondExchangeHistory
        (@crossing Fano.Point)
        (
          mapTriple
            fanoProjection
            triple
        ) := by

  cases triple

  rfl

/--
The Pascal-address projection commutes with the first woven history.
-/
theorem pascalAddressProjection_firstHistory
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple pascalAddressProjection
        (
          firstExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      firstExchangeHistory
        (@crossing PascalAddress)
        (
          mapTriple
            pascalAddressProjection
            triple
        ) := by

  cases triple

  rfl

/--
The Pascal-address projection commutes with the second woven history.
-/
theorem pascalAddressProjection_secondHistory
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple pascalAddressProjection
        (
          secondExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      secondExchangeHistory
        (@crossing PascalAddress)
        (
          mapTriple
            pascalAddressProjection
            triple
        ) := by

  cases triple

  rfl

/--
The forced Pascal-control projection commutes with the first history.
-/
theorem pascalControlProjection_firstHistory
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple pascalControlProjection
        (
          firstExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      firstExchangeHistory
        (@crossing PascalMod3.Control)
        (
          mapTriple
            pascalControlProjection
            triple
        ) := by

  cases triple

  rfl

/--
The forced Pascal-control projection commutes with the second history.
-/
theorem pascalControlProjection_secondHistory
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple pascalControlProjection
        (
          secondExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      secondExchangeHistory
        (@crossing PascalMod3.Control)
        (
          mapTriple
            pascalControlProjection
            triple
        ) := by

  cases triple

  rfl

/--
The combined Fano–Pascal structural projection commutes with the first
history.
-/
theorem structuralProjection_firstHistory
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple structuralProjection
        (
          firstExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      firstExchangeHistory
        (@crossing (Fano.Point × PascalAddress))
        (
          mapTriple
            structuralProjection
            triple
        ) := by

  cases triple

  rfl

/--
The combined Fano–Pascal structural projection commutes with the second
history.
-/
theorem structuralProjection_secondHistory
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple structuralProjection
        (
          secondExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      secondExchangeHistory
        (@crossing (Fano.Point × PascalAddress))
        (
          mapTriple
            structuralProjection
            triple
        ) := by

  cases triple

  rfl

/--
The two coherent woven histories remain equal after Fano projection.
-/
theorem fanoProjected_histories_agree
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple fanoProjection
        (
          firstExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      mapTriple fanoProjection
        (
          secondExchangeHistory
            (@wovenExchange Payload)
            triple
        ) := by

  rw [
    fanoProjection_firstHistory,
    fanoProjection_secondHistory
  ]

  exact
    crossing_threeChannelCoherent
      (
        mapTriple
          fanoProjection
          triple
      )

/--
The two coherent woven histories remain equal after forced Pascal
control projection.
-/
theorem pascalProjected_histories_agree
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple pascalControlProjection
        (
          firstExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      mapTriple pascalControlProjection
        (
          secondExchangeHistory
            (@wovenExchange Payload)
            triple
        ) := by

  rw [
    pascalControlProjection_firstHistory,
    pascalControlProjection_secondHistory
  ]

  exact
    crossing_threeChannelCoherent
      (
        mapTriple
          pascalControlProjection
          triple
      )

/--
The two coherent woven histories remain equal after the complete
Fano–Pascal structural projection.
-/
theorem structurallyProjected_histories_agree
    {Payload : Type u}
    (triple : Triple (WovenPacket Payload)) :
    mapTriple structuralProjection
        (
          firstExchangeHistory
            (@wovenExchange Payload)
            triple
        ) =
      mapTriple structuralProjection
        (
          secondExchangeHistory
            (@wovenExchange Payload)
            triple
        ) := by

  rw [
    structuralProjection_firstHistory,
    structuralProjection_secondHistory
  ]

  exact
    crossing_threeChannelCoherent
      (
        mapTriple
          structuralProjection
          triple
      )

end YangBaxterForcingWovenProjections

#check YangBaxterForcingWovenProjections.mapTriple
#check YangBaxterForcingWovenProjections.mapTriple_act12_crossing
#check YangBaxterForcingWovenProjections.mapTriple_act23_crossing
#check YangBaxterForcingWovenProjections.mapTriple_firstExchangeHistory
#check YangBaxterForcingWovenProjections.mapTriple_secondExchangeHistory
#check YangBaxterForcingWovenProjections.fanoProjection
#check YangBaxterForcingWovenProjections.pascalControlProjection
#check YangBaxterForcingWovenProjections.structuralProjection
#check YangBaxterForcingWovenProjections.fanoProjection_firstHistory
#check YangBaxterForcingWovenProjections.pascalControlProjection_secondHistory
#check YangBaxterForcingWovenProjections.structuralProjection_firstHistory
#check YangBaxterForcingWovenProjections.fanoProjected_histories_agree
#check YangBaxterForcingWovenProjections.pascalProjected_histories_agree
#check YangBaxterForcingWovenProjections.structurallyProjected_histories_agree
