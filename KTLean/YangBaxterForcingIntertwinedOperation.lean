import KTLean.YangBaxterForcingWovenProjections

/-!
# A Joint Fano–Pascal Structural Operation

## Formal status

**Level 1 — Concrete compatibility of the woven exchange with the two
forced operations.**

The forced structures supply two distinct operations:

* Fano completion on the seven-point multiplicative geometry;
* closed triadic addition on the Pascal control alphabet.

This module combines them componentwise into one structural operation:

    (fano₁, pascal₁) ⋆ (fano₂, pascal₂)
      =
    (
      Fano.complete fano₁ fano₂,
      pascal₁ + pascal₂
    ).

The operation is not introduced as a replacement for either component.
It records their simultaneous action on one woven state.

Because both component operations are commutative, exchanging two
complete woven packets does not change their joint structural
interaction value.

Thus the same local weave is equivariant for:

1. the forced Fano operation;
2. the forced Pascal addition;
3. their combined structural operation.

This is a concrete intertwining witness. A later module will abstract
the admissibility conditions and determine what is forced by them.
-/

namespace YangBaxterForcingIntertwinedOperation

universe u

open PascalMod3
open PascalForcingTriadicAddition
open YangBaxterRouting
open YangBaxterForcingWovenPacket
open YangBaxterForcingWovenProjections

/--
A joint structural state consists of a forced Fano point and a forced
Pascal control state.
-/
abbrev StructuralState :=
  Fano.Point × Control

/--
The joint Fano–Pascal operation.

The Fano component uses the explicit forced Fano completion.
The Pascal component uses the explicit forced triadic addition.
-/
def combine
    (first second : StructuralState) :
    StructuralState :=

  (
    Fano.system.complete
      first.1
      second.1,

    add
      first.2
      second.2
  )

/--
The joint operation is commutative because both forced component
operations are commutative.
-/
theorem combine_commutative
    (first second : StructuralState) :
    combine first second =
      combine second first := by

  apply Prod.ext

  · exact
      Fano.system.complete_comm
        first.1
        second.1

  · exact
      add_commutative
        first.2
        second.2

/--
Project a woven packet to the joint structural state formed from its
Fano address and forced Pascal control.
-/
def packetState
    {Payload : Type u}
    (packet : WovenPacket Payload) :
    StructuralState :=

  (
    packet.fanoAddress,
    packet.pascalControl
  )

/--
Woven exchange swaps the two complete joint structural states.
-/
@[simp]
theorem wovenExchange_packetStates
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    (
      packetState
        (wovenExchange (left, right)).1,
      packetState
        (wovenExchange (left, right)).2
    ) =
      (
        packetState right,
        packetState left
      ) := by

  rfl

/--
The joint structural interaction value of a packet pair.
-/
def interactionValue
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    StructuralState :=

  combine
    (packetState pair.1)
    (packetState pair.2)

/--
The Fano component of the joint interaction is exactly Fano
completion of the packet addresses.
-/
theorem interactionValue_fano
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    (
      interactionValue
        (left, right)
    ).1 =
      Fano.system.complete
        left.fanoAddress
        right.fanoAddress := by

  rfl

/--
The Pascal component of the joint interaction is exactly triadic
addition of the packet controls.
-/
theorem interactionValue_pascal
    {Payload : Type u}
    (left right : WovenPacket Payload) :
    (
      interactionValue
        (left, right)
    ).2 =
      add
        left.pascalControl
        right.pascalControl := by

  rfl

/--
Exchanging two woven packets preserves their joint structural
interaction value.
-/
theorem interactionValue_wovenExchange
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    interactionValue
        (wovenExchange pair) =
      interactionValue
        pair := by

  rcases pair with ⟨left, right⟩

  change
    combine
        (packetState right)
        (packetState left) =
      combine
        (packetState left)
        (packetState right)

  exact
    combine_commutative
      (packetState right)
      (packetState left)

/--
The Fano interaction value is invariant under woven exchange.
-/
theorem fanoInteraction_wovenExchange
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    (
      interactionValue
        (wovenExchange pair)
    ).1 =
      (
        interactionValue
          pair
      ).1 := by

  exact
    congrArg
      Prod.fst
      (
        interactionValue_wovenExchange
          pair
      )

/--
The Pascal interaction value is invariant under woven exchange.
-/
theorem pascalInteraction_wovenExchange
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    (
      interactionValue
        (wovenExchange pair)
    ).2 =
      (
        interactionValue
          pair
      ).2 := by

  exact
    congrArg
      Prod.snd
      (
        interactionValue_wovenExchange
          pair
      )

/--
The packet-state projection commutes with local woven exchange.
-/
theorem packetState_projection_commutes
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    mapPair
        packetState
        (wovenExchange pair) =
      crossing
        (
          mapPair
            packetState
            pair
        ) := by

  exact
    mapPair_crossing
      packetState
      pair

/--
Combining the packet states after exchange gives the same result as
combining them before exchange.
-/
theorem combine_after_exchange
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    combine
        (
          mapPair
            packetState
            (wovenExchange pair)
        ).1
        (
          mapPair
            packetState
            (wovenExchange pair)
        ).2
      =
    combine
        (
          mapPair
            packetState
            pair
        ).1
        (
          mapPair
            packetState
            pair
        ).2 := by

  exact
    interactionValue_wovenExchange
      pair

/--
The concrete woven exchange simultaneously intertwines the forced
Fano and Pascal operations.
-/
theorem wovenExchange_intertwines_forced_operations
    {Payload : Type u}
    (pair :
      WovenPacket Payload ×
        WovenPacket Payload) :
    (
      (
        interactionValue
          (wovenExchange pair)
      ).1 =
        (
          interactionValue
            pair
        ).1
    )
      ∧
    (
      (
        interactionValue
          (wovenExchange pair)
      ).2 =
        (
          interactionValue
            pair
        ).2
    ) := by

  exact
    ⟨
      fanoInteraction_wovenExchange pair,
      pascalInteraction_wovenExchange pair
    ⟩

end YangBaxterForcingIntertwinedOperation

#check YangBaxterForcingIntertwinedOperation.StructuralState
#check YangBaxterForcingIntertwinedOperation.combine
#check YangBaxterForcingIntertwinedOperation.combine_commutative
#check YangBaxterForcingIntertwinedOperation.packetState
#check YangBaxterForcingIntertwinedOperation.interactionValue
#check YangBaxterForcingIntertwinedOperation.interactionValue_fano
#check YangBaxterForcingIntertwinedOperation.interactionValue_pascal
#check YangBaxterForcingIntertwinedOperation.interactionValue_wovenExchange
#check YangBaxterForcingIntertwinedOperation.packetState_projection_commutes
#check YangBaxterForcingIntertwinedOperation.combine_after_exchange
#check YangBaxterForcingIntertwinedOperation.wovenExchange_intertwines_forced_operations
