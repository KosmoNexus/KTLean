import KTLean.BraidedQuaternion
import Mathlib.Logic.Function.Basic

/-!
# Yang–Baxter Routing

This module formalizes coherent local exchange of routed
Pascal-controlled packets.

A routed packet carries:

1. its Cayley–Dickson block;
2. its Pascal address;
3. its payload.

The Pascal control state is recoverable from the address.
The address therefore travels with the payload during an
exchange rather than being discarded.

The Yang–Baxter relation established here is

    R₁₂ R₂₃ R₁₂ = R₂₃ R₁₂ R₂₃.

This is a coherence condition on the order of adjacent
exchanges. It is not an associativity theorem, and it does
not assert that the routing data are uniquely determined.

Residual routing information remains present in the routed
packets and is preserved by the coherent exchange.
-/

namespace YangBaxterRouting


universe u v


/--
A triple of objects on which adjacent braid operators act.
-/
structure Triple
    (α : Type u) where

  first : α
  second : α
  third : α


/--
Apply a binary exchange operator to the first two positions
of a triple.
-/
def act12
    {α : Type u}
    (R : α × α → α × α)
    (triple : Triple α) :
    Triple α :=

  let result :=
    R
      (
        triple.first,
        triple.second
      )

  {
    first := result.1
    second := result.2
    third := triple.third
  }


/--
Apply a binary exchange operator to the final two positions
of a triple.
-/
def act23
    {α : Type u}
    (R : α × α → α × α)
    (triple : Triple α) :
    Triple α :=

  let result :=
    R
      (
        triple.second,
        triple.third
      )

  {
    first := triple.first
    second := result.1
    third := result.2
  }


/--
The left Yang–Baxter braid word

    R₁₂ R₂₃ R₁₂.
-/
def leftBraid
    {α : Type u}
    (R : α × α → α × α)
    (triple : Triple α) :
    Triple α :=

  act12 R
    (
      act23 R
        (
          act12 R triple
        )
    )


/--
The right Yang–Baxter braid word

    R₂₃ R₁₂ R₂₃.
-/
def rightBraid
    {α : Type u}
    (R : α × α → α × α)
    (triple : Triple α) :
    Triple α :=

  act23 R
    (
      act12 R
        (
          act23 R triple
        )
    )


/--
A binary exchange operator satisfies the Yang–Baxter
relation when the two three-exchange paths agree on every
triple.
-/
def SatisfiesYangBaxter
    {α : Type u}
    (R : α × α → α × α) :
    Prop :=

  ∀ triple,
    leftBraid R triple =
      rightBraid R triple


/--
The elementary exchange operator swaps two whole objects.
-/
def crossing
    {α : Type u}
    (pair : α × α) :
    α × α :=

  (
    pair.2,
    pair.1
  )


@[simp]
theorem crossing_pair
    {α : Type u}
    (x y : α) :

    crossing (x, y) =
      (y, x) := by

  rfl


/--
An elementary crossing is reversible.
-/
theorem crossing_involutive
    {α : Type u} :

    Function.Involutive
      (@crossing α) := by

  intro pair
  cases pair
  rfl


/--
The elementary crossing satisfies the Yang–Baxter
relation on every type.
-/
theorem crossing_satisfies_yang_baxter
    {α : Type u} :

    SatisfiesYangBaxter
      (@crossing α) := by

  intro triple
  cases triple
  rfl


/--
Both braid paths reverse the exterior objects while
preserving the middle object.
-/
@[simp]
theorem leftBraid_crossing
    {α : Type u}
    (x y z : α) :

    leftBraid
        (@crossing α)
        {
          first := x
          second := y
          third := z
        } =

      {
        first := z
        second := y
        third := x
      } := by

  rfl


@[simp]
theorem rightBraid_crossing
    {α : Type u}
    (x y z : α) :

    rightBraid
        (@crossing α)
        {
          first := x
          second := y
          third := z
        } =

      {
        first := z
        second := y
        third := x
      } := by

  rfl


/--
Map a function over both members of a pair.
-/
def mapPair
    {α : Type u}
    {β : Type v}
    (f : α → β)
    (pair : α × α) :
    β × β :=

  (
    f pair.1,
    f pair.2
  )


/--
Crossing commutes with every pointwise projection.

This permits visible data and hidden routing data to be
analyzed separately without breaking exchange coherence.
-/
@[simp]
theorem mapPair_crossing
    {α : Type u}
    {β : Type v}
    (f : α → β)
    (pair : α × α) :

    mapPair f
        (crossing pair) =

      crossing
        (mapPair f pair) := by

  cases pair
  rfl


/--
A routed packet carries its block, Pascal address, and
payload together.

Its control state is derived from the Pascal address rather
than stored independently.
-/
structure RoutedPacket
    (α : Type u) where

  block :
    CayleyDicksonQuaternion.Block

  address :
    BraidedQuaternion.PascalAddress

  payload :
    α


namespace RoutedPacket


/--
Recover the Pascal control state carried by a routed
packet.
-/
def control
    {α : Type u}
    (packet : RoutedPacket α) :
    PascalMod3.Control :=

  BraidedQuaternion.controlAt
    packet.address


/--
The visible block-and-payload projection of a packet.

The Pascal address is deliberately omitted from this
projection.
-/
def observable
    {α : Type u}
    (packet : RoutedPacket α) :
    CayleyDicksonQuaternion.Block × α :=

  (
    packet.block,
    packet.payload
  )


end RoutedPacket


/--
Exchange two complete routed packets.

The payload, block, and Pascal address travel together.
-/
def routedExchange
    {α : Type u}
    (pair :
      RoutedPacket α ×
        RoutedPacket α) :

    RoutedPacket α ×
      RoutedPacket α :=

  crossing pair


@[simp]
theorem routedExchange_pair
    {α : Type u}
    (left right : RoutedPacket α) :

    routedExchange
        (left, right) =

      (right, left) := by

  rfl


/--
Routed exchange is reversible.
-/
theorem routedExchange_involutive
    {α : Type u} :

    Function.Involutive
      (@routedExchange α) := by

  intro pair
  rcases pair with ⟨left, right⟩
  rfl


/--
Routed exchange satisfies the Yang–Baxter relation.
-/
theorem routedExchange_satisfies_yang_baxter
    {α : Type u} :

    SatisfiesYangBaxter
      (@routedExchange α) := by

  intro triple
  rcases triple with ⟨x, y, z⟩
  rfl


/--
The Pascal addresses are exchanged with their packets.
They are not erased by the crossing.
-/
@[simp]
theorem routedExchange_addresses
    {α : Type u}
    (left right : RoutedPacket α) :

    (
      (routedExchange
        (left, right)).1.address,

      (routedExchange
        (left, right)).2.address
    ) =

      (
        right.address,
        left.address
      ) := by

  rfl


/--
The derived Pascal control states travel with their
packets.
-/
@[simp]
theorem routedExchange_controls
    {α : Type u}
    (left right : RoutedPacket α) :

    (
      RoutedPacket.control
        (routedExchange
          (left, right)).1,

      RoutedPacket.control
        (routedExchange
          (left, right)).2
    ) =

      (
        RoutedPacket.control right,
        RoutedPacket.control left
      ) := by

  rfl


/--
The block labels travel with their packets.
-/
@[simp]
theorem routedExchange_blocks
    {α : Type u}
    (left right : RoutedPacket α) :

    (
      (routedExchange
        (left, right)).1.block,

      (routedExchange
        (left, right)).2.block
    ) =

      (
        right.block,
        left.block
      ) := by

  rfl


/--
The payloads travel with their packets.
-/
@[simp]
theorem routedExchange_payloads
    {α : Type u}
    (left right : RoutedPacket α) :

    (
      (routedExchange
        (left, right)).1.payload,

      (routedExchange
        (left, right)).2.payload
    ) =

      (
        right.payload,
        left.payload
      ) := by

  rfl


/--
Projecting away the Pascal address commutes with routed
exchange.

Consequently, the visible exchange can remain coherent
while routing history remains present in the full state.
-/
theorem observable_projection_commutes
    {α : Type u}
    (pair :
      RoutedPacket α ×
        RoutedPacket α) :

    mapPair
        RoutedPacket.observable
        (routedExchange pair) =

      crossing
        (
          mapPair
            RoutedPacket.observable
            pair
        ) := by

  simpa [routedExchange] using
    (
      mapPair_crossing
        RoutedPacket.observable
        pair
    )


/--
The two routed braid paths agree for every triple of
routed packets.
-/
theorem routed_braid_paths_agree
    {α : Type u}
    (triple :
      Triple (RoutedPacket α)) :

    leftBraid
        (@routedExchange α)
        triple =

      rightBraid
        (@routedExchange α)
        triple := by

  exact
    routedExchange_satisfies_yang_baxter
      triple


/--
A package containing both local reversibility and
Yang–Baxter coherence.
-/
structure CoherentExchange
    (α : Type u) where

  exchange :
    α × α → α × α

  involutive :
    Function.Involutive exchange

  yangBaxter :
    SatisfiesYangBaxter exchange


/--
The routed-packet exchange is a reversible coherent
exchange system.
-/
def routedCoherentExchange
    {α : Type u} :
    CoherentExchange
      (RoutedPacket α) where

  exchange :=
    routedExchange

  involutive :=
    routedExchange_involutive

  yangBaxter :=
    routedExchange_satisfies_yang_baxter


end YangBaxterRouting


#check YangBaxterRouting.Triple
#check YangBaxterRouting.act12
#check YangBaxterRouting.act23
#check YangBaxterRouting.leftBraid
#check YangBaxterRouting.rightBraid
#check YangBaxterRouting.SatisfiesYangBaxter
#check YangBaxterRouting.crossing
#check YangBaxterRouting.crossing_involutive
#check YangBaxterRouting.crossing_satisfies_yang_baxter
#check YangBaxterRouting.mapPair
#check YangBaxterRouting.mapPair_crossing
#check YangBaxterRouting.RoutedPacket
#check YangBaxterRouting.RoutedPacket.control
#check YangBaxterRouting.RoutedPacket.observable
#check YangBaxterRouting.routedExchange
#check YangBaxterRouting.routedExchange_involutive
#check YangBaxterRouting.routedExchange_satisfies_yang_baxter
#check YangBaxterRouting.routedExchange_addresses
#check YangBaxterRouting.routedExchange_controls
#check YangBaxterRouting.observable_projection_commutes
#check YangBaxterRouting.routed_braid_paths_agree
#check YangBaxterRouting.CoherentExchange
#check YangBaxterRouting.routedCoherentExchange
