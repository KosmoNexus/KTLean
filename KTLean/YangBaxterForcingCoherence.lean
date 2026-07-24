import KTLean.PascalForcingCapstone
import KTLean.YangBaxterRouting

/-!
# Three-Channel Exchange Coherence

## Formal status

**Level 1 — Abstract coherence requirement and identification with the
existing Yang–Baxter interface.**

Suppose a local binary exchange operator acts on adjacent members of a
three-object state.

There are two minimal sequences that exchange the exterior objects:

    exchange 12
    exchange 23
    exchange 12

and

    exchange 23
    exchange 12
    exchange 23.

Before naming any algebraic structure, global path independence
requires these two admissible local histories to produce the same
final triple.

This module defines that operational coherence condition and proves
that it is exactly the existing `SatisfiesYangBaxter` proposition.

Thus the Yang–Baxter relation is not introduced here as an ornamental
equation. It is the formal name for equality of the two minimal
overlapping exchange paths.
-/

namespace YangBaxterForcingCoherence

universe u

open YangBaxterRouting

/--
The first admissible three-exchange history:

    exchange 12
    exchange 23
    exchange 12.
-/
def firstExchangeHistory
    {α : Type u}
    (exchange : α × α → α × α)
    (triple : Triple α) :
    Triple α :=

  act12 exchange
    (
      act23 exchange
        (
          act12 exchange triple
        )
    )

/--
The second admissible three-exchange history:

    exchange 23
    exchange 12
    exchange 23.
-/
def secondExchangeHistory
    {α : Type u}
    (exchange : α × α → α × α)
    (triple : Triple α) :
    Triple α :=

  act23 exchange
    (
      act12 exchange
        (
          act23 exchange triple
        )
    )

/--
A local exchange is three-channel coherent when the two minimal
overlapping exchange histories agree on every input triple.
-/
def ThreeChannelCoherent
    {α : Type u}
    (exchange : α × α → α × α) :
    Prop :=

  ∀ triple : Triple α,
    firstExchangeHistory exchange triple =
      secondExchangeHistory exchange triple

/--
The first operational exchange history is exactly the existing left
braid path.
-/
theorem firstExchangeHistory_eq_leftBraid
    {α : Type u}
    (exchange : α × α → α × α)
    (triple : Triple α) :
    firstExchangeHistory exchange triple =
      leftBraid exchange triple := by

  rfl

/--
The second operational exchange history is exactly the existing right
braid path.
-/
theorem secondExchangeHistory_eq_rightBraid
    {α : Type u}
    (exchange : α × α → α × α)
    (triple : Triple α) :
    secondExchangeHistory exchange triple =
      rightBraid exchange triple := by

  rfl

/--
Three-channel path independence is equivalent to the existing
Yang–Baxter relation.
-/
theorem threeChannelCoherent_iff_yangBaxter
    {α : Type u}
    (exchange : α × α → α × α) :
    ThreeChannelCoherent exchange ↔
      SatisfiesYangBaxter exchange := by

  rfl

/--
Operational coherence forces the Yang–Baxter equation.

No Yang–Baxter hypothesis is assumed: the hypothesis is stated only as
equality of the two admissible local exchange histories.
-/
theorem coherence_forces_yangBaxter
    {α : Type u}
    {exchange : α × α → α × α}
    (hCoherent : ThreeChannelCoherent exchange) :
    SatisfiesYangBaxter exchange := by

  exact
    (
      threeChannelCoherent_iff_yangBaxter
        exchange
    ).1
      hCoherent

/--
Conversely, a Yang–Baxter exchange is operationally path independent
on three neighboring channels.
-/
theorem yangBaxter_gives_coherence
    {α : Type u}
    {exchange : α × α → α × α}
    (hYangBaxter : SatisfiesYangBaxter exchange) :
    ThreeChannelCoherent exchange := by

  exact
    (
      threeChannelCoherent_iff_yangBaxter
        exchange
    ).2
      hYangBaxter

/--
Plain crossing is three-channel coherent on every carrier.
-/
theorem crossing_threeChannelCoherent
    {α : Type u} :
    ThreeChannelCoherent
      (@crossing α) := by

  exact
    yangBaxter_gives_coherence
      crossing_satisfies_yang_baxter

/--
The existing routed packet exchange is three-channel coherent.

This witness carries Pascal addresses, derived Pascal controls,
Cayley–Dickson block labels, and payloads together through each local
exchange.
-/
theorem routedExchange_threeChannelCoherent
    {α : Type u} :
    ThreeChannelCoherent
      (@routedExchange α) := by

  exact
    yangBaxter_gives_coherence
      routedExchange_satisfies_yang_baxter

/--
For ordinary crossing, both coherent histories reverse the exterior
objects and preserve the middle object.
-/
theorem coherent_crossing_outcome
    {α : Type u}
    (first second third : α) :
    firstExchangeHistory
        (@crossing α)
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
        (@crossing α)
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

/--
The two routed exchange histories agree directly on every routed
packet triple.
-/
theorem routed_histories_agree
    {α : Type u}
    (triple : Triple (RoutedPacket α)) :
    firstExchangeHistory
        (@routedExchange α)
        triple =
      secondExchangeHistory
        (@routedExchange α)
        triple := by

  exact
    routedExchange_threeChannelCoherent
      triple

end YangBaxterForcingCoherence

#check YangBaxterForcingCoherence.firstExchangeHistory
#check YangBaxterForcingCoherence.secondExchangeHistory
#check YangBaxterForcingCoherence.ThreeChannelCoherent
#check YangBaxterForcingCoherence.threeChannelCoherent_iff_yangBaxter
#check YangBaxterForcingCoherence.coherence_forces_yangBaxter
#check YangBaxterForcingCoherence.yangBaxter_gives_coherence
#check YangBaxterForcingCoherence.crossing_threeChannelCoherent
#check YangBaxterForcingCoherence.routedExchange_threeChannelCoherent
#check YangBaxterForcingCoherence.coherent_crossing_outcome
#check YangBaxterForcingCoherence.routed_histories_agree
