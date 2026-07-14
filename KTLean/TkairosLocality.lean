import KTLean.Tkairos
import KTLean.FanoRecovery

/-!
# Tkairos Locality

Tkairos does not act from omniscient access to the entire
Kosmoplex.

It acts on a complete state through a locality or observable
projection.

This module formalizes:

1. observational equivalence;
2. locality-compatible Tkairos evolution;
3. visible factorization of complete evolution;
4. structured hidden residue inside one observable fiber;
5. the routed Fano packet exchange as a concrete witness.

The physical interpretation of the observable type as the
complete four-dimensional world is not imposed here. This
module establishes the abstract projection architecture on
which that interpretation may later be built.
-/

universe u v

namespace TkairosLocality


/--
A projection from a complete state to the state visible
inside a locality.
-/
structure Projection
    (Complete : Type u)
    (Visible : Type v) where

  observe :
    Complete → Visible


namespace Projection


/--
Two complete states are observationally equivalent when
they produce the same visible state.
-/
def Equivalent
    {Complete : Type u}
    {Visible : Type v}
    (P : Projection Complete Visible)
    (x y : Complete) :
    Prop :=

  P.observe x =
    P.observe y


@[refl]
theorem equivalent_refl
    {Complete : Type u}
    {Visible : Type v}
    (P : Projection Complete Visible)
    (x : Complete) :

    P.Equivalent x x := by

  rfl


@[symm]
theorem equivalent_symm
    {Complete : Type u}
    {Visible : Type v}
    (P : Projection Complete Visible)
    {x y : Complete}
    (hxy : P.Equivalent x y) :

    P.Equivalent y x := by

  exact hxy.symm


@[trans]
theorem equivalent_trans
    {Complete : Type u}
    {Visible : Type v}
    (P : Projection Complete Visible)
    {x y z : Complete}
    (hxy : P.Equivalent x y)
    (hyz : P.Equivalent y z) :

    P.Equivalent x z := by

  exact hxy.trans hyz


/--
The observable fiber above a visible state.
-/
def Fiber
    {Complete : Type u}
    {Visible : Type v}
    (P : Projection Complete Visible)
    (visible : Visible) :
    Set Complete :=

  {
    complete |
      P.observe complete = visible
  }


@[simp]
theorem mem_fiber
    {Complete : Type u}
    {Visible : Type v}
    (P : Projection Complete Visible)
    (visible : Visible)
    (complete : Complete) :

    complete ∈ P.Fiber visible ↔

      P.observe complete =
        visible := by

  rfl


/--
A projection contains hidden residue when distinct complete
states occupy the same observable fiber.
-/
def HasResidue
    {Complete : Type u}
    {Visible : Type v}
    (P : Projection Complete Visible) :
    Prop :=

  ∃ x y : Complete,
    x ≠ y ∧
    P.Equivalent x y


/--
A projection has no hidden residue exactly when it is
injective.
-/
theorem not_hasResidue_iff_injective
    {Complete : Type u}
    {Visible : Type v}
    (P : Projection Complete Visible) :

    ¬ P.HasResidue ↔
      Function.Injective P.observe := by

  constructor

  · intro hno x y hxy

    by_contra hne

    apply hno

    exact
      ⟨x, y, hne, hxy⟩

  · intro hinjective hresidue

    rcases hresidue with
      ⟨x, y, hxy, hobs⟩

    exact
      hxy
        (hinjective hobs)


end Projection


/--
A complete Tkairos system equipped with a locality
projection.
-/
structure LocalSystem
    (Complete : Type u)
    (Visible : Type v) where

  tkairos :
    Tkairos.System Complete

  projection :
    Projection Complete Visible


namespace LocalSystem


/--
The complete Tkairos successor.
-/
def completeStep
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible) :
    Complete → Complete :=

  L.tkairos.step


/--
The visible observation of a complete state.
-/
def observe
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible) :
    Complete → Visible :=

  L.projection.observe


/--
A visible successor operation realizes the complete
Tkairos step when observation commutes with succession.

This is the formal meaning of complete evolution factoring
through the local visible state.
-/
def RealizesVisibleStep
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible)
    (visibleStep : Visible → Visible) :
    Prop :=

  ∀ complete : Complete,

    L.observe
        (L.completeStep complete) =

      visibleStep
        (L.observe complete)


/--
Tkairos is observationally congruent when observationally
equivalent complete states remain observationally
equivalent after one complete successor step.
-/
def ObservationCongruent
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible) :
    Prop :=

  ∀ {x y : Complete},

    L.projection.Equivalent x y →

      L.projection.Equivalent
        (L.completeStep x)
        (L.completeStep y)


/--
Every visible factorization makes complete Tkairos
observationally congruent.
-/


theorem observationCongruent_of_visibleStep
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible)
    (visibleStep : Visible → Visible)
    (hrealizes :
      L.RealizesVisibleStep visibleStep) :

    L.ObservationCongruent := by

  intro x y hxy

  have hx :
      L.projection.observe
          (L.tkairos.step x) =
        visibleStep
          (L.projection.observe x) := by

    exact hrealizes x

  have hy :
      L.projection.observe
          (L.tkairos.step y) =
        visibleStep
          (L.projection.observe y) := by

    exact hrealizes y

  change
    L.projection.observe
        (L.tkairos.step x) =
      L.projection.observe
        (L.tkairos.step y)

  calc
    L.projection.observe
        (L.tkairos.step x) =

        visibleStep
          (L.projection.observe x) := hx

    _ =
        visibleStep
          (L.projection.observe y) := by

          exact congrArg visibleStep hxy

    _ =
        L.projection.observe
          (L.tkairos.step y) := hy.symm

/--
The complete Peano-indexed Tkairos history.
-/
def completeHistory
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible)
    (initial : Complete) :
    Nat → Complete :=

  L.tkairos.history initial


/--
The visible history obtained by observing the complete
Tkairos history.
-/
def visibleHistory
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible)
    (initial : Complete) :
    Nat → Visible :=

  fun n =>
    L.observe
      (L.completeHistory initial n)


@[simp]
theorem visibleHistory_zero
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible)
    (initial : Complete) :

    L.visibleHistory initial 0 =

      L.observe initial := by

  rfl


/--
When the complete step factors through a visible step, the
visible history obeys the corresponding visible recursion.
-/
theorem visibleHistory_succ
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible)
    (visibleStep : Visible → Visible)
    (hrealizes :
      L.RealizesVisibleStep visibleStep)
    (initial : Complete)
    (n : Nat) :

    L.visibleHistory
        initial
        (Nat.succ n) =

      visibleStep
        (L.visibleHistory initial n) := by

  unfold visibleHistory
  unfold completeHistory

  rw [Tkairos.System.history_succ]

  exact
    hrealizes
      (
        L.tkairos.history
          initial
          n
      )


/--
Hidden residue is present when the locality projection is
not injective.
-/
def HasHiddenResidue
    {Complete : Type u}
    {Visible : Type v}
    (L : LocalSystem Complete Visible) :
    Prop :=

  L.projection.HasResidue


end LocalSystem


/-
## Routed Fano packet witness
-/

/--
Complete state for one routed exchange event.
-/
abbrev RoutedPair :=

  FanoRecovery.PointPacket ×
    FanoRecovery.PointPacket


/--
Visible state for one routed exchange event.

Each routed packet is projected to its visible block and
Fano-point payload.
-/
abbrev VisiblePacket :=

  CayleyDicksonQuaternion.Block ×
    Fano.Point


abbrev VisiblePair :=

  VisiblePacket ×
    VisiblePacket


/--
Observe both routed packets while omitting their Pascal
addresses.
-/
def observeRoutedPair
    (pair : RoutedPair) :
    VisiblePair :=

  YangBaxterRouting.mapPair
    YangBaxterRouting.RoutedPacket.observable
    pair


/--
The visible exchange swaps the two visible packets.
-/
def visibleExchange
    (pair : VisiblePair) :
    VisiblePair :=

  YangBaxterRouting.crossing pair


/--
The complete routed exchange as a Tkairos system.
-/
def routedTkairos :
    Tkairos.System RoutedPair where

  step :=
    YangBaxterRouting.routedExchange


/--
The routed Tkairos system together with its visible
locality projection.
-/
def routedLocalSystem :
    LocalSystem RoutedPair VisiblePair where

  tkairos :=
    routedTkairos

  projection :=
    {
      observe :=
        observeRoutedPair
    }


/--
The complete routed Tkairos step factors through visible
packet exchange.
-/
theorem routed_realizes_visibleExchange :

    routedLocalSystem.RealizesVisibleStep
      visibleExchange := by

  intro pair

  exact
    YangBaxterRouting.observable_projection_commutes
      pair


/--
Routed Tkairos evolution is observationally congruent.
-/
theorem routed_observationCongruent :

    routedLocalSystem.ObservationCongruent := by

  exact
    LocalSystem.observationCongruent_of_visibleStep
      routedLocalSystem
      visibleExchange
      routed_realizes_visibleExchange


/--
The visible routed history obeys visible packet exchange at
every successor step.
-/
theorem routed_visibleHistory_succ
    (initial : RoutedPair)
    (n : Nat) :

    routedLocalSystem.visibleHistory
        initial
        (Nat.succ n) =

      visibleExchange
        (
          routedLocalSystem.visibleHistory
            initial
            n
        ) := by

  exact
    LocalSystem.visibleHistory_succ
      routedLocalSystem
      visibleExchange
      routed_realizes_visibleExchange
      initial
      n


/--
The routed locality projection contains structured hidden
residue.

Distinct complete routed-pair states can have the same
visible projection.
-/
theorem routed_hasHiddenResidue :

    routedLocalSystem.HasHiddenResidue := by

  rcases
      FanoRecovery.structured_route_residue_exists
    with
      ⟨left, right, hne, hobservable, _⟩

  refine
    ⟨
      (left, left),
      (right, left),
      ?_,
      ?_
    ⟩

  · intro hpairs

    have hfirst :
        left = right := by

      exact congrArg Prod.fst hpairs

    exact hne hfirst

  · change
      observeRoutedPair
          (left, left) =
        observeRoutedPair
          (right, left)

    unfold observeRoutedPair
    unfold YangBaxterRouting.mapPair

    change
      (
        YangBaxterRouting.RoutedPacket.observable left,
        YangBaxterRouting.RoutedPacket.observable left
      ) =
      (
        YangBaxterRouting.RoutedPacket.observable right,
        YangBaxterRouting.RoutedPacket.observable left
      )

    rw [hobservable]

/--
The complete routed state contains more information than
its visible locality projection.
-/
theorem routed_observe_not_injective :

    ¬ Function.Injective
        routedLocalSystem.observe := by

  intro hinjective

  have hnoResidue :
      ¬ routedLocalSystem.HasHiddenResidue := by

    exact
      (
        Projection.not_hasResidue_iff_injective
          routedLocalSystem.projection
      ).2 hinjective

  exact
    hnoResidue
      routed_hasHiddenResidue


end TkairosLocality


#check TkairosLocality.Projection
#check TkairosLocality.Projection.Equivalent
#check TkairosLocality.Projection.Fiber
#check TkairosLocality.Projection.HasResidue
#check TkairosLocality.Projection.not_hasResidue_iff_injective
#check TkairosLocality.LocalSystem
#check TkairosLocality.LocalSystem.RealizesVisibleStep
#check TkairosLocality.LocalSystem.ObservationCongruent
#check TkairosLocality.LocalSystem.observationCongruent_of_visibleStep
#check TkairosLocality.LocalSystem.completeHistory
#check TkairosLocality.LocalSystem.visibleHistory
#check TkairosLocality.LocalSystem.visibleHistory_succ
#check TkairosLocality.routedTkairos
#check TkairosLocality.routedLocalSystem
#check TkairosLocality.routed_realizes_visibleExchange
#check TkairosLocality.routed_observationCongruent
#check TkairosLocality.routed_visibleHistory_succ
#check TkairosLocality.routed_hasHiddenResidue
#check TkairosLocality.routed_observe_not_injective
