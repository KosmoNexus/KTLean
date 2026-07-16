import KTLean.MonadOrbit

/-!
# Monad trivializations

A trivialization is a reversible coordinate description of the complete
monad space.

Choosing a trivialization is permitted for calculation. Physical scalar
content may not depend on which lawfully frame-related trivialization was
chosen.

This module distinguishes:

1. a coordinate choice;
2. transport of that coordinate choice by a lawful substrate frame;
3. invariant physical content, which is unchanged by such transport.
-/

namespace KTLean

universe u v

namespace MonadTrivialization

variable
  {Frame : Type u}
  [Group Frame]

variable
  (A : MonadAction.FrameAction Frame)

/--
A reversible coordinate presentation of the complete monad space.

No claim is made that the coordinate type itself is physical.
-/
structure Trivialization
    (Coordinates : Type v) where

  toCoordinates :
    KTMonad.Monad →
      Coordinates

  fromCoordinates :
    Coordinates →
      KTMonad.Monad

  from_to :
    ∀ monad : KTMonad.Monad,
      fromCoordinates
          (toCoordinates monad) =
        monad

  to_from :
    ∀ coordinates : Coordinates,
      toCoordinates
          (fromCoordinates coordinates) =
        coordinates

namespace Trivialization

variable
  {Coordinates : Type v}

variable
  (T : Trivialization Coordinates)

/--
A trivialization determines an equivalence between complete monads and
its coordinate type.
-/
def equiv :
    KTMonad.Monad ≃ Coordinates where

  toFun :=
    T.toCoordinates

  invFun :=
    T.fromCoordinates

  left_inv :=
    T.from_to

  right_inv :=
    T.to_from

/--
Transport a trivialization by a lawful substrate-frame transformation.

Coordinates in the transported frame are obtained by first carrying the
monad back to the original frame.
-/
def transport
    (frame : Frame) :
    Trivialization Coordinates where

  toCoordinates :=
    fun monad =>
      T.toCoordinates
        (A.act frame⁻¹ monad)

  fromCoordinates :=
    fun coordinates =>
      A.act frame
        (T.fromCoordinates coordinates)

  from_to := by
    intro monad

    calc
      A.act frame
          (T.fromCoordinates
            (T.toCoordinates
              (A.act frame⁻¹ monad))) =
        A.act frame
          (A.act frame⁻¹ monad) := by
            rw [T.from_to]

      _ = monad := by
            calc
              A.act frame
                  (A.act frame⁻¹ monad) =
                A.act
                  (frame * frame⁻¹)
                  monad := by
                    exact
                      (A.mul_act
                        frame
                        frame⁻¹
                        monad).symm

              _ = A.act 1 monad := by
                    simp

              _ = monad := by
                    exact A.one_act monad

  to_from := by
    intro coordinates

    calc
      T.toCoordinates
          (A.act frame⁻¹
            (A.act frame
              (T.fromCoordinates coordinates))) =
        T.toCoordinates
          (T.fromCoordinates coordinates) := by
            rw [
              A.inverse_recovers
                frame
                (T.fromCoordinates coordinates)
            ]

      _ = coordinates := by
            exact T.to_from coordinates

/--
The identity frame leaves a trivialization unchanged at the level of
coordinate maps.
-/
theorem transport_one_toCoordinates
    (monad : KTMonad.Monad) :

    (T.transport A 1).toCoordinates monad =
      T.toCoordinates monad := by

  simp [transport]

/--
The identity frame leaves reconstruction unchanged.
-/
theorem transport_one_fromCoordinates
    (coordinates : Coordinates) :

    (T.transport A 1).fromCoordinates coordinates =
      T.fromCoordinates coordinates := by

  simp [transport]

/--
Successive transport of a trivialization agrees with transport by the
product frame.

The order follows the left action convention already established in
`MonadAction`.
-/
theorem transport_transport_toCoordinates
    (left right : Frame)
    (monad : KTMonad.Monad) :

    ((T.transport A right).transport A left).toCoordinates monad =
      (T.transport A (left * right)).toCoordinates monad := by

  change
    T.toCoordinates
        (A.act right⁻¹
          (A.act left⁻¹ monad)) =
      T.toCoordinates
        (A.act (left * right)⁻¹ monad)

  apply congrArg T.toCoordinates

  calc
    A.act right⁻¹
        (A.act left⁻¹ monad) =
      A.act
        (right⁻¹ * left⁻¹)
        monad := by
          exact
            (A.mul_act
              right⁻¹
              left⁻¹
              monad).symm

    _ =
      A.act
        (left * right)⁻¹
        monad := by
          simp

/--
Successive reconstruction through transported trivializations agrees
with reconstruction under the product frame.
-/
theorem transport_transport_fromCoordinates
    (left right : Frame)
    (coordinates : Coordinates) :

    ((T.transport A right).transport A left).fromCoordinates coordinates =
      (T.transport A (left * right)).fromCoordinates coordinates := by

  simp [transport]



/-!
## Coordinate representations of observables
-/

/--
Represent a monad observable in a chosen coordinate system.
-/
def coordinateObservable
    {Value : Type v}
    (observable :
      KTMonad.Monad → Value) :
    Coordinates → Value :=

  fun coordinates =>
    observable
      (T.fromCoordinates coordinates)

/--
An invariant observable has the same value when expressed in any
lawfully transported trivialization, provided the coordinate labels are
kept fixed.
-/
theorem invariant_coordinateObservable_transport
    {Value : Type v}
    (observable :
      KTMonad.Monad → Value)
    (hinvariant :
      MonadInvariant.InvariantObservable
        A
        observable)
    (frame : Frame)
    (coordinates : Coordinates) :

    (T.transport A frame).coordinateObservable observable coordinates =
      T.coordinateObservable observable coordinates := by

  change
    observable
        (A.act frame
          (T.fromCoordinates coordinates)) =
      observable
        (T.fromCoordinates coordinates)

  exact
    hinvariant
      frame
      (T.fromCoordinates coordinates)

/--
A physically admissible scalar observable is independent of every
lawfully frame-related trivialization.
-/
theorem physicallyAdmissible_independent_of_transport
    {Value : Type v}
    (observable :
      KTMonad.Monad → Value)
    (hadmissible :
      MonadInvariant.PhysicallyAdmissible
        A
        observable)
    (frame : Frame)
    (coordinates : Coordinates) :

    (T.transport A frame).coordinateObservable observable coordinates =
      T.coordinateObservable observable coordinates := by

  exact
    invariant_coordinateObservable_transport
      A
      T
      observable
      hadmissible
      frame
      coordinates

/-!
## Coordinate predicates
-/

/--
Represent a predicate on monads in a chosen coordinate system.
-/
def coordinatePredicate
    (P :
      KTMonad.Monad → Prop) :
    Coordinates → Prop :=

  fun coordinates =>
    P
      (T.fromCoordinates coordinates)

/--
An invariant predicate has the same truth value in every lawfully
transported trivialization.
-/
theorem invariant_coordinatePredicate_transport
    (P :
      KTMonad.Monad → Prop)
    (hinvariant :
      MonadInvariant.InvariantPredicate
        A
        P)
    (frame : Frame)
    (coordinates : Coordinates) :

    (T.transport A frame).coordinatePredicate P coordinates ↔
      T.coordinatePredicate P coordinates := by

  change
    P
        (A.act frame
          (T.fromCoordinates coordinates))
      ↔
    P
        (T.fromCoordinates coordinates)

  exact
    (hinvariant
      frame
      (T.fromCoordinates coordinates)).symm

end Trivialization

end MonadTrivialization

end KTLean
