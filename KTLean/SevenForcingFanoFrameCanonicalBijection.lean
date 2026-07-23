import KTLean.SevenForcingFanoFrameCanonicalInjective
import Mathlib.Data.Fintype.EquivFin

/-!
# Bijection from Canonical Fano-Frame Positions

## Formal status

**Level 2 — Consequence of global triadic closure, a selected
noncollinear frame, and exact seven-point cardinality.**

Every noncollinear frame generates seven pairwise distinct canonical
points.

When the ambient point carrier itself has exactly seven elements, the
injective map from the seven canonical positions into the carrier is
therefore bijective.

Thus every point of a seven-point global triadic-closure system is
uniquely one of the canonical frame expressions.

This module proves exhaustion of the carrier. It does not yet prove
that completion transported through this bijection agrees with the
explicit Fano completion table.
-/

namespace SevenForcingFanoFrameCanonicalBijection

noncomputable section

universe u

variable {Point : Type u}
variable [DecidableEq Point]

open SevenForcingFanoFrame
open SevenForcingFanoFrameCanonicalInjective

/--
Explicit finite enumeration of the seven canonical frame positions.
-/
instance canonicalPositionFintype :
    Fintype CanonicalPosition where

  elems :=
    {
      CanonicalPosition.first,
      CanonicalPosition.second,
      CanonicalPosition.lineThird,
      CanonicalPosition.external,
      CanonicalPosition.firstExternalThird,
      CanonicalPosition.secondExternalThird,
      CanonicalPosition.lineThirdExternalThird
    }

  complete := by
    intro position
    cases position <;> simp

/--
The canonical-position carrier has exactly seven elements.
-/
theorem card_canonicalPosition :
    Fintype.card CanonicalPosition =
      7 := by

  decide

/--
For a seven-point ambient carrier, the canonical frame map is
bijective.
-/
theorem pointAt_bijective_of_card_eq_seven
    [Fintype Point]
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard :
      Fintype.card Point = 7) :
    Function.Bijective
      (pointAt frame) := by

  rw [Fintype.bijective_iff_injective_and_card]

  exact
    ⟨
      pointAt_injective frame,
      by
        rw [
          card_canonicalPosition,
          hCard
        ]
    ⟩

/--
For a seven-point ambient carrier, every point is represented by a
canonical frame position.
-/
theorem pointAt_surjective_of_card_eq_seven
    [Fintype Point]
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard :
      Fintype.card Point = 7) :
    Function.Surjective
      (pointAt frame) := by

  exact
    (
      pointAt_bijective_of_card_eq_seven
        frame
        hCard
    ).2

/--
The seven canonical positions are equivalent to the ambient point
carrier whenever that carrier has cardinality seven.
-/
def canonicalPositionEquivPoint
    [Fintype Point]
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard :
      Fintype.card Point = 7) :
    CanonicalPosition ≃
      Point :=

  Equiv.ofBijective
    (pointAt frame)
    (
      pointAt_bijective_of_card_eq_seven
        frame
        hCard
    )

/--
The forward map of the canonical equivalence is exactly `pointAt`.
-/
@[simp]
theorem canonicalPositionEquivPoint_apply
    [Fintype Point]
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard :
      Fintype.card Point = 7)
    (position : CanonicalPosition) :
    canonicalPositionEquivPoint frame hCard position =
      pointAt frame position := by

  rfl

/--
Every point of a seven-point system has a unique canonical frame
position.
-/
theorem existsUnique_canonicalPosition
    [Fintype Point]
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard :
      Fintype.card Point = 7)
    (point : Point) :
    ∃! position : CanonicalPosition,
      pointAt frame position =
        point := by

  obtain ⟨position, hposition⟩ :=
    (
      pointAt_surjective_of_card_eq_seven
        frame
        hCard
    )
      point

  refine
    ⟨
      position,
      hposition,
      ?_
    ⟩

  intro otherPosition hotherPosition

  exact
    pointAt_injective
      frame
      (
        hotherPosition.trans
          hposition.symm
      )

/--
The image of the seven canonical positions is the entire ambient
carrier.
-/
theorem canonical_points_exhaust
    [Fintype Point]
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard :
      Fintype.card Point = 7)
    (point : Point) :
    ∃ position : CanonicalPosition,
      pointAt frame position =
        point := by

  exact
    (
      pointAt_surjective_of_card_eq_seven
        frame
        hCard
    )
      point

end

end SevenForcingFanoFrameCanonicalBijection

#check SevenForcingFanoFrameCanonicalBijection.card_canonicalPosition
#check SevenForcingFanoFrameCanonicalBijection.pointAt_bijective_of_card_eq_seven
#check SevenForcingFanoFrameCanonicalBijection.pointAt_surjective_of_card_eq_seven
#check SevenForcingFanoFrameCanonicalBijection.canonicalPositionEquivPoint
#check SevenForcingFanoFrameCanonicalBijection.existsUnique_canonicalPosition
#check SevenForcingFanoFrameCanonicalBijection.canonical_points_exhaust
