import KTLean.SevenForcingFanoIdentification

/-!
# Equivalence of Every Seven-Point Nondegenerate Closure with the Fano Plane

## Formal status

**Level 2 — Consequence of global triadic closure, nondegeneracy,
exact seven-point cardinality, and the resulting noncollinear frame.**

A selected frame gives an equivalence

    CanonicalPosition ≃ Point.

The forced canonical completion table gives an equivalence

    CanonicalPosition ≃ Fano.Point.

Composing the inverse of the first equivalence with the second yields

    Point ≃ Fano.Point.

This module proves that the composite equivalence preserves the
completion operation exactly:

    e (S.complete x y)
      =
    Fano.system.complete (e x) (e y).

It then removes the selected-frame parameter existentially:
every nondegenerate seven-point global triadic-closure geometry admits
an operation-preserving equivalence with the explicit Fano plane.
-/

namespace SevenForcingFanoEquivalence

noncomputable section

universe u

open SevenForcingFanoFrame
open SevenForcingFanoFrameCanonicalInjective
open SevenForcingFanoFrameCanonicalBijection
open SevenForcingFanoFrameCanonicalTransport
open SevenForcingFanoFrameCanonicalTable
open SevenForcingFanoIdentification

variable {Point : Type u}
variable [Fintype Point]
variable [DecidableEq Point]

/--
The equivalence from the original seven-point carrier to the explicit
Fano carrier induced by a selected noncollinear frame.
-/
def pointEquivFano
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    Point ≃ Fano.Point :=

  (
    canonicalPositionEquivPoint
      frame
      hCard
  ).symm.trans
    canonicalPositionEquivFano

/--
The frame-induced equivalence first recovers the unique canonical
position of an ambient point and then applies the explicit Fano
coordinate map.
-/
@[simp]
theorem pointEquivFano_apply
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (point : Point) :
    pointEquivFano frame hCard point =
      canonicalPositionEquivFano
        (
          (
            canonicalPositionEquivPoint
              frame
              hCard
          ).symm point
        ) := by

  rfl

/--
Pulling an ambient completion back through the canonical-position
equivalence gives completion in the transported canonical system.
-/
theorem canonicalPositionEquivPoint_symm_complete
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPoint secondPoint : Point) :
    (
      canonicalPositionEquivPoint
        frame
        hCard
    ).symm
        (
          S.complete
            firstPoint
            secondPoint
        ) =
      (
        canonicalSystem
          frame
          hCard
      ).complete
        (
          (
            canonicalPositionEquivPoint
              frame
              hCard
          ).symm firstPoint
        )
        (
          (
            canonicalPositionEquivPoint
              frame
              hCard
          ).symm secondPoint
        ) := by

  let canonicalEquivalence :=
    canonicalPositionEquivPoint
      frame
      hCard

  apply canonicalEquivalence.injective

  calc
    canonicalEquivalence
        (
          canonicalEquivalence.symm
            (
              S.complete
                firstPoint
                secondPoint
            )
        ) =
        S.complete
          firstPoint
          secondPoint := by

      exact
        canonicalEquivalence.apply_symm_apply
          (
            S.complete
              firstPoint
              secondPoint
          )

    _ =
        S.complete
          (
            canonicalEquivalence
              (
                canonicalEquivalence.symm
                  firstPoint
              )
          )
          (
            canonicalEquivalence
              (
                canonicalEquivalence.symm
                  secondPoint
              )
          ) := by

      rw [
        canonicalEquivalence.apply_symm_apply,
        canonicalEquivalence.apply_symm_apply
      ]

    _ =
        canonicalEquivalence
          (
            (
              canonicalSystem
                frame
                hCard
            ).complete
              (
                canonicalEquivalence.symm
                  firstPoint
              )
              (
                canonicalEquivalence.symm
                  secondPoint
              )
          ) := by

      exact
        (
          canonicalEquiv_preserves_complete
            frame
            hCard
            (
              canonicalEquivalence.symm
                firstPoint
            )
            (
              canonicalEquivalence.symm
                secondPoint
            )
        ).symm

/--
The frame-induced equivalence from the original carrier to
`Fano.Point` preserves completion exactly.
-/
theorem pointEquivFano_preserves_complete
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7)
    (firstPoint secondPoint : Point) :
    pointEquivFano
        frame
        hCard
        (
          S.complete
            firstPoint
            secondPoint
        ) =
      Fano.system.complete
        (
          pointEquivFano
            frame
            hCard
            firstPoint
        )
        (
          pointEquivFano
            frame
            hCard
            secondPoint
        ) := by

  rw [
    pointEquivFano_apply,
    pointEquivFano_apply,
    pointEquivFano_apply,
    canonicalPositionEquivPoint_symm_complete
      frame
      hCard
      firstPoint
      secondPoint,
    canonicalSystem_eq_forcedCanonicalSystem
      frame
      hCard
  ]

  exact
    canonicalPositionEquivFano_preserves_complete
      (
        (
          canonicalPositionEquivPoint
            frame
            hCard
        ).symm firstPoint
      )
      (
        (
          canonicalPositionEquivPoint
            frame
            hCard
        ).symm secondPoint
      )

/--
A selected frame in a seven-point closure geometry determines an
operation-preserving equivalence with the explicit Fano plane.
-/
theorem frame_induces_fano_equivalence
    {S : SevenForcing.GlobalTriadicClosure Point}
    (frame : Frame S)
    (hCard : Fintype.card Point = 7) :
    ∃ equivalence : Point ≃ Fano.Point,
      ∀ firstPoint secondPoint : Point,
        equivalence
            (
              S.complete
                firstPoint
                secondPoint
            ) =
          Fano.system.complete
            (equivalence firstPoint)
            (equivalence secondPoint) := by

  refine
    ⟨
      pointEquivFano
        frame
        hCard,
      ?_
    ⟩

  intro firstPoint secondPoint

  exact
    pointEquivFano_preserves_complete
      frame
      hCard
      firstPoint
      secondPoint

/--
Every nondegenerate seven-point global triadic-closure geometry is
operation-preservingly equivalent to the explicit Fano plane.
-/
theorem seven_point_nondegenerate_is_fano
    (S : SevenForcing.GlobalTriadicClosure Point)
    (hNondegenerate : SevenForcing.Nondegenerate S)
    (hCard : Fintype.card Point = 7) :
    ∃ equivalence : Point ≃ Fano.Point,
      ∀ firstPoint secondPoint : Point,
        equivalence
            (
              S.complete
                firstPoint
                secondPoint
            ) =
          Fano.system.complete
            (equivalence firstPoint)
            (equivalence secondPoint) := by

  obtain ⟨frame⟩ :=
    SevenForcingFanoFrame.exists_frame
      S
      hNondegenerate

  exact
    frame_induces_fano_equivalence
      frame
      hCard

end

end SevenForcingFanoEquivalence

#check SevenForcingFanoEquivalence.pointEquivFano
#check SevenForcingFanoEquivalence.pointEquivFano_apply
#check SevenForcingFanoEquivalence.canonicalPositionEquivPoint_symm_complete
#check SevenForcingFanoEquivalence.pointEquivFano_preserves_complete
#check SevenForcingFanoEquivalence.frame_induces_fano_equivalence
#check SevenForcingFanoEquivalence.seven_point_nondegenerate_is_fano
