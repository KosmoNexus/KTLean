import KTLean.SevenForcingPairOrbitCardinality

/-!
# Cardinality of the Distinct Ordered-Pair Carrier

## Formal status

**Level 2 — Consequence of finiteness and distinctness.**

A distinct ordered pair consists of:

1. a selected left endpoint `x`;
2. a right endpoint chosen from the complement of `x`.

Thus the carrier of distinct ordered pairs is equivalent to the
dependent sum

    Σ x : Point, PointComplement x.

Every complement has cardinality `v - 1`, where `v` is the cardinality
of the point carrier. Therefore

    card DistinctPair = v * (v - 1).

No orbit counting, minimality assumption, or cardinality-seven
conclusion enters this module.
-/

namespace SevenForcingDistinctPairCardinality

noncomputable section

universe u

variable {Point : Type u}

open SevenForcingDistinctPairs
open SevenForcingPairing
open SevenForcingOddCardinality

/--
Convert a distinct ordered pair into a left endpoint together with a
right endpoint in its complement.
-/
def distinctPairToSigmaComplement
    (pair : DistinctPair (Point := Point)) :
    Σ x : Point, PointComplement x :=
  ⟨
    pair.left,
    ⟨pair.right, Ne.symm pair.2⟩
  ⟩

/--
Convert a left endpoint and one point in its complement into a distinct
ordered pair.
-/
def sigmaComplementToDistinctPair :
    (Σ x : Point, PointComplement x) →
      DistinctPair (Point := Point)

  | ⟨x, y⟩ =>
      ⟨
        (x, y.1),
        Ne.symm y.2
      ⟩

/--
Distinct ordered pairs are equivalent to the dependent sum of all
point complements.
-/
def distinctPairEquivSigmaComplement :
    DistinctPair (Point := Point) ≃
      Σ x : Point, PointComplement x where

  toFun :=
    distinctPairToSigmaComplement

  invFun :=
    sigmaComplementToDistinctPair

  left_inv := by
    intro pair

    cases pair with
    | mk value hvalue =>
        cases value
        rfl

  right_inv := by
    intro pair

    rcases pair with ⟨x, y, hy⟩

    rfl

/--
The complement of any selected point has cardinality one less than the
full point carrier.
-/
theorem card_pointComplement_eq_card_sub_one
    [Fintype Point]
    [DecidableEq Point]
    (x : Point) :
    Fintype.card (PointComplement x) =
      Fintype.card Point - 1 := by

  have hcard :
      Fintype.card Point =
        1 + Fintype.card (PointComplement x) :=
    card_eq_one_add_card_pointComplement x

  rw [hcard]

  simp

/--
The carrier of distinct ordered pairs has cardinality

    v * (v - 1),

where `v` is the cardinality of the point carrier.
-/
theorem card_distinctPair
    [Fintype Point]
    [DecidableEq Point] :
    Fintype.card (DistinctPair (Point := Point)) =
      Fintype.card Point *
        (Fintype.card Point - 1) := by

  calc
    Fintype.card (DistinctPair (Point := Point)) =
        Fintype.card
          (Σ x : Point, PointComplement x) := by
      exact
        Fintype.card_congr
          distinctPairEquivSigmaComplement

    _ =
        ∑ x : Point,
          Fintype.card (PointComplement x) := by
      exact Fintype.card_sigma

    _ =
        ∑ _x : Point,
          (Fintype.card Point - 1) := by
      apply Finset.sum_congr rfl

      intro x hx

      exact
        card_pointComplement_eq_card_sub_one x

    _ =
        Fintype.card Point *
          (Fintype.card Point - 1) := by
      simp

end

end SevenForcingDistinctPairCardinality

#check SevenForcingDistinctPairCardinality.distinctPairToSigmaComplement
#check SevenForcingDistinctPairCardinality.sigmaComplementToDistinctPair
#check SevenForcingDistinctPairCardinality.distinctPairEquivSigmaComplement
#check SevenForcingDistinctPairCardinality.card_pointComplement_eq_card_sub_one
#check SevenForcingDistinctPairCardinality.card_distinctPair
