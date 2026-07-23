import KTLean.SevenForcingPairOrbitGlobalCardinality
import KTLean.SevenForcingDistinctPairCardinality

/-!
# Six-Divisibility of the Point-Cardinality Product

## Formal status

**Level 2 — Consequence of global triadic closure.**

The carrier of distinct ordered pairs has cardinality

    v * (v - 1),

where `v` is the cardinality of the point carrier.

The rotation–reversal quotient partitions that carrier into classes of
six elements. Therefore

    6 ∣ v * (v - 1).

No minimality assumption and no cardinality-seven conclusion enters
this module.
-/

namespace SevenForcingDivisibility

noncomputable section

universe u

variable {Point : Type u}

open SevenForcingDistinctPairs
open SevenForcingDistinctPairCardinality
open SevenForcingPairOrbitGlobalCardinality

/--
For a finite global triadic-closure system, six divides the product of
the point cardinality and its predecessor.
-/
theorem six_dvd_card_mul_card_sub_one
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point) :
    6 ∣
      Fintype.card Point *
        (Fintype.card Point - 1) := by

  have hdiv :
      6 ∣ Nat.card (DistinctPair (Point := Point)) :=
    six_dvd_natCard_distinctPair S

  have hnatCard :
      Nat.card (DistinctPair (Point := Point)) =
        Fintype.card (DistinctPair (Point := Point)) := by
    exact Nat.card_eq_fintype_card

  rw [hnatCard] at hdiv

  rw [card_distinctPair] at hdiv

  exact hdiv

/--
Equivalent divisibility statement written with an abbreviated point
cardinality.
-/
theorem six_dvd_pointCard_product
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point) :
    let v := Fintype.card Point
    6 ∣ v * (v - 1) := by

  exact
    six_dvd_card_mul_card_sub_one
      S

end

end SevenForcingDivisibility

#check SevenForcingDivisibility.six_dvd_card_mul_card_sub_one
#check SevenForcingDivisibility.six_dvd_pointCard_product
