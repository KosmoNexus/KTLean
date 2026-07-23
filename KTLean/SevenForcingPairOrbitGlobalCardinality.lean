import KTLean.SevenForcingPairOrbitFiberUniform

/-!
# Global Cardinality of Pair-Orbit Classes

## Formal status

**Level 2 — Consequence of global triadic closure.**

The distinct ordered-pair carrier decomposes as the dependent sum of
the fibers of the rotation–reversal quotient. Every such fiber has
natural cardinality six.

Therefore

    Nat.card DistinctPair
      =
    6 * Nat.card PairOrbitQuotient.

In particular, the natural cardinality of the distinct ordered-pair
carrier is divisible by six.

No minimality assumption and no cardinality-seven conclusion enters
this module.
-/

namespace SevenForcingPairOrbitGlobalCardinality

noncomputable section

universe u

variable {Point : Type u}

open SevenForcingDistinctPairs
open SevenForcingPairOrbitQuotient
open SevenForcingPairOrbitFiberUniform

/--
The global distinct-pair carrier has cardinality six times the number
of rotation–reversal quotient classes.
-/
theorem natCard_distinctPair_eq_six_mul_quotient
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point) :
    Nat.card (DistinctPair (Point := Point)) =
      6 * Nat.card (PairOrbitQuotient S) := by

  letI : Finite (PairOrbitQuotient S) :=
    Finite.of_surjective
      (pairOrbitClass S)
      (pairOrbitClass_surjective S)

  letI
      (orbitClass : PairOrbitQuotient S) :
      Finite (PairOrbitFiber S orbitClass) :=
    Finite.of_injective
      Subtype.val
      Subtype.val_injective

  letI : Fintype (PairOrbitQuotient S) :=
    Fintype.ofFinite (PairOrbitQuotient S)

  calc
    Nat.card (DistinctPair (Point := Point)) =
        Nat.card
          (
            Σ orbitClass : PairOrbitQuotient S,
              PairOrbitFiber S orbitClass
          ) := by
      exact
        Nat.card_congr
          (
            distinctPairEquivSigmaFiber
              S
          )

    _ =
        ∑ orbitClass : PairOrbitQuotient S,
          Nat.card
            (
              PairOrbitFiber
                S
                orbitClass
            ) := by
      exact Nat.card_sigma

    _ =
        ∑ _orbitClass : PairOrbitQuotient S,
          6 := by
      apply Finset.sum_congr rfl

      intro orbitClass horbitClass

      exact
        natCard_pairOrbitFiber_all
          S
          orbitClass

    _ =
        Nat.card (PairOrbitQuotient S) * 6 := by
      simp

    _ =
        6 * Nat.card (PairOrbitQuotient S) := by
      exact
        Nat.mul_comm
          (Nat.card (PairOrbitQuotient S))
          6

/--
The natural cardinality of the distinct ordered-pair carrier is
divisible by six.
-/
theorem six_dvd_natCard_distinctPair
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point) :
    6 ∣ Nat.card (DistinctPair (Point := Point)) := by

  rw [
    natCard_distinctPair_eq_six_mul_quotient
      S
  ]

  exact
    ⟨
      Nat.card (PairOrbitQuotient S),
      rfl
    ⟩

end

end SevenForcingPairOrbitGlobalCardinality

#check SevenForcingPairOrbitGlobalCardinality.natCard_distinctPair_eq_six_mul_quotient
#check SevenForcingPairOrbitGlobalCardinality.six_dvd_natCard_distinctPair
