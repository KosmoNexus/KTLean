import KTLean.SevenForcingParity

/-!
# Odd Cardinality of Global Triadic Closure

## Formal status

**Level 2 — Consequence of global triadic closure.**

For any selected point `x`, the full carrier decomposes into:

1. the distinguished singleton `{x}`;
2. the complement of `x`.

The complement has even cardinality by the preceding orbit-pairing
argument. Therefore the full carrier has odd cardinality.

No minimality assumption and no cardinality-seven conclusion enters
this module.
-/

namespace SevenForcingOddCardinality

noncomputable section

universe u

variable {Point : Type u}

/--
Insert either the distinguished point or one point from its complement
into the full carrier.
-/
def pointFromSingletonOrComplement
    (x : Point) :
    Unit ⊕ SevenForcingPairing.PointComplement x →
      Point
  | Sum.inl _ =>
      x
  | Sum.inr y =>
      y.1

/--
The singleton-plus-complement map is injective.
-/
theorem pointFromSingletonOrComplement_injective
    (x : Point) :
    Function.Injective
      (pointFromSingletonOrComplement x) := by

  intro left right h

  cases left with

  | inl leftUnit =>
      cases leftUnit

      cases right with

      | inl rightUnit =>
          cases rightUnit
          rfl

      | inr rightPoint =>
          exfalso
          exact rightPoint.2 h.symm

  | inr leftPoint =>
      cases right with

      | inl rightUnit =>
          cases rightUnit
          exfalso
          exact leftPoint.2 h

      | inr rightPoint =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact h

/--
The singleton-plus-complement map is surjective.
-/
theorem pointFromSingletonOrComplement_surjective
    [DecidableEq Point]
    (x : Point) :
    Function.Surjective
      (pointFromSingletonOrComplement x) := by

  intro y

  by_cases hyx : y = x

  · subst y
    exact ⟨Sum.inl (), rfl⟩

  · exact
      ⟨
        Sum.inr ⟨y, hyx⟩,
        rfl
      ⟩

/--
The full carrier is equivalent to one distinguished point plus its
complement.
-/
def singletonSumComplementEquiv
    [DecidableEq Point]
    (x : Point) :
    Unit ⊕ SevenForcingPairing.PointComplement x ≃
      Point :=

  Equiv.ofBijective
    (pointFromSingletonOrComplement x)
    ⟨
      pointFromSingletonOrComplement_injective x,
      pointFromSingletonOrComplement_surjective x
    ⟩

/--
The cardinality of the full carrier is one plus the cardinality of the
complement of any selected point.
-/
theorem card_eq_one_add_card_pointComplement
    [Fintype Point]
    [DecidableEq Point]
    (x : Point) :
    Fintype.card Point =
      1 +
        Fintype.card
          (SevenForcingPairing.PointComplement x) := by

  calc
    Fintype.card Point =
        Fintype.card
          (
            Unit ⊕
              SevenForcingPairing.PointComplement x
          ) :=
      Fintype.card_congr
        (singletonSumComplementEquiv x).symm

    _ =
      Fintype.card Unit +
        Fintype.card
          (SevenForcingPairing.PointComplement x) := by
      exact Fintype.card_sum

    _ =
      1 +
        Fintype.card
          (SevenForcingPairing.PointComplement x) := by
      change
        1 +
            Fintype.card
              (SevenForcingPairing.PointComplement x)
          =
        1 +
            Fintype.card
              (SevenForcingPairing.PointComplement x)
      rfl

/--
The full carrier of any finite global triadic-closure system has odd
cardinality.
-/
theorem odd_card
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Odd (Fintype.card Point) := by

  rcases
    SevenForcingParity.even_card_pointComplement
      S
      x
    with ⟨k, hk⟩

  refine ⟨k, ?_⟩

  calc
    Fintype.card Point =
        1 +
          Fintype.card
            (SevenForcingPairing.PointComplement x) :=
      card_eq_one_add_card_pointComplement x

    _ = 1 + (k + k) := by
      rw [hk]

    _ = k + k + 1 := by
      rw [Nat.add_comm 1 (k + k)]

    _ = 2 * k + 1 := by
      rw [two_mul]

end

end SevenForcingOddCardinality

#check SevenForcingOddCardinality.pointFromSingletonOrComplement
#check SevenForcingOddCardinality.singletonSumComplementEquiv
#check SevenForcingOddCardinality.card_eq_one_add_card_pointComplement
#check SevenForcingOddCardinality.odd_card
