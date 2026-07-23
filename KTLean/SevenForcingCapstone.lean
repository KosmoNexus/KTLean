import KTLean.SevenForcingFanoWitness
import KTLean.SevenForcingCongruence

/-!
# Seven Forcing Capstone

## Formal status

This module packages the completed seven-forcing chain into a compact
public interface.

The development proves:

1. every finite nondegenerate global triadic-closure system has at
   least seven points;
2. every finite global triadic-closure carrier has cardinality
   congruent to `1` or `3` modulo six;
3. the Fano plane supplies an explicit nondegenerate seven-point
   witness;
4. every cardinal-minimal finite nondegenerate global triadic-closure
   system therefore has exactly seven points.

Thus seven is not assumed as part of global triadic closure. It is
forced as the least nondegenerate finite cardinality.

This module does not yet prove that every seven-point system is
isomorphic to the explicit Fano system. That structural uniqueness
result belongs to the subsequent Fano-identification chain.
-/

namespace SevenForcingCapstone

noncomputable section

universe u

/--
Every finite nondegenerate global triadic-closure carrier has at least
seven points.
-/
theorem nondegenerate_seven_lower_bound
    {Point : Type u}
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (hNondegenerate : SevenForcing.Nondegenerate S)
    (x : Point) :
    7 ≤ Fintype.card Point := by

  exact
    SevenForcingLowerBound.seven_le_card
      S
      hNondegenerate
      x

/--
Every finite nonempty global triadic-closure carrier has cardinality
congruent to one or three modulo six.
-/
theorem steiner_admissibility
    {Point : Type u}
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Fintype.card Point % 6 = 1 ∨
      Fintype.card Point % 6 = 3 := by

  exact
    SevenForcingCongruence.card_mod_six_eq_one_or_three
      S
      x

/--
The explicit Fano system is a nondegenerate global triadic-closure
system on exactly seven points.
-/
theorem fano_witness :
    SevenForcing.Nondegenerate
        SevenForcingFanoWitness.fanoGlobalTriadicClosure
      ∧
    Fintype.card Fano.Point = 7 := by

  exact
    ⟨
      SevenForcingFanoWitness.fano_nondegenerate,
      SevenForcingFanoWitness.fano_card_eq_seven
    ⟩

/--
Seven is the least cardinality realized by a finite nondegenerate global
triadic-closure system.
-/
theorem seven_is_least_nondegenerate_cardinality :
    (
      ∀
        {Point : Type u}
        [Fintype Point]
        [DecidableEq Point]
        (S : SevenForcing.GlobalTriadicClosure Point),
        SevenForcing.Nondegenerate S →
          7 ≤ Fintype.card Point
    )
    ∧
    (
      SevenForcing.Nondegenerate
          SevenForcingFanoWitness.fanoGlobalTriadicClosure
        ∧
      Fintype.card Fano.Point = 7
    ) := by

  constructor

  · intro Point instFintype instDecidableEq S hNondegenerate

    letI : Fintype Point :=
      instFintype

    letI : DecidableEq Point :=
      instDecidableEq

    rcases
      SevenForcing.exists_external_point
        hNondegenerate
      with ⟨x, y, p, hxy, hp⟩

    exact
      nondegenerate_seven_lower_bound
        S
        hNondegenerate
        x

  · exact fano_witness

/--
Every cardinal-minimal finite nondegenerate global triadic-closure
system has exactly seven points.
-/
theorem cardinal_minimal_nondegenerate_card_eq_seven
    {Point : Type}
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (hMinimal :
      SevenForcingMinimality.CardinalityMinimalNondegenerate S)
    (x : Point) :
    Fintype.card Point = 7 := by

  exact
    SevenForcingFanoWitness.card_eq_seven_of_cardinality_minimal
      S
      hMinimal
      x

end

end SevenForcingCapstone

#check SevenForcingCapstone.nondegenerate_seven_lower_bound
#check SevenForcingCapstone.steiner_admissibility
#check SevenForcingCapstone.fano_witness
#check SevenForcingCapstone.seven_is_least_nondegenerate_cardinality
#check SevenForcingCapstone.cardinal_minimal_nondegenerate_card_eq_seven
