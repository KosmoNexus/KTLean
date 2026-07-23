import KTLean.SevenForcingDivisibility
import KTLean.SevenForcingOddCardinality
import Mathlib.Data.Nat.Prime.Defs

/-!
# Modulo-Six Congruence of Global Triadic Closure

## Formal status

**Level 2 — Consequence of global triadic closure.**

For a finite global triadic-closure system with a selected point:

1. the point carrier has odd cardinality;
2. six divides `v * (v - 1)`.

The second fact implies that three divides either `v` or `v - 1`.
Combining this ternary alternative with oddness yields

    v % 6 = 1  or  v % 6 = 3.

Equivalently, every finite nonempty global triadic-closure carrier has
cardinality congruent to `1` or `3` modulo six.

No minimality assumption and no cardinality-seven conclusion enters
this module.
-/

namespace SevenForcingCongruence

noncomputable section

universe u

variable {Point : Type u}

open SevenForcingDivisibility
open SevenForcingOddCardinality

/--
Three divides either the point cardinality or its predecessor.
-/
theorem three_dvd_card_or_card_sub_one
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point) :
    3 ∣ Fintype.card Point ∨
      3 ∣ (Fintype.card Point - 1) := by

  have hsix :
      6 ∣
        Fintype.card Point *
          (Fintype.card Point - 1) :=
    six_dvd_card_mul_card_sub_one S

  have hthreeSix :
      3 ∣ 6 := by
    exact ⟨2, rfl⟩

  have hthreeProduct :
      3 ∣
        Fintype.card Point *
          (Fintype.card Point - 1) :=
    dvd_trans hthreeSix hsix

  exact
    Nat.Prime.dvd_or_dvd Nat.prime_three
      hthreeProduct

/--
The point cardinality is congruent to one or three modulo six.
-/
theorem card_mod_six_eq_one_or_three
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Fintype.card Point % 6 = 1 ∨
      Fintype.card Point % 6 = 3 := by

  rcases odd_card S x with
    ⟨k, hodd⟩

  rcases
    three_dvd_card_or_card_sub_one S
    with hthree | hthree

  · rcases hthree with
      ⟨m, hthree⟩

    right
    omega

  · rcases hthree with
      ⟨m, hthree⟩

    left
    omega

/--
The standard Steiner-system admissibility condition, expressed using
`Nat.ModEq`.
-/
theorem card_modEq_one_or_three
    [Fintype Point]
    [DecidableEq Point]
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Nat.ModEq 6 (Fintype.card Point) 1 ∨
      Nat.ModEq 6 (Fintype.card Point) 3 := by

  rcases
    card_mod_six_eq_one_or_three
      S
      x
    with hone | hthree

  · left
    exact hone

  · right
    exact hthree

end

end SevenForcingCongruence

#check SevenForcingCongruence.three_dvd_card_or_card_sub_one
#check SevenForcingCongruence.card_mod_six_eq_one_or_three
#check SevenForcingCongruence.card_modEq_one_or_three
