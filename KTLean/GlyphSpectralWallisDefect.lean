import KTLean.GlyphSpectralWallisKernel
import Mathlib.Tactic

/-!
# The Triadic Defect of the Wallis Stream

## Formal status

**Level 2 — Exact finite arithmetic structure of the Wallis factors.**

At stage `n`, let

    m = n + 1.

The Wallis readout triad is then

    2m - 1, 2m, 2m + 1.

The central square differs from the product of its two neighbors by
exactly one:

    (2m)^2 - (2m - 1)(2m + 1) = 1.

Consequently,

    Wₙ = (2m)^2 / ((2m - 1)(2m + 1))
       = 1 + 1 / (4m² - 1).

Thus every Wallis factor is greater than one, with an exact positive
defect that decreases as the central triadic scale grows.

No infinite-product convergence theorem is asserted here.
-/

namespace GlyphSpectralWallisDefect

open GlyphSpectralWallisKernel

/--
The positive central scale at stage `n`.
-/
def centralScale
    (n : Nat) :
    Nat :=
  n + 1

/--
The three Wallis readouts are the lower neighbor, double center, and
upper neighbor of the central scale.
-/
theorem readouts_from_centralScale
    (n : Nat) :
    lowerReadout n =
        2 * centralScale n - 1
      ∧
    centralReadout n =
        2 * centralScale n
      ∧
    upperReadout n =
        2 * centralScale n + 1 := by

  unfold centralScale
  unfold lowerReadout
  unfold centralReadout
  unfold upperReadout

  omega

/--
The central square exceeds the neighboring product by exactly one.
-/
theorem central_square_minus_neighbors
    (n : Nat) :
    (centralReadout n : Int) ^ 2
      -
    (
      (lowerReadout n : Int)
        *
      (upperReadout n : Int)
    ) =
      1 := by

  unfold lowerReadout
  unfold centralReadout
  unfold upperReadout

  push_cast

  ring

/--
The rational Wallis denominator is the central square minus one.
-/
theorem neighbor_product_eq_central_square_sub_one
    (n : Nat) :
    (lowerReadout n : ℚ)
        *
      (upperReadout n : ℚ) =
    (centralReadout n : ℚ) ^ 2 - 1 := by

  unfold lowerReadout
  unfold centralReadout
  unfold upperReadout

  push_cast

  ring

/--
The exact positive correction above one.
-/
def wallisDefect
    (n : Nat) :
    ℚ :=

  1 /
    (
      4 * ((n + 1 : Nat) : ℚ) ^ 2 - 1
    )

/--
The denominator defining the defect is positive.
-/
theorem wallisDefect_denominator_positive
    (n : Nat) :
    0 <
      4 * ((n + 1 : Nat) : ℚ) ^ 2 - 1 := by

  have h :
      (1 : ℚ) ≤
        ((n + 1 : Nat) : ℚ) := by

    exact_mod_cast
      Nat.succ_le_succ
        (Nat.zero_le n)

  nlinarith [
    sq_nonneg
      (((n + 1 : Nat) : ℚ) - 1)
  ]

/--
Every Wallis defect is strictly positive.
-/
theorem wallisDefect_positive
    (n : Nat) :
    0 <
      wallisDefect n := by

  unfold wallisDefect

  exact
    one_div_pos.mpr
      (
        wallisDefect_denominator_positive n
      )

/--
Each Wallis factor is exactly one plus its triadic defect.
-/
theorem wallisFactor_eq_one_add_defect
    (n : Nat) :
    wallisFactor n =
      1 + wallisDefect n := by

  unfold wallisFactor
  unfold wallisDefect

  let denominator : ℚ :=
    4 * ((n + 1 : Nat) : ℚ) ^ 2 - 1

  have hDenominator :
      denominator ≠ 0 := by

    exact
      ne_of_gt
        (
          wallisDefect_denominator_positive n
        )

  have hNumerator :
      4 * ((n + 1 : Nat) : ℚ) ^ 2 =
        denominator + 1 := by

    unfold denominator

    ring

  rw [
    hNumerator
  ]

  field_simp [
    hDenominator
  ]

  ring
/--
Every Wallis factor is strictly greater than one.
-/
theorem one_lt_wallisFactor
    (n : Nat) :
    1 <
      wallisFactor n := by

  rw [
    wallisFactor_eq_one_add_defect
  ]

  exact
    lt_add_of_pos_right
      1
      (
        wallisDefect_positive n
      )

/--
Each successor product is strictly larger than the preceding product.
-/
theorem wallisProduct_strictly_increases
    (n : Nat) :
    wallisProduct n <
      wallisProduct (n + 1) := by

  rw [
    wallisProduct_succ
  ]

  have hProduct :
      0 <
        wallisProduct n :=
    wallisProduct_positive n

  have hFactor :
      1 <
        wallisFactor n :=
    one_lt_wallisFactor n

  nlinarith [
    mul_lt_mul_of_pos_left
      hFactor
      hProduct
  ]

/--
The exact difference between successive products.
-/
theorem wallisProduct_successor_difference
    (n : Nat) :
    wallisProduct (n + 1)
        -
      wallisProduct n =
    wallisProduct n
        *
      wallisDefect n := by

  rw [
    wallisProduct_succ,
    wallisFactor_eq_one_add_defect
  ]

  ring

/--
The first three factors are generated exactly.
-/
theorem first_three_wallisFactors :
    wallisFactor 0 =
        4 / 3
      ∧
    wallisFactor 1 =
        16 / 15
      ∧
    wallisFactor 2 =
        36 / 35 := by

  norm_num [
    wallisFactor
  ]

/--
Capstone theorem.

The middle member of every odd-even-odd readout triad has square one
greater than the neighboring product. Therefore each Wallis factor is
exactly one plus a unique positive rational defect, and the finite
Wallis products increase strictly at every stage.
-/
theorem triadic_unit_defect_drives_wallis_growth :
    (∀ n : Nat,
      (centralReadout n : Int) ^ 2
        -
      (
        (lowerReadout n : Int)
          *
        (upperReadout n : Int)
      ) =
        1)
      ∧
    (∀ n : Nat,
      wallisFactor n =
        1 + wallisDefect n)
      ∧
    (∀ n : Nat,
      0 <
        wallisDefect n)
      ∧
    (∀ n : Nat,
      wallisProduct n <
        wallisProduct (n + 1)) := by

  exact
    ⟨
      central_square_minus_neighbors,
      wallisFactor_eq_one_add_defect,
      wallisDefect_positive,
      wallisProduct_strictly_increases
    ⟩

end GlyphSpectralWallisDefect

#check GlyphSpectralWallisDefect.centralScale
#check GlyphSpectralWallisDefect.readouts_from_centralScale
#check GlyphSpectralWallisDefect.central_square_minus_neighbors
#check GlyphSpectralWallisDefect.neighbor_product_eq_central_square_sub_one
#check GlyphSpectralWallisDefect.wallisDefect
#check GlyphSpectralWallisDefect.wallisDefect_positive
#check GlyphSpectralWallisDefect.wallisFactor_eq_one_add_defect
#check GlyphSpectralWallisDefect.one_lt_wallisFactor
#check GlyphSpectralWallisDefect.wallisProduct_strictly_increases
#check GlyphSpectralWallisDefect.wallisProduct_successor_difference
#check GlyphSpectralWallisDefect.first_three_wallisFactors
#check GlyphSpectralWallisDefect.triadic_unit_defect_drives_wallis_growth
