import KTLean.GlyphSpectralTrigonometricOperations
import KTLean.GlyphSpectrum
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Differentiation of the Special-Function Operations

## Formal status

**Level 2 — Analytic reconstruction from mature arithmetic,
logarithmic, and trigonometric development.**

## Developmental predecessor

`GlyphSpectralTrigonometricOperations`

The preceding analytic development supplies arithmetic, powers,
reciprocal orientation, exponential and logarithmic evolution, and
circular and hyperbolic operations.

The next differentiated family consists of constants arising from
infinite accumulation:

* the Euler–Mascheroni constant `γ`, obtained from the asymptotic
  difference between harmonic growth and logarithmic growth;
* `ζ(2)` and `ζ(3)`, obtained from convergent reciprocal-power
  accumulation.

Each positive value produces a reciprocal orientation partner. Only
after these constants and reciprocal identities are established is the
canonical glyph table consulted.

The resulting block is

    γ⁻¹,    γ,
    ζ(2)⁻¹, ζ(2),
    ζ(3)⁻¹, ζ(3).
-/

namespace GlyphSpectralSpecialFunctionOperations

open Filter
open scoped BigOperators Topology

/-
## Euler–Mascheroni differentiation
-/

/--
The Euler–Mascheroni value produced by the asymptotic difference between
harmonic accumulation and logarithmic growth.
-/
noncomputable def eulerMascheroni :
    ℝ :=
  Real.eulerMascheroniConstant

/--
The Euler–Mascheroni value is the limit of harmonic growth minus
logarithmic growth.
-/
theorem harmonic_log_difference_tends_to_eulerMascheroni :
    Tendsto
        (fun n : ℕ =>
          (harmonic n : ℝ) -
            Real.log n)
        atTop
        (𝓝 eulerMascheroni) := by

  unfold eulerMascheroni

  exact
    Real.tendsto_harmonic_sub_log

/--
The Euler–Mascheroni value is strictly positive.
-/
theorem eulerMascheroni_positive :
    0 < eulerMascheroni := by

  unfold eulerMascheroni

  have hLower :
      (1 / 2 : ℝ) <
        Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant

  linarith

/--
The Euler–Mascheroni value is nonzero.
-/
theorem eulerMascheroni_ne_zero :
    eulerMascheroni ≠ 0 := by

  exact
    ne_of_gt
      eulerMascheroni_positive

/--
The reciprocal Euler–Mascheroni orientation.
-/
noncomputable def inverseEulerMascheroni :
    ℝ :=
  eulerMascheroni⁻¹

/--
The Euler–Mascheroni orientation pair is reciprocal.
-/
theorem inverseEulerMascheroni_mul_eulerMascheroni :
    inverseEulerMascheroni * eulerMascheroni =
      1 := by

  unfold inverseEulerMascheroni

  exact
    inv_mul_cancel₀
      eulerMascheroni_ne_zero

/-
## Reciprocal-power accumulation
-/

/--
The positive reciprocal-power tail beginning at the integer `2`.

The initial term `1` is separated explicitly. This makes the arithmetic
origin of the zeta values visible:

    ζ(s) = 1 + 1 / 2^s + 1 / 3^s + ...
-/
noncomputable def reciprocalPowerTail
    (exponent : ℕ) :
    ℝ :=
  ∑' n : ℕ,
    1 / (((n + 2 : ℕ) : ℝ) ^ exponent)

/--
Every term in a reciprocal-power tail is nonnegative.
-/
theorem reciprocalPowerTail_term_nonnegative
    (exponent n : ℕ) :
    0 ≤
      1 / (((n + 2 : ℕ) : ℝ) ^ exponent) := by

  positivity

/--
Every reciprocal-power tail is nonnegative.
-/
theorem reciprocalPowerTail_nonnegative
    (exponent : ℕ) :
    0 ≤ reciprocalPowerTail exponent := by

  unfold reciprocalPowerTail

  exact
    tsum_nonneg
      (fun n =>
        reciprocalPowerTail_term_nonnegative
          exponent
          n)

/--
The real Dirichlet-series zeta value at a natural exponent.
-/
noncomputable def zetaValue
    (exponent : ℕ) :
    ℝ :=
  1 + reciprocalPowerTail exponent

/--
Every reconstructed natural zeta value is at least one.
-/
theorem one_le_zetaValue
    (exponent : ℕ) :
    1 ≤ zetaValue exponent := by

  unfold zetaValue

  have hTail :
      0 ≤ reciprocalPowerTail exponent :=
    reciprocalPowerTail_nonnegative exponent

  linarith

/--
Every reconstructed natural zeta value is positive.
-/
theorem zetaValue_positive
    (exponent : ℕ) :
    0 < zetaValue exponent := by

  have hOne :
      1 ≤ zetaValue exponent :=
    one_le_zetaValue exponent

  linarith

/-
## ζ(2)
-/

/--
The reciprocal-square accumulation `ζ(2)`.
-/
noncomputable def zetaTwo :
    ℝ :=
  zetaValue 2

/--
`ζ(2)` is positive.
-/
theorem zetaTwo_positive :
    0 < zetaTwo := by

  unfold zetaTwo

  exact
    zetaValue_positive 2

/--
`ζ(2)` is nonzero.
-/
theorem zetaTwo_ne_zero :
    zetaTwo ≠ 0 := by

  exact
    ne_of_gt
      zetaTwo_positive

/--
The reciprocal orientation of `ζ(2)`.
-/
noncomputable def inverseZetaTwo :
    ℝ :=
  zetaTwo⁻¹

/--
The `ζ(2)` orientation pair is reciprocal.
-/
theorem inverseZetaTwo_mul_zetaTwo :
    inverseZetaTwo * zetaTwo =
      1 := by

  unfold inverseZetaTwo

  exact
    inv_mul_cancel₀
      zetaTwo_ne_zero

/-
## ζ(3)
-/

/--
The reciprocal-cube accumulation `ζ(3)`.
-/
noncomputable def zetaThree :
    ℝ :=
  zetaValue 3

/--
`ζ(3)` is positive.
-/
theorem zetaThree_positive :
    0 < zetaThree := by

  unfold zetaThree

  exact
    zetaValue_positive 3

/--
`ζ(3)` is nonzero.
-/
theorem zetaThree_ne_zero :
    zetaThree ≠ 0 := by

  exact
    ne_of_gt
      zetaThree_positive

/--
The reciprocal orientation of `ζ(3)`.
-/
noncomputable def inverseZetaThree :
    ℝ :=
  zetaThree⁻¹

/--
The `ζ(3)` orientation pair is reciprocal.
-/
theorem inverseZetaThree_mul_zetaThree :
    inverseZetaThree * zetaThree =
      1 := by

  unfold inverseZetaThree

  exact
    inv_mul_cancel₀
      zetaThree_ne_zero

/-
## Mature special-function family
-/

/--
The three direct special-function values are positive.
-/
theorem special_function_values_positive :
    0 < eulerMascheroni
      ∧
    0 < zetaTwo
      ∧
    0 < zetaThree := by

  exact
    ⟨
      eulerMascheroni_positive,
      zetaTwo_positive,
      zetaThree_positive
    ⟩

/--
The three special-function orientation pairs are reciprocal.
-/
theorem special_function_pairs_reciprocal :
    inverseEulerMascheroni * eulerMascheroni =
        1
      ∧
    inverseZetaTwo * zetaTwo =
        1
      ∧
    inverseZetaThree * zetaThree =
        1 := by

  exact
    ⟨
      inverseEulerMascheroni_mul_eulerMascheroni,
      inverseZetaTwo_mul_zetaTwo,
      inverseZetaThree_mul_zetaThree
    ⟩

/-
## Canonical registration
-/

/--
The canonical symbolic special-function block.
-/
def specialFunctionBlock :
    List GlyphSpectrum.SpectralValue :=
  [
    .inverse .eulerMascheroni,
    .eulerMascheroni,
    .inverse (.zeta 2),
    .zeta 2,
    .inverse (.zeta 3),
    .zeta 3
  ]

/--
Glyph positions 31 through 36 are exactly the canonical special-function
block.
-/
theorem registered_special_function_block :
    (GlyphSpectrum.values.drop 30).take 6 =
      specialFunctionBlock := by

  native_decide

/--
The Euler–Mascheroni pair occupies glyphs 31 and 32.
-/
theorem registered_eulerMascheroni_pair :
    GlyphSpectrum.values[30]? =
        some
          (.inverse .eulerMascheroni)
      ∧
    GlyphSpectrum.values[31]? =
        some
          .eulerMascheroni := by

  native_decide

/--
The `ζ(2)` pair occupies glyphs 33 and 34.
-/
theorem registered_zetaTwo_pair :
    GlyphSpectrum.values[32]? =
        some
          (.inverse (.zeta 2))
      ∧
    GlyphSpectrum.values[33]? =
        some
          (.zeta 2) := by

  native_decide

/--
The `ζ(3)` pair occupies glyphs 35 and 36.
-/
theorem registered_zetaThree_pair :
    GlyphSpectrum.values[34]? =
        some
          (.inverse (.zeta 3))
      ∧
    GlyphSpectrum.values[35]? =
        some
          (.zeta 3) := by

  native_decide

/--
Capstone theorem.

Harmonic and logarithmic growth differentiate the Euler–Mascheroni
constant. Reciprocal-power accumulation differentiates `ζ(2)` and
`ζ(3)`. Each direct value is positive and therefore nonzero, orientation
reversal produces its reciprocal, and the resulting six-value family is
exactly the canonical special-function glyph block.
-/
theorem special_function_operations_emerge :
    Tendsto
        (fun n : ℕ =>
          (harmonic n : ℝ) -
            Real.log n)
        atTop
        (𝓝 eulerMascheroni)
      ∧
    (
      0 < eulerMascheroni
        ∧
      0 < zetaTwo
        ∧
      0 < zetaThree
    )
      ∧
    (
      inverseEulerMascheroni * eulerMascheroni =
          1
        ∧
      inverseZetaTwo * zetaTwo =
          1
        ∧
      inverseZetaThree * zetaThree =
          1
    )
      ∧
    (GlyphSpectrum.values.drop 30).take 6 =
      specialFunctionBlock := by

  exact
    ⟨
      harmonic_log_difference_tends_to_eulerMascheroni,
      special_function_values_positive,
      special_function_pairs_reciprocal,
      registered_special_function_block
    ⟩

end GlyphSpectralSpecialFunctionOperations

#check GlyphSpectralSpecialFunctionOperations.eulerMascheroni
#check GlyphSpectralSpecialFunctionOperations.harmonic_log_difference_tends_to_eulerMascheroni
#check GlyphSpectralSpecialFunctionOperations.reciprocalPowerTail
#check GlyphSpectralSpecialFunctionOperations.zetaValue
#check GlyphSpectralSpecialFunctionOperations.zetaTwo
#check GlyphSpectralSpecialFunctionOperations.zetaThree
#check GlyphSpectralSpecialFunctionOperations.special_function_values_positive
#check GlyphSpectralSpecialFunctionOperations.special_function_pairs_reciprocal
#check GlyphSpectralSpecialFunctionOperations.specialFunctionBlock
#check GlyphSpectralSpecialFunctionOperations.registered_special_function_block
#check GlyphSpectralSpecialFunctionOperations.special_function_operations_emerge
