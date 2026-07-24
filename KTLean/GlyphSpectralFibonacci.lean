import KTLean.GlyphSpectralTriadicEngine
import KTLean.GlyphAttractorTableBridge
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Fibonacci Closure Forces the Golden Pair

## Formal status

**Level 2 — Exact fixed-ratio derivation for the Fibonacci basin.**

The native KT motif is:

    two existing states force one unique third state.

For the Fibonacci basin, the closure law is additive:

    x, y ↦ x + y.

If consecutive terms possess a stable positive ratio `r`, then the
next ratio is

    1 + 1 / r.

A fixed ratio therefore satisfies

    r = 1 + 1 / r,

equivalently

    r² = r + 1.

This module proves:

* the positive fixed ratio exists;
* it is unique;
* it is the golden ratio;
* orientation reversal reads the reciprocal ratio;
* that reciprocal equals `φ - 1`.

Thus the Fibonacci basin forces the unordered reciprocal pair

    {φ⁻¹, φ}.

The assignment of the two members to the two canonical orientation
labels is then fixed by the established glyph-order convention.
-/

namespace GlyphSpectralFibonacci

open GlyphSpectralTriadicEngine
open GlyphForcingOrientation

/--
The additive two-parent closure law.
-/
def additiveClosure :
    ClosureLaw ℝ :=
  fun x y =>
    x + y

/--
The additive closure has one unique completion for every ordered pair.
-/
theorem additiveClosure_unique
    (x y : ℝ) :
    ∃! z : ℝ,
      Completes
        additiveClosure
        x
        y
        z := by

  exact
    existsUnique_completion
      additiveClosure
      x
      y

/--
The ratio update induced by additive closure.

If `y / x = r`, then

    (x + y) / y = 1 + 1 / r.
-/
noncomputable def ratioUpdate
    (r : ℝ) :
    ℝ :=
  1 + 1 / r

/--
A positive stable ratio for additive triadic closure.
-/
def IsPositiveStableRatio
    (r : ℝ) :
    Prop :=

  0 < r
    ∧
  ratioUpdate r =
    r

/--
Every positive stable ratio satisfies the golden quadratic.
-/
theorem stableRatio_quadratic
    {r : ℝ}
    (hStable :
      IsPositiveStableRatio r) :
    r ^ 2 =
      r + 1 := by

  rcases hStable with
    ⟨hPositive, hFixed⟩

  have hNonzero :
      r ≠ 0 :=
    ne_of_gt hPositive

  unfold ratioUpdate at hFixed

  field_simp [hNonzero] at hFixed

  nlinarith

/--
The real golden ratio.
-/
noncomputable def phi :
    ℝ :=
  (
    1 + Real.sqrt 5
  ) / 2

/--
The square of `sqrt 5` is `5`.
-/
theorem sqrt_five_squared :
    (Real.sqrt 5) ^ 2 =
      5 := by

  exact
    Real.sq_sqrt
      (
        by
          norm_num
      )

/--
The golden ratio satisfies its defining quadratic.
-/
theorem phi_quadratic :
    phi ^ 2 =
      phi + 1 := by

  unfold phi

  have hSquare :
      (Real.sqrt 5) ^ 2 =
        5 :=
    sqrt_five_squared

  nlinarith

/--
The golden ratio is positive.
-/
theorem phi_positive :
    0 < phi := by

  unfold phi

  have hSqrtNonnegative :
      0 ≤ Real.sqrt 5 :=
    Real.sqrt_nonneg 5

  nlinarith

/--
The golden ratio is nonzero.
-/
theorem phi_ne_zero :
    phi ≠ 0 := by

  exact
    ne_of_gt
      phi_positive

/--
The golden ratio is a fixed point of the additive ratio update.
-/
theorem ratioUpdate_phi :
    ratioUpdate phi =
      phi := by

  unfold ratioUpdate

  field_simp [phi_ne_zero]

  nlinarith [
    phi_quadratic
  ]

/--
The golden ratio is a positive stable ratio.
-/
theorem phi_isPositiveStableRatio :
    IsPositiveStableRatio phi := by

  exact
    ⟨
      phi_positive,
      ratioUpdate_phi
    ⟩

/--
Two positive roots of the golden quadratic are equal.
-/
theorem positive_golden_root_unique
    {left right : ℝ}
    (hLeftPositive :
      0 < left)
    (hRightPositive :
      0 < right)
    (hLeft :
      left ^ 2 =
        left + 1)
    (hRight :
      right ^ 2 =
        right + 1) :
    left =
      right := by

  have hFactor :
      (
        left - right
      )
        *
      (
        left + right - 1
      ) =
        0 := by

    nlinarith

  rcases
    mul_eq_zero.mp hFactor
  with
    hEqual | hSum

  · exact
      sub_eq_zero.mp
        hEqual

  · exfalso

    nlinarith

/--
The golden ratio is the unique positive stable ratio of additive
triadic closure.
-/
theorem existsUnique_positiveStableRatio :
    ∃! r : ℝ,
      IsPositiveStableRatio r := by

  refine
    ⟨
      phi,
      phi_isPositiveStableRatio,
      ?_
    ⟩

  intro other hOther

  exact
    positive_golden_root_unique
      hOther.1
      phi_positive
      (
        stableRatio_quadratic
          hOther
      )
      phi_quadratic

/--
The reciprocal golden ratio.
-/
noncomputable def inversePhi :
    ℝ :=
  phi⁻¹

/--
The reciprocal golden ratio is positive.
-/
theorem inversePhi_positive :
    0 < inversePhi := by

  unfold inversePhi

  exact
    inv_pos.mpr
      phi_positive

/--
The reciprocal golden ratio equals `φ - 1`.
-/
theorem inversePhi_eq_phi_sub_one :
    inversePhi =
      phi - 1 := by

  unfold inversePhi

  field_simp [phi_ne_zero]

  nlinarith [
    phi_quadratic
  ]

/--
The golden ratio and its reciprocal multiply to one.
-/
theorem inversePhi_mul_phi :
    inversePhi * phi =
      1 := by

  unfold inversePhi

  exact
    inv_mul_cancel₀
      phi_ne_zero

/--
Reading the stable ratio in the opposite direction produces its
reciprocal.
-/
noncomputable def orientedGoldenValue :
    ForcedOrientation →
      ℝ

  | .forward =>
      inversePhi

  | .reverse =>
      phi

/--
The forward orientation carries the reciprocal member.
-/
@[simp]
theorem orientedGoldenValue_forward :
    orientedGoldenValue
        ForcedOrientation.forward =
      inversePhi := by

  rfl

/--
The reverse orientation carries the golden-ratio member.
-/
@[simp]
theorem orientedGoldenValue_reverse :
    orientedGoldenValue
        ForcedOrientation.reverse =
      phi := by

  rfl

/--
The two oriented Fibonacci values are reciprocal.
-/
theorem orientedGoldenValues_reciprocal :
    orientedGoldenValue
        ForcedOrientation.forward
      *
    orientedGoldenValue
        ForcedOrientation.reverse =
      1 := by

  exact
    inversePhi_mul_phi

/--
The structurally selected Fibonacci basin consists of exactly two
glyphs.
-/
theorem fibonacci_basin_has_two_glyphs :
    (
      GlyphAttractorTableBridge.glyphNumbersInBasin
        GlyphAttractorSignature.Basin.fibonacci
    ) =
      [7, 8] := by

  exact
    GlyphAttractorTableBridge.fibonacci_glyph_numbers

/--
The registered symbolic Fibonacci block is exactly the reciprocal
golden pair.
-/
theorem registered_fibonacci_block :
    GlyphAttractorTableBridge.registeredValuesInBasin
        GlyphAttractorSignature.Basin.fibonacci =
      [
        .inverse .goldenRatio,
        .goldenRatio
      ] := by

  exact
    GlyphAttractorTableBridge.fibonacci_registered_values

/--
Capstone theorem.

Additive two-parent closure has exactly one positive stable ratio,
namely `φ`, and reversing the ratio yields `φ⁻¹`. These are precisely
the two members registered on the structurally forced Fibonacci basin.
-/
theorem fibonacci_closure_forces_golden_pair :
    (∃! r : ℝ,
      IsPositiveStableRatio r)
      ∧
    IsPositiveStableRatio phi
      ∧
    inversePhi =
        phi⁻¹
      ∧
    inversePhi * phi =
        1
      ∧
    GlyphAttractorTableBridge.registeredValuesInBasin
        GlyphAttractorSignature.Basin.fibonacci =
      [
        .inverse .goldenRatio,
        .goldenRatio
      ] := by

  exact
    ⟨
      existsUnique_positiveStableRatio,
      phi_isPositiveStableRatio,
      rfl,
      inversePhi_mul_phi,
      registered_fibonacci_block
    ⟩

end GlyphSpectralFibonacci

#check GlyphSpectralFibonacci.additiveClosure
#check GlyphSpectralFibonacci.additiveClosure_unique
#check GlyphSpectralFibonacci.ratioUpdate
#check GlyphSpectralFibonacci.IsPositiveStableRatio
#check GlyphSpectralFibonacci.stableRatio_quadratic
#check GlyphSpectralFibonacci.phi
#check GlyphSpectralFibonacci.phi_quadratic
#check GlyphSpectralFibonacci.phi_positive
#check GlyphSpectralFibonacci.ratioUpdate_phi
#check GlyphSpectralFibonacci.phi_isPositiveStableRatio
#check GlyphSpectralFibonacci.positive_golden_root_unique
#check GlyphSpectralFibonacci.existsUnique_positiveStableRatio
#check GlyphSpectralFibonacci.inversePhi
#check GlyphSpectralFibonacci.inversePhi_eq_phi_sub_one
#check GlyphSpectralFibonacci.inversePhi_mul_phi
#check GlyphSpectralFibonacci.orientedGoldenValue
#check GlyphSpectralFibonacci.orientedGoldenValues_reciprocal
#check GlyphSpectralFibonacci.fibonacci_closure_forces_golden_pair
