import KTLean.GlyphSpectralLogarithmicOperations
import KTLean.SpinorOrbit
import KTLean.GlyphSpectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Differentiation of the Trigonometric Operations

## Formal status

**Level 2 — Analytic reconstruction from rotational and exponential
development.**

## Developmental predecessor

`GlyphSpectralLogarithmicOperations`

The preceding development reconstructs exponential evolution and its
logarithmic inverse. Independently, the KT spinor chain proves that a
half-closure reaches the deck partner and that doubling the traversal
returns to the initial state.

This module reads the unit parameter through the two natural continuations
of exponential evolution:

* circular rotation, producing `sin 1` and `cos 1`;
* hyperbolic evolution, producing `tanh 1`.

Orientation reversal supplies the reciprocal members. Only after these
analytic values and reciprocal pairs are established is the canonical
glyph table consulted.

The resulting block is

    (sin 1)⁻¹,  sin 1,
    (cos 1)⁻¹,  cos 1,
    (tanh 1)⁻¹, tanh 1.
-/

namespace GlyphSpectralTrigonometricOperations

open Set
open Filter
open scoped Topology

/-
## Rotational developmental parent
-/

/--
Every KT spinorial half-closure distinguishes the half-turn from the
full return.

This is the discrete rotational parent carried into the trigonometric
development.
-/
theorem spinorial_rotation_parent
    {S : SpinorOrbit.System}
    (H : S.HalfClosure) :
    S.ReachesDeckAt H.halfPeriod
      ∧
    ¬ S.ReturnsAt H.halfPeriod
      ∧
    S.ReturnsAt H.fullPeriod := by

   exact
    SpinorOrbit.System.double_cover_separation H

/-
## Direct unit trigonometric values
-/

/--
The unit circular sine value.
-/
noncomputable def sineOne :
    ℝ :=
  Real.sin 1

/--
The unit circular cosine value.
-/
noncomputable def cosineOne :
    ℝ :=
  Real.cos 1

/--
The unit hyperbolic tangent value.
-/
noncomputable def tanhOne :
    ℝ :=
  Real.tanh 1

/--
The unit parameter lies strictly below π.
-/
theorem one_lt_pi :
    (1 : ℝ) < Real.pi := by

  have hPi :
      (3 : ℝ) < Real.pi :=
    Real.pi_gt_three

  linarith

/--
The unit parameter lies strictly below π / 2.
-/
theorem one_lt_pi_div_two :
    (1 : ℝ) < Real.pi / 2 := by

  have hPi :
      (3 : ℝ) < Real.pi :=
    Real.pi_gt_three

  linarith


/--
The unit sine value is positive.
-/
theorem sineOne_positive :
    0 < sineOne := by

  unfold sineOne

  exact
    Real.sin_pos_of_pos_of_lt_pi
      (by norm_num)
      one_lt_pi

/--
The unit cosine value is positive.
-/
theorem cosineOne_positive :
    0 < cosineOne := by

  unfold cosineOne

  apply
    Real.cos_pos_of_mem_Ioo

  constructor

  · have hPositivePi :
        0 < Real.pi :=
      Real.pi_pos

    linarith

  · exact
      one_lt_pi_div_two

/--
The unit hyperbolic tangent value is positive.
-/
theorem tanhOne_positive :
    0 < tanhOne := by

  unfold tanhOne
  rw [Real.tanh_eq]

  have hNumerator :
      0 <
        Real.exp 1 -
          Real.exp (-1) := by

    exact
      sub_pos.mpr
        (
          Real.exp_lt_exp.mpr
            (by norm_num)
        )

  have hDenominator :
      0 <
        Real.exp 1 +
          Real.exp (-1) := by

    positivity

  exact
    div_pos
      hNumerator
      hDenominator

/--
All three direct unit values are positive.
-/
theorem trigonometric_values_positive :
    0 < sineOne
      ∧
    0 < cosineOne
      ∧
    0 < tanhOne := by

  exact
    ⟨
      sineOne_positive,
      cosineOne_positive,
      tanhOne_positive
    ⟩

/-
## Nonvanishing and reciprocal orientation
-/

/--
The unit sine value is nonzero.
-/
theorem sineOne_ne_zero :
    sineOne ≠ 0 := by

  exact
    ne_of_gt
      sineOne_positive

/--
The unit cosine value is nonzero.
-/
theorem cosineOne_ne_zero :
    cosineOne ≠ 0 := by

  exact
    ne_of_gt
      cosineOne_positive

/--
The unit hyperbolic tangent value is nonzero.
-/
theorem tanhOne_ne_zero :
    tanhOne ≠ 0 := by

  exact
    ne_of_gt
      tanhOne_positive

/--
The reciprocal unit sine value.
-/
noncomputable def inverseSineOne :
    ℝ :=
  sineOne⁻¹

/--
The reciprocal unit cosine value.
-/
noncomputable def inverseCosineOne :
    ℝ :=
  cosineOne⁻¹

/--
The reciprocal unit hyperbolic tangent value.
-/
noncomputable def inverseTanhOne :
    ℝ :=
  tanhOne⁻¹

/--
The sine orientation pair is reciprocal.
-/
theorem inverseSineOne_mul_sineOne :
    inverseSineOne * sineOne =
      1 := by

  unfold inverseSineOne

  exact
    inv_mul_cancel₀
      sineOne_ne_zero

/--
The cosine orientation pair is reciprocal.
-/
theorem inverseCosineOne_mul_cosineOne :
    inverseCosineOne * cosineOne =
      1 := by

  unfold inverseCosineOne

  exact
    inv_mul_cancel₀
      cosineOne_ne_zero

/--
The hyperbolic-tangent orientation pair is reciprocal.
-/
theorem inverseTanhOne_mul_tanhOne :
    inverseTanhOne * tanhOne =
      1 := by

  unfold inverseTanhOne

  exact
    inv_mul_cancel₀
      tanhOne_ne_zero

/--
The three trigonometric orientation pairs are reciprocal.
-/
theorem trigonometric_pairs_reciprocal :
    inverseSineOne * sineOne =
        1
      ∧
    inverseCosineOne * cosineOne =
        1
      ∧
    inverseTanhOne * tanhOne =
        1 := by

  exact
    ⟨
      inverseSineOne_mul_sineOne,
      inverseCosineOne_mul_cosineOne,
      inverseTanhOne_mul_tanhOne
    ⟩

/-
## Circular and hyperbolic provenance
-/

/--
The unit circular pair lies on the unit circle.
-/
theorem sineOne_sq_add_cosineOne_sq :
    sineOne ^ 2 + cosineOne ^ 2 =
      1 := by

  unfold sineOne
  unfold cosineOne

  exact
    Real.sin_sq_add_cos_sq 1

/--
The hyperbolic tangent is the quotient of hyperbolic sine and cosine at
unit parameter.
-/
theorem tanhOne_eq_sinh_div_cosh :
    tanhOne =
      Real.sinh 1 / Real.cosh 1 := by

  unfold tanhOne

  exact
    Real.tanh_eq_sinh_div_cosh 1

/--
The unit hyperbolic tangent lies below one.
-/
theorem tanhOne_lt_one :
    tanhOne < 1 := by

  unfold tanhOne

  exact
    Real.tanh_lt_one 1

/--
The three direct trigonometric values occupy their natural analytic
regions.
-/
theorem trigonometric_unit_profile :
    sineOne ^ 2 + cosineOne ^ 2 =
        1
      ∧
    0 < sineOne
      ∧
    0 < cosineOne
      ∧
    0 < tanhOne
      ∧
    tanhOne < 1 := by

  exact
    ⟨
      sineOne_sq_add_cosineOne_sq,
      sineOne_positive,
      cosineOne_positive,
      tanhOne_positive,
      tanhOne_lt_one
    ⟩

/-
## Canonical registration
-/

/--
The canonical symbolic trigonometric block.
-/
def trigonometricBlock :
    List GlyphSpectrum.SpectralValue :=
  [
    .inverse .sineOne,
    .sineOne,
    .inverse .cosineOne,
    .cosineOne,
    .inverse .hyperbolicTangentOne,
    .hyperbolicTangentOne
  ]

/--
Glyph positions 25 through 30 are exactly the canonical trigonometric
block.
-/
theorem registered_trigonometric_block :
    (GlyphSpectrum.values.drop 24).take 6 =
      trigonometricBlock := by

  native_decide

/--
The unit sine orientation pair occupies glyphs 25 and 26.
-/
theorem registered_sineOne_pair :
    GlyphSpectrum.values[24]? =
        some
          (.inverse .sineOne)
      ∧
    GlyphSpectrum.values[25]? =
        some
          .sineOne := by

  native_decide

/--
The unit cosine orientation pair occupies glyphs 27 and 28.
-/
theorem registered_cosineOne_pair :
    GlyphSpectrum.values[26]? =
        some
          (.inverse .cosineOne)
      ∧
    GlyphSpectrum.values[27]? =
        some
          .cosineOne := by

  native_decide

/--
The unit hyperbolic-tangent orientation pair occupies glyphs 29 and 30.
-/
theorem registered_tanhOne_pair :
    GlyphSpectrum.values[28]? =
        some
          (.inverse .hyperbolicTangentOne)
      ∧
    GlyphSpectrum.values[29]? =
        some
          .hyperbolicTangentOne := by

  native_decide

/--
Capstone theorem.

Spinorial double-cover evolution supplies the discrete rotational parent.
At unit parameter, circular evolution produces `sin 1` and `cos 1`,
while hyperbolic exponential evolution produces `tanh 1`. Each value is
positive and nonzero, orientation reversal produces its reciprocal, and
the resulting six-value family is exactly the canonical trigonometric
glyph block.
-/
theorem trigonometric_operations_emerge :
    (
      ∀
        {S : SpinorOrbit.System}
        (H : S.HalfClosure),
        S.ReachesDeckAt H.halfPeriod
          ∧
        ¬ S.ReturnsAt H.halfPeriod
          ∧
        S.ReturnsAt H.fullPeriod
    )
      ∧
    (
      sineOne ^ 2 + cosineOne ^ 2 =
          1
        ∧
      0 < sineOne
        ∧
      0 < cosineOne
        ∧
      0 < tanhOne
        ∧
      tanhOne < 1
    )
      ∧
    (
      inverseSineOne * sineOne =
          1
        ∧
      inverseCosineOne * cosineOne =
          1
        ∧
      inverseTanhOne * tanhOne =
          1
    )
      ∧
    (GlyphSpectrum.values.drop 24).take 6 =
      trigonometricBlock := by

  refine
    ⟨
      ?_,
      trigonometric_unit_profile,
      trigonometric_pairs_reciprocal,
      registered_trigonometric_block
    ⟩

  intro S H

  exact
    spinorial_rotation_parent H

end GlyphSpectralTrigonometricOperations

#check GlyphSpectralTrigonometricOperations.spinorial_rotation_parent
#check GlyphSpectralTrigonometricOperations.sineOne
#check GlyphSpectralTrigonometricOperations.cosineOne
#check GlyphSpectralTrigonometricOperations.tanhOne
#check GlyphSpectralTrigonometricOperations.trigonometric_values_positive
#check GlyphSpectralTrigonometricOperations.trigonometric_pairs_reciprocal
#check GlyphSpectralTrigonometricOperations.sineOne_sq_add_cosineOne_sq
#check GlyphSpectralTrigonometricOperations.tanhOne_eq_sinh_div_cosh
#check GlyphSpectralTrigonometricOperations.trigonometricBlock
#check GlyphSpectralTrigonometricOperations.registered_trigonometric_block
#check GlyphSpectralTrigonometricOperations.trigonometric_operations_emerge
