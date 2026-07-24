import KTLean.GlyphSpectralWallisDefect
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Tactic

/-!
# The Wallis Stream Converges to π / 2

## Formal status

**Level 3 — Analytic identification of the derived KT Wallis stream.**

Previous modules derived the discrete triadic factor

    Wₙ = (2n + 2)² / ((2n + 1)(2n + 3))

and its finite rational product.

Mathlib independently proves that the corresponding real Wallis
product converges to `π / 2`.

This module establishes that the cast of the KT rational product is
exactly Mathlib's Wallis product at every finite stage. The analytic
limit therefore follows without adding any new spectral assignment.

The result is:

    2 * limit(KT Wallis product) = π.
-/

namespace GlyphSpectralWallisLimit

open Filter
open Finset
open scoped Topology

open GlyphSpectralWallisKernel

/--
The real-valued form of the previously derived rational Wallis factor.
-/
noncomputable def realWallisFactor
    (n : Nat) :
    ℝ :=

  (wallisFactor n : ℝ)

/--
The factor used by Mathlib's Wallis product.
-/
noncomputable def mathlibWallisFactor
    (n : Nat) :
    ℝ :=

  ((2 : ℝ) * n + 2) / (2 * n + 1)
    *
  ((2 : ℝ) * n + 2) / (2 * n + 3)

/--
The denominator `2n + 1` is positive over the reals.
-/
theorem lower_real_positive
    (n : Nat) :
    0 <
      (2 : ℝ) * n + 1 := by

  positivity

/--
The denominator `2n + 3` is positive over the reals.
-/
theorem upper_real_positive
    (n : Nat) :
    0 <
      (2 : ℝ) * n + 3 := by

  positivity

/--
The denominator `4(n+1)² - 1` is positive over the reals.
-/
theorem wallis_real_denominator_positive
    (n : Nat) :
    0 <
      4 * ((n : ℝ) + 1) ^ 2 - 1 := by

  have hn :
      0 ≤ (n : ℝ) := by
    positivity

  nlinarith [
    sq_nonneg ((n : ℝ) + 1)
  ]

/--
The real cast of the KT factor is exactly Mathlib's Wallis factor.
-/
theorem realWallisFactor_eq_mathlib
    (n : Nat) :
    realWallisFactor n =
      mathlibWallisFactor n := by

  unfold realWallisFactor
  unfold wallisFactor
  unfold mathlibWallisFactor

  push_cast

  have hLower :
      (2 : ℝ) * n + 1 ≠ 0 :=
    ne_of_gt
      (lower_real_positive n)

  have hUpper :
      (2 : ℝ) * n + 3 ≠ 0 :=
    ne_of_gt
      (upper_real_positive n)

  have hCentral :
      4 * ((n : ℝ) + 1) ^ 2 - 1 ≠ 0 :=
    ne_of_gt
      (wallis_real_denominator_positive n)

  field_simp [
    hLower,
    hUpper,
    hCentral
  ]

  ring

/--
The real cast of the previously derived finite rational product.
-/
noncomputable def realWallisProduct
    (n : Nat) :
    ℝ :=

  (wallisProduct n : ℝ)

/--
The real finite product obeys the same successor recurrence.
-/
@[simp]
theorem realWallisProduct_zero :
    realWallisProduct 0 =
      1 := by

  simp [
    realWallisProduct
  ]

@[simp]
theorem realWallisProduct_succ
    (n : Nat) :
    realWallisProduct (n + 1) =
      realWallisProduct n *
        realWallisFactor n := by

  unfold realWallisProduct
  unfold realWallisFactor

  rw [
    wallisProduct_succ
  ]

  norm_cast

/--
The cast KT product equals Mathlib's finite Wallis product at every
depth.
-/
theorem realWallisProduct_eq_mathlib_W
    (n : Nat) :
    realWallisProduct n =
      Real.Wallis.W n := by

  induction n with

  | zero =>
      simp [
        realWallisProduct,
        Real.Wallis.W
      ]

   | succ n ih =>
      rw [
        realWallisProduct_succ,
        Real.Wallis.W_succ,
        ih,
        realWallisFactor_eq_mathlib
      ]

      unfold mathlibWallisFactor

      simp only [
        div_eq_mul_inv
      ]

      ring

/--
The derived KT Wallis product converges to `π / 2`.
-/
theorem tendsto_realWallisProduct_pi_div_two :
    Tendsto
        realWallisProduct
        atTop
        (𝓝 (Real.pi / 2)) := by

  have hWallis :
      Tendsto
        Real.Wallis.W
        atTop
        (𝓝 (Real.pi / 2)) :=
    Real.Wallis.tendsto_W_nhds_pi_div_two

  apply
    hWallis.congr'

  filter_upwards with n

  symm

  exact
    realWallisProduct_eq_mathlib_W n

/--
Doubling the finite KT Wallis products converges to π.
-/
theorem tendsto_two_mul_realWallisProduct_pi :
    Tendsto
        (fun n =>
          2 * realWallisProduct n)
        atTop
        (𝓝 Real.pi) := by

  have hTwo :
      Tendsto
        (fun _ : Nat => (2 : ℝ))
        atTop
        (𝓝 2) :=
    tendsto_const_nhds

  have hProduct :
      Tendsto
        (fun n =>
          2 * realWallisProduct n)
        atTop
        (𝓝 (2 * (Real.pi / 2))) :=
    hTwo.mul
      tendsto_realWallisProduct_pi_div_two

  convert hProduct using 1;
    ring_nf

/--
The reciprocal circle value is well-defined because π is nonzero.
-/
theorem pi_ne_zero :
    Real.pi ≠ 0 := by

  exact
    ne_of_gt
      Real.pi_pos

/--
The circle constant and its inverse form a reciprocal pair.
-/
theorem inverse_pi_mul_pi :
    Real.pi⁻¹ * Real.pi =
      1 := by

  exact
    inv_mul_cancel₀
      pi_ne_zero

/--
Orientation selects the reciprocal or direct circle value.
-/
noncomputable def orientedCircleValue :
    GlyphForcingOrientation.ForcedOrientation →
      ℝ

  | .forward =>
      Real.pi⁻¹

  | .reverse =>
      Real.pi

/--
The two oriented circle values are reciprocal.
-/
theorem orientedCircleValues_reciprocal :
    orientedCircleValue
        GlyphForcingOrientation.ForcedOrientation.forward
      *
    orientedCircleValue
        GlyphForcingOrientation.ForcedOrientation.reverse =
      1 := by

  exact
    inverse_pi_mul_pi

/--
The symbolic spectrum registers the same reciprocal circle pair.
-/
theorem registered_circle_pair :
    GlyphSpectrum.values[10]? =
        some
          (.inverse .circleConstant)
      ∧
    GlyphSpectrum.values[11]? =
        some
          .circleConstant := by

  exact
    circle_pair_registered

/--
Capstone theorem.

The triadically derived rational Wallis product is pointwise identical
to Mathlib's Wallis product. It therefore converges to `π / 2`, and
doubling the limit produces π. Orientation supplies the reciprocal
pair registered at glyphs 11 and 12.
-/
theorem triadic_wallis_stream_forces_circle_pair :
    Tendsto
        realWallisProduct
        atTop
        (𝓝 (Real.pi / 2))
      ∧
    Tendsto
        (fun n =>
          2 * realWallisProduct n)
        atTop
        (𝓝 Real.pi)
      ∧
    Real.pi⁻¹ * Real.pi =
        1
      ∧
    GlyphSpectrum.values[10]? =
        some
          (.inverse .circleConstant)
      ∧
    GlyphSpectrum.values[11]? =
        some
          .circleConstant := by

  exact
    ⟨
      tendsto_realWallisProduct_pi_div_two,
      tendsto_two_mul_realWallisProduct_pi,
      inverse_pi_mul_pi,
      registered_circle_pair.1,
      registered_circle_pair.2
    ⟩

end GlyphSpectralWallisLimit

#check GlyphSpectralWallisLimit.realWallisFactor
#check GlyphSpectralWallisLimit.mathlibWallisFactor
#check GlyphSpectralWallisLimit.realWallisFactor_eq_mathlib
#check GlyphSpectralWallisLimit.realWallisProduct
#check GlyphSpectralWallisLimit.realWallisProduct_eq_mathlib_W
#check GlyphSpectralWallisLimit.tendsto_realWallisProduct_pi_div_two
#check GlyphSpectralWallisLimit.tendsto_two_mul_realWallisProduct_pi
#check GlyphSpectralWallisLimit.inverse_pi_mul_pi
#check GlyphSpectralWallisLimit.orientedCircleValue
#check GlyphSpectralWallisLimit.triadic_wallis_stream_forces_circle_pair
