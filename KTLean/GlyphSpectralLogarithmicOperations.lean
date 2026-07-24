import KTLean.GlyphSpectralTranscendentalGenerators
import KTLean.GlyphSpectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Differentiation of the Logarithmic Basin

## Formal status

**Level 2 — Reconstruction from the inverse exponential branch.**

No new primitive analytic operation is postulated by the KT substrate in
this module.

The preceding development proves that the triadically generated
factorial stream converges to Euler's exponential generator. Once the
exponential operation is available, its inverse branch is the real
logarithm:

    log (exp x) = x,

and, for positive `x`,

    exp (log x) = x.

The logarithmic basin evaluates this inverse operation at the already
available positive generators

    2, 3, φ,

producing

    log 2, log 3, log φ.

Orientation reversal supplies their reciprocal partners. These six
values are then identified with the registered logarithmic glyph block

    (log 2)⁻¹, log 2,
    (log 3)⁻¹, log 3,
    (log φ)⁻¹, log φ.

The registered glyph table is consulted only after the analytic family
has been reconstructed.
-/

namespace GlyphSpectralLogarithmicBasin

open Filter
open scoped Topology

open GlyphSpectralFibonacci
open GlyphSpectralExponentialKernel
open GlyphSpectralExponentialLimit

/--
The logarithm is a left inverse of the real exponential map.
-/
theorem logarithm_left_inverse_of_exponential
    (x : ℝ) :
    Real.log (Real.exp x) =
      x := by

  exact
    Real.log_exp x

/--
On the positive reals, exponential is a left inverse of logarithm.
-/
theorem exponential_left_inverse_of_logarithm
    {x : ℝ}
    (hx :
      0 < x) :
    Real.exp (Real.log x) =
      x := by

  exact
    Real.exp_log hx

/--
The exponential generator produced by the triadic factorial stream is
returned to unit scale by the logarithmic inverse.
-/
theorem logarithm_of_exponential_generator :
    Real.log (Real.exp 1) =
      1 := by

  exact
    Real.log_exp 1

/--
The golden generator lies strictly above one.
-/
theorem one_lt_phi :
    1 < phi := by

  have hPositive :
      0 < phi :=
    phi_positive

  have hQuadratic :
      phi ^ 2 =
        phi + 1 :=
    phi_quadratic

  nlinarith [
    sq_nonneg (phi - 1)
  ]

/--
The three direct logarithmic values.
-/
noncomputable def logTwo :
    ℝ :=
  Real.log 2

noncomputable def logThree :
    ℝ :=
  Real.log 3

noncomputable def logPhi :
    ℝ :=
  Real.log phi

/--
The logarithm of two is positive.
-/
theorem logTwo_positive :
    0 < logTwo := by

  unfold logTwo

  exact
    Real.log_pos
      (by norm_num)

/--
The logarithm of three is positive.
-/
theorem logThree_positive :
    0 < logThree := by

  unfold logThree

  exact
    Real.log_pos
      (by norm_num)

/--
The logarithm of the golden generator is positive.
-/
theorem logPhi_positive :
    0 < logPhi := by

  unfold logPhi

  exact
    Real.log_pos
      one_lt_phi

/--
The three direct logarithmic generators are positive.
-/
theorem logarithmic_generators_positive :
    0 < logTwo
      ∧
    0 < logThree
      ∧
    0 < logPhi := by

  exact
    ⟨
      logTwo_positive,
      logThree_positive,
      logPhi_positive
    ⟩

/--
The logarithm of two is nonzero.
-/
theorem logTwo_ne_zero :
    logTwo ≠ 0 := by

  exact
    ne_of_gt
      logTwo_positive

/--
The logarithm of three is nonzero.
-/
theorem logThree_ne_zero :
    logThree ≠ 0 := by

  exact
    ne_of_gt
      logThree_positive

/--
The logarithm of the golden generator is nonzero.
-/
theorem logPhi_ne_zero :
    logPhi ≠ 0 := by

  exact
    ne_of_gt
      logPhi_positive

/--
The three reciprocal logarithmic values.
-/
noncomputable def inverseLogTwo :
    ℝ :=
  logTwo⁻¹

noncomputable def inverseLogThree :
    ℝ :=
  logThree⁻¹

noncomputable def inverseLogPhi :
    ℝ :=
  logPhi⁻¹

/--
The reciprocal logarithm of two is positive.
-/
theorem inverseLogTwo_positive :
    0 < inverseLogTwo := by

  unfold inverseLogTwo

  exact
    inv_pos.mpr
      logTwo_positive

/--
The reciprocal logarithm of three is positive.
-/
theorem inverseLogThree_positive :
    0 < inverseLogThree := by

  unfold inverseLogThree

  exact
    inv_pos.mpr
      logThree_positive

/--
The reciprocal logarithm of the golden generator is positive.
-/
theorem inverseLogPhi_positive :
    0 < inverseLogPhi := by

  unfold inverseLogPhi

  exact
    inv_pos.mpr
      logPhi_positive

/--
The logarithm-of-two pair is reciprocal.
-/
theorem inverseLogTwo_mul_logTwo :
    inverseLogTwo * logTwo =
      1 := by

  unfold inverseLogTwo

  exact
    inv_mul_cancel₀
      logTwo_ne_zero

/--
The logarithm-of-three pair is reciprocal.
-/
theorem inverseLogThree_mul_logThree :
    inverseLogThree * logThree =
      1 := by

  unfold inverseLogThree

  exact
    inv_mul_cancel₀
      logThree_ne_zero

/--
The golden-logarithm pair is reciprocal.
-/
theorem inverseLogPhi_mul_logPhi :
    inverseLogPhi * logPhi =
      1 := by

  unfold inverseLogPhi

  exact
    inv_mul_cancel₀
      logPhi_ne_zero

/--
The three logarithmic orientation pairs are reciprocal.
-/
theorem logarithmic_pairs_reciprocal :
    inverseLogTwo * logTwo =
        1
      ∧
    inverseLogThree * logThree =
        1
      ∧
    inverseLogPhi * logPhi =
        1 := by

  exact
    ⟨
      inverseLogTwo_mul_logTwo,
      inverseLogThree_mul_logThree,
      inverseLogPhi_mul_logPhi
    ⟩

/--
The canonical symbolic logarithmic block.
-/
def logarithmicBlock :
    List GlyphSpectrum.SpectralValue :=
  [
    .inverse (.logarithmNatural 2),
    .logarithmNatural 2,
    .inverse (.logarithmNatural 3),
    .logarithmNatural 3,
    .inverse .logarithmGoldenRatio,
    .logarithmGoldenRatio
  ]

/--
Glyph positions 19 through 24 are exactly the canonical logarithmic
block.
-/
theorem registered_logarithmic_block :
    (GlyphSpectrum.values.drop 18).take 6 =
      logarithmicBlock := by

  native_decide

/--
The logarithm-of-two orientation pair occupies glyphs 19 and 20.
-/
theorem registered_logTwo_pair :
    GlyphSpectrum.values[18]? =
        some
          (.inverse (.logarithmNatural 2))
      ∧
    GlyphSpectrum.values[19]? =
        some
          (.logarithmNatural 2) := by

  native_decide

/--
The logarithm-of-three orientation pair occupies glyphs 21 and 22.
-/
theorem registered_logThree_pair :
    GlyphSpectrum.values[20]? =
        some
          (.inverse (.logarithmNatural 3))
      ∧
    GlyphSpectrum.values[21]? =
        some
          (.logarithmNatural 3) := by

  native_decide

/--
The golden-logarithm orientation pair occupies glyphs 23 and 24.
-/
theorem registered_logPhi_pair :
    GlyphSpectrum.values[22]? =
        some
          (.inverse .logarithmGoldenRatio)
      ∧
    GlyphSpectrum.values[23]? =
        some
          .logarithmGoldenRatio := by

  native_decide

/--
Capstone theorem.

The triadic factorial stream first reconstructs the exponential
generator. The inverse exponential branch then differentiates into the
positive logarithmic values `log 2`, `log 3`, and `log φ`. Orientation
reversal supplies their reciprocals, and the resulting six-value basin
is exactly the canonical logarithmic glyph block.
-/
theorem logarithmic_basin_emerges :
    Tendsto
      (fun n : Nat =>
        ((orbit n).accumulated : ℝ))
      atTop
      (𝓝 (Real.exp 1))
      ∧
    (∀ x : ℝ,
      Real.log (Real.exp x) =
        x)
      ∧
    (∀ x : ℝ,
      0 < x →
        Real.exp (Real.log x) =
          x)
      ∧
    (
      0 < logTwo
        ∧
      0 < logThree
        ∧
      0 < logPhi
    )
      ∧
    (
      inverseLogTwo * logTwo =
          1
        ∧
      inverseLogThree * logThree =
          1
        ∧
      inverseLogPhi * logPhi =
          1
    )
      ∧
    (GlyphSpectrum.values.drop 18).take 6 =
      logarithmicBlock := by

  refine
    ⟨
      orbit_accumulated_tendsto_exp_one,
      ?_,
      ?_,
      logarithmic_generators_positive,
      logarithmic_pairs_reciprocal,
      registered_logarithmic_block
    ⟩

  · intro x

    exact
      logarithm_left_inverse_of_exponential x

  · intro x hx

    exact
      exponential_left_inverse_of_logarithm hx

end GlyphSpectralLogarithmicBasin

#check GlyphSpectralLogarithmicBasin.logarithm_left_inverse_of_exponential
#check GlyphSpectralLogarithmicBasin.exponential_left_inverse_of_logarithm
#check GlyphSpectralLogarithmicBasin.logarithm_of_exponential_generator
#check GlyphSpectralLogarithmicBasin.one_lt_phi
#check GlyphSpectralLogarithmicBasin.logTwo
#check GlyphSpectralLogarithmicBasin.logThree
#check GlyphSpectralLogarithmicBasin.logPhi
#check GlyphSpectralLogarithmicBasin.logarithmic_generators_positive
#check GlyphSpectralLogarithmicBasin.logarithmic_pairs_reciprocal
#check GlyphSpectralLogarithmicBasin.logarithmicBlock
#check GlyphSpectralLogarithmicBasin.registered_logarithmic_block
#check GlyphSpectralLogarithmicBasin.logarithmic_basin_emerges
