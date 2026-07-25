import KTLean.PhysicalCanonicalStateCount
import Mathlib.Tactic

/-!
# Certified Interval Architecture for the Projected Fine-Structure Constant

## Formal status

**Conditional numerical-certification theorem — exact rational enclosure of
the corrected alpha expression once a canonical projection state and certified
bounds are supplied.**

## Developmental predecessors

* `PhysicalAlphaProjectionCorrection`
* `PhysicalCanonicalStateCount`

The preceding modules establish:

1. the exact symbolic corrected inverse-alpha expression;
2. the obligation for selecting a unique canonical projection-state count;
3. an exact bridge from any canonical-state certification to the projection
   state required by the alpha expression.

This module introduces no decimal approximation as an axiom.

Instead, a certification consists of rational lower and upper bounds together
with Lean proofs that the exact corrected inverse-alpha value lies strictly
between them.

From such a certificate the module proves:

* positivity and admissibility of the corrected inverse;
* the same rational enclosure for the exact symbolic expression;
* positivity and uniqueness of the reciprocal alpha value;
* reciprocal bounds for alpha itself;
* preservation of the canonical state-count provenance.

A later numerical-enclosure module may discharge the rational inequalities
using certified bounds for `n`, `π`, `γ`, `ζ(3)`, and the logarithms.
-/

namespace PhysicalAlphaCertifiedValue

/-
## Canonical alpha state
-/

/--
The exact alpha-projection state supplied by a canonical state-count
certification.
-/
noncomputable def projectionState
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    (certification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion) :
    PhysicalAlphaProjectionCorrection.ProjectionState :=

  PhysicalCanonicalStateCount.alphaProjectionState
    certification

/--
The exact corrected inverse-alpha value associated with the canonical
projection state.
-/
noncomputable def alphaInverseValue
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    (certification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion) :
    ℝ :=

  PhysicalAlphaProjectionCorrection.correctedAlphaInverse
    (projectionState certification)

/--
The exact projected alpha value associated with the canonical projection
state.
-/
noncomputable def alphaValue
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    (certification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion) :
    ℝ :=

  PhysicalAlphaProjectionCorrection.correctedAlpha
    (projectionState certification)

/-
## Rational interval certification
-/

/--
A strict rational enclosure for the corrected inverse-alpha value.

The bounds are rational so that the final numerical claim can be checked
without relying on floating-point evaluation.
-/
structure InverseIntervalCertificate
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    (canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion) where

  lower :
    ℚ

  upper :
    ℚ

  lower_positive :
    0 < lower

  lower_lt_value :
    (lower : ℝ) <
      alphaInverseValue
        canonicalCertification

  value_lt_upper :
    alphaInverseValue
        canonicalCertification <
      (upper : ℝ)

/--
The certified rational interval is nonempty.
-/
theorem certificate_lower_lt_upper
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    certificate.lower <
      certificate.upper := by

  exact_mod_cast
    lt_trans
      certificate.lower_lt_value
      certificate.value_lt_upper

/--
The upper rational bound is positive.
-/
theorem certificate_upper_positive
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    0 <
      certificate.upper := by

  exact
    lt_trans
      certificate.lower_positive
      (certificate_lower_lt_upper certificate)

/-
## Admissibility
-/

/--
A positive rational lower bound proves that the exact corrected inverse is
physically admissible.
-/
theorem certified_inverse_positive
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    0 <
      alphaInverseValue
        canonicalCertification := by

  have hLowerReal :
      (0 : ℝ) <
        (certificate.lower : ℝ) := by

    exact_mod_cast
      certificate.lower_positive

  exact
    lt_trans
      hLowerReal
      certificate.lower_lt_value

/--
The canonical projection state satisfies the alpha module's admissibility
condition.
-/
theorem certified_isAdmissible
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    PhysicalAlphaProjectionCorrection.IsAdmissible
      (projectionState canonicalCertification) := by

  exact
    certified_inverse_positive certificate

/--
The certified inverse-alpha value is nonzero.
-/
theorem certified_inverse_ne_zero
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    alphaInverseValue
        canonicalCertification ≠
      0 := by

  exact
    ne_of_gt
      (certified_inverse_positive certificate)

/-
## Exact symbolic provenance
-/

/--
The certified quantity is still exactly the symbolic four-term corrected
inverse-alpha expression.
-/
theorem certified_inverse_formula
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    (canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion) :
    alphaInverseValue canonicalCertification =
      PhysicalAlphaProjectionCorrection.baseInverse
        +
      1 / (8 * Real.pi)
        -
      GlyphSpectralSpecialFunctionOperations.eulerMascheroni
        /
      (
        PhysicalAlphaProjectionCorrection.baseInverse
          +
        1 / (8 * Real.pi)
          -
        PhysicalAlphaProjectionCorrection.shannonMemoryCost
          (projectionState canonicalCertification)
      )
        +
      GlyphSpectralSpecialFunctionOperations.zetaThree
        /
      (
        PhysicalAlphaProjectionCorrection.baseInverse
          *
        PhysicalAlphaProjectionCorrection.cubicMemoryFactor
      ) := by

  exact
    PhysicalAlphaProjectionCorrection.correctedAlphaInverse_formula
      (projectionState canonicalCertification)

/--
The exact formula with finite structural counts exposed.
-/
theorem certified_inverse_explicit
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    (canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion) :
    alphaInverseValue canonicalCertification =
      137
        +
      1 / (8 * Real.pi)
        -
      GlyphSpectralSpecialFunctionOperations.eulerMascheroni
        /
      (
        137
          +
        1 / (8 * Real.pi)
          -
        (
          Real.log
              (projectionState
                canonicalCertification).stateCount
              /
            (2 * 137)
            +
          Real.log
              (
                Real.log
                  (projectionState
                    canonicalCertification).stateCount
              )
              /
            (42 * 7)
        )
      )
        +
      GlyphSpectralSpecialFunctionOperations.zetaThree
        /
      (137 * 20) := by

  exact
    PhysicalAlphaProjectionCorrection.correctedAlphaInverse_explicit
      (projectionState canonicalCertification)

/-
## Reciprocal alpha certification
-/

/--
The exact projected alpha value is positive.
-/
theorem certified_alpha_positive
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    0 <
      alphaValue
        canonicalCertification := by

  exact
    PhysicalAlphaProjectionCorrection.correctedAlpha_positive
      (projectionState canonicalCertification)
      (certified_isAdmissible certificate)

/--
The exact projected alpha and its exact corrected inverse multiply to one.
-/
theorem certified_alpha_mul_inverse
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    alphaValue canonicalCertification *
        alphaInverseValue canonicalCertification =
      1 := by

  exact
    PhysicalAlphaProjectionCorrection.correctedAlpha_mul_inverse
      (projectionState canonicalCertification)
      (certified_isAdmissible certificate)

/--
The projected alpha is uniquely determined by the certified corrected
inverse.
-/
theorem certified_alpha_unique
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification)
    (candidate : ℝ)
    (hCandidate :
      candidate *
          alphaInverseValue canonicalCertification =
        1) :
    candidate =
      alphaValue canonicalCertification := by

  exact
    PhysicalAlphaProjectionCorrection.correctedAlpha_unique
      (projectionState canonicalCertification)
      (certified_isAdmissible certificate)
      candidate
      hCandidate

/-
## Reciprocal interval
-/

/--
The upper inverse-alpha bound gives the lower alpha bound.
-/
theorem reciprocal_upper_lt_alpha
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    ((certificate.upper : ℝ)⁻¹) <
      alphaValue canonicalCertification := by

  have hUpperReal :
      (0 : ℝ) <
        (certificate.upper : ℝ) := by

    exact_mod_cast
      (certificate_upper_positive certificate)

  change
    ((certificate.upper : ℝ)⁻¹) <
      (alphaInverseValue canonicalCertification)⁻¹

  exact
    (
      inv_lt_inv₀
        hUpperReal
        (certified_inverse_positive certificate)
    ).2
      certificate.value_lt_upper

/--
The lower inverse-alpha bound gives the upper alpha bound.
-/
theorem alpha_lt_reciprocal_lower
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    alphaValue canonicalCertification <
      ((certificate.lower : ℝ)⁻¹) := by

  have hLowerReal :
      (0 : ℝ) <
        (certificate.lower : ℝ) := by

    exact_mod_cast
      certificate.lower_positive

  change
    (alphaInverseValue canonicalCertification)⁻¹ <
      ((certificate.lower : ℝ)⁻¹)

  exact
    (
      inv_lt_inv₀
        (certified_inverse_positive certificate)
        hLowerReal
    ).2
      certificate.lower_lt_value

/--
The exact projected alpha lies in the reciprocal rational interval.
-/
theorem certified_alpha_interval
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    ((certificate.upper : ℝ)⁻¹) <
        alphaValue canonicalCertification
      ∧
    alphaValue canonicalCertification <
      ((certificate.lower : ℝ)⁻¹) := by

  exact
    ⟨
      reciprocal_upper_lt_alpha certificate,
      alpha_lt_reciprocal_lower certificate
    ⟩

/-
## Canonical-state provenance
-/

/--
The numerical certification uses exactly the canonical state count selected
upstream.
-/
theorem certified_projection_state_count
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    (canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion) :
    (projectionState canonicalCertification).stateCount =
      PhysicalCanonicalStateCount.canonicalStateCount
        canonicalCertification := by

  rfl

/--
The certified projection state has count greater than one.
-/
theorem certified_projection_state_gt_one
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    (canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion) :
    1 <
      (projectionState canonicalCertification).stateCount := by

  exact
    PhysicalCanonicalStateCount.alphaProjectionState_gt_one
      canonicalCertification

/-
## Capstone
-/

/--
Capstone theorem.

A canonical-state certification together with a strict positive rational
enclosure proves:

* the exact inverse-alpha expression is positive and admissible;
* the exact inverse lies between the certified rational bounds;
* the exact alpha reciprocal is positive and unique;
* alpha lies between the reciprocal bounds;
* the state count used is exactly the canonical upstream count.

The theorem introduces no floating-point value and makes no unconditional
claim about the decimal expansion of alpha.
-/
theorem certified_projected_alpha
    {context :
      PhysicalCanonicalStateCount.Context}
    {criterion :
      PhysicalCanonicalStateCount.Criterion}
    {canonicalCertification :
      PhysicalCanonicalStateCount.Certification
        context
        criterion}
    (certificate :
      InverseIntervalCertificate
        canonicalCertification) :
    (
      (certificate.lower : ℝ) <
          alphaInverseValue canonicalCertification
        ∧
      alphaInverseValue canonicalCertification <
        (certificate.upper : ℝ)
    )
      ∧
    PhysicalAlphaProjectionCorrection.IsAdmissible
      (projectionState canonicalCertification)
      ∧
    0 <
      alphaValue canonicalCertification
      ∧
    (
      ((certificate.upper : ℝ)⁻¹) <
          alphaValue canonicalCertification
        ∧
      alphaValue canonicalCertification <
        ((certificate.lower : ℝ)⁻¹)
    )
      ∧
    (projectionState canonicalCertification).stateCount =
      PhysicalCanonicalStateCount.canonicalStateCount
        canonicalCertification := by

  exact
    ⟨
      ⟨
        certificate.lower_lt_value,
        certificate.value_lt_upper
      ⟩,
      certified_isAdmissible certificate,
      certified_alpha_positive certificate,
      certified_alpha_interval certificate,
      rfl
    ⟩

end PhysicalAlphaCertifiedValue

#check PhysicalAlphaCertifiedValue.projectionState
#check PhysicalAlphaCertifiedValue.alphaInverseValue
#check PhysicalAlphaCertifiedValue.alphaValue
#check PhysicalAlphaCertifiedValue.InverseIntervalCertificate
#check PhysicalAlphaCertifiedValue.certificate_lower_lt_upper
#check PhysicalAlphaCertifiedValue.certified_inverse_positive
#check PhysicalAlphaCertifiedValue.certified_isAdmissible
#check PhysicalAlphaCertifiedValue.certified_inverse_formula
#check PhysicalAlphaCertifiedValue.certified_inverse_explicit
#check PhysicalAlphaCertifiedValue.certified_alpha_positive
#check PhysicalAlphaCertifiedValue.certified_alpha_unique
#check PhysicalAlphaCertifiedValue.certified_alpha_interval
#check PhysicalAlphaCertifiedValue.certified_projected_alpha
