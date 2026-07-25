import KTLean.PhysicalCausalToken
import Mathlib.Tactic

/-!
# Emergence of the Gravitational Coupling Token

## Formal status

**Level 1 — Structural emergence of the gravitational coupling token,
conditional on one positive projected source scale and one positive
projected geometric-response scale.**

## Developmental predecessor

`PhysicalCausalToken`

The OMBT chain has already produced:

* projected locality;
* directed events;
* reversible monad dynamics;
* the reduced action token `ℏ`;
* the causal conversion token `c`.

The gravitational token `G` relates source content to the response of the
projected arena.

Once projection supplies:

* one positive source-content scale `Σ`;
* one positive geometric-response scale `Γ`;

the coupling magnitude is uniquely forced:

    G = Γ / Σ.

Equivalently:

    G Σ = Γ.

This module proves positivity, uniqueness, source-response conversion,
monadic provenance, and the dimensional signature

    L³ M⁻¹ T⁻².

No measured SI magnitude is inserted. The deeper obligation remains to
derive the primitive source and geometric-response scales from the full
OMBT arena-generation mechanism.
-/

namespace PhysicalGravityToken

/-
## Source-response normalization
-/

/--
A gravitational normalization supplies one positive source-content scale
and one positive projected geometric-response scale.
-/
structure Normalization where

  sourceScale :
    ℝ

  geometricResponse :
    ℝ

  sourceScale_positive :
    0 < sourceScale

  geometricResponse_positive :
    0 < geometricResponse

/--
The source scale is nonzero.
-/
theorem sourceScale_ne_zero
    (normalization : Normalization) :
    normalization.sourceScale ≠ 0 := by

  exact
    ne_of_gt normalization.sourceScale_positive

/--
The geometric-response scale is nonzero.
-/
theorem geometricResponse_ne_zero
    (normalization : Normalization) :
    normalization.geometricResponse ≠ 0 := by

  exact
    ne_of_gt normalization.geometricResponse_positive

/-
## Gravitational coupling magnitude
-/

/--
The gravitational coupling magnitude forced by the normalized
source-response pair.

    G = Γ / Σ.
-/
noncomputable def gravityMagnitude
    (normalization : Normalization) :
    ℝ :=

  normalization.geometricResponse /
    normalization.sourceScale

/--
The gravitational coupling magnitude is positive.
-/
theorem gravityMagnitude_positive
    (normalization : Normalization) :
    0 < gravityMagnitude normalization := by

  unfold gravityMagnitude

  exact
    div_pos
      normalization.geometricResponse_positive
      normalization.sourceScale_positive

/--
The gravitational coupling magnitude is nonzero.
-/
theorem gravityMagnitude_ne_zero
    (normalization : Normalization) :
    gravityMagnitude normalization ≠ 0 := by

  exact
    ne_of_gt
      (gravityMagnitude_positive normalization)

/--
Multiplying the gravitational coupling by the source scale recovers the
projected geometric response.

    G Σ = Γ.
-/
theorem gravityMagnitude_mul_sourceScale
    (normalization : Normalization) :
    gravityMagnitude normalization *
        normalization.sourceScale =
      normalization.geometricResponse := by

  unfold gravityMagnitude

  field_simp [
    sourceScale_ne_zero normalization
  ]

/--
The projected geometric response equals the coupling magnitude times the
source scale.

    Γ = G Σ.
-/
theorem geometricResponse_eq_gravity_mul_source
    (normalization : Normalization) :
    normalization.geometricResponse =
      gravityMagnitude normalization *
        normalization.sourceScale := by

  exact
    (gravityMagnitude_mul_sourceScale normalization).symm

/--
The gravitational coupling is the unique value converting the normalized
source scale into the normalized projected geometric response.
-/
theorem gravityMagnitude_unique
    (normalization : Normalization)
    (candidate : ℝ)
    (hCandidate :
      candidate *
          normalization.sourceScale =
        normalization.geometricResponse) :
    candidate =
      gravityMagnitude normalization := by

  apply
    mul_right_cancel₀
      (sourceScale_ne_zero normalization)

  calc
    candidate *
        normalization.sourceScale =
      normalization.geometricResponse :=
        hCandidate

    _ =
      gravityMagnitude normalization *
        normalization.sourceScale :=
        (gravityMagnitude_mul_sourceScale normalization).symm

/--
There exists exactly one positive gravitational coupling compatible with
the normalized source-response relation.
-/
theorem existsUnique_gravityMagnitude
    (normalization : Normalization) :
    ∃! coupling : ℝ,
      0 < coupling
        ∧
      coupling *
          normalization.sourceScale =
        normalization.geometricResponse := by

  refine
    ⟨
      gravityMagnitude normalization,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        gravityMagnitude_positive normalization,
        gravityMagnitude_mul_sourceScale normalization
      ⟩

  · intro candidate hCandidate

    exact
      gravityMagnitude_unique
        normalization
        candidate
        hCandidate.2

/-
## Source-response conversion
-/

/--
Convert source content into projected geometric response.

    Γ(Σ) = G Σ.
-/
noncomputable def sourceToGeometry
    (normalization : Normalization)
    (source : ℝ) :
    ℝ :=

  gravityMagnitude normalization *
    source

/--
Zero source content produces zero response in the linear token
interface.
-/
@[simp]
theorem sourceToGeometry_zero
    (normalization : Normalization) :
    sourceToGeometry normalization 0 =
      0 := by

  simp [sourceToGeometry]

/--
The normalized source scale produces the normalized geometric response.
-/
theorem sourceToGeometry_normalizedSource
    (normalization : Normalization) :
    sourceToGeometry
        normalization
        normalization.sourceScale =
      normalization.geometricResponse := by

  exact
    gravityMagnitude_mul_sourceScale normalization

/--
Source-to-geometry conversion is additive.
-/
theorem sourceToGeometry_add
    (normalization : Normalization)
    (left right : ℝ) :
    sourceToGeometry normalization (left + right) =
      sourceToGeometry normalization left +
        sourceToGeometry normalization right := by

  unfold sourceToGeometry

  ring

/--
Reversing the sign of source content reverses the signed response.
-/
theorem sourceToGeometry_neg
    (normalization : Normalization)
    (source : ℝ) :
    sourceToGeometry normalization (-source) =
      -sourceToGeometry normalization source := by

  unfold sourceToGeometry

  ring

/--
Recover source content from a projected geometric response.
-/
noncomputable def geometryToSource
    (normalization : Normalization)
    (response : ℝ) :
    ℝ :=

  response /
    gravityMagnitude normalization

/--
Converting source content to geometric response and back recovers the
source.
-/
theorem geometryToSource_sourceToGeometry
    (normalization : Normalization)
    (source : ℝ) :
    geometryToSource
        normalization
        (sourceToGeometry normalization source) =
      source := by

  unfold geometryToSource
  unfold sourceToGeometry

  field_simp [
    gravityMagnitude_ne_zero normalization
  ]

/--
Converting geometric response to source content and back recovers the
response.
-/
theorem sourceToGeometry_geometryToSource
    (normalization : Normalization)
    (response : ℝ) :
    sourceToGeometry
        normalization
        (geometryToSource normalization response) =
      response := by

  unfold sourceToGeometry
  unfold geometryToSource

  field_simp [
    gravityMagnitude_ne_zero normalization
  ]

/-
## Minting the gravitational token
-/

/--
Mint the gravitational coupling token over one OMBT monad.
-/
noncomputable def gravityToken
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    PhysicalTokenInterface.Token :=

  PhysicalTokenInterface.mint
    source
    .gravitationalCoupling
    (gravityMagnitude normalization)
    (gravityMagnitude_positive normalization)

/--
The gravitational token retains its source monad.
-/
@[simp]
theorem gravityToken_source
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (gravityToken normalization source).source =
      source := by

  rfl

/--
The gravitational token carries the gravitational-coupling role.
-/
@[simp]
theorem gravityToken_role
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (gravityToken normalization source).role =
      .gravitationalCoupling := by

  rfl

/--
The gravitational token carries the normalized coupling magnitude.
-/
@[simp]
theorem gravityToken_magnitude
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (gravityToken normalization source).magnitude =
      gravityMagnitude normalization := by

  rfl

/--
The gravitational token has dimensional signature

    L³ M⁻¹ T⁻².
-/
theorem gravityToken_signature
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (gravityToken normalization source).signature =
      PhysicalTokenInterface.gravitySignature := by

  exact
    PhysicalTokenInterface.gravityToken_has_gravity_signature
      (by rfl)

/--
The gravitational token has positive magnitude.
-/
theorem gravityToken_positive
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    0 <
      (gravityToken normalization source).magnitude := by

  exact
    (gravityToken normalization source).magnitude_positive

/-
## Universality across monads
-/

/--
All monads under one gravitational normalization carry the same coupling
magnitude.
-/
theorem gravityMagnitude_independent_of_monad
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (gravityToken normalization left).magnitude =
      (gravityToken normalization right).magnitude := by

  rfl

/--
Temporal reversal preserves the gravitational magnitude.
-/
theorem reverseTemporal_preserves_gravityMagnitude
    (normalization : Normalization)
    (monad : KTMonad.Monad) :
    (
      gravityToken
        normalization
        (OMBTMonadDynamics.reverseTemporal monad)
    ).magnitude =
      (gravityToken normalization monad).magnitude := by

  rfl

/--
Visible/escrow phase exchange preserves the gravitational magnitude.
-/
theorem exchangePhase_preserves_gravityMagnitude
    (normalization : Normalization)
    (monad : KTMonad.Monad) :
    (
      gravityToken
        normalization
        (OMBTMonadDynamics.exchangePhase monad)
    ).magnitude =
      (gravityToken normalization monad).magnitude := by

  rfl

/-
## Developmental ordering
-/

/--
Projected locality, directed events, action, and causal conversion all
precede gravitational coupling.
-/
theorem action_and_causality_precede_gravity :
    Fintype.card KTMonad.Monad =
        168
      ∧
    OMBTLocalityGeneration.ombtVisibleProjection.HasResidue
      ∧
    OMBTDirectedEvent.IsMoving
      OMBTDirectedEvent.movingProjectedToken
      ∧
    PhysicalTokenInterface.expectedSignature
        .reducedAction =
      PhysicalTokenInterface.actionSignature
      ∧
    PhysicalTokenInterface.expectedSignature
        .causalConversion =
      PhysicalTokenInterface.causalSignature := by

  exact
    ⟨
      OMBTMonadEmergence.existing_monad_card_from_ombt,
      OMBTLocalityGeneration.ombt_visible_projection_has_residue,
      OMBTDirectedEvent.movingProjectedToken_isMoving,
      rfl,
      rfl
    ⟩

/-
## Capstone
-/

/--
Capstone theorem.

A positive projected source scale and a positive projected
geometric-response scale force one unique positive coupling:

    G = Γ / Σ,
    G Σ = Γ.

The token converts source content into projected geometric response,
supports inverse conversion, and is additive under source composition.

Over every OMBT monad, the token retains monadic provenance and carries
the required gravitational signature `L³ M⁻¹ T⁻²`. Its magnitude is
universal across temporal reversal and visible/escrow phase exchange.

This proves structural emergence of the `G` token. It does not yet derive
the measured magnitude of `G`, nor the primitive source-response scales
from the full arena-generation mechanism.
-/
theorem physical_gravity_token_emerges
    (normalization : Normalization) :
    (
      ∃! coupling : ℝ,
        0 < coupling
          ∧
        coupling *
            normalization.sourceScale =
          normalization.geometricResponse
    )
      ∧
    gravityMagnitude normalization =
      normalization.geometricResponse /
        normalization.sourceScale
      ∧
    (
      ∀ source : KTMonad.Monad,
        (gravityToken normalization source).source =
            source
          ∧
        (gravityToken normalization source).role =
            .gravitationalCoupling
          ∧
        (gravityToken normalization source).signature =
            PhysicalTokenInterface.gravitySignature
          ∧
        0 <
          (gravityToken normalization source).magnitude
    )
      ∧
    (
      ∀ source : ℝ,
        geometryToSource
            normalization
            (sourceToGeometry normalization source) =
          source
    )
      ∧
    (
      ∀ response : ℝ,
        sourceToGeometry
            normalization
            (geometryToSource normalization response) =
          response
    )
      ∧
    sourceToGeometry
        normalization
        normalization.sourceScale =
      normalization.geometricResponse := by

  refine
    ⟨
      existsUnique_gravityMagnitude normalization,
      rfl,
      ?_,
      geometryToSource_sourceToGeometry normalization,
      sourceToGeometry_geometryToSource normalization,
      sourceToGeometry_normalizedSource normalization
    ⟩

  intro source

  exact
    ⟨
      gravityToken_source normalization source,
      gravityToken_role normalization source,
      gravityToken_signature normalization source,
      gravityToken_positive normalization source
    ⟩

end PhysicalGravityToken

#check PhysicalGravityToken.Normalization
#check PhysicalGravityToken.gravityMagnitude
#check PhysicalGravityToken.gravityMagnitude_positive
#check PhysicalGravityToken.gravityMagnitude_mul_sourceScale
#check PhysicalGravityToken.existsUnique_gravityMagnitude
#check PhysicalGravityToken.sourceToGeometry
#check PhysicalGravityToken.geometryToSource
#check PhysicalGravityToken.geometryToSource_sourceToGeometry
#check PhysicalGravityToken.sourceToGeometry_geometryToSource
#check PhysicalGravityToken.gravityToken
#check PhysicalGravityToken.gravityToken_signature
#check PhysicalGravityToken.action_and_causality_precede_gravity
#check PhysicalGravityToken.physical_gravity_token_emerges
