import KTLean.PhysicalActionToken
import Mathlib.Tactic

/-!
# Emergence of the Causal Conversion Token

## Formal status

**Level 1 — Structural emergence of the causal conversion token,
conditional on one positive projected spatial interval and one positive
projected temporal interval.**

## Developmental predecessor

`PhysicalActionToken`

The OMBT chain has already produced:

* projected locality;
* directed temporal events;
* reversible monad dynamics;
* a reduced action token connecting phase to action.

The next physical token is the causal conversion scale `c`.

Once projection supplies:

* one positive local spatial interval `Δx`;
* one positive local temporal interval `Δt`;

the conversion magnitude relating them is uniquely forced:

    c = Δx / Δt.

Equivalently:

    c Δt = Δx.

This module proves positivity, uniqueness, interval conversion, monadic
provenance, and the required dimensional signature

    L T⁻¹.

No measured SI value is inserted. The deeper obligation remains to derive
the primitive projected spatial and temporal intervals themselves from
the OMBT arena-generation mechanism.
-/

namespace PhysicalCausalToken

/-
## Projected interval normalization
-/

/--
A causal normalization supplies one positive projected spatial interval
and one positive projected temporal interval.

These are the local interval standards whose ratio determines the causal
conversion token.
-/
structure Normalization where

  spatialInterval :
    ℝ

  temporalInterval :
    ℝ

  spatialInterval_positive :
    0 < spatialInterval

  temporalInterval_positive :
    0 < temporalInterval

/--
The projected temporal interval is nonzero.
-/
theorem temporalInterval_ne_zero
    (normalization : Normalization) :
    normalization.temporalInterval ≠
      0 := by

  exact
    ne_of_gt
      normalization.temporalInterval_positive

/--
The projected spatial interval is nonzero.
-/
theorem spatialInterval_ne_zero
    (normalization : Normalization) :
    normalization.spatialInterval ≠
      0 := by

  exact
    ne_of_gt
      normalization.spatialInterval_positive

/-
## Causal conversion magnitude
-/

/--
The causal conversion magnitude forced by the projected interval pair.

    c = Δx / Δt.
-/
noncomputable def causalMagnitude
    (normalization : Normalization) :
    ℝ :=

  normalization.spatialInterval /
    normalization.temporalInterval

/--
The causal conversion magnitude is positive.
-/
theorem causalMagnitude_positive
    (normalization : Normalization) :
    0 <
      causalMagnitude normalization := by

  unfold causalMagnitude

  exact
    div_pos
      normalization.spatialInterval_positive
      normalization.temporalInterval_positive

/--
The causal conversion magnitude is nonzero.
-/
theorem causalMagnitude_ne_zero
    (normalization : Normalization) :
    causalMagnitude normalization ≠
      0 := by

  exact
    ne_of_gt
      (causalMagnitude_positive normalization)

/--
Multiplying the causal conversion scale by the projected temporal
interval recovers the projected spatial interval.

    c Δt = Δx.
-/
theorem causalMagnitude_mul_temporalInterval
    (normalization : Normalization) :
    causalMagnitude normalization *
        normalization.temporalInterval =
      normalization.spatialInterval := by

  unfold causalMagnitude

  field_simp [
    temporalInterval_ne_zero normalization
  ]

/--
The projected spatial interval equals the causal conversion scale times
the projected temporal interval.

    Δx = c Δt.
-/
theorem spatialInterval_eq_causal_mul_temporal
    (normalization : Normalization) :
    normalization.spatialInterval =
      causalMagnitude normalization *
        normalization.temporalInterval := by

  exact
    (
      causalMagnitude_mul_temporalInterval
        normalization
    ).symm

/--
The causal conversion scale is the unique real value carrying the
projected temporal interval into the projected spatial interval.
-/
theorem causalMagnitude_unique
    (normalization : Normalization)
    (candidate : ℝ)
    (hCandidate :
      candidate *
          normalization.temporalInterval =
        normalization.spatialInterval) :
    candidate =
      causalMagnitude normalization := by

  apply
    mul_right_cancel₀
      (temporalInterval_ne_zero normalization)

  calc
    candidate *
        normalization.temporalInterval =
      normalization.spatialInterval :=
        hCandidate

    _ =
      causalMagnitude normalization *
        normalization.temporalInterval :=
        (
          causalMagnitude_mul_temporalInterval
            normalization
        ).symm

/--
There exists exactly one positive causal conversion magnitude compatible
with the projected interval pair.
-/
theorem existsUnique_causalMagnitude
    (normalization : Normalization) :
    ∃! conversion : ℝ,
      0 < conversion
        ∧
      conversion *
          normalization.temporalInterval =
        normalization.spatialInterval := by

  refine
    ⟨
      causalMagnitude normalization,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        causalMagnitude_positive normalization,
        causalMagnitude_mul_temporalInterval normalization
      ⟩

  · intro candidate hCandidate

    exact
      causalMagnitude_unique
        normalization
        candidate
        hCandidate.2

/-
## Interval conversion
-/

/--
Convert a projected temporal duration into a projected spatial
separation using the causal token.

    x(t) = c t.
-/
noncomputable def temporalToSpatial
    (normalization : Normalization)
    (duration : ℝ) :
    ℝ :=

  causalMagnitude normalization *
    duration

/--
Zero temporal duration converts to zero spatial separation.
-/
@[simp]
theorem temporalToSpatial_zero
    (normalization : Normalization) :
    temporalToSpatial normalization 0 =
      0 := by

  simp [temporalToSpatial]

/--
One normalized projected temporal interval converts to the normalized
projected spatial interval.
-/
theorem temporalToSpatial_normalizedInterval
    (normalization : Normalization) :
    temporalToSpatial
        normalization
        normalization.temporalInterval =
      normalization.spatialInterval := by

  exact
    causalMagnitude_mul_temporalInterval normalization

/--
Temporal-to-spatial conversion is additive.
-/
theorem temporalToSpatial_add
    (normalization : Normalization)
    (left right : ℝ) :
    temporalToSpatial
        normalization
        (left + right) =
      temporalToSpatial normalization left +
        temporalToSpatial normalization right := by

  unfold temporalToSpatial

  ring

/--
Temporal reversal reverses projected spatial orientation.
-/
theorem temporalToSpatial_neg
    (normalization : Normalization)
    (duration : ℝ) :
    temporalToSpatial
        normalization
        (-duration) =
      -temporalToSpatial
        normalization
        duration := by

  unfold temporalToSpatial

  ring

/--
Recover a projected temporal duration from a projected spatial
separation.

    t(x) = x / c.
-/
noncomputable def spatialToTemporal
    (normalization : Normalization)
    (distance : ℝ) :
    ℝ :=

  distance /
    causalMagnitude normalization

/--
Converting temporal duration to spatial separation and back recovers the
original duration.
-/
theorem spatialToTemporal_temporalToSpatial
    (normalization : Normalization)
    (duration : ℝ) :
    spatialToTemporal
        normalization
        (
          temporalToSpatial
            normalization
            duration
        ) =
      duration := by

  unfold spatialToTemporal
  unfold temporalToSpatial

  field_simp [
    causalMagnitude_ne_zero normalization
  ]

/--
Converting spatial separation to temporal duration and back recovers the
original separation.
-/
theorem temporalToSpatial_spatialToTemporal
    (normalization : Normalization)
    (distance : ℝ) :
    temporalToSpatial
        normalization
        (
          spatialToTemporal
            normalization
            distance
        ) =
      distance := by

  unfold temporalToSpatial
  unfold spatialToTemporal

  field_simp [
    causalMagnitude_ne_zero normalization
  ]

/-
## Minting the causal token
-/

/--
Mint the causal conversion token over one OMBT monad.
-/
noncomputable def causalToken
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    PhysicalTokenInterface.Token :=

  PhysicalTokenInterface.mint
    source
    .causalConversion
    (causalMagnitude normalization)
    (causalMagnitude_positive normalization)

/--
The causal token retains its source monad.
-/
@[simp]
theorem causalToken_source
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (causalToken normalization source).source =
      source := by

  rfl

/--
The causal token carries the causal-conversion role.
-/
@[simp]
theorem causalToken_role
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (causalToken normalization source).role =
      .causalConversion := by

  rfl

/--
The causal token carries the magnitude `Δx / Δt`.
-/
@[simp]
theorem causalToken_magnitude
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (causalToken normalization source).magnitude =
      causalMagnitude normalization := by

  rfl

/--
The causal token has dimensional signature

    L T⁻¹.
-/
theorem causalToken_signature
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (causalToken normalization source).signature =
      PhysicalTokenInterface.causalSignature := by

  exact
    PhysicalTokenInterface.causalToken_has_causal_signature
      (by rfl)

/--
The causal token has positive magnitude.
-/
theorem causalToken_positive
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    0 <
      (causalToken normalization source).magnitude := by

  exact
    (causalToken normalization source).magnitude_positive

/-
## Universality across monads
-/

/--
All monads under one causal normalization carry the same causal
conversion magnitude.
-/
theorem causalMagnitude_independent_of_monad
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (causalToken normalization left).magnitude =
      (causalToken normalization right).magnitude := by

  rfl

/--
Temporal reversal of the source monad preserves the causal magnitude.
-/
theorem reverseTemporal_preserves_causalMagnitude
    (normalization : Normalization)
    (monad : KTMonad.Monad) :
    (
      causalToken
        normalization
        (OMBTMonadDynamics.reverseTemporal monad)
    ).magnitude =
      (causalToken normalization monad).magnitude := by

  rfl

/--
Visible/escrow phase exchange preserves the causal magnitude.
-/
theorem exchangePhase_preserves_causalMagnitude
    (normalization : Normalization)
    (monad : KTMonad.Monad) :
    (
      causalToken
        normalization
        (OMBTMonadDynamics.exchangePhase monad)
    ).magnitude =
      (causalToken normalization monad).magnitude := by

  rfl

/-
## Relation to projected event structure
-/

/--
The causal token is introduced only after OMBT locality and directed
events have emerged.
-/
theorem directed_events_precede_causal_token :
    OMBTLocalityGeneration.ombtVisibleProjection.HasResidue
      ∧
    OMBTDirectedEvent.IsMoving
      OMBTDirectedEvent.movingProjectedToken
      ∧
    OMBTDirectedEvent.forwardEvent
        OMBTDirectedEvent.movingProjectedToken
      ≠
    OMBTDirectedEvent.recoveredEvent
        OMBTDirectedEvent.movingProjectedToken := by

  exact
    ⟨
      OMBTLocalityGeneration.ombt_visible_projection_has_residue,
      OMBTDirectedEvent.movingProjectedToken_isMoving,
      OMBTDirectedEvent.concrete_forward_ne_recovered
    ⟩

/-
## Capstone
-/

/--
Capstone theorem.

A positive projected spatial interval and a positive projected temporal
interval force one unique positive causal conversion scale:

    c = Δx / Δt,
    c Δt = Δx.

That token converts temporal succession into spatial separation,
supports inverse conversion, is additive under interval composition, and
changes sign under temporal reversal.

Over every OMBT monad, the token retains monadic provenance and carries
the required causal signature `L T⁻¹`. Its magnitude is universal across
temporal reversal and visible/escrow phase exchange.

This proves the structural emergence of the `c` token. It does not yet
derive the measured magnitude of `c`, nor does it yet derive the primitive
projected intervals from the full arena-generation mechanism.
-/
theorem physical_causal_token_emerges
    (normalization : Normalization) :
    (
      ∃! conversion : ℝ,
        0 < conversion
          ∧
        conversion *
            normalization.temporalInterval =
          normalization.spatialInterval
    )
      ∧
    causalMagnitude normalization =
      normalization.spatialInterval /
        normalization.temporalInterval
      ∧
    (
      ∀ source : KTMonad.Monad,
        (causalToken normalization source).source =
            source
          ∧
        (causalToken normalization source).role =
            .causalConversion
          ∧
        (causalToken normalization source).signature =
            PhysicalTokenInterface.causalSignature
          ∧
        0 <
          (causalToken normalization source).magnitude
    )
      ∧
    (
      ∀ duration : ℝ,
        spatialToTemporal
            normalization
            (
              temporalToSpatial
                normalization
                duration
            ) =
          duration
    )
      ∧
    (
      ∀ distance : ℝ,
        temporalToSpatial
            normalization
            (
              spatialToTemporal
                normalization
                distance
            ) =
          distance
    )
      ∧
    temporalToSpatial
        normalization
        normalization.temporalInterval =
      normalization.spatialInterval := by

  refine
    ⟨
      existsUnique_causalMagnitude normalization,
      rfl,
      ?_,
      spatialToTemporal_temporalToSpatial normalization,
      temporalToSpatial_spatialToTemporal normalization,
      temporalToSpatial_normalizedInterval normalization
    ⟩

  intro source

  exact
    ⟨
      causalToken_source normalization source,
      causalToken_role normalization source,
      causalToken_signature normalization source,
      causalToken_positive normalization source
    ⟩

end PhysicalCausalToken

#check PhysicalCausalToken.Normalization
#check PhysicalCausalToken.causalMagnitude
#check PhysicalCausalToken.causalMagnitude_positive
#check PhysicalCausalToken.causalMagnitude_mul_temporalInterval
#check PhysicalCausalToken.existsUnique_causalMagnitude
#check PhysicalCausalToken.temporalToSpatial
#check PhysicalCausalToken.spatialToTemporal
#check PhysicalCausalToken.spatialToTemporal_temporalToSpatial
#check PhysicalCausalToken.temporalToSpatial_spatialToTemporal
#check PhysicalCausalToken.causalToken
#check PhysicalCausalToken.causalToken_signature
#check PhysicalCausalToken.directed_events_precede_causal_token
#check PhysicalCausalToken.physical_causal_token_emerges
