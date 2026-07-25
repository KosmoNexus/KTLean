import KTLean.PhysicalTokenInterface
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Emergence of the Reduced Action Token

## Formal status

**Level 1 — Structural emergence of the reduced action token,
conditional on one positive full-cycle action quantum.**

## Developmental predecessor

`PhysicalTokenInterface`

The OMBT chain has already produced:

* 168 monads;
* projected locality;
* visible and escrow information phases;
* directed temporal events;
* reversible monad dynamics.

These structures carry phase and event orientation, but they do not yet
possess a physical action scale.

A complete phase cycle has angular measure

    2π.

If one positive action quantum `h` is assigned to one complete cycle,
then the action carried per radian is forced uniquely:

    ℏ = h / (2π).

Equivalently:

    2πℏ = h.

This module derives that reduced action scale, proves its positivity and
uniqueness, and mints an `ℏ`-role physical token over every OMBT monad.

No measured SI value is inserted. The remaining physical obligation is
to derive the full-cycle action quantum itself from deeper tokenization
and projection structure.
-/

namespace PhysicalActionToken

/-
## Full-cycle phase geometry
-/

/--
The angular measure of one complete phase cycle.
-/
noncomputable def fullPhaseCycle :
    ℝ :=
  2 * Real.pi

/--
A complete phase cycle has positive angular measure.
-/
theorem fullPhaseCycle_positive :
    0 < fullPhaseCycle := by

  unfold fullPhaseCycle

  positivity

/--
A complete phase cycle is nonzero.
-/
theorem fullPhaseCycle_ne_zero :
    fullPhaseCycle ≠ 0 := by

  exact
    ne_of_gt fullPhaseCycle_positive

/-
## Action normalization
-/

/--
A physical action normalization supplies one positive action quantum for
a complete phase cycle.

This quantity corresponds to `h`, not yet to `ℏ`.
-/
structure Normalization where

  planckAction :
    ℝ

  planckAction_positive :
    0 < planckAction

/--
The reduced action magnitude forced by one full-cycle action quantum.

    ℏ = h / (2π).
-/
noncomputable def hbarMagnitude
    (normalization : Normalization) :
    ℝ :=

  normalization.planckAction /
    fullPhaseCycle

/--
The reduced action magnitude is positive.
-/
theorem hbarMagnitude_positive
    (normalization : Normalization) :
    0 <
      hbarMagnitude normalization := by

  unfold hbarMagnitude

  exact
    div_pos
      normalization.planckAction_positive
      fullPhaseCycle_positive

/--
The reduced action magnitude is nonzero.
-/
theorem hbarMagnitude_ne_zero
    (normalization : Normalization) :
    hbarMagnitude normalization ≠
      0 := by

  exact
    ne_of_gt
      (hbarMagnitude_positive normalization)

/--
Multiplying the reduced action scale by one complete phase cycle recovers
the full Planck action quantum.

    2πℏ = h.
-/
theorem fullPhaseCycle_mul_hbar
    (normalization : Normalization) :
    fullPhaseCycle *
        hbarMagnitude normalization =
      normalization.planckAction := by

  unfold hbarMagnitude

  field_simp [fullPhaseCycle_ne_zero]

/--
The conventional relation between the full and reduced Planck constants.

    h = 2πℏ.
-/
theorem planckAction_eq_two_pi_mul_hbar
    (normalization : Normalization) :
    normalization.planckAction =
      2 * Real.pi *
        hbarMagnitude normalization := by

  exact
    (fullPhaseCycle_mul_hbar normalization).symm

/--
The reduced action scale is the unique real value whose multiplication
by one full phase cycle gives the supplied Planck action quantum.
-/
theorem hbarMagnitude_unique
    (normalization : Normalization)
    (candidate : ℝ)
    (hCandidate :
      fullPhaseCycle * candidate =
        normalization.planckAction) :
    candidate =
      hbarMagnitude normalization := by

  apply
    (mul_left_cancel₀ fullPhaseCycle_ne_zero)

  calc
    fullPhaseCycle * candidate =
        normalization.planckAction :=
      hCandidate

    _ =
        fullPhaseCycle *
          hbarMagnitude normalization :=
      (fullPhaseCycle_mul_hbar normalization).symm

/--
There exists exactly one reduced action magnitude compatible with the
full-cycle action normalization.
-/
theorem existsUnique_hbarMagnitude
    (normalization : Normalization) :
    ∃! reducedAction : ℝ,
      0 < reducedAction
        ∧
      fullPhaseCycle * reducedAction =
        normalization.planckAction := by

  refine
    ⟨
      hbarMagnitude normalization,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        hbarMagnitude_positive normalization,
        fullPhaseCycle_mul_hbar normalization
      ⟩

  · intro candidate hCandidate

    exact
      hbarMagnitude_unique
        normalization
        candidate
        hCandidate.2

/-
## Action carried by phase
-/

/--
Convert a dimensionless phase displacement into physical action using
the reduced action scale.

    S(θ) = ℏ θ.
-/
noncomputable def phaseAction
    (normalization : Normalization)
    (phase : ℝ) :
    ℝ :=

  hbarMagnitude normalization *
    phase

/--
Zero phase displacement carries zero action.
-/
@[simp]
theorem phaseAction_zero
    (normalization : Normalization) :
    phaseAction normalization 0 =
      0 := by

  simp [phaseAction]

/--
One radian of phase carries exactly one reduced action quantum.
-/
@[simp]
theorem phaseAction_one
    (normalization : Normalization) :
    phaseAction normalization 1 =
      hbarMagnitude normalization := by

  simp [phaseAction]

/--
One complete phase cycle carries the full Planck action quantum.
-/
theorem phaseAction_full_cycle
    (normalization : Normalization) :
    phaseAction normalization fullPhaseCycle =
      normalization.planckAction := by

  unfold phaseAction

  rw [mul_comm]

  exact
    fullPhaseCycle_mul_hbar normalization

/--
Phase action is additive.
-/
theorem phaseAction_add
    (normalization : Normalization)
    (left right : ℝ) :
    phaseAction normalization (left + right) =
      phaseAction normalization left +
        phaseAction normalization right := by

  unfold phaseAction

  ring

/--
Phase reversal reverses the sign of physical action.
-/
theorem phaseAction_neg
    (normalization : Normalization)
    (phase : ℝ) :
    phaseAction normalization (-phase) =
      -phaseAction normalization phase := by

  unfold phaseAction

  ring

/-
## Minting the reduced action token
-/

/--
Mint the reduced action token over one OMBT monad.
-/
noncomputable def hbarToken
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    PhysicalTokenInterface.Token :=

  PhysicalTokenInterface.mint
    source
    .reducedAction
    (hbarMagnitude normalization)
    (hbarMagnitude_positive normalization)

/--
The reduced action token retains its source monad.
-/
@[simp]
theorem hbarToken_source
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (hbarToken normalization source).source =
      source := by

  rfl

/--
The reduced action token carries the reduced-action role.
-/
@[simp]
theorem hbarToken_role
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (hbarToken normalization source).role =
      .reducedAction := by

  rfl

/--
The reduced action token carries the magnitude `h / 2π`.
-/
@[simp]
theorem hbarToken_magnitude
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (hbarToken normalization source).magnitude =
      hbarMagnitude normalization := by

  rfl

/--
The reduced action token has the action signature

    M L² T⁻¹.
-/
theorem hbarToken_signature
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (hbarToken normalization source).signature =
      PhysicalTokenInterface.actionSignature := by

  exact
    PhysicalTokenInterface.hbarToken_has_action_signature
      (by rfl)

/--
The reduced action token is positive.
-/
theorem hbarToken_positive
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    0 <
      (hbarToken normalization source).magnitude := by

  exact
    (hbarToken normalization source).magnitude_positive

/-
## Uniformity over the monad space
-/

/--
All monads minted under one action normalization receive the same reduced
action magnitude.

The monad supplies provenance; the normalization supplies the universal
conversion scale.
-/
theorem hbarMagnitude_independent_of_monad
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (hbarToken normalization left).magnitude =
      (hbarToken normalization right).magnitude := by

  rfl

/--
Monad temporal reversal preserves the universal reduced action
magnitude.
-/
theorem reverseTemporal_preserves_hbarMagnitude
    (normalization : Normalization)
    (monad : KTMonad.Monad) :
    (
      hbarToken
        normalization
        (OMBTMonadDynamics.reverseTemporal monad)
    ).magnitude =
      (hbarToken normalization monad).magnitude := by

  rfl

/--
Monad phase exchange preserves the universal reduced action magnitude.
-/
theorem exchangePhase_preserves_hbarMagnitude
    (normalization : Normalization)
    (monad : KTMonad.Monad) :
    (
      hbarToken
        normalization
        (OMBTMonadDynamics.exchangePhase monad)
    ).magnitude =
      (hbarToken normalization monad).magnitude := by

  rfl

/-
## Capstone
-/

/--
Capstone theorem.

A positive full-cycle action quantum and the already-derived circular
phase geometry force one unique positive reduced action scale:

    ℏ = h / 2π,
    2πℏ = h.

That scale converts dimensionless phase displacement into physical
action, is additive under phase composition, and mints a positive
reduced-action token over every one of the 168 OMBT monads.

The token retains monadic provenance and carries the required action
signature `M L² T⁻¹`. Its magnitude is universal across temporal
reversal and visible/escrow phase exchange.

This proves the structural emergence of the `ℏ` token. It does not yet
derive the measured magnitude of `h` from the trit substrate.
-/
theorem physical_action_token_emerges
    (normalization : Normalization) :
    (
      ∃! reducedAction : ℝ,
        0 < reducedAction
          ∧
        fullPhaseCycle * reducedAction =
          normalization.planckAction
    )
      ∧
    hbarMagnitude normalization =
      normalization.planckAction /
        (2 * Real.pi)
      ∧
    (
      ∀ source : KTMonad.Monad,
        (hbarToken normalization source).source =
            source
          ∧
        (hbarToken normalization source).role =
            .reducedAction
          ∧
        (hbarToken normalization source).signature =
            PhysicalTokenInterface.actionSignature
          ∧
        0 <
          (hbarToken normalization source).magnitude
    )
      ∧
    (
      ∀ phase : ℝ,
        phaseAction normalization (-phase) =
          -phaseAction normalization phase
    )
      ∧
    (
      ∀ left right : ℝ,
        phaseAction normalization (left + right) =
          phaseAction normalization left +
            phaseAction normalization right
    )
      ∧
    phaseAction normalization fullPhaseCycle =
      normalization.planckAction := by

  refine
    ⟨
      existsUnique_hbarMagnitude normalization,
      rfl,
      ?_,
      phaseAction_neg normalization,
      phaseAction_add normalization,
      phaseAction_full_cycle normalization
    ⟩

  intro source

  exact
    ⟨
      hbarToken_source normalization source,
      hbarToken_role normalization source,
      hbarToken_signature normalization source,
      hbarToken_positive normalization source
    ⟩

end PhysicalActionToken

#check PhysicalActionToken.fullPhaseCycle
#check PhysicalActionToken.Normalization
#check PhysicalActionToken.hbarMagnitude
#check PhysicalActionToken.hbarMagnitude_positive
#check PhysicalActionToken.fullPhaseCycle_mul_hbar
#check PhysicalActionToken.planckAction_eq_two_pi_mul_hbar
#check PhysicalActionToken.existsUnique_hbarMagnitude
#check PhysicalActionToken.phaseAction
#check PhysicalActionToken.phaseAction_full_cycle
#check PhysicalActionToken.hbarToken
#check PhysicalActionToken.hbarToken_signature
#check PhysicalActionToken.hbarMagnitude_independent_of_monad
#check PhysicalActionToken.physical_action_token_emerges
