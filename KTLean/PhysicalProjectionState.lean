import KTLean.PhysicalPlanckScale
import Mathlib.Tactic

/-!
# Dimensionless Projection-State Interface

## Formal status

**Conditional theorem — admissible grammar for constructing a positive
dimensionless projection state from Planck-token ratios.**

## Developmental predecessor

`PhysicalPlanckScale`

The preceding module derives unique positive Planck mass, length, and time
scales from the already established positive `ℏ`, `c`, and `G` token
magnitudes.

The corrected four-dimensional interaction invariant depends on a positive
dimensionless projection-state count `n`. This module does not choose or
derive the canonical value of `n`.

Instead, it formalizes four admissible ways such a dimensionless state may
arise:

    length depth:   L / lP,

    area depth:     A / lP²,

    volume depth:   V / lP³,

    action depth:   S / ℏ.

Each construction:

* is positive when its supplied macroscopic scale is positive;
* has a nonzero denominator;
* is uniquely determined by its defining conversion equation;
* records which projection grammar produced it;
* remains independent of the originating OMBT monad.

The next module, `PhysicalCanonicalStateCount`, must determine which, if
any, of these candidate grammars is selected uniquely by KT projection
geometry.
-/

namespace PhysicalProjectionState

/-
## Projection-state kinds
-/

/--
The four admissible dimensionless projection-state grammars.
-/
inductive Kind where

  | lengthDepth
  | areaDepth
  | volumeDepth
  | actionDepth

  deriving
    DecidableEq,
    Repr

/--
Every projection-state candidate is dimensionless.
-/
def expectedSignature
    (_kind : Kind) :
    PhysicalTokenInterface.Signature :=

  PhysicalTokenInterface.dimensionlessSignature

/-
## Macroscopic normalization data
-/

/--
Positive macroscopic scales from which dimensionless Planck ratios may be
constructed.

No numerical value is fixed here.
-/
structure Normalization where

  lengthScale :
    ℝ

  lengthScale_positive :
    0 < lengthScale

  areaScale :
    ℝ

  areaScale_positive :
    0 < areaScale

  volumeScale :
    ℝ

  volumeScale_positive :
    0 < volumeScale

  actionScale :
    ℝ

  actionScale_positive :
    0 < actionScale

/-
## Candidate dimensionless counts
-/

/--
Length-depth candidate:

    nL = L / lP.
-/
noncomputable def lengthDepth
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    ℝ :=

  normalization.lengthScale /
    PhysicalPlanckScale.planckLength
      planckNormalization

/--
Area-depth candidate:

    nA = A / lP².
-/
noncomputable def areaDepth
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    ℝ :=

  normalization.areaScale /
    PhysicalPlanckScale.planckLength
        planckNormalization ^ 2

/--
Volume-depth candidate:

    nV = V / lP³.
-/
noncomputable def volumeDepth
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    ℝ :=

  normalization.volumeScale /
    PhysicalPlanckScale.planckLength
        planckNormalization ^ 3

/--
Action-depth candidate:

    nS = S / ℏ.
-/
noncomputable def actionDepth
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    ℝ :=

  normalization.actionScale /
    PhysicalPlanckScale.hbar
      planckNormalization

/-
## Denominator nonvanishing
-/

theorem planckLength_sq_ne_zero
    (planckNormalization :
      PhysicalPlanckScale.Normalization) :
    PhysicalPlanckScale.planckLength
        planckNormalization ^ 2 ≠
      0 := by

  exact
    pow_ne_zero
      2
      (
        PhysicalPlanckScale.planckLength_ne_zero
          planckNormalization
      )

theorem planckLength_cube_ne_zero
    (planckNormalization :
      PhysicalPlanckScale.Normalization) :
    PhysicalPlanckScale.planckLength
        planckNormalization ^ 3 ≠
      0 := by

  exact
    pow_ne_zero
      3
      (
        PhysicalPlanckScale.planckLength_ne_zero
          planckNormalization
      )
/-
## Positivity
-/

theorem lengthDepth_positive
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    0 <
      lengthDepth
        planckNormalization
        normalization := by

  unfold lengthDepth

  exact
    div_pos
      normalization.lengthScale_positive
      (
        PhysicalPlanckScale.planckLength_positive
          planckNormalization
      )

theorem areaDepth_positive
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    0 <
      areaDepth
        planckNormalization
        normalization := by

  unfold areaDepth

  exact
    div_pos
      normalization.areaScale_positive
      (
        pow_pos
          (
            PhysicalPlanckScale.planckLength_positive
              planckNormalization
          )
          2
      )

theorem volumeDepth_positive
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    0 <
      volumeDepth
        planckNormalization
        normalization := by

  unfold volumeDepth

  exact
    div_pos
      normalization.volumeScale_positive
      (
        pow_pos
          (
            PhysicalPlanckScale.planckLength_positive
              planckNormalization
          )
          3
      )

theorem actionDepth_positive
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    0 <
      actionDepth
        planckNormalization
        normalization := by

  unfold actionDepth

  exact
    div_pos
      normalization.actionScale_positive
      (
        PhysicalPlanckScale.hbar_positive
          planckNormalization
      )

/-
## Defining conversion equations
-/

/--
Multiplying the length-depth count by one Planck length recovers the
macroscopic length scale.
-/
theorem lengthDepth_mul_planckLength
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    lengthDepth
        planckNormalization
        normalization
      *
      PhysicalPlanckScale.planckLength
        planckNormalization
      =
      normalization.lengthScale := by

  unfold lengthDepth

  exact
    div_mul_cancel₀
      normalization.lengthScale
      (
        PhysicalPlanckScale.planckLength_ne_zero
          planckNormalization
      )

/--
Multiplying the area-depth count by one Planck area recovers the
macroscopic area scale.
-/
theorem areaDepth_mul_planckArea
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    areaDepth
        planckNormalization
        normalization
      *
      PhysicalPlanckScale.planckLength
          planckNormalization ^ 2
      =
      normalization.areaScale := by

  unfold areaDepth

  exact
    div_mul_cancel₀
      normalization.areaScale
      (
        planckLength_sq_ne_zero
          planckNormalization
      )
/--
Multiplying the volume-depth count by one Planck volume recovers the
macroscopic volume scale.
-/
theorem volumeDepth_mul_planckVolume
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    volumeDepth
        planckNormalization
        normalization
      *
      PhysicalPlanckScale.planckLength
          planckNormalization ^ 3
      =
      normalization.volumeScale := by

  unfold volumeDepth

  exact
    div_mul_cancel₀
      normalization.volumeScale
      (
        planckLength_cube_ne_zero
          planckNormalization
      )

/--
Multiplying the action-depth count by one reduced-action token recovers
the supplied action scale.
-/
theorem actionDepth_mul_hbar
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization) :
    actionDepth
        planckNormalization
        normalization
      *
      PhysicalPlanckScale.hbar
        planckNormalization
      =
      normalization.actionScale := by

  unfold actionDepth

  exact
    div_mul_cancel₀
      normalization.actionScale
      (
        PhysicalPlanckScale.hbar_ne_zero
          planckNormalization
      )

/-
## Uniqueness
-/

theorem lengthDepth_unique
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (candidate : ℝ)
    (hCandidate :
      candidate *
          PhysicalPlanckScale.planckLength
            planckNormalization
        =
      normalization.lengthScale) :
    candidate =
      lengthDepth
        planckNormalization
        normalization := by

  apply
    (
      mul_right_cancel₀
        (
          PhysicalPlanckScale.planckLength_ne_zero
            planckNormalization
        )
    )

  calc
    candidate *
        PhysicalPlanckScale.planckLength
          planckNormalization
        =
      normalization.lengthScale :=
        hCandidate

    _ =
      lengthDepth
          planckNormalization
          normalization
        *
      PhysicalPlanckScale.planckLength
        planckNormalization :=
        (
          lengthDepth_mul_planckLength
            planckNormalization
            normalization
        ).symm

theorem areaDepth_unique
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (candidate : ℝ)
    (hCandidate :
      candidate *
          PhysicalPlanckScale.planckLength
              planckNormalization ^ 2
        =
      normalization.areaScale) :
    candidate =
      areaDepth
        planckNormalization
        normalization := by

  apply
    (
      mul_right_cancel₀
        (
          planckLength_sq_ne_zero
            planckNormalization
        )
    )

  calc
    candidate *
        PhysicalPlanckScale.planckLength
            planckNormalization ^ 2
        =
      normalization.areaScale :=
        hCandidate

    _ =
      areaDepth
          planckNormalization
          normalization
        *
      PhysicalPlanckScale.planckLength
          planckNormalization ^ 2 :=
        (
          areaDepth_mul_planckArea
            planckNormalization
            normalization
        ).symm

theorem volumeDepth_unique
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (candidate : ℝ)
    (hCandidate :
      candidate *
          PhysicalPlanckScale.planckLength
              planckNormalization ^ 3
        =
      normalization.volumeScale) :
    candidate =
      volumeDepth
        planckNormalization
        normalization := by

  apply
    (
      mul_right_cancel₀
        (
          planckLength_cube_ne_zero
            planckNormalization
        )
    )

  calc
    candidate *
        PhysicalPlanckScale.planckLength
            planckNormalization ^ 3
        =
      normalization.volumeScale :=
        hCandidate

    _ =
      volumeDepth
          planckNormalization
          normalization
        *
      PhysicalPlanckScale.planckLength
          planckNormalization ^ 3 :=
        (
          volumeDepth_mul_planckVolume
            planckNormalization
            normalization
        ).symm

theorem actionDepth_unique
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (candidate : ℝ)
    (hCandidate :
      candidate *
          PhysicalPlanckScale.hbar
            planckNormalization
        =
      normalization.actionScale) :
    candidate =
      actionDepth
        planckNormalization
        normalization := by

  apply
    (
      mul_right_cancel₀
        (
          PhysicalPlanckScale.hbar_ne_zero
            planckNormalization
        )
    )

  calc
    candidate *
        PhysicalPlanckScale.hbar
          planckNormalization
        =
      normalization.actionScale :=
        hCandidate

    _ =
      actionDepth
          planckNormalization
          normalization
        *
      PhysicalPlanckScale.hbar
        planckNormalization :=
        (
          actionDepth_mul_hbar
            planckNormalization
            normalization
        ).symm

/-
## Unified projection-state object
-/

/--
A dimensionless projection-state candidate.

The state records:

* the grammar used to construct it;
* its positive dimensionless count;
* the originating OMBT monad.

This module does not claim that every candidate is physically canonical.
-/
structure State where

  source :
    KTMonad.Monad

  kind :
    Kind

  stateCount :
    ℝ

  stateCount_positive :
    0 < stateCount

/--
Every projection state carries the dimensionless signature.
-/
def State.signature
    (state : State) :
    PhysicalTokenInterface.Signature :=

  expectedSignature state.kind

/--
Mint a length-depth projection state.
-/
noncomputable def lengthState
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    State where

  source :=
    source

  kind :=
    .lengthDepth

  stateCount :=
    lengthDepth
      planckNormalization
      normalization

  stateCount_positive :=
    lengthDepth_positive
      planckNormalization
      normalization

/--
Mint an area-depth projection state.
-/
noncomputable def areaState
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    State where

  source :=
    source

  kind :=
    .areaDepth

  stateCount :=
    areaDepth
      planckNormalization
      normalization

  stateCount_positive :=
    areaDepth_positive
      planckNormalization
      normalization

/--
Mint a volume-depth projection state.
-/
noncomputable def volumeState
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    State where

  source :=
    source

  kind :=
    .volumeDepth

  stateCount :=
    volumeDepth
      planckNormalization
      normalization

  stateCount_positive :=
    volumeDepth_positive
      planckNormalization
      normalization

/--
Mint an action-depth projection state.
-/
noncomputable def actionState
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    State where

  source :=
    source

  kind :=
    .actionDepth

  stateCount :=
    actionDepth
      planckNormalization
      normalization

  stateCount_positive :=
    actionDepth_positive
      planckNormalization
      normalization

@[simp]
theorem lengthState_source
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      lengthState
        planckNormalization
        normalization
        source
    ).source =
      source := by

  rfl

@[simp]
theorem areaState_source
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      areaState
        planckNormalization
        normalization
        source
    ).source =
      source := by

  rfl

@[simp]
theorem volumeState_source
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      volumeState
        planckNormalization
        normalization
        source
    ).source =
      source := by

  rfl

@[simp]
theorem actionState_source
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      actionState
        planckNormalization
        normalization
        source
    ).source =
      source := by

  rfl

theorem lengthState_signature
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      lengthState
        planckNormalization
        normalization
        source
    ).signature =
      PhysicalTokenInterface.dimensionlessSignature := by

  rfl

theorem areaState_signature
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      areaState
        planckNormalization
        normalization
        source
    ).signature =
      PhysicalTokenInterface.dimensionlessSignature := by

  rfl

theorem volumeState_signature
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      volumeState
        planckNormalization
        normalization
        source
    ).signature =
      PhysicalTokenInterface.dimensionlessSignature := by

  rfl

theorem actionState_signature
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      actionState
        planckNormalization
        normalization
        source
    ).signature =
      PhysicalTokenInterface.dimensionlessSignature := by

  rfl

/-
## Independence from monadic view
-/

theorem lengthState_count_independent_of_monad
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (
      lengthState
        planckNormalization
        normalization
        left
    ).stateCount =
    (
      lengthState
        planckNormalization
        normalization
        right
    ).stateCount := by

  rfl

theorem areaState_count_independent_of_monad
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (
      areaState
        planckNormalization
        normalization
        left
    ).stateCount =
    (
      areaState
        planckNormalization
        normalization
        right
    ).stateCount := by

  rfl

theorem volumeState_count_independent_of_monad
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (
      volumeState
        planckNormalization
        normalization
        left
    ).stateCount =
    (
      volumeState
        planckNormalization
        normalization
        right
    ).stateCount := by

  rfl

theorem actionState_count_independent_of_monad
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (
      actionState
        planckNormalization
        normalization
        left
    ).stateCount =
    (
      actionState
        planckNormalization
        normalization
        right
    ).stateCount := by

  rfl

/-
## Candidate grammar
-/

/--
The four candidate projection states over one monad.

No theorem in this module selects one candidate as canonical.
-/
noncomputable def candidateStates
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    Fin 4 →
      State

  | 0 =>
      lengthState
        planckNormalization
        normalization
        source

  | 1 =>
      areaState
        planckNormalization
        normalization
        source

  | 2 =>
      volumeState
        planckNormalization
        normalization
        source

  | 3 =>
      actionState
        planckNormalization
        normalization
        source

/--
Every candidate projection state is positive, dimensionless, and retains
the supplied monadic provenance.
-/
theorem candidateStates_are_admissible
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad)
    (index : Fin 4) :
    (
      candidateStates
        planckNormalization
        normalization
        source
        index
    ).source =
        source
      ∧
    0 <
      (
        candidateStates
          planckNormalization
          normalization
          source
          index
      ).stateCount
      ∧
    (
      candidateStates
        planckNormalization
        normalization
        source
        index
    ).signature =
      PhysicalTokenInterface.dimensionlessSignature := by

  fin_cases index

  · exact
      ⟨
        rfl,
        lengthDepth_positive
          planckNormalization
          normalization,
        rfl
      ⟩

  · exact
      ⟨
        rfl,
        areaDepth_positive
          planckNormalization
          normalization,
        rfl
      ⟩

  · exact
      ⟨
        rfl,
        volumeDepth_positive
          planckNormalization
          normalization,
        rfl
      ⟩

  · exact
      ⟨
        rfl,
        actionDepth_positive
          planckNormalization
          normalization,
        rfl
      ⟩

/-
## Capstone
-/

/--
Capstone theorem.

The Planck token system admits four positive dimensionless candidate
projection-state grammars:

    L / lP,
    A / lP²,
    V / lP³,
    S / ℏ.

Each candidate is uniquely determined by its conversion equation, retains
its source monad, and carries the dimensionless signature.

This theorem deliberately establishes admissibility but not canonicality.
Selection of the unique physically relevant state count is the open
obligation of `PhysicalCanonicalStateCount`.
-/
theorem physical_projection_state_grammar_emerges
    (planckNormalization :
      PhysicalPlanckScale.Normalization)
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (
      0 <
        lengthDepth
          planckNormalization
          normalization
        ∧
      0 <
        areaDepth
          planckNormalization
          normalization
        ∧
      0 <
        volumeDepth
          planckNormalization
          normalization
        ∧
      0 <
        actionDepth
          planckNormalization
          normalization
    )
      ∧
    (
      ∀ index : Fin 4,
        (
          candidateStates
            planckNormalization
            normalization
            source
            index
        ).source =
            source
          ∧
        0 <
          (
            candidateStates
              planckNormalization
              normalization
              source
              index
          ).stateCount
          ∧
        (
          candidateStates
            planckNormalization
            normalization
            source
            index
        ).signature =
          PhysicalTokenInterface.dimensionlessSignature
    ) := by

  exact
    ⟨
      ⟨
        lengthDepth_positive
          planckNormalization
          normalization,
        areaDepth_positive
          planckNormalization
          normalization,
        volumeDepth_positive
          planckNormalization
          normalization,
        actionDepth_positive
          planckNormalization
          normalization
      ⟩,
      candidateStates_are_admissible
        planckNormalization
        normalization
        source
    ⟩

end PhysicalProjectionState

#check PhysicalProjectionState.Kind
#check PhysicalProjectionState.Normalization
#check PhysicalProjectionState.lengthDepth
#check PhysicalProjectionState.areaDepth
#check PhysicalProjectionState.volumeDepth
#check PhysicalProjectionState.actionDepth
#check PhysicalProjectionState.lengthDepth_unique
#check PhysicalProjectionState.areaDepth_unique
#check PhysicalProjectionState.volumeDepth_unique
#check PhysicalProjectionState.actionDepth_unique
#check PhysicalProjectionState.State
#check PhysicalProjectionState.candidateStates
#check PhysicalProjectionState.candidateStates_are_admissible
#check PhysicalProjectionState.physical_projection_state_grammar_emerges
