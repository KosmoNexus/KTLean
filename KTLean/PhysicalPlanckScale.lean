import KTLean.PhysicalGravityToken
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Emergence of the Planck-Scale Token System

## Formal status

**Conditional theorem — structural composition of the Planck scales from
the already established positive physical-token magnitudes `ℏ`, `c`, and
`G`.**

## Developmental predecessor

`PhysicalGravityToken`

The preceding physical-token modules establish three positive conversion
magnitudes:

* reduced action `ℏ`;
* causal conversion `c`;
* gravitational coupling `G`.

Given those positive token magnitudes, the canonical Planck scales are
forced:

    mP = sqrt (ℏ c / G),

    lP = sqrt (ℏ G / c^3),

    tP = sqrt (ℏ G / c^5).

This module proves:

* positivity;
* exact squared identities;
* uniqueness among positive candidate scales;
* the correct mass, length, and time signatures;
* common monadic provenance;
* invariance under temporal reversal and visible/escrow exchange.

No measured SI magnitude is inserted. The numerical Planck scales remain
conditional on the normalization-dependent magnitudes currently supplied
by the `ℏ`, `c`, and `G` modules.
-/

namespace PhysicalPlanckScale

/-
## Combined normalization
-/

/--
The three normalization structures required to construct a Planck-scale
system.
-/
structure Normalization where

  action :
    PhysicalActionToken.Normalization

  causal :
    PhysicalCausalToken.Normalization

  gravity :
    PhysicalGravityToken.Normalization

/--
The reduced-action magnitude supplied by the action normalization.
-/
noncomputable def hbar
    (normalization : Normalization) :
    ℝ :=

  PhysicalActionToken.hbarMagnitude
    normalization.action

/--
The causal-conversion magnitude supplied by the causal normalization.
-/
noncomputable def causalSpeed
    (normalization : Normalization) :
    ℝ :=

  PhysicalCausalToken.causalMagnitude
    normalization.causal

/--
The gravitational-coupling magnitude supplied by the gravitational
normalization.
-/
noncomputable def gravityCoupling
    (normalization : Normalization) :
    ℝ :=

  PhysicalGravityToken.gravityMagnitude
    normalization.gravity

theorem hbar_positive
    (normalization : Normalization) :
    0 < hbar normalization := by

  exact
    PhysicalActionToken.hbarMagnitude_positive
      normalization.action

theorem causalSpeed_positive
    (normalization : Normalization) :
    0 < causalSpeed normalization := by

  exact
    PhysicalCausalToken.causalMagnitude_positive
      normalization.causal

theorem gravityCoupling_positive
    (normalization : Normalization) :
    0 < gravityCoupling normalization := by

  exact
    PhysicalGravityToken.gravityMagnitude_positive
      normalization.gravity

theorem hbar_ne_zero
    (normalization : Normalization) :
    hbar normalization ≠ 0 := by

  exact
    ne_of_gt
      (hbar_positive normalization)

theorem causalSpeed_ne_zero
    (normalization : Normalization) :
    causalSpeed normalization ≠ 0 := by

  exact
    ne_of_gt
      (causalSpeed_positive normalization)

theorem gravityCoupling_ne_zero
    (normalization : Normalization) :
    gravityCoupling normalization ≠ 0 := by

  exact
    ne_of_gt
      (gravityCoupling_positive normalization)

/-
## Planck radicands
-/

/--
The squared Planck-mass magnitude.

    mP² = ℏ c / G.
-/
noncomputable def massRadicand
    (normalization : Normalization) :
    ℝ :=

  hbar normalization *
      causalSpeed normalization
    /
      gravityCoupling normalization

/--
The squared Planck-length magnitude.

    lP² = ℏ G / c³.
-/
noncomputable def lengthRadicand
    (normalization : Normalization) :
    ℝ :=

  hbar normalization *
      gravityCoupling normalization
    /
      causalSpeed normalization ^ 3

/--
The squared Planck-time magnitude.

    tP² = ℏ G / c⁵.
-/
noncomputable def timeRadicand
    (normalization : Normalization) :
    ℝ :=

  hbar normalization *
      gravityCoupling normalization
    /
      causalSpeed normalization ^ 5

theorem massRadicand_positive
    (normalization : Normalization) :
    0 < massRadicand normalization := by

  unfold massRadicand

  exact
    div_pos
      (
        mul_pos
          (hbar_positive normalization)
          (causalSpeed_positive normalization)
      )
      (gravityCoupling_positive normalization)

theorem lengthRadicand_positive
    (normalization : Normalization) :
    0 < lengthRadicand normalization := by

  unfold lengthRadicand

  exact
    div_pos
      (
        mul_pos
          (hbar_positive normalization)
          (gravityCoupling_positive normalization)
      )
      (
        pow_pos
          (causalSpeed_positive normalization)
          3
      )

theorem timeRadicand_positive
    (normalization : Normalization) :
    0 < timeRadicand normalization := by

  unfold timeRadicand

  exact
    div_pos
      (
        mul_pos
          (hbar_positive normalization)
          (gravityCoupling_positive normalization)
      )
      (
        pow_pos
          (causalSpeed_positive normalization)
          5
      )

/-
## Canonical Planck scales
-/

/--
The Planck mass.

    mP = sqrt (ℏ c / G).
-/
noncomputable def planckMass
    (normalization : Normalization) :
    ℝ :=

  Real.sqrt
    (massRadicand normalization)

/--
The Planck length.

    lP = sqrt (ℏ G / c³).
-/
noncomputable def planckLength
    (normalization : Normalization) :
    ℝ :=

  Real.sqrt
    (lengthRadicand normalization)

/--
The Planck time.

    tP = sqrt (ℏ G / c⁵).
-/
noncomputable def planckTime
    (normalization : Normalization) :
    ℝ :=

  Real.sqrt
    (timeRadicand normalization)

theorem planckMass_positive
    (normalization : Normalization) :
    0 < planckMass normalization := by

  unfold planckMass

  exact
    Real.sqrt_pos.2
      (massRadicand_positive normalization)

theorem planckLength_positive
    (normalization : Normalization) :
    0 < planckLength normalization := by

  unfold planckLength

  exact
    Real.sqrt_pos.2
      (lengthRadicand_positive normalization)

theorem planckTime_positive
    (normalization : Normalization) :
    0 < planckTime normalization := by

  unfold planckTime

  exact
    Real.sqrt_pos.2
      (timeRadicand_positive normalization)

theorem planckMass_ne_zero
    (normalization : Normalization) :
    planckMass normalization ≠ 0 := by

  exact
    ne_of_gt
      (planckMass_positive normalization)

theorem planckLength_ne_zero
    (normalization : Normalization) :
    planckLength normalization ≠ 0 := by

  exact
    ne_of_gt
      (planckLength_positive normalization)

theorem planckTime_ne_zero
    (normalization : Normalization) :
    planckTime normalization ≠ 0 := by

  exact
    ne_of_gt
      (planckTime_positive normalization)

/-
## Exact defining relations
-/

/--
The Planck mass satisfies its exact squared relation.
-/
theorem planckMass_sq
    (normalization : Normalization) :
    planckMass normalization ^ 2 =
      hbar normalization *
          causalSpeed normalization
        /
          gravityCoupling normalization := by

  unfold planckMass
  unfold massRadicand

  exact
    Real.sq_sqrt
      (
        le_of_lt
          (
            massRadicand_positive
              normalization
          )
      )

/--
The Planck length satisfies its exact squared relation.
-/
theorem planckLength_sq
    (normalization : Normalization) :
    planckLength normalization ^ 2 =
      hbar normalization *
          gravityCoupling normalization
        /
          causalSpeed normalization ^ 3 := by

  unfold planckLength
  unfold lengthRadicand

  exact
    Real.sq_sqrt
      (
        le_of_lt
          (
            lengthRadicand_positive
              normalization
          )
      )

/--
The Planck time satisfies its exact squared relation.
-/
theorem planckTime_sq
    (normalization : Normalization) :
    planckTime normalization ^ 2 =
      hbar normalization *
          gravityCoupling normalization
        /
          causalSpeed normalization ^ 5 := by

  unfold planckTime
  unfold timeRadicand

  exact
    Real.sq_sqrt
      (
        le_of_lt
          (
            timeRadicand_positive
              normalization
          )
      )

/--
The squared Planck length equals `c²` times the squared Planck time.

    lP² = c² tP².
-/
theorem planckLength_sq_eq_causal_sq_mul_planckTime_sq
    (normalization : Normalization) :
    planckLength normalization ^ 2 =
      causalSpeed normalization ^ 2 *
        planckTime normalization ^ 2 := by

  rw [
    planckLength_sq,
    planckTime_sq
  ]

  field_simp [
    causalSpeed_ne_zero normalization
  ]

/-
## Uniqueness
-/

/--
The Planck mass is the unique positive scale satisfying its squared
defining relation.
-/
theorem planckMass_unique
    (normalization : Normalization)
    (candidate : ℝ)
    (hPositive : 0 < candidate)
    (hSquare :
      candidate ^ 2 =
        massRadicand normalization) :
    candidate =
      planckMass normalization := by

  have hCanonicalPositive :
      0 <
        planckMass normalization :=
    planckMass_positive normalization

  have hCanonicalSquare :
      planckMass normalization ^ 2 =
        massRadicand normalization := by

    simpa [massRadicand] using
      planckMass_sq normalization

  nlinarith

/--
The Planck length is the unique positive scale satisfying its squared
defining relation.
-/
theorem planckLength_unique
    (normalization : Normalization)
    (candidate : ℝ)
    (hPositive : 0 < candidate)
    (hSquare :
      candidate ^ 2 =
        lengthRadicand normalization) :
    candidate =
      planckLength normalization := by

  have hCanonicalPositive :
      0 <
        planckLength normalization :=
    planckLength_positive normalization

  have hCanonicalSquare :
      planckLength normalization ^ 2 =
        lengthRadicand normalization := by

    simpa [lengthRadicand] using
      planckLength_sq normalization

  nlinarith

/--
The Planck time is the unique positive scale satisfying its squared
defining relation.
-/
theorem planckTime_unique
    (normalization : Normalization)
    (candidate : ℝ)
    (hPositive : 0 < candidate)
    (hSquare :
      candidate ^ 2 =
        timeRadicand normalization) :
    candidate =
      planckTime normalization := by

  have hCanonicalPositive :
      0 <
        planckTime normalization :=
    planckTime_positive normalization

  have hCanonicalSquare :
      planckTime normalization ^ 2 =
        timeRadicand normalization := by

    simpa [timeRadicand] using
      planckTime_sq normalization

  nlinarith

/--
There exists exactly one positive Planck mass.
-/
theorem existsUnique_planckMass
    (normalization : Normalization) :
    ∃! candidate : ℝ,
      0 < candidate
        ∧
      candidate ^ 2 =
        massRadicand normalization := by

  refine
    ⟨
      planckMass normalization,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        planckMass_positive normalization,
        by
          simpa [massRadicand] using
            planckMass_sq normalization
      ⟩

  · intro candidate hCandidate

    exact
      planckMass_unique
        normalization
        candidate
        hCandidate.1
        hCandidate.2

/--
There exists exactly one positive Planck length.
-/
theorem existsUnique_planckLength
    (normalization : Normalization) :
    ∃! candidate : ℝ,
      0 < candidate
        ∧
      candidate ^ 2 =
        lengthRadicand normalization := by

  refine
    ⟨
      planckLength normalization,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        planckLength_positive normalization,
        by
          simpa [lengthRadicand] using
            planckLength_sq normalization
      ⟩

  · intro candidate hCandidate

    exact
      planckLength_unique
        normalization
        candidate
        hCandidate.1
        hCandidate.2

/--
There exists exactly one positive Planck time.
-/
theorem existsUnique_planckTime
    (normalization : Normalization) :
    ∃! candidate : ℝ,
      0 < candidate
        ∧
      candidate ^ 2 =
        timeRadicand normalization := by

  refine
    ⟨
      planckTime normalization,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        planckTime_positive normalization,
        by
          simpa [timeRadicand] using
            planckTime_sq normalization
      ⟩

  · intro candidate hCandidate

    exact
      planckTime_unique
        normalization
        candidate
        hCandidate.1
        hCandidate.2

/-
## Dimensional signatures
-/

/--
The pure mass signature `M`.
-/
def massSignature :
    PhysicalTokenInterface.Signature where

  mass :=
    1

  length :=
    0

  time :=
    0

/--
The pure length signature `L`.
-/
def lengthSignature :
    PhysicalTokenInterface.Signature where

  mass :=
    0

  length :=
    1

  time :=
    0

/--
The pure time signature `T`.
-/
def timeSignature :
    PhysicalTokenInterface.Signature where

  mass :=
    0

  length :=
    0

  time :=
    1

theorem planck_scale_signatures_are_distinct :
    massSignature ≠ lengthSignature
      ∧
    massSignature ≠ timeSignature
      ∧
    lengthSignature ≠ timeSignature := by

  native_decide

/-
## Monad-derived Planck scale tokens
-/

/--
The three roles in the Planck token system.
-/
inductive Role where

  | mass
  | length
  | time

  deriving
    DecidableEq,
    Repr

/--
The expected dimensional signature of each Planck-scale role.
-/
def expectedSignature :
    Role →
      PhysicalTokenInterface.Signature

  | .mass =>
      massSignature

  | .length =>
      lengthSignature

  | .time =>
      timeSignature

/--
A Planck-scale token retains its originating OMBT monad.
-/
structure Token where

  source :
    KTMonad.Monad

  role :
    Role

  magnitude :
    ℝ

  magnitude_positive :
    0 < magnitude

/--
The dimensional signature of a Planck-scale token.
-/
def Token.signature
    (token : Token) :
    PhysicalTokenInterface.Signature :=

  expectedSignature token.role

/--
Mint a Planck-mass token over one OMBT monad.
-/
noncomputable def massToken
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    Token where

  source :=
    source

  role :=
    .mass

  magnitude :=
    planckMass normalization

  magnitude_positive :=
    planckMass_positive normalization

/--
Mint a Planck-length token over one OMBT monad.
-/
noncomputable def lengthToken
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    Token where

  source :=
    source

  role :=
    .length

  magnitude :=
    planckLength normalization

  magnitude_positive :=
    planckLength_positive normalization

/--
Mint a Planck-time token over one OMBT monad.
-/
noncomputable def timeToken
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    Token where

  source :=
    source

  role :=
    .time

  magnitude :=
    planckTime normalization

  magnitude_positive :=
    planckTime_positive normalization

@[simp]
theorem massToken_source
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (massToken normalization source).source =
      source := by

  rfl

@[simp]
theorem lengthToken_source
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (lengthToken normalization source).source =
      source := by

  rfl

@[simp]
theorem timeToken_source
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (timeToken normalization source).source =
      source := by

  rfl

theorem massToken_signature
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (massToken normalization source).signature =
      massSignature := by

  rfl

theorem lengthToken_signature
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (lengthToken normalization source).signature =
      lengthSignature := by

  rfl

theorem timeToken_signature
    (normalization : Normalization)
    (source : KTMonad.Monad) :
    (timeToken normalization source).signature =
      timeSignature := by

  rfl

/-
## Universality across monadic views
-/

theorem planckMass_independent_of_monad
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (massToken normalization left).magnitude =
      (massToken normalization right).magnitude := by

  rfl

theorem planckLength_independent_of_monad
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (lengthToken normalization left).magnitude =
      (lengthToken normalization right).magnitude := by

  rfl

theorem planckTime_independent_of_monad
    (normalization : Normalization)
    (left right : KTMonad.Monad) :
    (timeToken normalization left).magnitude =
      (timeToken normalization right).magnitude := by

  rfl

theorem reverseTemporal_preserves_planckScales
    (normalization : Normalization)
    (monad : KTMonad.Monad) :
    (
      massToken
        normalization
        (OMBTMonadDynamics.reverseTemporal monad)
    ).magnitude =
        (massToken normalization monad).magnitude
      ∧
    (
      lengthToken
        normalization
        (OMBTMonadDynamics.reverseTemporal monad)
    ).magnitude =
        (lengthToken normalization monad).magnitude
      ∧
    (
      timeToken
        normalization
        (OMBTMonadDynamics.reverseTemporal monad)
    ).magnitude =
      (timeToken normalization monad).magnitude := by

  exact
    ⟨rfl, rfl, rfl⟩

theorem exchangePhase_preserves_planckScales
    (normalization : Normalization)
    (monad : KTMonad.Monad) :
    (
      massToken
        normalization
        (OMBTMonadDynamics.exchangePhase monad)
    ).magnitude =
        (massToken normalization monad).magnitude
      ∧
    (
      lengthToken
        normalization
        (OMBTMonadDynamics.exchangePhase monad)
    ).magnitude =
        (lengthToken normalization monad).magnitude
      ∧
    (
      timeToken
        normalization
        (OMBTMonadDynamics.exchangePhase monad)
    ).magnitude =
      (timeToken normalization monad).magnitude := by

  exact
    ⟨rfl, rfl, rfl⟩

/-
## Capstone
-/

/--
Capstone theorem.

Positive `ℏ`, `c`, and `G` token magnitudes force unique positive Planck
mass, length, and time scales satisfying:

    mP² = ℏ c / G,

    lP² = ℏ G / c³,

    tP² = ℏ G / c⁵.

The squared length-time relation

    lP² = c² tP²

is also exact.

Each scale receives the correct pure dimensional signature, retains its
source monad, and remains invariant under temporal reversal and
visible/escrow exchange.

This establishes the Planck-scale token system structurally. Numerical SI
values remain conditional on the upstream token normalizations.
-/
theorem physical_planck_scale_emerges
    (normalization : Normalization) :
    (
      ∃! mass : ℝ,
        0 < mass
          ∧
        mass ^ 2 =
          massRadicand normalization
    )
      ∧
    (
      ∃! length : ℝ,
        0 < length
          ∧
        length ^ 2 =
          lengthRadicand normalization
    )
      ∧
    (
      ∃! time : ℝ,
        0 < time
          ∧
        time ^ 2 =
          timeRadicand normalization
    )
      ∧
    planckLength normalization ^ 2 =
      causalSpeed normalization ^ 2 *
        planckTime normalization ^ 2
      ∧
    (
      ∀ source : KTMonad.Monad,
        (massToken normalization source).source =
            source
          ∧
        (massToken normalization source).signature =
            massSignature
          ∧
        (lengthToken normalization source).source =
            source
          ∧
        (lengthToken normalization source).signature =
            lengthSignature
          ∧
        (timeToken normalization source).source =
            source
          ∧
        (timeToken normalization source).signature =
            timeSignature
    ) := by

  refine
    ⟨
      existsUnique_planckMass normalization,
      existsUnique_planckLength normalization,
      existsUnique_planckTime normalization,
      planckLength_sq_eq_causal_sq_mul_planckTime_sq
        normalization,
      ?_
    ⟩

  intro source

  exact
    ⟨
      massToken_source normalization source,
      massToken_signature normalization source,
      lengthToken_source normalization source,
      lengthToken_signature normalization source,
      timeToken_source normalization source,
      timeToken_signature normalization source
    ⟩

end PhysicalPlanckScale

#check PhysicalPlanckScale.Normalization
#check PhysicalPlanckScale.hbar
#check PhysicalPlanckScale.causalSpeed
#check PhysicalPlanckScale.gravityCoupling
#check PhysicalPlanckScale.massRadicand
#check PhysicalPlanckScale.lengthRadicand
#check PhysicalPlanckScale.timeRadicand
#check PhysicalPlanckScale.planckMass
#check PhysicalPlanckScale.planckLength
#check PhysicalPlanckScale.planckTime
#check PhysicalPlanckScale.planckMass_sq
#check PhysicalPlanckScale.planckLength_sq
#check PhysicalPlanckScale.planckTime_sq
#check PhysicalPlanckScale.existsUnique_planckMass
#check PhysicalPlanckScale.existsUnique_planckLength
#check PhysicalPlanckScale.existsUnique_planckTime
#check PhysicalPlanckScale.massToken
#check PhysicalPlanckScale.lengthToken
#check PhysicalPlanckScale.timeToken
#check PhysicalPlanckScale.physical_planck_scale_emerges
