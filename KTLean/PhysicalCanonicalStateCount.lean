import KTLean.PhysicalProjectionState
import KTLean.PhysicalAlphaProjectionCorrection
import Mathlib.Tactic

/-!
# Canonical Projection-State Count Obligation

## Formal status

**Open obligation interface — conditional extraction of one canonical
projection-state count from the four admissible Planck-ratio candidates.**

## Developmental predecessor

`PhysicalProjectionState`

The preceding module proves that four positive, dimensionless candidate
state counts are admissible:

    L / lP,
    A / lP²,
    V / lP³,
    S / ℏ.

It deliberately does not select one of them.

The corrected four-dimensional alpha expression requires a state count
strictly greater than one. This module therefore formalizes exactly what
must still be supplied by the projection geometry:

1. a criterion on candidate projection states;
2. proof that exactly one of the four candidates satisfies that criterion;
3. proof that the selected candidate has state count greater than one.

Once such a certification is supplied, the canonical index, canonical
projection state, and alpha-compatible projection state follow uniquely.

No value of `n` is inserted here. No candidate grammar is declared
canonical by definition.
-/

namespace PhysicalCanonicalStateCount

/-
## Candidate context
-/

/--
The data required to generate the four candidate projection states.
-/
structure Context where

  planckNormalization :
    PhysicalPlanckScale.Normalization

  projectionNormalization :
    PhysicalProjectionState.Normalization

  source :
    KTMonad.Monad

/--
The four candidate projection states associated with one context.
-/
noncomputable def candidate
    (context : Context)
    (index : Fin 4) :
    PhysicalProjectionState.State :=

  PhysicalProjectionState.candidateStates
    context.planckNormalization
    context.projectionNormalization
    context.source
    index

/--
Every candidate retains the context's source monad.
-/
theorem candidate_source
    (context : Context)
    (index : Fin 4) :
    (candidate context index).source =
      context.source := by

  exact
    (
      PhysicalProjectionState.candidateStates_are_admissible
        context.planckNormalization
        context.projectionNormalization
        context.source
        index
    ).1

/--
Every candidate has positive state count.
-/
theorem candidate_positive
    (context : Context)
    (index : Fin 4) :
    0 <
      (candidate context index).stateCount := by

  exact
    (
      PhysicalProjectionState.candidateStates_are_admissible
        context.planckNormalization
        context.projectionNormalization
        context.source
        index
    ).2.1

/--
Every candidate is dimensionless.
-/
theorem candidate_dimensionless
    (context : Context)
    (index : Fin 4) :
    (candidate context index).signature =
      PhysicalTokenInterface.dimensionlessSignature := by

  exact
    (
      PhysicalProjectionState.candidateStates_are_admissible
        context.planckNormalization
        context.projectionNormalization
        context.source
        index
    ).2.2

/-
## Selection criterion
-/

/--
A proposed geometric criterion for selecting a canonical projection state.

The predicate is intentionally abstract. A later derivation must define it
from KT projection geometry rather than from the desired numerical value.
-/
abbrev Criterion :=
  PhysicalProjectionState.State →
    Prop

/--
An index is admissibly selected when:

* its candidate satisfies the supplied criterion;
* its state count is strictly greater than one.

The second requirement is exactly what the logarithmic alpha correction
needs.
-/
def Selected
    (context : Context)
    (criterion : Criterion)
    (index : Fin 4) :
    Prop :=

  criterion (candidate context index)
    ∧
  1 < (candidate context index).stateCount

/--
A canonicality certification proves that exactly one of the four candidate
indices is admissibly selected.
-/
structure Certification
    (context : Context)
    (criterion : Criterion) where

  existsUnique_selected :
    ∃! index : Fin 4,
      Selected
        context
        criterion
        index

/-
## Extraction of the unique canonical candidate
-/

/--
The uniquely selected candidate index.
-/
noncomputable def canonicalIndex
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    Fin 4 :=

  Classical.choose
    certification.existsUnique_selected.exists

/--
The canonical index satisfies the selection predicate.
-/
theorem canonicalIndex_selected
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    Selected
      context
      criterion
      (canonicalIndex certification) := by

  exact
    Classical.choose_spec
      certification.existsUnique_selected.exists

/--
Any selected index equals the canonical index.
-/
theorem selected_index_unique
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion)
    (index : Fin 4)
    (hSelected :
      Selected context criterion index) :
    index =
      canonicalIndex certification := by

  rcases
      certification.existsUnique_selected
    with
      ⟨witness, hWitness, hUnique⟩

  have hIndex :
      index =
        witness :=
    hUnique
      index
      hSelected

  have hCanonical :
      canonicalIndex certification =
        witness :=
    hUnique
      (canonicalIndex certification)
      (canonicalIndex_selected certification)

  exact
    hIndex.trans
      hCanonical.symm

/--
The uniquely selected canonical projection state.
-/
noncomputable def canonicalState
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    PhysicalProjectionState.State :=

  candidate
    context
    (canonicalIndex certification)

/--
The canonical projection state's numerical count.
-/
noncomputable def canonicalStateCount
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    ℝ :=

  (canonicalState certification).stateCount

/-
## Canonical-state properties
-/

/--
The canonical state satisfies the supplied geometric criterion.
-/
theorem canonicalState_satisfies_criterion
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    criterion
      (canonicalState certification) := by

  exact
    (canonicalIndex_selected certification).1

/--
The canonical state count is strictly greater than one.
-/
theorem canonicalStateCount_gt_one
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    1 <
      canonicalStateCount certification := by

  exact
    (canonicalIndex_selected certification).2

/--
The canonical state count is positive.
-/
theorem canonicalStateCount_positive
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    0 <
      canonicalStateCount certification := by

  linarith [
    canonicalStateCount_gt_one certification
  ]

/--
The canonical state retains the originating monad.
-/
theorem canonicalState_source
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    (canonicalState certification).source =
      context.source := by

  exact
    candidate_source
      context
      (canonicalIndex certification)

/--
The canonical state remains dimensionless.
-/
theorem canonicalState_dimensionless
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    (canonicalState certification).signature =
      PhysicalTokenInterface.dimensionlessSignature := by

  exact
    candidate_dimensionless
      context
      (canonicalIndex certification)

/-
## Uniqueness at the state level
-/

/--
Any candidate satisfying the canonical criterion has the same index as the
canonical candidate.
-/
theorem candidate_eq_canonical_of_selected
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion)
    (index : Fin 4)
    (hSelected :
      Selected context criterion index) :
    candidate context index =
      canonicalState certification := by

  have hIndex :
      index =
        canonicalIndex certification :=
    selected_index_unique
      certification
      index
      hSelected

  subst index

  rfl

/--
Any selected candidate has exactly the canonical state count.
-/
theorem selected_stateCount_eq_canonical
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion)
    (index : Fin 4)
    (hSelected :
      Selected context criterion index) :
    (candidate context index).stateCount =
      canonicalStateCount certification := by

  have hIndex :
      index =
        canonicalIndex certification :=
    selected_index_unique
      certification
      index
      hSelected

  subst index

  rfl
/-
## Bridge to the alpha projection correction
-/

/--
The canonical count packaged in the exact state structure required by the
alpha-projection correction module.
-/
noncomputable def alphaProjectionState
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    PhysicalAlphaProjectionCorrection.ProjectionState where

  stateCount :=
    canonicalStateCount certification

  stateCount_gt_one :=
    canonicalStateCount_gt_one certification

/--
The alpha-compatible state uses exactly the canonical state count.
-/
@[simp]
theorem alphaProjectionState_stateCount
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    (alphaProjectionState certification).stateCount =
      canonicalStateCount certification := by

  rfl

/--
The alpha-compatible state count is strictly greater than one.
-/
theorem alphaProjectionState_gt_one
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    1 <
      (alphaProjectionState certification).stateCount := by

  exact
    canonicalStateCount_gt_one certification

/-
## Exact statement of the open obligation
-/

/--
The unresolved canonical-state-count obligation.

For a given context, projection geometry must supply a criterion for which
exactly one of the four candidates is selected.
-/
def CanonicalStateCountObligation
    (context : Context) :
    Prop :=

  ∃ criterion : Criterion,
    Nonempty
      (Certification context criterion)

/--
Any solution of the canonical-state-count obligation supplies a unique
alpha-compatible projection state.
-/
theorem obligation_supplies_alpha_state
    (context : Context)
    (hObligation :
      CanonicalStateCountObligation context) :
    ∃
      (criterion : Criterion)
      (certification :
        Certification context criterion),
      1 <
        (
          alphaProjectionState
            certification
        ).stateCount
        ∧
      (
        canonicalState certification
      ).source =
        context.source
        ∧
      (
        canonicalState certification
      ).signature =
        PhysicalTokenInterface.dimensionlessSignature := by

  rcases hObligation with
    ⟨criterion, hCertification⟩

  rcases hCertification with
    ⟨certification⟩

  exact
    ⟨
      criterion,
      certification,
      alphaProjectionState_gt_one certification,
      canonicalState_source certification,
      canonicalState_dimensionless certification
    ⟩

/-
## Capstone
-/

/--
Capstone theorem.

Given a projection-geometric criterion and proof that exactly one of the
four Planck-ratio candidates satisfies it with count greater than one:

* a unique canonical candidate index is obtained;
* the canonical state satisfies the criterion;
* its count is positive and greater than one;
* it remains dimensionless;
* it retains monadic provenance;
* it can be passed directly into the corrected-alpha construction.

The theorem does not supply the criterion. Deriving that criterion remains
the explicit open physical obligation.
-/
theorem canonical_state_count_follows_from_certification
    {context : Context}
    {criterion : Criterion}
    (certification :
      Certification context criterion) :
    Selected
        context
        criterion
        (canonicalIndex certification)
      ∧
    1 <
      canonicalStateCount certification
      ∧
    (canonicalState certification).source =
      context.source
      ∧
    (canonicalState certification).signature =
      PhysicalTokenInterface.dimensionlessSignature
      ∧
    (
      alphaProjectionState certification
    ).stateCount =
      canonicalStateCount certification := by

  exact
    ⟨
      canonicalIndex_selected certification,
      canonicalStateCount_gt_one certification,
      canonicalState_source certification,
      canonicalState_dimensionless certification,
      rfl
    ⟩

end PhysicalCanonicalStateCount

#check PhysicalCanonicalStateCount.Context
#check PhysicalCanonicalStateCount.Criterion
#check PhysicalCanonicalStateCount.Selected
#check PhysicalCanonicalStateCount.Certification
#check PhysicalCanonicalStateCount.canonicalIndex
#check PhysicalCanonicalStateCount.canonicalState
#check PhysicalCanonicalStateCount.canonicalStateCount
#check PhysicalCanonicalStateCount.alphaProjectionState
#check PhysicalCanonicalStateCount.CanonicalStateCountObligation
#check PhysicalCanonicalStateCount.obligation_supplies_alpha_state
#check PhysicalCanonicalStateCount.canonical_state_count_follows_from_certification
