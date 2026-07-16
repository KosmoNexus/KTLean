# KTLean Critical Theorem Audit

## Purpose

This document audits the most load-bearing theorems in KTLean.

For each theorem, the audit records:

- what the theorem formally proves;
- why it matters;
- whether the statement was fixed before proof;
- whether definitions changed during proof;
- what stronger claim is not established;
- what failure would have meant for the project;
- current axiom dependencies;
- frame and tokenization status;
- known open obligations.

The governing principle is:

> The theorem count measures formal output.  
> The audit measures epistemic weight.

---

# 1. `KTGlyph.card_glyph`

## Module

`KTLean/Glyph.lean`

## Formal statement

```lean
theorem card_glyph :
  Fintype.card Glyph = 42
```

## Informal claim

The lawful framed-operation space named `Glyph` contains exactly 42 elements.

## Claim class

- STRUCTURAL
- CARDINALITY

## Statement provenance

`SOURCE_FIXED` / `ARCHITECT_FIXED`

The 42 count predates the Lean proof and is central to the KT glyph construction.

## Statement frozen before proof?

`YES`

## Definitions changed during proof attempt?

`YES_SYNTACTIC_ONLY` or `UNKNOWN`

No known substantive change was introduced solely to obtain the count. This should be checked against the development history.

## Counterfactual importance

`CENTRAL_CLAIM_FAILURE`

Failure would have broken the 42-glyph architecture and every downstream theorem using the 42 × 4 = 168 monad construction.

## What the theorem proves

It proves that the exact Lean carrier

```lean
KTGlyph.Glyph
```

has cardinality 42.

## Stronger claim not established

It does not prove that every physically admissible local process in reality must be represented by one of these 42 glyphs.

The count is relative to the framed Fano law encoded in `OperationNormalForm`.

It does not yet prove that the glyph carrier is invariant under the concrete PSL(2,7) substrate action.

## Current axiom dependencies

From `AxiomAuditOutput.txt`:

```text
[propext, Classical.choice, Quot.sound]
```

No `native_decide` dependency remains.

## Frame status

`FRAME_STATUS_UNPROVED`

The abstract monad frame discipline has been formalized, but the concrete PSL(2,7) action on glyphs has not yet been constructed.

## Tokenization status

`PRE_TOKENIZATION`

## Failure condition

A proof that the framed Fano law is non-intrinsic, non-exhaustive, or dependent on an illicit preferred trivialization would force revision of the physical interpretation of the 42 count.

## Audit status

- LEAN_COMPILES
- LAKE_BUILD_PASSES
- AXIOM_AUDITED
- NATIVE_DECIDE_REMOVED
- DEFINITION_LEDGER_STARTED
- SOURCE_AUDIT_PENDING
- FRAME_AUDIT_PENDING

---

# 2. `KTMonad.card_monad`

## Module

`KTLean/Monad.lean`

## Formal statement

```lean
theorem card_monad :
  Fintype.card Monad = 168
```

## Informal claim

The complete monad space contains 168 elements: 42 glyphs paired with four realized walk states.

## Claim class

- STRUCTURAL
- CARDINALITY

## Statement provenance

`SOURCE_FIXED` / `ARCHITECT_FIXED`

The 168-monad construction predates the Lean proof.

## Statement frozen before proof?

`YES`

## Definitions changed during proof attempt?

`UNKNOWN`

The current Lean representation of the four walk realizations as temporal direction × information phase must be compared explicitly with the canonical monad source.

The count itself was not selected after computation. The target 168 was part of the source architecture before the Lean formalization.

## Counterfactual importance

`CENTRAL_CLAIM_FAILURE`

Failure would have broken the monad architecture and the intended relationship between 42 glyphs, four walk realizations, and the order of PSL(2,7).

## What the theorem proves

It proves that the exact Lean carrier

```lean
KTMonad.Monad
```

has cardinality 168.

## Stronger claim not established

It does not yet prove that the four walk realizations transform coherently under the concrete PSL(2,7) action.

It does not prove that every element of PSL(2,7) has already been identified canonically with one monad.

It does not prove that the 168 monads are directly observable physical objects.

It does not establish the particle assignments proposed in earlier monad manuscripts.

## Current axiom dependencies

```text
[propext, Classical.choice, Quot.sound]
```

No `native_decide` dependency remains.

## Frame status

`FRAME_STATUS_UNPROVED`

The abstract frame-action discipline exists through:

- `MonadAction`
- `MonadInvariant`
- `MonadOrbit`
- `MonadTrivialization`
- `MonadProjection`

The concrete PSL(2,7) action remains open.

## Tokenization status

`PRE_TOKENIZATION`

## Failure condition

A proof that the four walk states are not exhaustive, are not intrinsic, or fail coherent transport under PSL(2,7) would require revision of the monad definition.

A mismatch between the four-state Lean fiber and the source meaning of a glyph’s four walk realizations would also require revision.

## Audit status

- LEAN_COMPILES
- LAKE_BUILD_PASSES
- AXIOM_AUDITED
- NATIVE_DECIDE_REMOVED
- DEFINITION_LEDGER_STARTED
- SOURCE_AUDIT_PENDING
- FRAME_AUDIT_PENDING

---

# 3. `CayleyDicksonQuaternion.routedMul_eq_cdMul`

## Module

`KTLean/CayleyDicksonQuaternion.lean`

## Formal statement

```lean
theorem routedMul_eq_cdMul
    (x y : Carrier) :
    routedMul x y = cdMul x y
```

## Informal claim

The explicitly specified selector, routing, and orientation tables reconstruct the chosen Cayley–Dickson quaternion-block product exactly.

## Claim class

- STRUCTURAL
- ROUTING
- COMPOSITION

## Statement provenance

`FORMALIZATION_DERIVED`

The target Cayley–Dickson product is independently defined.

The selector, route, and orientation datum in the present module were then specified to reproduce that target.

## Statement frozen before proof?

`PARTIAL`

The target Cayley–Dickson multiplication was fixed before the equality proof.

The routing datum was target-informed and therefore cannot yet serve as independent evidence that Pascal routing forces the octonion product.

## Definitions changed during proof attempt?

`UNKNOWN`

No evidence of substantive drift is presently recorded.

The selector space was expanded during development from a restricted conjugation-only form to the necessary eight multiplication forms because the earlier construction could not represent terms with reversed quaternionic order.

That repair should be recorded as an architectural correction, not concealed as a syntactic change.

## Counterfactual importance

`MAJOR_BRANCH_FAILURE`

Failure would have meant that the current selector, route, and orientation implementation did not reconstruct the intended Cayley–Dickson product.

It would not by itself have falsified the broader routed-quaternion program, but it would have shown that the chosen routing architecture was inadequate.

## What the theorem proves

It proves exact equality between:

```lean
routedMul
```

and:

```lean
cdMul
```

for all quaternion-block pairs.

The routed expression therefore reproduces the standard target formula:

```text
(a,b) ⋆ (c,d) = (ac - conjugate(d)b, da + b conjugate(c)).
```

## Stronger claim not established

It does not prove that Pascal modulo 3 forces the routing datum.

It does not prove that the routing datum is unique.

It does not yet prove doubled norm composition:

```text
N(X ⋆ Y) = N(X)N(Y).
```

It does not yet provide a concrete nonzero associator witness.

It does not yet prove alternativity.

It does not prove the full Hurwitz classification theorem.

It does not prove that every routed quaternion-block algebra is octonionic.

## Current axiom dependencies

```text
[propext, Quot.sound]
```

## Frame status

`NOT_APPLICABLE` at the present stage.

The future Pascal-forcing theorem may introduce a relevant invariance requirement on address conventions.

## Tokenization status

`PRE_TOKENIZATION`

## Failure condition

Failure of the future theorem equating an independently derived Pascal routing datum with the Cayley–Dickson datum would defeat the substrate-forcing claim, though not the present implementation theorem.

Failure of norm composition under the intended field assumptions would show that the construction does not yet provide the required composition-algebra structure.

## Audit status

- LEAN_COMPILES
- LAKE_BUILD_PASSES
- AXIOM_AUDITED
- TARGET_IMPLEMENTATION_VERIFIED
- SOURCE_AUDIT_PENDING
- INDEPENDENCE_AUDIT_PARTIAL
- NORM_COMPOSITION_OPEN
- NONASSOCIATIVITY_WITNESS_OPEN
- PASCAL_FORCING_OPEN

---

# 4. `HurwitzBoundary.carrier_reaches_maximal_boundary`

## Module

`KTLean/HurwitzBoundary.lean`

## Formal statement

```lean
theorem carrier_reaches_maximal_boundary :
  Module.finrank R
    (CayleyDicksonQuaternion.Carrier (R := R)) =
      maximalHurwitzDimension
```

## Informal claim

The two-quaternion Cayley–Dickson carrier has scalar dimension 8, the maximal value recorded in the classical Hurwitz list.

## Claim class

- STRUCTURAL
- CARDINALITY
- DIMENSION

## Statement provenance

`FORMALIZATION_DERIVED`

The theorem packages the dimension of an already defined carrier and compares it with the explicitly defined value 8.

## Statement frozen before proof?

`YES`

The carrier was already fixed as a product of two quaternion spaces.

## Definitions changed during proof attempt?

`NO` or `UNKNOWN`

No substantive alteration is presently known.

## Counterfactual importance

`MODULE_REDESIGN`

Failure would indicate a mismatch in the carrier construction, imported quaternion dimension, or scalar-dimension calculation.

It would not by itself falsify KT, but it would break the present quaternion-doubling architecture.

## What the theorem proves

It proves that:

```text
finrank(H × H) = 8
```

over the stated field assumptions.

It establishes that the doubled quaternion carrier lies at dimension 8.

## Stronger claim not established

It does not prove the full Hurwitz classification theorem.

It does not prove that no other finite dimensions admit the relevant composition or division structure.

It does not prove that the doubled carrier itself satisfies norm composition.

It does not prove that doubling beyond 8 necessarily fails composition.

It does not prove that every 8-dimensional composition algebra is isomorphic to the octonions.

The module name `HurwitzBoundary` must therefore be interpreted narrowly: it records the location of constructed objects relative to the classical list, not the classification theorem itself.

## Current axiom dependencies

```text
[propext, Classical.choice, Quot.sound]
```

The presence of `Classical.choice` is consistent with Mathlib’s basis and `finrank` machinery.

The theorem should be classified as classical rather than computational.

## Frame status

`NOT_APPLICABLE`

## Tokenization status

`PRE_TOKENIZATION`

## Failure condition

A mismatch between the carrier and the intended doubled quaternion space would require correction of the construction.

The theorem cannot support the stronger statement that dimension 8 is forced until the missing classification and composition obligations are discharged.

## Audit status

- LEAN_COMPILES
- LAKE_BUILD_PASSES
- AXIOM_AUDITED
- SCOPE_CLARIFIED
- CLASSICAL_DEPENDENCY_RECORDED
- FULL_HURWITZ_OPEN
- DOUBLED_NORM_COMPOSITION_OPEN

---

# 5. `KTLean.RoutedResidueSensitive.dynamics_quasiStochastic`

## Module

`KTLean/RoutedResidueSensitive.lean`

## Formal statement

```lean
theorem dynamics_quasiStochastic :
  dynamics.QuasiStochastic
```

## Informal claim

The explicit address-sensitive routed dynamics is deterministic on complete states, non-injective under the local projection, and residue-sensitive. Therefore its visible dynamics is quasi-stochastic.

## Claim class

- STRUCTURAL
- PROJECTION
- DYNAMICS
- EXISTENCE

## Statement provenance

`FORMALIZATION_DERIVED`

The theorem emerged from the projection and provenance architecture.

The abstract definition of quasi-stochasticity was established before the concrete witness system was constructed.

## Statement frozen before proof?

`PARTIAL`

The abstract criterion was fixed before the witness.

The specific address-sensitive transition law was chosen as a minimal witness construction.

## Definitions changed during proof attempt?

`UNKNOWN`

The transition law should be classified as a designed witness rather than a uniquely forced substrate law.

The proof architecture distinguishes the existing simple routed exchange, which is visibly closed and not residue-sensitive, from the later address-sensitive witness, which is residue-sensitive.

## Counterfactual importance

`MAJOR_BRANCH_FAILURE`

Failure would have broken the first concrete demonstration that deterministic complete dynamics can appear non-Markovian and stochastic under a lower-dimensional projection.

It would not have disproved the abstract theorem that noninjective projection plus residue-sensitive dynamics implies quasi-stochastic visible behavior.

## What the theorem proves

It proves existence of one explicit routed KT system satisfying:

1. deterministic complete evolution;
2. a noninjective local view;
3. explicit hidden provenance residue;
4. different next visible states for presently indistinguishable complete states.

Therefore no visible-state-only Markov transition can reproduce the complete projected dynamics.

## Stronger claim not established

It does not prove that every KT routed system is quasi-stochastic.

It does not prove that the chosen address-sensitive action is uniquely forced.

It does not prove a Born rule.

It does not prove quantum amplitudes.

It does not reproduce empirical quantum statistics.

It does not by itself establish Bell or Tsirelson behavior.

It does not prove that a specific physical system implements this witness dynamics.

## Current axiom dependencies

```text
[propext]
```

No `Classical.choice`, `Quot.sound`, or native-decision axiom appears in the audited theorem.

## Frame status

`FRAME_STATUS_UNPROVED`

The witness transition law must eventually be tested against the concrete substrate symmetry.

A preferred address or preferred block action not preserved under the lawful frame group could weaken or defeat the physical interpretation.

## Tokenization status

`PRE_TOKENIZATION`

## Failure condition

A proof that the witness transition law violates a required substrate symmetry, introduces an illicit preferred frame, or relies on a noncanonical control action would defeat its intended physical interpretation.

The formal existence result would remain true for the specified system.

## Audit status

- LEAN_COMPILES
- LAKE_BUILD_PASSES
- AXIOM_AUDITED
- WITNESS_STATUS_CLARIFIED
- COMPLETE_STATE_DETERMINISM_PROVED
- VISIBLE_NONMARKOVIANITY_PROVED
- FRAME_AUDIT_PENDING
- CANONICAL_CONTROL_ACTION_OPEN

---

# 6. `KTLean.MonadProjection.ScalarProjection.constant_on_orbit`

## Module

`KTLean/MonadProjection.lean`

## Formal statement

```lean
theorem ScalarProjection.constant_on_orbit
    {left right : KTMonad.Monad}
    (horbit :
      MonadOrbit.OrbitEquivalent A left right) :
    P.project left = P.project right
```

## Informal claim

Any lawful scalar projection on monads has the same value on monads related by the declared substrate frame action.

## Claim class

- STRUCTURAL
- INVARIANCE
- PROJECTION

## Statement provenance

`ARCHITECT_FIXED`

The theorem formalizes the principle that a physical scalar statement about monads cannot depend on an arbitrary substrate trivialization or preferred frame.

## Statement frozen before proof?

`YES`

The invariance requirement was articulated before the proof module was constructed.

## Definitions changed during proof attempt?

`NO_SUBSTANTIVE_CHANGE_KNOWN`

The proof follows directly from the definition of invariant observable and orbit equivalence.

## Counterfactual importance

`CENTRAL_CLAIM_FAILURE`

Failure would have meant that the current definitions of orbit equivalence or physical scalar admissibility did not correctly encode the no-preferred-frame principle.

## What the theorem proves

Given an abstract lawful frame action `A`, any scalar projection constructed with an invariance proof is constant along the resulting monad orbits.

## Stronger claim not established

It does not construct the concrete PSL(2,7) action.

It does not prove that every existing monad theorem is invariant.

It does not prove that every monad orbit has a particular size.

It does not prove that the quotient by the action is the physically correct monad state space.

## Current axiom dependencies

```text
does not depend on any axioms
```

This is the cleanest theorem in the initial axiom audit sample.

## Frame status

`CONDITIONAL_ON_FRAME_ACTION`

The theorem is fully proved for any supplied lawful action.

The concrete KT interpretation remains conditional until the PSL(2,7) action is instantiated.

## Tokenization status

`PRE_TOKENIZATION`

## Failure condition

The theorem’s physical role would fail if the eventual concrete action did not represent the full lawful substrate symmetry, or if a claimed physical observable could not be shown invariant under that action.

## Audit status

- LEAN_COMPILES
- LAKE_BUILD_PASSES
- AXIOM_AUDITED
- AXIOM_FREE
- ABSTRACT_INVARIANCE_PROVED
- CONCRETE_PSL27_ACTION_OPEN

---

# 7. `KTLean.MonadOrbit.physicallyAdmissible_factors_through_orbit`

## Module

`KTLean/MonadOrbit.lean`

## Formal role

A physically admissible invariant observable on complete monads descends to a well-defined function on the monad orbit space.

## Informal claim

A physical scalar quantity depends only on the lawful frame orbit of a monad, not on the chosen monad representative.

## Claim class

- STRUCTURAL
- INVARIANCE
- QUOTIENT
- PROJECTION

## Statement provenance

`ARCHITECT_FIXED`

The theorem is a direct formal expression of the no-preferred-trivialization principle.

## Statement frozen before proof?

`YES`

## Definitions changed during proof attempt?

`NO_SUBSTANTIVE_CHANGE_KNOWN`

Quotient implementation details were adjusted to satisfy Lean, but the intended mathematical statement remained fixed.

## Counterfactual importance

`CENTRAL_CLAIM_FAILURE`

Failure would have indicated that the orbit relation, quotient construction, or admissibility definition did not correctly capture physical frame independence.

## What the theorem proves

For any supplied lawful frame action and any invariant observable, there exists a function on the orbit quotient whose value on a monad class equals the original observable on any representative.

## Stronger claim not established

It does not prove that the concrete KT monad space carries the intended PSL(2,7) action.

It does not prove that the physical state is literally the quotient.

It does not prove that all existing monad observables have been shown admissible.

## Current axiom dependencies

```text
[propext]
```

## Frame status

`CONDITIONAL_ON_FRAME_ACTION`

## Orbit status

`DESCENDS_TO_ORBIT_SPACE`

## Tokenization status

`PRE_TOKENIZATION`

## Failure condition

The theorem’s physical interpretation would fail if the declared group action omitted lawful substrate transformations or included transformations that are not physically gauge-like.

## Audit status

- LEAN_COMPILES
- LAKE_BUILD_PASSES
- AXIOM_AUDITED
- ABSTRACT_ORBIT_DESCENT_PROVED
- CONCRETE_PSL27_ACTION_OPEN

---

# 8. Audit Summary

The first critical audit finds:

1. No untracked bespoke axiom appeared in the sampled terminal theorem chains.

2. No `native_decide` dependency remains in the 42-glyph or 168-monad cardinality chain.

3. The remaining reported logical dependencies are ordinary Lean or Mathlib dependencies:
   - `propext`;
   - `Quot.sound`;
   - `Classical.choice`.

4. `Classical.choice` appears principally through finite-dimensional linear algebra, bases, `finrank`, and related imported structures. Results carrying this dependency must not be advertised as executable kernel computations.

5. The exact 42 and 168 cardinalities remain proved after removal of native-evaluation trust axioms.

6. The Cayley–Dickson routed multiplication theorem is a genuine exact implementation theorem, but not yet a Pascal-forcing theorem.

7. The current Hurwitz boundary module proves dimensions of constructed objects, not the full Hurwitz classification theorem.

8. The routed residue-sensitive module gives a genuine concrete quasi-stochastic witness, but the witness transition law is not yet shown canonical or invariant under the concrete substrate symmetry.

9. The new monad invariance, orbit, trivialization, and projection architecture correctly encodes the prohibition against a preferred substrate frame at the abstract level.

10. The concrete PSL(2,7) action remains the next major structural obligation.

11. No evidence in this initial sample indicates that KTLean is a collection of unconstrained target fits. The corpus contains multiple interacting structures whose agreement creates substantial internal overdetermination.

12. Formal proof count measures output, not correspondence with reality. Source provenance, independence, frame status, and empirical interpretation remain separate audit obligations.

---

# 9. Immediate Open Obligations

The following obligations should be audited or constructed next.

## 9.1 Concrete monad symmetry

- define the concrete PSL(2,7) object;
- formalize its action on Fano points;
- lift the action to glyphs;
- lift the action to walk realizations;
- construct the concrete action on monads;
- revisit earlier monad theorems under that action.

## 9.2 Cayley–Dickson target hardening

- define the doubled norm;
- prove or disprove norm composition;
- exhibit a concrete nonzero associator witness;
- classify the exact field assumptions required;
- record `#print axioms` for the endpoint theorems.

## 9.3 Pascal forcing

Freeze an independently defined Pascal-mod-3 routing datum and test:

```text
Pascal-derived selector/route/orientation
=
Cayley–Dickson selector/route/orientation.
```

The Pascal-side definition must not refer to the Cayley–Dickson target.

## 9.4 Full Hurwitz scope

Separate clearly:

1. reversibility from anisotropic multiplicative norm;
2. structural Cayley–Dickson doubling;
3. composition at dimension 8;
4. failure of composition beyond dimension 8;
5. full classification of finite-dimensional unital composition algebras.

## 9.5 Source mapping

Complete the canonical source mapping for:

- `AdmissibleOperation.Operation`;
- `OperationNormalForm.LawfulFramedOperation`;
- `KTGlyph.Glyph`;
- `KTMonad.Monad`;
- the four monad walk realizations;
- `CayleyDicksonQuaternion.cdMul`;
- quasi-stochasticity and residue sensitivity.

---

# 10. Next Critical Theorem Audit Targets

The next audit pass should include:

- the terminal theorem of `FanoRecovery`;
- the normal-form equivalence in `OperationNormalForm`;
- the terminal theorem of `SpinorIrreducibility`;
- the terminal theorem of `PrimitiveRecurrence`;
- `MonadOrbit.physicallyAdmissible_factors_through_orbit`;
- `MonadProjection.ScalarProjection.constant_on_orbit`;
- the strongest tokenization endpoint;
- the deepest memory-escrow recovery theorem.

For each target, record:

1. exact theorem statement;
2. source provenance;
3. whether the statement was frozen before proof;
4. whether any substantive definition changed during proof;
5. verbatim `#print axioms` output;
6. stronger claims not established;
7. frame status;
8. tokenization status;
9. failure condition;
10. counterfactual impact on the project.

---

# 11. Epistemic Direction of Fit

KTLean is a formal program intended to approximate the structure of reality.

Lean establishes that conclusions follow from encoded definitions, assumptions, and imported results.

Lean does not establish that those definitions correspond to the universe.

The direction of fit is one-way:

> The program bends to reality. Reality does not bend to preserve the program.

A theorem may therefore be:

- formally correct;
- correctly scoped;
- source-faithful;
- frame-invariant;
- and still physically wrong.

The universe remains the referent and final arbiter.

The theorem count measures formal output.

The audit measures epistemic weight.