import KTLean.MonadProjection
import KTLean.BraidedQuaternion
import KTLean.YangBaxterRouting
import KTLean.MemoryEscrowRouted
import KTLean.BraidedQuaternion
import KTLean.YangBaxterRouting
import KTLean.MemoryEscrowRouted
import KTLean.HurwitzBoundary
import KTLean.CayleyDicksonQuaternion
import KTLean.RoutedResidueSensitive
import KTLean.FanoRecovery
import KTLean.OperationNormalForm
import KTLean.PrimitiveRecurrence
import KTLean.SpinorIrreducibility
import KTLean.MemoryEscrow
import KTLean.RoutedTokenization

/-!
# KTLean Axiom Audit

This file records the logical dependencies of selected load-bearing
and terminal theorems.

The terminal output from compiling this file should be copied verbatim
into the verification manifest.

`#print axioms` audits logical dependencies. It does not by itself audit:

- fidelity of definitions to source material;
- independence from target values;
- physical interpretation;
- definitional drift;
- frame invariance unless encoded in the audited theorem.
-/

/-!
## Glyph and monad cardinality
-/

#print axioms KTGlyph.card_glyph
#print axioms KTMonad.card_monad
#print axioms KTMonad.card_monad_eq_glyph_times_four
#print axioms KTMonad.card_monad_prime_structure

/-!
## Quaternion composition and Cayley–Dickson routing
-/

#print axioms QuaternionWitness.composition_leftMul_injective
#print axioms QuaternionWitness.composition_existsUnique_left_solution

#print axioms CayleyDicksonQuaternion.routedMul_eq_cdMul

/-!
## Hurwitz boundary

These theorems certify dimensions of constructed objects.
They do not constitute the full Hurwitz classification theorem.
-/

#print axioms HurwitzBoundary.quaternion_finrank
#print axioms HurwitzBoundary.carrier_finrank
#print axioms HurwitzBoundary.carrier_reaches_maximal_boundary
#print axioms HurwitzBoundary.carrier_is_quaternion_doubling

/-!
## Quasi-stochastic routed dynamics
-/

#print axioms KTLean.RoutedResidueSensitive.witness_states_ne
#print axioms KTLean.RoutedResidueSensitive.witness_residues_ne
#print axioms KTLean.RoutedResidueSensitive.witness_next_observations_ne
#print axioms KTLean.RoutedResidueSensitive.dynamics_noninjectiveView
#print axioms KTLean.RoutedResidueSensitive.dynamics_residueSensitive
#print axioms KTLean.RoutedResidueSensitive.dynamics_quasiStochastic
#print axioms KTLean.RoutedResidueSensitive.dynamics_not_visiblyClosed
#print axioms KTLean.RoutedResidueSensitive.no_complete_visibleStep

/-!
## Monad orbit and projection layer
-/

#print axioms KTLean.MonadOrbit.physicallyAdmissible_factors_through_orbit
#print axioms KTLean.MonadProjection.ScalarProjection.constant_on_orbit
#print axioms KTLean.MonadProjection.ScalarProjection.onOrbitSpace_classOf
#print axioms KTLean.MonadProjection.ScalarProjection.eq_of_same_orbit_class
#print axioms KTLean.MonadProjection.ScalarProjection.inCoordinates_transport

/-!
## Fano recovery and routing residue

These theorems distinguish exact recovery of Fano
incidence from the residual routing information that
recovery does not determine.
-/

#print axioms FanoRecovery.recoveredLines_eq_fanoLines
#print axioms FanoRecovery.braid_paths_recover_same_exteriorBlock
#print axioms FanoRecovery.structured_route_residue_exists
#print axioms FanoRecovery.recovery_ignores_route_residue


/-!
## Lawful operation normal form

These theorems audit the semantic classification of
lawful framed operations by the 42 coordinate triples.

The classification remains relative to the explicit
framed Fano law.
-/

#print axioms OperationNormalForm.unique_normal_form
#print axioms OperationNormalForm.lawful_operation_card
#print axioms OperationNormalForm.lawful_operation_card_prime_structure


/-!
## Primitive recurrence boundary

These theorems distinguish primitive recurrence from
arithmetic primality and record the double-cover
factorization boundary.
-/

#print axioms PrimitiveRecurrence.double_cover_arithmetic_dichotomy
#print axioms PrimitiveRecurrence.primitive_recurrence_not_sufficient_for_primality
#print axioms PrimitiveRecurrence.recurrence_boundary


/-!
## Spinor irreducibility

These theorems audit the additional indecomposability
hypothesis required to pass from primitive recurrence
to primality.
-/

#print axioms SpinorIrreducibility.prime_of_primitive_indecomposable
#print axioms SpinorIrreducibility.PrimeMode.period_prime
#print axioms SpinorIrreducibility.PrimeMode.no_proper_nontrivial_divisor
#print axioms SpinorIrreducibility.spinor_prime_boundary


/-!
## Memory escrow

These theorems audit exact recovery of complete states
from retained transition history.
-/

#print axioms ReversibleStep.history_recovers_initial
#print axioms ReversibleStep.recoverN_stepN
#print axioms ReversibleStep.stepN_recoverN
#print axioms ReversibleStep.history_eq_stepN


/-!
## Routed tokenization

These theorems audit the reversible encoding between
complete routed states and dimensional token states,
including recovery through token history.
-/

#print axioms RoutedTokenization.encode_bijective
#print axioms RoutedTokenization.completeStep_conjugate
#print axioms RoutedTokenization.tokenStep_bijective
#print axioms RoutedTokenization.token_recovery
#print axioms RoutedTokenization.tokenHistory_recovers_initial
#print axioms RoutedTokenization.complete_eq_of_token_eq

/-!
## Forcing-round execution gate

Terminal results required by Phase 0.2 of
`KTLean_Forcing_Round_Work_Plan.md`.
-/

#print axioms BraidedQuaternion.pascalRoutedMul_eq_cdMul
#print axioms YangBaxterRouting.routedExchange_satisfies_yang_baxter
#print axioms MemoryEscrowRouted.complete_state_exactly_visible_plus_escrow
