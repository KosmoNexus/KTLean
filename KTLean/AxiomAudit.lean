import KTLean.MonadProjection
import KTLean.HurwitzBoundary
import KTLean.CayleyDicksonQuaternion
import KTLean.RoutedResidueSensitive

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
