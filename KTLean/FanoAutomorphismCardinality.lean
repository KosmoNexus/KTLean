import KTLean.FanoAutomorphism
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Cardinality of the Fano automorphism group

The intrinsic automorphism group of the Fano completion
structure consists of all permutations of the seven Fano
points that preserve the completion operation.

Because the point set is finite, these automorphisms can
be enumerated directly. Their cardinality is 168.

This theorem is independent of any prior identification
with `GL(3, 2)` or `PSL(2, 7)`.
-/

namespace FanoAutomorphismCardinality

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/--
Preservation of Fano completion is decidable because it
is a finite statement over the seven Fano points.
-/
local instance preservesCompletionDecidable :
    DecidablePred
      FanoAutomorphism.PreservesCompletion := by
  intro σ
  unfold FanoAutomorphism.PreservesCompletion
  infer_instance

/--
Membership in the intrinsic Fano automorphism subgroup
is decidable.
-/
local instance groupMembershipDecidable :
    DecidablePred
      (fun σ : Equiv.Perm Fano.Point =>
        σ ∈ FanoAutomorphism.group) := by
  intro σ
  change Decidable
    (FanoAutomorphism.PreservesCompletion σ)
  infer_instance

/--
The intrinsic automorphism group of the Fano completion
structure has exactly 168 elements.
-/
theorem card_automorphism :
    Fintype.card
      FanoAutomorphism.Automorphism = 168 := by
  native_decide


  /-!

## Verification note

The theorem `card_automorphism` is proved by `native_decide`.

This gives a compiled finite verification of the proposition

    Fintype.card FanoAutomorphism.Automorphism = 168.

The automorphism count was also independently confirmed by direct
evaluation of the finite completion-preserving permutation subgroup.

Its current proof is computational: Lean enumerates the permutations
of the seven Fano points and verifies preservation of the Fano
completion law.

The separate module `FanoFrame` independently proves that the type of
ordered noncollinear Fano frames also has cardinality 168. A future
module will construct the explicit correspondence between these two
168-element structures.

The present theorem is retained as a valid, reproducible finite proof
of the intrinsic Fano automorphism-group cardinality.
-/

end FanoAutomorphismCardinality
