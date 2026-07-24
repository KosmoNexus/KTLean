import KTLean.GlyphSpectralAlphaBoundary
import KTLean.GlyphForcingFrobeniusIdentification
import Mathlib.Tactic

/-!
# The Frobenius Boundary Pair 23 and 46

## Formal status

**Level 2 — Exact finite derivation from the visible Fano-pair count,
the middle Frobenius stride, and binary orientation.**

The forced Fano carrier supplies twenty-one visible unordered pairs:

    C(7,2) = 21.

The middle forced Frobenius role carries stride two. Under additive
triadic completion:

    21, 2 ↦ 23.

Binary orientation then supplies the doubled resonance:

    2 × 23 = 46.

Thus the middle boundary pair is exactly:

    23, 46.

No primality theorem is required for the construction. Primality of
23 is proved separately as an arithmetic property of the forced value.
-/

namespace GlyphSpectralFrobeniusBoundary

open GlyphSpectralTriadicEngine
open GlyphForcingTriadicRole
open GlyphForcingFrobeniusIdentification

/--
The middle forced Frobenius role.
-/
def middleBoundaryRole :
    ForcedRole :=
  1

/--
The middle role carries Frobenius step two.
-/
theorem middleBoundaryRole_step :
    stepOfForcedRole middleBoundaryRole =
      FrobeniusOrbit.Step.two := by

  rfl

/--
The numerical stride represented by each Frobenius step.
-/
def frobeniusStride :
    FrobeniusOrbit.Step →
      Nat

  | .one =>
      1

  | .two =>
      2

  | .four =>
      4

/--
The middle boundary role has numerical stride two.
-/
theorem middleBoundaryStride_eq_two :
    frobeniusStride
        (stepOfForcedRole middleBoundaryRole) =
      2 := by

  rfl

/--
Additive closure on natural-number boundary counts.
-/
def boundaryAdditiveClosure :
    ClosureLaw Nat :=
  fun x y =>
    x + y

/--
The base boundary count is the already derived visible-pair count.
-/
def baseBoundaryCount :
    Nat :=
  GlyphSpectralBoundaryCombinatorics.visiblePairCount

/--
The middle Frobenius boundary value is the unique additive completion
of the visible-pair count and stride two.
-/
def frobeniusBoundaryPrime :
    Nat :=

  boundaryAdditiveClosure
    baseBoundaryCount
    (
      frobeniusStride
        (
          stepOfForcedRole
            middleBoundaryRole
        )
    )

/--
The visible-pair count and middle Frobenius stride force 23.
-/
theorem frobeniusBoundaryPrime_eq_twentyThree :
    frobeniusBoundaryPrime =
      23 := by

  unfold frobeniusBoundaryPrime
  unfold boundaryAdditiveClosure
  unfold baseBoundaryCount

  rw [
    GlyphSpectralBoundaryCombinatorics.visiblePairCount_eq_twentyOne
  ]

  rfl

/--
The completion to 23 is unique.
-/
theorem unique_frobeniusBoundaryPrime :
    ∃! z : Nat,
      Completes
        boundaryAdditiveClosure
        baseBoundaryCount
        (
          frobeniusStride
            (
              stepOfForcedRole
                middleBoundaryRole
            )
        )
        z := by

  exact
    existsUnique_completion
      boundaryAdditiveClosure
      baseBoundaryCount
      (
        frobeniusStride
          (
            stepOfForcedRole
              middleBoundaryRole
          )
      )

/--
The forced value 23 is prime.
-/
theorem frobeniusBoundaryPrime_isPrime :
    Nat.Prime frobeniusBoundaryPrime := by

  rw [
    frobeniusBoundaryPrime_eq_twentyThree
  ]

  norm_num

/--
Binary orientation doubles the middle boundary value.
-/
def compositeResonance :
    Nat :=
  2 * frobeniusBoundaryPrime

/--
The oriented composite resonance is exactly 46.
-/
theorem compositeResonance_eq_fortySix :
    compositeResonance =
      46 := by

  unfold compositeResonance

  rw [
    frobeniusBoundaryPrime_eq_twentyThree
  ]

/--
The resonance is exactly twice its unoriented boundary value.
-/
theorem resonance_is_oriented_double :
    compositeResonance =
      2 * frobeniusBoundaryPrime := by

  rfl

/--
The two canonical spectrum positions carry 23 and 46.
-/
theorem frobenius_boundary_registered_positions :
    GlyphSpectrum.values[38]? =
        some (.natural 23)
      ∧
    GlyphSpectrum.values[39]? =
        some (.natural 46) := by

  native_decide

/--
The pair occurs in the registered boundary block.
-/
theorem registered_frobenius_boundary_pair :
    (
      GlyphSpectralBoundaryCombinatorics.registeredBoundaryBlock.drop 2
    ).take 2 =
      [
        .natural 23,
        .natural 46
      ] := by

  native_decide

/--
The finite boundary chain now accounts for all six registered values.
-/
theorem complete_boundary_arithmetic :
    GlyphSpectralBoundaryCombinatorics.visiblePairCount =
        21
      ∧
    GlyphSpectralBoundaryCombinatorics.orientedPairCount =
        42
      ∧
    frobeniusBoundaryPrime =
        23
      ∧
    compositeResonance =
        46
      ∧
    GlyphSpectralBoundaryCombinatorics.sevenfoldClosureDepth =
        147
      ∧
    GlyphSpectralAlphaBoundary.usableProjectionChannels =
        137 := by

  exact
    ⟨
      GlyphSpectralBoundaryCombinatorics.visiblePairCount_eq_twentyOne,
      GlyphSpectralBoundaryCombinatorics.orientedPairCount_eq_fortyTwo,
      frobeniusBoundaryPrime_eq_twentyThree,
      compositeResonance_eq_fortySix,
      GlyphSpectralBoundaryCombinatorics.sevenfoldClosureDepth_eq_oneFortySeven,
      GlyphSpectralAlphaBoundary.usableProjectionChannels_eq_oneThirtySeven
    ⟩

/--
Capstone theorem.

The middle Frobenius stride completes the visible Fano-pair count:

    21 + 2 = 23.

Binary orientation then produces:

    2 × 23 = 46.

These are exactly the two middle entries of the canonical boundary
block.
-/
theorem middle_frobenius_closure_forces_23_46 :
    (∃! z : Nat,
      Completes
        boundaryAdditiveClosure
        baseBoundaryCount
        (
          frobeniusStride
            (
              stepOfForcedRole
                middleBoundaryRole
            )
        )
        z)
      ∧
    frobeniusBoundaryPrime =
        23
      ∧
    Nat.Prime frobeniusBoundaryPrime
      ∧
    compositeResonance =
        46
      ∧
    GlyphSpectrum.values[38]? =
        some (.natural 23)
      ∧
    GlyphSpectrum.values[39]? =
        some (.natural 46) := by

  exact
    ⟨
      unique_frobeniusBoundaryPrime,
      frobeniusBoundaryPrime_eq_twentyThree,
      frobeniusBoundaryPrime_isPrime,
      compositeResonance_eq_fortySix,
      frobenius_boundary_registered_positions.1,
      frobenius_boundary_registered_positions.2
    ⟩

end GlyphSpectralFrobeniusBoundary

#check GlyphSpectralFrobeniusBoundary.middleBoundaryRole
#check GlyphSpectralFrobeniusBoundary.middleBoundaryRole_step
#check GlyphSpectralFrobeniusBoundary.frobeniusStride
#check GlyphSpectralFrobeniusBoundary.middleBoundaryStride_eq_two
#check GlyphSpectralFrobeniusBoundary.boundaryAdditiveClosure
#check GlyphSpectralFrobeniusBoundary.frobeniusBoundaryPrime
#check GlyphSpectralFrobeniusBoundary.frobeniusBoundaryPrime_eq_twentyThree
#check GlyphSpectralFrobeniusBoundary.unique_frobeniusBoundaryPrime
#check GlyphSpectralFrobeniusBoundary.frobeniusBoundaryPrime_isPrime
#check GlyphSpectralFrobeniusBoundary.compositeResonance
#check GlyphSpectralFrobeniusBoundary.compositeResonance_eq_fortySix
#check GlyphSpectralFrobeniusBoundary.frobenius_boundary_registered_positions
#check GlyphSpectralFrobeniusBoundary.complete_boundary_arithmetic
#check GlyphSpectralFrobeniusBoundary.middle_frobenius_closure_forces_23_46
