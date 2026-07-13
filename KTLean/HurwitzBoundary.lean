import KTLean.CayleyDicksonQuaternion
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The Hurwitz Dimensional Boundary

This module records the dimensional facts required by
the routed-quaternion reconstruction program.

It does not yet formalize the full Hurwitz classification
theorem. Instead, it certifies the dimensions of the
objects already constructed in KTLean:

    dim ℍ = 4
    dim (ℍ × ℍ) = 8

The second equality places the two-quaternion
Cayley–Dickson carrier at the maximal dimension appearing
in the classical Hurwitz list:

    1, 2, 4, 8.

The distinction is important:

- this module proves the dimensions of the KTLean objects;
- a later theorem must establish that no other finite
  dimensions admit the required composition/division
  structure.
-/

open scoped Quaternion

universe u

namespace HurwitzBoundary


variable {R : Type u}
variable [Field R]


/--
The four classical dimensions occurring in the
Hurwitz classification.
-/
def IsHurwitzDimension
    (n : ℕ) :
    Prop :=
  n = 1 ∨
  n = 2 ∨
  n = 4 ∨
  n = 8


/--
The maximal dimension in the classical Hurwitz list.
-/
def maximalHurwitzDimension :
    ℕ :=
  8


/--
The quaternion algebra has scalar dimension four.
-/
theorem quaternion_finrank :
    Module.finrank R ℍ[R] = 4 := by
  exact Quaternion.finrank_eq_four


/--
The two-quaternion Cayley–Dickson carrier has
scalar dimension eight.
-/
theorem carrier_finrank :
    Module.finrank R
      (CayleyDicksonQuaternion.Carrier (R := R)) =
        8 := by

  change
    Module.finrank R (ℍ[R] × ℍ[R]) = 8

  rw [
    Module.finrank_prod,
    Quaternion.finrank_eq_four
  ]


/--
Quaternion dimension belongs to the Hurwitz list.
-/
theorem quaternion_is_hurwitz_dimension :
    IsHurwitzDimension
      (Module.finrank R ℍ[R]) := by

  rw [quaternion_finrank]

  exact
    Or.inr
      (Or.inr
        (Or.inl rfl))


/--
The two-quaternion carrier dimension belongs to
the Hurwitz list.
-/
theorem carrier_is_hurwitz_dimension :
    IsHurwitzDimension
      (
        Module.finrank R
          (CayleyDicksonQuaternion.Carrier (R := R))
      ) := by

  rw [carrier_finrank]

  exact
    Or.inr
      (Or.inr
        (Or.inr rfl))


/--
The Cayley–Dickson carrier reaches the maximal
dimension recorded by the Hurwitz list.
-/
theorem carrier_reaches_maximal_boundary :
    Module.finrank R
      (CayleyDicksonQuaternion.Carrier (R := R)) =
        maximalHurwitzDimension := by

  simpa [maximalHurwitzDimension]
    using carrier_finrank (R := R)


/--
The passage from one quaternion block to two quaternion
blocks doubles the scalar dimension from four to eight.
-/
theorem carrier_is_quaternion_doubling :
    Module.finrank R
      (CayleyDicksonQuaternion.Carrier (R := R)) =
        2 * Module.finrank R ℍ[R] := by

  rw [
    carrier_finrank,
    quaternion_finrank
  ]


end HurwitzBoundary


#check HurwitzBoundary.IsHurwitzDimension
#check HurwitzBoundary.maximalHurwitzDimension
#check HurwitzBoundary.quaternion_finrank
#check HurwitzBoundary.carrier_finrank
#check HurwitzBoundary.quaternion_is_hurwitz_dimension
#check HurwitzBoundary.carrier_is_hurwitz_dimension
#check HurwitzBoundary.carrier_reaches_maximal_boundary
#check HurwitzBoundary.carrier_is_quaternion_doubling
