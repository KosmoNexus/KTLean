import Mathlib.Data.Complex.Basic

/-!
# Spinor Closure

This module begins the formal study of two-component complex spinors
as candidate state spaces for primitive KT closure paths.

## Formal status

**Level 1 — Encoding, with elementary reconstruction.**

This module defines:

- a two-component complex spinor;
- its squared norm;
- normalized spinors;
- its four real coordinates;
- the unit-three-sphere equation in those coordinates.

It does not yet prove:

- that a primitive KT path is necessarily spinorial;
- that its canonical geometric measure is `2 * π^2`;
- that seven such paths are forced.

Those remain separate obligations.
-/

namespace SpinorClosure

/--
A two-component complex spinor.

No chirality convention is imposed at this level.
-/
structure WeylSpinor where
  upper : ℂ
  lower : ℂ

/--
The squared norm of a two-component complex spinor.
-/
def normSq
    (ψ : WeylSpinor) :
    ℝ :=
  Complex.normSq ψ.upper +
    Complex.normSq ψ.lower

/--
A normalized two-component spinor.
-/
abbrev NormalizedSpinor :=
  { ψ : WeylSpinor // normSq ψ = 1 }

/--
The four real coordinates carried by a two-component complex spinor.
-/
structure RealFour where
  x₀ : ℝ
  x₁ : ℝ
  x₂ : ℝ
  x₃ : ℝ

/--
The real-coordinate representation of a two-component complex spinor.
-/
def toRealFour
    (ψ : WeylSpinor) :
    RealFour where
  x₀ := ψ.upper.re
  x₁ := ψ.upper.im
  x₂ := ψ.lower.re
  x₃ := ψ.lower.im

/--
The squared Euclidean radius in four real coordinates.
-/
def RealFour.radiusSq
    (x : RealFour) :
    ℝ :=
  x.x₀ ^ 2 +
    x.x₁ ^ 2 +
    x.x₂ ^ 2 +
    x.x₃ ^ 2

/--
The unit three-sphere represented as the unit-radius locus in four real
coordinates.
-/
abbrev UnitThreeSphere :=
  { x : RealFour // x.radiusSq = 1 }

/--
The spinor squared norm agrees with the squared Euclidean radius of its
four real coordinates.
-/
theorem radiusSq_toRealFour
    (ψ : WeylSpinor) :
    (toRealFour ψ).radiusSq =
      normSq ψ := by

  simp [
    RealFour.radiusSq,
    toRealFour,
    normSq,
    Complex.normSq,
    pow_two,
    add_assoc
  ]

/--
Every normalized spinor determines a point on the unit three-sphere.
-/
def normalizedToSphere
    (ψ : NormalizedSpinor) :
    UnitThreeSphere :=

  ⟨
    toRealFour ψ.1,
    by
      rw [radiusSq_toRealFour]
      exact ψ.2
  ⟩

@[simp]
theorem normalizedToSphere_coordinates
    (ψ : NormalizedSpinor) :
    (normalizedToSphere ψ).1 =
      toRealFour ψ.1 := by
  rfl

/--
Normalization of a two-component complex spinor is exactly the
unit-three-sphere equation in its four real coordinates.
-/
theorem normalized_iff_on_unitThreeSphere
    (ψ : WeylSpinor) :
    normSq ψ = 1
      ↔
    (toRealFour ψ).radiusSq = 1 := by

  rw [radiusSq_toRealFour]

end SpinorClosure

#check SpinorClosure.WeylSpinor
#check SpinorClosure.NormalizedSpinor
#check SpinorClosure.UnitThreeSphere
#check SpinorClosure.normalizedToSphere
#check SpinorClosure.normalized_iff_on_unitThreeSphere

namespace SpinorClosure

/-!
## Full normalized-spinor / unit-three-sphere equivalence
-/

/--
Reconstruct a two-component complex spinor from four real coordinates.

The coordinate convention is

    (x₀,x₁,x₂,x₃)
      ↦
    (x₀ + x₁ i, x₂ + x₃ i).
-/
def RealFour.toSpinor
    (x : RealFour) :
    WeylSpinor where
  upper := ⟨x.x₀, x.x₁⟩
  lower := ⟨x.x₂, x.x₃⟩

@[simp]
theorem toRealFour_toSpinor
    (x : RealFour) :
    toRealFour x.toSpinor = x := by
  cases x
  rfl

@[simp]
theorem RealFour.toSpinor_toRealFour
    (ψ : WeylSpinor) :
    (toRealFour ψ).toSpinor = ψ := by
  cases ψ with
  | mk upper lower =>
      cases upper
      cases lower
      rfl

/--
Every point of the unit three-sphere reconstructs a normalized spinor.
-/
def sphereToNormalized
    (x : UnitThreeSphere) :
    NormalizedSpinor :=
  ⟨
    x.1.toSpinor,
    by
      rw [← radiusSq_toRealFour]
      rw [toRealFour_toSpinor]
      exact x.2
  ⟩

@[simp]
theorem sphereToNormalized_value
    (x : UnitThreeSphere) :
    (sphereToNormalized x).1 =
      x.1.toSpinor := by
  rfl

@[simp]
theorem normalizedToSphere_sphereToNormalized
    (x : UnitThreeSphere) :
    normalizedToSphere (sphereToNormalized x) = x := by
  apply Subtype.ext
  exact toRealFour_toSpinor x.1

@[simp]
theorem sphereToNormalized_normalizedToSphere
    (ψ : NormalizedSpinor) :
    sphereToNormalized (normalizedToSphere ψ) = ψ := by
  apply Subtype.ext
  exact RealFour.toSpinor_toRealFour ψ.1

/--
Normalized two-component complex spinors are exactly the unit
three-sphere in four real coordinates.
-/
def normalizedSpinorEquivSphere :
    NormalizedSpinor ≃ UnitThreeSphere where
  toFun := normalizedToSphere
  invFun := sphereToNormalized
  left_inv := sphereToNormalized_normalizedToSphere
  right_inv := normalizedToSphere_sphereToNormalized

end SpinorClosure

#check SpinorClosure.RealFour.toSpinor
#check SpinorClosure.sphereToNormalized
#check SpinorClosure.normalizedSpinorEquivSphere
