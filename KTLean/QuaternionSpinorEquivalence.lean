import Mathlib.Algebra.Quaternion
import KTLean.GenericDoubling
import KTLean.SpinorClosure

/-!
# Quaternion–Spinor Equivalence

This module identifies one Cayley–Dickson doubling of the complex
numbers with two-component complex spinors and with real quaternions.

## Formal status

**Level 2 — Carrier reconstruction and convention locking.**

The multiplication convention is frozen as

    q = z + w * j

where `z,w ∈ ℂ`.

Writing

    z = a + b i
    w = c + d i

the corresponding quaternion is

    a + b i + c j + d k.

This convention is selected because it matches the generic
Cayley–Dickson product

    (z,w)(u,v)
      = (z*u - conj(v)*w,
         v*z + w*conj(u)).

This file first proves the carrier equivalences. Multiplication,
involution, and norm compatibility are subsequent theorem layers.
-/

namespace QuaternionSpinorEquivalence

open scoped Quaternion

/--
One complex Cayley–Dickson doubling.
-/
abbrev ComplexDouble :=
  GenericDoubling.Double ℂ

/--
A complex double and a two-component spinor carry exactly the same two
complex coordinates.
-/
def doubleSpinorEquiv :
    ComplexDouble ≃ SpinorClosure.WeylSpinor where

  toFun x :=
    {
      upper := x.fst
      lower := x.snd
    }

  invFun ψ :=
    {
      fst := ψ.upper
      snd := ψ.lower
    }

  left_inv x := by
    cases x
    rfl

  right_inv ψ := by
    cases ψ
    rfl

/--
The frozen quaternion convention:

    (z,w) ↦ z + w*j.

In real coordinates this is

    (z.re, z.im, w.re, w.im).
-/
def doubleQuaternionEquiv :
    ComplexDouble ≃ ℍ[ℝ] where

  toFun x :=
    {
      re := x.fst.re
      imI := x.fst.im
      imJ := x.snd.re
      imK := x.snd.im
    }

  invFun q :=
    {
      fst := ⟨q.re, q.imI⟩
      snd := ⟨q.imJ, q.imK⟩
    }

  left_inv x := by
    cases x with
    | mk z w =>
        cases z
        cases w
        rfl

  right_inv q := by
    cases q
    rfl

/--
A two-component complex spinor is therefore equivalent, as a carrier,
to a real quaternion.
-/
def spinorQuaternionEquiv :
    SpinorClosure.WeylSpinor ≃ ℍ[ℝ] :=
  doubleSpinorEquiv.symm.trans
    doubleQuaternionEquiv

@[simp]
theorem doubleSpinorEquiv_upper
    (x : ComplexDouble) :
    (doubleSpinorEquiv x).upper =
      x.fst := by
  rfl

@[simp]
theorem doubleSpinorEquiv_lower
    (x : ComplexDouble) :
    (doubleSpinorEquiv x).lower =
      x.snd := by
  rfl

@[simp]
theorem doubleQuaternionEquiv_re
    (x : ComplexDouble) :
    (doubleQuaternionEquiv x).re =
      x.fst.re := by
  rfl

@[simp]
theorem doubleQuaternionEquiv_imI
    (x : ComplexDouble) :
    (doubleQuaternionEquiv x).imI =
      x.fst.im := by
  rfl

@[simp]
theorem doubleQuaternionEquiv_imJ
    (x : ComplexDouble) :
    (doubleQuaternionEquiv x).imJ =
      x.snd.re := by
  rfl

@[simp]
theorem doubleQuaternionEquiv_imK
    (x : ComplexDouble) :
    (doubleQuaternionEquiv x).imK =
      x.snd.im := by
  rfl

end QuaternionSpinorEquivalence

#check QuaternionSpinorEquivalence.ComplexDouble
#check QuaternionSpinorEquivalence.doubleSpinorEquiv
#check QuaternionSpinorEquivalence.doubleQuaternionEquiv
#check QuaternionSpinorEquivalence.spinorQuaternionEquiv

namespace QuaternionSpinorEquivalence

/-!
## QSE1: Algebra compatibility
-/

/--
The frozen quaternion identification preserves involution.

For the doubled complex carrier,

    star (z,w) = (conj z, -w),

which corresponds exactly to quaternion conjugation under

    q = z + w*j.
-/
theorem doubleQuaternionEquiv_map_star
    (x : ComplexDouble) :
    doubleQuaternionEquiv (star x) =
      star (doubleQuaternionEquiv x) := by

  apply Quaternion.ext

  · simp [
      doubleQuaternionEquiv
    ]

  · simp [
      doubleQuaternionEquiv
    ]

  · simp [
      doubleQuaternionEquiv
    ]

  · simp [
      doubleQuaternionEquiv
    ]

/--
The frozen quaternion identification preserves multiplication.

This theorem is the decisive convention check. It proves that the
generic Cayley–Dickson product on `Double ℂ` is exactly standard
quaternion multiplication under

    q = z + w*j.
-/
theorem doubleQuaternionEquiv_map_mul
    (x y : ComplexDouble) :
    doubleQuaternionEquiv (x * y) =
      doubleQuaternionEquiv x *
        doubleQuaternionEquiv y := by

  apply Quaternion.ext

  · simp [
      doubleQuaternionEquiv,
      Quaternion.re_mul,
      Complex.mul_re,
      Complex.mul_im,
      Complex.conj_re,
      Complex.conj_im
    ]
    ring

  · simp [
      doubleQuaternionEquiv,
      Quaternion.imI_mul,
      Complex.mul_re,
      Complex.mul_im,
      Complex.conj_re,
      Complex.conj_im
    ]
    ring

  · simp [
      doubleQuaternionEquiv,
      Quaternion.imJ_mul,
      Complex.mul_re,
      Complex.mul_im,
      Complex.conj_re,
      Complex.conj_im
    ]
    ring

  · simp [
      doubleQuaternionEquiv,
      Quaternion.imK_mul,
      Complex.mul_re,
      Complex.mul_im,
      Complex.conj_re,
      Complex.conj_im
    ]
    ring

end QuaternionSpinorEquivalence

#check QuaternionSpinorEquivalence.doubleQuaternionEquiv_map_star
#check QuaternionSpinorEquivalence.doubleQuaternionEquiv_map_mul

namespace QuaternionSpinorEquivalence

/--
Quaternion norm-square agrees with the sum of the two complex
norm-squares under the frozen identification

    q = z + w*j.
-/
theorem doubleQuaternionEquiv_normSq
    (x : ComplexDouble) :
    Quaternion.normSq
        (doubleQuaternionEquiv x)
      =
    Complex.normSq x.fst +
      Complex.normSq x.snd := by

  rw [Quaternion.normSq_def]

  simp [
    doubleQuaternionEquiv,
    Quaternion.re_mul,
    Quaternion.re_star,
    Quaternion.imI_star,
    Quaternion.imJ_star,
    Quaternion.imK_star,
    Complex.normSq_apply
  ]

  ring

/--
The spinor norm-square is exactly the quaternion norm-square under the
spinor–quaternion equivalence.
-/
theorem spinorQuaternionEquiv_normSq
    (ψ : SpinorClosure.WeylSpinor) :
    Quaternion.normSq
        (spinorQuaternionEquiv ψ)
      =
    SpinorClosure.normSq ψ := by

  change
    Quaternion.normSq
        (doubleQuaternionEquiv
          {
            fst := ψ.upper
            snd := ψ.lower
          })
      =
    SpinorClosure.normSq ψ

  rw [doubleQuaternionEquiv_normSq]

  rfl

end QuaternionSpinorEquivalence

#check QuaternionSpinorEquivalence.doubleQuaternionEquiv_normSq
#check QuaternionSpinorEquivalence.spinorQuaternionEquiv_normSq
