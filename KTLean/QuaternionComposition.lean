import Mathlib.Algebra.Quaternion
import KTLean.OrderedComposition

/-!
# Quaternions as an Ordered Composition Algebra

This module packages the quaternion norm-square as the
quadratic norm required by `CompositionCore`.

The resulting structure is a concrete positive-definite
composition algebra witness.

The progression is:

    quaternion norm-square
        → quadratic form
        → multiplicative composition core
        → positive-definite ordered composition core
-/

open scoped Quaternion

universe u



namespace QuaternionWitness


variable {R : Type u}
variable [Field R]
variable [LinearOrder R]
variable [IsStrictOrderedRing R]


/--
The polar expression associated with quaternion norm-square.

For quaternions, the polar form is twice the real part of
`x * star y`.
-/
theorem normSq_polar
    (x y : ℍ[R]) :
    QuadraticMap.polar
        (fun q : ℍ[R] => Quaternion.normSq q)
        x
        y =
      2 * (x * star y).re := by

  unfold QuadraticMap.polar
  simp only []
  rw [Quaternion.normSq_add]
  ring


/--
Quaternion norm-square, packaged as a quadratic form.
-/
def normSqForm :
    QuadraticForm R ℍ[R] :=

  QuadraticMap.ofPolar
    (fun q : ℍ[R] => Quaternion.normSq q)

    (by
      intro r q

      rw [Quaternion.normSq_smul]

      simp only [
        pow_two,
        smul_eq_mul
      ])

    (by
      intro x x' y

      rw [
        normSq_polar,
        normSq_polar,
        normSq_polar
      ]

      simp only [
        add_mul,
        Quaternion.re_add
      ]

      ring)

    (by
      intro r x y

      rw [
        normSq_polar,
        normSq_polar
      ]

      simp only [
        Algebra.smul_mul_assoc,
        Quaternion.re_smul,
        smul_eq_mul
      ]

      ring)


/--
Evaluation of the quadratic form agrees definitionally
with Mathlib's quaternion norm-square.
-/
@[simp]
theorem normSqForm_apply
    (q : ℍ[R]) :
    normSqForm (R := R) q =
      Quaternion.normSq q := by

  rfl


/--
Quaternions form a composition core under their
standard norm-square.
-/
def compositionCore :
    CompositionCore R ℍ[R] where

  two_ne_zero := by
    exact two_ne_zero

  normSq :=
    normSqForm

  normSq_one := by
    change Quaternion.normSq (1 : ℍ[R]) = 1
    exact Quaternion.normSq.map_one

  normSq_mul := by
    intro x y

    change
      Quaternion.normSq (x * y) =
        Quaternion.normSq x *
          Quaternion.normSq y

    exact Quaternion.normSq.map_mul x y


/--
The norm-square carried by the quaternion composition
core is Mathlib's quaternion norm-square.
-/
@[simp]
theorem compositionCore_normSq
    (q : ℍ[R]) :
    (compositionCore (R := R)).normSq q =
      Quaternion.normSq q := by

  rfl


/--
Quaternions form a positive-definite ordered
composition core.
-/
def orderedCompositionCore :
    OrderedCompositionCore R ℍ[R] where

  toCompositionCore :=
    compositionCore

  normSq_posDef := by
    intro q hq

    change 0 < Quaternion.normSq q

    exact
      lt_of_le_of_ne
        (Quaternion.normSq_nonneg (a := q))
        (Ne.symm
          ((Quaternion.normSq_ne_zero (a := q)).2 hq))


/--
The quaternion quadratic norm is anisotropic.
-/
theorem normSqForm_anisotropic :
    QuadraticMap.Anisotropic
      (normSqForm (R := R)) := by

  exact
    (orderedCompositionCore (R := R)).normSq_anisotropic


/--
Left multiplication by a nonzero quaternion is
injective, now derived through the generic ordered
composition framework.
-/
theorem composition_leftMul_injective
    {a : ℍ[R]}
    (ha : a ≠ 0) :
    Function.Injective
      (fun x : ℍ[R] => a * x) := by

  exact
    (orderedCompositionCore (R := R)).leftMul_injective ha


/--
Every quaternion target has a unique predecessor under
left multiplication by a nonzero quaternion.
-/
theorem composition_existsUnique_left_solution
    {a : ℍ[R]}
    (ha : a ≠ 0)
    (target : ℍ[R]) :
    ∃! x : ℍ[R], a * x = target := by

  exact
    (orderedCompositionCore (R := R))
      |>.existsUnique_left_solution ha target


end QuaternionWitness


#check QuaternionWitness.normSq_polar
#check QuaternionWitness.normSqForm
#check QuaternionWitness.normSqForm_apply
#check QuaternionWitness.compositionCore
#check QuaternionWitness.compositionCore_normSq
#check QuaternionWitness.orderedCompositionCore
#check QuaternionWitness.normSqForm_anisotropic
#check QuaternionWitness.composition_leftMul_injective
#check QuaternionWitness.composition_existsUnique_left_solution
