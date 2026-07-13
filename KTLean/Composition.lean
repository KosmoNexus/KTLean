import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Composition Algebras in KTLean

Foundational design principles:

1. Generic scalar field `K`.
2. Characteristic not equal to two.
3. Unital, nonassociative algebra.
4. Quadratic norm-square as the primitive metric object.
5. Polar form derived from the quadratic form.
6. Multiplicative norm.
7. Ordered-field positivity introduced only in a specialized layer.
8. No claim of `DecidableRealization` unless an explicit decision
   procedure is supplied.

This module begins the algebraic bridge from reversible dynamics
to composition algebras and, eventually, Hurwitz's theorem.
-/

universe u v


/--
The field-generic algebraic core of a unital composition algebra.

`K` is the scalar field.

`A` is a unital, possibly nonassociative algebra whose
multiplication is bilinear over `K`.

The norm-square is primitive. Its polar form is derived
from the quadratic form rather than introduced as an
independent parameter.
-/
structure CompositionCore
    (K : Type u)
    (A : Type v)
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A] where

  /--
  The scalar field has characteristic different from two.
  -/
  two_ne_zero :
    (2 : K) ≠ 0

  /--
  The primitive quadratic norm-square.
  -/
  normSq :
    QuadraticForm K A

  /--
  The multiplicative identity has unit norm-square.
  -/
  normSq_one :
    normSq 1 = 1

  /--
  The norm-square composes under multiplication.
  -/
  normSq_mul :
    ∀ x y : A,
      normSq (x * y) =
        normSq x * normSq y


namespace CompositionCore


/--
The raw polar form derived from the norm-square.

This is `Q (x + y) - Q x - Q y`.
No additional bilinear form is introduced as primitive data.
-/
def polar
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    (C : CompositionCore K A)
    (x y : A) :
    K :=
  QuadraticMap.polar C.normSq x y


/--
For an anisotropic norm-square, a nonzero algebra element
has nonzero norm-square.
-/
theorem normSq_ne_zero_of_ne_zero
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {x : A}
    (hx : x ≠ 0) :
    C.normSq x ≠ 0 := by

  intro hnorm
  exact hx (hAniso x hnorm)


/--
Under an anisotropic multiplicative norm-square,
a nonzero left multiplier cannot annihilate a state.
-/
theorem leftMul_eq_zero
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {a x : A}
    (ha : a ≠ 0)
    (hax : a * x = 0) :
    x = 0 := by

  apply hAniso x

  have hnorm :
      C.normSq (a * x) = 0 := by
    rw [hax]
    exact C.normSq.map_zero

  rw [C.normSq_mul a x] at hnorm

  have hna :
      C.normSq a ≠ 0 :=
    C.normSq_ne_zero_of_ne_zero hAniso ha

  exact
    (mul_eq_zero.mp hnorm).resolve_left hna


/--
Under an anisotropic multiplicative norm-square,
left multiplication by any nonzero element is injective.

Thus nonzero left multiplication cannot erase information.
-/
theorem leftMul_injective
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {a : A}
    (ha : a ≠ 0) :
    Function.Injective (fun x : A => a * x) := by

  intro x y hxy

  apply sub_eq_zero.mp

  apply C.leftMul_eq_zero hAniso ha

  simp only at hxy
  rw [mul_sub, hxy, sub_self]


end CompositionCore


#check CompositionCore
#check CompositionCore.polar
#check CompositionCore.normSq_ne_zero_of_ne_zero
#check CompositionCore.leftMul_eq_zero
#check CompositionCore.leftMul_injective
