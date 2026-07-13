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

namespace CompositionCore


/--
Left multiplication by `a` as a linear endomorphism
of the underlying `K`-vector space.
-/
def leftMulLinear
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    (a : A) :
    A →ₗ[K] A where

  toFun := fun x => a * x

  map_add' := by
    intro x y
    exact mul_add a x y

  map_smul' := by
    intro r x
    exact mul_smul_comm r a x


/--
The linear map representing multiplication by a nonzero
element is injective when the norm-square is anisotropic.
-/
theorem leftMulLinear_injective
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
    Function.Injective
      (leftMulLinear (K := K) a) := by

  simpa [leftMulLinear] using
    C.leftMul_injective hAniso ha


/--
In finite dimension, multiplication on the left by any
nonzero element is surjective.

Every target state therefore has a predecessor under
left multiplication.
-/
theorem leftMul_surjective
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    [FiniteDimensional K A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {a : A}
    (ha : a ≠ 0) :
    Function.Surjective (fun x : A => a * x) := by

  have hinj :
      Function.Injective
        (leftMulLinear (K := K) a) :=
    C.leftMulLinear_injective hAniso ha

  have hsurj :
      Function.Surjective
        (leftMulLinear (K := K) a) :=
    LinearMap.injective_iff_surjective.mp hinj

  simpa [leftMulLinear] using hsurj


/--
For every target `b`, multiplication on the left by a
nonzero element has a solution.
-/
theorem exists_left_solution
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    [FiniteDimensional K A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {a : A}
    (ha : a ≠ 0)
    (b : A) :
    ∃ x : A, a * x = b := by

  exact C.leftMul_surjective hAniso ha b


end CompositionCore


#check CompositionCore.leftMulLinear
#check CompositionCore.leftMulLinear_injective
#check CompositionCore.leftMul_surjective
#check CompositionCore.exists_left_solution

namespace CompositionCore


/--
In finite dimension, left multiplication by a nonzero
element defines a linear equivalence of the state space.

The inverse is supplied abstractly from injectivity and
finite dimensionality. This construction is therefore
marked `noncomputable`.
-/
noncomputable def leftMulEquiv
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    [FiniteDimensional K A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {a : A}
    (ha : a ≠ 0) :
    A ≃ₗ[K] A :=

  LinearEquiv.ofInjectiveEndo
    (leftMulLinear (K := K) a)
    (C.leftMulLinear_injective hAniso ha)


/--
The forward map of `leftMulEquiv` is precisely
left multiplication by `a`.
-/
@[simp]
theorem leftMulEquiv_apply
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    [FiniteDimensional K A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {a : A}
    (ha : a ≠ 0)
    (x : A) :
    C.leftMulEquiv hAniso ha x =
      a * x := by

  rfl


/--
Applying the inverse equivalence after multiplication
by `a` recovers the original state.
-/
theorem leftMulEquiv_recovers
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    [FiniteDimensional K A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {a : A}
    (ha : a ≠ 0)
    (x : A) :
    (C.leftMulEquiv hAniso ha).symm
        (a * x) =
      x := by

  rw [← C.leftMulEquiv_apply hAniso ha x]

  exact
    (C.leftMulEquiv hAniso ha).symm_apply_apply x


/--
Multiplying by `a` after applying the inverse equivalence
returns the target state.
-/
theorem leftMulEquiv_reconstructs
    {K : Type u}
    {A : Type v}
    [Field K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    [FiniteDimensional K A]
    (C : CompositionCore K A)
    (hAniso : QuadraticMap.Anisotropic C.normSq)
    {a : A}
    (ha : a ≠ 0)
    (target : A) :
    a *
        (C.leftMulEquiv hAniso ha).symm target =
      target := by

  rw [← C.leftMulEquiv_apply hAniso ha]

  exact
    (C.leftMulEquiv hAniso ha).apply_symm_apply target


end CompositionCore


#check CompositionCore.leftMulEquiv
#check CompositionCore.leftMulEquiv_apply
#check CompositionCore.leftMulEquiv_recovers
#check CompositionCore.leftMulEquiv_reconstructs
