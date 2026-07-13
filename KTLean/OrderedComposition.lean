import KTLean.Composition

/-!
# Ordered Composition Algebras in KTLean

This module adds positivity to the field-generic composition core.

The generic `CompositionCore` requires only an anisotropic
multiplicative quadratic norm-square for its cancellation and
reversibility results.

Here the scalar field is ordered and the norm-square is assumed
positive definite. Positive definiteness then implies anisotropy,
allowing all existing composition theorems to be reused without
assuming anisotropy separately.

This remains field-generic: no commitment to `ℝ` is made here.
-/

universe u v


/--
A composition core over a linearly ordered field whose
quadratic norm-square is positive definite.

The underlying algebra remains unital and possibly
nonassociative.
-/
structure OrderedCompositionCore
    (K : Type u)
    (A : Type v)
    [Field K]
    [LinearOrder K]
    [IsStrictOrderedRing K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    extends CompositionCore K A where

  /--
  The quadratic norm-square is positive on every
  nonzero algebra element.
  -/
  normSq_posDef :
    QuadraticMap.PosDef toCompositionCore.normSq


namespace OrderedCompositionCore


/--
Positive definiteness implies anisotropy.

Thus the norm-square vanishes only at the zero element.
-/
theorem normSq_anisotropic
    {K : Type u}
    {A : Type v}
    [Field K]
    [LinearOrder K]
    [IsStrictOrderedRing K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    (C : OrderedCompositionCore K A) :
    QuadraticMap.Anisotropic
      C.toCompositionCore.normSq := by

  exact C.normSq_posDef.anisotropic


/--
For a positive-definite composition core, left
multiplication by every nonzero element is injective.
-/
theorem leftMul_injective
    {K : Type u}
    {A : Type v}
    [Field K]
    [LinearOrder K]
    [IsStrictOrderedRing K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    (C : OrderedCompositionCore K A)
    {a : A}
    (ha : a ≠ 0) :
    Function.Injective (fun x : A => a * x) := by

  exact
    C.toCompositionCore.leftMul_injective
      C.normSq_anisotropic
      ha


/--
In finite dimension, positive-definite norm composition
makes left multiplication by every nonzero element
surjective.
-/
theorem leftMul_surjective
    {K : Type u}
    {A : Type v}
    [Field K]
    [LinearOrder K]
    [IsStrictOrderedRing K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    [FiniteDimensional K A]
    (C : OrderedCompositionCore K A)
    {a : A}
    (ha : a ≠ 0) :
    Function.Surjective (fun x : A => a * x) := by

  exact
    C.toCompositionCore.leftMul_surjective
      C.normSq_anisotropic
      ha


/--
Every target has a unique predecessor under left
multiplication by a nonzero element.
-/
theorem existsUnique_left_solution
    {K : Type u}
    {A : Type v}
    [Field K]
    [LinearOrder K]
    [IsStrictOrderedRing K]
    [NonAssocRing A]
    [Module K A]
    [SMulCommClass K A A]
    [IsScalarTower K A A]
    [FiniteDimensional K A]
    (C : OrderedCompositionCore K A)
    {a : A}
    (ha : a ≠ 0)
    (target : A) :
    ∃! x : A, a * x = target := by

  obtain ⟨x, hx⟩ :=
    C.leftMul_surjective ha target

  refine ⟨x, hx, ?_⟩

  intro y hy

  exact
    C.leftMul_injective ha
      (hy.trans hx.symm)


end OrderedCompositionCore


#check OrderedCompositionCore
#check OrderedCompositionCore.normSq_anisotropic
#check OrderedCompositionCore.leftMul_injective
#check OrderedCompositionCore.leftMul_surjective
#check OrderedCompositionCore.existsUnique_left_solution
