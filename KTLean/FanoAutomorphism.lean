import KTLean.Fano
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Automorphisms of the Fano completion structure

This module defines the concrete symmetry group needed by KT.

A Fano automorphism is a permutation of the seven Fano
points that preserves the Fano completion operation:

    σ (complete x y) = complete (σ x) (σ y).

This is the exact incidence-preserving object that will
later act on glyphs, walk states, and monads.

No cardinality claim is made in this module yet.
-/

namespace FanoAutomorphism

/--
A permutation preserves the Fano completion law when
it commutes with the completion operation.
-/
def PreservesCompletion
    (σ : Equiv.Perm Fano.Point) :
    Prop :=
  ∀ x y : Fano.Point,
    σ (Fano.complete x y) =
      Fano.complete (σ x) (σ y)

/--
The identity permutation preserves Fano completion.
-/
theorem preservesCompletion_one :
    PreservesCompletion
      (1 : Equiv.Perm Fano.Point) := by
  intro x y
  rfl

/--
The composition of two completion-preserving
permutations again preserves completion.
-/
theorem preservesCompletion_mul
    {σ τ : Equiv.Perm Fano.Point}
    (hσ : PreservesCompletion σ)
    (hτ : PreservesCompletion τ) :
    PreservesCompletion (σ * τ) := by
  intro x y

  change
    σ (τ (Fano.complete x y)) =
      Fano.complete
        (σ (τ x))
        (σ (τ y))

  rw [
    hτ x y,
    hσ (τ x) (τ y)
  ]

/--
The inverse of a completion-preserving permutation
again preserves completion.
-/
theorem preservesCompletion_inv
    {σ : Equiv.Perm Fano.Point}
    (hσ : PreservesCompletion σ) :
    PreservesCompletion σ⁻¹ := by
  intro x y

  apply σ.injective

  have h :=
    hσ (σ⁻¹ x) (σ⁻¹ y)

  simpa using h.symm

/--
The subgroup of all permutations of the seven Fano
points that preserve the completion law.
-/
def group :
    Subgroup (Equiv.Perm Fano.Point) where

  carrier :=
    {σ | PreservesCompletion σ}

  one_mem' :=
    preservesCompletion_one

  mul_mem' := by
    intro σ τ hσ hτ
    exact
      preservesCompletion_mul hσ hτ

  inv_mem' := by
    intro σ hσ
    exact
      preservesCompletion_inv hσ
/--
The concrete type of Fano automorphisms.
-/
abbrev Automorphism :=
  group

/--
Membership in the Fano automorphism subgroup is exactly
preservation of the completion law.
-/
theorem mem_group_iff
    (σ : Equiv.Perm Fano.Point) :
    σ ∈ group ↔
      PreservesCompletion σ := by
  rfl

/--
Every bundled Fano automorphism preserves completion.
-/
theorem map_complete
    (σ : Automorphism)
    (x y : Fano.Point) :
    σ.1 (Fano.complete x y) =
      Fano.complete (σ.1 x) (σ.1 y) := by
  exact σ.2 x y

end FanoAutomorphism
