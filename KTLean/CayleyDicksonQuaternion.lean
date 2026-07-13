import KTLean.QuaternionComposition

/-!
# Cayley–Dickson Reconstruction from Quaternion Blocks

This module begins the reconstruction of the octonionic
Cayley–Dickson product from two quaternionic compartments.

The carrier is

    ℍ[R] × ℍ[R]

but multiplication is not the ordinary componentwise
multiplication on the product type.

For quaternion pairs

    x = (a, b)
    y = (c, d)

the Cayley–Dickson product is

    (a, b) ⋆ (c, d)
      = (a*c - star d*b, d*a + b*star c).

The first objective is deliberately small:

1. define the two-block carrier;
2. define its distinguished block embeddings;
3. define the target Cayley–Dickson product;
4. verify the four elementary block interactions.

Later modules will reconstruct this product from routing,
orientation, and multiplication-selector data rather than
taking the formula as primitive.
-/

open scoped Quaternion

universe u

namespace CayleyDicksonQuaternion


variable {R : Type u}
variable [CommRing R]


/--
The two-quaternion carrier underlying the octonionic
Cayley–Dickson construction.

The two coordinates should be interpreted as distinct
quaternionic compartments rather than as componentwise
multiplicative registers.
-/
abbrev Carrier :=
  ℍ[R] × ℍ[R]


/--
Embed a quaternion into the first compartment.
-/
def e0 (q : ℍ[R]) :
    Carrier (R := R) :=
  (q, 0)


/--
Embed a quaternion into the second compartment.
-/
def e1 (q : ℍ[R]) :
    Carrier (R := R) :=
  (0, q)


/--
The target Cayley–Dickson product on two quaternion blocks.

For `x = (a,b)` and `y = (c,d)`,

    x ⋆ y = (a*c - star d*b, d*a + b*star c).
-/
def cdMul
    (x y : Carrier (R := R)) :
    Carrier (R := R) :=
  (
    x.1 * y.1 - star y.2 * x.2,
    y.2 * x.1 + x.2 * star y.1
  )


/--
Coordinate form of the Cayley–Dickson product.
-/
@[simp]
theorem cdMul_apply
    (a b c d : ℍ[R]) :
    cdMul (R := R) (a, b) (c, d) =
      (
        a * c - star d * b,
        d * a + b * star c
      ) := by
  rfl


/--
First block multiplied by first block remains in
the first block.
-/
@[simp]
theorem cdMul_e0_e0
    (a c : ℍ[R]) :
    cdMul (R := R) (e0 a) (e0 c) =
      e0 (a * c) := by
  simp [cdMul, e0]


/--
First block multiplied by second block routes into
the second block and reverses quaternionic order.
-/
@[simp]
theorem cdMul_e0_e1
    (a d : ℍ[R]) :
    cdMul (R := R) (e0 a) (e1 d) =
      e1 (d * a) := by
  simp [cdMul, e0, e1]


/--
Second block multiplied by first block routes into
the second block and conjugates the second input.
-/
@[simp]
theorem cdMul_e1_e0
    (b c : ℍ[R]) :
    cdMul (R := R) (e1 b) (e0 c) =
      e1 (b * star c) := by
  simp [cdMul, e0, e1]


/--
Second block multiplied by second block returns to
the first block with negative orientation and conjugation.
-/
@[simp]
theorem cdMul_e1_e1
    (b d : ℍ[R]) :
    cdMul (R := R) (e1 b) (e1 d) =
      e0 (-(star d * b)) := by
  simp [cdMul, e0, e1]


end CayleyDicksonQuaternion


#check CayleyDicksonQuaternion.Carrier
#check CayleyDicksonQuaternion.e0
#check CayleyDicksonQuaternion.e1
#check CayleyDicksonQuaternion.cdMul
#check CayleyDicksonQuaternion.cdMul_apply
#check CayleyDicksonQuaternion.cdMul_e0_e0
#check CayleyDicksonQuaternion.cdMul_e0_e1
#check CayleyDicksonQuaternion.cdMul_e1_e0
#check CayleyDicksonQuaternion.cdMul_e1_e1
