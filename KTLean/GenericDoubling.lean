import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Tactic.Abel



/-!
# Generic Cayley–Dickson Doubling

This module begins Phase A of the KTLean forcing round.

## Formal status

**Level 1 — Encoding.**

The present milestone defines the weakest algebraic interface intended
to support iterated Cayley–Dickson doubling. No doubling product is
defined yet, and no closure theorem is claimed in this file at A0.

The interface deliberately does not assume associativity.
-/

namespace GenericDoubling

universe u

/--
The weakest currently declared substrate interface for iterable
Cayley–Dickson doubling.

`NonAssocRing A` supplies:

- an additive commutative group;
- a multiplicative unit;
- left and right distributivity;
- multiplication without an associativity assumption.

`StarRing A` supplies:

- an involutive star;
- additivity of star;
- reversal of multiplication:
  `star (x * y) = star y * star x`.

The only additional law recorded here is preservation of the unit.
-/
class IterableCDBase
    (A : Type u)
    [NonAssocRing A]
    [StarRing A] : Prop where

  star_one :
    star (1 : A) = 1

end GenericDoubling

#check GenericDoubling.IterableCDBase

namespace GenericDoubling

universe u

/-!
## A1: The generic doubled carrier
-/

/--
One Cayley–Dickson doubling of a carrier `A`.

This is deliberately a nominal structure rather than an abbreviation
for `A × A`. Consequently it cannot silently inherit the product
type's componentwise multiplication.
-/
@[ext]
structure Double (A : Type u) where
  fst : A
  snd : A

/--
The underlying equivalence between the nominal doubled carrier
and an ordinary product.

This equivalence is used only to transport the additive structure.
Multiplication will be defined separately by the Cayley–Dickson law.
-/
def doubleEquiv
    (A : Type u) :
    Double A ≃ A × A where

  toFun x :=
    (x.fst, x.snd)

  invFun x :=
    ⟨x.1, x.2⟩

  left_inv x := by
    cases x
    rfl

  right_inv x := by
    cases x
    rfl

/--
The doubled carrier inherits componentwise additive-group structure
from `A × A`.

No multiplicative structure is transported here.
-/
instance instAddCommGroupDouble
    {A : Type u}
    [AddCommGroup A] :
    AddCommGroup (Double A) :=
  (doubleEquiv A).addCommGroup

example
    {A : Type u}
    [AddCommGroup A] :
    AddCommGroup (Double A) :=
  inferInstance

end GenericDoubling

#check GenericDoubling.Double
#check GenericDoubling.doubleEquiv

namespace GenericDoubling

universe u

/-!
## A1.2: Primitive doubled operations
-/

/--
The multiplicative identity of the doubled carrier.

The unit lies entirely in the first compartment.
-/
def doubleOne
    {A : Type u}
    [Zero A]
    [One A] :
    Double A :=
  ⟨1, 0⟩

instance instOneDouble
    {A : Type u}
    [Zero A]
    [One A] :
    One (Double A) :=
  ⟨doubleOne⟩

/--
The Cayley–Dickson product on the doubled carrier.

For `x = (a,b)` and `y = (c,d)`:

    x * y = (a*c - star d*b, d*a + b*star c).
-/
def doubleMul
    {A : Type u}
    [Add A]
    [Sub A]
    [Mul A]
    [Star A]
    (x y : Double A) :
    Double A :=
  ⟨
    x.fst * y.fst - star y.snd * x.snd,
    y.snd * x.fst + x.snd * star y.fst
  ⟩

instance instMulDouble
    {A : Type u}
    [Add A]
    [Sub A]
    [Mul A]
    [Star A] :
    Mul (Double A) :=
  ⟨doubleMul⟩

/--
The canonical involution on a Cayley–Dickson double.

    star (a,b) = (star a, -b).
-/
def doubleStar
    {A : Type u}
    [Neg A]
    [Star A]
    (x : Double A) :
    Double A :=
  ⟨star x.fst, -x.snd⟩

instance instStarDouble
    {A : Type u}
    [Neg A]
    [Star A] :
    Star (Double A) :=
  ⟨doubleStar⟩

/--
Natural-number casts enter through the first compartment.
-/
instance instNatCastDouble
    {A : Type u}
    [Zero A]
    [NatCast A] :
    NatCast (Double A) :=
  ⟨fun n => ⟨n, 0⟩⟩

/--
Integer casts enter through the first compartment.
-/
instance instIntCastDouble
    {A : Type u}
    [Zero A]
    [IntCast A] :
    IntCast (Double A) :=
  ⟨fun z => ⟨z, 0⟩⟩

@[simp]
theorem one_fst
    {A : Type u}
    [Zero A]
    [One A] :
    (1 : Double A).fst = 1 := by
  rfl

@[simp]
theorem one_snd
    {A : Type u}
    [Zero A]
    [One A] :
    (1 : Double A).snd = 0 := by
  rfl

@[simp]
theorem mul_fst
    {A : Type u}
    [Add A]
    [Sub A]
    [Mul A]
    [Star A]
    (x y : Double A) :
    (x * y).fst =
      x.fst * y.fst - star y.snd * x.snd := by
  rfl

@[simp]
theorem mul_snd
    {A : Type u}
    [Add A]
    [Sub A]
    [Mul A]
    [Star A]
    (x y : Double A) :
    (x * y).snd =
      y.snd * x.fst + x.snd * star y.fst := by
  rfl

@[simp]
theorem star_fst
    {A : Type u}
    [Neg A]
    [Star A]
    (x : Double A) :
    (star x).fst = star x.fst := by
  rfl

@[simp]
theorem star_snd
    {A : Type u}
    [Neg A]
    [Star A]
    (x : Double A) :
    (star x).snd = -x.snd := by
  rfl

end GenericDoubling

namespace GenericDoubling

universe u

/-!
## A1.3: Nonunital nonassociative ring closure
-/

/-
Coordinate simplification lemmas for the transported additive structure.
-/

@[simp]
theorem zero_fst
    {A : Type u}
    [AddCommGroup A] :
    (0 : Double A).fst = 0 := by
  rfl

@[simp]
theorem zero_snd
    {A : Type u}
    [AddCommGroup A] :
    (0 : Double A).snd = 0 := by
  rfl

@[simp]
theorem add_fst
    {A : Type u}
    [AddCommGroup A]
    (x y : Double A) :
    (x + y).fst = x.fst + y.fst := by
  rfl

@[simp]
theorem add_snd
    {A : Type u}
    [AddCommGroup A]
    (x y : Double A) :
    (x + y).snd = x.snd + y.snd := by
  rfl

@[simp]
theorem neg_fst
    {A : Type u}
    [AddCommGroup A]
    (x : Double A) :
    (-x).fst = -x.fst := by
  rfl

@[simp]
theorem neg_snd
    {A : Type u}
    [AddCommGroup A]
    (x : Double A) :
    (-x).snd = -x.snd := by
  rfl

@[simp]
theorem sub_fst
    {A : Type u}
    [AddCommGroup A]
    (x y : Double A) :
    (x - y).fst = x.fst - y.fst := by
  rfl

@[simp]
theorem sub_snd
    {A : Type u}
    [AddCommGroup A]
    (x y : Double A) :
    (x - y).snd = x.snd - y.snd := by
  rfl

/--
The doubled Cayley–Dickson product distributes over addition
in its right argument.
-/
theorem double_left_distrib
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    (x y z : Double A) :
    x * (y + z) = x * y + x * z := by

  apply Double.ext

  · simp only [
      mul_fst,
      add_fst,
      add_snd,
      star_add,
      left_distrib,
      right_distrib,
      sub_eq_add_neg
    ]
    abel

  · simp only [
      mul_snd,
      add_fst,
      add_snd,
      star_add,
      left_distrib,
      right_distrib
    ]
    abel

/--
The doubled Cayley–Dickson product distributes over addition
in its left argument.
-/
theorem double_right_distrib
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    (x y z : Double A) :
    (x + y) * z = x * z + y * z := by

  apply Double.ext

  · simp only [
      mul_fst,
      add_fst,
      add_snd,
      left_distrib,
      right_distrib,
      sub_eq_add_neg
    ]
    abel

  · simp only [
      mul_snd,
      add_fst,
      add_snd,
      left_distrib,
      right_distrib
    ]
    abel


/--
Zero annihilates the doubled product on the left.
-/
theorem double_zero_mul
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    (x : Double A) :
    0 * x = 0 := by

  ext <;> simp

/--
Zero annihilates the doubled product on the right.
-/
theorem double_mul_zero
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    (x : Double A) :
    x * 0 = 0 := by

  ext <;> simp
/--
One Cayley–Dickson doubling preserves the nonunital
nonassociative ring structure.

No associativity of multiplication is used or obtained.
-/
instance instNonUnitalNonAssocRingDouble
    {A : Type u}
    [NonAssocRing A]
    [StarRing A] :
    NonUnitalNonAssocRing (Double A) :=
  NonUnitalNonAssocRing.mk
    double_left_distrib
    double_right_distrib
    double_zero_mul
    double_mul_zero

example
    {A : Type u}
    [NonAssocRing A]
    [StarRing A] :
    NonUnitalNonAssocRing (Double A) :=
  inferInstance

end GenericDoubling

namespace GenericDoubling

universe u

/-!
## A1.4: Unital nonassociative ring closure
-/

@[simp]
theorem natCast_fst
    {A : Type u}
    [Zero A]
    [NatCast A]
    (n : Nat) :
    (n : Double A).fst = (n : A) := by
  rfl

@[simp]
theorem natCast_snd
    {A : Type u}
    [Zero A]
    [NatCast A]
    (n : Nat) :
    (n : Double A).snd = 0 := by
  rfl

@[simp]
theorem intCast_fst
    {A : Type u}
    [Zero A]
    [IntCast A]
    (z : Int) :
    (z : Double A).fst = (z : A) := by
  rfl

@[simp]
theorem intCast_snd
    {A : Type u}
    [Zero A]
    [IntCast A]
    (z : Int) :
    (z : Double A).snd = 0 := by
  rfl

/--
The doubled unit acts as a left multiplicative identity.

This direction does not require preservation of one by star.
-/
theorem double_one_mul
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    (x : Double A) :
    1 * x = x := by

  apply Double.ext <;>
    simp

/--
The doubled unit acts as a right multiplicative identity.

The second coordinate requires `star 1 = 1`.
-/
theorem double_mul_one
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    [IterableCDBase A]
    (x : Double A) :
    x * 1 = x := by

  apply Double.ext

  · simp

  · simp only [
      mul_snd,
      one_fst,
      one_snd,
      zero_mul,
      zero_add
    ]

    rw [IterableCDBase.star_one]

    exact mul_one x.snd

/--
Natural zero casts correctly into the doubled carrier.
-/
theorem double_natCast_zero
    {A : Type u}
    [NonAssocRing A] :
    ((0 : Nat) : Double A) = 0 := by

  apply Double.ext <;>
    simp

/--
Natural successor casts correctly into the doubled carrier.
-/
theorem double_natCast_succ
    {A : Type u}
    [NonAssocRing A]
    (n : Nat) :
    ((n + 1 : Nat) : Double A) =
      (n : Double A) + 1 := by

  apply Double.ext <;>
    simp

/--
A nonnegative integer cast agrees with its natural-number cast.
-/
theorem double_intCast_ofNat
    {A : Type u}
    [NonAssocRing A]
    (n : Nat) :
    ((n : Int) : Double A) =
      (n : Double A) := by

  apply Double.ext <;>
    simp

/--
A negative successor integer casts to the additive inverse
of the corresponding positive natural cast.
-/
theorem double_intCast_negSucc
    {A : Type u}
    [NonAssocRing A]
    (n : Nat) :
    ((Int.negSucc n : Int) : Double A) =
      -((n + 1 : Nat) : Double A) := by

  apply Double.ext <;>
    simp

/--
One Cayley–Dickson doubling preserves the full
nonassociative-ring structure.

No multiplication associativity is assumed or produced.
-/
instance instNonAssocRingDouble
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    [IterableCDBase A] :
    NonAssocRing (Double A) :=
  NonAssocRing.mk
    double_one_mul
    double_mul_one
    (natCast_zero := double_natCast_zero)
    (natCast_succ := double_natCast_succ)
    (intCast_ofNat := double_intCast_ofNat)
    (intCast_negSucc := double_intCast_negSucc)

example
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    [IterableCDBase A] :
    NonAssocRing (Double A) :=
  inferInstance

end GenericDoubling

namespace GenericDoubling

universe u

/-!
## A1.5: Star structure and iteration closure
-/

/--
The canonical involution on the double is involutive.
-/
theorem double_star_involutive
    {A : Type u}
    [NonAssocRing A]
    [StarRing A] :
    Function.Involutive
      (star : Double A → Double A) := by

  intro x
  apply Double.ext <;>
    simp

/--
The canonical involution on the double preserves addition.
-/
theorem double_star_add
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    (x y : Double A) :
    star (x + y) = star x + star y := by

  apply Double.ext

  · simp only [
      star_fst,
      add_fst,
      star_add
    ]

  · simp only [
      star_snd,
      add_snd
    ]
    abel

/--
The canonical involution reverses the doubled product.
-/

theorem double_star_mul
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    (x y : Double A) :
    star (x * y) = star y * star x := by

  apply Double.ext

  · simp only [
      star_fst,
      mul_fst,
      star_snd,
      sub_eq_add_neg,
      star_add,
      star_neg,
      star_mul,
      star_star,
      neg_mul,
      mul_neg,
      neg_neg
    ]

  · simp only [
      star_snd,
      mul_snd,
      star_fst,
      star_star,
      neg_mul
    ]
    abel

/--
The canonical involution preserves the doubled unit.
-/
theorem double_star_one
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    [IterableCDBase A] :
    star (1 : Double A) = 1 := by

  apply Double.ext

  · simp only [
      star_fst,
      one_fst
    ]
    exact IterableCDBase.star_one

  · simp

/--
The doubled involution is involutive.
-/
instance instInvolutiveStarDouble
    {A : Type u}
    [NonAssocRing A]
    [StarRing A] :
    InvolutiveStar (Double A) where

  star_involutive :=
    double_star_involutive

/--
The doubled involution reverses multiplication.
-/
instance instStarMulDouble
    {A : Type u}
    [NonAssocRing A]
    [StarRing A] :
    StarMul (Double A) where

  star_mul :=
    double_star_mul

/--
The doubled carrier is again a star ring.
-/
instance instStarRingDouble
    {A : Type u}
    [NonAssocRing A]
    [StarRing A] :
    StarRing (Double A) where

  star_add :=
    double_star_add

/--
**A1 closure theorem.**

One Cayley–Dickson doubling preserves the complete iterable
nonassociative involutive interface.

Consequently the construction may accept its own output as input,
licensing further iterations without importing associativity.
-/
instance instIterableCDBaseDouble
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    [IterableCDBase A] :
    IterableCDBase (Double A) where

  star_one :=
    double_star_one

example
    {A : Type u}
    [NonAssocRing A]
    [StarRing A]
    [IterableCDBase A] :
    IterableCDBase (Double A) :=
  inferInstance

end GenericDoubling
