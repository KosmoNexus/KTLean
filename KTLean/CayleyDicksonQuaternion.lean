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


/-!
## Quaternion multiplication selectors

The routed-quaternion construction requires more than a choice
between `r` and `star r`.

Because quaternion multiplication is noncommutative, the selector
must also be capable of reversing operand order.

Three independent conjugation bits are sufficient:

1. conjugate the left input;
2. conjugate the right input;
3. conjugate the output.

Since quaternion conjugation reverses multiplication order,

    star (q * r) = star r * star q,

these three bits generate exactly eight multiplication forms.
-/

/--
A single binary choice controlling quaternionic conjugation.
-/
inductive ConjBit
  | keep
  | flip
  deriving DecidableEq, Repr


/--
Apply a conjugation bit to a quaternion.
-/
def applyConjBit
    (bit : ConjBit)
    (q : ℍ[R]) :
    ℍ[R] :=
  match bit with
  | .keep => q
  | .flip => star q


@[simp]
theorem applyConjBit_keep
    (q : ℍ[R]) :
    applyConjBit ConjBit.keep q = q := by
  rfl


@[simp]
theorem applyConjBit_flip
    (q : ℍ[R]) :
    applyConjBit ConjBit.flip q = star q := by
  rfl


/--
A quaternion multiplication selector consists of three
independent conjugation bits:

- one acting on the left input;
- one acting on the right input;
- one acting on the completed product.
-/
structure MultiplicationSelector where
  leftInput : ConjBit
  rightInput : ConjBit
  output : ConjBit
  deriving DecidableEq, Repr


/--
Execute a multiplication selector on two quaternions.
-/
def runSelector
    (s : MultiplicationSelector)
    (q r : ℍ[R]) :
    ℍ[R] :=
  applyConjBit s.output
    (
      applyConjBit s.leftInput q *
      applyConjBit s.rightInput r
    )


/-
The eight selectors are named by their three bits:

    left-input bit,
    right-input bit,
    output bit.
-/

def selector000 : MultiplicationSelector :=
  ⟨.keep, .keep, .keep⟩

def selector001 : MultiplicationSelector :=
  ⟨.keep, .keep, .flip⟩

def selector010 : MultiplicationSelector :=
  ⟨.keep, .flip, .keep⟩

def selector011 : MultiplicationSelector :=
  ⟨.keep, .flip, .flip⟩

def selector100 : MultiplicationSelector :=
  ⟨.flip, .keep, .keep⟩

def selector101 : MultiplicationSelector :=
  ⟨.flip, .keep, .flip⟩

def selector110 : MultiplicationSelector :=
  ⟨.flip, .flip, .keep⟩

def selector111 : MultiplicationSelector :=
  ⟨.flip, .flip, .flip⟩


/--
No conjugations: `q * r`.
-/
@[simp]
theorem runSelector_000
    (q r : ℍ[R]) :
    runSelector selector000 q r =
      q * r := by
  rfl


/--
Output conjugation reverses order and conjugates both inputs:

    star (q * r) = star r * star q.
-/
@[simp]
theorem runSelector_001
    (q r : ℍ[R]) :
    runSelector selector001 q r =
      star r * star q := by
  simp [runSelector, selector001]


/--
Conjugate only the right input: `q * star r`.
-/
@[simp]
theorem runSelector_010
    (q r : ℍ[R]) :
    runSelector selector010 q r =
      q * star r := by
  rfl


/--
Conjugate the right input and then the output:

    star (q * star r) = r * star q.
-/
@[simp]
theorem runSelector_011
    (q r : ℍ[R]) :
    runSelector selector011 q r =
      r * star q := by
  simp [runSelector, selector011]


/--
Conjugate only the left input: `star q * r`.
-/
@[simp]
theorem runSelector_100
    (q r : ℍ[R]) :
    runSelector selector100 q r =
      star q * r := by
  rfl


/--
Conjugate the left input and then the output:

    star (star q * r) = star r * q.
-/
@[simp]
theorem runSelector_101
    (q r : ℍ[R]) :
    runSelector selector101 q r =
      star r * q := by
  simp [runSelector, selector101]


/--
Conjugate both inputs: `star q * star r`.
-/
@[simp]
theorem runSelector_110
    (q r : ℍ[R]) :
    runSelector selector110 q r =
      star q * star r := by
  rfl


/--
Conjugate both inputs and then the output:

    star (star q * star r) = r * q.
-/
@[simp]
theorem runSelector_111
    (q r : ℍ[R]) :
    runSelector selector111 q r =
      r * q := by
  simp [runSelector, selector111]


/--
The two quaternionic compartments.
-/
inductive Block
  | first
  | second
  deriving DecidableEq, Repr


/--
The multiplication-selector table required by the
Cayley–Dickson quaternion-block product.
-/
def cdSelector :
    Block → Block → MultiplicationSelector
  | .first,  .first  => selector000
  | .first,  .second => selector111
  | .second, .first  => selector010
  | .second, .second => selector101


/--
The first-first block interaction selects ordinary
quaternion multiplication.
-/
@[simp]
theorem run_cdSelector_first_first
    (a c : ℍ[R]) :
    runSelector
        (cdSelector Block.first Block.first)
        a c =
      a * c := by
  simp [cdSelector]


/--
The first-second block interaction selects reversed
multiplication, producing `d * a`.
-/
@[simp]
theorem run_cdSelector_first_second
    (a d : ℍ[R]) :
    runSelector
        (cdSelector Block.first Block.second)
        a d =
      d * a := by
  simp [cdSelector]


/--
The second-first block interaction selects
`b * star c`.
-/
@[simp]
theorem run_cdSelector_second_first
    (b c : ℍ[R]) :
    runSelector
        (cdSelector Block.second Block.first)
        b c =
      b * star c := by
  simp [cdSelector]


/--
The second-second block interaction selects
`star d * b`.

The negative orientation required by Cayley–Dickson
will be supplied separately by the routing sign.
-/
@[simp]
theorem run_cdSelector_second_second
    (b d : ℍ[R]) :
    runSelector
        (cdSelector Block.second Block.second)
        b d =
      star d * b := by
  simp [cdSelector]


/-!
## Routing and orientation

The multiplication selector determines the quaternionic
payload. Two additional pieces of data determine:

1. which compartment receives the payload;
2. whether the payload receives positive or negative orientation.

The Cayley–Dickson product is then reconstructed by summing
the four routed block interactions.
-/

/--
Orientation carried by a routed block interaction.
-/
inductive Orientation
  | positive
  | negative
  deriving DecidableEq, Repr


/--
Apply an orientation to a quaternionic payload.
-/
def applyOrientation
    (orientation : Orientation)
    (q : ℍ[R]) :
    ℍ[R] :=
  match orientation with
  | .positive => q
  | .negative => -q


@[simp]
theorem applyOrientation_positive
    (q : ℍ[R]) :
    applyOrientation Orientation.positive q = q := by
  rfl


@[simp]
theorem applyOrientation_negative
    (q : ℍ[R]) :
    applyOrientation Orientation.negative q = -q := by
  rfl


/--
Place a quaternionic payload into one of the two compartments.
-/
def place
    (block : Block)
    (q : ℍ[R]) :
    Carrier (R := R) :=
  match block with
  | .first => e0 q
  | .second => e1 q


@[simp]
theorem place_first
    (q : ℍ[R]) :
    place Block.first q = e0 q := by
  rfl


@[simp]
theorem place_second
    (q : ℍ[R]) :
    place Block.second q = e1 q := by
  rfl


/--
The Cayley–Dickson routing table.

The equal-block interactions return to the first compartment.
The mixed-block interactions route to the second compartment.
-/
def cdRoute :
    Block → Block → Block
  | .first,  .first  => .first
  | .first,  .second => .second
  | .second, .first  => .second
  | .second, .second => .first


/--
The Cayley–Dickson orientation table.

Only the second-second interaction receives negative orientation.
-/
def cdOrientation :
    Block → Block → Orientation
  | .second, .second => .negative
  | _, _ => .positive


/--
One fully routed block interaction.

The selector computes the quaternionic payload.
The orientation supplies its sign.
The route determines its destination compartment.
-/
def routedTerm
    (leftBlock rightBlock : Block)
    (q r : ℍ[R]) :
    Carrier (R := R) :=
  place
    (cdRoute leftBlock rightBlock)
    (
      applyOrientation
        (cdOrientation leftBlock rightBlock)
        (
          runSelector
            (cdSelector leftBlock rightBlock)
            q
            r
        )
    )


/--
First-first interaction:
ordinary quaternion multiplication routed to the first block.
-/
@[simp]
theorem routedTerm_first_first
    (a c : ℍ[R]) :
    routedTerm Block.first Block.first a c =
      e0 (a * c) := by
  simp [routedTerm, cdRoute, cdOrientation]


/--
First-second interaction:
reversed quaternion multiplication routed to the second block.
-/
@[simp]
theorem routedTerm_first_second
    (a d : ℍ[R]) :
    routedTerm Block.first Block.second a d =
      e1 (d * a) := by
  simp [routedTerm, cdRoute, cdOrientation]


/--
Second-first interaction:
right-input conjugation routed to the second block.
-/
@[simp]
theorem routedTerm_second_first
    (b c : ℍ[R]) :
    routedTerm Block.second Block.first b c =
      e1 (b * star c) := by
  simp [routedTerm, cdRoute, cdOrientation]


/--
Second-second interaction:
reversed/conjugated payload, negative orientation,
and return to the first block.
-/
@[simp]
theorem routedTerm_second_second
    (b d : ℍ[R]) :
    routedTerm Block.second Block.second b d =
      e0 (-(star d * b)) := by
  simp [routedTerm, cdRoute, cdOrientation]


/--
The product reconstructed by summing all four routed
quaternion-block interactions.
-/
def routedMul
    (x y : Carrier (R := R)) :
    Carrier (R := R) :=
  routedTerm Block.first Block.first x.1 y.1 +
  routedTerm Block.first Block.second x.1 y.2 +
  routedTerm Block.second Block.first x.2 y.1 +
  routedTerm Block.second Block.second x.2 y.2


/--
Coordinate form of the selector-and-routing reconstruction.
-/
@[simp]
theorem routedMul_apply
    (a b c d : ℍ[R]) :
    routedMul (R := R) (a, b) (c, d) =
      (
        a * c - star d * b,
        d * a + b * star c
      ) := by
  simp [routedMul, e0, e1, sub_eq_add_neg]


/--
The selector, route, and orientation tables reconstruct
the target Cayley–Dickson multiplication exactly.
-/
theorem routedMul_eq_cdMul
    (x y : Carrier (R := R)) :
    routedMul x y =
      cdMul x y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp [routedMul, cdMul, e0, e1, sub_eq_add_neg]

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
#check CayleyDicksonQuaternion.ConjBit
#check CayleyDicksonQuaternion.applyConjBit
#check CayleyDicksonQuaternion.MultiplicationSelector
#check CayleyDicksonQuaternion.runSelector
#check CayleyDicksonQuaternion.runSelector_000
#check CayleyDicksonQuaternion.runSelector_001
#check CayleyDicksonQuaternion.runSelector_010
#check CayleyDicksonQuaternion.runSelector_011
#check CayleyDicksonQuaternion.runSelector_100
#check CayleyDicksonQuaternion.runSelector_101
#check CayleyDicksonQuaternion.runSelector_110
#check CayleyDicksonQuaternion.runSelector_111
#check CayleyDicksonQuaternion.Block
#check CayleyDicksonQuaternion.cdSelector
#check CayleyDicksonQuaternion.run_cdSelector_first_first
#check CayleyDicksonQuaternion.run_cdSelector_first_second
#check CayleyDicksonQuaternion.run_cdSelector_second_first
#check CayleyDicksonQuaternion.run_cdSelector_second_second
#check CayleyDicksonQuaternion.Orientation
#check CayleyDicksonQuaternion.applyOrientation
#check CayleyDicksonQuaternion.place
#check CayleyDicksonQuaternion.cdRoute
#check CayleyDicksonQuaternion.cdOrientation
#check CayleyDicksonQuaternion.routedTerm
#check CayleyDicksonQuaternion.routedTerm_first_first
#check CayleyDicksonQuaternion.routedTerm_first_second
#check CayleyDicksonQuaternion.routedTerm_second_first
#check CayleyDicksonQuaternion.routedTerm_second_second
#check CayleyDicksonQuaternion.routedMul
#check CayleyDicksonQuaternion.routedMul_apply
#check CayleyDicksonQuaternion.routedMul_eq_cdMul