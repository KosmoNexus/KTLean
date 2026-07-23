import KTLean.PascalForcingTriadicAddition

/-!
# Residue Representation of Triadic Addition

## Formal status

**Level 1 — Concrete arithmetic identification.**

The explicit triadic additive states are represented by residues

    inactive ↦ 0
    positive ↦ 1
    negative ↦ 2.

This module proves:

1. every encoded state lies below three;
2. encoding is injective;
3. decoding recovers every encoded state;
4. triadic addition corresponds exactly to natural-number addition
   reduced modulo three;
5. triadic negation corresponds to additive inversion modulo three.

No abstract group classification is claimed here. This module provides
the concrete residue bridge needed for the subsequent forcing and
Pascal-recursion modules.
-/

namespace PascalForcingTriadicResidues

open PascalMod3
open PascalForcingTriadicAddition

/--
Encode a triadic control state as its residue modulo three.
-/
def encode :
    Control → Nat

  | .inactive =>
      0

  | .positive =>
      1

  | .negative =>
      2

/--
Decode a canonical residue representative.
Values outside `{0,1,2}` are first reduced modulo three.
-/
def decode
    (residue : Nat) :
    Control :=

  match residue % 3 with

  | 0 =>
      .inactive

  | 1 =>
      .positive

  | _ =>
      .negative

/--
Every encoded state is a canonical residue below three.
-/
theorem encode_lt_three
    (state : Control) :
    encode state < 3 := by

  cases state <;>
    decide

/--
Encoding distinguishes the three triadic states.
-/
theorem encode_injective :
    Function.Injective encode := by

  intro first second h

  cases first <;>
    cases second <;>
    simp [encode] at h ⊢

/--
Decoding an encoded state recovers that state.
-/
@[simp]
theorem decode_encode
    (state : Control) :
    decode (encode state) =
      state := by

  cases state <;>
    rfl

/--
Encoding after decoding produces the canonical residue modulo three.
-/
theorem encode_decode
    (residue : Nat) :
    encode (decode residue) =
      residue % 3 := by

  have hlt :
      residue % 3 < 3 := by
    exact
      Nat.mod_lt
        residue
        (by decide)

  have hcases :
      residue % 3 = 0 ∨
      residue % 3 = 1 ∨
      residue % 3 = 2 := by
    omega

  rcases hcases with hzero | hone | htwo

  · simp [decode, encode, hzero]

  · simp [decode, encode, hone]

  · simp [decode, encode, htwo]

/--
Triadic addition is exactly natural-number addition modulo three under
the residue encoding.
-/
theorem encode_add
    (first second : Control) :
    encode (add first second) =
      (encode first + encode second) % 3 := by

  cases first <;>
    cases second <;>
    decide

/--
Decoding the modular sum of two encoded states gives their triadic
sum.
-/
theorem decode_modular_sum
    (first second : Control) :
    decode
        (
          (encode first + encode second) % 3
        ) =
      add first second := by

  rw [
    ← encode_add,
    decode_encode
  ]

/--
The inactive state represents the additive residue zero.
-/
@[simp]
theorem encode_inactive :
    encode Control.inactive =
      0 := by

  rfl

/--
The positive state represents residue one.
-/
@[simp]
theorem encode_positive :
    encode Control.positive =
      1 := by

  rfl

/--
The negative state represents residue two, the canonical representative
of minus one modulo three.
-/
@[simp]
theorem encode_negative :
    encode Control.negative =
      2 := by

  rfl

/--
Triadic negation gives the additive inverse residue modulo three.
-/
theorem encode_neg
    (state : Control) :
    (
      encode state +
      encode (neg state)
    ) % 3 =
      0 := by

  cases state <;>
    decide

/--
Every encoded state has additive order dividing three.
-/
theorem triple_addition_vanishes
    (state : Control) :
    add
        state
        (
          add state state
        ) =
      Control.inactive := by

  cases state <;>
    rfl

/--
Every encoded residue added to itself three times vanishes modulo
three.
-/
theorem triple_residue_vanishes
    (state : Control) :
    (
      encode state +
      encode state +
      encode state
    ) % 3 =
      0 := by

  cases state <;>
    decide

/--
The positive state generates all three states by repeated addition.
-/
theorem positive_generates :
    add Control.positive Control.positive =
        Control.negative
      ∧
    add
        Control.positive
        (
          add Control.positive Control.positive
        ) =
      Control.inactive := by

  constructor <;>
    rfl

end PascalForcingTriadicResidues

#check PascalForcingTriadicResidues.encode
#check PascalForcingTriadicResidues.decode
#check PascalForcingTriadicResidues.encode_lt_three
#check PascalForcingTriadicResidues.encode_injective
#check PascalForcingTriadicResidues.decode_encode
#check PascalForcingTriadicResidues.encode_decode
#check PascalForcingTriadicResidues.encode_add
#check PascalForcingTriadicResidues.decode_modular_sum
#check PascalForcingTriadicResidues.encode_neg
#check PascalForcingTriadicResidues.triple_addition_vanishes
#check PascalForcingTriadicResidues.triple_residue_vanishes
#check PascalForcingTriadicResidues.positive_generates
