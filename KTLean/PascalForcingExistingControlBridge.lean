import KTLean.PascalForcingPropagationUniqueness

/-!
# Bridge to the Existing Pascal Modulo Three Controls

## Formal status

**Level 2 — Identification of existing implementation.**

The earlier `PascalMod3` module defines a control state by reducing a
natural number modulo three and selecting:

    0 ↦ inactive
    1 ↦ positive
    2 ↦ negative.

The newer forcing chain independently introduced the residue decoder
with the same interpretation.

This module proves that the two implementations coincide. It does not
yet prove that the binomial field satisfies the two-parent propagation
specification; that recurrence is the next step.
-/

namespace PascalForcingExistingControlBridge

open PascalMod3
open PascalForcingTriadicResidues

/--
The existing `controlOfNat` implementation agrees with the canonical
triadic residue decoder.
-/
theorem controlOfNat_eq_decode
    (value : Nat) :
    controlOfNat value =
      decode value := by

  have hlt :
      value % 3 < 3 := by
    exact
      Nat.mod_lt
        value
        (by decide)

  have hcases :
      value % 3 = 0 ∨
      value % 3 = 1 ∨
      value % 3 = 2 := by
    omega

  rcases hcases with hzero | hone | htwo

  · simp [
      controlOfNat,
      decode,
      hzero
    ]

  · simp [
      controlOfNat,
      decode,
      hone
    ]

  · simp [
      controlOfNat,
      decode,
      htwo
    ]

/--
Decoding is unchanged if its input is first reduced modulo three.
-/
theorem decode_mod_three
    (value : Nat) :
    decode (value % 3) =
      decode value := by

  unfold decode

  rw [Nat.mod_mod]

/--
The existing Pascal control at `(n,k)` is the decoding of the
corresponding binomial coefficient.
-/
theorem control_eq_decode_choose
    (n k : Nat) :
    PascalMod3.control n k =
      decode (Nat.choose n k) := by

  unfold PascalMod3.control

  exact
    controlOfNat_eq_decode
      (Nat.choose n k)

/--
The existing Pascal control is also the decoding of the explicitly
recorded Pascal residue.
-/
theorem control_eq_decode_residue
    (n k : Nat) :
  PascalMod3.control n k =
      decode (residue n k) := by

  rw [
    control_eq_decode_choose,
    ← decode_mod_three
      (Nat.choose n k)
  ]

  rfl

/--
Encoding the existing Pascal control recovers its canonical residue.
-/
theorem encode_control
    (n k : Nat) :
    encode (PascalMod3.control n k) =
      residue n k := by

  rw [control_eq_decode_residue]

  calc
    encode (decode (residue n k)) =
        residue n k % 3 := by
      exact
        encode_decode
          (residue n k)

    _ =
        residue n k := by
      exact
        Nat.mod_eq_of_lt
          (residue_lt_three n k)

/--
The existing Pascal control is positive exactly when its residue is
one.
-/
theorem control_eq_positive_iff
    (n k : Nat) :
  PascalMod3.control n k = .positive ↔
      residue n k = 1 := by

  rw [control_eq_decode_residue]

  have hlt :
      residue n k < 3 :=
    residue_lt_three n k

  have hcases :
      residue n k = 0 ∨
      residue n k = 1 ∨
      residue n k = 2 := by
    omega

  rcases hcases with hzero | hone | htwo

  · simp [decode, hzero]

  · simp [decode, hone]

  · simp [decode, htwo]

/--
The existing Pascal control is negative exactly when its residue is
two.
-/
theorem control_eq_negative_iff
    (n k : Nat) :
  PascalMod3.control n k = .negative ↔
      residue n k = 2 := by

  rw [control_eq_decode_residue]

  have hlt :
      residue n k < 3 :=
    residue_lt_three n k

  have hcases :
      residue n k = 0 ∨
      residue n k = 1 ∨
      residue n k = 2 := by
    omega

  rcases hcases with hzero | hone | htwo

  · simp [decode, hzero]

  · simp [decode, hone]

  · simp [decode, htwo]

end PascalForcingExistingControlBridge

#check PascalForcingExistingControlBridge.controlOfNat_eq_decode
#check PascalForcingExistingControlBridge.decode_mod_three
#check PascalForcingExistingControlBridge.control_eq_decode_choose
#check PascalForcingExistingControlBridge.control_eq_decode_residue
#check PascalForcingExistingControlBridge.encode_control
#check PascalForcingExistingControlBridge.control_eq_positive_iff
#check PascalForcingExistingControlBridge.control_eq_negative_iff
