import KTLean.GlyphSpectralFundamentalIntegers
import Mathlib.Tactic

/-!
# The Triadic Wallis Kernel

## Formal status

**Level 2 — Exact discrete rational kernel for the π glyph.**

The KT Wallis construction reads a central triad:

    lower, center, upper

and forms the closure invariant

    center² / (lower * upper).

At stage `n`, using the positive odd-even-odd triple

    2n + 1, 2n + 2, 2n + 3,

the observable is exactly

    4(n+1)² / (4(n+1)² - 1),

the corresponding Wallis factor.

This module proves the rational factor identity and the deterministic
multiplicative accumulation law. It does not yet prove the real-analysis
limit of the infinite product to `π / 2`.
-/

namespace GlyphSpectralWallisKernel

/--
The lower member of the stage-`n` readout triad.
-/
def lowerReadout
    (n : Nat) :
    Nat :=
  2 * n + 1

/--
The central member of the stage-`n` readout triad.
-/
def centralReadout
    (n : Nat) :
    Nat :=
  2 * n + 2

/--
The upper member of the stage-`n` readout triad.
-/
def upperReadout
    (n : Nat) :
    Nat :=
  2 * n + 3

/--
The three readouts are consecutive.
-/
theorem readout_triad_consecutive
    (n : Nat) :
    centralReadout n =
        lowerReadout n + 1
      ∧
    upperReadout n =
        centralReadout n + 1 := by

  constructor <;>
    simp [
      lowerReadout,
      centralReadout,
      upperReadout
    ]

/--
The rational closure observable formed from the central triad.
-/
def wallisObservable
    (n : Nat) :
    ℚ :=

  (
    centralReadout n : ℚ
  ) ^ 2
    /
  (
    (
      lowerReadout n : ℚ
    )
      *
    (
      upperReadout n : ℚ
    )
  )

/--
The standard stage-`n` Wallis factor, indexed from zero.
-/
def wallisFactor
    (n : Nat) :
    ℚ :=

  4 * ((n + 1 : Nat) : ℚ) ^ 2
    /
  (
    4 * ((n + 1 : Nat) : ℚ) ^ 2 - 1
  )

/--
The lower readout is nonzero.
-/
theorem lowerReadout_ne_zero
    (n : Nat) :
    (lowerReadout n : ℚ) ≠ 0 := by

  unfold lowerReadout

  have hn :
      (0 : ℚ) ≤ (n : ℚ) := by
    positivity

  push_cast

  nlinarith

/--
The denominator of the Wallis factor is nonzero.
-/
theorem wallisFactor_denominator_ne_zero
    (n : Nat) :
    4 * ((n + 1 : Nat) : ℚ) ^ 2 - 1 ≠
      0 := by

  have h :
      (1 : ℚ) ≤
        ((n + 1 : Nat) : ℚ) := by

    exact_mod_cast
      Nat.succ_le_succ
        (Nat.zero_le n)

  nlinarith [
    sq_nonneg
      (((n + 1 : Nat) : ℚ) - 1)
  ]

/--
The triadic readout observable is exactly the Wallis factor.
-/
theorem wallisObservable_eq_factor
    (n : Nat) :
    wallisObservable n =
      wallisFactor n := by

  unfold wallisObservable
  unfold wallisFactor
  unfold lowerReadout
  unfold centralReadout
  unfold upperReadout

  push_cast

  have hNumerator :
      (2 * (n : ℚ) + 2) ^ 2 =
        4 * ((n : ℚ) + 1) ^ 2 := by

    ring

  have hDenominator :
      (2 * (n : ℚ) + 1)
          *
        (2 * (n : ℚ) + 3) =
      4 * ((n : ℚ) + 1) ^ 2 - 1 := by

    ring

  rw [
    hNumerator,
    hDenominator
  ]

/--
Every Wallis factor is positive.
-/
theorem wallisFactor_positive
    (n : Nat) :
    0 <
      wallisFactor n := by

  unfold wallisFactor

  have hN :
      (1 : ℚ) ≤
        ((n + 1 : Nat) : ℚ) := by

    exact_mod_cast
      Nat.succ_le_succ
        (Nat.zero_le n)

  apply div_pos

  · positivity

  · nlinarith

/--
Finite multiplicative accumulation of the Wallis stream.
-/
def wallisProduct :
    Nat →
      ℚ

  | 0 =>
      1

  | n + 1 =>
      wallisProduct n *
        wallisFactor n

/--
The empty Wallis product is one.
-/
@[simp]
theorem wallisProduct_zero :
    wallisProduct 0 =
      1 := by

  rfl

/--
Each stage is uniquely determined by the previous product and the next
triadic Wallis factor.
-/
@[simp]
theorem wallisProduct_succ
    (n : Nat) :
    wallisProduct (n + 1) =
      wallisProduct n *
        wallisFactor n := by

  rfl

/--
The finite product remains positive at every depth.
-/
theorem wallisProduct_positive
    (n : Nat) :
    0 <
      wallisProduct n := by

  induction n with

  | zero =>
      norm_num

  | succ n ih =>
      rw [
        wallisProduct_succ
      ]

      exact
        mul_pos
          ih
          (wallisFactor_positive n)

/--
The canonical π pair occupies glyphs 11 and 12.
-/
theorem circle_pair_registered :
    GlyphSpectrum.values[10]? =
        some
          (.inverse .circleConstant)
      ∧
    GlyphSpectrum.values[11]? =
        some
          .circleConstant := by

  native_decide

/--
Capstone theorem.

Every stage is generated from one consecutive odd-even-odd triad,
whose central-square closure invariant is exactly the corresponding
Wallis factor. These factors accumulate deterministically and remain
positive.
-/
theorem triadic_readout_forces_wallis_stream :
    (∀ n : Nat,
      wallisObservable n =
        wallisFactor n)
      ∧
    (∀ n : Nat,
      wallisProduct (n + 1) =
        wallisProduct n *
          wallisFactor n)
      ∧
    (∀ n : Nat,
      0 <
        wallisProduct n)
      ∧
    GlyphSpectrum.values[10]? =
        some
          (.inverse .circleConstant)
      ∧
    GlyphSpectrum.values[11]? =
        some
          .circleConstant := by

  exact
    ⟨
      wallisObservable_eq_factor,
      wallisProduct_succ,
      wallisProduct_positive,
      circle_pair_registered.1,
      circle_pair_registered.2
    ⟩

end GlyphSpectralWallisKernel

#check GlyphSpectralWallisKernel.lowerReadout
#check GlyphSpectralWallisKernel.centralReadout
#check GlyphSpectralWallisKernel.upperReadout
#check GlyphSpectralWallisKernel.readout_triad_consecutive
#check GlyphSpectralWallisKernel.wallisObservable
#check GlyphSpectralWallisKernel.wallisFactor
#check GlyphSpectralWallisKernel.wallisObservable_eq_factor
#check GlyphSpectralWallisKernel.wallisFactor_positive
#check GlyphSpectralWallisKernel.wallisProduct
#check GlyphSpectralWallisKernel.wallisProduct_positive
#check GlyphSpectralWallisKernel.circle_pair_registered
#check GlyphSpectralWallisKernel.triadic_readout_forces_wallis_stream
