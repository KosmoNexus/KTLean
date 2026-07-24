import KTLean.GlyphForcingCapstone
import KTLean.GlyphTable

/-!
# The Four-Register Glyph Attractor Signature

## Formal status

**Level 2 — Structural classification of the forced 42-state glyph
carrier into the four basin registers displayed in the Denver
canonical table.**

The forced glyph carrier has coordinates

    Fano address × forced role × forced orientation.

The Denver construction assigns four sedenion-index registers:

    e₈  : Pascal
    e₉  : Fibonacci
    e₁₀ : Wallis
    e₁₁ : Alpha.

The assignment is determined entirely from the forced structural
coordinates:

* Fibonacci: line 1, Frobenius step 1, both orientations;
* Wallis: line 1, Frobenius step 4, together with all of line 5;
* Alpha: line 6, Frobenius step 4, reverse orientation;
* Pascal: every remaining forced glyph state.

This module proves the resulting multiplicity signature

    31, 2, 8, 1

without consulting the registered spectral-value list.

Thus the four-register basin partition is structurally upstream of the
assignments π, φ, e, γ, ζ(2), ζ(3), 147, and 137.

This module proves the partition and its counts. It does not yet prove
that each basin forces its registered analytic constants.
-/

namespace GlyphAttractorSignature

open GlyphForcingTriadicRole
open GlyphForcingOrientation
open GlyphForcingPrimitiveWalk
open GlyphForcingNormalForm

/--
The four canonical attractor registers carried by the sedenion
indexing extension in the Denver glyph table.
-/
inductive Basin where

  | pascal
  | fibonacci
  | wallis
  | alpha

  deriving
    DecidableEq,
    Repr

/--
Explicit finite enumeration of the four basin registers.
-/
instance basinFintype :
    Fintype Basin where

  elems :=
    {
      Basin.pascal,
      Basin.fibonacci,
      Basin.wallis,
      Basin.alpha
    }

  complete := by
    intro basin
    cases basin <;>
      simp

/--
The sedenion indexing register associated with each basin.

The zero-based register numbers correspond to:

    0 ↦ e₈
    1 ↦ e₉
    2 ↦ e₁₀
    3 ↦ e₁₁.
-/
def registerOfBasin :
    Basin →
      Fin 4

  | .pascal =>
      0

  | .fibonacci =>
      1

  | .wallis =>
      2

  | .alpha =>
      3

/--
Recover the basin represented by one sedenion indexing register.
-/
def basinOfRegister :
    Fin 4 →
      Basin

  | 0 =>
      .pascal

  | 1 =>
      .fibonacci

  | 2 =>
      .wallis

  | 3 =>
      .alpha

/--
Register recovery after basin encoding returns the original basin.
-/
@[simp]
theorem basinOfRegister_registerOfBasin
    (basin : Basin) :
    basinOfRegister
        (registerOfBasin basin) =
      basin := by

  cases basin <;>
    rfl

/--
Basin recovery followed by register encoding returns the original
register.
-/
@[simp]
theorem registerOfBasin_basinOfRegister
    (register : Fin 4) :
    registerOfBasin
        (basinOfRegister register) =
      register := by

  fin_cases register <;>
    rfl

/--
The four basin classes are canonically equivalent to the four
sedenion indexing registers.
-/
def basinEquivRegister :
    Basin ≃
      Fin 4 where

  toFun :=
    registerOfBasin

  invFun :=
    basinOfRegister

  left_inv :=
    basinOfRegister_registerOfBasin

  right_inv :=
    registerOfBasin_basinOfRegister

/--
Classify one independently forced primitive walk into its canonical
attractor basin.

The conditions are expressed entirely in forced coordinates and do not
inspect the registered spectral value attached to the corresponding
glyph.
-/
def basinOfWalk
    (walk : PrimitiveWalk) :
    Basin :=

  if
    walk.1 = 1
      ∧
    walk.2.1 = 0
  then
    .fibonacci

  else if
    (
      walk.1 = 1
        ∧
      walk.2.1 = 2
    )
      ∨
    walk.1 = 5
  then
    .wallis

  else if
    walk.1 = 6
      ∧
    walk.2.1 = 2
      ∧
    walk.2.2 =
      ForcedOrientation.reverse
  then
    .alpha

  else
    .pascal

/--
Classify one existing canonical coordinate triple through its unique
forced primitive-walk normal form.
-/
def basinOfCoordinates
    (coordinates : KTGlyph.Coordinates) :
    Basin :=

  basinOfWalk
    (
      fromExistingCoordinates
        coordinates
    )

/--
The fiber of forced primitive walks lying in one basin.
-/
abbrev WalksInBasin
    (basin : Basin) :=

  {
    walk : PrimitiveWalk //
      basinOfWalk walk =
        basin
  }

/--
The executable canonical coordinate rows lying in one basin.
-/
def coordinatesInBasin
    (basin : Basin) :
    List KTGlyph.Coordinates :=

  GlyphTable.coordinates.filter
    (
      fun coordinates =>
        basinOfCoordinates coordinates =
          basin
    )

/--
The Fibonacci basin consists of line 1, step 1, in both orientations.
-/
theorem fibonacci_characterization
    (walk : PrimitiveWalk) :
    basinOfWalk walk =
        Basin.fibonacci
      ↔
    walk.1 = 1
      ∧
    walk.2.1 = 0 := by

  rcases walk with
    ⟨address, role, orientation⟩

  fin_cases address <;>
    fin_cases role <;>
    cases orientation <;>
    decide

/--
The Wallis basin consists of line 1 at step 4 together with the whole
six-state fiber over line 5.
-/
theorem wallis_characterization
    (walk : PrimitiveWalk) :
    basinOfWalk walk =
        Basin.wallis
      ↔
    (
      walk.1 = 1
        ∧
      walk.2.1 = 2
    )
      ∨
    walk.1 = 5 := by

  rcases walk with
    ⟨address, role, orientation⟩

  fin_cases address <;>
    fin_cases role <;>
    cases orientation <;>
    decide

/--
The Alpha basin is the unique reverse-framed state at line 6 and
Frobenius step 4.
-/
theorem alpha_characterization
    (walk : PrimitiveWalk) :
    basinOfWalk walk =
        Basin.alpha
      ↔
    walk.1 = 6
      ∧
    walk.2.1 = 2
      ∧
    walk.2.2 =
      ForcedOrientation.reverse := by

  rcases walk with
    ⟨address, role, orientation⟩

  fin_cases address <;>
    fin_cases role <;>
    cases orientation <;>
    decide

/--
The Pascal basin is exactly the complement of the three exceptional
structural basin rules.
-/
theorem pascal_characterization
    (walk : PrimitiveWalk) :
    basinOfWalk walk =
        Basin.pascal
      ↔
    ¬
      (
        walk.1 = 1
          ∧
        walk.2.1 = 0
      )
      ∧
    ¬
      (
        (
          walk.1 = 1
            ∧
          walk.2.1 = 2
        )
          ∨
        walk.1 = 5
      )
      ∧
    ¬
      (
        walk.1 = 6
          ∧
        walk.2.1 = 2
          ∧
        walk.2.2 =
          ForcedOrientation.reverse
      ) := by

  rcases walk with
    ⟨address, role, orientation⟩

  fin_cases address <;>
    fin_cases role <;>
    cases orientation <;>
    decide

/--
The Pascal basin contains exactly 31 forced glyph states.
-/
theorem card_pascal :
    Fintype.card
        (WalksInBasin Basin.pascal) =
      31 := by

  native_decide

/--
The Fibonacci basin contains exactly two forced glyph states.
-/
theorem card_fibonacci :
    Fintype.card
        (WalksInBasin Basin.fibonacci) =
      2 := by

  native_decide

/--
The Wallis basin contains exactly eight forced glyph states.
-/
theorem card_wallis :
    Fintype.card
        (WalksInBasin Basin.wallis) =
      8 := by

  native_decide

/--
The Alpha basin contains exactly one forced glyph state.
-/
theorem card_alpha :
    Fintype.card
        (WalksInBasin Basin.alpha) =
      1 := by

  native_decide

/--
The corresponding executable coordinate subsets have the same
31, 2, 8, 1 multiplicities.
-/
theorem coordinate_basin_lengths :
    (
      coordinatesInBasin Basin.pascal
    ).length =
        31
      ∧
    (
      coordinatesInBasin Basin.fibonacci
    ).length =
        2
      ∧
    (
      coordinatesInBasin Basin.wallis
    ).length =
        8
      ∧
    (
      coordinatesInBasin Basin.alpha
    ).length =
        1 := by

  native_decide

/--
The four basin multiplicities exhaust all 42 forced glyph states.
-/
theorem basin_counts_sum_to_glyph_count :
    31 + 2 + 8 + 1 =
      Fintype.card PrimitiveWalk := by

  rw [
    card_primitiveWalk
  ]



/--
The basin multiplicities have the canonical power-of-two form shown in
the Denver sedenion register encoding.
-/
theorem basin_power_signature :
    31 =
        2 ^ 5 - 1
      ∧
    2 =
        2 ^ 1
      ∧
    8 =
        2 ^ 3
      ∧
    1 =
        2 ^ 0 := by

  decide

/--
The complete four-register multiplicity signature.
-/
def multiplicitySignature :
    List Nat :=

  [
    Fintype.card
      (WalksInBasin Basin.pascal),

    Fintype.card
      (WalksInBasin Basin.fibonacci),

    Fintype.card
      (WalksInBasin Basin.wallis),

    Fintype.card
      (WalksInBasin Basin.alpha)
  ]

/--
The computed structural signature is exactly `31, 2, 8, 1`.
-/
theorem multiplicitySignature_eq :
    multiplicitySignature =
      [31, 2, 8, 1] := by

  native_decide

/--
Every forced primitive walk belongs to exactly one basin.
-/
theorem walk_has_unique_basin
    (walk : PrimitiveWalk) :
    ∃! basin : Basin,
      basinOfWalk walk =
        basin := by

  refine
    ⟨
      basinOfWalk walk,
      rfl,
      ?_
    ⟩

  intro other hOther

  exact
    hOther.symm

/--
Capstone statement for the structural sedenion signature.

The forced 42-state glyph carrier admits a complete four-register
partition with multiplicities `31, 2, 8, 1`, and those multiplicities
exhaust the carrier.
-/
theorem forced_glyphs_have_sedenion_basin_signature :
    Fintype.card PrimitiveWalk =
        42
      ∧
    Fintype.card
        (WalksInBasin Basin.pascal) =
        31
      ∧
    Fintype.card
        (WalksInBasin Basin.fibonacci) =
        2
      ∧
    Fintype.card
        (WalksInBasin Basin.wallis) =
        8
      ∧
    Fintype.card
        (WalksInBasin Basin.alpha) =
        1
      ∧
    multiplicitySignature =
        [31, 2, 8, 1] := by

  exact
    ⟨
      card_primitiveWalk,
      card_pascal,
      card_fibonacci,
      card_wallis,
      card_alpha,
      multiplicitySignature_eq
    ⟩

end GlyphAttractorSignature

#check GlyphAttractorSignature.Basin
#check GlyphAttractorSignature.registerOfBasin
#check GlyphAttractorSignature.basinEquivRegister
#check GlyphAttractorSignature.basinOfWalk
#check GlyphAttractorSignature.basinOfCoordinates
#check GlyphAttractorSignature.fibonacci_characterization
#check GlyphAttractorSignature.wallis_characterization
#check GlyphAttractorSignature.alpha_characterization
#check GlyphAttractorSignature.pascal_characterization
#check GlyphAttractorSignature.card_pascal
#check GlyphAttractorSignature.card_fibonacci
#check GlyphAttractorSignature.card_wallis
#check GlyphAttractorSignature.card_alpha
#check GlyphAttractorSignature.coordinate_basin_lengths
#check GlyphAttractorSignature.basin_power_signature
#check GlyphAttractorSignature.multiplicitySignature_eq
#check GlyphAttractorSignature.walk_has_unique_basin
#check GlyphAttractorSignature.forced_glyphs_have_sedenion_basin_signature
