import KTLean.PhysicalGravityToken
import KTLean.GlyphSpectralAlphaBoundary
import Mathlib.Tactic

/-!
# Emergence of the Physical Alpha Invariant

## Formal status

**Level 2 — Exact structural emergence of the dimensionless
eight-dimensional alpha invariant from reversible projection-channel
capacity.**

## Developmental predecessor

`PhysicalGravityToken`

The preceding physical-token development supplies the dimensional token
grammar:

* reduced action token `ℏ`;
* causal conversion token `c`;
* gravitational coupling token `G`.

The electromagnetic interaction invariant `α` differs fundamentally from
those three tokens. It is dimensionless.

The already formalized projection boundary proves that an eight-channel
carrier projected through four-channel selections has:

    C(8,4) = 70

unoriented channels. Reversible transport doubles this count:

    2 C(8,4) = 140.

One primordial triad is reserved for closure:

    140 - 3 = 137.

Thus the usable reversible channel capacity is forced to be:

    α⁻¹₈ = 137.

The corresponding dimensionless interaction invariant is:

    α₈ = 1 / 137.

This module proves that exact structural invariant, its positivity,
uniqueness, reciprocal relation, monadic provenance, and dimensionless
signature.

It does not yet derive the projected four-dimensional correction that
shifts the inverse value from exactly `137` to the physical low-energy
value near `137.035999...`. That is a later projection-refinement
obligation.
-/

namespace PhysicalAlphaInvariant

/-
## Reversible channel capacity
-/

/--
The exact number of usable reversible projection channels.
-/
def usableChannelCount :
    Nat :=

  GlyphSpectralAlphaBoundary.usableProjectionChannels

/--
The projection architecture forces exactly 137 usable channels.
-/
theorem usableChannelCount_eq_oneThirtySeven :
    usableChannelCount =
      137 := by

  exact
    GlyphSpectralAlphaBoundary.usableProjectionChannels_eq_oneThirtySeven

/--
The usable channel count is positive.
-/
theorem usableChannelCount_positive :
    0 <
      usableChannelCount := by

  rw [usableChannelCount_eq_oneThirtySeven]

  norm_num

/--
The usable channel count is nonzero.
-/
theorem usableChannelCount_ne_zero :
    usableChannelCount ≠
      0 := by

  exact
    Nat.ne_of_gt
      usableChannelCount_positive

/-
## Real channel-capacity magnitude
-/

/--
The inverse alpha magnitude supplied by the usable channel capacity.

    α⁻¹₈ = 137.
-/
noncomputable def alphaInverseMagnitude :
    ℝ :=

  usableChannelCount

/--
The inverse alpha magnitude is exactly 137.
-/
theorem alphaInverseMagnitude_eq_oneThirtySeven :
    alphaInverseMagnitude =
      137 := by

  unfold alphaInverseMagnitude

  exact_mod_cast
    usableChannelCount_eq_oneThirtySeven

/--
The inverse alpha magnitude is positive.
-/
theorem alphaInverseMagnitude_positive :
    0 <
      alphaInverseMagnitude := by

  rw [alphaInverseMagnitude_eq_oneThirtySeven]

  norm_num

/--
The inverse alpha magnitude is nonzero.
-/
theorem alphaInverseMagnitude_ne_zero :
    alphaInverseMagnitude ≠
      0 := by

  exact
    ne_of_gt
      alphaInverseMagnitude_positive

/-
## Dimensionless alpha invariant
-/

/--
The eight-dimensional interaction invariant.

    α₈ = (α⁻¹₈)⁻¹ = 1 / 137.
-/
noncomputable def alphaMagnitude :
    ℝ :=

  alphaInverseMagnitude⁻¹

/--
The structural alpha invariant is exactly `1 / 137`.
-/
theorem alphaMagnitude_eq_one_div_oneThirtySeven :
    alphaMagnitude =
      (1 : ℝ) / 137 := by

  unfold alphaMagnitude

  rw [alphaInverseMagnitude_eq_oneThirtySeven]

  norm_num

/--
The structural alpha invariant is positive.
-/
theorem alphaMagnitude_positive :
    0 <
      alphaMagnitude := by

  unfold alphaMagnitude

  exact
    inv_pos.mpr
      alphaInverseMagnitude_positive

/--
The structural alpha invariant is nonzero.
-/
theorem alphaMagnitude_ne_zero :
    alphaMagnitude ≠
      0 := by

  exact
    ne_of_gt
      alphaMagnitude_positive

/--
Alpha and its inverse channel magnitude multiply to one.

    α₈ α⁻¹₈ = 1.
-/
theorem alpha_mul_alphaInverse :
    alphaMagnitude *
        alphaInverseMagnitude =
      1 := by

  unfold alphaMagnitude

  exact
    inv_mul_cancel₀
      alphaInverseMagnitude_ne_zero

/--
The inverse channel magnitude multiplied by alpha also gives one.
-/
theorem alphaInverse_mul_alpha :
    alphaInverseMagnitude *
        alphaMagnitude =
      1 := by

  rw [mul_comm]

  exact
    alpha_mul_alphaInverse

/--
The inverse of the structural alpha invariant is exactly 137.
-/
theorem alphaMagnitude_inverse_eq_oneThirtySeven :
    alphaMagnitude⁻¹ =
      137 := by

  unfold alphaMagnitude

  rw [inv_inv]

  exact
    alphaInverseMagnitude_eq_oneThirtySeven

/-
## Uniqueness from channel normalization
-/

/--
The structural alpha invariant is the unique real value whose product
with the usable channel capacity is one.
-/
theorem alphaMagnitude_unique
    (candidate : ℝ)
    (hCandidate :
      candidate *
          alphaInverseMagnitude =
        1) :
    candidate =
      alphaMagnitude := by

  apply
    mul_right_cancel₀
      alphaInverseMagnitude_ne_zero

  calc
    candidate *
        alphaInverseMagnitude =
      1 :=
        hCandidate

    _ =
      alphaMagnitude *
        alphaInverseMagnitude :=
        alpha_mul_alphaInverse.symm

/--
There exists exactly one positive dimensionless interaction magnitude
normalized by the usable reversible channel capacity.
-/
theorem existsUnique_alphaMagnitude :
    ∃! interaction : ℝ,
      0 < interaction
        ∧
      interaction *
          alphaInverseMagnitude =
        1 := by

  refine
    ⟨
      alphaMagnitude,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        alphaMagnitude_positive,
        alpha_mul_alphaInverse
      ⟩

  · intro candidate hCandidate

    exact
      alphaMagnitude_unique
        candidate
        hCandidate.2

/-
## Projection provenance
-/

/--
The unoriented eight-to-four projection carrier contains 70 channels.
-/
theorem unoriented_channels_eq_seventy :
    GlyphSpectralAlphaBoundary.unorientedProjectionChannels =
      70 := by

  exact
    GlyphSpectralAlphaBoundary.unorientedProjectionChannels_eq_seventy

/--
Reversible orientation doubles the carrier to 140 channels.
-/
theorem reversible_channels_eq_oneForty :
    GlyphSpectralAlphaBoundary.reversibleProjectionChannels =
      140 := by

  exact
    GlyphSpectralAlphaBoundary.reversibleProjectionChannels_eq_oneForty

/--
One primordial closure triad is reserved.
-/
theorem closure_overhead_eq_three :
    GlyphSpectralAlphaBoundary.triadicClosureOverhead =
      3 := by

  rfl

/--
The complete finite channel derivation is

    2 C(8,4) - 3 = 137.
-/
theorem alpha_channel_formula :
    2 * Nat.choose 8 4 - 3 =
      137 := by

  exact
    GlyphSpectralAlphaBoundary.alphaBoundary_formula

/--
The structural inverse-alpha value is the usable reversible projection
capacity, not an independently inserted number.
-/
theorem alphaInverse_is_projection_capacity :
    alphaInverseMagnitude =
      GlyphSpectralAlphaBoundary.usableProjectionChannels := by

  rfl

/--
The final canonical glyph carries the inverse-alpha boundary value 137.
-/
theorem alpha_boundary_is_final_glyph :
    GlyphSpectrum.values[41]? =
      some
        (.natural 137) := by

  exact
    GlyphSpectralAlphaBoundary.alphaBoundary_registered_at_glyph_fortyTwo

/-
## Minting the dimensionless alpha token
-/

/--
Mint the alpha interaction token over one OMBT monad.
-/
noncomputable def alphaToken
    (source : KTMonad.Monad) :
    PhysicalTokenInterface.Token :=

  PhysicalTokenInterface.mint
    source
    .interactionStrength
    alphaMagnitude
    alphaMagnitude_positive

/--
The alpha token retains its source monad.
-/
@[simp]
theorem alphaToken_source
    (source : KTMonad.Monad) :
    (alphaToken source).source =
      source := by

  rfl

/--
The alpha token carries the interaction-strength role.
-/
@[simp]
theorem alphaToken_role
    (source : KTMonad.Monad) :
    (alphaToken source).role =
      .interactionStrength := by

  rfl

/--
The alpha token carries the structural magnitude `1 / 137`.
-/
@[simp]
theorem alphaToken_magnitude
    (source : KTMonad.Monad) :
    (alphaToken source).magnitude =
      alphaMagnitude := by

  rfl

/--
The alpha token is dimensionless.
-/
theorem alphaToken_signature
    (source : KTMonad.Monad) :
    (alphaToken source).signature =
      PhysicalTokenInterface.dimensionlessSignature := by

  exact
    PhysicalTokenInterface.alphaToken_is_dimensionless
      (by rfl)

/--
The alpha token has positive magnitude.
-/
theorem alphaToken_positive
    (source : KTMonad.Monad) :
    0 <
      (alphaToken source).magnitude := by

  exact
    (alphaToken source).magnitude_positive

/-
## Universality across the monad space
-/

/--
Every monad carries the same structural alpha invariant.
-/
theorem alphaMagnitude_independent_of_monad
    (left right : KTMonad.Monad) :
    (alphaToken left).magnitude =
      (alphaToken right).magnitude := by

  rfl

/--
Temporal reversal preserves the alpha invariant.
-/
theorem reverseTemporal_preserves_alphaMagnitude
    (monad : KTMonad.Monad) :
    (
      alphaToken
        (OMBTMonadDynamics.reverseTemporal monad)
    ).magnitude =
      (alphaToken monad).magnitude := by

  rfl

/--
Visible/escrow phase exchange preserves the alpha invariant.
-/
theorem exchangePhase_preserves_alphaMagnitude
    (monad : KTMonad.Monad) :
    (
      alphaToken
        (OMBTMonadDynamics.exchangePhase monad)
    ).magnitude =
      (alphaToken monad).magnitude := by

  rfl

/-
## Distinction from dimensional tokens
-/

/--
The alpha role is dimensionally distinct from the action, causal, and
gravitational roles.
-/
theorem alpha_is_not_dimensional_conversion :
    PhysicalTokenInterface.expectedSignature
        .interactionStrength =
        PhysicalTokenInterface.dimensionlessSignature
      ∧
    PhysicalTokenInterface.expectedSignature
        .reducedAction ≠
        PhysicalTokenInterface.dimensionlessSignature
      ∧
    PhysicalTokenInterface.expectedSignature
        .causalConversion ≠
        PhysicalTokenInterface.dimensionlessSignature
      ∧
    PhysicalTokenInterface.expectedSignature
        .gravitationalCoupling ≠
        PhysicalTokenInterface.dimensionlessSignature := by

  native_decide

/--
The dimensional token grammar is established before the alpha invariant
is interpreted physically.
-/
theorem dimensional_tokens_precede_alpha :
    PhysicalTokenInterface.expectedSignature
        .reducedAction =
        PhysicalTokenInterface.actionSignature
      ∧
    PhysicalTokenInterface.expectedSignature
        .causalConversion =
        PhysicalTokenInterface.causalSignature
      ∧
    PhysicalTokenInterface.expectedSignature
        .gravitationalCoupling =
        PhysicalTokenInterface.gravitySignature
      ∧
    PhysicalTokenInterface.expectedSignature
        .interactionStrength =
        PhysicalTokenInterface.dimensionlessSignature := by

  exact
    ⟨
      rfl,
      rfl,
      rfl,
      rfl
    ⟩

/-
## Capstone
-/

/--
Capstone theorem.

The reversible eight-to-four projection interface supplies 70 unoriented
channels. Reversibility doubles that carrier to 140, and reservation of
one primordial closure triad leaves exactly 137 usable channels:

    2 C(8,4) - 3 = 137.

The unique positive dimensionless interaction invariant normalized by
that capacity is therefore:

    α₈ = 1 / 137,
    α⁻¹₈ = 137.

Over every OMBT monad, the alpha token retains monadic provenance, carries
the dimensionless interaction-strength role, and remains invariant under
temporal reversal and visible/escrow exchange.

This proves the exact structural eight-dimensional alpha invariant. It
does not yet prove the projected four-dimensional correction responsible
for the measured low-energy inverse value near `137.035999...`.
-/
theorem physical_alpha_invariant_emerges :
    (
      GlyphSpectralAlphaBoundary.unorientedProjectionChannels =
          70
        ∧
      GlyphSpectralAlphaBoundary.reversibleProjectionChannels =
          140
        ∧
      GlyphSpectralAlphaBoundary.triadicClosureOverhead =
          3
        ∧
      usableChannelCount =
          137
    )
      ∧
    (
      ∃! interaction : ℝ,
        0 < interaction
          ∧
        interaction *
            alphaInverseMagnitude =
          1
    )
      ∧
    alphaInverseMagnitude =
      137
      ∧
    alphaMagnitude =
      (1 : ℝ) / 137
      ∧
    alphaMagnitude⁻¹ =
      137
      ∧
    (
      ∀ source : KTMonad.Monad,
        (alphaToken source).source =
            source
          ∧
        (alphaToken source).role =
            .interactionStrength
          ∧
        (alphaToken source).signature =
            PhysicalTokenInterface.dimensionlessSignature
          ∧
        0 <
          (alphaToken source).magnitude
    )
      ∧
    GlyphSpectrum.values[41]? =
      some
        (.natural 137) := by

  refine
    ⟨
      ?_,
      existsUnique_alphaMagnitude,
      alphaInverseMagnitude_eq_oneThirtySeven,
      alphaMagnitude_eq_one_div_oneThirtySeven,
      alphaMagnitude_inverse_eq_oneThirtySeven,
      ?_,
      alpha_boundary_is_final_glyph
    ⟩

  · exact
      ⟨
        unoriented_channels_eq_seventy,
        reversible_channels_eq_oneForty,
        closure_overhead_eq_three,
        usableChannelCount_eq_oneThirtySeven
      ⟩

  · intro source

    exact
      ⟨
        alphaToken_source source,
        alphaToken_role source,
        alphaToken_signature source,
        alphaToken_positive source
      ⟩

end PhysicalAlphaInvariant

#check PhysicalAlphaInvariant.usableChannelCount
#check PhysicalAlphaInvariant.usableChannelCount_eq_oneThirtySeven
#check PhysicalAlphaInvariant.alphaInverseMagnitude
#check PhysicalAlphaInvariant.alphaMagnitude
#check PhysicalAlphaInvariant.alphaMagnitude_eq_one_div_oneThirtySeven
#check PhysicalAlphaInvariant.alpha_mul_alphaInverse
#check PhysicalAlphaInvariant.existsUnique_alphaMagnitude
#check PhysicalAlphaInvariant.alpha_channel_formula
#check PhysicalAlphaInvariant.alphaToken
#check PhysicalAlphaInvariant.alphaToken_signature
#check PhysicalAlphaInvariant.alpha_is_not_dimensional_conversion
#check PhysicalAlphaInvariant.physical_alpha_invariant_emerges
