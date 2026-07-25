import KTLean.OMBTMonadDynamics
import Mathlib.Tactic

/-!
# Physical Token Interface

## Formal status

**Level 1 — Dimensional and semantic interface for the transition from
OMBT monads to physical tokens.**

## Developmental predecessor

`OMBTMonadDynamics`

The preceding chain has derived:

* the complete 42-glyph spectrum;
* OMBT projection with escrow;
* projected locality;
* directed events;
* four realized views per glyph;
* 168 monads with reversible dynamics.

Those objects are still pre-physical. They carry information, orientation,
memory, and event structure, but they do not yet carry physical
dimensions.

This module introduces the obligations that must be satisfied before a
monad-derived token can be interpreted physically.

The four target token roles are:

* reduced action token `ℏ`;
* causal conversion token `c`;
* gravitational coupling token `G`;
* dimensionless interaction token `α`.

No numerical value is assigned here. In particular, this module does not
define measured constants and does not claim that their physical
magnitudes have yet emerged.

It proves only the dimensional grammar and a provenance-preserving
interface through which later modules must derive the four tokens.
-/

namespace PhysicalTokenInterface

/-
## Dimensional signatures
-/

/--
A dimensional signature in the mass-length-time basis.

The fields are integer exponents in

    M^mass * L^length * T^time.
-/
structure Signature where

  mass :
    Int

  length :
    Int

  time :
    Int

  deriving
    DecidableEq,
    Repr

/--
The dimensionless signature.
-/
def dimensionlessSignature :
    Signature where

  mass :=
    0

  length :=
    0

  time :=
    0

/--
The reduced-action signature:

    M L² T⁻¹.
-/
def actionSignature :
    Signature where

  mass :=
    1

  length :=
    2

  time :=
    -1

/--
The causal-speed signature:

    L T⁻¹.
-/
def causalSignature :
    Signature where

  mass :=
    0

  length :=
    1

  time :=
    -1

/--
The gravitational-coupling signature:

    L³ M⁻¹ T⁻².
-/
def gravitySignature :
    Signature where

  mass :=
    -1

  length :=
    3

  time :=
    -2

/--
The interaction-strength signature is dimensionless.
-/
def interactionSignature :
    Signature :=

  dimensionlessSignature

/-
## Physical token roles
-/

/--
The four semantic roles required for the first physical-token basis.
-/
inductive Role where

  | reducedAction

  | causalConversion

  | gravitationalCoupling

  | interactionStrength

  deriving
    DecidableEq,
    Repr

/--
The required dimensional signature of each physical-token role.
-/
def expectedSignature :
    Role →
      Signature

  | .reducedAction =>
      actionSignature

  | .causalConversion =>
      causalSignature

  | .gravitationalCoupling =>
      gravitySignature

  | .interactionStrength =>
      interactionSignature

/--
The four physical-token roles are pairwise distinct constructors.
-/
theorem role_distinctions :
    Role.reducedAction ≠
        Role.causalConversion
      ∧
    Role.reducedAction ≠
        Role.gravitationalCoupling
      ∧
    Role.reducedAction ≠
        Role.interactionStrength
      ∧
    Role.causalConversion ≠
        Role.gravitationalCoupling
      ∧
    Role.causalConversion ≠
        Role.interactionStrength
      ∧
    Role.gravitationalCoupling ≠
        Role.interactionStrength := by

  decide

/--
There are exactly four physical-token roles.
-/
instance roleFintype :
    Fintype Role where

  elems :=
    {
      .reducedAction,
      .causalConversion,
      .gravitationalCoupling,
      .interactionStrength
    }

  complete := by
    intro role
    cases role <;>
      simp

/--
The physical-token role carrier has cardinality four.
-/
theorem role_card :
    Fintype.card Role =
      4 := by

  decide

/-
## Signature separation
-/

/--
The reduced-action and causal signatures are distinct.
-/
theorem actionSignature_ne_causalSignature :
    actionSignature ≠
      causalSignature := by

  decide

/--
The reduced-action and gravitational signatures are distinct.
-/
theorem actionSignature_ne_gravitySignature :
    actionSignature ≠
      gravitySignature := by

  decide

/--
The causal and gravitational signatures are distinct.
-/
theorem causalSignature_ne_gravitySignature :
    causalSignature ≠
      gravitySignature := by

  decide

/--
The interaction token is dimensionless.
-/
theorem interactionSignature_dimensionless :
    interactionSignature =
      dimensionlessSignature := by

  rfl

/--
The three dimensional basis roles have non-dimensionless signatures.
-/
theorem dimensional_roles_are_not_dimensionless :
    actionSignature ≠
        dimensionlessSignature
      ∧
    causalSignature ≠
        dimensionlessSignature
      ∧
    gravitySignature ≠
        dimensionlessSignature := by

  decide

/-
## Provenance-bearing physical tokens
-/

/--
A candidate physical token retains:

* the OMBT monad from which it was minted;
* its physical semantic role;
* a positive real magnitude.

Its dimensional signature is determined by its role.

The magnitude is deliberately abstract at this stage. Later emergence
modules must derive rather than insert the canonical magnitudes.
-/
structure Token where

  source :
    KTMonad.Monad

  role :
    Role

  magnitude :
    ℝ

  magnitude_positive :
    0 < magnitude

/--
The dimensional signature carried by a physical token.
-/
def Token.signature
    (token : Token) :
    Signature :=

  expectedSignature token.role

/--
Every token carries exactly the signature required by its role.
-/
theorem Token.signature_eq_expected
    (token : Token) :
    token.signature =
      expectedSignature token.role := by

  rfl

/--
Tokenization preserves explicit monadic provenance.
-/
def mint
    (source : KTMonad.Monad)
    (role : Role)
    (magnitude : ℝ)
    (hPositive :
      0 < magnitude) :
    Token where

  source :=
    source

  role :=
    role

  magnitude :=
    magnitude

  magnitude_positive :=
    hPositive

/--
Minting preserves the source monad.
-/
@[simp]
theorem mint_source
    (source : KTMonad.Monad)
    (role : Role)
    (magnitude : ℝ)
    (hPositive :
      0 < magnitude) :
    (
      mint
        source
        role
        magnitude
        hPositive
    ).source =
      source := by

  rfl

/--
Minting preserves the requested physical role.
-/
@[simp]
theorem mint_role
    (source : KTMonad.Monad)
    (role : Role)
    (magnitude : ℝ)
    (hPositive :
      0 < magnitude) :
    (
      mint
        source
        role
        magnitude
        hPositive
    ).role =
      role := by

  rfl

/--
Minting assigns the role's required dimensional signature.
-/
@[simp]
theorem mint_signature
    (source : KTMonad.Monad)
    (role : Role)
    (magnitude : ℝ)
    (hPositive :
      0 < magnitude) :
    (
      mint
        source
        role
        magnitude
        hPositive
    ).signature =
      expectedSignature role := by

  rfl

/-
## Named token predicates
-/

/--
A token is an `ℏ` candidate when it carries the reduced-action role.
-/
def IsHbarToken
    (token : Token) :
    Prop :=

  token.role =
    .reducedAction

/--
A token is a `c` candidate when it carries the causal-conversion role.
-/
def IsCausalToken
    (token : Token) :
    Prop :=

  token.role =
    .causalConversion

/--
A token is a `G` candidate when it carries the gravitational-coupling
role.
-/
def IsGravityToken
    (token : Token) :
    Prop :=

  token.role =
    .gravitationalCoupling

/--
A token is an `α` candidate when it carries the dimensionless
interaction-strength role.
-/
def IsAlphaToken
    (token : Token) :
    Prop :=

  token.role =
    .interactionStrength

/--
Every `ℏ` candidate has the action signature.
-/
theorem hbarToken_has_action_signature
    {token : Token}
    (hToken :
      IsHbarToken token) :
    token.signature =
      actionSignature := by

  unfold IsHbarToken at hToken
  unfold Token.signature

  rw [hToken]

  rfl

/--
Every causal token has the speed signature.
-/
theorem causalToken_has_causal_signature
    {token : Token}
    (hToken :
      IsCausalToken token) :
    token.signature =
      causalSignature := by

  unfold IsCausalToken at hToken
  unfold Token.signature

  rw [hToken]

  rfl

/--
Every gravitational token has the gravitational-coupling signature.
-/
theorem gravityToken_has_gravity_signature
    {token : Token}
    (hToken :
      IsGravityToken token) :
    token.signature =
      gravitySignature := by

  unfold IsGravityToken at hToken
  unfold Token.signature

  rw [hToken]

  rfl

/--
Every alpha token is dimensionless.
-/
theorem alphaToken_is_dimensionless
    {token : Token}
    (hToken :
      IsAlphaToken token) :
    token.signature =
      dimensionlessSignature := by

  unfold IsAlphaToken at hToken
  unfold Token.signature

  rw [hToken]

  rfl

/-
## Token-family interface
-/

/--
A physical-token family over the OMBT monads.

The family supplies one positive token magnitude for every monad and
every physical role.

Later modules must replace this abstract provision with forced
constructions for `ℏ`, `c`, `G`, and `α`.
-/
structure Family where

  magnitude :
    KTMonad.Monad →
      Role →
        ℝ

  magnitude_positive :
    ∀
      (monad : KTMonad.Monad)
      (role : Role),
      0 <
        magnitude monad role

/--
Mint the token supplied by a physical-token family.
-/
def Family.token
    (family : Family)
    (monad : KTMonad.Monad)
    (role : Role) :
    Token :=

  mint
    monad
    role
    (family.magnitude monad role)
    (family.magnitude_positive monad role)

/--
A family token retains its source monad.
-/
@[simp]
theorem Family.token_source
    (family : Family)
    (monad : KTMonad.Monad)
    (role : Role) :
    (family.token monad role).source =
      monad := by

  rfl

/--
A family token carries its requested role.
-/
@[simp]
theorem Family.token_role
    (family : Family)
    (monad : KTMonad.Monad)
    (role : Role) :
    (family.token monad role).role =
      role := by

  rfl

/--
A family token carries the signature required by its role.
-/
@[simp]
theorem Family.token_signature
    (family : Family)
    (monad : KTMonad.Monad)
    (role : Role) :
    (family.token monad role).signature =
      expectedSignature role := by

  rfl

/-
## Developmental bridge
-/

/--
The monad space is already fully derived before physical dimensions are
assigned.
-/
theorem monads_precede_physical_tokenization :
    Fintype.card KTMonad.Monad =
      168 := by

  exact
    OMBTMonadEmergence.existing_monad_card_from_ombt

/--
OMBT monad dynamics are already lawful before dimensional semantics are
introduced.
-/
theorem monad_dynamics_precede_physical_tokenization :
    Function.Involutive
        OMBTMonadDynamics.reverseTemporal
      ∧
    Function.Involutive
        OMBTMonadDynamics.exchangePhase := by

  exact
    ⟨
      OMBTMonadDynamics.reverseTemporal_involutive,
      OMBTMonadDynamics.exchangePhase_involutive
    ⟩

/-
## Capstone
-/

/--
Capstone theorem.

The 168 OMBT-derived monads and their reversible dynamics exist before
physical tokenization. Physical interpretation begins by assigning one
of four distinct semantic roles, each with a forced dimensional
signature:

    ℏ : M L² T⁻¹
    c : L T⁻¹
    G : L³ M⁻¹ T⁻²
    α : dimensionless.

Every candidate physical token retains its source monad, carries a
positive magnitude, and receives its dimensional signature solely from
its physical role.

The numerical magnitudes are not yet derived. This interface therefore
states the exact proof obligations for the subsequent action, causal,
gravity, and alpha emergence modules without smuggling measured
constants into the theory.
-/
theorem physical_token_interface_emerges :
    Fintype.card KTMonad.Monad =
        168
      ∧
    Function.Involutive
        OMBTMonadDynamics.reverseTemporal
      ∧
    Function.Involutive
        OMBTMonadDynamics.exchangePhase
      ∧
    Fintype.card Role =
        4
      ∧
    (
      expectedSignature .reducedAction =
          actionSignature
        ∧
      expectedSignature .causalConversion =
          causalSignature
        ∧
      expectedSignature .gravitationalCoupling =
          gravitySignature
        ∧
      expectedSignature .interactionStrength =
          dimensionlessSignature
    )
      ∧
    (
      ∀
        (source : KTMonad.Monad)
        (role : Role)
        (magnitude : ℝ)
        (hPositive :
          0 < magnitude),
        (
          mint
            source
            role
            magnitude
            hPositive
        ).source =
          source
          ∧
        (
          mint
            source
            role
            magnitude
            hPositive
        ).signature =
          expectedSignature role
    ) := by

  refine
    ⟨
      monads_precede_physical_tokenization,
      OMBTMonadDynamics.reverseTemporal_involutive,
      OMBTMonadDynamics.exchangePhase_involutive,
      role_card,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        rfl,
        rfl,
        rfl,
        rfl
      ⟩

  · intro source role magnitude hPositive

    exact
      ⟨
        mint_source
          source
          role
          magnitude
          hPositive,
        mint_signature
          source
          role
          magnitude
          hPositive
      ⟩

end PhysicalTokenInterface

#check PhysicalTokenInterface.Signature
#check PhysicalTokenInterface.actionSignature
#check PhysicalTokenInterface.causalSignature
#check PhysicalTokenInterface.gravitySignature
#check PhysicalTokenInterface.Role
#check PhysicalTokenInterface.expectedSignature
#check PhysicalTokenInterface.Token
#check PhysicalTokenInterface.Token.signature
#check PhysicalTokenInterface.mint
#check PhysicalTokenInterface.IsHbarToken
#check PhysicalTokenInterface.IsCausalToken
#check PhysicalTokenInterface.IsGravityToken
#check PhysicalTokenInterface.IsAlphaToken
#check PhysicalTokenInterface.alphaToken_is_dimensionless
#check PhysicalTokenInterface.Family
#check PhysicalTokenInterface.monads_precede_physical_tokenization
#check PhysicalTokenInterface.physical_token_interface_emerges
