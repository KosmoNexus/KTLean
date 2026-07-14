import KTLean.MemoryEscrowRouted

/-!
# Routed Tokenization

This module formalizes tokenization of the complete routed
state.

A token contains:

1. the visible projected state;
2. the hidden route-address escrow record.

Encoding loses no information:

    complete state ≃ token

The complete Tkairos step is transported through this
equivalence to a lawful token step.

Thus tokenization is not merely labeling. It is an exact
change of representation preserving evolution, history,
and recovery.
-/

namespace RoutedTokenization


/--
A routed token contains visible information together with
the escrow record required to reconstruct the complete
state.
-/
abbrev Token :=
  MemoryEscrowRouted.VisibleState ×
    MemoryEscrowRouted.EscrowRecord


/--
Encode a complete routed state as a token.
-/
def encode
    (complete :
      MemoryEscrowRouted.CompleteState) :
    Token :=

  MemoryEscrowRouted.decompose complete


/--
Decode a token into the complete routed state it
represents.
-/
def decode
    (token : Token) :
    MemoryEscrowRouted.CompleteState :=

  MemoryEscrowRouted.reconstruct token


/--
Encoding and then decoding returns the original complete
state.
-/
@[simp]
theorem decode_encode
    (complete :
      MemoryEscrowRouted.CompleteState) :

    decode
        (encode complete) =
      complete := by

  exact
    MemoryEscrowRouted.reconstruct_decompose
      complete


/--
Decoding and then encoding returns the original token.
-/
@[simp]
theorem encode_decode
    (token : Token) :

    encode
        (decode token) =
      token := by

  exact
    MemoryEscrowRouted.decompose_reconstruct
      token


/--
Complete routed states and routed tokens are equivalent.
-/
def tokenEquiv :

    MemoryEscrowRouted.CompleteState ≃
      Token :=

  MemoryEscrowRouted.completeEquivVisibleEscrow


/--
Token encoding is injective.
-/
theorem encode_injective :

    Function.Injective encode := by

  intro x y hxy

  have :=
    congrArg decode hxy

  simpa using this


/--
Token encoding is surjective.
-/
theorem encode_surjective :

    Function.Surjective encode := by

  intro token

  exact
    ⟨decode token, encode_decode token⟩


/--
Token encoding is bijective.
-/
theorem encode_bijective :

    Function.Bijective encode := by

  exact
    ⟨
      encode_injective,
      encode_surjective
    ⟩


/-
## Token dynamics
-/

/--
The lawful token step evolves:

- the visible component by visible exchange;
- the escrow component by route exchange.
-/
def tokenStep
    (token : Token) :
    Token :=

  (
    MemoryEscrowRouted.visibleStep
      token.1,

    MemoryEscrowRouted.escrowStep
      token.2
  )


/--
Encoding a complete successor gives the token successor.

This is the principal dynamical tokenization theorem.
-/
theorem encode_completeStep
    (complete :
      MemoryEscrowRouted.CompleteState) :

    encode
        (
          MemoryEscrowRouted.completeStep
            complete
        ) =

      tokenStep
        (encode complete) := by

  exact
    MemoryEscrowRouted.decompose_completeStep
      complete


/--
Decoding a token successor gives the complete successor.
-/
theorem decode_tokenStep
    (token : Token) :

    decode
        (tokenStep token) =

      MemoryEscrowRouted.completeStep
        (decode token) := by

  exact
    MemoryEscrowRouted.reconstruct_step
      token


/--
The complete transition is conjugate to the token
transition through the encoding equivalence.
-/
theorem completeStep_conjugate :

    encode ∘
        MemoryEscrowRouted.completeStep =

      tokenStep ∘ encode := by

  funext complete

  exact
    encode_completeStep complete


/--
The token transition is involutive.
-/
theorem tokenStep_involutive :

    Function.Involutive tokenStep := by

  intro token

  rcases token with
    ⟨visible, escrow⟩

  change
    (
      MemoryEscrowRouted.visibleStep
        (
          MemoryEscrowRouted.visibleStep
            visible
        ),

      MemoryEscrowRouted.escrowStep
        (
          MemoryEscrowRouted.escrowStep
            escrow
        )
    ) =
    (visible, escrow)

  rw [
    MemoryEscrowRouted.visibleStep_involutive
      visible,

    MemoryEscrowRouted.escrowStep_involutive
      escrow
  ]


/--
Token evolution is bijective.
-/
theorem tokenStep_bijective :

    Function.Bijective tokenStep := by

  exact
    Function.Involutive.bijective
      tokenStep_involutive


/-
## Reversible token evolution
-/

/--
Token evolution packaged as a reversible transition.
-/
def reversibleToken :
    ReversibleStep Token :=

  ReversibleStep.ofInvolution
    tokenStep
    tokenStep_involutive


@[simp]
theorem reversibleToken_step
    (token : Token) :

    reversibleToken.step token =
      tokenStep token := by

  rfl


@[simp]
theorem reversibleToken_recover
    (token : Token) :

    reversibleToken.recover token =
      tokenStep token := by

  rfl


/--
A token step followed by token recovery returns the
original token.
-/
theorem token_recovery
    (token : Token) :

    reversibleToken.recover
        (
          reversibleToken.step token
        ) =
      token := by

  exact
    reversibleToken.recover_step token


/-
## Token histories
-/

/--
The token history generated from an encoded complete state.
-/
def tokenHistory
    (initial :
      MemoryEscrowRouted.CompleteState) :
    Nat → Token :=

  reversibleToken.history
    (encode initial)


/--
The token history begins at the encoded initial state.
-/
@[simp]
theorem tokenHistory_zero
    (initial :
      MemoryEscrowRouted.CompleteState) :

    tokenHistory initial 0 =
      encode initial := by

  rfl


/--
Token history advances by one lawful token step.
-/
theorem tokenHistory_succ
    (initial :
      MemoryEscrowRouted.CompleteState)
    (n : Nat) :

    tokenHistory
        initial
        (Nat.succ n) =

      tokenStep
        (
          tokenHistory
            initial
            n
        ) := by

  exact
    ReversibleStep.history_succ
      reversibleToken
      (encode initial)
      n


/--
Encoding the complete history at any stage gives the token
history at that stage.
-/
theorem encode_completeHistory
    (initial :
      MemoryEscrowRouted.CompleteState)
    (n : Nat) :

    encode
        (
          MemoryEscrowRouted.reversibleComplete.history
            initial
            n
        ) =

      tokenHistory
        initial
        n := by

  induction n with

  | zero =>
      rfl

   | succ n ih =>

      rw [
        ReversibleStep.history_succ,
        tokenHistory_succ,
        MemoryEscrowRouted.reversibleComplete_step,
        encode_completeStep,
        ih
      ]


/--
Decoding the token history at any stage reconstructs the
complete routed history at that stage.
-/
theorem decode_tokenHistory
    (initial :
      MemoryEscrowRouted.CompleteState)
    (n : Nat) :

    decode
        (
          tokenHistory
            initial
            n
        ) =

      MemoryEscrowRouted.reversibleComplete.history
        initial
        n := by

  have hencoded :=
    encode_completeHistory
      initial
      n

  have hdecoded :=
    congrArg decode hencoded

  simpa using hdecoded.symm


/--
Finite-depth recovery in token space returns any earlier
token in the history.
-/
theorem tokenHistory_recovers_after
    (initial :
      MemoryEscrowRouted.CompleteState)
    (n k : Nat) :

    ReversibleStep.recoverN
        reversibleToken
        k
        (
          tokenHistory
            initial
            (n + k)
        ) =

      tokenHistory
        initial
        n := by

  exact
    ReversibleStep.history_recovers_after
      reversibleToken
      (encode initial)
      n
      k


/--
Recovering from the kth token returns the encoded initial
state.
-/
theorem tokenHistory_recovers_initial
    (initial :
      MemoryEscrowRouted.CompleteState)
    (k : Nat) :

    ReversibleStep.recoverN
        reversibleToken
        k
        (
          tokenHistory
            initial
            k
        ) =

      encode initial := by

  exact
    ReversibleStep.history_recovers_initial
      reversibleToken
      (encode initial)
      k


/-
## Token components
-/

/--
The visible component of an encoded token is exactly the
local projection of the complete state.
-/
@[simp]
theorem encode_visible
    (complete :
      MemoryEscrowRouted.CompleteState) :

    (encode complete).1 =

      TkairosLocality.observeRoutedPair
        complete := by

  rfl


/--
The escrow component of an encoded token is exactly the
route-address record of the complete state.
-/
@[simp]
theorem encode_escrow
    (complete :
      MemoryEscrowRouted.CompleteState) :

    (encode complete).2 =

      MemoryEscrowRouted.escrow
        complete := by

  rfl


/--
A token is exactly the combination of its visible and
escrow components.
-/
theorem token_ext
    {token₁ token₂ : Token}
    (hvisible :
      token₁.1 = token₂.1)
    (hescrow :
      token₁.2 = token₂.2) :

    token₁ = token₂ := by

  exact
    Prod.ext
      hvisible
      hescrow


/--
Two complete states with equal encoded tokens are equal.

Neither visible information nor escrow information alone
is sufficient in general; their tokenized combination is.
-/
theorem complete_eq_of_token_eq
    {x y :
      MemoryEscrowRouted.CompleteState}
    (htoken :
      encode x = encode y) :

    x = y := by

  exact
    encode_injective htoken


end RoutedTokenization


#check RoutedTokenization.Token
#check RoutedTokenization.encode
#check RoutedTokenization.decode
#check RoutedTokenization.decode_encode
#check RoutedTokenization.encode_decode
#check RoutedTokenization.tokenEquiv
#check RoutedTokenization.encode_injective
#check RoutedTokenization.encode_surjective
#check RoutedTokenization.encode_bijective
#check RoutedTokenization.tokenStep
#check RoutedTokenization.encode_completeStep
#check RoutedTokenization.decode_tokenStep
#check RoutedTokenization.completeStep_conjugate
#check RoutedTokenization.tokenStep_involutive
#check RoutedTokenization.tokenStep_bijective
#check RoutedTokenization.reversibleToken
#check RoutedTokenization.token_recovery
#check RoutedTokenization.tokenHistory
#check RoutedTokenization.tokenHistory_succ
#check RoutedTokenization.encode_completeHistory
#check RoutedTokenization.decode_tokenHistory
#check RoutedTokenization.tokenHistory_recovers_after
#check RoutedTokenization.tokenHistory_recovers_initial
#check RoutedTokenization.encode_visible
#check RoutedTokenization.encode_escrow
#check RoutedTokenization.token_ext
#check RoutedTokenization.complete_eq_of_token_eq
