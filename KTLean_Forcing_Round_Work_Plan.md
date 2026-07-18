# KTLean Work Plan: The Forcing Round
## Version 1.3 — July 18, 2026 — APPROVED FOR EXECUTION, INTERFACE-COMPLETE
### Revision: V1.0 (checker draft) → GPT review 1 (two structural repairs) → V1.1 → GPT review 2 (four binding changes) → V1.2 → GPT review 3 (sign-field restoration; destination-preserving evaluator) → V1.3 (both integrated; checker additionally corrected the proposed effectiveSign combinator, which under multiplicative semantics falsifies the two-block theorem — trial runs replacement semantics; see C0) → review 4 (GPT: unreachable O2 branch removed, outcome partition sharpened to masked-CD agreement vs measured-disagreement spectrum; named coefficient policies mandated). The circuit record stands: errors and catches both have named owners.
### Execution gate: begin with Phase 0 and A0–A1 ONLY. Further phases unlock on their exit criteria.

---

## The stake

If the 42 glyphs are not forced, and if we cannot explain exactly how they
are forced, we are building a sand castle. Every phase exits in a
kernel-checked result or a located failure naming which wall is sand.

## The level ladder (docstring-mandatory on major theorems)

    Level 1  Encoding         — represented in the formal language
    Level 2  Reconstruction   — proved equivalent to a known target
    Level 3  Forcing          — unique under a frozen, stated requirement set
    Level 4  Presentation-independent necessity — same object uniquely
             recovered from independently defined characterizations with
             commuting equivalences, or uniqueness across a declared
             maximal comparison class

Conditional classifications are legitimate and must be written as such,
e.g. "Level 3 given Fano" (see SEVEN-FORCING below).

## Named open obligations (ledger-tracked across rounds)

    SELECTOR-FORCING : derivation of route and the three conjugation bits
                       from Pascal structure. Does not exist. First
                       candidate attack: the three Pascal-recursion
                       neighbors of an entry carry three trits — the
                       right-shaped data for three bits (conjecture,
                       so-labeled).
    SEVEN-FORCING    : the canon asserts PG(2,2) is the minimal
                       nondegenerate realization of triadic closure; the
                       corpus proves properties of Fano, not its
                       inevitability. Until this is a theorem, every
                       42-result is classified "forced given Fano." This
                       obligation is the difference between the glyphs
                       being forced by the whole KT chain and forced once
                       Fano is assumed. It is not this round's work, but
                       this round's results are labeled relative to it.

---

## Phase 0: Housekeeping (blocking; one session)

0.1  `GlyphBasin` → `GlyphFamily`; empty `AttractorBasin` type; recompile.
0.2  Hygiene audit, verbatim to checker: sorry/axiom grep (expected
     empty); `#print axioms` on `pascalRoutedMul_eq_cdMul`, deepest
     escrow theorem, `routedExchange_satisfies_yang_baxter`.
0.3  Level-ladder docstrings on `BraidedQuaternion.lean`,
     `CayleyDicksonQuaternion.lean`.

**Exit: recompile PASS; audit outputs delivered.**

---

## Phase A: Generic doubling over the iterable interface

A0.  Define the weakest iterable interface: additive commutative group;
     distributive, non-associative-assumed multiplication; unit;
     involution with `star_involutive`, `star_add`, `star_one`,
     `star (x*y) = star y * star x`. Builder duty: verify mathlib's
     star hierarchy against nonassociativity before adopting any class;
     mismatches resolved by bespoke minimal class, never by strengthening
     assumptions.
A1.  Generic doubling: `A × A`, `star (a,b) = (star a, −b)`,
     `(a,b)(c,d) = (a·c − star d·b, d·a + b·star c)`. Prove the A0
     interface is CLOSED under doubling. This closure theorem licenses
     iteration; it is the round's foundation stone.
A2.  Quaternion instantiation; regression vs `cdMul` (`rfl`-grade;
     representations intentionally aligned here and only here).
A3.  `Double (Double ℍ[R])`: sedenion-level object by instantiation.
A4.  Boundary witness profile over ℚ: quaternion associativity (mathlib);
     octonion nonzero-associator witness (alternativity spot-checks
     optional, full generic alternativity out of scope, docstring says
     so); sedenion zero-divisor witness. Kernel-visible Hurwitz-boundary
     profile without the classification theorem.

**Exit: A1 closure PASS/FAIL; A2 PASS/FAIL; A3 compiles; A4 witnesses.
GATE: A0–A1 outcome reported to checker before A2 proceeds.**

---

## Phase B: The diagonal address law

B0.  Define over natural coordinates, NOT Fin arithmetic:
     `def pascalAddressLaw {n : ℕ} (i j : Fin n) : ℕ × ℕ :=
        (i.val + j.val, i.val)`.
     (Fin addition is modular; `(3,2)` must reach row 5, not row 1. The
     silent-wraparound trap is hereby named so it cannot be stepped in.)
B1.  Prove `cdPascalAddress = pascalAddressLaw` (via the coercion) by
     `decide`. Level 2, annotated: canonical uniformization of witness
     data. Compression, not forcing. Update `BraidedQuaternion.lean`
     docstring.
B2.  Characterize (parametrically; the codomain is infinite, this is not
     a finite enumeration) the assignments satisfying the V1.0 draft
     R1–R4, without consulting control outputs — expected verdict: large
     slack, confirming the draft requirements were too weak. Purpose:
     validate that frozen conditions mean what they claim before any
     freeze.
B3.  Freeze the universal-property requirements (replaces V1.1's
     description-length language, which was a disguised free choice):
     row functional r : ℕ² → ℕ additive with r(1,0) = r(0,1) = 1
     (additive grading; equal unit cost of left and right inputs);
     column functional c : ℕ² → ℕ additive with c(1,0) = 1, c(0,1) = 0
     (left registration; the torsor base-point convention already used
     in the frame modules). Architect ratifies this exact set before B4.
B4.  Prove: since ℕ² is the free commutative monoid on two generators,
     the frozen requirements force r(i,j) = i+j and c(i,j) = i uniquely.
     A genuine Level 3 theorem by universal property, no minimality
     axiom. Statement: `diagonal_pascal_address_unique`.
B4a. Convention-inertness theorem: the mirror registration
     (c(1,0), c(0,1)) = (0,1) yields the transpose law (i+j, j), and
     C(i+j, i) = C(i+j, j), so the control table is IDENTICAL. The one
     residual convention in the law is provably control-inert. Two
     lines; closes the last "tuned convention" door.
B5.  Conjecture module (statement only): control as braid-crossing count
     — balanced C(i+j,i) mod 3 as crossing number of block histories;
     four-block test named; links to `YangBaxterRouting` and to
     SELECTOR-FORCING.

**Exit: B1 PASS; B2 characterization delivered; B3 ratified; B4 proved
or slack exhibited; B4a proved.**

---

## Phase C: The routing compiler and pre-registration PD-DIAGONAL-01

C0.  The compiler, stated honestly. Pascal currently determines control
     ONLY. Route and selector have no Pascal derivation
     (SELECTOR-FORCING is open). The datum carries FOUR logically
     separate fields — support/polarity (control), algebraic sign,
     selector, route — and the terminology repair applies at the type
     level:
       `structure RoutingDatum (I) where
          route    : I → I → I
          sign     : I → I → Sign          -- inherited CD orientation
          selector : I → I → ConjBits
          control  : I → I → PascalMod3.Control`
     with `pascalControl` derived from the diagonal law (B0), and
     `inheritedRoute`, `inheritedSign`, `inheritedSelector` extracted by
     the Phase D flattening compiler, never hand-entered.

     TRIAL SEMANTICS, binding: the routed product for the trial uses
     REPLACEMENT semantics — where control is active, its polarity IS
     the coefficient; inactive suppresses; the inherited `sign` field is
     carried as data but does not multiply into the product. Rationale:
     this is the semantics under which the two-block theorem
     `pascalRoutedMul_eq_cdMul` holds (Pascal control REPLACED
     `cdOrientation` there). The alternative multiplicative combinator
       `effectiveSign i j = control-polarity × sign`
     is retained in the file as a definition for possible future use,
     with a warning docstring: under multiplicative semantics the
     two-block case yields all-positive coefficients and the CD
     reconstruction is FALSE — it is not the trial semantics and must
     not become it by drift.

     The inherited `sign` field's role in the trial is as COMPARISON
     TARGET: Phase E measures, channel by channel, agreement between
     Pascal polarity and the flattened sedenion sign. That agreement
     map, together with the suppression pattern, is the measurement.

     Implementation requirement (review 4): no generic multiplication
     that silently carries but ignores a coefficient field. Either
     split the datum types (`AlgebraicRoutingDatum` extended by
     `ControlledRoutingDatum`) or give the two coefficient policies
     unmistakable names — `routedMulByInheritedSign` and
     `routedMulByPascalControl` — so the trial proposition is
     transparent in the code itself: same route, same selector,
     evaluated once under each policy, compared.
C1.  Committed objects, four forms frozen together: mathematical
     statement; the explicit 4×4 table below; a Lean generator
     `diagonalPredictionTable` computing the table from B0's law; git
     commit hash. Then prove `registeredTable = diagonalPredictionTable`
     by `decide` before any comparison (a transcription slip must never
     masquerade as mathematical failure).

     The registered control table, C(i+j, i) mod 3, balanced, rows
     i = 0..3, columns j = 0..3, labels in CONTROL vocabulary
     (positive-control / negative-control / suppressed — not
     orientations):

         residues:                controls:
         1 1 1 1                  P  P  P  P
         1 2 0 1                  P  N  S  P
         1 0 0 1                  P  S  S  P
         1 1 1 2                  P  P  P  N

     Predicted suppressions: exactly THREE — (1,2), (2,1), (2,2).
     Predicted negative-controls: (1,1) and (3,3).
     Predicted positive-controls: the remaining eleven.
     The table predicts CONTROL only; the inherited CD sign is not
     predicted by it and is measured against it in E2.
C2.  Terminology, binding: balanced mod-3 value is a CONTROL; zero is
     suppression, not an orientation. Support and orientation are
     distinct notions in every definition and statement.
C3.  Contaminated ground: two-block CD agreement is known; not a hit.
C4.  Admissible outcomes (partition corrected in review 4: the former
     "reproduces standard sedenion CD" branch is unreachable — the
     registered table suppresses three channels that standard iterated
     CD does not, and the C1 generator-equality theorem closes the
     transcription-error channel that branch existed to cover):
     (O1) The masked product is degenerate or structurally incoherent —
          the law refuted as structure above two blocks.
     (O2) Masked-CD agreement: on ALL 13 supported channels, Pascal
          polarity equals the flattened inherited CD sign; the hybrid
          algebra is exactly the Pascal-masked sedenion routing
          skeleton. Target theorem shape:
          `hybrid_basis_mul_eq_masked_cd_basis_mul` — hybrid basis
          product equals (match control: inactive → 0, else CD basis
          product).
     (O3) Coherent sparse algebra with k < 13 agreeing channels: the
          agreement count k is the measured statistic, reported with
          the disagreeing channel list; a genuinely different routed
          product, characterized per E3.
     The E2 agreement map is the discriminator across all three; its
     two-block restriction must show 4/4 agreement (positive control).
C5.  Anticipated-relationship clause (softened language per review): the
     sparse algebra may be a closed subobject, homomorphic image, or
     congruence quotient of the routed sedenion carrier — "quotient"
     claimable only after a product-compatible congruence is exhibited.
     Logged before computation.

**Exit: instrument filed, hashed; generator-equality theorem proved.**

---

## Phase D: Four-register algebra, flattening compiler, sedenion Level 2

D1.  Carrier: `Fin 4 → ℍ[R]`, nothing else. No glyph/basin/walk names in
     the formal definition; interpretation must be earned later by a
     decomposition theorem. General routing datum: the four-field
     `RoutingDatum` of C0 — route, sign, three conjugation bits per
     pair, control in `PascalMod3.Control`.
D2.  The flattening compiler, split out as the major construction it is
     (the architectural thesis — iterated CD is compilable to routing
     instructions — is proved or refuted here):
     D2a. `fourRegisterEquiv : (Fin 4 → ℍ[R]) ≃ₗ[R] Double (Double ℍ[R])`.
     D2b. Recursive extraction of flat route, sign, and selector bits
          from the generic doubling — target shape
          `flattenCDDatum : RoutingDatum I → RoutingDatum (Fin 2 × I)`
          or equivalent; this is also what C0's `inheritedRoute` and
          `inheritedSelector` consume, so D2b precedes the C1 freeze.
     D2c. Multiplication-preservation proved on basis blocks first.
     D2d. Extension to arbitrary elements by bilinearity:
          `fourRegisterEquiv (routedMul₄ cdDatum x y) =
             sedenionMul (fourRegisterEquiv x) (fourRegisterEquiv y)`.
     Level 2 at sixteen dimensions, docstringed as such.
D3.  Witnesses at the routed representation as needed (A4 transports).

**Exit: D2a–D2d PASS/FAIL individually; D2b unlocks C1.**

---

## Phase E: The trial (after C filed and D passed)

E1.  Instantiate `hybridDatum` at four blocks.
E2.  Compute support and CONTROL POLARITY against the registered table;
     separately compute the channel-by-channel agreement map between
     Pascal polarity and the flattened inherited CD sign (the table does
     not predict the latter; the agreement map is a measured output, and
     its two-block restriction must reproduce perfect agreement as a
     regression check). Classify per C4.
E3.  If O3, characterize in order: closure of the supported subset under
     the product; relation to the octonion subalgebra; C5-clause
     relation to the sedenions (with the congruence-compatibility
     requirement before the word "quotient" is used); norm behavior on
     the supported subset; Yang–Baxter and cocycle checks for the hybrid
     datum; count of admissible operations under corpus admissibility.
E4.  Ledger the outcome in pre-committed vocabulary. Scope reminder in
     the ledger entry: this trial adjudicates the control layer;
     SELECTOR-FORCING remains open regardless of outcome.

**Exit: O1, O2, or O3 with characterization.**

---

## Phase F: The glyph forcing question (de-circularized, provenance-audited)

F00. Provenance audit BEFORE F0 is written, ledgered as a table. Every
     predicate entering `Admissible` is listed with its permitted source
     and its forbidden dependencies:

     | Component     | Permitted source        | Forbidden dependency        |
     |---------------|-------------------------|-----------------------------|
     | Support       | Pascal mod 3            | Glyph/Fano cardinalities    |
     | Route         | diagonal law / D2b      | hand-entered Fano table     |
     | Selector      | conjugation closure     | CD target table post-freeze |
     | Coherence     | Yang–Baxter             | glyph enumeration           |
     | Reversibility | product behavior        | any type of cardinality 42  |

     Additionally: any appearance of the numbers 7, the stride set
     {1,2,4}, AGL(1,F₇), or any cardinality-42 type in the dependency
     graph of `Admissible` is a provenance violation and blocks F1.
F0.  `def RoutedOperationCode (n : ℕ)` — a genuinely finite SYNTACTIC
     code type (left, right, destination : Fin n; three conjugation
     bits; sign; control), with a DESTINATION-PRESERVING evaluator
     `RoutedOperationCode.evalBasis : Code → ℍ[R] → ℍ[R] →
     (Fin n → ℍ[R])`, the result supported only at `code.destination`
     — an evaluator returning a bare quaternion would erase routing and
     make codes with distinct destinations semantically
     indistinguishable before the quotient is even declared.
     `Admissible` is defined on codes from F00-cleared predicates only,
     frozen before F1. The count lives on the code space; semantic
     equivalence (which must respect BOTH the quaternionic rule AND the
     destination) is imposed separately and explicitly, so
     syntactically distinct codes computing the same routed operation
     are neither silently merged nor silently double-counted — the
     quotient, if taken, is a declared step.
F1.  `Fintype.card {c : RoutedOperationCode n // Admissible c} = ?` —
     computed, whatever it is, at n = 2 and n = 4. If 42 does not
     appear, locate what does, and where in the register hierarchy 42
     first could appear. Honest structural note, on record now: with no
     independently derived seven-class incidence structure in the
     routed universe, there is no reason to expect the factor 7 at
     small n — that expectation gap is exactly what SEVEN-FORCING
     names, and finding the true small-n counts is the measurement of
     it.
F2.  Structural analysis of the admissible code space: actions, orbits,
     factorizations.
F3.  If counts permit: `AdmissibleOperation ≃ Glyph` as a
     STRUCTURE-PRESERVING (equivariant) equivalence, never a mere
     bijection of equinumerous sets.
F4.  Canonicity: uniqueness/naturality of F3. F3+F4 constitute the
     forcing claim; F1 alone is a count. Classification of any success:
     "Level 3/4 given Fano" until SEVEN-FORCING closes.
F5.  Forbidden move: no adjustment of `Admissible` after F1 computes.
     Amendments are new registrations; amended success is downgraded
     evidence, permanently.

**Exit this round: F00 table ledgered; F0 frozen; F1 computed at n = 2.
F2–F4 reach goals.**

---

## Sequencing

0 blocks all. A0–A1 first, outcome to checker before A2 (execution
gate). B interleaves with A after B0. B2 strictly before B3 (validation
before freeze — mandatory). D2b before C1's freeze (the compiler feeds
the instrument). C complete before E. F00/F0 may be drafted from the
start; F1 after F0 freeze.

## Standing rules

Freeze before compute; amendments are new registrations. No ℝ in the
substrate track. `#print axioms` verbatim on terminal theorems. No
scaffolding axioms; assumptions are named hypotheses carried explicitly.
Level-ladder docstrings, conditional labels permitted and mandatory
where applicable. Support ≠ orientation everywhere. Natural coordinates
for Pascal addresses; Fin arithmetic forbidden in addressing. Checkpoint
states: PROVED / FAILED-AT(x) / NOT-YET-ATTEMPTED. A located failure is
a deliverable.

## What this round settles

B4 landing gives the first unconditional Level 3 object (the address
law, by universal property). E adjudicates the control layer beyond the
Hurwitz boundary under pre-registration. F1 measures where the glyph
count actually lives in the routed hierarchy, which is the sand-castle
core sample. And the round's honest residue is named in advance:
SELECTOR-FORCING and SEVEN-FORCING, the two conditionals standing
between "forced given Fano" and "forced." Knowing precisely which
conditionals remain is the difference between a sand castle and a
building with a posted engineering report.
