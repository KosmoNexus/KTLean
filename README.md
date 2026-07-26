# KTLean

**KTLean** is a Lean 4 formalization of **Kosmoplex Theory**.

At the current Draft 1 checkpoint, the repository contains:

- **1,992 theorem and lemma declarations**
- **No `sorry`**
- **No `sorryAx`**
- A successful full `lake build`
- A successful clean-clone build on an independent physical drive
- An explicit axiom audit of the principal capstone theorems

Project website: **https://thektproject.org**

## What KTLean formalizes

The current verified structural spine proceeds through:

```text
triadic closure
    →
canonical 42-glyph spectrum
    →
spinorial double-cover boundary
    →
visible projection with recoverable escrow
    →
four directed views per glyph
    →
168 monads
    →
exact structural inverse-alpha invariant 137
```

A conditional physical layer then develops:

```text
action, causal, and gravity tokens
    →
Planck mass, length, and time
    →
four candidate dimensionless projection-state grammars
    →
explicit canonical-state selection obligation
    →
exact interval-certification architecture for projected alpha
```

The principal navigational capstone is:

```lean
MainTheoremChain.ktlean_structural_spine
```

## Clone and build

Requirements:

- Git
- Lean 4 through `elan`
- Lake

Clone the repository:

```bash
git clone https://github.com/KosmoNexus/KTLean.git
cd KTLean
lake build
```

The first build may take time because Lake downloads Mathlib and its pinned dependencies.

A successful build ends with output similar to:

```text
Build completed successfully
```

## Repository integrity checks

Check for unfinished proofs:

```bash
grep -RniE '\bsorry\b|sorryAx' KTLean --include='*.lean'
```

A clean repository should return no output.

Count theorem and lemma declarations:

```bash
grep -RhoE '^[[:space:]]*(theorem|lemma)[[:space:]]+[A-Za-z0-9_′]+' KTLean \
  --include='*.lean' | wc -l
```

At the current Draft 1 checkpoint, the count is:

```text
1992
```

Check repository state:

```bash
git status
```

## Where to begin

New readers should start with:

1. `KTLean/MainTheoremChain.lean`
2. `KTLean/AxiomAudit.lean`
3. `KTLean/GlyphSpectralCompleteEmergence.lean`
4. `KTLean/OMBTLocalityGeneration.lean`
5. `KTLean/OMBTMonadEmergence.lean`
6. `KTLean/PhysicalAlphaInvariant.lean`
7. `KTLean/PhysicalPlanckScale.lean`
8. `KTLean/PhysicalCanonicalStateCount.lean`
9. `KTLean/PhysicalAlphaCertifiedValue.lean`

## Claim status

The repository distinguishes carefully among:

- proved structural results
- explicit hypotheses
- finite computational certificates
- conditional physical constructions
- open formal obligations

The current corpus does **not** claim that every physical consequence of Kosmoplex Theory has already been derived.

In particular, the following remain open or conditional:

- a unique physical criterion selecting the canonical projection-state count
- exact certification of the claimed projected decimal value of alpha
- a full Bell/Tsirelson reconstruction in the KT setting
- a full Hurwitz classification at the octonionic boundary
- derivation of the full Standard Model parameter set

These boundaries are stated explicitly rather than hidden in implementation details.

## Axiom audit

The audited capstones contain:

- no `sorryAx`
- no undeclared KT-specific axiom
- standard Lean logical dependencies such as:
  - `propext`
  - `Classical.choice`
  - `Quot.sound`
- visible `native_decide` certificates for selected finite computations

See:

```text
KTLean/AxiomAudit.lean
```

## Project guide

A public PDF introducing the project, module architecture, glossary, theorem tour, open problems, and dependency structure is available at:

**https://thektproject.org**

## Constructive criticism and collaboration

Independent verification, constructive criticism, alternate formalizations, and serious collaboration are welcome.

The aim of KTLean is not to insulate Kosmoplex Theory from criticism. It is to make the theory precise enough that its claims can be inspected, reproduced, challenged, and extended in a common formal language.

## Repository

**https://github.com/KosmoNexus/KTLean**
