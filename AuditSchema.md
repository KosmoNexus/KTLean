# KTLean Verification and Provenance Audit Schema

## Purpose

KTLean is a formally verified reconstruction program in theoretical physics.

Lean verifies that theorem statements follow from encoded definitions, assumptions, and imported results. Lean does not determine whether those definitions faithfully represent the intended mathematics or whether the resulting formal system corresponds to physical reality.

This audit layer therefore records:

1. the provenance of each load-bearing definition;
2. the logical dependencies of each terminal theorem;
3. the distinction between formal consequence and physical interpretation;
4. any divergence between source statements and Lean encodings;
5. the conditions under which a result would fail or require revision.

The governing direction of fit is:

> The program bends to reality. Reality does not bend to preserve the program.

---

# 1. Definition Audit Record

Each substantive definition should receive one record.

## Required fields

### Lean name

Fully qualified declaration name.

Example:

```text
KTMonad.Monad
