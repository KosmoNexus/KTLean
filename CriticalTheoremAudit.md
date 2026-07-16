# KTLean Critical Theorem Audit

## Purpose

This document audits the most load-bearing theorems in KTLean.

For each theorem, the audit records:

- what the theorem formally proves;
- why it matters;
- whether the statement was fixed before proof;
- whether definitions changed during proof;
- what stronger claim is not established;
- what failure would have meant for the project;
- current axiom dependencies;
- frame and tokenization status;
- known open obligations.

The governing principle is:

> The theorem count measures formal output.  
> The audit measures epistemic weight.

---

# 1. `KTGlyph.card_glyph`

## Module

`KTLean/Glyph.lean`

## Formal statement

```lean
theorem card_glyph :
  Fintype.card Glyph = 42