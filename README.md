# FDBLean — Formal Deductive Biology in Lean 4

FDBLean formalizes finite structural claims about nucleotide alphabets, codons,
directed RNA editing, genetic-code translation, and selected biochemical
classification laws. The goal is to make the exact boundary between a proven
mathematical consequence and an empirical biological assumption inspectable.

**Branch:** `forced-alphabet`
**Toolchain:** Lean 4.31.0 / Mathlib `v4.31.0`
**Source status (November 26, 2026):** 321 named theorem declarations across
23 theorem-bearing modules; full `lake build` succeeds on this branch. The
historical 293-theorem `main` snapshot is preserved in the claim-status index.

## Principal formal results

| Domain | What is established |
|---|---|
| Four-state nucleotide alphabet | For the declared four-base type, independently specified `R` and `S` profiles bijectively encode two Boolean coordinates; `M = R XOR S`. |
| Forced involutions | All fixed-point-free involutions of the four-element alphabet are exactly the three named involutions; they form the Klein four-group together with the identity. |
| Nucleotide torsor | The Klein action is free and transitive. |
| Codon geometry | The 64 codons carry pairwise transverse profile partitions; the homogeneous/generic split is exactly 22/42. |
| Directed recoding | Admissible editing yields `R' = R`, `M' = M OR E`, `S' = S XOR E`, with exact recovery of the edit mask. |
| RNA/DNA correspondence | A specified `U ↔ T` transport preserves the modeled involutions. |
| Genetic-code consequences | With the standard genetic code and charge conventions as explicit inputs, position-dependent `A → G` edits obey the formal charge-sign law. |
| Fano obstruction | Directed editing generates only the eight coordinate subspaces of `F₂³`, not the full seven-point/seven-line Fano incidence geometry. |
| Frame stabilizers | The formal matrix families have sizes `6 ⊆ 24 ⊆ 168`; the six edit-preserving transformations equal the selected-frame stabilizer fixing the `111` point. |

The principal results are gathered in
[`FDBLean/MainTheoremChain.lean`](FDBLean/MainTheoremChain.lean).
The detailed epistemic inventory is
[`docs/CLAIM_STATUS.md`](docs/CLAIM_STATUS.md).

## Scope and assumptions

These results **do not prove that chemistry uniquely had to produce the
four canonical RNA bases**. The alphabet, its biochemical names, the
independently specified profile tables and pairing operations are formalized
inputs. The forced-alphabet result classifies the fixed-point-free involutions
**conditional on that alphabet and those algebraic properties**.

Likewise, the standard genetic code and amino-acid charge assignments are
explicit empirical inputs, not consequences of the Klein group alone.
FDBLean does not establish universal biological optimality, protein-folding
predictions, or experimental therapeutic efficacy.

The Fano obstruction is a negative result: the modeled editing dynamics do
**not** generate the entire Fano plane or its 168 symmetries. The more recent
selected-frame theorem gives the precise finite-set stabilizer relationship.

## Reproduce the build

```bash
# From the root of the FDBLean repository
lake exe cache get
lake build

# Inspect the main theorem object
lake env lean FDBLean/MainTheoremChain.lean

# Inspect explicit axiom dependencies
lake env lean FDBLean/AxiomAudit.lean
```

The axiom audit prints the dependencies of selected public theorems, including
all ten forced-alphabet theorems and the eighteen new Fano/frame theorems.
Expected logical dependencies are at most `propext`, `Classical.choice`, and
`Quot.sound`. Any `sorryAx`, `Lean.ofReduceBool`, or native compiler-trust
axiom would require investigation. A successful build and a theorem's axiom
provenance are distinct checks.

## Directory guide

- `FDBLean/Base.lean`, `Involutions.lean`, `KleinAction.lean`, `Profiles.lean`:
  finite nucleotide geometry.
- `FDBLean/ForcedAlphabet.lean`: exhaustive four-base involution
  classification, a later extension to the foundation.
- `FDBLean/Codon.lean`, `ThreeNet.lean`, `HomogeneousSplit.lean`:
  codon profiles and the 22/42 decomposition.
- `FDBLean/Recoding.lean`, `EditingTrichotomy.lean`, `OriginNarrowing.lean`:
  directed recoding and exactly recoverable edit masks.
- `FDBLean/StandardCode.lean`, `Charge.lean`, `PositionalChargeLaw.lean`:
  genetic-code input and conditional charge consequences.
- `FDBLean/FanoObstruction.lean`: coordinate-reachability obstruction
  and selected-frame stabilizer chain.
- `FDBLean/MainTheoremChain.lean`: capstone theorem assembly.
- `FDBLean/AxiomAudit.lean`: independent named axiom inspections.
- `docs/CLAIM_STATUS.md`: theorem index, input classifications,
  limitations, and open questions.

## Research status

The formal development provides a finite deductive testbed for examining
which biological relationships are forced by selected algebraic premises.
Extensions to kinetic ribosomal decoding, context-dependent editing,
sequence-level provenance, and protein function remain open research
programs rather than proved consequences of the present model.
