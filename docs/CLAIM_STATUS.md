# FDBLean Claim Status

## Purpose

This document records the epistemic status of the principal claims in
FDBLean. It distinguishes:

- machine-checked theorems;
- explicit definitions and conventions;
- empirical biological inputs;
- formal consequences conditional on those inputs;
- open mathematical and biological questions.

## Machine-checked formal results

### Nucleotide geometry

- The RNA nucleotide alphabet has four elements.
- The three involutions form a Klein four-group action.
- The action is free and transitive.
- The nucleotide alphabet is a Klein torsor.
- The three relative profiles satisfy the XOR law.
- Any two profiles determine the nucleotide.

### Codon geometry

- RNA codon space has 64 elements.
- Codon profile space has 8 elements.
- The three profile partitions are pairwise transverse.
- The resulting structure is a 3-net of order 8.
- The homogeneous union has 22 codons.
- The generic complement has 42 codons.
- The pairwise homogeneous intersections are the origin codon.

### Recoding dynamics

- Directed recoding is:
  - A → G
  - C → U
  - G → G
  - U → U
- Recoding is idempotent.
- Under admissible editing:
  - R is invariant.
  - M changes monotonically according to `M' = M OR E`.
  - S changes according to `S' = S XOR E`.
- The edit mask is recovered exactly from the pre/post S-profile difference.
- The absorbing alphabet is exactly `{G,U}`.
- The absorbing codons are exactly `{G,U}^3`.
- The zero-M origin narrows exactly to `G` or `U`.
- Watson-Crick complementation transports to wobble pairing after recoding.

### RNA/DNA transport

- The map `U ↔ T` defines a bijection between RNA and DNA alphabets.
- The transport preserves all three involutions.
- RNA and DNA codon spaces are equivalent.
- The tagged RNA/DNA nucleotide space has 8 states.
- The tagged construction is only a direct product with polymer identity.
- No relation to 84 or 168 is claimed.

### Pair classification and error geometry

- The six unordered distinct DNA-base pairs partition into:
  - two complement pairs;
  - two wobble-class pairs;
  - two transition pairs.
- Complement and wobble classes reverse ring class.
- Transition class preserves ring class.
- Every mismatch lies in exactly one ring-behavior stratum.

### Genetic code and charge

- The standard RNA genetic code is encoded explicitly.
- There are 61 amino-acid codons and 3 stop codons.
- The amino-acid charge convention is encoded exactly.
- Under A→G editing:
  - position 1 gives `Δq ≤ 0`;
  - position 2 gives `Δq ≥ 0`;
  - position 3 gives `Δq = 0`.

## Declared inputs and conventions

The following are not derived from the Klein geometry:

- the biological interpretation of the three involutions;
- the standard genetic code;
- the amino-acid charge convention;
- histidine charge `+1/2`;
- the biological admissibility of selected editing sites;
- polymerase rejection, repair, or tolerance behavior.

Lean verifies consequences of these declarations once encoded.

## Empirical hypotheses represented but not proved

- specific polymerase mismatch behavior;
- mismatch-repair preferences;
- biochemical tolerance of transition-class mismatches;
- organism-specific editing frequencies;
- selective enrichment of particular codon classes;
- functional or therapeutic utility of derived candidates.

## Open formal questions

- generalization beyond the four-base nucleotide alphabet;
- generalization to nonstandard genetic codes;
- formal treatment of context-dependent editing efficiency;
- integration with protein structure and function;
- formalization of multi-codon and transcript-level constraints;
- stronger abstraction of admissible transport and provenance;
- extension from finite enumeration to scalable biological search.

## Trust and proof status

- No theorem in the main development uses `sorry`.
- No theorem uses `native_decide`.
- Ordinary `decide` is used only for kernel-reducible finite propositions.
- The main theorem chain is assembled in `FDBLean/MainTheoremChain.lean`.
- `#print axioms` results are recorded in `FDBLean/AxiomAudit.lean`.

## What FDBLean does not establish

FDBLean does not by itself establish:

- that the formal structures are uniquely biologically privileged;
- that the framework generalizes to all of biology;
- that the empirical hypotheses are true;
- that the framework improves drug discovery;
- that the framework predicts new therapeutic compounds;
- that the formal model is sufficient for autonomous biological science.

Those are separate scientific questions.