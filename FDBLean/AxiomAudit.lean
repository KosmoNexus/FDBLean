import FDBLean.Base
import FDBLean.Involutions
import FDBLean.KleinAction

/-!
# FDBLean.AxiomAudit

Kernel-cleanliness audit for the whole development.

## What this file is for

Every exported theorem in FDBLean must depend on at most

  `[propext, Classical.choice, Quot.sound]`

and nothing else. Those three are the standard axioms of Lean's classical
foundation and are checked by the kernel. Many results here depend on none
of them, closing by reduction alone; that is stronger still.

Any of the following appearing in an axiom list is a defect, not a style
preference:

* `Lean.ofReduceBool`
* `Lean.trustCompiler`
* any axiom whose name contains `._native.`

These are the signature of `native_decide`, which compiles the decision
procedure to native code and accepts the result on the word of the compiler
rather than by kernel reduction. It places the Lean compiler, its runtime,
and the C toolchain inside the trusted base.

## Why this matters more here than in an ordinary Lean project

The manuscript claims that a machine-verified proof is an *independent*
witness, one that fails differently from a hand-checked proof. A theorem
carrying `ofReduceBool` fails the way a compiler bug fails, which is not
independent of anything, and it is the first thing a referee who knows Lean
will check on the headline result.

Nothing in this development needs `native_decide`. The largest object is a
64-element codon space; the kernel reduces everything at that scale without
complaint. If a proof appears to require it, the proof is wrong, not the
budget. Raise `maxHeartbeats` or restructure the argument.

## A note on syntax

`#print axioms` is a command, not a declaration, so it cannot carry a
`/-- ... -/` doc-comment. Use plain `--` comments between entries.

## How to use

Build this module and read the output. No line may show a `._native.` entry.
Add one `#print axioms` line per exported theorem as each new module lands,
before the theorem is cited in the manuscript.
-/

namespace FDBLean

-- ---------------------------------------------------------------------------
-- Group structure
-- ---------------------------------------------------------------------------

#print axioms Klein.card
#print axioms Klein.e_mul
#print axioms Klein.mul_e
#print axioms Klein.mul_assoc
#print axioms Klein.mul_comm
#print axioms Klein.self_inverse
#print axioms Klein.mul_left_cancel
#print axioms Klein.c_ne_t
#print axioms Klein.c_ne_w
#print axioms Klein.t_ne_w
#print axioms Klein.c_mul_t

-- ---------------------------------------------------------------------------
-- The action on the nucleotide alphabet
-- ---------------------------------------------------------------------------

#print axioms kleinAct_identity
#print axioms kleinAct_mul
#print axioms kleinAct_c
#print axioms kleinAct_t
#print axioms kleinAct_w
#print axioms kleinAct_free
#print axioms kleinAct_exists
#print axioms kleinAct_transporter_unique
#print axioms kleinAct_unique
#print axioms kleinAct_transitive

-- ---------------------------------------------------------------------------
-- Manuscript claims
-- ---------------------------------------------------------------------------

-- Theorem 1. The headline result, and the one a reviewer is most likely to
-- audit directly.
#print axioms nucleotide_alphabet_is_klein_torsor

-- The composition law tau_c . tau_t = tau_w, recovered from the action.
#print axioms biochemical_composition_from_action

-- ---------------------------------------------------------------------------
-- TODO as modules land, one line each
-- ---------------------------------------------------------------------------
--   Profiles.lean            profile_xor_law, tauT_preserves_R,
--                            tauC_preserves_S, tauW_preserves_M
--   Codon.lean               codon_card
--   ThreeNet.lean            fiber_card, pairwise_transverse
--   HomogeneousSplit.lean    homogeneous_card_22, generic_card_42
--   Recoding.lean            R_invariant, M_monotone
--   EditingTrichotomy.lean   S_difference_eq_edit_indicator, absorbing_set
--   OriginNarrowing.lean     origin_narrowing
--   ComplementToWobble.lean  complement_to_wobble
--   RNADNATransport.lean     transport_iso, decomposition_preserved
--   PairClassification.lean  pair_partition, ring_class_split
--   ErrorControl.lean        code_injective, min_distance_two
--   PositionalChargeLaw.lean charge_law_pos1, charge_law_pos2,
--                            charge_law_pos3, charge_edges_exhaustive

end FDBLean
