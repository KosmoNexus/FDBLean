import FDBLean.MainTheoremChain

/-!
# FDBLean.AxiomAudit — forced-alphabet branch

This file audits the capstone and selected public theorems, especially
all ten new theorems in `ForcedAlphabet.lean` and the eighteen additions
to `FanoObstruction.lean` on branch `forced-alphabet`.

Read each `#print axioms` result. The acceptable dependencies are the
standard Lean logical axioms `propext`, `Classical.choice`, `Quot.sound`
(or fewer). No result should contain `sorryAx`, `Lean.ofReduceBool`,
`Lean.trustCompiler`, or native-decision trust dependencies.

This is an explicitly named theorem audit, not a claim that a successful
`lake build` alone establishes the axiom provenance of every declaration.

The chemical profile tables, the choice of four RNA bases, the named
biochemical pairings, and the empirical standard genetic code remain
inputs to the model, not consequences of finite group theory.
-/

namespace FDBLean

-- Foundation: four-base algebra and action.
#print axioms Base.card_base
#print axioms Klein.card
#print axioms Klein.mul_assoc
#print axioms Klein.mul_comm
#print axioms kleinAct_identity
#print axioms kleinAct_mul
#print axioms kleinAct_free
#print axioms kleinAct_transitive
#print axioms nucleotide_alphabet_is_klein_torsor
#print axioms biochemical_composition_from_action

-- Forced alphabet: all ten new theorem declarations.
#print axioms rs_profile_surjective
#print axioms rs_profile_bijective
#print axioms chemical_profile_rank_two
#print axioms tauC_preserves_exactly_S
#print axioms tauT_preserves_exactly_R
#print axioms tauW_preserves_exactly_M
#print axioms named_relations_are_fixed_point_free_involutions
#print axioms fixed_point_free_involution_classification
#print axioms no_fourth_fixed_point_free_involution
#print axioms canonical_alphabet_forces_klein_structure

-- Some main pre-existing biological theorem interfaces.
#print axioms profile_xor_law
#print axioms card_codon
#print axioms homogeneousUnion_card
#print axioms genericCodons_card
#print axioms recodeBase_tauC_eq_tauW_recodeBase
#print axioms standardCode_exhaustive
#print axioms positional_charge_law

-- Fano geometry and the previously established obstruction.
#print axioms FanoObstruction.points_card
#print axioms FanoObstruction.lines_card
#print axioms FanoObstruction.reached_card
#print axioms FanoObstruction.reachedPoints_card
#print axioms FanoObstruction.reachedLines_card
#print axioms FanoObstruction.lines_missed
#print axioms FanoObstruction.glMatrices_card
#print axioms FanoObstruction.preservingGL_card
#print axioms FanoObstruction.fano_obstruction_summary

-- New Fano diagonal: four added theorems.
#print axioms FanoObstruction.diagonal_points_sum_zero
#print axioms FanoObstruction.frameDiagonal_isSubspace
#print axioms FanoObstruction.frameDiagonal_card
#print axioms FanoObstruction.frameDiagonal_isLine

-- New Fano reachability counterexample: four added theorems.
#print axioms FanoObstruction.frameDiagonal_not_coordinate
#print axioms FanoObstruction.frameDiagonal_not_reached
#print axioms FanoObstruction.frameDiagonal_not_reachedLine
#print axioms FanoObstruction.frameDiagonal_mem_missedLines

-- New selected-frame characterization: ten added theorems.
#print axioms FanoObstruction.selectedFrame_card
#print axioms FanoObstruction.framePoint_eq_sum_basis
#print axioms FanoObstruction.frameStabilizer_card
#print axioms FanoObstruction.frameStabilizer_subset_glMatrices
#print axioms FanoObstruction.framePointStabilizer_card
#print axioms FanoObstruction.preservingGL_subset_framePointStabilizer
#print axioms FanoObstruction.framePointStabilizer_subset_preservingGL
#print axioms FanoObstruction.preservingGL_eq_framePointStabilizer
#print axioms FanoObstruction.frame_stabilizer_chain
#print axioms FanoObstruction.frame_stabilizer_cardinality_indices

-- Capstone: one typed theorem collecting the model's central results.
#print axioms mainTheoremChain

end FDBLean
