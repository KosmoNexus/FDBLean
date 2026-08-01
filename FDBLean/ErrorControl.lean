import FDBLean.PairClassification

/-!
# FDBLean.ErrorControl

A formal separation between nucleotide-pair geometry and empirical
error-control behavior.

The Klein geometry proves that every distinct DNA-base pairing belongs
to exactly one of three classes:

* Watson--Crick complement;
* wobble analogue;
* transition.

It also proves a ring-class dichotomy:

* complement and wobble pairings reverse purine/pyrimidine class;
* transition pairings preserve purine/pyrimidine class.

Polymerase rejection, mismatch repair, biochemical tolerance, and
fitness are empirical properties. They are therefore represented here
as predicates or explicit hypotheses rather than derived from the
finite geometry alone.
-/

namespace FDBLean

open DNABase

/-!
## Formal pair geometry
-/

/--
A DNA-base pair is a mismatch when its two bases are distinct.
-/
def IsMismatch
    (a b : DNABase) :
    Prop :=
  a ≠ b

instance isMismatchDecidable
    (a b : DNABase) :
    Decidable (IsMismatch a b) := by
  unfold IsMismatch
  infer_instance

/--
A mismatch preserves ring class when the two bases have the same
purine/pyrimidine profile.
-/
def RingPreservingMismatch
    (a b : DNABase) :
    Prop :=
  IsMismatch a b ∧
    dnaRBit a = dnaRBit b

instance ringPreservingMismatchDecidable
    (a b : DNABase) :
    Decidable (RingPreservingMismatch a b) := by
  unfold RingPreservingMismatch
  infer_instance

/--
A mismatch reverses ring class when the two bases have opposite
purine/pyrimidine profiles.
-/
def RingReversingMismatch
    (a b : DNABase) :
    Prop :=
  IsMismatch a b ∧
    dnaRBit b = !(dnaRBit a)
instance ringReversingMismatchDecidable
    (a b : DNABase) :
    Decidable (RingReversingMismatch a b) := by
  unfold RingReversingMismatch
  infer_instance
/--
Transition-class pairings are mismatches.
-/
theorem transition_pair_is_mismatch
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.transition) :
    IsMismatch a b := by
  intro hab
  subst b
  have hnone :
      classifyPair a a = none :=
    (classifyPair_eq_none_iff a a).2 rfl
  rw [h] at hnone
  cases hnone

/--
Complement-class pairings are mismatches.
-/
theorem complement_pair_is_mismatch
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.complement) :
    IsMismatch a b := by
  intro hab
  subst b
  have hnone :
      classifyPair a a = none :=
    (classifyPair_eq_none_iff a a).2 rfl
  rw [h] at hnone
  cases hnone

/--
Wobble-class pairings are mismatches.
-/
theorem wobble_pair_is_mismatch
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.wobble) :
    IsMismatch a b := by
  intro hab
  subst b
  have hnone :
      classifyPair a a = none :=
    (classifyPair_eq_none_iff a a).2 rfl
  rw [h] at hnone
  cases hnone

/--
Every transition-class pairing is a ring-preserving mismatch.
-/
theorem transition_pair_ring_preserving
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.transition) :
    RingPreservingMismatch a b := by
  constructor
  · exact transition_pair_is_mismatch a b h
  · exact
      (transition_pair_preserves_ring_class a b h).symm

/--
Every complement-class pairing is a ring-reversing mismatch.
-/
theorem complement_pair_ring_reversing
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.complement) :
    RingReversingMismatch a b := by
  constructor
  · exact complement_pair_is_mismatch a b h
  · exact complement_pair_inverts_ring_class a b h

/--
Every wobble-class pairing is a ring-reversing mismatch.
-/
theorem wobble_pair_ring_reversing
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.wobble) :
    RingReversingMismatch a b := by
  constructor
  · exact wobble_pair_is_mismatch a b h
  · exact wobble_pair_inverts_ring_class a b h

/--
A distinct pair preserves ring class exactly when it belongs to the
transition class.
-/
theorem ring_preserving_iff_transition
    (a b : DNABase) :
    RingPreservingMismatch a b ↔
      classifyPair a b =
        some PairClass.transition := by
  cases a <;> cases b <;>
    decide

/--
A distinct pair reverses ring class exactly when it belongs to either
the complement or wobble class.
-/
theorem ring_reversing_iff_complement_or_wobble
    (a b : DNABase) :
    RingReversingMismatch a b ↔
      classifyPair a b =
        some PairClass.complement ∨
      classifyPair a b =
        some PairClass.wobble := by
  cases a <;> cases b <;>
    decide

/--
No mismatch can be both ring preserving and ring reversing.
-/
theorem mismatch_ring_modes_disjoint
    (a b : DNABase) :
    ¬(
      RingPreservingMismatch a b ∧
      RingReversingMismatch a b
    ) := by
  cases a <;> cases b <;>
    decide

/--
Every mismatch is either ring preserving or ring reversing.
-/
theorem mismatch_ring_modes_exhaustive
    (a b : DNABase)
    (hMismatch : IsMismatch a b) :
    RingPreservingMismatch a b ∨
      RingReversingMismatch a b := by
  cases a <;> cases b <;>
    simp_all [
      IsMismatch,
      RingPreservingMismatch,
      RingReversingMismatch,
      dnaRBit,
      rBit,
      dnaToRNA
    ]

/-!
## Empirical error-control interface
-/

/--
An abstract biochemical error-control policy.

The predicates are deliberately unconstrained here. Particular
polymerases, repair systems, organisms, tissues, or experimental
conditions may instantiate them differently.
-/
structure ErrorControlPolicy where
  rejected : DNABase → DNABase → Prop
  repaired : DNABase → DNABase → Prop
  tolerated : DNABase → DNABase → Prop

/--
A policy is exclusive when no pair is simultaneously rejected,
repaired, and tolerated in conflicting ways.
-/
def ErrorControlPolicy.Exclusive
    (P : ErrorControlPolicy) :
    Prop :=
  (∀ a b,
    ¬(P.rejected a b ∧ P.repaired a b)) ∧
  (∀ a b,
    ¬(P.rejected a b ∧ P.tolerated a b)) ∧
  (∀ a b,
    ¬(P.repaired a b ∧ P.tolerated a b))

/--
A policy is mismatch-directed when it assigns no error-control action
to equal-base pairs.
-/
def ErrorControlPolicy.MismatchDirected
    (P : ErrorControlPolicy) :
    Prop :=
  ∀ a : DNABase,
    ¬P.rejected a a ∧
    ¬P.repaired a a ∧
    ¬P.tolerated a a

/--
An empirical hypothesis that ring-reversing mismatches are rejected
or repaired.
-/
def RingReversingControlled
    (P : ErrorControlPolicy) :
    Prop :=
  ∀ a b,
    RingReversingMismatch a b →
      P.rejected a b ∨ P.repaired a b

/--
An empirical hypothesis that ring-preserving mismatches may be
tolerated.
-/
def RingPreservingTolerated
    (P : ErrorControlPolicy) :
    Prop :=
  ∀ a b,
    RingPreservingMismatch a b →
      P.tolerated a b

/--
Under the explicit empirical hypothesis `RingReversingControlled`,
every complement-class mismatch is rejected or repaired.
-/
theorem complement_controlled_of_ring_reversing
    (P : ErrorControlPolicy)
    (hControl : RingReversingControlled P)
    (a b : DNABase)
    (hClass :
      classifyPair a b =
        some PairClass.complement) :
    P.rejected a b ∨ P.repaired a b := by
  exact hControl a b
    (complement_pair_ring_reversing a b hClass)

/--
Under the explicit empirical hypothesis `RingReversingControlled`,
every wobble-class mismatch is rejected or repaired.
-/
theorem wobble_controlled_of_ring_reversing
    (P : ErrorControlPolicy)
    (hControl : RingReversingControlled P)
    (a b : DNABase)
    (hClass :
      classifyPair a b =
        some PairClass.wobble) :
    P.rejected a b ∨ P.repaired a b := by
  exact hControl a b
    (wobble_pair_ring_reversing a b hClass)

/--
Under the explicit empirical hypothesis `RingPreservingTolerated`,
every transition-class mismatch is tolerated.
-/
theorem transition_tolerated_of_ring_preserving
    (P : ErrorControlPolicy)
    (hTolerance : RingPreservingTolerated P)
    (a b : DNABase)
    (hClass :
      classifyPair a b =
        some PairClass.transition) :
    P.tolerated a b := by
  exact hTolerance a b
    (transition_pair_ring_preserving a b hClass)

/--
The formal geometry supplies a complete two-way error-control
stratification of mismatches. Which stratum is rejected, repaired,
or tolerated remains an empirical premise.
-/
theorem formal_error_control_stratification
    (a b : DNABase)
    (hMismatch : IsMismatch a b) :
    (
      classifyPair a b =
        some PairClass.transition ∧
      RingPreservingMismatch a b
    ) ∨
    (
      (
        classifyPair a b =
          some PairClass.complement ∨
        classifyPair a b =
          some PairClass.wobble
      ) ∧
      RingReversingMismatch a b
    ) := by
  rcases
    mismatch_ring_modes_exhaustive a b hMismatch
      with hPreserving | hReversing
  · left
    exact ⟨
      (ring_preserving_iff_transition a b).1 hPreserving,
      hPreserving
    ⟩
  · right
    exact ⟨
      (ring_reversing_iff_complement_or_wobble a b).1
        hReversing,
      hReversing
    ⟩

end FDBLean
