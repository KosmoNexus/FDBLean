import FDBLean.TaggedNucleotide

/-!
# FDBLean.PairClassification

Classification of the six unordered pairings of distinct DNA bases.

The three fixed-point-free involutions partition the six pairings into
three classes of two:

* Watson--Crick:
  `{A,T}`, `{G,C}`;
* wobble analogue:
  `{G,T}`, `{A,C}`;
* transition:
  `{A,G}`, `{C,T}`.

The Watson--Crick and wobble classes exchange purine/pyrimidine ring
class. The transition class preserves ring class.
-/

namespace FDBLean

open DNABase

/-!
## Relation classes
-/

/--
The three nontrivial pair classes of the nucleotide Klein geometry.
-/
inductive PairClass
  | complement
  | wobble
  | transition
  deriving DecidableEq, Repr, Fintype

/--
Classify an ordered pair of DNA bases.

Equal bases return `none`. Every pair of distinct bases belongs to
exactly one of the three nontrivial relation classes.
-/
def classifyPair :
    DNABase → DNABase → Option PairClass
  | A, A => none
  | A, C => some PairClass.wobble
  | A, G => some PairClass.transition
  | A, T => some PairClass.complement

  | C, A => some PairClass.wobble
  | C, C => none
  | C, G => some PairClass.complement
  | C, T => some PairClass.transition

  | G, A => some PairClass.transition
  | G, C => some PairClass.complement
  | G, G => none
  | G, T => some PairClass.wobble

  | T, A => some PairClass.complement
  | T, C => some PairClass.transition
  | T, G => some PairClass.wobble
  | T, T => none

/--
A pair is unclassified exactly when its two bases are equal.
-/
theorem classifyPair_eq_none_iff
    (a b : DNABase) :
    classifyPair a b = none ↔ a = b := by
  cases a <;> cases b <;>
    decide

/--
A pair belongs to the complement class exactly when the second base
is the Watson--Crick complement of the first.
-/
theorem classifyPair_eq_complement_iff
    (a b : DNABase) :
    classifyPair a b = some PairClass.complement ↔
      b = DNABase.tauC a := by
  cases a <;> cases b <;>
    decide

/--
A pair belongs to the wobble class exactly when the second base is
the third-involution partner of the first.
-/
theorem classifyPair_eq_wobble_iff
    (a b : DNABase) :
    classifyPair a b = some PairClass.wobble ↔
      b = DNABase.tauW a := by
  cases a <;> cases b <;>
    decide

/--
A pair belongs to the transition class exactly when the second base
is the transition partner of the first.
-/
theorem classifyPair_eq_transition_iff
    (a b : DNABase) :
    classifyPair a b = some PairClass.transition ↔
      b = DNABase.tauT a := by
  cases a <;> cases b <;>
    decide

/--
Pair classification is independent of orientation.
-/
theorem classifyPair_symmetric
    (a b : DNABase) :
    classifyPair a b =
      classifyPair b a := by
  cases a <;> cases b <;>
    rfl

/--
Every pair of distinct bases belongs to one of the three classes.
-/
theorem distinct_pair_classified
    (a b : DNABase)
    (h : a ≠ b) :
    ∃ relation : PairClass,
      classifyPair a b = some relation := by
  cases a <;> cases b <;>
    simp_all [classifyPair]

/--
The class of a distinct pair is unique.
-/
theorem distinct_pair_class_unique
    (a b : DNABase)
    (x y : PairClass)
    (hx : classifyPair a b = some x)
    (hy : classifyPair a b = some y) :
    x = y := by
  rw [hx] at hy
  exact Option.some.inj hy

/-!
## The six unordered pairings
-/

/--
An unordered DNA-base pair.
-/
abbrev UnorderedDNAPair :=
  Finset DNABase

/--
The two Watson--Crick unordered pairings.
-/
def complementPairSet :
    Finset UnorderedDNAPair :=
  [
    ({A, T} : Finset DNABase),
    ({G, C} : Finset DNABase)
  ].toFinset

/--
The two wobble-class unordered pairings.
-/
def wobblePairSet :
    Finset UnorderedDNAPair :=
  [
    ({G, T} : Finset DNABase),
    ({A, C} : Finset DNABase)
  ].toFinset

/--
The two transition-class unordered pairings.
-/
def transitionPairSet :
    Finset UnorderedDNAPair :=
  [
    ({A, G} : Finset DNABase),
    ({C, T} : Finset DNABase)
  ].toFinset

/--
All six unordered pairings of distinct DNA bases.
-/
def allDistinctPairSet :
    Finset UnorderedDNAPair :=
  complementPairSet ∪
    wobblePairSet ∪
    transitionPairSet

/--
There are exactly two Watson--Crick pairings.
-/
theorem complementPairSet_card :
    complementPairSet.card = 2 := by
  decide

/--
There are exactly two wobble-class pairings.
-/
theorem wobblePairSet_card :
    wobblePairSet.card = 2 := by
  decide

/--
There are exactly two transition-class pairings.
-/
theorem transitionPairSet_card :
    transitionPairSet.card = 2 := by
  decide

/--
The three unordered relation classes are pairwise disjoint.
-/
theorem pair_sets_pairwise_disjoint :
    Disjoint complementPairSet wobblePairSet ∧
    Disjoint complementPairSet transitionPairSet ∧
    Disjoint wobblePairSet transitionPairSet := by
  decide

/--
The three orbit classes contain exactly six unordered pairings.
-/
theorem allDistinctPairSet_card :
    allDistinctPairSet.card = 6 := by
  decide

/--
The displayed six pairings are exactly all two-element subsets of
the four-base DNA alphabet.
-/
theorem allDistinctPairSet_complete :
    allDistinctPairSet =
      Finset.univ.filter
        (fun p : Finset DNABase =>
          p.card = 2) := by
  decide

/--
Proposition 7: the six unordered pairings of distinct bases partition
into three pairwise-disjoint classes of two.
-/
theorem mismatch_classification :
    complementPairSet.card = 2 ∧
    wobblePairSet.card = 2 ∧
    transitionPairSet.card = 2 ∧
    Disjoint complementPairSet wobblePairSet ∧
    Disjoint complementPairSet transitionPairSet ∧
    Disjoint wobblePairSet transitionPairSet ∧
    allDistinctPairSet.card = 6 := by
  exact ⟨
    complementPairSet_card,
    wobblePairSet_card,
    transitionPairSet_card,
    pair_sets_pairwise_disjoint.1,
    pair_sets_pairwise_disjoint.2.1,
    pair_sets_pairwise_disjoint.2.2,
    allDistinctPairSet_card
  ⟩

/-!
## Ring-class behavior
-/

/--
The purine/pyrimidine profile on DNA, transported from RNA.
-/
def dnaRBit
    (b : DNABase) :
    Bool :=
  rBit (dnaToRNA b)

/--
Watson--Crick complementation reverses ring class.
-/
theorem dnaRBit_tauC
    (b : DNABase) :
    dnaRBit (DNABase.tauC b) =
      !(dnaRBit b) := by
  cases b <;> rfl

/--
The wobble-class involution reverses ring class.
-/
theorem dnaRBit_tauW
    (b : DNABase) :
    dnaRBit (DNABase.tauW b) =
      !(dnaRBit b) := by
  cases b <;> rfl

/--
Transition substitution preserves ring class.
-/
theorem dnaRBit_tauT
    (b : DNABase) :
    dnaRBit (DNABase.tauT b) =
      dnaRBit b := by
  cases b <;> rfl

/--
Complement-class pairs always have opposite ring class.
-/
theorem complement_pair_inverts_ring_class
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.complement) :
    dnaRBit b = !(dnaRBit a) := by
  have hb :
      b = DNABase.tauC a :=
    (classifyPair_eq_complement_iff a b).1 h
  rw [hb]
  exact dnaRBit_tauC a

/--
Wobble-class pairs always have opposite ring class.
-/
theorem wobble_pair_inverts_ring_class
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.wobble) :
    dnaRBit b = !(dnaRBit a) := by
  have hb :
      b = DNABase.tauW a :=
    (classifyPair_eq_wobble_iff a b).1 h
  rw [hb]
  exact dnaRBit_tauW a

/--
Transition-class pairs always have the same ring class.
-/
theorem transition_pair_preserves_ring_class
    (a b : DNABase)
    (h :
      classifyPair a b =
        some PairClass.transition) :
    dnaRBit b = dnaRBit a := by
  have hb :
      b = DNABase.tauT a :=
    (classifyPair_eq_transition_iff a b).1 h
  rw [hb]
  exact dnaRBit_tauT a

/--
The complete pair-classification and ring-class trichotomy.
-/
theorem pair_classification_with_ring_behavior :
    (∀ a : DNABase,
      dnaRBit (DNABase.tauC a) =
        !(dnaRBit a)) ∧
    (∀ a : DNABase,
      dnaRBit (DNABase.tauW a) =
        !(dnaRBit a)) ∧
    (∀ a : DNABase,
      dnaRBit (DNABase.tauT a) =
        dnaRBit a) := by
  exact ⟨
    dnaRBit_tauC,
    dnaRBit_tauW,
    dnaRBit_tauT
  ⟩

end FDBLean
