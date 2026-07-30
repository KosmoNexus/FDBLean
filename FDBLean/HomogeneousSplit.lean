import FDBLean.ThreeNet

/-!
# FDBLean.HomogeneousSplit

The `22 = 7 + 7 + 7 + 1` decomposition of codon space and its
42-element generic complement.

For a chosen origin, a codon is homogeneous for one profile when that
entire three-bit profile vanishes. Each homogeneous class contains eight
codons. The three classes intersect only in the constant origin codon.
-/

namespace FDBLean

/--
The zero codon profile.
-/
def zeroProfile : CodonProfile :=
  fun _ => false

/--
The codons whose `R` profile vanishes relative to the chosen origin.
-/
def homogeneousR
    (origin : Base) :
    Finset Codon :=
  Finset.univ.filter
    (fun c => rProfileAt origin c = zeroProfile)

/--
The codons whose `S` profile vanishes relative to the chosen origin.
-/
def homogeneousS
    (origin : Base) :
    Finset Codon :=
  Finset.univ.filter
    (fun c => sProfileAt origin c = zeroProfile)

/--
The codons whose `M` profile vanishes relative to the chosen origin.
-/
def homogeneousM
    (origin : Base) :
    Finset Codon :=
  Finset.univ.filter
    (fun c => mProfileAt origin c = zeroProfile)

/--
The union of the three homogeneous profile classes.
-/
def homogeneousUnion
    (origin : Base) :
    Finset Codon :=
  homogeneousR origin ∪
    homogeneousS origin ∪
    homogeneousM origin

/--
The codons generic with respect to all three profiles.
-/
def genericCodons
    (origin : Base) :
    Finset Codon :=
  Finset.univ \ homogeneousUnion origin

/-!
## Membership of the origin codon
-/

theorem originCodon_mem_homogeneousR
    (origin : Base) :
    originCodon origin ∈ homogeneousR origin := by
  simp only [homogeneousR, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [rProfileAt_originCodon]
  rfl

theorem originCodon_mem_homogeneousS
    (origin : Base) :
    originCodon origin ∈ homogeneousS origin := by
  simp only [homogeneousS, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [sProfileAt_originCodon]
  rfl

theorem originCodon_mem_homogeneousM
    (origin : Base) :
    originCodon origin ∈ homogeneousM origin := by
  simp only [homogeneousM, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [mProfileAt_originCodon]
  rfl

/-!
## Cardinalities of the three homogeneous classes
-/

/--
Every `R`-homogeneous class contains eight codons.
-/
theorem homogeneousR_card
    (origin : Base) :
    (homogeneousR origin).card = 8 := by
  cases origin <;> decide

/--
Every `S`-homogeneous class contains eight codons.
-/
theorem homogeneousS_card
    (origin : Base) :
    (homogeneousS origin).card = 8 := by
  cases origin <;> decide

/--
Every `M`-homogeneous class contains eight codons.
-/
theorem homogeneousM_card
    (origin : Base) :
    (homogeneousM origin).card = 8 := by
  cases origin <;> decide

/-!
## Intersections
-/

/--
The `R`- and `S`-homogeneous classes meet only in the origin codon.
-/
theorem homogeneousR_inter_homogeneousS
    (origin : Base) :
    homogeneousR origin ∩ homogeneousS origin =
      {originCodon origin} := by
  cases origin <;> decide

/--
The `R`- and `M`-homogeneous classes meet only in the origin codon.
-/
theorem homogeneousR_inter_homogeneousM
    (origin : Base) :
    homogeneousR origin ∩ homogeneousM origin =
      {originCodon origin} := by
  cases origin <;> decide

/--
The `S`- and `M`-homogeneous classes meet only in the origin codon.
-/
theorem homogeneousS_inter_homogeneousM
    (origin : Base) :
    homogeneousS origin ∩ homogeneousM origin =
      {originCodon origin} := by
  cases origin <;> decide

/--
All three homogeneous classes meet only in the origin codon.
-/
theorem homogeneous_triple_intersection
    (origin : Base) :
    homogeneousR origin ∩
        homogeneousS origin ∩
        homogeneousM origin =
      {originCodon origin} := by
  cases origin <;> decide

/--
Every pairwise homogeneous intersection has cardinality one.
-/
theorem homogeneous_pairwise_intersection_card
    (origin : Base) :
    (homogeneousR origin ∩ homogeneousS origin).card = 1 ∧
    (homogeneousR origin ∩ homogeneousM origin).card = 1 ∧
    (homogeneousS origin ∩ homogeneousM origin).card = 1 := by
  constructor
  · rw [homogeneousR_inter_homogeneousS]
    simp
  constructor
  · rw [homogeneousR_inter_homogeneousM]
    simp
  · rw [homogeneousS_inter_homogeneousM]
    simp

/-!
## The 22/42 decomposition
-/

/--
The union of the three homogeneous classes contains 22 codons.
-/
theorem homogeneousUnion_card
    (origin : Base) :
    (homogeneousUnion origin).card = 22 := by
  cases origin <;> decide

/--
The homogeneous union decomposes as three disjoint seven-element
remainders together with the shared origin codon.
-/
theorem homogeneous_twenty_two_decomposition :
    22 = 7 + 7 + 7 + 1 := by
  rfl

/--
The complement of the homogeneous union contains 42 codons.
-/
theorem genericCodons_card
    (origin : Base) :
    (genericCodons origin).card = 42 := by
  cases origin <;> decide

/--
Codon space splits into 22 homogeneous and 42 generic codons.
-/
theorem codon_twenty_two_forty_two_split
    (origin : Base) :
    (homogeneousUnion origin).card +
      (genericCodons origin).card = 64 := by
  rw [homogeneousUnion_card, genericCodons_card]

/--
The homogeneous and generic sets are disjoint.
-/
theorem homogeneous_generic_disjoint
    (origin : Base) :
    Disjoint (homogeneousUnion origin) (genericCodons origin) := by
  rw [Finset.disjoint_left]
  intro c hcHom hcGen
  exact (Finset.mem_sdiff.mp hcGen).2 hcHom

/--
The homogeneous and generic sets exhaust codon space.
-/
theorem homogeneous_union_generic
    (origin : Base) :
    homogeneousUnion origin ∪ genericCodons origin =
      Finset.univ := by
  simp [genericCodons]

/--
A codon is generic exactly when none of its three profiles vanishes.
-/
theorem mem_genericCodons_iff
    (origin : Base)
    (c : Codon) :
    c ∈ genericCodons origin ↔
      rProfileAt origin c ≠ zeroProfile ∧
      sProfileAt origin c ≠ zeroProfile ∧
      mProfileAt origin c ≠ zeroProfile := by
  simp [genericCodons, homogeneousUnion,
    homogeneousR, homogeneousS, homogeneousM]

end FDBLean
