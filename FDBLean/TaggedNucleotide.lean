import FDBLean.RNADNATransport

/-!
# FDBLean.TaggedNucleotide

A unified eight-state nucleotide object obtained by tagging the
four-state nucleotide alphabet with polymer identity.

The construction is a direct product of:

* the four-state RNA nucleotide geometry;
* a two-state RNA/DNA tag.

The resulting state space has cardinality eight. This is a tagged
doubling only. No identification with any unrelated `84`, `168`, or
Kosmoplex construction is asserted.
-/

namespace FDBLean

/-!
## Polymer tag
-/

/--
The polymer carrying the nucleotide.
-/
inductive PolymerTag
  | RNA
  | DNA
  deriving DecidableEq, Repr, Fintype

namespace PolymerTag

/--
Exchange RNA and DNA tags.
-/
def flip : PolymerTag → PolymerTag
  | RNA => DNA
  | DNA => RNA

/--
Polymer-tag exchange is involutive.
-/
theorem flip_involutive :
    Function.Involutive flip := by
  intro p
  cases p <;> rfl

/--
There are exactly two polymer tags.
-/
theorem card :
    Fintype.card PolymerTag = 2 := by
  decide

end PolymerTag

/-!
## Tagged nucleotide
-/

/--
A tagged nucleotide consists of an RNA-coordinate base together with
a polymer tag.

For DNA-tagged states, the RNA-coordinate base is interpreted through
the canonical `U ↔ T` transport.
-/
abbrev TaggedNucleotide := Base × PolymerTag

/--
The tagged nucleotide space has eight elements.
-/
theorem card_taggedNucleotide :
    Fintype.card TaggedNucleotide = 8 := by
  decide

/--
Embed an RNA nucleotide into the tagged space.
-/
def tagRNA
    (b : Base) :
    TaggedNucleotide :=
  (b, PolymerTag.RNA)

/--
Embed a DNA nucleotide into the tagged space using the canonical
DNA-to-RNA coordinate.
-/
def tagDNA
    (b : DNABase) :
    TaggedNucleotide :=
  (dnaToRNA b, PolymerTag.DNA)

/--
Read a tagged nucleotide as an RNA base.
-/
def taggedAsRNA
    (x : TaggedNucleotide) :
    Base :=
  x.1

/--
Read a tagged nucleotide as a DNA base.
-/
def taggedAsDNA
    (x : TaggedNucleotide) :
    DNABase :=
  rnaToDNA x.1

@[simp]
theorem taggedAsRNA_tagRNA
    (b : Base) :
    taggedAsRNA (tagRNA b) = b := by
  rfl

@[simp]
theorem taggedAsDNA_tagDNA
    (b : DNABase) :
    taggedAsDNA (tagDNA b) = b := by
  simp [taggedAsDNA, tagDNA]

/--
RNA embedding is injective.
-/
theorem tagRNA_injective :
    Function.Injective tagRNA := by
  intro a b h
  exact congrArg Prod.fst h

/--
DNA embedding is injective.
-/
theorem tagDNA_injective :
    Function.Injective tagDNA := by
  intro a b h
  have hab :=
    congrArg taggedAsDNA h
  simpa using hab
/--
The RNA and DNA tagged images are disjoint.
-/
theorem tagRNA_ne_tagDNA
    (r : Base)
    (d : DNABase) :
    tagRNA r ≠ tagDNA d := by
  intro h
  have :=
    congrArg Prod.snd h
  cases this

/-!
## Lifted Klein operations
-/

/--
Lift Watson--Crick complementation to the tagged space while preserving
the polymer tag.
-/
def taggedTauC
    (x : TaggedNucleotide) :
    TaggedNucleotide :=
  (tauC x.1, x.2)

/--
Lift transition substitution to the tagged space while preserving the
polymer tag.
-/
def taggedTauT
    (x : TaggedNucleotide) :
    TaggedNucleotide :=
  (tauT x.1, x.2)

/--
Lift the third Klein involution to the tagged space while preserving
the polymer tag.
-/
def taggedTauW
    (x : TaggedNucleotide) :
    TaggedNucleotide :=
  (tauW x.1, x.2)

/--
Exchange polymer identity while preserving the common nucleotide
coordinate.
-/
def taggedPolymerFlip
    (x : TaggedNucleotide) :
    TaggedNucleotide :=
  (x.1, PolymerTag.flip x.2)

/--
Tagged complementation is involutive.
-/
theorem taggedTauC_involutive :
    Function.Involutive taggedTauC := by
  intro x
  rcases x with ⟨b, p⟩
  apply Prod.ext
  · exact tauC_involutive b
  · rfl
/--
Tagged transition substitution is involutive.
-/
theorem taggedTauT_involutive :
    Function.Involutive taggedTauT := by
  intro x
  rcases x with ⟨b, p⟩
  apply Prod.ext
  · exact tauT_involutive b
  · rfl
/--
The lifted third involution is involutive.
-/
theorem taggedTauW_involutive :
    Function.Involutive taggedTauW := by
  intro x
  rcases x with ⟨b, p⟩
  apply Prod.ext
  · exact tauW_involutive b
  · rfl
/--
Polymer exchange is involutive.
-/
theorem taggedPolymerFlip_involutive :
    Function.Involutive taggedPolymerFlip := by
  intro x
  rcases x with ⟨b, p⟩
  apply Prod.ext
  · rfl
  · exact PolymerTag.flip_involutive p

/--
The lifted biochemical involutions preserve polymer identity.
-/
theorem taggedTauC_preserves_tag
    (x : TaggedNucleotide) :
    (taggedTauC x).2 = x.2 := by
  rfl

theorem taggedTauT_preserves_tag
    (x : TaggedNucleotide) :
    (taggedTauT x).2 = x.2 := by
  rfl

theorem taggedTauW_preserves_tag
    (x : TaggedNucleotide) :
    (taggedTauW x).2 = x.2 := by
  rfl

/--
Polymer exchange commutes with tagged Watson--Crick complementation.
-/
theorem taggedPolymerFlip_commutes_tauC
    (x : TaggedNucleotide) :
    taggedPolymerFlip (taggedTauC x) =
      taggedTauC (taggedPolymerFlip x) := by
  cases x
  all_goals rfl

/--
Polymer exchange commutes with tagged transition substitution.
-/
theorem taggedPolymerFlip_commutes_tauT
    (x : TaggedNucleotide) :
    taggedPolymerFlip (taggedTauT x) =
      taggedTauT (taggedPolymerFlip x) := by
  cases x
  all_goals rfl

/--
Polymer exchange commutes with the lifted third involution.
-/
theorem taggedPolymerFlip_commutes_tauW
    (x : TaggedNucleotide) :
    taggedPolymerFlip (taggedTauW x) =
      taggedTauW (taggedPolymerFlip x) := by
  cases x
  all_goals rfl

/--
The tagged state space is the Cartesian product of the four-state
nucleotide geometry with the two-state polymer tag.
-/
theorem tagged_nucleotide_is_eight_state_product :
    Fintype.card TaggedNucleotide =
      Fintype.card Base * Fintype.card PolymerTag := by
  decide

end FDBLean
