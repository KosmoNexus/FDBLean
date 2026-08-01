import FDBLean.DNAAlphabet

/-!
# FDBLean.RNADNATransport

Transport of the RNA nucleotide alphabet to the DNA nucleotide
alphabet by the canonical substitution `U ↔ T`.

The transport is a bijection and intertwines all three involutions:

* Watson--Crick complementation;
* transition substitution;
* the third Klein involution.

Thus the RNA and DNA alphabets carry isomorphic four-state torsor
geometry. This is a formal structural statement, not a claim that
each relation has the same biochemical role or admissibility in the
two polymers.
-/

namespace FDBLean

/-!
## Base-level RNA/DNA transport
-/

/--
Transport an RNA base to the corresponding DNA base.
-/
def rnaToDNA : Base → DNABase
  | Base.A => DNABase.A
  | Base.C => DNABase.C
  | Base.G => DNABase.G
  | Base.U => DNABase.T

/--
Transport a DNA base to the corresponding RNA base.
-/
def dnaToRNA : DNABase → Base
  | DNABase.A => Base.A
  | DNABase.C => Base.C
  | DNABase.G => Base.G
  | DNABase.T => Base.U

@[simp]
theorem dnaToRNA_rnaToDNA
    (b : Base) :
    dnaToRNA (rnaToDNA b) = b := by
  cases b <;> rfl

@[simp]
theorem rnaToDNA_dnaToRNA
    (b : DNABase) :
    rnaToDNA (dnaToRNA b) = b := by
  cases b <;> rfl

/--
The canonical equivalence between the RNA and DNA alphabets.
-/
def rnaDNAEquiv : Base ≃ DNABase where
  toFun := rnaToDNA
  invFun := dnaToRNA
  left_inv := dnaToRNA_rnaToDNA
  right_inv := rnaToDNA_dnaToRNA

/--
RNA-to-DNA transport is injective.
-/
theorem rnaToDNA_injective :
    Function.Injective rnaToDNA :=
  rnaDNAEquiv.injective

/--
RNA-to-DNA transport is surjective.
-/
theorem rnaToDNA_surjective :
    Function.Surjective rnaToDNA :=
  rnaDNAEquiv.surjective

/-!
## Intertwining of the three involutions
-/

/--
RNA-to-DNA transport preserves Watson--Crick complementation.
-/
theorem rnaToDNA_tauC
    (b : Base) :
    rnaToDNA (tauC b) =
      DNABase.tauC (rnaToDNA b) := by
  cases b <;> rfl

/--
RNA-to-DNA transport preserves transition substitution.
-/
theorem rnaToDNA_tauT
    (b : Base) :
    rnaToDNA (tauT b) =
      DNABase.tauT (rnaToDNA b) := by
  cases b <;> rfl

/--
RNA-to-DNA transport preserves the third Klein involution.
-/
theorem rnaToDNA_tauW
    (b : Base) :
    rnaToDNA (tauW b) =
      DNABase.tauW (rnaToDNA b) := by
  cases b <;> rfl

/--
DNA-to-RNA transport preserves Watson--Crick complementation.
-/
theorem dnaToRNA_tauC
    (b : DNABase) :
    dnaToRNA (DNABase.tauC b) =
      tauC (dnaToRNA b) := by
  cases b <;> rfl

/--
DNA-to-RNA transport preserves transition substitution.
-/
theorem dnaToRNA_tauT
    (b : DNABase) :
    dnaToRNA (DNABase.tauT b) =
      tauT (dnaToRNA b) := by
  cases b <;> rfl

/--
DNA-to-RNA transport preserves the third Klein involution.
-/
theorem dnaToRNA_tauW
    (b : DNABase) :
    dnaToRNA (DNABase.tauW b) =
      tauW (dnaToRNA b) := by
  cases b <;> rfl

/--
Functional form of Watson--Crick transport.
-/
theorem rnaToDNA_comp_tauC :
    rnaToDNA ∘ tauC =
      DNABase.tauC ∘ rnaToDNA := by
  funext b
  exact rnaToDNA_tauC b

/--
Functional form of transition transport.
-/
theorem rnaToDNA_comp_tauT :
    rnaToDNA ∘ tauT =
      DNABase.tauT ∘ rnaToDNA := by
  funext b
  exact rnaToDNA_tauT b

/--
Functional form of third-involution transport.
-/
theorem rnaToDNA_comp_tauW :
    rnaToDNA ∘ tauW =
      DNABase.tauW ∘ rnaToDNA := by
  funext b
  exact rnaToDNA_tauW b

/-!
## Codon-level transport
-/

/--
A DNA codon is an ordered triple of DNA bases.
-/
abbrev DNACodon := Fin 3 → DNABase

/--
Transport an RNA codon coordinatewise to DNA.
-/
def rnaCodonToDNA
    (c : Codon) :
    DNACodon :=
  fun i => rnaToDNA (c i)

/--
Transport a DNA codon coordinatewise to RNA.
-/
def dnaCodonToRNA
    (c : DNACodon) :
    Codon :=
  fun i => dnaToRNA (c i)

@[simp]
theorem dnaCodonToRNA_rnaCodonToDNA
    (c : Codon) :
    dnaCodonToRNA (rnaCodonToDNA c) = c := by
  funext i
  exact dnaToRNA_rnaToDNA (c i)

@[simp]
theorem rnaCodonToDNA_dnaCodonToRNA
    (c : DNACodon) :
    rnaCodonToDNA (dnaCodonToRNA c) = c := by
  funext i
  exact rnaToDNA_dnaToRNA (c i)

/--
The canonical equivalence between RNA and DNA codon spaces.
-/
def rnaDNACodonEquiv : Codon ≃ DNACodon where
  toFun := rnaCodonToDNA
  invFun := dnaCodonToRNA
  left_inv := dnaCodonToRNA_rnaCodonToDNA
  right_inv := rnaCodonToDNA_dnaCodonToRNA

/--
The DNA codon space contains exactly 64 elements.
-/
theorem card_dnaCodon :
    Fintype.card DNACodon = 64 := by
  decide

/--
RNA and DNA codon spaces have equal cardinality.
-/
theorem card_rnaCodon_eq_card_dnaCodon :
    Fintype.card Codon =
      Fintype.card DNACodon := by
  rw [card_codon, card_dnaCodon]

/--
Coordinatewise RNA-to-DNA transport preserves Watson--Crick
complementation.
-/
theorem rnaCodonToDNA_tauC
    (c : Codon) :
    rnaCodonToDNA (tauCCodon c) =
      fun i =>
        DNABase.tauC (rnaCodonToDNA c i) := by
  funext i
  exact rnaToDNA_tauC (c i)

/--
Coordinatewise RNA-to-DNA transport preserves transition
substitution.
-/
theorem rnaCodonToDNA_tauT
    (c : Codon) :
    rnaCodonToDNA (tauTCodon c) =
      fun i =>
        DNABase.tauT (rnaCodonToDNA c i) := by
  funext i
  exact rnaToDNA_tauT (c i)

/--
Coordinatewise RNA-to-DNA transport preserves the third Klein
involution.
-/
theorem rnaCodonToDNA_tauW
    (c : Codon) :
    rnaCodonToDNA (tauWCodon c) =
      fun i =>
        DNABase.tauW (rnaCodonToDNA c i) := by
  funext i
  exact rnaToDNA_tauW (c i)

/--
The RNA/DNA substitution `U ↔ T` preserves the complete finite
four-state and codon geometry.
-/
theorem rna_dna_geometry_preserved :
    Function.Bijective rnaToDNA ∧
    (∀ b : Base,
      rnaToDNA (tauC b) =
        DNABase.tauC (rnaToDNA b)) ∧
    (∀ b : Base,
      rnaToDNA (tauT b) =
        DNABase.tauT (rnaToDNA b)) ∧
    (∀ b : Base,
      rnaToDNA (tauW b) =
        DNABase.tauW (rnaToDNA b)) := by
  exact ⟨
    ⟨rnaToDNA_injective, rnaToDNA_surjective⟩,
    rnaToDNA_tauC,
    rnaToDNA_tauT,
    rnaToDNA_tauW
  ⟩

end FDBLean
