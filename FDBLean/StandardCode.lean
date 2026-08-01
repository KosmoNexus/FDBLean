import FDBLean.AminoAcid

/-!
# FDBLean.StandardCode

The standard RNA genetic code.

This module is the first point in the development where codons are
assigned to amino acids. The assignment is empirical biological data,
not a consequence of the nucleotide Klein geometry.

Stop codons are represented explicitly rather than being conflated
with amino acids.
-/

namespace FDBLean

open Base
open AminoAcid

/--
The translation product of one RNA codon.
-/
inductive TranslationProduct
  | aminoAcid (aa : AminoAcid)
  | stop
  deriving DecidableEq, Repr

open TranslationProduct

/--
The standard RNA codon table.
-/
def standardCode
    (c : Codon) :
    TranslationProduct :=
  match c 0, c 1, c 2 with
  -- U-starting codons
  | U, U, U => aminoAcid Phe
  | U, U, C => aminoAcid Phe
  | U, U, A => aminoAcid Leu
  | U, U, G => aminoAcid Leu

  | U, C, U => aminoAcid Ser
  | U, C, C => aminoAcid Ser
  | U, C, A => aminoAcid Ser
  | U, C, G => aminoAcid Ser

  | U, A, U => aminoAcid Tyr
  | U, A, C => aminoAcid Tyr
  | U, A, A => stop
  | U, A, G => stop

  | U, G, U => aminoAcid Cys
  | U, G, C => aminoAcid Cys
  | U, G, A => stop
  | U, G, G => aminoAcid Trp

  -- C-starting codons
  | C, U, U => aminoAcid Leu
  | C, U, C => aminoAcid Leu
  | C, U, A => aminoAcid Leu
  | C, U, G => aminoAcid Leu

  | C, C, U => aminoAcid Pro
  | C, C, C => aminoAcid Pro
  | C, C, A => aminoAcid Pro
  | C, C, G => aminoAcid Pro

  | C, A, U => aminoAcid His
  | C, A, C => aminoAcid His
  | C, A, A => aminoAcid Gln
  | C, A, G => aminoAcid Gln

  | C, G, U => aminoAcid Arg
  | C, G, C => aminoAcid Arg
  | C, G, A => aminoAcid Arg
  | C, G, G => aminoAcid Arg

  -- A-starting codons
  | A, U, U => aminoAcid Ile
  | A, U, C => aminoAcid Ile
  | A, U, A => aminoAcid Ile
  | A, U, G => aminoAcid Met

  | A, C, U => aminoAcid Thr
  | A, C, C => aminoAcid Thr
  | A, C, A => aminoAcid Thr
  | A, C, G => aminoAcid Thr

  | A, A, U => aminoAcid Asn
  | A, A, C => aminoAcid Asn
  | A, A, A => aminoAcid Lys
  | A, A, G => aminoAcid Lys

  | A, G, U => aminoAcid Ser
  | A, G, C => aminoAcid Ser
  | A, G, A => aminoAcid Arg
  | A, G, G => aminoAcid Arg

  -- G-starting codons
  | G, U, U => aminoAcid Val
  | G, U, C => aminoAcid Val
  | G, U, A => aminoAcid Val
  | G, U, G => aminoAcid Val

  | G, C, U => aminoAcid Ala
  | G, C, C => aminoAcid Ala
  | G, C, A => aminoAcid Ala
  | G, C, G => aminoAcid Ala

  | G, A, U => aminoAcid Asp
  | G, A, C => aminoAcid Asp
  | G, A, A => aminoAcid Glu
  | G, A, G => aminoAcid Glu

  | G, G, U => aminoAcid Gly
  | G, G, C => aminoAcid Gly
  | G, G, A => aminoAcid Gly
  | G, G, G => aminoAcid Gly

/--
Construct a codon from its three ordered bases.
-/
def codon
    (b₀ b₁ b₂ : Base) :
    Codon
  | 0 => b₀
  | 1 => b₁
  | 2 => b₂

/--
A codon is a stop codon exactly when it is `UAA`, `UAG`, or `UGA`.
-/
theorem standardCode_eq_stop_iff
    (c : Codon) :
    standardCode c = stop ↔
      c = codon U A A ∨
      c = codon U A G ∨
      c = codon U G A := by
  decide +revert

/--
There are exactly three stop codons in the standard code.
-/
theorem standard_stop_codon_count :
    (Finset.univ.filter
      (fun c : Codon =>
        standardCode c = stop)).card = 3 := by
  decide

/--
The remaining sixty-one codons encode amino acids.
-/
theorem standard_amino_acid_codon_count :
    (Finset.univ.filter
      (fun c : Codon =>
        ∃ aa : AminoAcid,
          standardCode c = aminoAcid aa)).card = 61 := by
  decide

/--
Every codon either encodes exactly one amino acid or is a stop codon.
-/
theorem standardCode_exhaustive
    (c : Codon) :
    (∃ aa : AminoAcid,
      standardCode c = aminoAcid aa) ∨
    standardCode c = stop := by
  cases h : standardCode c with
  | aminoAcid aa =>
      exact Or.inl ⟨aa, rfl⟩
  | stop =>
      exact Or.inr rfl

/--
No codon is simultaneously an amino-acid codon and a stop codon.
-/
theorem aminoAcid_ne_stop
    (aa : AminoAcid) :
    aminoAcid aa ≠ stop := by
  intro h
  cases h

end FDBLean
