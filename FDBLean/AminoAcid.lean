import FDBLean.ErrorControl

/-!
# FDBLean.AminoAcid

The canonical twenty-amino-acid alphabet.

This module introduces only the finite amino-acid state space.
It contains no codon assignment and no charge convention. Those
enter separately in `StandardCode` and `Charge`.
-/

namespace FDBLean

/--
The twenty standard proteinogenic amino acids.
-/
inductive AminoAcid
  | Ala
  | Arg
  | Asn
  | Asp
  | Cys
  | Gln
  | Glu
  | Gly
  | His
  | Ile
  | Leu
  | Lys
  | Met
  | Phe
  | Pro
  | Ser
  | Thr
  | Trp
  | Tyr
  | Val
  deriving DecidableEq, Repr, Fintype

namespace AminoAcid

/--
The standard proteinogenic amino-acid alphabet contains exactly
twenty elements.
-/
theorem card :
    Fintype.card AminoAcid = 20 := by
  decide

/--
A short stable name for each amino acid.

This is metadata only and plays no role in later proofs.
-/
def abbreviation : AminoAcid → String
  | Ala => "Ala"
  | Arg => "Arg"
  | Asn => "Asn"
  | Asp => "Asp"
  | Cys => "Cys"
  | Gln => "Gln"
  | Glu => "Glu"
  | Gly => "Gly"
  | His => "His"
  | Ile => "Ile"
  | Leu => "Leu"
  | Lys => "Lys"
  | Met => "Met"
  | Phe => "Phe"
  | Pro => "Pro"
  | Ser => "Ser"
  | Thr => "Thr"
  | Trp => "Trp"
  | Tyr => "Tyr"
  | Val => "Val"

/--
The one-letter amino-acid code.
-/
def oneLetter : AminoAcid → Char
  | Ala => 'A'
  | Arg => 'R'
  | Asn => 'N'
  | Asp => 'D'
  | Cys => 'C'
  | Gln => 'Q'
  | Glu => 'E'
  | Gly => 'G'
  | His => 'H'
  | Ile => 'I'
  | Leu => 'L'
  | Lys => 'K'
  | Met => 'M'
  | Phe => 'F'
  | Pro => 'P'
  | Ser => 'S'
  | Thr => 'T'
  | Trp => 'W'
  | Tyr => 'Y'
  | Val => 'V'

/--
The three-letter abbreviations distinguish all twenty amino acids.
-/
theorem abbreviation_injective :
    Function.Injective abbreviation := by
  intro a b h
  cases a <;> cases b <;>
    simp [abbreviation] at h ⊢

/--
The one-letter codes distinguish all twenty amino acids.
-/
theorem oneLetter_injective :
    Function.Injective oneLetter := by
  intro a b h
  cases a <;> cases b <;>
    simp [oneLetter] at h ⊢

end AminoAcid

end FDBLean
