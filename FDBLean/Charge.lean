import FDBLean.StandardCode

/-!
# FDBLean.Charge

A rational-valued amino-acid side-chain charge convention.

The convention used in the manuscript is:

* arginine and lysine: `+1`;
* histidine: `+1/2`;
* aspartate and glutamate: `-1`;
* all other standard amino acids: `0`.

This is a declared biochemical convention, not a consequence of the
nucleotide geometry. Using rational values keeps every later charge
comparison exact.
-/

namespace FDBLean

open AminoAcid

/--
The side-chain charge assigned to a standard amino acid.

Histidine is assigned `+1/2`, corresponding to the manuscript's
physiological-pH convention.
-/
def aminoAcidCharge : AminoAcid → ℚ
  | Arg => 1
  | Lys => 1
  | His => 1 / 2
  | Asp => -1
  | Glu => -1
  | Ala => 0
  | Asn => 0
  | Cys => 0
  | Gln => 0
  | Gly => 0
  | Ile => 0
  | Leu => 0
  | Met => 0
  | Phe => 0
  | Pro => 0
  | Ser => 0
  | Thr => 0
  | Trp => 0
  | Tyr => 0
  | Val => 0

@[simp]
theorem charge_Arg :
    aminoAcidCharge Arg = 1 := by
  rfl

@[simp]
theorem charge_Lys :
    aminoAcidCharge Lys = 1 := by
  rfl

@[simp]
theorem charge_His :
    aminoAcidCharge His = 1 / 2 := by
  rfl

@[simp]
theorem charge_Asp :
    aminoAcidCharge Asp = -1 := by
  rfl

@[simp]
theorem charge_Glu :
    aminoAcidCharge Glu = -1 := by
  rfl

/--
Every amino-acid charge used here is one of
`-1`, `0`, `1/2`, or `1`.
-/
theorem aminoAcidCharge_range
    (aa : AminoAcid) :
    aminoAcidCharge aa = -1 ∨
    aminoAcidCharge aa = 0 ∨
    aminoAcidCharge aa = 1 / 2 ∨
    aminoAcidCharge aa = 1 := by
  cases aa <;> norm_num [aminoAcidCharge]

/--
The positively charged amino acids under this convention are exactly
arginine, histidine, and lysine.
-/
theorem aminoAcidCharge_pos_iff
    (aa : AminoAcid) :
    aminoAcidCharge aa > 0 ↔
      aa = Arg ∨ aa = His ∨ aa = Lys := by
  cases aa <;> norm_num [aminoAcidCharge] <;> simp

/--
The negatively charged amino acids under this convention are exactly
aspartate and glutamate.
-/
theorem aminoAcidCharge_neg_iff
    (aa : AminoAcid) :
    aminoAcidCharge aa < 0 ↔
      aa = Asp ∨ aa = Glu := by
  cases aa <;> norm_num [aminoAcidCharge] <;> simp

/--
The neutral amino acids are precisely those outside the five charged
residues in this convention.
-/
theorem aminoAcidCharge_eq_zero_iff
    (aa : AminoAcid) :
    aminoAcidCharge aa = 0 ↔
      aa ≠ Arg ∧
      aa ≠ His ∧
      aa ≠ Lys ∧
      aa ≠ Asp ∧
      aa ≠ Glu := by
  cases aa <;> norm_num [aminoAcidCharge] <;> simp



/--
The charge change associated with an amino-acid substitution.
-/
def chargeChange
    (source target : AminoAcid) :
    ℚ :=
  aminoAcidCharge target -
    aminoAcidCharge source

/--
A synonymous substitution has zero charge change.
-/
@[simp]
theorem chargeChange_self
    (aa : AminoAcid) :
    chargeChange aa aa = 0 := by
  simp [chargeChange]

/--
Charge change reverses sign when source and target are exchanged.
-/
theorem chargeChange_reverse
    (a b : AminoAcid) :
    chargeChange b a =
      -(chargeChange a b) := by
  simp [chargeChange]


/--
Charge change composes additively through an intermediate amino acid.
-/
theorem chargeChange_add
    (a b c : AminoAcid) :
    chargeChange a b +
      chargeChange b c =
    chargeChange a c := by
  simp [chargeChange]

/--
A translation product has an amino-acid charge only when it is not a
stop signal.
-/
def translationProductCharge :
    TranslationProduct → Option ℚ
  | TranslationProduct.aminoAcid aa =>
      some (aminoAcidCharge aa)
  | TranslationProduct.stop =>
      none

@[simp]
theorem translationProductCharge_aminoAcid
    (aa : AminoAcid) :
    translationProductCharge
      (TranslationProduct.aminoAcid aa) =
        some (aminoAcidCharge aa) := by
  rfl

@[simp]
theorem translationProductCharge_stop :
    translationProductCharge
      TranslationProduct.stop = none := by
  rfl

end FDBLean
