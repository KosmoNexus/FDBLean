import FDBLean.Charge

/-!
# FDBLean.PositionalChargeLaw

The positional charge law for adenosine deamination.

At the sequence level, adenosine-to-inosine editing is represented as
the directed substitution `A → G`.

Against the standard genetic code:

* first-position nonsynonymous amino-acid substitutions have
  nonpositive charge change;
* second-position nonsynonymous amino-acid substitutions have
  nonnegative charge change;
* third-position amino-acid substitutions have zero charge change.

The proof is exhaustive finite enumeration of the standard codon
table. Integer half-charge units are used internally so that the
enumeration remains kernel-reducible without relying on rational
normalization.
-/

namespace FDBLean

open Base
open AminoAcid
open TranslationProduct

/-!
## Single-position adenosine editing
-/

/--
Replace the nucleotide at position `i` by `G`, leaving the other two
positions unchanged.

The biological precondition that the source base is `A` is stated
separately in the theorems below.
-/
def editAAt
    (i : Fin 3)
    (c : Codon) :
    Codon :=
  fun j =>
    if j = i then G else c j

@[simp]
theorem editAAt_same
    (i : Fin 3)
    (c : Codon) :
    editAAt i c i = G := by
  simp [editAAt]

theorem editAAt_other
    (i j : Fin 3)
    (c : Codon)
    (h : j ≠ i) :
    editAAt i c j = c j := by
  simp [editAAt, h]

/--
Editing an already edited position again has no further effect.
-/
theorem editAAt_idempotent
    (i : Fin 3)
    (c : Codon) :
    editAAt i (editAAt i c) =
      editAAt i c := by
  funext j
  by_cases h : j = i
  · simp [editAAt, h]
  · simp [editAAt, h]

/-!
## Integer half-charge units
-/

/--
Twice the amino-acid charge.

Using integer half-charge units represents:

* Arg, Lys as `+2`;
* His as `+1`;
* Asp, Glu as `-2`;
* all neutral residues as `0`.
-/
def chargeUnits : AminoAcid → ℤ
  | Arg => 2
  | Lys => 2
  | His => 1
  | Asp => -2
  | Glu => -2
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

/--
The rational charge convention is exactly one half of the integer
charge-unit convention.
-/
theorem aminoAcidCharge_eq_chargeUnits_half
    (aa : AminoAcid) :
    aminoAcidCharge aa =
      (chargeUnits aa : ℚ) / 2 := by
  cases aa <;>
    norm_num [aminoAcidCharge, chargeUnits]

/--
Charge change in integer half-charge units.
-/
def chargeUnitChange
    (source target : AminoAcid) :
    ℤ :=
  chargeUnits target - chargeUnits source

/--
The rational charge change is exactly half the integer-unit change.
-/
theorem chargeChange_eq_chargeUnitChange_half
    (source target : AminoAcid) :
    chargeChange source target =
      (chargeUnitChange source target : ℚ) / 2 := by
  rw [
    chargeChange,
    aminoAcidCharge_eq_chargeUnits_half,
    aminoAcidCharge_eq_chargeUnits_half
  ]
  simp [chargeUnitChange]
  ring

/-!
## Exhaustive integer positional laws
-/

/--
At the first codon position, every amino-acid-to-amino-acid outcome
of an admissible `A → G` edit has nonpositive charge change.
-/
theorem first_position_charge_units_nonpositive :
    ∀ c : Codon,
    ∀ source target : AminoAcid,
      c (0 : Fin 3) = A →
      standardCode c = aminoAcid source →
      standardCode
          (editAAt (0 : Fin 3) c) =
        aminoAcid target →
      source ≠ target →
      chargeUnitChange source target ≤ 0 := by
  decide +revert

/--
At the second codon position, every amino-acid-to-amino-acid outcome
of an admissible `A → G` edit has nonnegative charge change.
-/
theorem second_position_charge_units_nonnegative :
    ∀ c : Codon,
    ∀ source target : AminoAcid,
      c (1 : Fin 3) = A →
      standardCode c = aminoAcid source →
      standardCode
          (editAAt (1 : Fin 3) c) =
        aminoAcid target →
      source ≠ target →
      0 ≤ chargeUnitChange source target := by
  decide +revert

/--
At the third codon position, every amino-acid-to-amino-acid outcome
of an admissible `A → G` edit is charge neutral.
-/
theorem third_position_charge_units_zero :
    ∀ c : Codon,
    ∀ source target : AminoAcid,
      c (2 : Fin 3) = A →
      standardCode c = aminoAcid source →
      standardCode
          (editAAt (2 : Fin 3) c) =
        aminoAcid target →
      chargeUnitChange source target = 0 := by
  decide +revert

/-!
## Rational-valued positional charge law
-/

/--
First-position nonsynonymous adenosine edits have
`Δq ≤ 0`.
-/
theorem first_position_charge_nonpositive
    (c : Codon)
    (source target : AminoAcid)
    (hA : c (0 : Fin 3) = A)
    (hSource :
      standardCode c = aminoAcid source)
    (hTarget :
      standardCode
          (editAAt (0 : Fin 3) c) =
        aminoAcid target)
    (hNonsynonymous : source ≠ target) :
    chargeChange source target ≤ 0 := by
  have hUnits :
      chargeUnitChange source target ≤ 0 :=
    first_position_charge_units_nonpositive
      c source target
      hA hSource hTarget hNonsynonymous
  have hCast :
      (chargeUnitChange source target : ℚ) ≤ 0 := by
    exact_mod_cast hUnits
  rw [chargeChange_eq_chargeUnitChange_half]
  linarith

/--
Second-position nonsynonymous adenosine edits have
`Δq ≥ 0`.
-/
theorem second_position_charge_nonnegative
    (c : Codon)
    (source target : AminoAcid)
    (hA : c (1 : Fin 3) = A)
    (hSource :
      standardCode c = aminoAcid source)
    (hTarget :
      standardCode
          (editAAt (1 : Fin 3) c) =
        aminoAcid target)
    (hNonsynonymous : source ≠ target) :
    0 ≤ chargeChange source target := by
  have hUnits :
      0 ≤ chargeUnitChange source target :=
    second_position_charge_units_nonnegative
      c source target
      hA hSource hTarget hNonsynonymous
  have hCast :
      (0 : ℚ) ≤
        (chargeUnitChange source target : ℚ) := by
    exact_mod_cast hUnits
  rw [chargeChange_eq_chargeUnitChange_half]
  linarith

/--
Third-position amino-acid outcomes of adenosine editing have
`Δq = 0`.
-/
theorem third_position_charge_zero
    (c : Codon)
    (source target : AminoAcid)
    (hA : c (2 : Fin 3) = A)
    (hSource :
      standardCode c = aminoAcid source)
    (hTarget :
      standardCode
          (editAAt (2 : Fin 3) c) =
        aminoAcid target) :
    chargeChange source target = 0 := by
  have hUnits :
      chargeUnitChange source target = 0 :=
    third_position_charge_units_zero
      c source target
      hA hSource hTarget
  have hCast :
      (chargeUnitChange source target : ℚ) = 0 := by
    exact_mod_cast hUnits
  rw [chargeChange_eq_chargeUnitChange_half]
  rw [hCast]
  norm_num

/--
Proposition 10: the sign of amino-acid charge change under admissible
adenosine editing is fixed by codon position.
-/
theorem positional_charge_law :
    (
      ∀ c : Codon,
      ∀ source target : AminoAcid,
        c (0 : Fin 3) = A →
        standardCode c = aminoAcid source →
        standardCode
            (editAAt (0 : Fin 3) c) =
          aminoAcid target →
        source ≠ target →
        chargeChange source target ≤ 0
    ) ∧
    (
      ∀ c : Codon,
      ∀ source target : AminoAcid,
        c (1 : Fin 3) = A →
        standardCode c = aminoAcid source →
        standardCode
            (editAAt (1 : Fin 3) c) =
          aminoAcid target →
        source ≠ target →
        0 ≤ chargeChange source target
    ) ∧
    (
      ∀ c : Codon,
      ∀ source target : AminoAcid,
        c (2 : Fin 3) = A →
        standardCode c = aminoAcid source →
        standardCode
            (editAAt (2 : Fin 3) c) =
          aminoAcid target →
        chargeChange source target = 0
    ) := by
  exact ⟨
    first_position_charge_nonpositive,
    second_position_charge_nonnegative,
    third_position_charge_zero
  ⟩

end FDBLean
