import FDBLean.PositionalChargeLaw
import FDBLean.FanoObstruction
import FDBLean.PositionalChargeLaw

/-!
# FDBLean.MainTheoremChain

Capstone assembly of the Formal Deductive Biology nucleotide program.

This module introduces no new biological definitions and no new
empirical assumptions. It gathers the principal theorem-bearing
results of the development into one explicit, machine-checkable
object.

The ordering records the architecture of the program:

1. nucleotide Klein torsor;
2. profile XOR geometry;
3. pairwise-transverse codon profiles;
4. 22/42 codon decomposition;
5. directed editing trichotomy and exact edit recovery;
6. absorbing alphabet and origin narrowing;
7. complement-to-wobble transport;
8. RNA/DNA structural transport;
9. mismatch and error-control stratification;
10. positional amino-acid charge law.

The standard genetic code and amino-acid charge convention remain
declared empirical inputs. Lean verifies the consequences of those
inputs; it does not derive them from nucleotide geometry.
-/

namespace FDBLean

open Base
open TranslationProduct

/--
The principal results of the FDB nucleotide construction, collected
without collapsing their distinct epistemic roles.
-/
structure MainTheoremChain where

  /-- The RNA alphabet is a torsor under the Klein four-group. -/
  nucleotideTorsor :
    ∀ a b : Base,
      ∃! g : Klein,
        kleinAct g a = b

  /-- The three relative nucleotide profiles satisfy the XOR law. -/
  profileXor :
    ∀ origin b : Base,
      Bool.xor
        (rBitAt origin b)
        (sBitAt origin b) =
      mBitAt origin b

  /-- The three codon-profile partitions are pairwise transverse. -/
  codonThreeNet :
    ∀ origin : Base,
      (∀ r s : CodonProfile,
        ∃! c : Codon,
          rProfileAt origin c = r ∧
          sProfileAt origin c = s) ∧
      (∀ r m : CodonProfile,
        ∃! c : Codon,
          rProfileAt origin c = r ∧
          mProfileAt origin c = m) ∧
      (∀ s m : CodonProfile,
        ∃! c : Codon,
          sProfileAt origin c = s ∧
          mProfileAt origin c = m)

  /-- The homogeneous union contains 22 codons. -/
  homogeneousTwentyTwo :
    ∀ origin : Base,
      (homogeneousUnion origin).card = 22

  /-- The generic complement contains 42 codons. -/
  genericFortyTwo :
    ∀ origin : Base,
      (genericCodons origin).card = 42

  /-- Directed admissible editing obeys the R/M/S trichotomy. -/
  editingProfiles :
    ∀ sites : CodonProfile,
    ∀ c : Codon,
      AdmissibleEditing sites c →
      ∀ i : Fin 3,
        rBit (recodeCodon sites c i) =
            rBit (c i) ∧
        mBit (recodeCodon sites c i) =
            Bool.or (mBit (c i)) (sites i) ∧
        sBit (recodeCodon sites c i) =
            Bool.xor (sBit (c i)) (sites i)

  /-- The pre/post S-profile difference recovers the edit mask. -/
  editMaskRecovery :
    ∀ sites : CodonProfile,
    ∀ c : Codon,
      AdmissibleEditing sites c →
      (fun i =>
        Bool.xor
          (sBit (c i))
          (sBit (recodeCodon sites c i))) =
        sites

  /-- Recoding narrows the zero-M origins exactly to G and U. -/
  narrowedOrigins :
    ∀ origin : Base,
      (∀ b : Base,
        mBitAt origin b = false ↔
          b = G ∨ b = U) ↔
        origin = G ∨ origin = U

  /-- Recoding transports complementation into wobble pairing. -/
  complementToWobble :
    ∀ b : Base,
      recodeBase (tauC b) =
        tauW (recodeBase b)

  /-- U-to-T transport preserves the complete four-state geometry. -/
  rnaDnaTransport :
    Function.Bijective rnaToDNA ∧
    (∀ b : Base,
      rnaToDNA (tauC b) =
        DNABase.tauC (rnaToDNA b)) ∧
    (∀ b : Base,
      rnaToDNA (tauT b) =
        DNABase.tauT (rnaToDNA b)) ∧
    (∀ b : Base,
      rnaToDNA (tauW b) =
        DNABase.tauW (rnaToDNA b))

  /-- Every mismatch lies in exactly one ring-behavior stratum. -/
  errorControlStratification :
    ∀ a b : DNABase,
      IsMismatch a b →
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
      )

  /--
  Directed recoding generates only the coordinate-subspace lattice,
  not the complete Fano incidence geometry.
  -/
  fanoObstruction :
    FanoObstruction.reachedPoints.card = 3 ∧
    FanoObstruction.reachedLines.card = 3 ∧
    FanoObstruction.glMatrices.card = 168 ∧
    FanoObstruction.preservingGL.card = 6 ∧
    FanoObstruction.glMatrices.card -
        FanoObstruction.preservingGL.card = 162

  /-- Position fixes the sign of charge change under A-to-G editing. -/
  positionalCharge :
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
    )

/--
The complete theorem chain presently established in FDBLean.
-/
theorem mainTheoremChain :
    MainTheoremChain where
  nucleotideTorsor :=
    nucleotide_alphabet_is_klein_torsor

  profileXor :=
    relative_profile_xor_law

  codonThreeNet :=
    codon_profiles_pairwise_transverse

  homogeneousTwentyTwo :=
    homogeneousUnion_card

  genericFortyTwo :=
    genericCodons_card

  editingProfiles := by
    intro sites c hAdmissible i
    exact editing_trichotomy
      sites c hAdmissible i

  editMaskRecovery := by
    intro sites c hAdmissible
    exact editing_mask_recovered_by_S
      sites c hAdmissible

  narrowedOrigins :=
    origin_narrowing

  complementToWobble :=
    recodeBase_tauC_eq_tauW_recodeBase

  rnaDnaTransport :=
    rna_dna_geometry_preserved

  errorControlStratification := by
    intro a b hMismatch
    exact formal_error_control_stratification
      a b hMismatch

  fanoObstruction := by
    exact ⟨
      FanoObstruction.reachedPoints_card,
      FanoObstruction.reachedLines_card,
      FanoObstruction.glMatrices_card,
      FanoObstruction.preservingGL_card,
      FanoObstruction.unrealized_collineations
    ⟩

  positionalCharge :=
    positional_charge_law

end FDBLean
