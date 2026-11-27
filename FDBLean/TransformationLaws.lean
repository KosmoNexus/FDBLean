import FDBLean.OriginNarrowing

/-!
# FDBLean.TransformationLaws

The transformation laws of the three codon profiles under recoding,
stated at every origin, together with the polarity of the `M` law.

`EditingTrichotomy` states the `M` law with the `M` bit anchored at
origin `A`, where it reads as a join (`editing_M_exact`), and recovers
the edit mask from the `S` profile only. Origin `A` is one of the two
origins that `OriginNarrowing` excludes. This module states the laws in
the forms the manuscript uses:

* the polarity-free form, valid at every origin under admissible
  editing: post-edit `M` = pre-edit `M` XOR edit mask;
* the meet form at the admissible origins `G` and `U`:
  post-edit `M` = pre-edit `M` AND NOT edit mask;
* the join form at the excluded origins `A` and `C`:
  post-edit `M` = pre-edit `M` OR edit mask;
* exact recovery of the edit mask from the `M` profile, at every origin.

The `R` and `S` laws are restated at every origin, so that the three
laws and both recoveries are available in one place and in one
convention.

The meet and join forms hold for every site mask, admissible or not,
because recoding is total and fixes `G` and `U`. The XOR form and the
recoveries require admissibility.

Trust rules: no `sorry`, no `native_decide`.
-/

namespace FDBLean

open Base

/-!
## Base-level facts
-/

/--
An editable source lies in the `false` class of the `A`-anchored `M` bit.
-/
theorem mBit_source_false
    (b : Base)
    (hSource : EditingSource b) :
    mBit b = false := by
  rcases hSource with rfl | rfl <;> rfl

/--
At every origin, recoding preserves the relative `R` bit.
-/
theorem rBitAt_recodeBase
    (origin b : Base) :
    rBitAt origin (recodeBase b) = rBitAt origin b := by
  cases origin <;> cases b <;> rfl

/--
At every origin, recoding an editable source flips the relative `S` bit.
-/
theorem sBitAt_recodeBase_source
    (origin b : Base)
    (hSource : EditingSource b) :
    sBitAt origin (recodeBase b) = !(sBitAt origin b) := by
  rcases hSource with rfl | rfl <;> cases origin <;> rfl

/--
At every origin, recoding an editable source flips the relative `M` bit.
-/
theorem mBitAt_recodeBase_source
    (origin b : Base)
    (hSource : EditingSource b) :
    mBitAt origin (recodeBase b) = !(mBitAt origin b) := by
  rcases hSource with rfl | rfl <;> cases origin <;> rfl

/--
At origin `G`, every recoding output has relative `M` bit `false`.
-/
theorem mBitAt_G_recodeBase
    (b : Base) :
    mBitAt G (recodeBase b) = false := by
  cases b <;> rfl

/--
At origin `U`, every recoding output has relative `M` bit `false`.
-/
theorem mBitAt_U_recodeBase
    (b : Base) :
    mBitAt U (recodeBase b) = false := by
  cases b <;> rfl

/--
At origin `A`, every recoding output has relative `M` bit `true`.
-/
theorem mBitAt_A_recodeBase
    (b : Base) :
    mBitAt A (recodeBase b) = true := by
  cases b <;> rfl

/--
At origin `C`, every recoding output has relative `M` bit `true`.
-/
theorem mBitAt_C_recodeBase
    (b : Base) :
    mBitAt C (recodeBase b) = true := by
  cases b <;> rfl

/--
At origin `G`, an editable source has relative `M` bit `true`.
-/
theorem mBitAt_G_source_true
    (b : Base)
    (hSource : EditingSource b) :
    mBitAt G b = true := by
  rcases hSource with rfl | rfl <;> rfl

/--
At origin `U`, an editable source has relative `M` bit `true`.
-/
theorem mBitAt_U_source_true
    (b : Base)
    (hSource : EditingSource b) :
    mBitAt U b = true := by
  rcases hSource with rfl | rfl <;> rfl

/-!
## The `R` and `S` laws at every origin
-/

/--
Recoding preserves the relative `R` profile at every codon position,
at every origin, for every site mask.
-/
theorem editing_preserves_R_at
    (origin : Base)
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3) :
    rBitAt origin (recodeCodon sites c i) =
      rBitAt origin (c i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      rw [recodeCodon_at_selected sites c i hSite]
      exact rBitAt_recodeBase origin (c i)

/--
Under admissible editing, the relative `S` profile is translated by
the edit mask, at every origin.
-/
theorem editing_S_xor_at
    (origin : Base)
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3) :
    sBitAt origin (recodeCodon sites c i) =
      Bool.xor (sBitAt origin (c i)) (sites i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      have hSource : EditingSource (c i) :=
        hAdmissible i hSite
      rw [recodeCodon_at_selected sites c i hSite]
      rw [sBitAt_recodeBase_source origin (c i) hSource]
      cases hBit : sBitAt origin (c i) <;> rfl

/-!
## The `M` law: polarity-free form
-/

/--
Under admissible editing, the `A`-anchored `M` bit is translated by
the edit mask.
-/
theorem editing_M_xor
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3) :
    mBit (recodeCodon sites c i) =
      Bool.xor (mBit (c i)) (sites i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      have hSource : EditingSource (c i) :=
        hAdmissible i hSite
      rw [recodeCodon_at_selected sites c i hSite]
      rcases hSource with hA | hC
      · simp [hA, recodeBase, mBit]
      · simp [hC, recodeBase, mBit]

/--
Under admissible editing, the relative `M` profile is translated by
the edit mask, at every origin. This is the polarity-free form of the
`M` law.
-/
theorem editing_M_xor_at
    (origin : Base)
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3) :
    mBitAt origin (recodeCodon sites c i) =
      Bool.xor (mBitAt origin (c i)) (sites i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      have hSource : EditingSource (c i) :=
        hAdmissible i hSite
      rw [recodeCodon_at_selected sites c i hSite]
      rw [mBitAt_recodeBase_source origin (c i) hSource]
      cases hBit : mBitAt origin (c i) <;> rfl

/-!
## The `M` law: meet form at the admissible origins
-/

/--
At origin `G`, the post-edit `M` bit is the meet of the pre-edit `M`
bit with the complement of the edit mask. No admissibility hypothesis
is needed.
-/
theorem editing_M_meet_at_G
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3) :
    mBitAt G (recodeCodon sites c i) =
      Bool.and (mBitAt G (c i)) (!(sites i)) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      rw [recodeCodon_at_selected sites c i hSite]
      rw [mBitAt_G_recodeBase (c i)]
      cases hBit : mBitAt G (c i) <;> rfl

/--
At origin `U`, the post-edit `M` bit is the meet of the pre-edit `M`
bit with the complement of the edit mask.
-/
theorem editing_M_meet_at_U
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3) :
    mBitAt U (recodeCodon sites c i) =
      Bool.and (mBitAt U (c i)) (!(sites i)) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      rw [recodeCodon_at_selected sites c i hSite]
      rw [mBitAt_U_recodeBase (c i)]
      cases hBit : mBitAt U (c i) <;> rfl

/--
The meet form of the `M` law at either admissible origin.
-/
theorem editing_M_meet_at_admissible
    (origin : Base)
    (hOrigin : origin = G ∨ origin = U)
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3) :
    mBitAt origin (recodeCodon sites c i) =
      Bool.and (mBitAt origin (c i)) (!(sites i)) := by
  rcases hOrigin with rfl | rfl
  · exact editing_M_meet_at_G sites c i
  · exact editing_M_meet_at_U sites c i

/--
At the admissible origin `G`, under admissible editing, the support of
the edit mask lies inside the support of the pre-edit `M` profile.
-/
theorem edit_support_subset_M_support_at_G
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3)
    (hSite : sites i = true) :
    mBitAt G (c i) = true :=
  mBitAt_G_source_true (c i) (hAdmissible i hSite)

/--
At the admissible origin `U`, under admissible editing, the support of
the edit mask lies inside the support of the pre-edit `M` profile.
-/
theorem edit_support_subset_M_support_at_U
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3)
    (hSite : sites i = true) :
    mBitAt U (c i) = true :=
  mBitAt_U_source_true (c i) (hAdmissible i hSite)

/-!
## The `M` law: join form at the excluded origins
-/

/--
At origin `A`, the post-edit `M` bit is the join of the pre-edit `M`
bit with the edit mask.
-/
theorem editing_M_join_at_A
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3) :
    mBitAt A (recodeCodon sites c i) =
      Bool.or (mBitAt A (c i)) (sites i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      rw [recodeCodon_at_selected sites c i hSite]
      rw [mBitAt_A_recodeBase (c i)]
      cases hBit : mBitAt A (c i) <;> rfl

/--
At origin `C`, the post-edit `M` bit is the join of the pre-edit `M`
bit with the edit mask.
-/
theorem editing_M_join_at_C
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3) :
    mBitAt C (recodeCodon sites c i) =
      Bool.or (mBitAt C (c i)) (sites i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      rw [recodeCodon_at_selected sites c i hSite]
      rw [mBitAt_C_recodeBase (c i)]
      cases hBit : mBitAt C (c i) <;> rfl

/--
The join form of the `M` law at either excluded origin.
-/
theorem editing_M_join_at_excluded
    (origin : Base)
    (hOrigin : origin = A ∨ origin = C)
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3) :
    mBitAt origin (recodeCodon sites c i) =
      Bool.or (mBitAt origin (c i)) (sites i) := by
  rcases hOrigin with rfl | rfl
  · exact editing_M_join_at_A sites c i
  · exact editing_M_join_at_C sites c i

/-!
## The two polarities are not interchangeable

Editing one adenosine already separates them: the meet form is false
at origin `A` and the join form is false at origin `G`.
-/

/--
The meet form fails at the excluded origin `A`.
-/
theorem M_meet_form_fails_at_A :
    mBitAt A (recodeBase A) ≠
      Bool.and (mBitAt A A) (!true) := by
  decide

/--
The join form fails at the admissible origin `G`.
-/
theorem M_join_form_fails_at_G :
    mBitAt G (recodeBase A) ≠
      Bool.or (mBitAt G A) true := by
  decide

/-!
## Exact recovery of the edit mask
-/

/--
The edit mask is recovered exactly as the XOR difference of the
`A`-anchored `M` profile before and after admissible editing.
-/
theorem editing_mask_recovered_by_M
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c) :
    (fun i =>
      Bool.xor
        (mBit (c i))
        (mBit (recodeCodon sites c i))) =
      sites := by
  funext i
  rw [editing_M_xor sites c hAdmissible i]
  cases hBit : mBit (c i) <;>
    cases hSite : sites i <;>
    rfl

/--
At every origin, the edit mask is recovered exactly as the XOR
difference of the relative `M` profile before and after admissible
editing.
-/
theorem editing_mask_recovered_by_M_at
    (origin : Base)
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c) :
    (fun i =>
      Bool.xor
        (mBitAt origin (c i))
        (mBitAt origin (recodeCodon sites c i))) =
      sites := by
  funext i
  rw [editing_M_xor_at origin sites c hAdmissible i]
  cases hBit : mBitAt origin (c i) <;>
    cases hSite : sites i <;>
    rfl

/--
At every origin, the edit mask is recovered exactly as the XOR
difference of the relative `S` profile before and after admissible
editing.
-/
theorem editing_mask_recovered_by_S_at
    (origin : Base)
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c) :
    (fun i =>
      Bool.xor
        (sBitAt origin (c i))
        (sBitAt origin (recodeCodon sites c i))) =
      sites := by
  funext i
  rw [editing_S_xor_at origin sites c hAdmissible i]
  cases hBit : sBitAt origin (c i) <;>
    cases hSite : sites i <;>
    rfl

/-!
## Profile-level statements
-/

/--
The three transformation laws at profile level, at every origin:
`R` is invariant, and `M` and `S` are each translated by the edit
mask.
-/
theorem transformation_laws_at
    (origin : Base)
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c) :
    rProfileAt origin (recodeCodon sites c) =
        rProfileAt origin c ∧
    mProfileAt origin (recodeCodon sites c) =
        (fun i => Bool.xor (mProfileAt origin c i) (sites i)) ∧
    sProfileAt origin (recodeCodon sites c) =
        (fun i => Bool.xor (sProfileAt origin c i) (sites i)) := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    exact editing_preserves_R_at origin sites c i
  · funext i
    exact editing_M_xor_at origin sites c hAdmissible i
  · funext i
    exact editing_S_xor_at origin sites c hAdmissible i

/--
Exact recovery of the edit mask at profile level, at every origin,
from either the `M` profile or the `S` profile.
-/
theorem edit_mask_recovered_at
    (origin : Base)
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c) :
    (fun i =>
      Bool.xor
        (mProfileAt origin c i)
        (mProfileAt origin (recodeCodon sites c) i)) = sites ∧
    (fun i =>
      Bool.xor
        (sProfileAt origin c i)
        (sProfileAt origin (recodeCodon sites c) i)) = sites :=
  ⟨editing_mask_recovered_by_M_at origin sites c hAdmissible,
   editing_mask_recovered_by_S_at origin sites c hAdmissible⟩

/--
The meet form at profile level, at either admissible origin.
-/
theorem mProfileAt_meet_at_admissible
    (origin : Base)
    (hOrigin : origin = G ∨ origin = U)
    (sites : CodonProfile)
    (c : Codon) :
    mProfileAt origin (recodeCodon sites c) =
      (fun i => Bool.and (mProfileAt origin c i) (!(sites i))) := by
  funext i
  exact editing_M_meet_at_admissible origin hOrigin sites c i

/-!
## Terminus of the monotone descent
-/

/--
At origin `G`, full recoding sends every codon to the zero `M`
profile. The monotone descent terminates on the absorbing set.
-/
theorem full_recode_mProfileAt_G_zero
    (c : Codon) :
    mProfileAt G (recodeCodon (fun _ => true) c) =
      (fun _ => false) :=
  (mProfileAt_G_zero_iff_absorbing
      (recodeCodon (fun _ => true) c)).2
    (full_recode_is_absorbing c)

/--
At origin `U`, full recoding sends every codon to the zero `M`
profile.
-/
theorem full_recode_mProfileAt_U_zero
    (c : Codon) :
    mProfileAt U (recodeCodon (fun _ => true) c) =
      (fun _ => false) :=
  (mProfileAt_U_zero_iff_absorbing
      (recodeCodon (fun _ => true) c)).2
    (full_recode_is_absorbing c)

end FDBLean

-- Axiom footprint of the headline statements. Each line must report at most
-- `propext`, `Classical.choice` and `Quot.sound`. Move these lines into
-- `AxiomAudit.lean` when that module is extended to the whole development.
#print axioms FDBLean.transformation_laws_at
#print axioms FDBLean.edit_mask_recovered_at
#print axioms FDBLean.mProfileAt_meet_at_admissible
#print axioms FDBLean.editing_M_join_at_excluded
#print axioms FDBLean.full_recode_mProfileAt_G_zero
#print axioms FDBLean.full_recode_mProfileAt_U_zero
