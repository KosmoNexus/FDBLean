import FDBLean.Recoding

/-!
# FDBLean.EditingTrichotomy

The formal profile behavior of admissible directed RNA deamination.

At each edited codon position:

* the `R` profile is invariant;
* the `M` profile changes from `false` to `true`;
* the `S` profile flips.

Thus the edit mask is recovered exactly from the pre/post `S`
profile difference.
-/

namespace FDBLean

open Base

/-!
## Base-level profile behavior
-/

/--
Directed recoding preserves the `R` profile.
-/
theorem rBit_recodeBase
    (b : Base) :
    rBit (recodeBase b) = rBit b := by
  cases b <;> rfl

/--
Directed recoding changes the `S` profile exactly when the source
nucleotide is editable, namely `A` or `C`.
-/
theorem sBit_recodeBase_ne_iff
    (b : Base) :
    sBit (recodeBase b) ≠ sBit b ↔
      EditingSource b := by
  cases b <;> simp [EditingSource, recodeBase, sBit]

/--
Directed recoding sends every editable source into the `true`
class of the `M` profile.
-/
theorem mBit_recodeBase_source_true
    (b : Base)
    (hSource : EditingSource b) :
    mBit (recodeBase b) = true := by
  rcases hSource with hA | hC
  · simp [hA, recodeBase, mBit]
  · simp [hC, recodeBase, mBit]

/--
The `M` profile never changes from `true` to `false`.
-/
theorem mBit_recodeBase_monotone
    (b : Base) :
    mBit b = true →
    mBit (recodeBase b) = true := by
  cases b <;> simp [mBit, recodeBase]

/--
After recoding, the `M` profile is always `true`.
-/
theorem mBit_recodeBase_true
    (b : Base) :
    mBit (recodeBase b) = true := by
  cases b <;> rfl

/-!
## Codon-level editing trichotomy
-/

/--
Recoding preserves the `R` profile at every codon position.
-/
theorem editing_preserves_R
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3) :
    rBit (recodeCodon sites c i) =
      rBit (c i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      simp only [recodeCodon, hSite, if_true]
      exact rBit_recodeBase (c i)

/--
Under admissible editing, the post-edit `M` profile is the Boolean
disjunction of the original `M` profile and the edit-site bit.
-/
theorem editing_M_exact
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3) :
    mBit (recodeCodon sites c i) =
      Bool.or (mBit (c i)) (sites i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      have hSource : EditingSource (c i) :=
        hAdmissible i hSite
      rw [recodeCodon_at_selected sites c i hSite]
      rw [mBit_recodeBase_source_true (c i) hSource]
      simp

/--
Admissible editing is monotone in the `M` profile.
-/
theorem editing_M_monotone
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3) :
    mBit (c i) = true →
    mBit (recodeCodon sites c i) = true := by
  intro hM
  rw [editing_M_exact sites c hAdmissible i]
  simp [hM]

/--
Under admissible editing, the post-edit `S` profile is the XOR of
the original `S` profile with the edit-site bit.
-/
theorem editing_S_exact
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3) :
    sBit (recodeCodon sites c i) =
      Bool.xor (sBit (c i)) (sites i) := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      have hSource : EditingSource (c i) :=
        hAdmissible i hSite
      rw [recodeCodon_at_selected sites c i hSite]
      rcases hSource with hA | hC
      · simp [hA, recodeBase, sBit]
      · simp [hC, recodeBase, sBit]

/--
The `S` profile changes exactly at the admissibly edited positions.
-/
theorem editing_S_changes_iff
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3) :
    sBit (recodeCodon sites c i) ≠ sBit (c i) ↔
      sites i = true := by
  cases hSite : sites i with
  | false =>
      simp [recodeCodon, hSite]
  | true =>
      have hSource : EditingSource (c i) :=
        hAdmissible i hSite
      rw [recodeCodon_at_selected sites c i hSite]
      rcases hSource with hA | hC
      · simp [hA, recodeBase, sBit]
      · simp [hC, recodeBase, sBit]

/--
The edit mask is recovered exactly as the coordinatewise XOR
difference between the pre-edit and post-edit `S` profiles.
-/
theorem editing_mask_recovered_by_S
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c) :
    (fun i =>
      Bool.xor
        (sBit (c i))
        (sBit (recodeCodon sites c i))) =
      sites := by
  funext i
  rw [editing_S_exact sites c hAdmissible i]
  cases hSource : sBit (c i) <;>
    cases hSite : sites i <;>
    rfl

/--
The complete editing trichotomy at one codon position.
-/
theorem editing_trichotomy
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3) :
    rBit (recodeCodon sites c i) = rBit (c i) ∧
    mBit (recodeCodon sites c i) =
      Bool.or (mBit (c i)) (sites i) ∧
    sBit (recodeCodon sites c i) =
      Bool.xor (sBit (c i)) (sites i) := by
  exact ⟨
    editing_preserves_R sites c i,
    editing_M_exact sites c hAdmissible i,
    editing_S_exact sites c hAdmissible i
  ⟩

end FDBLean
