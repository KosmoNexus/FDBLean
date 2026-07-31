import FDBLean.Recoding

/-!
# FDBLean.EditingTrichotomy

The formal profile behavior of admissible directed `A → G` recoding.

At each codon position:

* the `R` profile is invariant;
* the `M` profile changes monotonically from `false` to `true`
  exactly when editing occurs;
* the `S` profile flips exactly at the edited positions.

Thus the `S`-profile difference recovers the edit mask exactly.
-/

namespace FDBLean

open Base

/-!
## Base-level profile behavior
-/

/--
Directed `A → G` recoding preserves the `R` profile.
-/
theorem rBit_recodeBase
    (b : Base) :
    rBit (recodeBase b) = rBit b := by
  cases b <;> rfl

/--
The `S` profile changes under base recoding exactly when the
source nucleotide is `A`.
-/
theorem sBit_recodeBase_ne_iff
    (b : Base) :
    sBit (recodeBase b) ≠ sBit b ↔ b = A := by
  cases b <;> decide

/--
Base recoding cannot change the `M` profile from `true` to `false`.
-/
theorem mBit_recodeBase_monotone
    (b : Base) :
    mBit b = true →
    mBit (recodeBase b) = true := by
  cases b <;> simp [mBit, recodeBase]

/--
The `M` profile after recoding is the Boolean disjunction of its
original value with the proposition that the source was `A`.
-/
theorem mBit_recodeBase_eq_or
    (b : Base) :
    mBit (recodeBase b) =
      Bool.or (mBit b) (decide (b = A)) := by
  cases b <;> rfl

/-!
## Codon-level editing trichotomy
-/

/--
Admissible recoding preserves the `R` profile at every codon
position.
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
      have hA : c i = A :=
        hAdmissible i hSite
      simp [recodeCodon, hSite, hA, recodeBase, mBit]

/--
Admissible editing is monotone in the `M` profile: an `M` bit that
is already true remains true.
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
      have hA : c i = A :=
        hAdmissible i hSite
      simp [recodeCodon, hSite, hA, recodeBase, sBit]

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
      have hA : c i = A :=
        hAdmissible i hSite
      simp [recodeCodon, hSite, hA, recodeBase, sBit]

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
