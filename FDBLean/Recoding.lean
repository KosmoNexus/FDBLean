import FDBLean.HomogeneousSplit

/-!
# FDBLean.Recoding

Directed adenosine-to-inosine recoding, represented at the RNA
sequence level as the substitution `A → G`.

The operation is deliberately directional:

* `A` is replaced by `G`;
* `C`, `G`, and `U` are unchanged.

A codon-level recoding operation is controlled by a three-bit site
profile. Biological admissibility is recorded separately: a selected
site is admissible only when the source nucleotide is `A`.
-/

namespace FDBLean

open Base

/-!
## Base-level recoding
-/

/--
Directed RNA recoding at one nucleotide.

At the sequence level, adenosine-to-inosine editing is represented
by the effective substitution `A → G`.
-/
def recodeBase : Base → Base
  | A => G
  | C => C
  | G => G
  | U => U

@[simp]
theorem recodeBase_A :
    recodeBase A = G := by
  rfl

@[simp]
theorem recodeBase_C :
    recodeBase C = C := by
  rfl

@[simp]
theorem recodeBase_G :
    recodeBase G = G := by
  rfl

@[simp]
theorem recodeBase_U :
    recodeBase U = U := by
  rfl

/--
Recoding is idempotent: once `A` has been replaced by `G`,
a second application makes no further change.
-/
theorem recodeBase_idempotent
    (b : Base) :
    recodeBase (recodeBase b) = recodeBase b := by
  cases b <;> rfl

/--
Recoding never produces `A`.
-/
theorem recodeBase_ne_A
    (b : Base) :
    recodeBase b ≠ A := by
  cases b <;> decide

/--
A nucleotide changes under recoding exactly when it is `A`.
-/
theorem recodeBase_ne_iff
    (b : Base) :
    recodeBase b ≠ b ↔ b = A := by
  cases b <;> decide

/--
A nucleotide is fixed by recoding exactly when it is not `A`.
-/
theorem recodeBase_eq_self_iff
    (b : Base) :
    recodeBase b = b ↔ b ≠ A := by
  cases b <;> decide

/-!
## Codon-level recoding
-/

/--
Apply directed recoding at the codon positions selected by `sites`.

A true bit selects a position for recoding. A false bit leaves the
position unchanged.
-/
def recodeCodon
    (sites : CodonProfile)
    (c : Codon) :
    Codon :=
  fun i =>
    if sites i = true then
      recodeBase (c i)
    else
      c i

/--
A selected codon position is recoded.
-/
theorem recodeCodon_at_selected
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3)
    (h : sites i = true) :
    recodeCodon sites c i = recodeBase (c i) := by
  simp [recodeCodon, h]

/--
An unselected codon position is unchanged.
-/
theorem recodeCodon_at_unselected
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3)
    (h : sites i = false) :
    recodeCodon sites c i = c i := by
  simp [recodeCodon, h]

/--
A site profile is biologically admissible for a codon when every
selected position contains `A` before recoding.
-/
def AdmissibleEditing
    (sites : CodonProfile)
    (c : Codon) :
    Prop :=
  ∀ i : Fin 3,
    sites i = true →
    c i = A

/--
At every selected admissible position, recoding produces `G`.
-/
theorem admissible_recode_selected_eq_G
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3)
    (hSelected : sites i = true) :
    recodeCodon sites c i = G := by
  rw [recodeCodon_at_selected sites c i hSelected]
  rw [hAdmissible i hSelected]
  rfl

/--
At an admissibly selected position, the nucleotide necessarily
changes.
-/
theorem admissible_recode_selected_ne
    (sites : CodonProfile)
    (c : Codon)
    (hAdmissible : AdmissibleEditing sites c)
    (i : Fin 3)
    (hSelected : sites i = true) :
    recodeCodon sites c i ≠ c i := by
  rw [admissible_recode_selected_eq_G sites c hAdmissible i hSelected]
  rw [hAdmissible i hSelected]
  decide

/--
Applying the same recoding mask twice has the same effect as applying
it once.
-/
theorem recodeCodon_idempotent
    (sites : CodonProfile)
    (c : Codon) :
    recodeCodon sites (recodeCodon sites c) =
      recodeCodon sites c := by
  funext i
  cases h : sites i with
  | false =>
      simp [recodeCodon, h]
  | true =>
      simp only [recodeCodon, h, if_true]
      exact recodeBase_idempotent (c i)
/--
The all-false site profile performs no editing.
-/
theorem recodeCodon_zero
    (c : Codon) :
    recodeCodon (fun _ => false) c = c := by
  funext i
  simp [recodeCodon]

end FDBLean
