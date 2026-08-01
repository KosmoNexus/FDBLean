import FDBLean.HomogeneousSplit

/-!
# FDBLean.Recoding

Directed RNA deamination recoding on the four-base alphabet.

At the sequence level, the two effective substitutions are:

* `A → G`, representing adenosine-to-inosine editing;
* `C → U`, representing cytidine-to-uridine editing.

The product bases `G` and `U` are fixed. Thus recoding is directional,
idempotent, and has absorbing base set `{G,U}`.

A codon-level recoding operation is controlled by a three-bit site
profile. Biological admissibility is recorded separately: every
selected site must initially contain either `A` or `C`.
-/

namespace FDBLean

open Base

/-!
## Base-level recoding
-/

/--
A nucleotide is an admissible source for directed deamination exactly
when it is `A` or `C`.
-/
def EditingSource (b : Base) : Prop :=
  b = A ∨ b = C



/--
Directed RNA deamination at one nucleotide:

* `A → G`;
* `C → U`;
* `G → G`;
* `U → U`.
-/
def recodeBase : Base → Base
  | A => G
  | C => U
  | G => G
  | U => U

@[simp]
theorem recodeBase_A :
    recodeBase A = G := by
  rfl

@[simp]
theorem recodeBase_C :
    recodeBase C = U := by
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
Recoding is idempotent.
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
Recoding never produces `C`.
-/
theorem recodeBase_ne_C
    (b : Base) :
    recodeBase b ≠ C := by
  cases b <;> decide

/--
A nucleotide changes under recoding exactly when it is an admissible
source: `A` or `C`.
-/
theorem recodeBase_ne_iff
    (b : Base) :
    recodeBase b ≠ b ↔ EditingSource b := by
  cases b <;> simp [EditingSource, recodeBase]
/--
A nucleotide is fixed by recoding exactly when it is `G` or `U`.
-/
theorem recodeBase_eq_self_iff
    (b : Base) :
    recodeBase b = b ↔ b = G ∨ b = U := by
  cases b <;> decide

/--
Every recoding output lies in the absorbing base set `{G,U}`.
-/
theorem recodeBase_eq_G_or_U
    (b : Base) :
    recodeBase b = G ∨ recodeBase b = U := by
  cases b <;> simp [recodeBase]

/-!
## Codon-level recoding
-/

/--
Apply directed recoding at the codon positions selected by `sites`.

A true bit selects a position for recoding. A false bit leaves that
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
selected position initially contains either `A` or `C`.
-/
def AdmissibleEditing
    (sites : CodonProfile)
    (c : Codon) :
    Prop :=
  ∀ i : Fin 3,
    sites i = true →
    EditingSource (c i)

/--
At every selected admissible position, recoding produces either `G`
or `U`.
-/
theorem admissible_recode_selected_eq_G_or_U
    (sites : CodonProfile)
    (c : Codon)

    (i : Fin 3)
    (hSelected : sites i = true) :
    recodeCodon sites c i = G ∨
      recodeCodon sites c i = U := by
  rw [recodeCodon_at_selected sites c i hSelected]
  exact recodeBase_eq_G_or_U (c i)

/--
An admissibly selected `A` position becomes `G`.
-/
theorem admissible_recode_selected_A_eq_G
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3)
    (hSelected : sites i = true)
    (hA : c i = A) :
    recodeCodon sites c i = G := by
  rw [recodeCodon_at_selected sites c i hSelected]
  simp [hA]

/--
An admissibly selected `C` position becomes `U`.
-/
theorem admissible_recode_selected_C_eq_U
    (sites : CodonProfile)
    (c : Codon)
    (i : Fin 3)
    (hSelected : sites i = true)
    (hC : c i = C) :
    recodeCodon sites c i = U := by
  rw [recodeCodon_at_selected sites c i hSelected]
  simp [hC]

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
  rw [recodeCodon_at_selected sites c i hSelected]
  exact
    (recodeBase_ne_iff (c i)).2
      (hAdmissible i hSelected)

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
