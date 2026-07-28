import Mathlib


/-!
# FDBLean.Base

The four-letter RNA nucleotide alphabet used in the first
Formal Deductive Biology development.

This module introduces only the finite alphabet. It makes no
claim about codon assignment, amino acids, or empirical biology.
-/

namespace FDBLean

inductive Base
  | A
  | C
  | G
  | U
  deriving DecidableEq, Repr, Fintype

namespace Base

theorem card_base :
    Fintype.card Base = 4 := by
  decide

theorem exhaustive
    (b : Base) :
    b = A ∨ b = C ∨ b = G ∨ b = U := by
  cases b <;> simp

end Base

end FDBLean

#check FDBLean.Base
#check FDBLean.Base.card_base
