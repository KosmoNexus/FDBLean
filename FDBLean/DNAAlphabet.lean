import FDBLean.ComplementToWobble

/-!
# FDBLean.DNAAlphabet

The four-base DNA alphabet and its induced Klein structure.

RNA and DNA differ only in the pyrimidine base `U` versus `T`.
This module defines the DNA alphabet directly and records the three
corresponding involutions:

* Watson--Crick complementation;
* transition substitution;
* wobble-analogue pairing.

The module remains purely formal. It does not claim that every RNA
relation has the same biochemical admissibility in DNA.
-/

namespace FDBLean

/--
The four DNA bases.
-/
inductive DNABase
  | A
  | C
  | G
  | T
  deriving DecidableEq, Repr, Fintype

namespace DNABase

/--
Watson--Crick complementation on DNA.
-/
def tauC : DNABase → DNABase
  | A => T
  | T => A
  | C => G
  | G => C

/--
Transition substitution on DNA.
-/
def tauT : DNABase → DNABase
  | A => G
  | G => A
  | C => T
  | T => C

/--
The third fixed-point-free involution on the DNA alphabet.
-/
def tauW : DNABase → DNABase
  | A => C
  | C => A
  | G => T
  | T => G

/--
DNA Watson--Crick complementation is involutive.
-/
theorem tauC_involutive :
    Function.Involutive tauC := by
  intro b
  cases b <;> rfl

/--
DNA transition substitution is involutive.
-/
theorem tauT_involutive :
    Function.Involutive tauT := by
  intro b
  cases b <;> rfl

/--
The third DNA involution is involutive.
-/
theorem tauW_involutive :
    Function.Involutive tauW := by
  intro b
  cases b <;> rfl

/--
DNA complementation and transition commute.
-/
theorem tauC_tauT_commute
    (b : DNABase) :
    tauC (tauT b) = tauT (tauC b) := by
  cases b <;> rfl

/--
DNA complementation followed by transition equals the third
involution.
-/
theorem tauC_comp_tauT_eq_tauW :
    tauC ∘ tauT = tauW := by
  funext b
  cases b <;> rfl

/--
DNA transition followed by complementation equals the third
involution.
-/
theorem tauT_comp_tauC_eq_tauW :
    tauT ∘ tauC = tauW := by
  funext b
  cases b <;> rfl

/--
The DNA alphabet has four elements.
-/
theorem card :
    Fintype.card DNABase = 4 := by
  decide

end DNABase

end FDBLean
