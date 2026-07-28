import FDBLean.Base

/-!
# FDBLean.Involutions

The three biochemical relations on the RNA nucleotide alphabet:

* Watson–Crick complementation
* transition substitution
* wobble pairing

Each relation is represented as a total map on the four-base alphabet.
-/

namespace FDBLean

open Base

/--
Watson–Crick complementation:
A ↔ U and G ↔ C.
-/
def tauC : Base → Base
  | A => U
  | U => A
  | G => C
  | C => G

/--
Transition substitution:
A ↔ G and C ↔ U.
-/
def tauT : Base → Base
  | A => G
  | G => A
  | C => U
  | U => C

/--
Wobble pairing:
G ↔ U and A ↔ C.
-/
def tauW : Base → Base
  | G => U
  | U => G
  | A => C
  | C => A

theorem tauC_involutive :
    Function.Involutive tauC := by
  intro b
  cases b <;> rfl

theorem tauT_involutive :
    Function.Involutive tauT := by
  intro b
  cases b <;> rfl

theorem tauW_involutive :
    Function.Involutive tauW := by
  intro b
  cases b <;> rfl

theorem tauC_fixed_point_free :
    ∀ b : Base, tauC b ≠ b := by
  intro b
  cases b <;> decide

theorem tauT_fixed_point_free :
    ∀ b : Base, tauT b ≠ b := by
  intro b
  cases b <;> decide

theorem tauW_fixed_point_free :
    ∀ b : Base, tauW b ≠ b := by
  intro b
  cases b <;> decide

theorem tauC_tauT_commute :
    Function.Commute tauC tauT := by
  intro b
  cases b <;> rfl

theorem tauC_comp_tauT_eq_tauW :
    tauC ∘ tauT = tauW := by
  funext b
  cases b <;> rfl

theorem tauT_comp_tauC_eq_tauW :
    tauT ∘ tauC = tauW := by
  funext b
  cases b <;> rfl

end FDBLean
