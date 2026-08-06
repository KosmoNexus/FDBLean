import FDBLean.Profiles

/-!
# FDBLean.ForcedAlphabet

The chemical profile tables `rBit`, `sBit`, and `mBit` are
defined independently in `Profiles.lean` from:

* ring class,
* hydrogen-bond class,
* amino/keto pairing-face class.

Likewise, `tauC`, `tauT`, and `tauW` are independently defined
from Watson–Crick complementation, transition substitution, and
wobble pairing.

This module proves the stronger classification result:

* the three chemical profiles have binary rank two;
* the four bases exhaust the four `(R,S)` coordinate states;
* every fixed-point-free involution of the four-base alphabet is
  one of `tauC`, `tauT`, or `tauW`;
* therefore the Klein structure is forced once the four-state
  alphabet and total fixed-point-free pairing relations are given.
-/

namespace FDBLean

open Base

/--
A total map on the nucleotide alphabet is a fixed-point-free
involution when it is self-inverse and moves every base.
-/
def IsFixedPointFreeInvolution (f : Base → Base) : Prop :=
  Function.Involutive f ∧ ∀ b : Base, f b ≠ b

/-!
## The independently defined chemical profile table
-/

/--
The four bases occupy all four possible `(R,S)` binary states.
-/
theorem rs_profile_surjective :
    Function.Surjective
      (fun b : Base => (rBit b, sBit b)) := by
  intro x
  rcases x with ⟨r, s⟩
  cases r <;> cases s
  · exact ⟨A, rfl⟩
  · exact ⟨G, rfl⟩
  · exact ⟨U, rfl⟩
  · exact ⟨C, rfl⟩

/--
The `(R,S)` profile map is a bijection from the four canonical
bases to the four binary coordinate states.
-/
theorem rs_profile_bijective :
    Function.Bijective
      (fun b : Base => (rBit b, sBit b)) := by
  exact ⟨rs_profile_injective, rs_profile_surjective⟩

/--
The canonical base alphabet therefore has exactly two binary
degrees of freedom, while the third profile is their XOR.
-/
theorem chemical_profile_rank_two :
    Function.Bijective
        (fun b : Base => (rBit b, sBit b)) ∧
      (∀ b : Base,
        Bool.xor (rBit b) (sBit b) = mBit b) := by
  exact ⟨rs_profile_bijective, profile_xor_law⟩

/-!
## Each biochemical involution preserves exactly one profile
-/

/--
Watson–Crick complementation preserves exactly the `S` profile
and reverses `R` and `M`.
-/
theorem tauC_preserves_exactly_S
    (b : Base) :
    rBit (tauC b) = !(rBit b) ∧
    sBit (tauC b) = sBit b ∧
    mBit (tauC b) = !(mBit b) := by
  exact ⟨rBit_tauC b, sBit_tauC b, mBit_tauC b⟩

/--
Transition substitution preserves exactly the `R` profile and
reverses `S` and `M`.
-/
theorem tauT_preserves_exactly_R
    (b : Base) :
    rBit (tauT b) = rBit b ∧
    sBit (tauT b) = !(sBit b) ∧
    mBit (tauT b) = !(mBit b) := by
  exact ⟨rBit_tauT b, sBit_tauT b, mBit_tauT b⟩

/--
Wobble pairing preserves exactly the `M` profile and reverses
`R` and `S`.
-/
theorem tauW_preserves_exactly_M
    (b : Base) :
    rBit (tauW b) = !(rBit b) ∧
    sBit (tauW b) = !(sBit b) ∧
    mBit (tauW b) = mBit b := by
  exact ⟨rBit_tauW b, sBit_tauW b, mBit_tauW b⟩

/-!
## Classification of all fixed-point-free involutions
-/

/--
The three named biochemical relations are fixed-point-free
involutions.
-/
theorem named_relations_are_fixed_point_free_involutions :
    IsFixedPointFreeInvolution tauC ∧
    IsFixedPointFreeInvolution tauT ∧
    IsFixedPointFreeInvolution tauW := by
  exact ⟨
    ⟨tauC_involutive, tauC_fixed_point_free⟩,
    ⟨tauT_involutive, tauT_fixed_point_free⟩,
    ⟨tauW_involutive, tauW_fixed_point_free⟩
  ⟩

/--
Every fixed-point-free involution on the four-base alphabet is
one of Watson–Crick complementation, transition substitution, or
wobble pairing.

This is the finite classification theorem that makes the Klein
structure forced rather than merely observed.
-/
theorem fixed_point_free_involution_classification :
    ∀ f : Base → Base,
      IsFixedPointFreeInvolution f →
        f = tauC ∨ f = tauT ∨ f = tauW := by
  intro f hf
  rcases hf with ⟨hinv, hfree⟩

  cases hA : f A with

  -- f A = A contradicts fixed-point freedom.
  | A =>
      exact False.elim (hfree A hA)

  -- f A = C forces A ↔ C and G ↔ U, hence tauW.
  | C =>
      have hC : f C = A := by
        simpa [hA] using hinv A

      cases hG : f G with
      | A =>
          have h := hinv G
          rw [hG, hA] at h
          cases h

      | C =>
          have h := hinv G
          rw [hG, hC] at h
          cases h

      | G =>
          exact False.elim (hfree G hG)

      | U =>
          have hU : f U = G := by
            simpa [hG] using hinv G

          right
          right
          funext b
          cases b <;>
            simp [tauW, hA, hC, hG, hU]

  -- f A = G forces A ↔ G and C ↔ U, hence tauT.
  | G =>
      have hG : f G = A := by
        simpa [hA] using hinv A

      cases hC : f C with
      | A =>
          have h := hinv C
          rw [hC, hA] at h
          cases h

      | C =>
          exact False.elim (hfree C hC)

      | G =>
          have h := hinv C
          rw [hC, hG] at h
          cases h

      | U =>
          have hU : f U = C := by
            simpa [hC] using hinv C

          right
          left
          funext b
          cases b <;>
            simp [tauT, hA, hC, hG, hU]

  -- f A = U forces A ↔ U and C ↔ G, hence tauC.
  | U =>
      have hU : f U = A := by
        simpa [hA] using hinv A

      cases hC : f C with
      | A =>
          have h := hinv C
          rw [hC, hA] at h
          cases h

      | C =>
          exact False.elim (hfree C hC)

      | G =>
          have hG : f G = C := by
            simpa [hC] using hinv C

          left
          funext b
          cases b <;>
            simp [tauC, hA, hC, hG, hU]

      | U =>
          have h := hinv C
          rw [hC, hU] at h
          cases h
/--
There are no further fixed-point-free involutive relations on the
canonical four-base alphabet beyond the three chemically named
ones.
-/
theorem no_fourth_fixed_point_free_involution
    (f : Base → Base)
    (hf : IsFixedPointFreeInvolution f)
    (hfc : f ≠ tauC)
    (hft : f ≠ tauT) :
    f = tauW := by
  rcases fixed_point_free_involution_classification f hf with
    h | h | h
  · exact False.elim (hfc h)
  · exact False.elim (hft h)
  · exact h

/--
The chemically defined relations exhaust all fixed-point-free
involutions, and their composition closes as the Klein four-group.
-/
theorem canonical_alphabet_forces_klein_structure :
    (∀ f : Base → Base,
      IsFixedPointFreeInvolution f →
        f = tauC ∨ f = tauT ∨ f = tauW) ∧
    tauC ∘ tauT = tauW ∧
    tauT ∘ tauC = tauW := by
  exact ⟨
    fixed_point_free_involution_classification,
    tauC_comp_tauT_eq_tauW,
    tauT_comp_tauC_eq_tauW
  ⟩

end FDBLean

#check FDBLean.chemical_profile_rank_two
#check FDBLean.fixed_point_free_involution_classification
#check FDBLean.canonical_alphabet_forces_klein_structure
