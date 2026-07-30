import FDBLean.Profiles

/-!
# FDBLean.Codon

The 64-element RNA codon space and its three coordinatewise profiles.

A codon is a function from the three codon positions to the nucleotide
alphabet. A codon profile is a three-bit vector.
-/

namespace FDBLean

/--
A codon is an ordered triple of RNA bases.
-/
abbrev Codon := Fin 3 → Base

/--
A codon profile is a three-bit vector.
-/
abbrev CodonProfile := Fin 3 → Bool

/--
The codon space contains exactly 64 elements.
-/
theorem card_codon :
    Fintype.card Codon = 64 := by
  decide

/--
The profile space contains exactly eight elements.
-/
theorem card_codonProfile :
    Fintype.card CodonProfile = 8 := by
  decide

/-!
## Codon profiles relative to an origin
-/

/--
The coordinatewise `R` profile of a codon.
-/
def rProfileAt
    (origin : Base)
    (c : Codon) :
    CodonProfile :=
  fun i => rBitAt origin (c i)

/--
The coordinatewise `S` profile of a codon.
-/
def sProfileAt
    (origin : Base)
    (c : Codon) :
    CodonProfile :=
  fun i => sBitAt origin (c i)

/--
The coordinatewise `M` profile of a codon.
-/
def mProfileAt
    (origin : Base)
    (c : Codon) :
    CodonProfile :=
  fun i => mBitAt origin (c i)

/--
The codon consisting entirely of the chosen origin.
-/
def originCodon
    (origin : Base) :
    Codon :=
  fun _ => origin

/--
The `R` profile of the origin codon is the zero profile.
-/
theorem rProfileAt_originCodon
    (origin : Base) :
    rProfileAt origin (originCodon origin) =
      fun _ => false := by
  funext i
  exact rBitAt_origin origin

/--
The `S` profile of the origin codon is the zero profile.
-/
theorem sProfileAt_originCodon
    (origin : Base) :
    sProfileAt origin (originCodon origin) =
      fun _ => false := by
  funext i
  exact sBitAt_origin origin

/--
The `M` profile of the origin codon is the zero profile.
-/
theorem mProfileAt_originCodon
    (origin : Base) :
    mProfileAt origin (originCodon origin) =
      fun _ => false := by
  funext i
  exact mBitAt_origin origin

/-!
## Pointwise XOR law
-/

/--
The codon profiles satisfy the XOR law at every position.
-/
theorem codon_profile_xor_law
    (origin : Base)
    (c : Codon) :
    ∀ i : Fin 3,
      Bool.xor
        (rProfileAt origin c i)
        (sProfileAt origin c i) =
      mProfileAt origin c i := by
  intro i
  exact relative_profile_xor_law origin (c i)

/--
The codon-level `M` profile is the pointwise XOR of the
`R` and `S` profiles.
-/
theorem mProfileAt_eq_xor
    (origin : Base)
    (c : Codon) :
    mProfileAt origin c =
      fun i =>
        Bool.xor
          (rProfileAt origin c i)
          (sProfileAt origin c i) := by
  funext i
  exact (codon_profile_xor_law origin c i).symm

/-!
## Any two profiles determine the codon
-/

/--
For a fixed origin, the pair of codon profiles `(R,S)`
uniquely determines the codon.
-/
theorem rs_codon_profile_injective
    (origin : Base) :
    Function.Injective
      (fun c : Codon =>
        (rProfileAt origin c, sProfileAt origin c)) := by
  intro c d h
  funext i
  apply relative_rs_profile_injective origin
  exact congrArg
    (fun p => (p.1 i, p.2 i))
    h

/-!
## Coordinatewise biochemical actions
-/

/--
Apply Watson--Crick complementation at every codon position.
-/
def tauCCodon
    (c : Codon) :
    Codon :=
  fun i => tauC (c i)

/--
Apply transition substitution at every codon position.
-/
def tauTCodon
    (c : Codon) :
    Codon :=
  fun i => tauT (c i)

/--
Apply wobble pairing at every codon position.
-/
def tauWCodon
    (c : Codon) :
    Codon :=
  fun i => tauW (c i)

/--
Coordinatewise Watson--Crick complementation is involutive.
-/
theorem tauCCodon_involutive :
    Function.Involutive tauCCodon := by
  intro c
  funext i
  exact tauC_involutive (c i)

/--
Coordinatewise transition substitution is involutive.
-/
theorem tauTCodon_involutive :
    Function.Involutive tauTCodon := by
  intro c
  funext i
  exact tauT_involutive (c i)

/--
Coordinatewise wobble pairing is involutive.
-/
theorem tauWCodon_involutive :
    Function.Involutive tauWCodon := by
  intro c
  funext i
  exact tauW_involutive (c i)

/--
Coordinatewise complementation followed by transition equals
coordinatewise wobble.
-/
theorem tauCCodon_comp_tauTCodon :
    tauCCodon ∘ tauTCodon = tauWCodon := by
  funext c i
  exact congrFun tauC_comp_tauT_eq_tauW (c i)

end FDBLean
