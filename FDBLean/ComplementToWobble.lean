import FDBLean.OriginNarrowing

/-!
# FDBLean.ComplementToWobble

Directed deamination transports Watson--Crick complementation on the
four-base RNA alphabet to wobble pairing on the absorbing alphabet
`{G,U}`.

At base level:

`recodeBase (tauC b) = tauW (recodeBase b)`.

The same transport law holds coordinatewise on codons after full
recoding.
-/

namespace FDBLean

open Base

/-!
## Base-level transport
-/

/--
Recoding transports Watson--Crick complementation into wobble pairing.
-/
theorem recodeBase_tauC_eq_tauW_recodeBase
    (b : Base) :
    recodeBase (tauC b) =
      tauW (recodeBase b) := by
  cases b <;> rfl

/--
Functional form of the complement-to-wobble transport law.
-/
theorem recodeBase_comp_tauC :
    recodeBase ∘ tauC =
      tauW ∘ recodeBase := by
  funext b
  exact recodeBase_tauC_eq_tauW_recodeBase b

/--
After recoding, both sides of a Watson--Crick complementary pair lie
in the absorbing alphabet.
-/
theorem recoded_complement_pair_absorbing
    (b : Base) :
    AbsorbingBase (recodeBase b) ∧
      AbsorbingBase (recodeBase (tauC b)) := by
  constructor
  · exact recodeBase_idempotent b
  · exact recodeBase_idempotent (tauC b)

/--
The recoded complement of a base is the wobble partner of its recoded
image.
-/
theorem recoded_complement_is_wobble_partner
    (b : Base) :
    tauW (recodeBase b) =
      recodeBase (tauC b) := by
  exact (recodeBase_tauC_eq_tauW_recodeBase b).symm

/-!
## Codon-level transport
-/

/--
Full recoding of a codon.
-/
def fullyRecodeCodon
    (c : Codon) :
    Codon :=
  recodeCodon (fun _ => true) c

/--
Full codon recoding is coordinatewise base recoding.
-/
theorem fullyRecodeCodon_apply
    (c : Codon)
    (i : Fin 3) :
    fullyRecodeCodon c i =
      recodeBase (c i) := by
  simp [fullyRecodeCodon, recodeCodon]

/--
Full recoding transports coordinatewise Watson--Crick
complementation into coordinatewise wobble pairing.
-/
theorem fullyRecodeCodon_tauC
    (c : Codon) :
    fullyRecodeCodon (tauCCodon c) =
      tauWCodon (fullyRecodeCodon c) := by
  funext i
  simp only [
    fullyRecodeCodon_apply,
    tauCCodon,
    tauWCodon
  ]
  exact recodeBase_tauC_eq_tauW_recodeBase (c i)

/--
Functional form of the codon-level transport law.
-/
theorem fullyRecodeCodon_comp_tauCCodon :
    fullyRecodeCodon ∘ tauCCodon =
      tauWCodon ∘ fullyRecodeCodon := by
  funext c
  exact fullyRecodeCodon_tauC c

/--
Every fully recoded codon lies in the absorbing codon set.
-/
theorem fullyRecodeCodon_absorbing
    (c : Codon) :
    AbsorbingCodon (fullyRecodeCodon c) := by
  exact full_recode_is_absorbing c

/--
On fully recoded codons, complementation inherited from the original
alphabet appears exactly as wobble pairing.
-/
theorem complement_becomes_wobble
    (c : Codon) :
    fullyRecodeCodon (tauCCodon c) =
      tauWCodon (fullyRecodeCodon c) := by
  exact fullyRecodeCodon_tauC c

end FDBLean
