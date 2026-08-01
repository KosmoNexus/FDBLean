import FDBLean.EditingTrichotomy

/-!
# FDBLean.OriginNarrowing

Repeated directed RNA deamination narrows the alphabet to the
absorbing product bases `{G,U}`.

At codon scale, the absorbing set is therefore `{G,U}³`. This is
exactly the zero `M`-profile fiber when the chosen origin is `G`
or `U`, but not when the origin is `A` or `C`.

The two admissible origins are exchanged by wobble pairing.
-/

namespace FDBLean

open Base

/-!
## Absorbing bases
-/

/--
A base is absorbing under recoding when recoding leaves it fixed.
-/
def AbsorbingBase (b : Base) : Prop :=
  recodeBase b = b

/--
The absorbing bases are exactly `G` and `U`.
-/
theorem absorbingBase_iff
    (b : Base) :
    AbsorbingBase b ↔ b = G ∨ b = U := by
  exact recodeBase_eq_self_iff b

/--
`G` is absorbing.
-/
theorem absorbingBase_G :
    AbsorbingBase G := by
  rfl

/--
`U` is absorbing.
-/
theorem absorbingBase_U :
    AbsorbingBase U := by
  rfl

/--
`A` is not absorbing.
-/
theorem not_absorbingBase_A :
    ¬ AbsorbingBase A := by
  simp [AbsorbingBase, recodeBase]

/--
`C` is not absorbing.
-/
theorem not_absorbingBase_C :
    ¬ AbsorbingBase C := by
  simp [AbsorbingBase, recodeBase]



/--
A codon is absorbing when every coordinate is an absorbing base.
-/
def AbsorbingCodon (c : Codon) : Prop :=
  ∀ i : Fin 3, AbsorbingBase (c i)

/--
A codon is absorbing exactly when every coordinate is `G` or `U`.
-/
theorem absorbingCodon_iff
    (c : Codon) :
    AbsorbingCodon c ↔
      ∀ i : Fin 3, c i = G ∨ c i = U := by
  constructor
  · intro h i
    exact (absorbingBase_iff (c i)).1 (h i)
  · intro h i
    exact (absorbingBase_iff (c i)).2 (h i)

/--
Applying recoding at every codon position always produces an
absorbing codon.
-/
theorem full_recode_is_absorbing
    (c : Codon) :
    AbsorbingCodon
      (recodeCodon (fun _ => true) c) := by
  intro i
  rw [absorbingBase_iff]
  simp [recodeCodon, recodeBase_eq_G_or_U]

/--
A codon is absorbing exactly when full recoding leaves it unchanged.
-/
theorem absorbingCodon_iff_full_recode_fixed
    (c : Codon) :
    AbsorbingCodon c ↔
      recodeCodon (fun _ => true) c = c := by
  constructor
  · intro h
    funext i
    simp [recodeCodon]
    exact h i
  · intro h i
    have hi :
        recodeCodon (fun _ => true) c i = c i :=
      congrFun h i
    show recodeBase (c i) = c i
    simpa [recodeCodon] using hi

/-!
## Origin narrowing by the `M` profile
-/

/--
For origin `G`, the zero `M`-profile class is exactly `{G,U}`.
-/
theorem mBitAt_G_zero_iff
    (b : Base) :
    mBitAt G b = false ↔ b = G ∨ b = U := by
  cases b <;> decide

/--
For origin `U`, the zero `M`-profile class is exactly `{G,U}`.
-/
theorem mBitAt_U_zero_iff
    (b : Base) :
    mBitAt U b = false ↔ b = G ∨ b = U := by
  cases b <;> decide

/--
For origin `G`, a codon has zero `M` profile exactly when it is
absorbing.
-/
theorem mProfileAt_G_zero_iff_absorbing
    (c : Codon) :
    mProfileAt G c = (fun _ => false) ↔
      AbsorbingCodon c := by
  constructor
  · intro h i
    have hi :
        mBitAt G (c i) = false :=
      congrFun h i
    exact
      (absorbingBase_iff (c i)).2
        ((mBitAt_G_zero_iff (c i)).1 hi)
  · intro h
    funext i
    exact
      (mBitAt_G_zero_iff (c i)).2
        ((absorbingBase_iff (c i)).1 (h i))

/--
For origin `U`, a codon has zero `M` profile exactly when it is
absorbing.
-/
theorem mProfileAt_U_zero_iff_absorbing
    (c : Codon) :
    mProfileAt U c = (fun _ => false) ↔
      AbsorbingCodon c := by
  constructor
  · intro h i
    have hi :
        mBitAt U (c i) = false :=
      congrFun h i
    exact
      (absorbingBase_iff (c i)).2
        ((mBitAt_U_zero_iff (c i)).1 hi)
  · intro h
    funext i
    exact
      (mBitAt_U_zero_iff (c i)).2
        ((absorbingBase_iff (c i)).1 (h i))

/--
The absorbing base set is the zero `M`-profile class exactly for
origins `G` and `U`.
-/
theorem origin_narrowing
    (origin : Base) :
    (∀ b : Base,
      mBitAt origin b = false ↔
        b = G ∨ b = U) ↔
      origin = G ∨ origin = U := by
  cases origin <;> decide

/-!
## Wobble exchange of the two surviving origins
-/

/--
Wobble pairing exchanges `G` with `U`.
-/
theorem tauW_G_eq_U :
    tauW G = U := by
  rfl

/--
Wobble pairing exchanges `U` with `G`.
-/
theorem tauW_U_eq_G :
    tauW U = G := by
  rfl

/--
The two origins selected by recoding are exactly the wobble pair
`G ↔ U`.
-/
theorem narrowed_origins_form_wobble_pair :
    tauW G = U ∧ tauW U = G := by
  exact ⟨tauW_G_eq_U, tauW_U_eq_G⟩

end FDBLean
