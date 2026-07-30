import FDBLean.Codon

/-!
# FDBLean.ThreeNet

Pairwise transversality of the three codon-profile partitions.

For every origin and every pair of profiles from two distinct classes,
there exists exactly one codon carrying those two profiles.
-/

namespace FDBLean

/--
Recover a base from its absolute `(R,S)` bits.
-/
def baseFromRS : Bool → Bool → Base
  | false, false => .A
  | false, true  => .G
  | true,  false => .U
  | true,  true  => .C

/--
Recover a base from its `(R,S)` bits relative to a chosen origin.
-/
def baseFromRSAt
    (origin : Base)
    (r s : Bool) :
    Base :=
  baseFromRS
    (Bool.xor r (rBit origin))
    (Bool.xor s (sBit origin))

/--
`baseFromRSAt` recovers the requested relative `R` bit.
-/
theorem rBitAt_baseFromRSAt
    (origin : Base)
    (r s : Bool) :
    rBitAt origin (baseFromRSAt origin r s) = r := by
  cases origin <;> cases r <;> cases s <;> rfl

/--
`baseFromRSAt` recovers the requested relative `S` bit.
-/
theorem sBitAt_baseFromRSAt
    (origin : Base)
    (r s : Bool) :
    sBitAt origin (baseFromRSAt origin r s) = s := by
  cases origin <;> cases r <;> cases s <;> rfl

/--
The nucleotide recovered from the relative `(R,S)` profile of a
base is the original base.
-/
theorem baseFromRSAt_profiles
    (origin b : Base) :
    baseFromRSAt origin
      (rBitAt origin b)
      (sBitAt origin b) = b := by
  apply relative_rs_profile_injective origin
  apply Prod.ext
  · exact rBitAt_baseFromRSAt origin
      (rBitAt origin b) (sBitAt origin b)
  · exact sBitAt_baseFromRSAt origin
      (rBitAt origin b) (sBitAt origin b)

/--
Construct a codon from prescribed `R` and `S` profiles.
-/
def codonFromRSAt
    (origin : Base)
    (r s : CodonProfile) :
    Codon :=
  fun i => baseFromRSAt origin (r i) (s i)

/--
The constructed codon has the prescribed `R` profile.
-/
theorem rProfileAt_codonFromRSAt
    (origin : Base)
    (r s : CodonProfile) :
    rProfileAt origin (codonFromRSAt origin r s) = r := by
  funext i
  exact rBitAt_baseFromRSAt origin (r i) (s i)

/--
The constructed codon has the prescribed `S` profile.
-/
theorem sProfileAt_codonFromRSAt
    (origin : Base)
    (r s : CodonProfile) :
    sProfileAt origin (codonFromRSAt origin r s) = s := by
  funext i
  exact sBitAt_baseFromRSAt origin (r i) (s i)

/--
Every `R` fiber meets every `S` fiber in exactly one codon.
-/
theorem rs_fibers_unique_intersection
    (origin : Base)
    (r s : CodonProfile) :
    ∃! c : Codon,
      rProfileAt origin c = r ∧
      sProfileAt origin c = s := by
  refine ⟨codonFromRSAt origin r s, ?_, ?_⟩
  · exact ⟨
      rProfileAt_codonFromRSAt origin r s,
      sProfileAt_codonFromRSAt origin r s
    ⟩
  · intro c hc
    apply rs_codon_profile_injective origin
    apply Prod.ext
    · exact hc.1.trans
        (rProfileAt_codonFromRSAt origin r s).symm
    · exact hc.2.trans
        (sProfileAt_codonFromRSAt origin r s).symm

/--
Pointwise XOR of two codon profiles.
-/
def xorProfile
    (p q : CodonProfile) :
    CodonProfile :=
  fun i => Bool.xor (p i) (q i)

/--
For every origin, the relative `(R,M)` profile uniquely
determines the base.
-/
theorem relative_rm_profile_injective
    (origin : Base) :
    Function.Injective
      (fun b : Base => (rBitAt origin b, mBitAt origin b)) := by
  intro a b h
  cases origin <;> cases a <;> cases b <;>
    simp [rBitAt, mBitAt, rBit, mBit] at h ⊢

/--
For every origin, the relative `(S,M)` profile uniquely
determines the base.
-/
theorem relative_sm_profile_injective
    (origin : Base) :
    Function.Injective
      (fun b : Base => (sBitAt origin b, mBitAt origin b)) := by
  intro a b h
  cases origin <;> cases a <;> cases b <;>
    simp [sBitAt, mBitAt, sBit, mBit] at h ⊢

/--
For a fixed origin, the pair of codon profiles `(R,M)`
uniquely determines the codon.
-/
theorem rm_codon_profile_injective
    (origin : Base) :
    Function.Injective
      (fun c : Codon =>
        (rProfileAt origin c, mProfileAt origin c)) := by
  intro c d h
  funext i
  apply relative_rm_profile_injective origin
  exact congrArg
    (fun p => (p.1 i, p.2 i))
    h

/--
For a fixed origin, the pair of codon profiles `(S,M)`
uniquely determines the codon.
-/
theorem sm_codon_profile_injective
    (origin : Base) :
    Function.Injective
      (fun c : Codon =>
        (sProfileAt origin c, mProfileAt origin c)) := by
  intro c d h
  funext i
  apply relative_sm_profile_injective origin
  exact congrArg
    (fun p => (p.1 i, p.2 i))
    h

/--
Construct a codon from prescribed `R` and `M` profiles.
-/
def codonFromRMAt
    (origin : Base)
    (r m : CodonProfile) :
    Codon :=
  codonFromRSAt origin r (xorProfile r m)

/--
The `R` profile of `codonFromRMAt` is the requested profile.
-/
theorem rProfileAt_codonFromRMAt
    (origin : Base)
    (r m : CodonProfile) :
    rProfileAt origin (codonFromRMAt origin r m) = r := by
  exact rProfileAt_codonFromRSAt origin r (xorProfile r m)

/--
The `M` profile of `codonFromRMAt` is the requested profile.
-/
theorem mProfileAt_codonFromRMAt
    (origin : Base)
    (r m : CodonProfile) :
    mProfileAt origin (codonFromRMAt origin r m) = m := by
  funext i
  have hr :=
    congrFun
      (rProfileAt_codonFromRSAt
        origin r (xorProfile r m))
      i
  have hs :=
    congrFun
      (sProfileAt_codonFromRSAt
        origin r (xorProfile r m))
      i
  rw [mProfileAt_eq_xor]
  change
    Bool.xor
      (rProfileAt origin
        (codonFromRSAt origin r (xorProfile r m)) i)
      (sProfileAt origin
        (codonFromRSAt origin r (xorProfile r m)) i) =
      m i
  rw [hr, hs]
  unfold xorProfile
  cases r i <;> cases m i <;> rfl

/--
Every `R` fiber meets every `M` fiber in exactly one codon.
-/
theorem rm_fibers_unique_intersection
    (origin : Base)
    (r m : CodonProfile) :
    ∃! c : Codon,
      rProfileAt origin c = r ∧
      mProfileAt origin c = m := by
  refine ⟨codonFromRMAt origin r m, ?_, ?_⟩
  · exact ⟨
      rProfileAt_codonFromRMAt origin r m,
      mProfileAt_codonFromRMAt origin r m
    ⟩
  · intro c hc
    apply rm_codon_profile_injective origin
    apply Prod.ext
    · exact hc.1.trans
        (rProfileAt_codonFromRMAt origin r m).symm
    · exact hc.2.trans
        (mProfileAt_codonFromRMAt origin r m).symm

/--
Construct a codon from prescribed `S` and `M` profiles.
-/
def codonFromSMAt
    (origin : Base)
    (s m : CodonProfile) :
    Codon :=
  codonFromRSAt origin (xorProfile s m) s

/--
The `S` profile of `codonFromSMAt` is the requested profile.
-/
theorem sProfileAt_codonFromSMAt
    (origin : Base)
    (s m : CodonProfile) :
    sProfileAt origin (codonFromSMAt origin s m) = s := by
  exact sProfileAt_codonFromRSAt origin (xorProfile s m) s

/--
The `M` profile of `codonFromSMAt` is the requested profile.
-/
theorem mProfileAt_codonFromSMAt
    (origin : Base)
    (s m : CodonProfile) :
    mProfileAt origin (codonFromSMAt origin s m) = m := by
  funext i
  have hr :=
    congrFun
      (rProfileAt_codonFromRSAt
        origin (xorProfile s m) s)
      i
  have hs :=
    congrFun
      (sProfileAt_codonFromRSAt
        origin (xorProfile s m) s)
      i
  rw [mProfileAt_eq_xor]
  change
    Bool.xor
      (rProfileAt origin
        (codonFromRSAt origin (xorProfile s m) s) i)
      (sProfileAt origin
        (codonFromRSAt origin (xorProfile s m) s) i) =
      m i
  rw [hr, hs]
  unfold xorProfile
  cases s i <;> cases m i <;> rfl
/--
Every `S` fiber meets every `M` fiber in exactly one codon.
-/
theorem sm_fibers_unique_intersection
    (origin : Base)
    (s m : CodonProfile) :
    ∃! c : Codon,
      sProfileAt origin c = s ∧
      mProfileAt origin c = m := by
  refine ⟨codonFromSMAt origin s m, ?_, ?_⟩
  · exact ⟨
      sProfileAt_codonFromSMAt origin s m,
      mProfileAt_codonFromSMAt origin s m
    ⟩
  · intro c hc
    apply sm_codon_profile_injective origin
    apply Prod.ext
    · exact hc.1.trans
        (sProfileAt_codonFromSMAt origin s m).symm
    · exact hc.2.trans
        (mProfileAt_codonFromSMAt origin s m).symm
/--
The three profile partitions are pairwise transverse.
-/
theorem codon_profiles_pairwise_transverse
    (origin : Base) :
    (∀ r s : CodonProfile,
      ∃! c : Codon,
        rProfileAt origin c = r ∧
        sProfileAt origin c = s) ∧
    (∀ r m : CodonProfile,
      ∃! c : Codon,
        rProfileAt origin c = r ∧
        mProfileAt origin c = m) ∧
    (∀ s m : CodonProfile,
      ∃! c : Codon,
        sProfileAt origin c = s ∧
        mProfileAt origin c = m) := by
  exact ⟨
    rs_fibers_unique_intersection origin,
    rm_fibers_unique_intersection origin,
    sm_fibers_unique_intersection origin
  ⟩

end FDBLean
