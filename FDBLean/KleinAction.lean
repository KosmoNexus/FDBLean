import FDBLean.Involutions

/-!
# FDBLean.KleinAction

The Klein four-group action on the RNA nucleotide alphabet.

This file gives an explicit four-element group whose three nonidentity
elements act as Watson–Crick complementation, transition substitution,
and wobble pairing. It then proves that the action is simply transitive.

## Kernel cleanliness

No proof in this file may use `native_decide`. That tactic compiles the
decision procedure to native code and trusts the result, placing the Lean
compiler, its runtime, and the C toolchain inside the trusted base, and
leaving a `._native.` entry in `#print axioms`. A theorem carrying such an
axiom does not fail independently of a hand-written proof, which is the sole
reason the manuscript treats this development as a second witness.

Every theorem below must audit to exactly
`[propext, Classical.choice, Quot.sound]`. See `FDBLean.AxiomAudit`.
-/

namespace FDBLean

open Base

/--
The four elements of the Klein group.

* `e` is the identity;
* `c` acts by Watson–Crick complementation;
* `t` acts by transition substitution;
* `w` acts by wobble pairing.
-/
inductive Klein
  | e
  | c
  | t
  | w
  deriving DecidableEq, Repr, Fintype

namespace Klein

/--
Multiplication in the Klein four-group.
-/
def mul : Klein → Klein → Klein
  | e, x => x
  | x, e => x
  | c, c => e
  | t, t => e
  | w, w => e
  | c, t => w
  | t, c => w
  | c, w => t
  | w, c => t
  | t, w => c
  | w, t => c

/--
The Klein group contains four elements.

Proved by definitional reduction of the derived `Fintype` instance.
If the instance does not reduce, replace with `by decide`; both are
kernel-checked. Do not use `native_decide`.
-/
theorem card :
    Fintype.card Klein = 4 := rfl

/--
The identity acts on the left.
-/
theorem e_mul
    (g : Klein) :
    mul e g = g := by
  cases g <;> rfl

/--
The identity acts on the right.
-/
theorem mul_e
    (g : Klein) :
    mul g e = g := by
  cases g <;> rfl

/--
Multiplication is associative.
-/
theorem mul_assoc
    (g h k : Klein) :
    mul (mul g h) k = mul g (mul h k) := by
  cases g <;> cases h <;> cases k <;> rfl

/--
Multiplication is commutative.
-/
theorem mul_comm
    (g h : Klein) :
    mul g h = mul h g := by
  cases g <;> cases h <;> rfl

/--
Every element is its own inverse.
-/
theorem self_inverse
    (g : Klein) :
    mul g g = e := by
  cases g <;> rfl

/--
Left cancellation, obtained from self-inversion and associativity.
Used to derive uniqueness of the transporter without case analysis.
-/
theorem mul_left_cancel
    (g x y : Klein)
    (h : mul g x = mul g y) :
    x = y := by
  have h' := congrArg (mul g) h
  rwa [← mul_assoc, ← mul_assoc, self_inverse, e_mul, e_mul] at h'

/--
The three nonidentity elements are distinct.
-/
theorem c_ne_t : c ≠ t := by decide

theorem c_ne_w : c ≠ w := by decide

theorem t_ne_w : t ≠ w := by decide

/--
Composition of complementation and transition gives wobble.
-/
theorem c_mul_t :
    mul c t = w := by
  rfl

end Klein

/--
The action of the Klein group on the nucleotide alphabet.
-/
def kleinAct : Klein → Base → Base
  | .e, b => b
  | .c, b => tauC b
  | .t, b => tauT b
  | .w, b => tauW b

/--
The identity element acts trivially.
-/
theorem kleinAct_identity
    (b : Base) :
    kleinAct .e b = b := by
  rfl

/--
Group multiplication agrees with composition of actions.
-/
theorem kleinAct_mul
    (g h : Klein)
    (b : Base) :
    kleinAct (Klein.mul g h) b =
      kleinAct g (kleinAct h b) := by
  cases g <;> cases h <;> cases b <;> rfl

/--
The element `c` acts as Watson–Crick complementation.
-/
theorem kleinAct_c :
    kleinAct .c = tauC := by
  rfl

/--
The element `t` acts as transition substitution.
-/
theorem kleinAct_t :
    kleinAct .t = tauT := by
  rfl

/--
The element `w` acts as wobble pairing.
-/
theorem kleinAct_w :
    kleinAct .w = tauW := by
  rfl

/--
The action is free: no nonidentity element fixes a nucleotide.
-/
theorem kleinAct_free
    (g : Klein)
    (b : Base)
    (h : kleinAct g b = b) :
    g = .e := by
  cases g <;> cases b <;>
    simp [kleinAct, tauC, tauT, tauW] at h ⊢

/--
Existence of a transporter: every nucleotide can be carried to every other.

Each of the sixteen cases is discharged by exhibiting the transporter and
reducing. No `Decidable` instance enters the proof term, so the result is
independent of how `DecidableEq Base` happens to be derived.
-/
theorem kleinAct_exists
    (a b : Base) :
    ∃ g : Klein, kleinAct g a = b := by
  cases a <;> cases b <;>
    first
      | exact ⟨.e, rfl⟩
      | exact ⟨.c, rfl⟩
      | exact ⟨.t, rfl⟩
      | exact ⟨.w, rfl⟩

/--
Uniqueness of the transporter, obtained from freeness and the group law
rather than by case analysis.

If two elements carry `a` to `b`, then since every element is its own
inverse, the second carries `b` back to `a`. Their product therefore fixes
`a`, so by freeness the product is the identity, and left cancellation gives
equality.
-/
theorem kleinAct_transporter_unique
    (a b : Base)
    (g₁ g₂ : Klein)
    (h₁ : kleinAct g₁ a = b)
    (h₂ : kleinAct g₂ a = b) :
    g₁ = g₂ := by
  have hback : kleinAct g₂ b = a := by
    rw [← h₂, ← kleinAct_mul, Klein.self_inverse, kleinAct_identity]
  have hfix : kleinAct (Klein.mul g₂ g₁) a = a := by
    rw [kleinAct_mul, h₁, hback]
  have he : Klein.mul g₂ g₁ = .e := kleinAct_free _ _ hfix
  have : Klein.mul g₂ g₁ = Klein.mul g₂ g₂ := by
    rw [he, Klein.self_inverse]
  exact Klein.mul_left_cancel g₂ g₁ g₂ this

/--
For each ordered pair of nucleotides, the transporter exists and is unique.

Fallback if the structural proof above needs adjusting: this goal is
decidable over a `Fintype`, so
`by cases a <;> cases b <;> decide`
also closes it and is likewise kernel-checked. Do not use `native_decide`.
-/
theorem kleinAct_unique
    (a b : Base) :
    ∃! g : Klein, kleinAct g a = b := by
  obtain ⟨g, hg⟩ := kleinAct_exists a b
  refine ⟨g, hg, ?_⟩
  intro y hy
  exact kleinAct_transporter_unique a b y g hy hg

/--
The action is transitive.

Recorded separately because the manuscript states transitivity and freeness
as distinct properties; it is an immediate consequence of `kleinAct_unique`.
-/
theorem kleinAct_transitive
    (a b : Base) :
    ∃ g : Klein, kleinAct g a = b := by
  obtain ⟨g, hg, _⟩ := kleinAct_unique a b
  exact ⟨g, hg⟩

/--
The RNA nucleotide alphabet is a torsor under the Klein four-group.
-/
theorem nucleotide_alphabet_is_klein_torsor :
    ∀ a b : Base, ∃! g : Klein, kleinAct g a = b := by
  intro a b
  exact kleinAct_unique a b

/--
The biochemical composition law is reproduced by the group action:
transition followed by complementation is wobble.
-/
theorem biochemical_composition_from_action
    (b : Base) :
    kleinAct .c (kleinAct .t b) = kleinAct .w b := by
  rw [← kleinAct_mul]
  rfl

end FDBLean
