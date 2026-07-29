import FDBLean.Involutions

/-!
# FDBLean.KleinAction

The Klein four-group action on the RNA nucleotide alphabet.

This file gives an explicit four-element group whose three nonidentity
elements act as Watson–Crick complementation, transition substitution,
and wobble pairing. It then proves that the action is simply transitive.
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
-/
theorem card :
    Fintype.card Klein = 4 := by
  native_decide

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
The action is transitive: every nucleotide can be carried to
every other nucleotide.
-/
theorem kleinAct_transitive
    (a b : Base) :
    ∃ g : Klein, kleinAct g a = b := by
  cases a <;> cases b <;> native_decide

/--
For each ordered pair of nucleotides, the transporter is unique.
-/
theorem kleinAct_unique
    (a b : Base) :
    ∃! g : Klein, kleinAct g a = b := by
  cases a <;> cases b
  · refine ⟨.e, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.w, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.t, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.c, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢

  · refine ⟨.w, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.e, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.c, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.t, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢

  · refine ⟨.t, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.c, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.e, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.w, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢

  · refine ⟨.c, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.t, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.w, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢
  · refine ⟨.e, rfl, ?_⟩
    intro g hg
    cases g <;> simp [kleinAct, tauC, tauT, tauW] at hg ⊢

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
