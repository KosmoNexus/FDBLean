/-
  FDBLean / FanoObstruction.lean

  PURPOSE. Establish a negative result: directed recoding does not
  generate the complete incidence structure of PG(2,2) on the
  three-position edit-profile space.

  Recoding generates exactly the coordinate-subspace lattice of F₂³.
  It therefore reaches only three of the seven projective points and
  three of the seven projective lines. Of the 168 elements of
  GL(3,F₂), exactly six preserve this edit-reachable family.

  We call this the edit-reachability obstruction.

  This result does not rule out arbitrary bijections between
  seven-element sets. It rules out the stronger claim that the
  recoding dynamics naturally realizes the complete Fano plane or
  its full collineation symmetry.

  PRE-REGISTERED VALUES:

      reached.card                         = 8
      reachedPoints.card                   = 3
      reachedLines.card                    = 3
      glMatrices.card                      = 168
      permutationMatrices.card             = 6
      preservingGL.card                    = 6
      glMatrices.card - preservingGL.card  = 162

  If any value differs, the discrepancy is retained as the result.

  TRUST RULES. No `sorry`. No `native_decide`. No compiler-trust
  axioms. Ordinary `decide` is permitted because its proof term is
  checked by the Lean kernel.
-/

import FDBLean.Recoding

namespace FDBLean.FanoObstruction

open FDBLean

/-!
## Concrete representation of F₂³

Concrete structures are used instead of function types so that
decidable equality is transparent enough for kernel reduction.
-/

/-- A vector in `F₂³`. -/
structure Vec where
  x0 : Bool
  x1 : Bool
  x2 : Bool
  deriving DecidableEq, Repr, Fintype

namespace Vec

/-- Read a coordinate of a vector. -/
def get
    (v : Vec) :
    Fin 3 → Bool :=
  Fin.cases v.x0
    (Fin.cases v.x1
      (fun _ => v.x2))

@[simp]
theorem get_zero
    (v : Vec) :
    v.get 0 = v.x0 := by
  rfl

@[simp]
theorem get_one
    (v : Vec) :
    v.get 1 = v.x1 := by
  rfl

@[simp]
theorem get_two
    (v : Vec) :
    v.get 2 = v.x2 := by
  rfl

end Vec

/-- Addition in `F₂³`. -/
def vadd
    (u v : Vec) :
    Vec where
  x0 := Bool.xor u.x0 v.x0
  x1 := Bool.xor u.x1 v.x1
  x2 := Bool.xor u.x2 v.x2

/-- The zero vector. -/
def vzero : Vec where
  x0 := false
  x1 := false
  x2 := false
/-- First standard basis vector of `F₂³`. -/
def e0 : Vec where
  x0 := true
  x1 := false
  x2 := false

/-- Second standard basis vector of `F₂³`. -/
def e1 : Vec where
  x0 := false
  x1 := true
  x2 := false

/-- Third standard basis vector of `F₂³`. -/
def e2 : Vec where
  x0 := false
  x1 := false
  x2 := true

/--
First diagonal point of the coordinate projective frame:
`e0 + e1 = 110`.
-/
def diagonal01 : Vec :=
  vadd e0 e1

/--
Second diagonal point of the coordinate projective frame:
`e0 + e2 = 101`.
-/
def diagonal02 : Vec :=
  vadd e0 e2

/--
Third diagonal point of the coordinate projective frame:
`e1 + e2 = 011`.
-/
def diagonal12 : Vec :=
  vadd e1 e2

/--
The diagonal line of the selected projective frame.

Its nonzero vectors are `110`, `101`, and `011`.
-/
def frameDiagonal : Finset Vec :=
  {vzero, diagonal01, diagonal02, diagonal12}

/-- A concrete finite subset of `F₂³`. -/
abbrev Sub := Finset Vec

/--
A subset is a subspace when it contains zero and is closed under
addition.
-/
def isSubspace
    (S : Sub) :
    Prop :=
  vzero ∈ S ∧
  ∀ u ∈ S,
  ∀ v ∈ S,
    vadd u v ∈ S

instance isSubspaceDecidable
    (S : Sub) :
    Decidable (isSubspace S) := by
  unfold isSubspace
  infer_instance

/-- All subspaces of `F₂³`. -/
def allSubspaces :
    Finset Sub :=
  (Finset.univ : Finset Vec).powerset.filter isSubspace

/--
Subspaces of dimension `d`, recognized by cardinality `2^d`.
-/
def subsOfDim
    (d : Nat) :
    Finset Sub :=
  allSubspaces.filter
    (fun S => S.card = 2 ^ d)

/-- `PG(2,2)` has seven projective points. -/
theorem points_card :
    (subsOfDim 1).card = 7 := by
  decide

/-- `PG(2,2)` has seven projective lines. -/
theorem lines_card :
    (subsOfDim 2).card = 7 := by
  decide
/-!
## The diagonal line of the coordinate frame
-/

/--
The three diagonal points sum to zero in characteristic two.
Equivalently, any two sum to the third.
-/
theorem diagonal_points_sum_zero :
    vadd diagonal01
      (vadd diagonal02 diagonal12) =
        vzero := by
  rfl

/--
The frame diagonal is closed under Boolean-vector addition.
-/
theorem frameDiagonal_isSubspace :
    isSubspace frameDiagonal := by
  decide

/--
The frame diagonal has four vectors.
-/
theorem frameDiagonal_card :
    frameDiagonal.card = 4 := by
  decide

/--
The frame diagonal is one of the seven projective lines of
`PG(2,2)`.
-/
theorem frameDiagonal_isLine :
    frameDiagonal ∈ subsOfDim 2 := by
  decide

/-!
## Coordinate subspaces and edit reachability
-/

/--
Boolean form of the editable-source predicate.

`A` and `C` are editable; `G` and `U` are products.
-/
def editableBool : Base → Bool
  | Base.A => true
  | Base.C => true
  | Base.G => false
  | Base.U => false

/--
The Boolean predicate agrees with `EditingSource`.
-/
theorem editableBool_eq_true_iff
    (b : Base) :
    editableBool b = true ↔ EditingSource b := by
  cases b <;> simp [editableBool, EditingSource]

/--
The coordinate subspace supported on `I`.
-/
def coordinateSubspace
    (I : Finset (Fin 3)) :
    Sub :=
  (Finset.univ : Finset Vec).filter
    (fun v =>
      ∀ i : Fin 3,
        v.get i = true →
        i ∈ I)

/--
Every coordinate subspace is a linear subspace.
-/
theorem coordinateSubspace_isSubspace
    (I : Finset (Fin 3)) :
    isSubspace (coordinateSubspace I) := by
  decide +revert

/-- The editable coordinates of a codon. -/
def editableSupport
    (c : Codon) :
    Finset (Fin 3) :=
  Finset.univ.filter
    (fun i => editableBool (c i) = true)

/--
The edit masks reachable from a codon.
-/
def reachable
    (c : Codon) :
    Sub :=
  coordinateSubspace (editableSupport c)

/--
Every edit-reachable set is a subspace.
-/
theorem reachable_isSubspace
    (c : Codon) :
    isSubspace (reachable c) := by
  exact coordinateSubspace_isSubspace
    (editableSupport c)

/--
Construct a codon with precisely the prescribed editable support.
-/
def codonForSupport
    (I : Finset (Fin 3)) :
    Codon :=
  fun i =>
    if i ∈ I then Base.A else Base.G

/--
The constructed codon has the prescribed editable support.
-/
theorem editableSupport_codonForSupport
    (I : Finset (Fin 3)) :
    editableSupport (codonForSupport I) = I := by
  ext i
  by_cases hi : i ∈ I
  · simp [
      editableSupport,
      codonForSupport,
      editableBool,
      hi
    ]
  · simp [
      editableSupport,
      codonForSupport,
      editableBool,
      hi
    ]

/-- The family of all coordinate subspaces. -/
def coordinateSubspaces :
    Finset Sub :=
  (Finset.univ : Finset (Finset (Fin 3))).image
    coordinateSubspace

/--
The subspaces generated by editing across all codons.
-/
def reached :
    Finset Sub :=
  (Finset.univ : Finset Codon).image reachable

/--
Editing generates exactly the coordinate-subspace lattice.
-/
theorem reached_eq_coordinateSubspaces :
    reached = coordinateSubspaces := by
  apply Finset.ext
  intro S
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with
      ⟨c, _, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨editableSupport c, Finset.mem_univ _, rfl⟩
  · intro hS
    rcases Finset.mem_image.mp hS with
      ⟨I, _, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨codonForSupport I, Finset.mem_univ _, ?_⟩
    unfold reachable
    rw [editableSupport_codonForSupport]

/--
The edit-reachable lattice has eight subspaces.
-/
theorem reached_card :
    reached.card = 8 := by
  set_option maxHeartbeats 2000000 in
    decide

/-- The reachable one-dimensional subspaces. -/
def reachedPoints :
    Finset Sub :=
  reached.filter
    (fun S => S.card = 2)

/-- The reachable two-dimensional subspaces. -/
def reachedLines :
    Finset Sub :=
  reached.filter
    (fun S => S.card = 4)

/--
Exactly three projective points are edit reachable.
-/
theorem reachedPoints_card :
    reachedPoints.card = 3 := by
  set_option maxHeartbeats 2000000 in
    decide

/--
Exactly three projective lines are edit reachable.
-/
theorem reachedLines_card :
    reachedLines.card = 3 := by
  set_option maxHeartbeats 2000000 in
    decide

/-!
## The edit-reachability obstruction
-/

/-- Erase one coordinate of a vector. -/
def eraseCoordinate
    (i : Fin 3)
    (v : Vec) :
    Vec where
  x0 := if i = 0 then false else v.x0
  x1 := if i = 1 then false else v.x1
  x2 := if i = 2 then false else v.x2

/--
A subspace is coordinate when erasing any coordinate preserves
membership.
-/
def isCoordinate
    (S : Sub) :
    Prop :=
  ∀ v ∈ S,
  ∀ i : Fin 3,
    eraseCoordinate i v ∈ S

instance isCoordinateDecidable
    (S : Sub) :
    Decidable (isCoordinate S) := by
  unfold isCoordinate
  infer_instance

/--
Every coordinate subspace satisfies coordinate-erasure closure.
-/
theorem coordinateSubspace_isCoordinate
    (I : Finset (Fin 3)) :
    isCoordinate (coordinateSubspace I) := by
  decide +revert

/--
Every edit-reachable subspace is coordinate.
-/
theorem reached_all_coordinate :
    ∀ S ∈ reached,
      isCoordinate S := by
  intro S hS
  rw [reached_eq_coordinateSubspaces] at hS
  rcases Finset.mem_image.mp hS with
    ⟨I, _, rfl⟩
  exact coordinateSubspace_isCoordinate I

/--
Four of the seven projective lines are never generated.
-/
theorem lines_missed :
    ((subsOfDim 2) \ reachedLines).card = 4 := by
  set_option maxHeartbeats 2000000 in
    decide
/--
The diagonal line is not a coordinate subspace.

For example, it contains `110`, but erasing either of its nonzero
coordinates produces a standard basis vector, which the diagonal
line does not contain.
-/
theorem frameDiagonal_not_coordinate :
    ¬ isCoordinate frameDiagonal := by
  decide

/--
The edit dynamics cannot generate the diagonal line of the selected
projective frame.
-/
theorem frameDiagonal_not_reached :
    frameDiagonal ∉ reached := by
  intro h
  have hCoordinate :
      isCoordinate frameDiagonal :=
    reached_all_coordinate frameDiagonal h
  exact frameDiagonal_not_coordinate hCoordinate

/--
In particular, the frame diagonal is not among the reachable
projective lines.
-/
theorem frameDiagonal_not_reachedLine :
    frameDiagonal ∉ reachedLines := by
  intro h
  exact frameDiagonal_not_reached
    (Finset.mem_filter.mp h).1

/--
The frame diagonal is one of the four projective lines missed by
the recoding dynamics.
-/
theorem frameDiagonal_mem_missedLines :
    frameDiagonal ∈
      ((subsOfDim 2) \ reachedLines) := by
  exact Finset.mem_sdiff.mpr
    ⟨frameDiagonal_isLine, frameDiagonal_not_reachedLine⟩

/-!
## Concrete Boolean matrices
-/

/--
A `3 × 3` Boolean matrix, represented by its three column vectors.
-/
structure Matrix3 where
  c0 : Vec
  c1 : Vec
  c2 : Vec
  deriving DecidableEq, Repr, Fintype

namespace Matrix3

/-- Read a matrix column. -/
def column
    (M : Matrix3) :
    Fin 3 → Vec :=
  Fin.cases M.c0
    (Fin.cases M.c1
      (fun _ => M.c2))

end Matrix3

/-- The standard coordinate vector `eᵢ`. -/
def e
    (i : Fin 3) :
    Vec where
  x0 := decide (i = 0)
  x1 := decide (i = 1)
  x2 := decide (i = 2)

/--
One output coordinate of a Boolean-linear map.
-/
def linearCoordinate
    (M : Matrix3)
    (v : Vec)
    (j : Fin 3) :
    Bool :=
  Bool.xor
    (v.x0 && (M.column 0).get j)
    (Bool.xor
      (v.x1 && (M.column 1).get j)
      (v.x2 && (M.column 2).get j))

/--
Apply a Boolean matrix to a vector.
-/
def applyLin
    (M : Matrix3)
    (v : Vec) :
    Vec where
  x0 := linearCoordinate M v 0
  x1 := linearCoordinate M v 1
  x2 := linearCoordinate M v 2

/--
A matrix is invertible when its image has all eight vectors.
-/
def isInvertible
    (M : Matrix3) :
    Prop :=
  ((Finset.univ : Finset Vec).image
    (applyLin M)).card = 8

instance isInvertibleDecidable
    (M : Matrix3) :
    Decidable (isInvertible M) := by
  unfold isInvertible
  infer_instance

/--
The invertible Boolean matrices.
-/
def glMatrices :
    Finset Matrix3 :=
  (Finset.univ : Finset Matrix3).filter isInvertible

/--
`GL(3,F₂)` contains 168 matrices.
-/
theorem glMatrices_card :
    glMatrices.card = 168 := by
  set_option maxHeartbeats 5000000 in
  set_option maxRecDepth 100000 in
    decide

/-!
## Coordinate permutations
-/

/--
The matrix induced by a permutation of the coordinate axes.
-/
def permutationMatrix
    (σ : Equiv.Perm (Fin 3)) :
    Matrix3 where
  c0 := e (σ 0)
  c1 := e (σ 1)
  c2 := e (σ 2)

/-- The coordinate-permutation matrices. -/
def permutationMatrices :
    Finset Matrix3 :=
  (Finset.univ : Finset (Equiv.Perm (Fin 3))).image
    permutationMatrix

/--
There are six coordinate-permutation matrices.
-/
theorem permutationMatrices_card :
    permutationMatrices.card = 6 := by
  decide

/--
The invertible matrices preserving every edit-reachable subspace.
-/
def preservingGL :
    Finset Matrix3 :=
  glMatrices.filter
    (fun M =>
      ∀ S ∈ reached,
        S.image (applyLin M) ∈ reached)

/--
Exactly six invertible matrices preserve edit reachability.
-/
theorem preservingGL_card :
    preservingGL.card = 6 := by
  set_option maxHeartbeats 10000000 in
  set_option maxRecDepth 100000 in
    decide

/--
The remaining 162 collineations do not preserve the biological
reachability structure.
-/
theorem unrealized_collineations :
    glMatrices.card - preservingGL.card = 162 := by
  rw [glMatrices_card, preservingGL_card]

/--
The complete edit-reachability obstruction.
-/
theorem fano_obstruction_summary :
    (subsOfDim 1).card = 7 ∧
    (subsOfDim 2).card = 7 ∧
    reached.card = 8 ∧
    reachedPoints.card = 3 ∧
    reachedLines.card = 3 ∧
    ((subsOfDim 2) \ reachedLines).card = 4 ∧
    glMatrices.card = 168 ∧
    preservingGL.card = 6 ∧
    glMatrices.card - preservingGL.card = 162 := by
  exact ⟨
    points_card,
    lines_card,
    reached_card,
    reachedPoints_card,
    reachedLines_card,
    lines_missed,
    glMatrices_card,
    preservingGL_card,
    unrealized_collineations
  ⟩

end FDBLean.FanoObstruction
