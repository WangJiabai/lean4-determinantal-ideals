/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Hom.Basic

/-!
# Basic definitions for determinantal ideals

This file defines the coordinate ring of a generic `m × n` matrix, the generic matrix itself,
indexing data for `t × t` minors, the corresponding minors, and the set of all such minors.
-/

namespace Determinantal

/-- The generic `m × n` matrix whose `(i,j)` entry is the variable `X (i,j)`. -/
noncomputable def genericMatrix (m n : ℕ) (k : Type*) [CommSemiring k] :
    Matrix (Fin m) (Fin n) (MvPolynomial (Fin m × Fin n) k) :=
  fun i j => MvPolynomial.X (i, j)

@[simp] lemma genericMatrix_apply {m n : ℕ} (i : Fin m) (j : Fin n)
    (k : Type*) [CommSemiring k] :
    genericMatrix m n k i j = MvPolynomial.X (i, j) := rfl

section CommRing

variable (k : Type*) [CommRing k]

/-- Index data for a `t × t` minor of an `m × n` matrix.

The row and column choices are encoded as order embeddings, so the selected indices are listed
in strictly increasing order. -/
structure MinorIndex (m n t : ℕ) where
  /-- The chosen row indices, in increasing order. -/
  row : Fin t ↪o Fin m
  /-- The chosen column indices, in increasing order. -/
  col : Fin t ↪o Fin n

/-- The `t × t` minor of the generic `m × n` matrix corresponding to `I`. -/
noncomputable def minor {m n t : ℕ} (I : MinorIndex m n t) :
    MvPolynomial (Fin m × Fin n) k :=
  Matrix.det <| Matrix.submatrix (genericMatrix m n k) I.row I.col

/-- The set of all `t × t` minors of the generic `m × n` matrix. -/
def minorSet {m n : ℕ} (t : ℕ) : Set (MvPolynomial (Fin m × Fin n) k) :=
  Set.range (minor (m := m) (n := n) (k := k) (t := t))

@[simp] lemma mem_minorSet_iff {m n t : ℕ} {f : MvPolynomial (Fin m × Fin n) k} :
    f ∈ minorSet k t ↔ ∃ I : MinorIndex m n t, minor k I = f := Iff.rfl

lemma minor_mem_minorSet {m n t : ℕ} (I : MinorIndex m n t) :
    minor k I ∈ minorSet k t :=
  ⟨I, rfl⟩

end CommRing

end Determinantal
