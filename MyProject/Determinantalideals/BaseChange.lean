import Mathlib
import MyProject.Determinantalideals.basic
import MyProject.Determinantalideals.Ideal

namespace Determinantal
section BaseChange

variable {k : Type*} [CommRing k]
variable {S : Type*} [CommRing S]
variable {m n t : ℕ}

lemma genericMatrix_map (f : k →+* S) :
    (genericMatrix (m := m) (n := n) k).map (MvPolynomial.map f)
      = genericMatrix (m := m) (n := n) S := by
  ext i j
  simp [genericMatrix]

lemma map_minor (f : k →+* S) (I : MinorIndex m n t) :
    (MvPolynomial.map f)
        (minor (m := m) (n := n) (k := k) (t := t) I)
      = minor (m := m) (n := n) (k := S) (t := t) I := by
  classical
  unfold minor
  have hdet :
      (MvPolynomial.map f)
          (Matrix.det (Matrix.submatrix (genericMatrix (m := m) (n := n) k) I.row I.col))
        =
      Matrix.det
        ((Matrix.submatrix (genericMatrix (m := m) (n := n) k) I.row I.col).map
        (MvPolynomial.map f)) := by
    simpa using (RingHom.map_det (MvPolynomial.map f)
      (Matrix.submatrix (genericMatrix (m := m) (n := n) k) I.row I.col))
  simpa [Matrix.submatrix_map, ←genericMatrix_map (k := k) (S := S) (m := m) (n := n) f] using hdet


lemma detIdeal_map (f : k →+* S) :
    Ideal.map (MvPolynomial.map f) (detIdeal (m := m) (n := n) (k := k) t)
      = detIdeal (m := m) (n := n) (k := S) t := by
  classical
  let φ : R m n k →+* R m n S := MvPolynomial.map f
  apply le_antisymm
  · refine (Ideal.map_le_iff_le_comap).2 ?_
    change Ideal.span (minorSet (m := m) (n := n) (k := k) t)
      ≤ Ideal.comap φ (Ideal.span (minorSet (m := m) (n := n) (k := S) t))
    refine (Ideal.span_le).2 ?_
    intro x hx
    rcases hx with ⟨I, rfl⟩
    have : φ (minor (m := m) (n := n) (k := k) (t := t) I)
        ∈ Ideal.span (minorSet (m := m) (n := n) (k := S) t) :=
      Ideal.subset_span ⟨I, map_minor f I⟩
    simpa [φ, map_minor (k := k) (S := S) (m := m) (n := n) (t := t) f I] using this
  · change Ideal.span (minorSet (m := m) (n := n) (k := S) t)
      ≤ Ideal.map (MvPolynomial.map f) (Ideal.span (minorSet (m := m) (n := n) (k := k) t))
    refine (Ideal.span_le).2 ?_
    intro x hx
    rcases hx with ⟨I, rfl⟩
    have hx0 :
        minor (m := m) (n := n) (k := k) (t := t) I
          ∈ detIdeal (m := m) (n := n) (k := k) t :=
      minor_mem_detIdeal (m := m) (n := n) (k := k) (t := t) I
    have : (MvPolynomial.map f)
        (minor (m := m) (n := n) (k := k) (t := t) I)
        ∈ Ideal.map (MvPolynomial.map f) (detIdeal (m := m) (n := n) (k := k) t) :=
      Ideal.mem_map_of_mem (MvPolynomial.map f) hx0
    simpa [map_minor (k := k) (S := S) (m := m) (n := n) (t := t) f I] using this

end BaseChange
end Determinantal
