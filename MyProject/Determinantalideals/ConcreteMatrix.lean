import Mathlib
import MyProject.Determinantalideals.Eval

namespace Determinantal


section ConcreteMatrix

variable {S T : Type*} [CommRing S] [CommRing T]
variable {m n t : ℕ}

/-- `matrixMinor` 在环同态下自然：`f (minor(A)) = minor(A.map f)`。 -/
lemma matrixMinor_map (f : S →+* T) (A : Matrix (Fin m) (Fin n) S) (I : MinorIndex m n t) :
    f (matrixMinor (m := m) (n := n) (t := t) A I)
      = matrixMinor (m := m) (n := n) (t := t) (A.map f) I := by
  classical
  unfold matrixMinor
  simpa [Matrix.submatrix_map] using
    (RingHom.map_det f (Matrix.submatrix A I.row I.col))

end ConcreteMatrix
end Determinantal
