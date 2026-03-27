import Mathlib
import MyProject.Determinantalideals.Ideal
import MyProject.Determinantalideals.MinorTerms
import MyProject.Determinantalideals.DiagonalOrder
import Groebner.Groebner
import Groebner.Remainder
import Groebner.Ideal

namespace Determinantal

section first

variable {m n t : ℕ}
variable {k : Type*} [CommRing k] [Nontrivial k]

lemma minorSet_leadingCoeff_isUnit_or_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    (t : ℕ) :
    ∀ g ∈ minorSet (m := m) (n := n) (k := k) t,
      IsUnit (ord.leadingCoeff g) ∨ g = 0 := by
  intro g hg
  rcases hg with ⟨I, rfl⟩
  left
  simp [leadingCoeff_minor_eq_one (ord := ord) hdiag I]

omit [Nontrivial k] in
lemma minorSet_subset_detIdeal (t : ℕ) :
    minorSet (m := m) (n := n) (k := k) t ⊆ detIdeal m n t k := by
  intro g hg
  rcases hg with ⟨I, rfl⟩
  exact minor_mem_detIdeal (k := k) I

theorem minorSet_isGroebnerBasis_iff_pairwise_sPolynomial_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (t : ℕ) :
    ord.IsGroebnerBasis
      (minorSet (m := m) (n := n) (k := k) t)
      (detIdeal m n t k)
      ↔
    ∀ I J : MinorIndex m n t,
      ord.IsRemainder
        (ord.sPolynomial (genericMinor I) (genericMinor J))
        (minorSet (m := m) (n := n) (k := k) t) 0 := by
  rw [detIdeal]
  refine
    (MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_isRemainder_sPolynomial_zero₀
      (minorSet_leadingCoeff_isUnit_or_zero ord hdiag t)).trans ?_
  constructor
  · intro h I J
    exact h
      ⟨genericMinor I, ⟨I, rfl⟩⟩
      ⟨genericMinor J, ⟨J, rfl⟩⟩
  · intro h g₁ g₂
    rcases g₁ with ⟨g₁, hg₁⟩
    rcases g₂ with ⟨g₂, hg₂⟩
    rcases hg₁ with ⟨I, rfl⟩
    rcases hg₂ with ⟨J, rfl⟩
    exact h I J


end first

section second

theorem isRemainder_zero_range_iff
    {σ α : Type*}
    {ord : MonomialOrder σ}
    {R : Type*} [CommSemiring R]
    {f : α → MvPolynomial σ R}
    {p : MvPolynomial σ R} :
    ord.IsRemainder p (Set.range f) 0 ↔
      ∃ a : α →₀ MvPolynomial σ R,
        p = Finsupp.linearCombination _ f a ∧
        ∀ i ∈ a.support,
          ord.toWithBotSyn (ord.withBotDegree (f i)) +
            ord.toWithBotSyn (ord.withBotDegree (a i))
              ≤ ord.toWithBotSyn (ord.withBotDegree p) := by
  classical
  rw [MonomialOrder.IsRemainder.isRemainder_range p f 0]
  simp only [add_zero, MvPolynomial.support_zero, Finset.notMem_empty, ne_eq, IsEmpty.forall_iff,
    implies_true, and_true, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨a, ha, hdeg⟩
    exact ⟨a, ha, fun i hi => hdeg i⟩
  · rintro ⟨a, ha, hdeg⟩
    refine ⟨a, ha, ?_⟩
    intro i
    by_cases hi : i ∈ a.support
    · exact hdeg i (Finsupp.mem_support_iff.mp hi)
    · subst ha
      simp_all only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not,
        MonomialOrder.withBotDegree_zero, MonomialOrder.toWithBotSyn_apply_bot,
         WithBot.add_bot, bot_le]

variable {m n t : ℕ}
variable {k : Type*} [CommRing k]

theorem isRemainder_zero_minorSet_iff
    (ord : MonomialOrder (Fin m × Fin n))
    {p : MvPolynomial (Fin m × Fin n) k} :
    ord.IsRemainder p (minorSet (m := m) (n := n) (k := k) t) 0 ↔
      ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
        p = Finsupp.linearCombination _ (fun I ↦ genericMinor I) a ∧
        ∀ I ∈ a.support,
          ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
            ord.toWithBotSyn (ord.withBotDegree (a I))
              ≤ ord.toWithBotSyn (ord.withBotDegree p) := by
  simpa [minorSet]
    using (isRemainder_zero_range_iff (f := fun I : MinorIndex m n t ↦ genericMinor I) (p := p))


end second


section third

variable {m n t : ℕ}
variable (k : Type*) [CommRing k]



theorem sPolynomial_minor_eq [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    (I J : MinorIndex m n t) :
    ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) =
      MvPolynomial.monomial (diagExp J - diagExp I) 1 * genericMinor I
        - MvPolynomial.monomial (diagExp I - diagExp J) 1 * genericMinor J := by
  simp only [MonomialOrder.sPolynomial, degree_minor_eq_diagExp ord hdiag J,
    degree_minor_eq_diagExp ord hdiag I, leadingCoeff_minor_eq_one ord hdiag J,
    leadingCoeff_minor_eq_one ord hdiag I]

end third

section fourth

variable {m n t : ℕ}
variable {k : Type*} [CommRing k] [Nontrivial k]

def diagDisjoint (I J : MinorIndex m n t) : Prop :=
  Disjoint (diagExp I).support (diagExp J).support

theorem sPolynomial_minor_eq_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.sPolynomial (genericMinor I) (genericMinor J) =
      diagMonomial J * genericMinor (k := k) I - diagMonomial I * genericMinor J := by
  have hdisj' : Disjoint (diagExp I).support (diagExp J).support := by
    simpa [diagDisjoint] using hdisj
  have hsubJI : diagExp J - diagExp I = diagExp J := by
    ext x
    by_cases hI0 : diagExp I x = 0
    · simp [hI0]
    · have hJ0 : diagExp J x = 0 := by
        by_contra hJ0
        have hxI : x ∈ (diagExp I).support := by
          simp [Finsupp.mem_support_iff, hI0]
        have hxJ : x ∈ (diagExp J).support := by
          simp [Finsupp.mem_support_iff, hJ0]
        exact (Finset.disjoint_left.mp hdisj' hxI hxJ)
      simp [hJ0]
  have hsubIJ : diagExp I - diagExp J = diagExp I := by
    ext x
    by_cases hJ0 : diagExp J x = 0
    · simp [hJ0]
    · have hI0 : diagExp I x = 0 := by
        by_contra hI0
        have hxI : x ∈ (diagExp I).support := by
          simp [Finsupp.mem_support_iff, hI0]
        have hxJ : x ∈ (diagExp J).support := by
          simp [Finsupp.mem_support_iff, hJ0]
        exact (Finset.disjoint_left.mp hdisj' hxI hxJ)
      simp [hI0]
  rw [MonomialOrder.sPolynomial]
  rw [degree_minor_eq_diagExp ord hdiag I, degree_minor_eq_diagExp ord hdiag J]
  rw [leadingCoeff_minor_eq_one ord hdiag I, leadingCoeff_minor_eq_one ord hdiag J]
  rw [hsubJI, hsubIJ]
  simp [diagMonomial]

theorem sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) =
      (diagMonomial J - genericMinor J) * genericMinor I
    + (genericMinor I - diagMonomial I) * genericMinor J := by
  rw[sPolynomial_minor_eq_of_diagDisjoint ord hdiag hdisj]
  ring

theorem withBotDegree_mul_eq
    (ord : MonomialOrder (Fin m × Fin n))
    {f g : MvPolynomial (Fin m × Fin n) k}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ord.toWithBotSyn (ord.withBotDegree (f * g))
      =
    ord.toWithBotSyn (ord.withBotDegree f) +
      ord.toWithBotSyn (ord.withBotDegree g) := by
  sorry

theorem right_tail_product_lt_left_tail_product_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.withBotDegree
      ((genericMinor (k := k) I - diagMonomial I) * genericMinor J)
      <
    ord.withBotDegree
      ((diagMonomial (k := k) J - genericMinor J) * genericMinor I) := by
  sorry

theorem withBotDegree_add_eq_left_of_lt
    (ord : MonomialOrder (Fin m × Fin n))
    {f g : MvPolynomial (Fin m × Fin n) k}
    (h : ord.withBotDegree g < ord.withBotDegree f) :
    ord.withBotDegree (f + g) = ord.withBotDegree f := by
  sorry

theorem left_tail_coeff_ne_zero_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    diagMonomial J - genericMinor (k := k) J ≠ 0 := by
  sorry

theorem minor_ne_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    genericMinor (k := k) I ≠ 0 := by
  sorry

theorem degree_bound_left_tail_coeff_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
    ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
    ≤
    ord.toWithBotSyn (ord.withBotDegree (ord.sPolynomial (genericMinor (k := k) I)
    (genericMinor J))) := by
  let A := (diagMonomial J - genericMinor J) * genericMinor (k:= k) I
  let B := (genericMinor (k := k) I - diagMonomial I) * genericMinor J

  have hs :
      ord.sPolynomial (genericMinor I) (genericMinor J) = A + B := by
    simp [A, B, sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
      (k := k) (ord := ord) hdiag hdisj]

  have hA_ne : A ≠ 0 := by
    -- from left_tail_coeff_ne_zero_of_diagDisjoint + minor_ne_zero
    sorry

  have hAdeg :
      ord.toWithBotSyn (ord.withBotDegree A)
        =
      ord.toWithBotSyn (ord.withBotDegree (diagMonomial  (k:= k) J - genericMinor J)) +
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) := by
    -- from withBotDegree_mul_eq
    sorry

  have hBA :
      ord.withBotDegree B < ord.withBotDegree A := by
    exact right_tail_product_lt_left_tail_product_of_diagDisjoint
      (k := k) (ord := ord) hdiag hdisj

  have hsdeg :
      ord.withBotDegree (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))
        =
      ord.withBotDegree A := by
    rw [hs, withBotDegree_add_eq_left_of_lt (ord := ord) hBA]

  rw [hsdeg]
  rw [hAdeg]
  simp [add_comm]

theorem degree_bound_right_tail_coeff_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.toWithBotSyn
        (ord.withBotDegree (genericMinor (k := k) J)) +
      ord.toWithBotSyn
        (ord.withBotDegree
          (genericMinor (k := k) I - diagMonomial I))
      ≤
      ord.toWithBotSyn (ord.withBotDegree
        (ord.sPolynomial (genericMinor (k:= k) I) (genericMinor J))) := by
  sorry

theorem exists_diagDisjoint_sPolynomial_certificate
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
      ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) =
      Finsupp.linearCombination _ (fun K ↦ genericMinor K) a
      ∧
      ∀ K ∈ a.support,
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
      ord.toWithBotSyn (ord.withBotDegree (a K))
    ≤ ord.toWithBotSyn (ord.withBotDegree
    (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
  sorry

theorem isRemainder_sPolynomial_minor_zero_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.IsRemainder
      (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J)) (minorSet t) 0 := by
  rw [isRemainder_zero_minorSet_iff]
  exact exists_diagDisjoint_sPolynomial_certificate ord hdiag hdisj

end fourth

section fifth

variable {m n t : ℕ}
variable {k : Type*} [CommRing k]

theorem exists_sPolynomial_minor_certificate
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    (I J : MinorIndex m n t) :
    ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
      ord.sPolynomial (genericMinor I) (genericMinor (k := k) J) =
        Finsupp.linearCombination _ (fun K ↦ genericMinor K) a
      ∧
      ∀ K ∈ a.support,
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
          ord.toWithBotSyn (ord.withBotDegree (a K))
            ≤ ord.toWithBotSyn
                (ord.withBotDegree
                  (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
  sorry

theorem isRemainder_sPolynomial_minor_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    (I J : MinorIndex m n t) :
    ord.IsRemainder
      (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))
      (minorSet (m := m) (n := n) (k := k) t) 0 := by
  rw [isRemainder_zero_minorSet_iff]
  exact exists_sPolynomial_minor_certificate ord hdiag I J

end fifth



section

variable {m n t : ℕ}
variable {k : Type*} [CommRing k]




theorem minorSet_isGroebnerBasis_of_isDiagonalTermOrder
    {k : Type*} [CommRing k] [Nontrivial k]
    {m n : ℕ}
    (ord : MonomialOrder (Fin m × Fin n))
    (t : ℕ)
    (hdiag : IsDiagonalTermOrder ord) :
    ord.IsGroebnerBasis
      (minorSet (m := m) (n := n) (k := k) t)
      (detIdeal m n t k) := by
  rw [minorSet_isGroebnerBasis_iff_pairwise_sPolynomial_zero ord hdiag]
  intro I J
  exact isRemainder_sPolynomial_minor_zero ord hdiag I J



end


end Determinantal
