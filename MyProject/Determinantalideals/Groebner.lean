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
      (minorSet (k := k) t)
      (detIdeal m n t k)
      ↔
    ∀ I J : MinorIndex m n t,
      ord.IsRemainder
        (ord.sPolynomial (genericMinor I) (genericMinor J))
        (minorSet (k := k) t) 0 := by
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


theorem withBotDegree_mul_genericMinor_eq_left
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t)
    {f : MvPolynomial (Fin m × Fin n) k} :
    ord.toWithBotSyn (ord.withBotDegree (f * genericMinor I)) =
      ord.toWithBotSyn (ord.withBotDegree f) +
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) := by
  have hreg : ord.leadingCoeff (genericMinor (k := k) I) ∈ nonZeroDivisors k := by
    have hunit : IsUnit (ord.leadingCoeff (genericMinor (k := k) I)) := by
      simp [leadingCoeff_minor_eq_one ord hdiag I]
    exact hunit.mem_nonZeroDivisors
  simpa using congrArg ord.toWithBotSyn
    (ord.withBotDegree_mul_of_right_mem_nonZeroDivisors hreg)

theorem withBotDegree_mul_genericMinor_eq_right
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t)
    {f : MvPolynomial (Fin m × Fin n) k} :
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I * f)) =
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
      ord.toWithBotSyn (ord.withBotDegree f) := by
  have hreg : ord.leadingCoeff (genericMinor (k := k) I) ∈ nonZeroDivisors k := by
    have hunit : IsUnit (ord.leadingCoeff (genericMinor (k := k) I)) := by
      simp [leadingCoeff_minor_eq_one  ord hdiag I]
    exact hunit.mem_nonZeroDivisors
  simpa using congrArg ord.toWithBotSyn
    (ord.withBotDegree_mul_of_left_mem_nonZeroDivisors hreg)

theorem minor_ne_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    genericMinor (k := k) I ≠ 0 := by
  rw [← ord.leadingCoeff_ne_zero_iff]
  simp [leadingCoeff_minor_eq_one ord hdiag I]

theorem withBotDegree_minor_sub_diag_lt_minor
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.toWithBotSyn
      (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
      <
    ord.toWithBotSyn
      (ord.withBotDegree (genericMinor (k := k) I)) := by
  have hminor : genericMinor (k := k) I ≠ 0 := minor_ne_zero (k := k) ord hdiag I
  by_cases hzero : genericMinor (k := k) I - diagMonomial I = 0
  · rw [hzero]
    refine bot_lt_iff_ne_bot.mpr ?_
    simpa [ord.withBotDegree_eq]
  · change
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
      <
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I))
    refine (ord.withBotDegree_lt_withBotDegree_iff_of_ne_zero
      (f := genericMinor (k := k) I - diagMonomial I)
      (g := genericMinor (k := k) I)
      hzero).2 ?_
    have hlead :
        ord.leadingTerm (genericMinor (k := k) I) = ord.leadingTerm (diagMonomial I) := by
      rw [leadingTerm_minor_eq_diagMonomial (k := k) ord hdiag I]
      simp [diagMonomial]
    have hmem :
        ord.degree (genericMinor (k := k) I - diagMonomial I) ∈
          (genericMinor (k := k) I - diagMonomial I).support := by
      rw [MvPolynomial.mem_support_iff]
      simpa [MonomialOrder.leadingCoeff] using
        (ord.leadingCoeff_ne_zero_iff).2 hzero
    have hsupp :=
      ord.support_sub_of_leadingTerm_eq_leadingTerm
        (p := genericMinor (k := k) I) (q := diagMonomial I) hlead
        (a := ord.degree (genericMinor (k := k) I - diagMonomial I)) hmem
    rcases hsupp with h | h
    · exact h.2
    · have hdeg_diag :
          ord.degree (diagMonomial (k := k) I) = ord.degree (genericMinor (k := k) I) := by
        rcases ord.leadingTerm_eq_leadingTerm_iff.mp hlead with ⟨_, hdeg⟩
        exact hdeg.symm
      simpa [hdeg_diag] using h.2

theorem withBotDegree_tail_lt_minor
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (J : MinorIndex m n t) :
    ord.toWithBotSyn
      (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
      <
    ord.toWithBotSyn
      (ord.withBotDegree (genericMinor (k := k) J)) := by
    have h :=
    withBotDegree_minor_sub_diag_lt_minor
      (k := k) (ord := ord) hdiag J
    rw [show diagMonomial J - genericMinor (k := k) J =
      -(genericMinor (k := k) J - diagMonomial J) by abel, ord.withBotDegree_neg]
    exact withBotDegree_minor_sub_diag_lt_minor ord hdiag J

omit [Nontrivial k] in
theorem degree_tail_eq_permExp
    (ord : MonomialOrder (Fin m × Fin n))
    (I : MinorIndex m n t)
    (hI : genericMinor (k := k) I - diagMonomial I ≠ 0) :
    ∃ σ : Equiv.Perm (Fin t),
      σ ≠ 1 ∧
      ord.degree (genericMinor (k := k) I - diagMonomial I) = permExp I σ := by
  classical
  let c := ord.degree (genericMinor (k := k) I - diagMonomial I)
  have htail :
      genericMinor (k := k) I - diagMonomial I =
        ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)), permTerm (k := k) I σ := by
    rw [minor_eq_sum_permTerm (k := k) I]
    simp only [Finset.mem_univ, Finset.sum_erase_eq_sub, permTerm_one_eq_diagMonomial]
  have hcoeff :
      MvPolynomial.coeff c (genericMinor (k := k) I - diagMonomial I) ≠ 0 := by
    simpa [c, MonomialOrder.leadingCoeff] using
      (ord.leadingCoeff_ne_zero_iff).2 hI
  rw [htail, MvPolynomial.coeff_sum] at hcoeff
  have hex :
      ∃ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)),
        MvPolynomial.coeff c (permTerm (k := k) I σ) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hcoeff <| by
      refine Finset.sum_eq_zero ?_
      intro σ hσ
      exact h σ hσ
  rcases hex with ⟨σ, hσmem, hσcoeff⟩
  have hσne : σ ≠ 1 := (Finset.mem_erase.mp hσmem).1
  have hc_eq : c = permExp I σ := by
    by_contra hne
    have : MvPolynomial.coeff c (permTerm (k := k) I σ) = 0 := by
      simp [coeff_permTerm, hne]
    exact hσcoeff this
  refine ⟨σ, hσne, ?_⟩
  simpa [c] using hc_eq

omit [Nontrivial k] in
theorem degree_diag_sub_minor_eq_permExp
    (ord : MonomialOrder (Fin m × Fin n))
    (J : MinorIndex m n t)
    (hJ : diagMonomial J - genericMinor (k := k) J ≠ 0) :
    ∃ σ : Equiv.Perm (Fin t),
      σ ≠ 1 ∧
      ord.degree (diagMonomial J - genericMinor (k := k) J) = permExp J σ := by
  have hnegJ :
      -(diagMonomial J - genericMinor (k := k) J) =
        genericMinor (k := k) J - diagMonomial J := by
    abel
  have hJ' : genericMinor (k := k) J - diagMonomial J ≠ 0 := by
    simpa [hnegJ] using (neg_ne_zero.mpr hJ)
  rcases degree_tail_eq_permExp ord J hJ' with
    ⟨σ, hσ, hdeg⟩
  refine ⟨σ, hσ, ?_⟩
  calc
    ord.degree (diagMonomial J - genericMinor (k := k) J)
        = ord.degree (-(genericMinor (k := k) J - diagMonomial J)) := by
            congr 1
            abel
    _ = ord.degree (genericMinor (k := k) J - diagMonomial J) := by rw [MonomialOrder.degree_neg]
    _ = permExp J σ := hdeg

theorem permExp_add_diagExp_ne_diagExp_add_permExp_of_diagDisjoint
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J)
    {σ τ : Equiv.Perm (Fin t)}
    (hσ : σ ≠ 1) :
    permExp J σ + diagExp I ≠ permExp I τ + diagExp J := by
  classical
  have hdisj' : Disjoint (diagExp I).support (diagExp J).support := by
    simpa [diagDisjoint] using hdisj
  rcases exists_min_moved hσ with ⟨j0, hmove, hfix_before⟩
  let d : Fin m × Fin n := (J.row j0, J.col j0)
  have hdJ_mem : d ∈ (diagExp J).support := by
    have : diagExp J d = 1 := by
      simp [d]
    exact by
      simp [Finsupp.mem_support_iff, this, d]
  have hdI_not : d ∉ (diagExp I).support := by
    intro hdI
    exact (Finset.disjoint_left.mp hdisj' hdI hdJ_mem)
  have hdI_zero : diagExp I d = 0 := by
    by_contra hne
    exact hdI_not <| by
      simp [Finsupp.mem_support_iff, hne]
  have hleft_zero : (permExp J σ + diagExp I) d = 0 := by
    simp [Finsupp.add_apply, d, hdI_zero,
      permExp_apply_diag_eq_zero J σ hmove hfix_before]
  have hright_ne_zero : (permExp I τ + diagExp J) d ≠ 0 := by
    simp [Finsupp.add_apply, d, diagExp_apply_diag]
  intro hEq
  have hval := congrArg (fun e => e d) hEq
  simp only [hleft_zero, Finsupp.coe_add, Pi.add_apply] at hval
  exact Ne.elim hright_ne_zero (id (Eq.symm hval))

theorem tail_products_have_distinct_withBotDegree_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J)
    (hI : genericMinor (k := k) I - diagMonomial I ≠ 0)
    (hJ : diagMonomial J - genericMinor (k := k) J ≠ 0) :
    ord.toWithBotSyn (ord.withBotDegree
      ((diagMonomial J - genericMinor (k := k) J) * genericMinor (k := k) I))
    ≠
    ord.toWithBotSyn (ord.withBotDegree
      ((genericMinor (k := k) I - diagMonomial I) * genericMinor J)) := by
  classical
  rcases degree_diag_sub_minor_eq_permExp ord J hJ with
    ⟨σ, hσ, hdegJ⟩
  rcases degree_tail_eq_permExp ord I hI with
    ⟨τ, hτ, hdegI⟩
  intro hEq
  have hmulL :
      ord.toWithBotSyn
        (ord.withBotDegree
          ((diagMonomial J - genericMinor (k := k) J) * genericMinor (k := k) I))
      =
      ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
      +
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) := by
    simpa using
      withBotDegree_mul_genericMinor_eq_left ord hdiag I
  have hmulR :
      ord.toWithBotSyn
        (ord.withBotDegree
          ((genericMinor (k := k) I - diagMonomial I) * genericMinor J))
      =
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
      +
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) J)) := by
    simpa using
      withBotDegree_mul_genericMinor_eq_left ord hdiag J
        (f := genericMinor (k := k) I - diagMonomial I)
  have hsumEq :
      (((ord.toSyn (permExp J σ) : ord.syn) : WithBot ord.syn) +
        ((ord.toSyn (diagExp I) : ord.syn) : WithBot ord.syn))
        =
      (((ord.toSyn (permExp I τ) : ord.syn) : WithBot ord.syn) +
        ((ord.toSyn (diagExp J) : ord.syn) : WithBot ord.syn)) := by
    rw [hmulL, hmulR] at hEq
    simpa [ord.withBotDegree_eq, hJ, hI, (minor_ne_zero ord hdiag I), (minor_ne_zero ord hdiag J),
      hdegJ, hdegI,
      degree_minor_eq_diagExp (k := k) ord hdiag I,
      degree_minor_eq_diagExp (k := k) ord hdiag J,
      ord.toWithBotSyn_apply_coe] using hEq
  have hdegEq' :
      ((ord.toSyn (permExp J σ + diagExp I) : ord.syn) : WithBot ord.syn)
        =
      ((ord.toSyn (permExp I τ + diagExp J) : ord.syn) : WithBot ord.syn) := by
    simpa [← WithBot.coe_add, ← map_add] using hsumEq
  have hdegEq :
      ord.toSyn (permExp J σ + diagExp I)
        =
      ord.toSyn (permExp I τ + diagExp J) := by
    exact_mod_cast hdegEq'
  have hcontra :
      permExp J σ + diagExp I ≠ permExp I τ + diagExp J :=
    permExp_add_diagExp_ne_diagExp_add_permExp_of_diagDisjoint
      (I := I) (J := J) hdisj hσ
  exact hcontra (ord.toSyn.injective hdegEq)

omit [Nontrivial k] in
theorem toWithBotSyn_withBotDegree_add_eq_max_of_ne
    (ord : MonomialOrder (Fin m × Fin n))
    {f g : MvPolynomial (Fin m × Fin n) k}
    (hne : ord.withBotDegree f ≠ ord.withBotDegree g) :
    ord.toWithBotSyn (ord.withBotDegree (f + g)) =
      max (ord.toWithBotSyn (ord.withBotDegree f))
          (ord.toWithBotSyn (ord.withBotDegree g)) := by
  have hne' :
      ord.toWithBotSyn (ord.withBotDegree f) ≠
      ord.toWithBotSyn (ord.withBotDegree g) := by
    intro h
    apply hne
    exact ord.toWithBotSyn.injective h
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have hadd :
        ord.withBotDegree (f + g) = ord.withBotDegree g := by
      exact ord.withBotDegree_add_of_right_lt (f := f) (g := g) hlt
    rw [hadd]
    exact (max_eq_right_of_lt hlt).symm
  · have hadd :
        ord.withBotDegree (f + g) = ord.withBotDegree f := by
      exact ord.withBotDegree_add_of_lt (f := f) (g := g) hgt
    rw [hadd]
    exact (max_eq_left_of_lt hgt).symm


theorem degree_bound_left_tail_coeff_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J)
    (hJ : diagMonomial J - genericMinor (k := k) J ≠ 0) :
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
      ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
      ≤
      ord.toWithBotSyn
        (ord.withBotDegree
          (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
  let A := (diagMonomial J - genericMinor J) * genericMinor (k := k) I
  let B := (genericMinor (k := k) I - diagMonomial I) * genericMinor J
  have hs :
      ord.sPolynomial (genericMinor I) (genericMinor J) = A + B := by
    simp [A, B, sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
      (k := k) (ord := ord) hdiag hdisj]
  have hAdeg :
      ord.toWithBotSyn (ord.withBotDegree A) =
        ord.toWithBotSyn (ord.withBotDegree (diagMonomial (k := k) J - genericMinor J)) +
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) := by
    simp [A, withBotDegree_mul_genericMinor_eq_left (k := k) (ord := ord) hdiag I, add_comm]
  by_cases hI : genericMinor (k := k) I - diagMonomial I = 0
  · have hB0 : B = 0 := by
      simp [B, hI]
    have hsA :
        ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) = A := by
      rw [hs, hB0, add_zero]
    calc
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
          ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
          =
        ord.toWithBotSyn (ord.withBotDegree A) := by
          rw [hAdeg, add_comm]
      _ =
        ord.toWithBotSyn
          (ord.withBotDegree (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
          rw [hsA]
    trivial
  · have hAB_ne_syn :
        ord.toWithBotSyn (ord.withBotDegree A) ≠
        ord.toWithBotSyn (ord.withBotDegree B) := by
      simpa [A, B] using
        tail_products_have_distinct_withBotDegree_of_diagDisjoint
          (k := k) (ord := ord) hdiag hdisj hI hJ
    have hAB_ne :
        ord.withBotDegree A ≠ ord.withBotDegree B := by
      intro hEq
      apply hAB_ne_syn
      simp [hEq]
    have hsdeg :
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) =
          max (ord.toWithBotSyn (ord.withBotDegree A))
              (ord.toWithBotSyn (ord.withBotDegree B)) := by
      rw [hs]
      exact toWithBotSyn_withBotDegree_add_eq_max_of_ne (ord := ord) hAB_ne
    calc
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
          ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
          =
        ord.toWithBotSyn (ord.withBotDegree A) := by
          rw [hAdeg, add_comm]
      _ ≤ max (ord.toWithBotSyn (ord.withBotDegree A))
              (ord.toWithBotSyn (ord.withBotDegree B)) := le_max_left _ _
      _ =
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
          symm
          exact hsdeg

theorem degree_bound_right_tail_coeff_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J)
    (hI : genericMinor (k := k) I - diagMonomial I ≠ 0) :
    ord.toWithBotSyn
        (ord.withBotDegree (genericMinor (k := k) J)) +
      ord.toWithBotSyn
        (ord.withBotDegree
          (genericMinor (k := k) I - diagMonomial I))
      ≤
      ord.toWithBotSyn (ord.withBotDegree
        (ord.sPolynomial (genericMinor (k:= k) I) (genericMinor J))) := by
  let A := (diagMonomial J - genericMinor J) * genericMinor (k := k) I
  let B := (genericMinor (k := k) I - diagMonomial I) * genericMinor J
  have hs :
      ord.sPolynomial (genericMinor I) (genericMinor J) = A + B := by
    simp [A, B, sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
      (k := k) (ord := ord) hdiag hdisj]
  have hBdeg :
      ord.toWithBotSyn (ord.withBotDegree B) =
        ord.toWithBotSyn
          (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I)) +
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) J)) := by
    simp [B, withBotDegree_mul_genericMinor_eq_left
      (k := k) (ord := ord) hdiag J, add_comm]
  by_cases hJ : diagMonomial (k := k) J - genericMinor J = 0
  · have hA0 : A = 0 := by
      simp [A, hJ]
    have hsB :
        ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) = B := by
      rw [hs, hA0, zero_add]
    calc
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) J)) +
          ord.toWithBotSyn
            (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
          =
        ord.toWithBotSyn (ord.withBotDegree B) := by
          rw [hBdeg, add_comm]
      _ =
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
          rw [hsB]
    trivial
  · have hAB_ne_syn :
        ord.toWithBotSyn (ord.withBotDegree A) ≠
        ord.toWithBotSyn (ord.withBotDegree B) := by
      simpa [A, B] using
        tail_products_have_distinct_withBotDegree_of_diagDisjoint
          (k := k) (ord := ord) hdiag hdisj hI hJ
    have hAB_ne :
        ord.withBotDegree A ≠ ord.withBotDegree B := by
      intro hEq
      apply hAB_ne_syn
      simp [hEq]
    have hsdeg :
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) =
          max (ord.toWithBotSyn (ord.withBotDegree A))
              (ord.toWithBotSyn (ord.withBotDegree B)) := by
      rw [hs]
      exact toWithBotSyn_withBotDegree_add_eq_max_of_ne (ord := ord) hAB_ne
    calc
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) J)) +
          ord.toWithBotSyn
            (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
          =
        ord.toWithBotSyn (ord.withBotDegree B) := by
          rw [hBdeg, add_comm]
      _ ≤ max (ord.toWithBotSyn (ord.withBotDegree A))
              (ord.toWithBotSyn (ord.withBotDegree B)) := le_max_right _ _
      _ =
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
          symm
          exact hsdeg

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
  classical
  by_cases hIJ : I = J
  · refine ⟨0, ?_, ?_⟩
    · subst hIJ
      simp [MonomialOrder.sPolynomial]
    · intro K hK
      simp at hK
  · let a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k :=
      Finsupp.single I (diagMonomial J - genericMinor (k := k) J) +
      Finsupp.single J (genericMinor (k := k) I - diagMonomial I)
    refine ⟨a, ?_, ?_⟩
    · calc
        ord.sPolynomial (genericMinor (k := k) I) (genericMinor J)
            =
          (diagMonomial J - genericMinor J) * genericMinor I
            +
          (genericMinor I - diagMonomial I) * genericMinor J := by
              simpa using
                sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
                  (k := k) (ord := ord) hdiag hdisj
        _ =
          Finsupp.linearCombination _ (fun K ↦ genericMinor K) a := by
            simp [a]
            ring
    · intro K hK
      rw [Finsupp.mem_support_iff] at hK
      by_cases hKI : K = I
      · subst hKI
        have hcoeffJ : diagMonomial J - genericMinor (k := k) J ≠ 0 := by
          simpa [a, hIJ] using hK
        have hval : a K = diagMonomial J - genericMinor (k := k) J := by
          simp [a, hIJ]
        simpa [hval] using
          degree_bound_left_tail_coeff_of_diagDisjoint
            (k := k) (ord := ord) hdiag hdisj hcoeffJ
      · by_cases hKJ : K = J
        · subst hKJ
          have hJI : K ≠ I := by
            intro h
            exact hIJ h.symm
          have hcoeffI : genericMinor (k := k) I - diagMonomial I ≠ 0 := by
            simpa [a, hIJ, hJI] using hK
          have hval : a K = genericMinor (k := k) I - diagMonomial I := by
            simp [a, hJI]
          simpa [hval] using
            degree_bound_right_tail_coeff_of_diagDisjoint
              (k := k) (ord := ord) hdiag hdisj hcoeffI
        · exfalso
          have : a K = 0 := by
            simp [a, hKI, hKJ]
          exact hK this

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
variable {k : Type*} [CommRing k] [Nontrivial k]

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
