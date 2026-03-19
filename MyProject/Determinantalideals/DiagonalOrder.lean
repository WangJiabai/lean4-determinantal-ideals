import Mathlib
import MyProject.Determinantalideals.basic
import MyProject.Determinantalideals.MinorTerms

open scoped BigOperators MonomialOrder

namespace Determinantal

section DiagonalProperty

variable {m n : ℕ}

/--
`ord` is a diagonal term order if, for every minor and every nontrivial permutation
term in its determinant expansion, the diagonal exponent vector is strictly larger.
-/
def IsDiagonalTermOrder
    (ord : MonomialOrder (Fin m × Fin n)) : Prop :=
  ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)),
    σ ≠ 1 → permExp I σ ≺[ord] diagExp I


end DiagonalProperty

section ConcreteLex

variable (m n : ℕ)

/--
The linear order on `Fin m × Fin n` obtained by pulling back the usual order on
`Fin (m * n)` along `rowMajorVarEquiv`.
-/
noncomputable def rowMajorVarOrder : LinearOrder (Fin m × Fin n) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective



noncomputable def rowMajorWF (m n : ℕ) :
    @WellFoundedGT (Fin m × Fin n) (@Preorder.toLT _ (rowMajorVarOrder m n).toPreorder) :=
  @Finite.to_wellFoundedGT
    (Fin m × Fin n)
    (inferInstance : Finite (Fin m × Fin n))
    (rowMajorVarOrder m n).toPreorder

/--
The lexicographic monomial order induced by `rowMajorVarOrder`.
-/
noncomputable def rowMajorLex (m n : ℕ) : MonomialOrder (Fin m × Fin n) :=
  @MonomialOrder.lex (Fin m × Fin n) (rowMajorVarOrder m n) (rowMajorWF m n)


/-- Row-major order: smaller row comes first. -/
lemma rowMajor_lt_of_row_lt
    {i i' : Fin m} {j : Fin n} {j' : Fin n}
    (h : i < i') :
    @LT.lt (Fin m × Fin n) (rowMajorVarOrder m n).toLT
      (i, j) (i', j') := by
  change finProdFinEquiv (i, j) < finProdFinEquiv (i', j')
  change ((finProdFinEquiv (i, j) : Fin (m * n)) : ℕ) <
      ((finProdFinEquiv (i', j') : Fin (m * n)) : ℕ)
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  have haNat : (i : ℕ) < (i' : ℕ) := h
  have hbNat : (j : ℕ) < n := j.isLt
  have h1 : (j : ℕ) + n * (i : ℕ) < n * ((i : ℕ) + 1) := by
    linarith
  have h2 : n * ((i : ℕ) + 1) ≤ n * (i' : ℕ) := by
    exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt haNat)
  have h3 : n * (i' : ℕ) ≤ (j' : ℕ) + n * (i' : ℕ) := by
    simp only [le_add_iff_nonneg_left, zero_le]
  exact lt_of_lt_of_le h1 (le_trans h2 h3)


/-- Row-major order: same row, smaller column comes first. -/
lemma rowMajor_lt_of_col_lt
    {i : Fin m} {j j' : Fin n}
    (h : j < j') :
    @LT.lt (Fin m × Fin n) (rowMajorVarOrder m n).toLT
      (i, j) (i, j') := by
    change finProdFinEquiv (i, j) < finProdFinEquiv (i, j')
    change ((finProdFinEquiv (i, j) : Fin (m * n)) : ℕ) <
        ((finProdFinEquiv (i, j') : Fin (m * n)) : ℕ)
    simp [finProdFinEquiv]
    omega




/--
Main future theorem for the concrete order:
the chosen lex order is indeed diagonal.
-/
theorem rowMajorLex_isDiagonal :
    IsDiagonalTermOrder (m := m) (n := n) (rowMajorLex m n) := by
  classical
  intro t I σ hσ
  let instLO : LinearOrder (Fin m × Fin n) := rowMajorVarOrder m n
  let instWF : @WellFoundedGT (Fin m × Fin n) (@Preorder.toLT _ instLO.toPreorder) := by
    simp [instLO, rowMajorWF]
  rw [show
      (rowMajorLex m n).toSyn (permExp I σ) <
        (rowMajorLex m n).toSyn (diagExp I) ↔
      @LT.lt (Lex ((Fin m × Fin n) →₀ ℕ))
        (@Finsupp.instLTLex
          (Fin m × Fin n) ℕ
          inferInstance
          instLO.toLT
          instLTNat)
        (toLex (permExp I σ))
        (toLex (diagExp I))
      by
        simpa [rowMajorLex, rowMajorWF, instLO, instWF] using
          (@MonomialOrder.lex_lt_iff
            (Fin m × Fin n)
            instLO
            instWF
            (permExp I σ)
            (diagExp I))]
  change Finsupp.Lex
      (fun x y : Fin m × Fin n => @LT.lt _ instLO.toLT x y)
      (fun a b : ℕ => a < b)
      (permExp I σ)
      (diagExp I)
  rw [Finsupp.lex_def]
  let s : Finset (Fin t) := Finset.univ.filter fun i => σ i ≠ i
  have hs : s.Nonempty := by
    by_contra hs'
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
    apply hσ
    ext i
    have hi_not : i ∉ s := by
      simp [hs0]
    have hfix : σ i = i := by
      simpa [s] using hi_not
    simpa using congrArg Fin.val hfix
  let i0 : Fin t := s.min' hs
  have hi0_mem : i0 ∈ s := Finset.min'_mem s hs
  have hi0_move : σ i0 ≠ i0 := (Finset.mem_filter.mp hi0_mem).2
  have hfix_before : ∀ j : Fin t, j < i0 → σ j = j := by
    intro j hj
    by_contra hjne
    have hjmem : j ∈ s := by
      simp [s, hjne]
    exact not_lt_of_ge (Finset.min'_le s j hjmem) hj
  have hi0_lt_sigma : i0 < σ i0 := by
    by_contra hnot
    have hle : σ i0 ≤ i0 := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hfixσ : σ (σ i0) = σ i0 := hfix_before (σ i0) hlt
      exact hi0_move (σ.injective hfixσ)
    · exact hi0_move heq
  have rowMajor_row_lt
    {a a' : Fin m} {b b' : Fin n}
    (ha : a < a') :
    @LT.lt (Fin m × Fin n) instLO.toLT (a, b) (a', b') := by
    exact rowMajor_lt_of_row_lt m n ha
  have rowMajor_col_lt
      {a : Fin m} {b b' : Fin n}
      (hb : b < b') :
      @LT.lt (Fin m × Fin n) instLO.toLT (a, b) (a, b') := by
    exact rowMajor_lt_of_col_lt m n hb
  refine ⟨(I.row i0, I.col i0), ?_, ?_⟩
  · intro d hd
    by_cases hdiagd : ∃ k : Fin t, d = (I.row k, I.col k)
    · rcases hdiagd with ⟨k, rfl⟩
      have hk_lt : k < i0 := by
        by_contra hk_not
        have hk_ge : i0 ≤ k := le_of_not_gt hk_not
        rcases lt_or_eq_of_le hk_ge with hk_gt | rfl
        · have hgt :
              @LT.lt (Fin m × Fin n) instLO.toLT
                (I.row i0, I.col i0) (I.row k, I.col k) :=
            rowMajor_row_lt
              (a := I.row i0) (a' := I.row k)
              (b := I.col i0) (b' := I.col k)
              (I.row.strictMono hk_gt)
          have hgt' :
              finProdFinEquiv (I.row i0, I.col i0) <
                finProdFinEquiv (I.row k, I.col k) := by
            simpa [instLO] using hgt
          have hd' :
              finProdFinEquiv (I.row k, I.col k) <
                finProdFinEquiv (I.row i0, I.col i0) := by
            simpa [instLO] using hd
          exact (lt_irrefl _ (lt_trans hgt' hd'))
        · exact (lt_irrefl _ (by exact Option.some_lt_some.mp hd))
      have hkfix : σ k = k := hfix_before k hk_lt
      have hperm : permExp I σ (I.row k, I.col k) = 1 :=
        permExp_apply_diag_of_fix I σ (hfix_before k hk_lt)
      have hdiag : diagExp I (I.row k, I.col k) = 1 :=
        diagExp_apply_diag (I := I) k
      simp [hperm, hdiag]
    · have hdiag0 : diagExp I d = 0 := by
        rw [diagExp,Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finsupp.single_apply]
        by_cases hk' : (I.row k, I.col k) = d
        · exact False.elim (hdiagd ⟨k, hk'.symm⟩)
        · simp [hk']
      have hperm0 : permExp I σ d = 0 := by
        classical
        rw [permExp, Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finsupp.single_apply]
        by_cases hk' : (I.row k, I.col (σ k)) = d
        · have hk_lt : k < i0 := by
            by_contra hk_not
            have hk_ge : i0 ≤ k := le_of_not_gt hk_not
            rcases lt_or_eq_of_le hk_ge with hk_gt | rfl
            · have hjk :
                @LT.lt (Fin m × Fin n) instLO.toLT
                  (I.row i0, I.col i0) (I.row k, I.col (σ k)) :=
                rowMajor_row_lt
                  (a := I.row i0) (a' := I.row k)
                  (b := I.col i0) (b' := I.col (σ k))
                  (I.row.strictMono hk_gt)
              have hjk' :
                  finProdFinEquiv (I.row i0, I.col i0) <
                    finProdFinEquiv d := by
                simpa [instLO, hk'] using hjk
              have hd' :
                  finProdFinEquiv d <
                    finProdFinEquiv (I.row i0, I.col i0) := by
                simpa [instLO] using hd
              exact (lt_irrefl _ (lt_trans hjk' hd'))
            · have hjk :
                @LT.lt (Fin m × Fin n) instLO.toLT
                  (I.row i0, I.col i0) (I.row i0, I.col (σ i0)) :=
                rowMajor_col_lt
                  (a := I.row i0)
                  (b := I.col i0) (b' := I.col (σ i0))
                  (I.col.strictMono hi0_lt_sigma)
              have hjk' :
                  finProdFinEquiv (I.row i0, I.col i0) <
                    finProdFinEquiv d := by
                simpa [instLO, hk'] using hjk
              have hd' :
                  finProdFinEquiv d <
                    finProdFinEquiv (I.row i0, I.col i0) := by
                simpa [instLO] using hd
              exact (lt_irrefl _ (lt_trans hjk' hd'))
          have hkdiag : d = (I.row k, I.col k) := by
            calc
              d = (I.row k, I.col (σ k)) := hk'.symm
              _ = (I.row k, I.col k) :=
                congrArg (Prod.mk (I.row k)) (congrArg (⇑I.col) (hfix_before k hk_lt))
          exact False.elim (hdiagd ⟨k, hkdiag⟩)
        · simp [hk']
      simp [hdiag0, hperm0]
  · have hdiag_at : diagExp I (I.row i0, I.col i0) = 1 := by
      exact diagExp_apply_diag I i0
    have hperm_at : permExp I σ (I.row i0, I.col i0) = 0 := by
      exact permExp_apply_diag_eq_zero I σ hi0_move (by exact fun j a ↦ hfix_before j a)
    simp [hperm_at, hdiag_at]

end ConcreteLex

section FutureBridgeLemmas

variable {k : Type*} [CommRing k]
variable {m n t : ℕ}


/--
A non-identity permutation term has exponent vector different from the diagonal one.
This is usually proved combinatorially from injectivity of the row/column embeddings.
-/
theorem permExp_ne_diagExp_of_ne_one
    (I : MinorIndex m n t) {σ : Equiv.Perm (Fin t)}
    (hσ : σ ≠ 1) :
    permExp I σ ≠ diagExp I:=by
    intro hEq
    have hlt : permExp I σ ≺[rowMajorLex m n] diagExp I :=
      rowMajorLex_isDiagonal (m := m) (n := n) I σ hσ
    simp [hEq] at hlt

end FutureBridgeLemmas

section LeadingTermConsequences

variable {k : Type*} [CommRing k] [Nontrivial k]
variable {m n t : ℕ}

/--
Under a diagonal term order, the `degree` of a minor is exactly the diagonal exponent vector.
-/
theorem degree_minor_eq_diagExp
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    (I : MinorIndex m n t) :
    ord.degree (minor (m := m) (n := n) (k := k) I) = diagExp I:=by
  classical
  apply ord.toSyn.injective
  apply le_antisymm
  · rw [ord.degree_le_iff]
    intro c hc
    have hcoeff : MvPolynomial.coeff c (minor (m := m) (n := n) (k := k) I) ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hc
    rw [minor_eq_sum_permTerm (k := k) (I := I), MvPolynomial.coeff_sum] at hcoeff
    have hex :
        ∃ σ : Equiv.Perm (Fin t),
          MvPolynomial.coeff c (permTerm (k := k) I σ) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hcoeff <| by
        refine Finset.sum_eq_zero ?_
        intro σ hσ
        exact h σ
    rcases hex with ⟨σ, hσcoeff⟩
    have hc_eq : c = permExp I σ := by
      by_contra hne
      have : MvPolynomial.coeff c (permTerm (k := k) I σ) = 0 := by
        simp only [permTerm, permExp, MvPolynomial.coeff_monomial, ite_eq_right_iff]
        exact fun a ↦ False.elim (hne (id (Eq.symm a)))
      exact hσcoeff this
    by_cases hσ1 : σ = 1
    · subst hσ1
      simp [hc_eq, permExp_one]
    · exact le_of_lt <| by
        simpa [hc_eq] using hdiag I σ hσ1
  · have hsupp : diagExp I ∈ (minor (m := m) (n := n) (k := k) I).support := by
      rw [MvPolynomial.mem_support_iff,
      minor_eq_sum_permTerm (k := k) (I := I), MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin t))]
      · simp [permTerm, permCoeff, permExp_one, MvPolynomial.coeff_monomial]
      · intro σ hσ hσne
        simp [permTerm, MvPolynomial.coeff_monomial,
          permExp_ne_diagExp_of_ne_one (m := m) (n := n) (t := t) (I := I) hσne]
      · intro h
        simp at h
    exact ord.le_degree hsupp

/--
Under a diagonal term order, the leading coefficient of a minor is `1`.
-/
theorem leadingCoeff_minor_eq_one
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    (I : MinorIndex m n t) :
    ord.leadingCoeff (minor (m := m) (n := n) (k := k) I) = 1:=by
    rw [MonomialOrder.leadingCoeff]
    rw [degree_minor_eq_diagExp (ord := ord) (hdiag := hdiag) (I := I)]
    rw [minor_eq_sum_permTerm (k := k) (I := I), MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin t))]
    · simp [permTerm, permCoeff, permExp_one, MvPolynomial.coeff_monomial]
    · intro σ hσ hσne
      simp [permTerm, MvPolynomial.coeff_monomial,
        permExp_ne_diagExp_of_ne_one (m := m) (n := n) (t := t) (I := I) hσne]
    · intro h
      simp at h

theorem monic_minor_of_isDiagonal
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    (I : MinorIndex m n t) :
    ord.Monic (minor (m := m) (n := n) (k := k) I) := by
  simp [MonomialOrder.Monic, leadingCoeff_minor_eq_one (ord := ord) (hdiag := hdiag) (I := I)]

theorem leadingTerm_minor_eq_diagMonomial
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder (m := m) (n := n) ord)
    (I : MinorIndex m n t) :
    ord.leadingTerm (minor (m := m) (n := n) (k := k) I)
      = diagMonomial (k := k) I := by
  simp [MonomialOrder.leadingTerm, diagMonomial,
    degree_minor_eq_diagExp (ord := ord) (hdiag := hdiag) (I := I),
    leadingCoeff_minor_eq_one (ord := ord) (hdiag := hdiag) (I := I)]

theorem degree_minor_rowMajorLex
    (I : MinorIndex m n t) :
    (rowMajorLex m n).degree (minor (m := m) (n := n) (k := k) I) = diagExp I :=
  degree_minor_eq_diagExp
    (ord := rowMajorLex m n)
    (hdiag := rowMajorLex_isDiagonal (m := m) (n := n))
    (I := I)

theorem leadingTerm_minor_rowMajorLex
    (I : MinorIndex m n t) :
    (rowMajorLex m n).leadingTerm (minor (m := m) (n := n) (k := k) I)
      = diagMonomial (k := k) I :=
  leadingTerm_minor_eq_diagMonomial
    (ord := rowMajorLex m n)
    (hdiag := rowMajorLex_isDiagonal (m := m) (n := n))
    (I := I)

end LeadingTermConsequences

end Determinantal
