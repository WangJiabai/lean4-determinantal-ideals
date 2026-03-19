/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib

/-! # Degree, leading coefficient and leading term of polynomials with respect to a monomial order

We consider a type `σ` of indeterminates and a commutative semiring `R`
and a monomial order `m : MonomialOrder σ`.

* `m.degree f` is the degree of `f` for the monomial ordering `m`.

* `m.leadingCoeff f` is the leading coefficient of `f` for the monomial ordering `m`.

* `m.Monic f` asserts that the leading coefficient of `f` is `1`.

* `m.leadingTerm f` is the leading term of `f` for the monomial ordering `m`.

* `m.sPolynomial f g` is S-polynomial of `f` and `g`.

* `m.leadingCoeff_ne_zero_iff f` asserts that this coefficient is nonzero iff `f ≠ 0`.

* in a field, `m.isUnit_leadingCoeff f` asserts that this coefficient is a unit iff `f ≠ 0`.

* `m.degree_add_le` : the `m.degree` of `f + g` is smaller than or equal to the supremum
  of those of `f` and `g`.

* `m.degree_add_of_lt h` : the `m.degree` of `f + g` is equal to that of `f`
  if the `m.degree` of `g` is strictly smaller than that `f`.

* `m.leadingCoeff_add_of_lt h`: then, the leading coefficient of `f + g` is that of `f`.

* `m.degree_add_of_ne h` : the `m.degree` of `f + g` is equal to that the supremum
  of those of `f` and `g` if they are distinct.

* `m.degree_sub_le` : the `m.degree` of `f - g` is smaller than or equal to the supremum
  of those of `f` and `g`.

* `m.degree_sub_of_lt h` : the `m.degree` of `f - g` is equal to that of `f`
  if the `m.degree` of `g` is strictly smaller than that `f`.

* `m.leadingCoeff_sub_of_lt h`: then, the leading coefficient of `f - g` is that of `f`.

* `m.degree_mul_le`: the `m.degree` of `f * g` is smaller than or equal to the sum of those of
  `f` and `g`.

* `m.degree_mul_of_mul_leadingCoeff_ne_zero` : if the product of the leading coefficients
  is nonzero, then the degree is the sum of the degrees.

* `m.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero` : if the product of the leading coefficients
  is nonzero, then the leading coefficient is that product.

* `m.degree_mul_of_isRegular_left`, `m.degree_mul_of_isRegular_right` and `m.degree_mul`
  assert the  equality when the leading coefficient of `f` or `g` is regular,
  or when `R` is a domain and `f` and `g` are nonzero.

* `m.leadingCoeff_mul_of_isRegular_left`, `m.leadingCoeff_mul_of_isRegular_right`
  and `m.leadingCoeff_mul` say that `m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g`

* `m.degree_pow_of_pow_leadingCoeff_ne_zero` : is the `n`th power of the leading coefficient
  of `f` is nonzero, then the degree of `f ^ n` is `n • (m.degree f)`

* `m.leadingCoeff_pow_of_pow_leadingCoeff_ne_zero` : is the `n`th power of the leading coefficient
  of `f` is nonzero, then the leading coefficient of `f ^ n` is that power.

* `m.degree_prod_of_regular` : the degree of a product of polynomials whose leading coefficients
  are regular is the sum of their degrees.

* `m.leadingCoeff_prod_of_regular` : the leading coefficient of a product of polynomials
  whose leading coefficients are regular is the product of their leading coefficients.

* `m.Monic.prod` : a product of monic polynomials is monic.

* `m.degree_sub_leadingTerm` : the degree of `f - m.leadingTerm f` is smaller than
  the degree of `f` unless `f - m.leadingTerm f = 0`.

* `m.degree_sub_leadingTerm_lt_degree` : if `f - m.leadingTerm f ≠ 0`, the degree of
  `f - m.leadingTerm f` is smaller than the degree of `f`.

* `m.degree_sub_leadingTerm_lt_iff` : the degree of `f - m.leadingTerm f` is smaller than the
  degree of `f` if and only if `m.degree f ≠ 0`.

## Reference

[Becker-Weispfenning1993]

-/

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ}

section Semiring

variable {R : Type*} [CommSemiring R]

variable (m) in
/-- the degree of a multivariate polynomial with respect to a monomial ordering -/
def degree (f : MvPolynomial σ R) : σ →₀ ℕ :=
  m.toSyn.symm (f.support.sup m.toSyn)

variable (m) in
/-- the leading coefficient of a multivariate polynomial with respect to a monomial ordering -/
def leadingCoeff (f : MvPolynomial σ R) : R :=
  f.coeff (m.degree f)

variable (m) in
/-- A multivariate polynomial is `Monic` with respect to a monomial order
if its leading coefficient (for that monomial order) is 1. -/
def Monic (f : MvPolynomial σ R) : Prop :=
  m.leadingCoeff f = 1

/-- The leading term of of a multivariate polynomial with respect to a monomial ordering. -/
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

@[nontriviality] theorem Monic.of_subsingleton [Subsingleton R] {f : MvPolynomial σ R} :
    m.Monic f :=
  Subsingleton.eq_one (m.leadingCoeff f)

instance Monic.decidable [DecidableEq R] (f : MvPolynomial σ R) :
    Decidable (m.Monic f) := by
  unfold Monic; infer_instance

@[simp]
theorem Monic.leadingCoeff_eq_one {f : MvPolynomial σ R} (hf : m.Monic f) : m.leadingCoeff f = 1 :=
  hf

theorem Monic.coeff_degree {f : MvPolynomial σ R} (hf : m.Monic f) : f.coeff (m.degree f) = 1 :=
  hf

@[simp]
theorem degree_zero : m.degree (0 : MvPolynomial σ R) = 0 := by
  simp [degree]

theorem ne_zero_of_degree_ne_zero {f : MvPolynomial σ R} (h : m.degree f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h m.degree_zero

@[simp, nontriviality]
theorem degree_subsingleton [Subsingleton R] {f : MvPolynomial σ R} :
    m.degree f = 0 := by
  rw [Subsingleton.eq_zero f, degree_zero]

@[simp]
theorem leadingCoeff_zero : m.leadingCoeff (0 : MvPolynomial σ R) = 0 := by
  simp [degree, leadingCoeff]

theorem Monic.ne_zero [Nontrivial R] {f : MvPolynomial σ R} (hf : m.Monic f) :
    f ≠ 0 := by
  rintro rfl
  simp [Monic, leadingCoeff_zero] at hf

theorem degree_monomial_le {d : σ →₀ ℕ} (c : R) :
    m.degree (monomial d c) ≼[m] d := by
  simp only [degree, AddEquiv.apply_symm_apply]
  apply le_trans (Finset.sup_mono support_monomial_subset)
  simp only [Finset.sup_singleton, le_refl]

theorem degree_monomial {d : σ →₀ ℕ} (c : R) [Decidable (c = 0)] :
    m.degree (monomial d c) = if c = 0 then 0 else d := by
  simp only [degree, support_monomial]
  split_ifs with hc <;> simp

theorem degree_X_le_single {s : σ} : m.degree (X s : MvPolynomial σ R) ≼[m] Finsupp.single s 1 :=
  degree_monomial_le 1

theorem degree_X [Nontrivial R] {s : σ} :
    m.degree (X s : MvPolynomial σ R) = Finsupp.single s 1 := by
  classical
  change m.degree (monomial (Finsupp.single s 1) (1 : R)) = _
  rw [degree_monomial, if_neg one_ne_zero]

@[simp] theorem degree_one : m.degree (1 : MvPolynomial σ R) = 0 := by
  nontriviality R
  classical rw [MvPolynomial.one_def, degree_monomial]
  simp

@[simp]
theorem leadingCoeff_monomial {d : σ →₀ ℕ} (c : R) :
    m.leadingCoeff (monomial d c) = c := by
  classical
  simp only [leadingCoeff, degree_monomial]
  split_ifs with hc <;> simp [hc]

@[simp] theorem monic_monomial_one {d : σ →₀ ℕ} :
    m.Monic (monomial d (1 : R)) :=
  m.leadingCoeff_monomial 1

theorem monic_monomial {d : σ →₀ ℕ} {c : R} :
    m.Monic (monomial d c) ↔ c = 1 := by
  rw [Monic, m.leadingCoeff_monomial]

theorem leadingCoeff_X {s : σ} :
    m.leadingCoeff (X s : MvPolynomial σ R) = 1 :=
  m.leadingCoeff_monomial 1

@[simp] theorem monic_X {s : σ} :
    m.Monic (X s : MvPolynomial σ R) :=
  monic_monomial_one

theorem leadingCoeff_one : m.leadingCoeff (1 : MvPolynomial σ R) = 1 :=
  m.leadingCoeff_monomial 1

theorem monic_one : m.Monic (C 1 : MvPolynomial σ R) :=
  monic_monomial_one

theorem degree_le_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} :
    m.degree f ≼[m] d ↔ ∀ c ∈ f.support, c ≼[m] d := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.sup_le_iff, mem_support_iff, ne_eq]

theorem degree_lt_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : 0 ≺[m] d) :
    m.degree f ≺[m] d ↔ ∀ c ∈ f.support, c ≺[m] d := by
  simp only [map_zero] at hd
  unfold degree
  simp only [AddEquiv.apply_symm_apply]
  exact Finset.sup_lt_iff hd

theorem le_degree {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    d ≼[m] m.degree f := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.le_sup hd]

theorem coeff_eq_zero_of_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : m.degree f ≺[m] d) :
    f.coeff d = 0 := by
  rw [← not_le] at hd
  by_contra hf
  apply hd (m.le_degree (mem_support_iff.mpr hf))

theorem leadingCoeff_ne_zero_iff {f : MvPolynomial σ R} :
    m.leadingCoeff f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · rw [not_imp_not]
    intro hf
    rw [hf, leadingCoeff_zero]
  · intro hf
    rw [← support_nonempty] at hf
    rw [leadingCoeff, ← mem_support_iff, degree]
    suffices f.support.sup m.toSyn ∈ m.toSyn '' f.support by
      obtain ⟨d, hd, hd'⟩ := this
      rw [← hd', AddEquiv.symm_apply_apply]
      exact hd
    exact Finset.sup_mem_of_nonempty hf

@[simp]
theorem leadingCoeff_eq_zero_iff {f : MvPolynomial σ R} :
    leadingCoeff m f = 0 ↔ f = 0 := by
  simp only [← not_iff_not, leadingCoeff_ne_zero_iff]

theorem coeff_degree_ne_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) ≠ 0 ↔ f ≠ 0 :=
  m.leadingCoeff_ne_zero_iff

theorem degree_mem_support_iff (f : MvPolynomial σ R) : m.degree f ∈ f.support ↔ f ≠ 0 :=
  mem_support_iff.trans coeff_degree_ne_zero_iff

@[simp]
theorem coeff_degree_eq_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) = 0 ↔ f = 0 :=
  m.leadingCoeff_eq_zero_iff

lemma degree_mem_support {p : MvPolynomial σ R} (hp : p ≠ 0) :
    m.degree p ∈ p.support := by
  rwa [MvPolynomial.mem_support_iff, coeff_degree_ne_zero_iff]

theorem degree_eq_zero_iff_totalDegree_eq_zero {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f.totalDegree = 0 := by
  rw [← m.toSyn.injective.eq_iff]
  rw [map_zero, ← m.bot_eq_zero, eq_bot_iff, m.bot_eq_zero, ← m.toSyn.map_zero]
  rw [degree_le_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall_congr'
  intro d
  apply imp_congr (rfl.to_iff)
  rw [map_zero, ← m.bot_eq_zero, ← eq_bot_iff, m.bot_eq_zero]
  simp only [EmbeddingLike.map_eq_zero_iff]
  exact Finsupp.ext_iff

@[simp]
theorem degree_C (r : R) :
    m.degree (C r) = 0 := by
  rw [degree_eq_zero_iff_totalDegree_eq_zero, totalDegree_C]

theorem eq_C_of_degree_eq_zero {f : MvPolynomial σ R} (hf : m.degree f = 0) :
    f = C (m.leadingCoeff f) := by
  ext d
  simp only [leadingCoeff, hf]
  classical
  by_cases hd : d = 0
  · simp [hd]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    apply coeff_eq_zero_of_lt (m := m)
    rw [hf, map_zero, lt_iff_le_and_ne, ne_eq, eq_comm, EmbeddingLike.map_eq_zero_iff]
    exact ⟨bot_le, hd⟩

theorem degree_eq_zero_iff {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f = C (m.leadingCoeff f) :=
  ⟨MonomialOrder.eq_C_of_degree_eq_zero, fun h => by rw [h, MonomialOrder.degree_C]⟩

theorem degree_add_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f + g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  conv_rhs => rw [← m.toSyn.apply_symm_apply (_ ⊔ _)]
  rw [degree_le_iff]
  simp only [AddEquiv.apply_symm_apply, le_sup_iff]
  intro b hb
  by_cases hf : b ∈ f.support
  · left
    exact m.le_degree hf
  · right
    apply m.le_degree
    simp only [notMem_support_iff] at hf
    simpa only [mem_support_iff, coeff_add, hf, zero_add] using hb

theorem degree_sum_le {α : Type*} {s : Finset α} {f : α → MvPolynomial σ R} :
    (m.toSyn <| m.degree <| ∑ x ∈ s, f x) ≤ s.sup fun x ↦ (m.toSyn <| m.degree <| f x) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact le_trans m.degree_add_le (max_le_max le_rfl h)

theorem degree_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f + g) = m.degree f := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply le_trans degree_add_le
    simp only [sup_le_iff, le_refl, true_and, le_of_lt h]
  · apply le_degree
    rw [mem_support_iff, coeff_add, m.coeff_eq_zero_of_lt h, add_zero,
      ← leadingCoeff, leadingCoeff_ne_zero_iff]
    intro hf
    rw [← not_le, hf] at h
    apply h
    simp only [degree_zero, map_zero]
    apply bot_le

theorem degree_add_eq_right_of_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g) :
    m.degree (f + g) = m.degree g := by
  rw [add_comm]
  exact degree_add_of_lt h

theorem leadingCoeff_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.leadingCoeff (f + g) = m.leadingCoeff f := by
  simp only [leadingCoeff, m.degree_add_of_lt h, coeff_add, coeff_eq_zero_of_lt h, add_zero]

theorem Monic.add_of_lt {f g : MvPolynomial σ R} (hf : m.Monic f) (h : m.degree g ≺[m] m.degree f) :
    m.Monic (f + g) := by
  simp only [Monic, leadingCoeff_add_of_lt h, hf.leadingCoeff_eq_one]

theorem degree_add_of_ne {f g : MvPolynomial σ R}
    (h : m.degree f ≠ m.degree g) :
    m.toSyn (m.degree (f + g)) = m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  by_cases h' : m.degree g ≺[m] m.degree f
  · simp [degree_add_of_lt h', le_of_lt h']
  · rw [not_lt, le_iff_eq_or_lt, Classical.or_iff_not_imp_left, EmbeddingLike.apply_eq_iff_eq] at h'
    rw [add_comm, degree_add_of_lt (h' h), right_eq_sup]
    simp only [le_of_lt (h' h)]

theorem degree_mul_le {f g : MvPolynomial σ R} :
    m.degree (f * g) ≼[m] m.degree f + m.degree g := by
  classical
  rw [degree_le_iff]
  intro c
  rw [← not_lt, mem_support_iff, not_imp_not]
  intro hc
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  dsimp only
  by_cases hd : m.degree f ≺[m] d
  · rw [m.coeff_eq_zero_of_lt hd, zero_mul]
  · suffices m.degree g ≺[m] e by
      rw [m.coeff_eq_zero_of_lt this, mul_zero]
    simp only [not_lt] at hd
    apply lt_of_add_lt_add_left (a := m.toSyn d)
    grw [← map_add _ _ e, hd, ← map_add, hde]
    exact hc

/-- Multiplicativity of leading coefficients -/
theorem coeff_mul_of_add_of_degree_le {f g : MvPolynomial σ R} {a b : σ →₀ ℕ}
    (ha : m.degree f ≼[m] a) (hb : m.degree g ≼[m] b) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (a,b)]
  · rintro ⟨c, d⟩ hcd h
    simp only [Finset.mem_antidiagonal] at hcd
    by_cases hf : m.degree f ≺[m] c
    · rw [m.coeff_eq_zero_of_lt hf, zero_mul]
    · suffices m.degree g ≺[m] d by
        rw [coeff_eq_zero_of_lt this, mul_zero]
      rw [not_lt] at hf
      rw [← not_le]
      intro hf'
      apply h
      suffices c = a by
        simpa [Prod.mk.injEq, this] using hcd
      apply m.toSyn.injective
      apply le_antisymm (le_trans hf ha)
      apply le_of_add_le_add_right (a := m.toSyn b)
      rw [← map_add, ← hcd, map_add]
      simp only [add_le_add_iff_left]
      exact le_trans hf' hb
  · simp

/-- Multiplicativity of leading coefficients -/
theorem coeff_mul_of_degree_add {f g : MvPolynomial σ R} :
    (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m.leadingCoeff g :=
  coeff_mul_of_add_of_degree_le (le_of_eq rfl) (le_of_eq rfl)

/-- Monomial degree of product -/
theorem degree_mul_of_mul_leadingCoeff_ne_zero {f g : MvPolynomial σ R}
    (hfg : m.leadingCoeff f * m.leadingCoeff g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply m.toSyn.injective
  apply le_antisymm degree_mul_le
  apply le_degree
  rw [mem_support_iff, coeff_mul_of_degree_add]
  exact hfg

/-- Multiplicativity of leading coefficients -/
theorem leadingCoeff_mul_of_mul_leadingCoeff_ne_zero {f g : MvPolynomial σ R}
    (hfg : m.leadingCoeff f * m.leadingCoeff g ≠ 0) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  rw [leadingCoeff, ← coeff_mul_of_degree_add, degree_mul_of_mul_leadingCoeff_ne_zero hfg]

/-- Monomial degree of product -/
theorem degree_mul_of_isRegular_left {f g : MvPolynomial σ R}
    (hf : IsRegular (m.leadingCoeff f)) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, hf, IsRegular.left, IsLeftRegular.mul_left_eq_zero_iff,
    leadingCoeff_eq_zero_iff]
  exact hg

/-- Multiplicativity of leading coefficients -/
theorem leadingCoeff_mul_of_isRegular_left {f g : MvPolynomial σ R}
    (hf : IsRegular (m.leadingCoeff f)) (hg : g ≠ 0) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  simp only [leadingCoeff, degree_mul_of_isRegular_left hf hg, coeff_mul_of_degree_add]

/-- Monomial degree of product -/
theorem degree_mul_of_isRegular_right {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : IsRegular (m.leadingCoeff g)) :
    m.degree (f * g) = m.degree f + m.degree g := by
  rw [mul_comm, m.degree_mul_of_isRegular_left hg hf, add_comm]

/-- Multiplicativity of leading coefficients -/
theorem leadingCoeff_mul_of_isRegular_right {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : IsRegular (m.leadingCoeff g)) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  simp only [leadingCoeff, degree_mul_of_isRegular_right hf hg, coeff_mul_of_degree_add]

theorem Monic.mul {f g : MvPolynomial σ R} (hf : m.Monic f) (hg : m.Monic g) :
    m.Monic (f * g) := by
  nontriviality R
  suffices m.leadingCoeff f * m.leadingCoeff g = 1 by
    rw [Monic, MonomialOrder.leadingCoeff,
      degree_mul_of_mul_leadingCoeff_ne_zero, coeff_mul_of_degree_add, this]
    rw [this]
    exact one_ne_zero
  rw [hf.leadingCoeff_eq_one, hg.leadingCoeff_eq_one, one_mul]

/-- Monomial degree of product -/
theorem degree_mul [IsCancelMulZero R] {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g :=
  degree_mul_of_isRegular_left (isRegular_of_ne_zero (leadingCoeff_ne_zero_iff.mpr hf)) hg

/-- Multiplicativity of leading coefficients -/
theorem leadingCoeff_mul [IsCancelMulZero R] {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  rw [leadingCoeff, degree_mul hf hg, ← coeff_mul_of_degree_add]

/-- Monomial degree of powers -/
theorem degree_pow_le {f : MvPolynomial σ R} (n : ℕ) :
    m.degree (f ^ n) ≼[m] n • (m.degree f) := by
  induction n with
  | zero => simp [m.degree_one]
  | succ n hrec =>
      simp only [pow_add, pow_one, add_smul, one_smul]
      apply le_trans m.degree_mul_le
      simp only [map_add, add_le_add_iff_right]
      exact hrec

theorem coeff_pow_nsmul_degree (f : MvPolynomial σ R) (n : ℕ) :
    (f ^ n).coeff (n • m.degree f) = m.leadingCoeff f ^ n := by
  induction n with
  | zero => simp
  | succ n hrec =>
    simp only [add_smul, one_smul, pow_add, pow_one]
    rw [m.coeff_mul_of_add_of_degree_le (m.degree_pow_le _) le_rfl, hrec, leadingCoeff]

/-- Monomial degree of powers -/
theorem degree_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : ℕ}
    (hf : m.leadingCoeff f ^ n ≠ 0) :
    m.degree (f ^ n) = n • m.degree f := by
  apply m.toSyn.injective
  apply le_antisymm (m.degree_pow_le n)
  apply le_degree
  rw [mem_support_iff, coeff_pow_nsmul_degree]
  exact hf

/-- Leading coefficient of powers -/
theorem leadingCoeff_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : ℕ}
    (hf : m.leadingCoeff f ^ n ≠ 0) :
    m.leadingCoeff (f ^ n) = m.leadingCoeff f ^ n := by
  rw [leadingCoeff, degree_pow_of_pow_leadingCoeff_ne_zero hf, coeff_pow_nsmul_degree]

protected theorem Monic.pow {f : MvPolynomial σ R} {n : ℕ} (hf : m.Monic f) :
    m.Monic (f ^ n) := by
  nontriviality R
  rw [Monic, leadingCoeff_pow_of_pow_leadingCoeff_ne_zero, hf.leadingCoeff_eq_one, one_pow]
  rw [hf.leadingCoeff_eq_one, one_pow]
  exact one_ne_zero

/-- Monomial degree of powers (in a reduced ring) -/
theorem degree_pow [IsReduced R] (f : MvPolynomial σ R) (n : ℕ) :
    m.degree (f ^ n) = n • m.degree f := by
  by_cases hf : f = 0
  · rw [hf, degree_zero, smul_zero]
    by_cases hn : n = 0
    · rw [hn, pow_zero, degree_one]
    · rw [zero_pow hn, degree_zero]
  nontriviality R
  apply degree_pow_of_pow_leadingCoeff_ne_zero
  apply IsReduced.pow_ne_zero
  rw [leadingCoeff_ne_zero_iff]
  exact hf

/-- Leading coefficient of powers (in a reduced ring) -/
theorem leadingCoeff_pow [IsReduced R] (f : MvPolynomial σ R) (n : ℕ) :
    m.leadingCoeff (f ^ n) = m.leadingCoeff f ^ n := by
  rw [leadingCoeff, degree_pow, coeff_pow_nsmul_degree]

theorem degree_smul_le {r : R} {f : MvPolynomial σ R} :
    m.degree (r • f) ≼[m] m.degree f := by
  rw [smul_eq_C_mul]
  apply le_of_le_of_eq degree_mul_le
  simp

theorem degree_smul {r : R} (hr : IsRegular r) {f : MvPolynomial σ R} :
    m.degree (r • f) = m.degree f := by
  by_cases hf : f = 0
  · simp [hf]
  apply m.toSyn.injective
  apply le_antisymm degree_smul_le
  apply le_degree
  simp only [mem_support_iff, smul_eq_C_mul]
  rw [← zero_add (degree m f), ← degree_C r, coeff_mul_of_degree_add]
  simp [leadingCoeff, hr.left.mul_left_eq_zero_iff, hf]

theorem degree_prod_le {ι : Type*} {P : ι → MvPolynomial σ R} {s : Finset ι} :
    m.degree (∏ i ∈ s, P i) ≼[m] ∑ i ∈ s, m.degree (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1, m.degree_C, map_zero]
  | insert a s has hrec =>
    rw [Finset.prod_insert has, Finset.sum_insert has]
    apply le_trans degree_mul_le
    simp only [map_add, add_le_add_iff_left, hrec]

theorem coeff_prod_sum_degree {ι : Type*} (P : ι → MvPolynomial σ R) (s : Finset ι) :
    coeff (∑ i ∈ s, m.degree (P i)) (∏ i ∈ s, P i) = ∏ i ∈ s, m.leadingCoeff (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has hrec =>
    simp only [Finset.prod_insert has, Finset.sum_insert has]
    rw [coeff_mul_of_add_of_degree_le (le_of_eq rfl) degree_prod_le]
    exact congr_arg₂ _ rfl hrec

-- TODO : it suffices that all leading coefficients but one are regular
theorem degree_prod_of_regular {ι : Type*}
    {P : ι → MvPolynomial σ R} {s : Finset ι} (H : ∀ i ∈ s, IsRegular (m.leadingCoeff (P i))) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, m.degree (P i) := by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff, m.coeff_prod_sum_degree]
    exact (IsRegular.prod H).ne_zero

theorem degree_prod [IsCancelMulZero R] {ι : Type*} {P : ι → MvPolynomial σ R} {s : Finset ι}
    (H : ∀ i ∈ s, P i ≠ 0) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, m.degree (P i) := by
  apply degree_prod_of_regular
  intro i hi
  apply isRegular_of_ne_zero
  rw [leadingCoeff_ne_zero_iff]
  exact H i hi

lemma degree_mul' [IsCancelMulZero R] [NoZeroDivisors R]
    {f g : MvPolynomial σ R} (hf : f * g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  rw [mul_ne_zero_iff] at hf
  exact m.degree_mul hf.1 hf.2

lemma notMem_support_of_degree_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g) :
    m.degree g ∉ f.support := by
  simp [coeff_eq_zero_of_lt h]

-- TODO : it suffices that all leading coefficients but one are regular
theorem leadingCoeff_prod_of_regular {ι : Type*}
    {P : ι → MvPolynomial σ R} {s : Finset ι} (H : ∀ i ∈ s, IsRegular (m.leadingCoeff (P i))) :
    m.leadingCoeff (∏ i ∈ s, P i) = ∏ i ∈ s, m.leadingCoeff (P i) := by
  simp only [leadingCoeff, degree_prod_of_regular H, coeff_prod_sum_degree]

/-- A product of monic polynomials is monic -/
protected theorem Monic.prod {ι : Type*} {P : ι → MvPolynomial σ R} {s : Finset ι}
    (H : ∀ i ∈ s, m.Monic (P i)) :
    m.Monic (∏ i ∈ s, P i) := by
  rw [Monic, leadingCoeff_prod_of_regular]
  · exact Finset.prod_eq_one H
  · intro i hi
    rw [(H i hi).leadingCoeff_eq_one]
    exact isRegular_one

/--
The leading term in a multivariate polynomial is zero if and only if this polynomial is zero.
-/
@[simp]
lemma leadingTerm_eq_zero_iff (p : MvPolynomial σ R) : m.leadingTerm p = 0 ↔ p = 0 := by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

/-- The leading term of the zero polynomial is zero -/
@[simp]
lemma leadingTerm_zero : m.leadingTerm (0 : MvPolynomial σ R) = 0 := by
  rw [leadingTerm_eq_zero_iff]

/--
The leading terms of non-zero polynomials within a set `B` is equal to the leading terms
of all polynomials in B, excluding zero.
-/
lemma image_leadingTerm_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
    m.leadingTerm '' (B \ {0}) = (m.leadingTerm '' B) \ {0} := by
  ext x : 1
  simp_all only [Set.mem_image, Set.mem_diff, Set.mem_singleton_iff, ne_eq]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨left, right_1⟩ := left
    subst right
    simp_all only [leadingTerm_eq_zero_iff, not_false_eq_true, and_true]
    apply Exists.intro
    · apply And.intro
      on_goal 2 => { rfl
      }
      · simp_all only
  · intro a
    obtain ⟨left, right⟩ := a
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    subst right_1
    simp_all only [leadingTerm_eq_zero_iff]
    apply Exists.intro
    · apply And.intro
      on_goal 2 => { rfl
      }
      · simp_all only [not_false_eq_true, and_self]

/--
The leading terms of a Set `B` inserted zero polynomial equal to leading terms of `B`
inserted zero polynomial
-/
lemma image_leadingTerm_insert_zero (B : Set (MvPolynomial σ R)) :
    m.leadingTerm '' (insert (0 : MvPolynomial σ R) B) = insert 0 (m.leadingTerm '' B) := by
  aesop

/-- The degree of `f` equals to the degree of `leadingTerm f` -/
@[simp]
lemma degree_leadingTerm (f : MvPolynomial σ R) :
    m.degree (m.leadingTerm f) = m.degree f := by
  classical
  -- simp? [leadingTerm, degree_monomial]
  simp only [leadingTerm, degree_monomial, leadingCoeff_eq_zero_iff, ite_eq_right_iff]
  simp_intro h

@[simp]
lemma leadingCoeff_leadingTerm (f : MvPolynomial σ R) :
    m.leadingCoeff (m.leadingTerm f) = m.leadingCoeff f := by
  simp [leadingTerm, leadingCoeff_monomial]

end Semiring

section Ring

variable {R : Type*} [CommRing R]

variable (m) in
/-- The S-polynomial of two polynomials -/
noncomputable def sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g

@[simp]
theorem degree_neg {f : MvPolynomial σ R} :
    m.degree (-f) = m.degree f := by
  unfold degree
  rw [support_neg]

@[simp]
theorem leadingCoeff_neg {f : MvPolynomial σ R} :
    m.leadingCoeff (-f) = - m.leadingCoeff f := by
  simp only [leadingCoeff, degree_neg, coeff_neg]

theorem degree_sub_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f - g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  rw [sub_eq_add_neg]
  apply le_of_le_of_eq m.degree_add_le
  rw [degree_neg]

theorem degree_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f - g) = m.degree f := by
  rw [sub_eq_add_neg]
  apply degree_add_of_lt
  simp only [degree_neg, h]

theorem leadingCoeff_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.leadingCoeff (f - g) = m.leadingCoeff f := by
  rw [sub_eq_add_neg]
  apply leadingCoeff_add_of_lt
  simp only [degree_neg, h]

theorem degree_sub_leadingTerm_le (f : MvPolynomial σ R) :
    m.degree (f - m.leadingTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp [degree_leadingTerm]

theorem degree_sub_leadingTerm (f : MvPolynomial σ R) :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f ∨ f - m.leadingTerm f = 0 := by
  classical
  rw [or_iff_not_imp_right]
  intro h
  apply lt_of_le_of_ne (m.degree_sub_leadingTerm_le f) ?_
  simp_intro h'
  apply m.degree_mem_support at h
  rw [h', mem_support_iff] at h
  simp [leadingTerm, leadingCoeff] at h

theorem degree_sub_leadingTerm_lt_degree {f : MvPolynomial σ R} (h : f - m.leadingTerm f ≠ 0) :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f :=
  (or_iff_left h).mp <| m.degree_sub_leadingTerm f

theorem degree_sub_leadingTerm_lt_iff {f : MvPolynomial σ R} :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f ↔ m.degree f ≠ 0 := by
  constructor
  · intro h h'
    -- simp? [h'] at h
    simp only [h', map_zero] at h
    exact not_lt_bot h
  · intro h
    by_cases hl : f - m.leadingTerm f = 0
    · simpa [hl, toSyn_lt_iff_ne_zero]
    · exact m.degree_sub_leadingTerm_lt_degree hl

lemma sPolynomial_antisymm (f g : MvPolynomial σ R) :
    m.sPolynomial f g = - m.sPolynomial g f :=
  Eq.symm (neg_sub (_ * g) (_ * f))

@[simp]
lemma sPolynomial_left_zero (g : MvPolynomial σ R) :
    m.sPolynomial 0 g = 0 := by
  simp [sPolynomial]

@[simp]
lemma sPolynomial_right_zero (f : MvPolynomial σ R) :
    m.sPolynomial f 0 = 0 := by
  rw [sPolynomial_antisymm, sPolynomial_left_zero, neg_zero]

lemma sPolynomial_def (f g : MvPolynomial σ R) :
    m.sPolynomial f g =
      monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff g) * f -
      monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff f) * g := by
  unfold sPolynomial
  congr 4
  all_goals
    rw [Finsupp.ext_iff]
    simp_intro a
    by_cases h : (m.degree f) a ≤ (m.degree g) a
    ·simp [h]
    ·simp [le_of_lt (not_le.mp h)]

@[simp]
lemma sPolynomial_self (f : MvPolynomial σ R) : m.sPolynomial f f = 0 := sub_self _

lemma degree_sPolynomial_le (f g : MvPolynomial σ R) :
    ((m.degree <| m.sPolynomial f g) ≼[m] m.degree f ⊔ m.degree g) := by
  classical
  by_cases hf_zero: f = 0
  · simp [hf_zero]
  by_cases hg_zero: g = 0
  · simp [hg_zero]
  simp [sPolynomial_def]
  calc
    _ ≤ _ ⊔ _ := degree_sub_le
    _ ≤  m.toSyn (m.degree _ + m.degree _) ⊔ m.toSyn (m.degree _ + m.degree _) :=
      sup_le_sup degree_mul_le degree_mul_le
    _ ≤ (m.toSyn <| m.degree f ⊔ m.degree g - m.degree f + m.degree f) ⊔
          (m.toSyn <| m.degree f ⊔ m.degree g - m.degree g + m.degree g) := by
      simp_rw [degree_monomial]
      simp [hg_zero, hf_zero]
    _ ≤ m.toSyn (m.degree f ⊔ m.degree g) := by
      simp
      constructor
      all_goals
        apply le_of_eq
        simp_rw [← AddEquiv.map_add, (AddEquiv.injective m.toSyn).eq_iff, Finsupp.ext_iff]
        intro a
        exact Nat.sub_add_cancel <| by simp

lemma coeff_sPolynomial_sup_eq_zero (f g : MvPolynomial σ R) :
    (m.sPolynomial f g).coeff (m.degree f ⊔ m.degree g) = 0 := by
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hg0 : g = 0
  · simp [hg0]
  classical
  rw [sPolynomial_def, coeff_sub]
  have : m.degree f ⊔ m.degree g = m.degree f ⊔ m.degree g - m.degree f + m.degree f := by
    rw [Finsupp.ext_iff]
    exact fun _ ↦ (Nat.sub_add_cancel <| by simp).symm
  nth_rewrite 1 [this, coeff_monomial_mul]
  have : m.degree f ⊔ m.degree g = m.degree f ⊔ m.degree g - m.degree g + m.degree g := by
    rw [Finsupp.ext_iff]
    exact fun _ ↦ (Nat.sub_add_cancel <| by simp).symm
  nth_rewrite 1 [this, coeff_monomial_mul]
  unfold leadingCoeff
  ring

lemma degree_sPolynomial (f g : MvPolynomial σ R) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g ∨ m.sPolynomial f g = 0 := by
  classical
  by_cases hf : m.degree f = 0 ∧ m.degree g = 0
  · rcases hf with ⟨h₁, h₂⟩
    right
    simp [sPolynomial_def, h₁, h₂]
    nth_rewrite 1 [degree_eq_zero_iff.mp h₁]
    nth_rewrite 2 [degree_eq_zero_iff.mp h₂]
    ring
  · by_cases hs: m.sPolynomial f g = 0
    · simp [hs]
    by_cases hf_zero: f = 0
    · simp [hf_zero]
    by_cases hg_zero: g = 0
    · simp [hg_zero]
    left
    have h1: m.toSyn (m.degree (m.sPolynomial f g)) ≤  m.toSyn (m.degree f ⊔ m.degree g) :=
      m.degree_sPolynomial_le f g
    have h3: m.toSyn (m.degree (m.sPolynomial f g)) ≠ m.toSyn (m.degree f ⊔ m.degree g) := by
      simp
      by_contra h
      have: coeff (m.degree (m.sPolynomial f g)) (m.sPolynomial f g) ≠ 0 :=
        coeff_degree_ne_zero_iff.mpr hs
      rw [h] at this
      exact this (m.coeff_sPolynomial_sup_eq_zero _ _)
    exact lt_of_le_of_ne h1 h3

lemma degree_sPolynomial_lt_sup_degree {f g : MvPolynomial σ R} (h : m.sPolynomial f g ≠ 0) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g :=
  (or_iff_left h).mp <| m.degree_sPolynomial f g

lemma sPolynomial_lt_of_degree_ne_zero_of_degree_eq {f g : MvPolynomial σ R}
    (h : m.degree f = m.degree g) (hs : m.sPolynomial f g ≠ 0) :
    m.degree (m.sPolynomial f g) ≺[m] m.degree f := by
  convert m.degree_sPolynomial f g
  simp [h, hs]

lemma sPolynomial_mul_monomial [IsCancelMulZero R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial ((monomial d₁ c₁) * p₁) ((monomial d₂ c₂) * p₂) =
      monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  simp only [sPolynomial_def]
  by_cases hc1 : c₁ = 0
  · by_cases hc2 : c₂ = 0 <;> simp [hc1, hc2]
  by_cases hc2 : c₂ = 0
  · simp [hc2]
  by_cases hp1 : p₁ = 0
  · simp [hp1]
  by_cases hp2 : p₂ = 0
  · simp [hp2]
  have hm1 := (monomial_eq_zero (s:=d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s:=d₂)).not.mpr hc2
  simp_rw [m.degree_mul hm1 hp1, m.degree_mul hm2 hp2,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul,
    m.leadingCoeff_mul hm1 hp1, m.leadingCoeff_mul hm2 hp2, m.leadingCoeff_monomial,
    degree_monomial]
  simp [hc1, hc2]
  congr 2
  all_goals
    congr 1
    · congr 1
      simp [Finsupp.ext_iff]
      intro a
      rw [Nat.sub_add_sub_cancel (by rw [Nat.max_le]; simp) (by simp)]
      rw [← Nat.sub_add_comm (by simp)]
      nth_rewrite 3 [add_comm _ <| (m.degree _) a]
      rw [Nat.add_sub_add_right]
    · ring

lemma sPolynomial_decomposition {d : m.syn} {ι : Type*}
    {B : Finset ι} {g : ι → MvPolynomial σ R}
    (hd : ∀ b ∈ B,
      (m.toSyn <| m.degree <| g b) = d ∧ IsUnit (m.leadingCoeff <| g b) ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → R),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb h =>
    by_cases hb0 : g b = 0
    · simp [Finset.sum_insert hb, hb0] at hd hfd ⊢
      exact h hd hfd
    simp [Finset.sum_insert hb, hb0] at hfd hd
    obtain ⟨⟨deg_gb_eq_d, isunit_gb⟩, hd⟩ := hd
    use fun b₁ b₂ ↦ if b₂ = b then ↑isunit_gb.unit⁻¹ else 0
    simp [Finset.sum_insert hb, hb]
    simp [← deg_gb_eq_d] at *
    clear d
    trans ∑ b' ∈ B, (g b' - (m.leadingCoeff (g b') * ↑isunit_gb.unit⁻¹) • g b)
    · rw [Finset.sum_sub_distrib, add_comm, sub_eq_add_neg,
        ← Finset.sum_smul, ← Finset.sum_mul, ← neg_smul]
      nth_rewrite 1 [← one_smul R <| g b]
      congr
      rw [← neg_mul, eq_comm]
      convert isunit_gb.mul_val_inv
      rw [← add_eq_zero_iff_neg_eq']
      trans (g b).coeff (m.degree <| g b) + ∑ i ∈ B, (g i).coeff (m.degree <| g b)
      · unfold leadingCoeff
        congr 1
        apply Finset.sum_congr rfl
        intro b' hb'
        rcases hd b' hb' with h | h <;> simp [h]
      · rw [← coeff_sum, ← coeff_add, ← notMem_support_iff]
        exact m.notMem_support_of_degree_lt hfd
    · apply Finset.sum_congr rfl
      intro b' hb'
      rw [sPolynomial]
      by_cases h : g b' = 0
      · simp [h]
      have := hd b' hb'
      simp [h] at this
      simp [this, smul_eq_C_mul, mul_sub, ← mul_assoc _ _ (g b), ← mul_assoc _ _ (g b'),]
      simp_rw [← C_mul]
      simp [mul_comm]

end Ring

section Field

variable {R : Type*} [Field R]

theorem isUnit_leadingCoeff {f : MvPolynomial σ R} :
    IsUnit (m.leadingCoeff f) ↔ f ≠ 0 := by
  simp only [isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff]

lemma sPolynomial_decomposition' {d : m.syn} {ι : Type*}
    {B : Finset ι} (g : ι → MvPolynomial σ R)
    (hd : ∀ b ∈ B, (m.toSyn <| m.degree <| g b) = d ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → R),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  refine m.sPolynomial_decomposition ?_ hfd
  simpa [and_or_right, em']

end Field

section Binomial

variable {R : Type*} [CommRing R]

open Finsupp MvPolynomial

lemma degree_X_add_C [Nontrivial R]
    {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.degree (X i + C r) = single i 1 := by
  rw [degree_add_of_lt, degree_X]
  simp only [degree_C, map_zero, degree_X]
  rw [← bot_eq_zero, bot_lt_iff_ne_bot, bot_eq_zero, ← map_zero m.toSyn]
  simp

lemma degree_X_sub_C [Nontrivial R]
    {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.degree (X i - C r) = single i 1 := by
  rw [sub_eq_add_neg, ← map_neg, degree_X_add_C]

lemma monic_X_add_C {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.Monic (X i + C r) := by
  nontriviality R
  apply monic_X.add_of_lt
  simp [degree_C, degree_X, ← not_le, ← eq_zero_iff]

lemma monic_X_sub_C {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.Monic (X i - C r) := by
  rw [sub_eq_add_neg, ← map_neg]
  apply monic_X_add_C

end Binomial

end MonomialOrder
/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

/-!
# Lemmas about ideals of `MvPolynomial`

Notably this contains results about monomial ideals.

## Main results

* `MvPolynomial.mem_ideal_span_monomial_image`
* `MvPolynomial.mem_ideal_span_X_image`
-/


variable {σ R : Type*}

namespace MvPolynomial

variable [CommSemiring R]

/-- `x` is in a monomial ideal generated by `s` iff every element of its support dominates one of
the generators. Note that `si ≤ xi` is analogous to saying that the monomial corresponding to `si`
divides the monomial corresponding to `xi`. -/
theorem mem_ideal_span_monomial_image {x : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    x ∈ Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔ ∀ xi ∈ x.support, ∃ si ∈ s, si ≤ xi := by
  refine AddMonoidAlgebra.mem_ideal_span_of'_image.trans ?_
  simp_rw [le_iff_exists_add, add_comm]
  rfl

theorem mem_ideal_span_monomial_image_iff_dvd {x : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    x ∈ Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔
      ∀ xi ∈ x.support, ∃ si ∈ s, monomial si 1 ∣ monomial xi (x.coeff xi) := by
  refine mem_ideal_span_monomial_image.trans (forall₂_congr fun xi hxi => ?_)
  simp_rw [monomial_dvd_monomial, one_dvd, and_true, mem_support_iff.mp hxi, false_or]

/-- `x` is in a monomial ideal generated by variables `X` iff every element of its support
has a component in `s`. -/
theorem mem_ideal_span_X_image {x : MvPolynomial σ R} {s : Set σ} :
    x ∈ Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial σ R)) ↔
      ∀ m ∈ x.support, ∃ i ∈ s, (m : σ →₀ ℕ) i ≠ 0 := by
  have := @mem_ideal_span_monomial_image σ R _ x ((fun i => Finsupp.single i 1) '' s)
  rw [Set.image_image] at this
  refine this.trans ?_
  simp [Nat.one_le_iff_ne_zero]

end MvPolynomial

namespace MonomialOrder

variable [CommSemiring R] {m : MonomialOrder σ}
open Ideal

lemma span_leadingTerm_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
    span (m.leadingTerm '' (B \ {0})) = span (m.leadingTerm '' B) :=
  m.image_leadingTerm_sdiff_singleton_zero B ▸ Ideal.span_sdiff_singleton_zero

lemma span_leadingTerm_insert_zero (B : Set (MvPolynomial σ R)) :
    span (m.leadingTerm '' (insert 0 B)) = span (m.leadingTerm '' B) := by
  by_cases h : 0 ∈ B
  · rw [Set.insert_eq_of_mem h]
  · simp [image_leadingTerm_insert_zero]

lemma span_leadingTerm_eq_span_monomial {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p)) :
    span (m.leadingTerm '' B) =
      span ((fun p ↦ MvPolynomial.monomial (m.degree p) (1 : R)) '' B) := by
  classical
  apply le_antisymm
  all_goals
    rintro p hl
    simp_rw [MonomialOrder.leadingTerm, ← submodule_span_eq,
      Submodule.mem_span_image_iff_exists_fun] at *
    rcases hl with ⟨t, ht, c, hc⟩
    rw [←hc]
    use t
  · split_ands
    · exact ht
    · use fun p ↦ (MvPolynomial.C (m.leadingCoeff ↑p : R) : MvPolynomial σ R) • c ↑p
      apply Finset.sum_congr rfl
      -- simp?
      simp only [Finset.univ_eq_attach, Finset.mem_attach, smul_eq_mul, forall_const,
        Subtype.forall]
      intro a ha
      rw [mul_assoc, mul_left_comm, MvPolynomial.C_mul_monomial, mul_one]
  · split_ands
    · exact ht
    · use fun p ↦ if hp : ↑p ∈ B then ((hB (↑p) (hp)).unit)⁻¹ • c ↑p else 0
      apply Finset.sum_congr rfl
      · -- simp?
        simp only [Finset.univ_eq_attach, Finset.mem_attach, smul_eq_mul, dite_mul, zero_mul,
        forall_const, Subtype.forall]
        intro a ha
        simp [Set.mem_of_mem_of_subset ha ht, smul_mul_assoc, ←mul_smul_comm,
          MvPolynomial.smul_monomial, IsUnit.inv_smul]

lemma span_leadingTerm_eq_span_monomial₀ {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0) :
    span (m.leadingTerm '' B) =
    span ((fun p ↦ MvPolynomial.monomial (m.degree p) 1) '' (B \ {0})) := by
  calc
    _ = span (m.leadingTerm '' B \ {0}) := Ideal.span_sdiff_singleton_zero.symm
    _ = span (m.leadingTerm '' (B \ {0})) := by rw [m.image_leadingTerm_sdiff_singleton_zero]
    _ = _ := by
      apply span_leadingTerm_eq_span_monomial
      simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

lemma span_leadingTerm_eq_span_monomial' {k : Type*} [Field k] {B : Set (MvPolynomial σ k)} :
    span (m.leadingTerm '' B) =
    span ((fun p ↦ MvPolynomial.monomial (m.degree p) 1) '' (B \ {0})) := by
  apply span_leadingTerm_eq_span_monomial₀
  simp [em']

lemma sPolynomial_mem_ideal {R : Type*} [CommRing R]
    {I : Ideal <| MvPolynomial σ R} {p q : MvPolynomial σ R}
    (hp : p ∈ I) (hq : q ∈ I) : m.sPolynomial p q ∈ I :=
  sub_mem (mul_mem_left I _ hp) (mul_mem_left I _ hq)

end MonomialOrder
namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

section CommSemiring
variable {σ : Type*} (m : MonomialOrder σ)

variable {R : Type*} [CommSemiring R]
variable (f p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)

/--
Given a multivariate polynomial `f` and a set `B` of
  multivariate polynomials over a commutative semiring `R`, with respect to a monomial order `m`.
  A polynomial `r` is called a remainder of `f` on division by `B` if there exists:
  (1) A finite linear combination:
   `f = ∑ (g(b) * b) + r` where `g : B →₀ R[X]` (finitely supported coefficients).
  (2) Degree condition:
   For each `b ∈ B`, the degree of `g(b) * b` is ≤ the degree of `f` under `m`.
  (3) Remainder irreducibility:
   No term of `r` is divisible by the leading monomial of any non-zero `b ∈ B`.
-/
def IsRemainder :=
  (∃ (g : B →₀ MvPolynomial σ R),
    f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
    ∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)

/--
A variant of `MonomialOrder.IsRemainder` without coercion of a `Set (MvPolynomial σ R)`.
-/
theorem isRemainder_def' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
        ↑g.support ⊆ B ∧
        p = Finsupp.linearCombination _ id g + r ∧
        ∀ b ∈ B, m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree p) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  classical
  constructor
  · intro ⟨⟨g, h₁, h₂⟩, h₃⟩
    split_ands
    · use g.mapDomain Subtype.val
      split_ands
      · exact subset_trans (Finset.coe_subset.mpr Finsupp.mapDomain_support) (by simp)
      · simp [h₁]
      · intro b hb
        rw [show b = ↑(Subtype.mk b hb) by rfl, Finsupp.mapDomain_apply (by simp)]
        exact h₂ ⟨b, hb⟩
    · exact h₃
  · intro ⟨⟨g, hg, h₁, h₂⟩, h₃⟩
    split_ands
    · use {
        support := (g.support.subtype (· ∈ B)),
        toFun := (g.toFun ·),
        mem_support_toFun := by intro; simp; rfl
      }
      split_ands
      · rw [h₁, eq_comm]
        congr 1
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
        apply Finset.sum_nbij (↑·)
        · simp_intro ..
        · simp_intro b _ b₁ _ h [Subtype.eq_iff]
        · simp_intro b hb
          exact Set.mem_of_subset_of_mem hg <| Finsupp.mem_support_iff.mpr hb
        · simp [DFunLike.coe]
      · simpa
    · exact h₃

/--
A variant of `MonomialOrder.IsRemainder` where `g : MvPolynomial σ R →₀ MvPolynomial σ R` is
replaced with a function `g : MvPolynomial σ R → MvPolynomial σ R` without limitation on its
support.
-/
theorem isRemainder_def'' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) :
      m.IsRemainder p B r ↔
        (∃ (g : MvPolynomial σ R → MvPolynomial σ R) (B' : Finset (MvPolynomial σ R)),
          ↑B' ⊆ B ∧
          p = B'.sum (fun x => g x * x) + r ∧
          ∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c) := by
  classical
  rw [isRemainder_def']
  constructor
  · intro ⟨⟨g, h₁, h₂, h₃⟩, h₄⟩
    refine ⟨?_, h₄⟩
    use g.toFun, g.support
    refine ⟨h₁, by rwa [Finsupp.linearCombination_apply, Finsupp.sum] at h₂, ?_⟩
    intro g' hg'
    exact h₃ g' (Set.mem_of_mem_of_subset hg' h₁)
  · intro ⟨⟨g, B', h₁, h₂, h₃⟩, h₄⟩
    split_ands
    · use Finsupp.onFinset B' (fun b' => if b' ∈ B' then g b' else 0) (by simp_intro ..)
      split_ands
      · simp_intro b' hb'
        exact Set.mem_of_mem_of_subset hb'.1 h₁
      · rw [Finsupp.linearCombination_apply, Finsupp.sum, h₂, Finsupp.support_onFinset]
        congr 1
        simp [Finset.filter_and, Finset.filter_mem_eq_inter,
          Finset.inter_self, Finset.inter_filter, Finset.filter_inter]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b' _
        by_cases hb' : g b' = 0 <;> simp [hb']
      · intro b hb
        by_cases hbB' : b ∈ B'
        · simp [hbB', h₃]
        · simp [hbB']
    · exact h₄

/--
A variant of `MonomialOrder.IsRemainder_def'` where `B` is `Finset (MvPolynomial σ R)`.
-/
theorem isRemainder_finset (p : MvPolynomial σ R) (B' : Finset (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        ∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  classical
  constructor
  · rw [isRemainder_def']
    intro ⟨⟨g, hgsup, hsum, hg⟩, hr⟩
    split_ands
    · use g.toFun
      split_ands
      · simp [Finsupp.linearCombination_apply, Finsupp.sum] at hsum
        rw [hsum]
        congr 1
        apply Finset.sum_subset hgsup
        simp_intro ..
      · exact hg
    · exact hr
  · rw [isRemainder_def'']
    intro ⟨⟨g, hsum, hg⟩, hr⟩
    refine ⟨?_, hr⟩
    use fun b' ↦ if b' ∈ B' then g b' else 0
    use B'
    split_ands
    · rfl
    · simp [hsum]
    · simp_intro .. [hg]

/-- `r` is a remainder of a family of polynomials, if and only if it is a remainder with properities
defined in `MonomialOrder.div` with this family of polynomials given as a map from indexes to them.

It is a variant of `MonomialOrder.IsRemainder` where divisors are given as a map from indexes to
polynomials. -/
theorem isRemainder_range {ι : Type*} (f : MvPolynomial σ R)
    (b : ι → MvPolynomial σ R) (r : MvPolynomial σ R) :
    m.IsRemainder f (Set.range b) r ↔
      (∃ g : ι →₀ MvPolynomial σ R,
        f = Finsupp.linearCombination _ b g + r ∧
        ∀ i : ι, m.degree (b i * g i) ≼[m] m.degree f) ∧
      ∀ c ∈ r.support, ∀ i : ι, b i ≠ 0 → ¬ (m.degree (b i) ≤ c) := by
  classical
  constructor
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    let idx : (↑(Set.range b)) ↪ ι := {
      toFun := Set.rangeSplitting b,
      inj' := Set.rangeSplitting_injective b
    }
    split_ands
    · use Finsupp.embDomain idx g
      split_ands
      · ext
        simp [h₁, Finsupp.linearCombination_apply, Finsupp.sum]
        congr
        simp [idx, Set.apply_rangeSplitting]
      · intro i
        specialize h₂ ⟨b i, Set.mem_range_self i⟩
        simp at h₂
        by_cases h' : (Finsupp.embDomain idx g) i = 0
        · simp [h']
        simp at h'
        convert h₂
        generalize_proofs hbi
        convert_to g.embDomain idx (hbi.choose) = _
        · simp [Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain, Finsupp.single_apply] at ⊢ h'
          congr
          ext
          congr
          obtain ⟨a, ha, ha'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
          simp [idx] at ha'
          convert_to i = Set.rangeSplitting b ⟨b i, hbi⟩
          simp [← ha'.1, Set.apply_rangeSplitting]
        · exact Finsupp.embDomain_apply idx g ⟨b i, hbi⟩
    · intro i hi b hb
      aesop
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    refine ⟨?_, ?_⟩
    · let b_support : Finset (Set.range b) :=
        (g.support.biUnion fun i ↦
          {⟨b i, Set.mem_range_self i⟩})
      let b' : ι → Set.range b := fun i ↦ ⟨b i, Set.mem_range_self i⟩
      let g' : Set.range b → MvPolynomial σ R := fun x ↦
         Finset.sum (g.support.filter fun i ↦ b' i = x) fun i ↦ g i
      have mem_support : ∀ x, g' x ≠ 0 → x ∈ b_support := by
        intro x hx
        obtain ⟨i, hi, hb'x⟩ : ∃ i ∈ g.support, b' i = x := by
          contrapose! hx
          simp [g']
          rw [Finset.sum_filter]
          suffices (g.support.filter (fun i => b' i = x)) = ∅ by
            rw [← Finset.sum_filter, this, Finset.sum_empty]
          ext i
          simp at hx
          simp
          exact hx i
        simp [b_support, Finset.mem_biUnion]
        use i
        constructor
        · exact Finsupp.mem_support_iff.mp hi
        · exact hb'x.symm
      use Finsupp.onFinset b_support g' mem_support
      split_ands
      · simp [h₁, Finsupp.linearCombination_apply, Finsupp.sum]
        congr
        calc
          ∑ x ∈ g.support, g x * b x
            = ∑ x ∈ g.support, g x * (b' x : MvPolynomial σ R) := by rfl
          _ = ∑ y ∈ Finset.image b' g.support,
              (∑ x ∈ g.support.filter (b' · = y), g x) * (y : MvPolynomial σ R) := by
            rw [Finset.sum_image']
            intro y hy
            rw [Finset.sum_filter]
            ext x
            congr
            calc
              (∑ a ∈ g.support, if b' a = b' y then g a else 0) * ↑(b' y) =
                  (∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j) * ↑(b' y) := by
                congr 1
                simp [Finset.sum_filter]
              _ = ∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j * ↑(b' y) :=
                Finset.sum_mul {j ∈ g.support | b' j = b' y} ⇑g ↑(b' y)
              _ = ∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j * ↑(b' j) := by
                apply Finset.sum_congr rfl
                intro j hj
                congr 2
                exact (Finset.mem_filter.mp hj).2.symm
          _ = ∑ y ∈ Finset.image b' g.support, g' y * (y : MvPolynomial σ R) := by rfl
          _ = ∑ y ∈ b_support, g' y * (y : MvPolynomial σ R) := by
            congr
            ext y
            simp [b_support, Eq.comm (a:=y), b']
          _ = ∑ x ∈ (Finsupp.onFinset b_support g' mem_support).support, g' x * ↑x := by
            rw [Finsupp.support_onFinset, Finset.sum_filter]
            congr
            ext x
            by_cases hx : g' x = 0 <;> simp [hx]
      · intro b1
        simp [Finsupp.onFinset, g']
        rw [Finset.mul_sum]
        have sum_eq : (∑ i ∈ g.support.filter (fun i => b' i = b1), ↑b1 * g i) =
            (∑ i ∈ g.support.filter (fun i => b' i = b1), b i * g i) := by
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [Finset.mem_filter] at hi
          congr
          exact Subtype.eq_iff.mp hi.2.symm
        rw [sum_eq]
        have degree_le : ∀ i ∈ g.support.filter (fun i => b' i = b1),
            m.degree (b i * g i) ≼[m] m.degree f := by
          intro i hi
          rw [Finset.mem_filter] at hi
          exact h₂ i
        trans (g.support.filter fun i ↦ b' i = b1).sup fun i ↦ m.toSyn (m.degree (b i * g i))
        · exact m.degree_sum_le
        · exact Finset.sup_le (fun i hi ↦ degree_le i hi)
    · aesop

/--
Remainders are preserved on insertion of the zero polynomial into the set of divisors.
-/
@[simp]
theorem isRemainder_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
    (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p (insert 0 B) r ↔ m.IsRemainder p B r := by
  classical
  constructor
  · by_cases hB : 0 ∈ B
    · simp [hB]
    simp_rw [isRemainder_def'']
    intro ⟨⟨g, B', hB', h₁, h₂⟩, h₃⟩
    split_ands
    · use g, (B'.erase 0)
      split_ands
      · simp [hB']
      · rw [h₁]
        congr 1
        by_cases hB'0 : 0 ∈ B'
        · nth_rw 1 [← Finset.insert_erase hB'0]
          rw [Finset.sum_insert_zero (a:=0)]
          simp
        · rw [Finset.erase_eq_self.mpr hB'0]
      · simp_intro b' hb'
        exact h₂ b' hb'.2
    · intro c hc b hbB hb
      exact h₃ c hc b (by simp [hbB]) hb
  · rw [isRemainder_def', isRemainder_def']
    intro ⟨⟨g, hg, h₁, h₂⟩, h₃⟩
    split_ands
    · use g
      split_ands
      · exact subset_trans hg (Set.subset_insert _ _)
      · exact h₁
      · intro b hb
        by_cases hb0 : b = 0
        · simp [hb0]
        · exact h₂ b ((Set.mem_insert_iff.mp hb).resolve_left hb0)
    · intro c hc b hb hbne0
      exact h₃ c hc b ((Set.mem_insert_iff.mp hb).resolve_left hbne0) hbne0

/--
Remainders are preserved with the zero polynomial removed from the set of divisors.
-/
@[simp]
theorem isRemainder_sdiff_singleton_zero_iff_isRemainder (p : MvPolynomial σ R)
  (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (B \ {0}) r ↔ m.IsRemainder p B r := by
  by_cases h : 0 ∈ B
  · rw [←isRemainder_insert_zero_iff_isRemainder, show insert 0 (B \ {0}) = B by simp [h]]
  · simp [h]

variable {m B} in
theorem isRemainder_zero {r : MvPolynomial σ R} (hB : ∀ b ∈ B, IsRegular (m.leadingCoeff b))
    (h : m.IsRemainder 0 B r) : r = 0 := by
  unfold IsRemainder at h
  obtain ⟨⟨g, h0sumg, hg⟩, hr⟩ := h
  conv at hg =>
    intro b
    simp
    rw [← m.eq_zero_iff, AddEquiv.map_eq_zero_iff, mul_comm]
  simp [Finsupp.linearCombination_apply, Finsupp.sum] at h0sumg
  have rdeg0 : m.degree r = 0 := by
    apply congrArg m.degree at h0sumg
    contrapose! h0sumg
    simp [-ne_eq]
    rw [ne_comm, ← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero, add_comm]
    rw [← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero] at h0sumg
    rwa [degree_add_of_lt]
    apply lt_of_le_of_lt m.degree_sum_le
    simp [hg]
    exact lt_of_le_of_lt Finset.sup_const_le h0sumg
  contrapose! hr
  use 0
  split_ands
  · rw [m.degree_eq_zero_iff.mp rdeg0]; simp [hr]
  contrapose! h0sumg
  simp at h0sumg
  suffices ∀ b : B, g b * ↑b = 0 by simp [this, hr.symm]
  intro b
  suffices g b = 0 ∨ b.1 = 0 by by_cases h : g b = 0; simp [h]; simp [this.resolve_left h]
  rw [or_iff_not_imp_right]
  intro hb
  specialize hg b
  specialize h0sumg b b.2 hb
  contrapose! hg
  rw [m.degree_mul_of_isRegular_right hg <| hB ↑b (by simp)]
  simp [h0sumg]

variable {m B} in
theorem isRemainder_zero₀ {r : MvPolynomial σ R}
    (hB : ∀ b ∈ B, IsRegular (m.leadingCoeff b) ∨ b = 0) (h : m.IsRemainder 0 B r) : r = 0 := by
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine m.isRemainder_zero ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

variable {m B} in
theorem isRemainder_zero' [IsCancelMulZero R] {r : MvPolynomial σ R} (h : m.IsRemainder 0 B r) :
    r = 0 := by
  refine isRemainder_zero₀ ?_ h
  intro b _
  rw [or_iff_not_imp_right]
  intro hb
  exact isRegular_of_ne_zero <| leadingCoeff_ne_zero_iff.mpr hb

variable {m} in
theorem isRemainder_finset₁ (p : MvPolynomial σ R) {B' : Finset (MvPolynomial σ R)}
    (hB' : ∀ b' ∈ B', IsRegular (m.leadingCoeff b'))
    (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero hB' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

variable {m} in
theorem isRemainder_finset₀₁ (p : MvPolynomial σ R) {B' : Finset (MvPolynomial σ R)}
    (hB' : ∀ b' ∈ B', IsRegular (m.leadingCoeff b') ∨ b' = 0)
    (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero₀ hB' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

variable {m} in
theorem isRemainder_finset'₁ [IsCancelMulZero R] (p : MvPolynomial σ R)
    (B' : Finset (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

theorem isRemainder_def'₁ [IsCancelMulZero R] (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
        ↑g.support ⊆ B ∧
        p = Finsupp.linearCombination _ id g + r ∧
        ∀ b ∈ B, m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree p ∧
        (p = 0 → g = 0)) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  by_cases h : p ≠ 0
  · simp [isRemainder_def', h]
  push_neg at h
  rw [h]
  constructor
  · intro h'
    simp [isRemainder_zero' h']
    use 0
    simp
  · intro h'
    rw [isRemainder_def']
    subst h
    simp_all only [degree_zero, map_zero, forall_const,
     mem_support_iff, ne_eq, not_false_eq_true, implies_true,
      and_true]
    obtain ⟨left, right⟩ := h'
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    obtain ⟨left_1, right_1⟩ := right_1
    simp_all only
    apply Exists.intro
    · apply And.intro
      on_goal 2 => apply And.intro
      on_goal 2 => { rfl
      }
      · simp_all only
      · intro b a
        simp_all only

variable {m} in
lemma mem_ideal_of_isRemainder_of_mem_ideal {B : Set (MvPolynomial σ R)} {r : MvPolynomial σ R}
    {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) (hr : r ∈ I) :
    p ∈ I := by
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  rw [h_eq]
  refine Ideal.add_mem _ ?_ hr
  rw [Finsupp.linearCombination_apply]
  apply Ideal.sum_mem
  exact fun _ _ ↦ Ideal.mul_mem_left _ _ (Set.mem_of_mem_of_subset (by simp) hBI)

variable {m} in
lemma term_notMem_span_leadingTerm_of_isRemainder {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)} (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  intro s hs
  rw [span_leadingTerm_eq_span_monomial hB, ← Set.image_image (monomial · 1) _ _,
    mem_ideal_span_monomial_image]
  have h1ne0: (1 : R) ≠ 0 := by
    by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff s, h1eq0, mul_zero] at hs
    exact hs rfl
  simp [MvPolynomial.mem_support_iff.mp hs]
  intro b hb
  unfold MonomialOrder.IsRemainder at h
  apply h.2 s hs b hb
  by_contra hq0
  specialize hB b hb
  simp [hq0, h1ne0.symm] at hB

variable {m} in
lemma term_notMem_span_leadingTerm_of_isRemainder₀ {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  rw [← span_leadingTerm_sdiff_singleton_zero]
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine m.term_notMem_span_leadingTerm_of_isRemainder ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

variable {m} in
lemma monomial_notMem_span_leadingTerm {r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : ∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  intro s hs
  rw [span_leadingTerm_eq_span_monomial hB,
      ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
  simp
  split_ands
  · by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff s, h1eq0, mul_zero] at hs
    exact hs rfl
  · intro b hb
    exact h s hs b hb

variable {m} in
lemma monomial_notMem_span_leadingTerm_of_isRemainder {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  apply monomial_notMem_span_leadingTerm hB
  intro c hc b hb
  have : Nontrivial R := by
    rw [nontrivial_iff_exists_ne 0]
    use 1
    by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff c, h1eq0, mul_zero] at hc
    exact hc rfl
  refine h.2 c hc b hb (m.leadingCoeff_ne_zero_iff.mp (hB _ hb).ne_zero)

variable {m} in
lemma monomial_notMem_span_leadingTerm_of_isRemainder₀ {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [← span_leadingTerm_sdiff_singleton_zero]
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine m.monomial_notMem_span_leadingTerm_of_isRemainder ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

/-- A subset `G` of an ideal `I` is said to be a Gröbner basis if:

1. `G` is contained in `I` (i.e., all polynomials in `G` belong to the ideal `I`).
2. The ideal generated by the leading terms of all polynomials in `I` is equal to
   the ideal generated by the leading terms of the polynomials in `G`.
-/
def IsGroebnerBasis {R : Type*} [CommSemiring R] (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' ↑I) = Ideal.span (m.leadingTerm '' G)

@[simp]
lemma isGroebnerBasis_self (I : Ideal (MvPolynomial σ R)) :
    m.IsGroebnerBasis I I := by
  simp [IsGroebnerBasis]

open Classical in
@[simp]
lemma isGroebnerBasis_sdiff_singleton_zero (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) :
    m.IsGroebnerBasis (G \ {0}) I ↔ m.IsGroebnerBasis G I := by
  simp [IsGroebnerBasis, m.span_leadingTerm_sdiff_singleton_zero]

open Classical in
@[simp]
lemma isGroebnerBasis_insert_zero (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) :
    m.IsGroebnerBasis (insert 0 G) I ↔ m.IsGroebnerBasis G I := by
  unfold IsGroebnerBasis
  congr! 1
  · constructor
    · intro h x hx
      apply h
      simp [hx]
    · simp [Set.insert_subset_iff]
  · simp [m.span_leadingTerm_insert_zero]

variable {m} in
lemma exists_degree_le_degree_of_isRemainder_zero
    (p : MvPolynomial σ R) (hp : p ≠ 0) (B : Set (MvPolynomial σ R))
    (hB : ∀ b ∈ B, IsRegular (m.leadingCoeff b))
    (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, m.degree b ≤ m.degree p := by
  classical
  rw [isRemainder_def''] at h
  rcases h with ⟨⟨g, B', h₁, hsum, h₃⟩, h₄⟩
  simp at hsum
  have : m.degree p ∈ p.support := m.degree_mem_support hp
  rw [hsum] at this
  obtain ⟨b, hb⟩ := Finset.mem_biUnion.mp <| hsum.symm ▸ Finset.mem_of_subset support_sum this
  use b
  constructor
  · exact h₁ hb.1
  · rcases hb with ⟨hb₁, hb₂⟩
    have := h₃ b hb₁
    obtain hgbne0 : g b ≠ 0 := by
      contrapose! hb₂
      simp [hb₂]
    apply le_degree (m:=m) at hb₂
    rw [mul_comm b] at this
    apply le_antisymm this at hb₂
    simp at hb₂
    rw [degree_mul_of_isRegular_right hgbne0] at hb₂
    · exact le_of_add_le_right (le_of_eq hb₂)
    exact hB b (Set.mem_of_mem_of_subset hb₁ h₁)

variable {m} in
lemma exists_degree_le_degree_of_isRemainder_zero₀ {R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (hp : p ≠ 0) (B : Set (MvPolynomial σ R))
    (hB : ∀ b ∈ B, IsRegular (m.leadingCoeff b) ∨ b = 0)
    (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree p := by
  rw [← isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  convert m.exists_degree_le_degree_of_isRemainder_zero p hp (B \ {0}) ?_ h using 2
  · simp
    rw [and_assoc]
  · simp_intro a b [or_iff_not_imp_right.mp (hB _ _)]

end CommSemiring

section CommRing

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

variable (m) in
/-- Delete the leading term in a multivariate polynomial (for some monomial order) -/
noncomputable def subLTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  f - monomial (m.degree f) (m.leadingCoeff f)

theorem degree_sub_LTerm_le (f : MvPolynomial σ R) :
    m.degree (m.subLTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp only [sup_le_iff, le_refl, true_and]
  apply degree_monomial_le

theorem degree_sub_LTerm_lt {f : MvPolynomial σ R} (hf : m.degree f ≠ 0) :
    m.degree (m.subLTerm f) ≺[m] m.degree f := by
  rw [lt_iff_le_and_ne]
  refine ⟨degree_sub_LTerm_le f, ?_⟩
  classical
  intro hf'
  simp only [EmbeddingLike.apply_eq_iff_eq] at hf'
  have : m.subLTerm f ≠ 0 := by
    intro h
    simp only [h, degree_zero] at hf'
    exact hf hf'.symm
  rw [← coeff_degree_ne_zero_iff (m := m), hf'] at this
  apply this
  simp [subLTerm, coeff_monomial, leadingCoeff]

variable (m) in
/-- Reduce a polynomial modulo a polynomial with unit leading term (for some monomial order) -/
noncomputable
def reduce {b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
  f - monomial (m.degree f - m.degree b) (hb.unit⁻¹ * m.leadingCoeff f) * b

theorem degree_reduce_lt {f b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
    (hbf : m.degree b ≤ m.degree f) (hf : m.degree f ≠ 0) :
    m.degree (m.reduce hb f) ≺[m] m.degree f := by
  have H : m.degree f =
      m.degree ((monomial (m.degree f - m.degree b)) (hb.unit⁻¹ * m.leadingCoeff f)) +
        m.degree b := by
    classical
    rw [degree_monomial, if_neg]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, leadingCoeff_eq_zero_iff]
      intro hf0
      apply hf
      simp [hf0]
  have H' : coeff (m.degree f) (m.reduce hb f) = 0 := by
    simp only [reduce, coeff_sub, sub_eq_zero]
    nth_rewrite 2 [H]
    rw [coeff_mul_of_degree_add (m := m), leadingCoeff_monomial, mul_comm, ← mul_assoc,
      IsUnit.mul_val_inv, one_mul, ← leadingCoeff]
  rw [lt_iff_le_and_ne]
  constructor
  · classical
    apply le_trans degree_sub_le
    simp only [sup_le_iff, le_refl, true_and]
    apply le_of_le_of_eq degree_mul_le
    rw [m.toSyn.injective.eq_iff]
    exact H.symm
  · intro K
    simp only [EmbeddingLike.apply_eq_iff_eq] at K
    nth_rewrite 1 [← K] at H'
    rw [← leadingCoeff, leadingCoeff_eq_zero_iff] at H'
    rw [H', degree_zero] at K
    exact hf K.symm

/-- Division by a family of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order -/
theorem div {ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (f : MvPolynomial σ R) :
    ∃ (g : ι →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ b g + r ∧
        (∀ i, m.degree (b i * (g i)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ i, ¬ (m.degree (b i) ≤ c)) := by
  by_cases hb' : ∃ i, m.degree (b i) = 0
  · obtain ⟨i, hb0⟩ := hb'
    use Finsupp.single i ((hb i).unit⁻¹ • f), 0
    constructor
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      nth_rewrite 2 [eq_C_of_degree_eq_zero hb0]
      rw [mul_comm, smul_eq_C_mul]
    constructor
    · intro j
      by_cases hj : j = i
      · apply le_trans degree_mul_le
        simp only [hj, hb0, Finsupp.single_eq_same, zero_add]
        apply le_of_eq
        simp only [EmbeddingLike.apply_eq_iff_eq]
        apply degree_smul (Units.isRegular _)
      · simp only [Finsupp.single_eq_of_ne hj, mul_zero, degree_zero, map_zero]
        apply bot_le
    · simp
  push_neg at hb'
  by_cases hf0 : f = 0
  · refine ⟨0, 0, by simp [hf0], ?_, by simp⟩
    intro b
    simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
    exact bot_le
  by_cases hf : ∃ i, m.degree (b i) ≤ m.degree f
  · obtain ⟨i, hf⟩ := hf
    have deg_reduce : m.degree (m.reduce (hb i) f) ≺[m] m.degree f := by
      apply degree_reduce_lt (hb i) hf
      intro hf0'
      apply hb' i
      simpa [hf0'] using hf
    obtain ⟨g', r', H'⟩ := div hb (m.reduce (hb i) f)
    use g' +
      Finsupp.single i (monomial (m.degree f - m.degree (b i)) ((hb i).unit⁻¹ * m.leadingCoeff f))
    use r'
    constructor
    · rw [map_add, add_assoc, add_comm _ r', ← add_assoc, ← H'.1]
      simp [reduce]
    constructor
    · rintro j
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [mul_add]
      apply le_trans degree_add_le
      simp only [sup_le_iff]
      constructor
      · exact le_trans (H'.2.1 _) (le_of_lt deg_reduce)
      · classical
        rw [Finsupp.single_apply]
        split_ifs with hc
        · subst j
          grw [degree_mul_le, map_add, degree_monomial_le, ← map_add, add_tsub_cancel_of_le hf]
        · simp only [mul_zero, degree_zero, map_zero]
          exact bot_le
    · exact H'.2.2
  · push_neg at hf
    suffices ∃ (g' : ι →₀ MvPolynomial σ R), ∃ r',
        (m.subLTerm f = Finsupp.linearCombination (MvPolynomial σ R) b g' + r') ∧
        (∀ i, m.degree ((b  i) * (g' i)) ≼[m] m.degree (m.subLTerm f)) ∧
        (∀ c ∈ r'.support, ∀ i, ¬ m.degree (b i) ≤ c) by
      obtain ⟨g', r', H'⟩ := this
      use g', r' +  monomial (m.degree f) (m.leadingCoeff f)
      constructor
      · simp [← add_assoc, ← H'.1, subLTerm]
      constructor
      · exact fun b ↦ le_trans (H'.2.1 b) (degree_sub_LTerm_le f)
      · intro c hc i
        by_cases hc' : c ∈ r'.support
        · exact H'.2.2 c hc' i
        · convert hf i
          classical
          have := MvPolynomial.support_add hc
          rw [Finset.mem_union, Classical.or_iff_not_imp_left] at this
          simpa only [Finset.mem_singleton] using support_monomial_subset (this hc')
    by_cases hf'0 : m.subLTerm f = 0
    · refine ⟨0, 0, by simp [hf'0], ?_, by simp⟩
      intro b
      simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
      exact bot_le
    · exact (div hb) (m.subLTerm f)
termination_by WellFounded.wrap
  ((isWellFounded_iff m.syn fun x x_1 ↦ x < x_1).mp m.wf) (m.toSyn (m.degree f))
decreasing_by
· exact deg_reduce
· apply degree_sub_LTerm_lt
  intro hf0
  apply hf'0
  simp only [subLTerm, sub_eq_zero]
  nth_rewrite 1 [eq_C_of_degree_eq_zero hf0, hf0]
  simp

/-- Division by a *set* of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order -/
theorem div_set {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    ∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
        (∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) := by
  obtain ⟨g, r, H⟩ := m.div (b := fun (p : B) ↦ p) (fun b ↦ hB b b.prop) f
  exact ⟨g, r, H.1, H.2.1, fun c hc b hb ↦ H.2.2 c hc ⟨b, hb⟩⟩

/-- A variant of `MonomialOrder.div_set` using `MonomialOrder.IsRemainder`. -/
theorem div_set' {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit <| m.leadingCoeff b) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  obtain ⟨g, r, h⟩ := MonomialOrder.div_set hB p
  use r
  split_ands
  · use g
    exact ⟨h.1, h.2.1⟩
  · intro c hc b hb _
    exact h.2.2 c hc b hb

/-- A variant of `div_set'` including `0` -/
theorem div_set'₀ {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, (IsUnit (m.leadingCoeff b) ∨ b = 0)) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  have hB₁ : ∀ b ∈ B \ {0}, IsUnit (m.leadingCoeff b) := by
    simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]
  obtain ⟨r, h⟩ := m.div_set' hB₁ p
  exists r
  rwa [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder]

/-- Division by a multivariate polynomial
whose leading coefficient is invertible with respect to a monomial order -/
theorem div_single {b : MvPolynomial σ R}
    (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    ∃ (g : MvPolynomial σ R) (r : MvPolynomial σ R),
      f = g * b + r ∧
        (m.degree (b * g) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ¬ (m.degree b ≤ c)) := by
  obtain ⟨g, r, hgr, h1, h2⟩ := div_set (B := {b}) (m := m) (by simp [hb]) f
  specialize h1 ⟨b, by simp⟩
  set q := g ⟨b, by simp⟩
  simp only [Set.mem_singleton_iff, forall_eq] at h2
  simp only at h1
  refine ⟨q, r, ?_, h1, h2⟩
  rw [hgr]
  simp only [Finsupp.linearCombination, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id_eq, smul_eq_mul, add_left_inj]
  rw [Finsupp.sum_eq_single ⟨b, by simp⟩ _ (by simp)]
  simp +contextual

lemma mem_ideal_iff_of_isRemainder {B : Set (MvPolynomial σ R)}
    {r : MvPolynomial σ R} {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) : r ∈ I ↔ p ∈ I := by
  refine ⟨m.mem_ideal_of_isRemainder_of_mem_ideal hBI hpBr, ?_⟩
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  intro hp
  rw [← sub_eq_of_eq_add' h_eq]
  apply Ideal.sub_mem I hp
  apply Ideal.sum_mem
  exact fun _ _ ↦ Ideal.mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hBI)

lemma sub_mem_ideal_of_isRemainder_of_subset_ideal
    {B : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hBI : B ⊆ I) (hr₁ : m.IsRemainder p B r₁) (hr₂ : m.IsRemainder p B r₂) :
    r₁ - r₂ ∈ I := by
  obtain ⟨⟨f₁, h_eq₁, h_deg₁⟩, h_remain₁⟩ := hr₁
  obtain ⟨⟨f₂, h_eq₂, h_deg₂⟩, h_remain₂⟩ := hr₂
  rw [← sub_eq_of_eq_add' h_eq₁, ← sub_eq_of_eq_add' h_eq₂]
  simp
  apply Ideal.sub_mem I
  all_goals
    apply Ideal.sum_mem
    intro g hg
    exact Ideal.mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hBI)

lemma sub_monomial_notMem_span_leadingTerm_of_isRemainder
    {R : Type*} [CommRing R]
    {B : Set (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (hr₁ : m.IsRemainder p B r₁) (hr₂ : m.IsRemainder p B r₂) :
    ∀ s ∈ (r₁ - r₂).support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  apply m.monomial_notMem_span_leadingTerm hB
  intro c hc
  apply MvPolynomial.support_sub at hc
  rw [Finset.mem_union] at hc
  have {b} (hb : b ∈ B) : b ≠ 0 := by
    have : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      simp [Subsingleton.elim _ (0 : MvPolynomial σ R)] at hc
    rw [← m.leadingCoeff_ne_zero_iff]
    exact (hB b hb).ne_zero
  rcases hc with hc | hc
  · intro b hb
    exact hr₁.2 c hc b hb <| this hb
  · intro b hb
    exact hr₂.2 c hc b hb <| this hb

/-- Given a remainder `r` of a polynomial `p` on division by a Gröbner basis `G` of an ideal `I`,
the remainder `r` is 0 if and only if `p` is in the ideal `I`.

Any leading coefficient of polynomial in the Gröbner basis `G` is required to be a unit. -/
theorem remainder_eq_zero_iff_mem_ideal_of_isGroebner
    {p : MvPolynomial σ R} {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    {r : MvPolynomial σ R} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder p G r) :
    r = 0 ↔ p ∈ I := by
  constructor
  · rw [← m.mem_ideal_iff_of_isRemainder h.1 hr]
    simp_intro ..
  · intro h_p_mem
    by_contra hr_ne_zero
    have h₃: m.leadingTerm r ∉ Ideal.span (m.leadingTerm '' ↑G) := by
      nth_rewrite 1 [leadingTerm]
      apply term_notMem_span_leadingTerm_of_isRemainder hG hr
      exact (m.degree_mem_support_iff r).mpr hr_ne_zero
    rcases h with ⟨h_G', h_span⟩
    obtain ⟨⟨q, h_p_eq_sum_r, h_r_reduced⟩, h_degree⟩ := hr
    have h₁: (Finsupp.linearCombination (MvPolynomial σ R) fun g' ↦ ↑g') q ∈ I := by
      rw [Finsupp.linearCombination_apply]
      rw [Finsupp.sum]
      apply Ideal.sum_mem I
      intro a h_a_in_support
      exact Submodule.smul_mem I (q a) (h_G' a.2)
    rw [h_p_eq_sum_r] at h_p_mem
    have h₂: r ∈ I := by
      exact (Submodule.add_mem_iff_right I h₁).mp h_p_mem
    have h₄: m.leadingTerm r ∈ Ideal.span (m.leadingTerm '' ↑G) := by
      rw [←h_span]
      apply Ideal.subset_span
      apply Set.mem_image_of_mem
      exact h₂
    exact h₃ h₄

/-- Given a remainder `r` of a polynomial `p` on division by a Gröbner basis `G` of an ideal `I`,
the remainder `r` is 0 if and only if `p` is in the ideal `I`.

It is a variant of `MonomialOrder.remainder_eq_zero_iff_mem_ideal_of_isGroebner`, allowing the
Gröbner basis to contain also 0, besides polynomials with invertible leading coefficients. -/
theorem remainder_eq_zero_iff_mem_ideal_of_isGroebner₀ {p : MvPolynomial σ R}
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} {r : MvPolynomial σ R}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder p G r) :
    r = 0 ↔ p ∈ I := by
  rw [← m.isGroebnerBasis_sdiff_singleton_zero] at h
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at hr
  refine m.remainder_eq_zero_iff_mem_ideal_of_isGroebner ?_ h ?_
  · simp_intro .. [or_iff_not_imp_right.mp (hG _ _)]
  · exact hr

theorem isRemainder_zero_iff_mem_ideal_of_isGroebner {p : MvPolynomial σ R}
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (h : m.IsGroebnerBasis G I) :
    m.IsRemainder p G 0 ↔ p ∈ I := by
  constructor
  · intro hr
    apply (remainder_eq_zero_iff_mem_ideal_of_isGroebner hG h hr).mp rfl
  · intro hp
    have hor: ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0 := by
      exact fun g a ↦ Or.symm (Or.inr (hG g a))
    have h₁:  ∃ (r : MvPolynomial σ R), m.IsRemainder p G r := by
      exact m.div_set'₀ hor p
    obtain ⟨r, hr⟩ := h₁
    have h₂: r = 0 := by
      exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner hG h hr).mpr hp
    rw [h₂] at hr
    exact hr

lemma isRemainder_zero_iff_mem_ideal_of_isGroebner₀ {p : MvPolynomial σ R}
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (h : m.IsGroebnerBasis G I) :
    m.IsRemainder p G 0 ↔ p ∈ I := by
  rw [← m.isGroebnerBasis_sdiff_singleton_zero] at h
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder]
  refine m.isRemainder_zero_iff_mem_ideal_of_isGroebner ?_ h
  simp_intro a b [or_iff_not_imp_right.mp (hG _ _)]

/-- Gröbner basis of any ideal spans the ideal. -/
theorem ideal_eq_span_of_isGroebner {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) (h : m.IsGroebnerBasis G I) :
    I = Ideal.span G := by
  apply le_antisymm
  · intro p hp
    rw [← isRemainder_zero_iff_mem_ideal_of_isGroebner hG h] at hp
    obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hp
    rw [h_eq, Finsupp.linearCombination_apply, add_zero]
    apply Ideal.sum_mem
    intro g hg
    rcases g with ⟨g, gG'⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span gG')
  · intro p hp
    suffices Ideal.span ↑G ≤ I by
      exact this hp
    apply Ideal.span_le.mpr
    intro p hp'
    rw [SetLike.mem_coe]
    exact h.1 hp'

theorem isGroebnerBasis_iff_ideal_eq_span_and_isGroebner_span (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔ (I = Ideal.span G ∧ m.IsGroebnerBasis G (Ideal.span G)) := by
  constructor
  · intro this
    simpa [ideal_eq_span_of_isGroebner hG this]
  · simp_intro ..

theorem isGroebnerBasis_iff_span_eq_and_degree_le (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      Ideal.span G = I ∧ ∀ p ∈ I, p ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree p := by
  classical
  constructor
  · intro h
    exists (m.ideal_eq_span_of_isGroebner hG h).symm
    intro p hp hp0
    apply m.exists_degree_le_degree_of_isRemainder_zero _ hp0 ↑G
      (by simp_intro .. [(hG _ _).isRegular])
    exact (m.isRemainder_zero_iff_mem_ideal_of_isGroebner hG h).mpr hp
  · rintro ⟨hG', h_degree⟩
    constructor
    · exact hG' ▸ Submodule.subset_span
    · rw [← hG', ←SetLike.coe_set_eq]
      apply Set.eq_of_subset_of_subset
      · apply Ideal.span_le.mpr
        intro p' hp
        rcases hp with ⟨p, hp', hp'₁⟩
        rw [hG'] at hp'
        rw [←hp'₁, leadingTerm, SetLike.mem_coe,
          m.span_leadingTerm_eq_span_monomial (by simp_intro .. [hG]),
          ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
        intro j hj
        simp [MonomialOrder.leadingCoeff_eq_zero_iff] at hj
        simp
        exact hj.1 ▸ h_degree p hp' hj.2
      · rw [hG']
        apply Ideal.span_mono
        exact Set.image_mono (hG' ▸ Submodule.subset_span)

/-- A set of polynomials is a Gröbner basis of an ideal if and only if it is a subset of this ideal
and 0 is a remainder of each member of this ideal on division by this set.

Any leading coefficient of polynomial in the set is required to be a unit. -/
theorem isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero
    (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R))
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔ G ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G 0 := by
  classical
  constructor
  · intro h
    exists h.1
    intro p h_p_in_I
    rwa [isRemainder_zero_iff_mem_ideal_of_isGroebner hG h]
  · intro h
    rcases h with ⟨h_G, h_remainder⟩
    rw [m.isGroebnerBasis_iff_span_eq_and_degree_le G I hG]
    constructor
    · rw [←SetLike.coe_set_eq]
      norm_cast
      apply le_antisymm (Ideal.span_le.mpr h_G)
      intro p hp
      specialize h_remainder p hp
      have: Ideal.span G ≤ I:= by
        apply Ideal.span_le.mpr
        intro p hp'
        rw [SetLike.mem_coe]
        exact h_G hp'
      have h1: (G : Set <| MvPolynomial σ R) ⊆ (Ideal.span (α := MvPolynomial σ R) ↑G) := by
        exact Ideal.subset_span
      apply (mem_ideal_iff_of_isRemainder h1 h_remainder).mp
      simp
    · intro p hp hp0
      exact m.exists_degree_le_degree_of_isRemainder_zero p hp0 G
        (by simp_intro .. [(hG _ _).isRegular]) <|
          h_remainder p hp

/-- A set of polynomials is a Gröbner basis of an ideal if and only if it is a subset of this ideal
and 0 is a remainder of each member of this ideal on division by this set.

It is a variant of `MonomialOrder.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero`, allowing
the set to contain also 0, besides polynomials with invertible leading coefficients. -/
theorem isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero₀ (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) :
    m.IsGroebnerBasis G I ↔ G ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G 0 := by
  rw [← m.isGroebnerBasis_sdiff_singleton_zero]
  convert m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero (G \ {0}) I _ using 2
  · simp
  · simp [m.isRemainder_sdiff_singleton_zero_iff_isRemainder]
  · simp_intro .. [or_iff_not_imp_right.mp (hG _ _)]

theorem span_leadingTerm_eq_span_monomial_of_isGroebner {G : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    Ideal.span (m.leadingTerm '' ↑G) =
    Ideal.span ((fun p ↦ monomial (m.degree p) (1 : R)) '' (I \ {(0 : MvPolynomial σ R)})) := by
  classical
  by_cases hR : Nontrivial R
  · rw [m.span_leadingTerm_eq_span_monomial (B := (↑G : Set (MvPolynomial σ R))) hG]
    apply le_antisymm
    · rw [Ideal.span_le]
      refine subset_trans ?_ Submodule.subset_span
      apply Set.image_mono
      apply Set.subset_diff_singleton h.1
      contrapose! hG
      use 0
      simpa
    · rw [Ideal.span_le]
      intro x
      simp
      intro y hy hy0 hxy
      rw [← hxy, ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
      simp
      exact ((m.isGroebnerBasis_iff_span_eq_and_degree_le _ _ hG).mp h).2 y hy hy0
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact ((Submodule.subsingleton_iff _).mpr inferInstance).elim _ _

theorem span_leadingTerm_eq_span_monomial_of_isGroebner₀ {G : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) :
    Ideal.span (m.leadingTerm '' ↑G) =
    Ideal.span ((fun p ↦ monomial (m.degree p) (1 : R)) '' (I \ {(0 : MvPolynomial σ R)})) := by
  rw [← m.isGroebnerBasis_sdiff_singleton_zero] at h
  convert m.span_leadingTerm_eq_span_monomial_of_isGroebner h _ using 1
  · simp [m.image_leadingTerm_sdiff_singleton_zero]
  · simp_intro .. [or_iff_not_imp_right.mp (hG _ _)]

/-- Remainder of any polynomial on division by a Gröbner basis exists and is unique.

Any leading coefficient of polynomial in the Gröbner basis is required to be a unit. -/
theorem existsUnique_isRemainder_of_isGroebnerBasis {G : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) (p : MvPolynomial σ R) :
    ∃! (r : MvPolynomial σ R), m.IsRemainder p G r := by
  classical
  apply existsUnique_of_exists_of_unique (m.div_set' hG p)
  intro r₁ r₂ hr₁ hr₂
  rw [← sub_eq_zero]
  by_contra! hrne0
  have hr := (m.degree_mem_support_iff _).mpr hrne0
  apply m.sub_monomial_notMem_span_leadingTerm_of_isRemainder (B := ↑G) hG hr₁ hr₂ at hr
  rw [m.span_leadingTerm_eq_span_monomial_of_isGroebner h hG] at hr
  apply hr
  apply Submodule.mem_span_of_mem
  apply Set.mem_image_of_mem
  simp [hrne0]
  exact m.sub_mem_ideal_of_isRemainder_of_subset_ideal h.1 hr₁ hr₂

/-- Remainder of any polynomial on division by a Gröbner basis exists and is unique.

It is a variant of `MonomialOrder.existsUnique_isRemainder_of_isGroebnerBasis`, allowing the
Gröbner basis to contain also 0, besides polynomials with invertible leading coefficients. -/
theorem existsUnique_isRemainder_of_isGroebnerBasis₀ {G : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (p : MvPolynomial σ R) :
    ∃! (r : MvPolynomial σ R), m.IsRemainder p G r := by
  rw [← m.isGroebnerBasis_sdiff_singleton_zero] at h
  simp_rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder p G]
  convert m.existsUnique_isRemainder_of_isGroebnerBasis h _ p
  simp_intro .. [or_iff_not_imp_right.mp (hG _ _)]

end CommRing

section Field

variable {k : Type*} [Field k]
variable {σ : Type*} {m : MonomialOrder σ}

variable (m) in
theorem exists_isGroebnerBasis_finite [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    ∃ G : Set (MvPolynomial σ k), m.IsGroebnerBasis G ↑I ∧ G.Finite := by
  have key : (Ideal.span (α:=MvPolynomial σ k) (m.leadingTerm '' ↑I)).FG :=
    (inferInstance : IsNoetherian _ _).noetherian _
  -- todo: Ideal.fg_span_iff_fg_span_finset_subset
  apply (Submodule.fg_span_iff_fg_span_finset_subset _).mp at key
  simp only [Set.subset_image_iff] at key
  rcases key with ⟨s, ⟨G', hG'I, hG's⟩, hIs⟩
  have ⟨G, hG, hG₁⟩ := hG's ▸ Set.exists_subset_bijOn G' m.leadingTerm
  use G
  split_ands
  · exact subset_trans hG hG'I
  · rwa [hG₁.image_eq]
  · simp [Set.BijOn.finite_iff_finite hG₁]

/-- A variant of `div_set'` in field -/
theorem div_set'' (B : Set (MvPolynomial σ k))
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p B r := by
  apply div_set'₀
  simp [em']

lemma term_notMem_span_leadingTerm_of_isRemainder' {p r : MvPolynomial σ k}
    {B : Set (MvPolynomial σ k)} (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [←Ideal.span_sdiff_singleton_zero, ← m.image_leadingTerm_sdiff_singleton_zero]
  apply term_notMem_span_leadingTerm_of_isRemainder
  · simp
  rwa [←isRemainder_sdiff_singleton_zero_iff_isRemainder] at h

/-- Given a remainder `r` of a polynomial `p` on division by a Gröbner basis `G` of an ideal `I`,
the remainder `r` is 0 if and only if `p` is in the ideal `I`.

It is a variant of `MonomialOrder.remainder_eq_zero_iff_mem_ideal_of_isGroebner`, over a field and
without hypothesis on leading coefficients in the Gröbner basis. -/
theorem remainder_eq_zero_iff_mem_ideal_of_isGroebner' {p : MvPolynomial σ k}
    {G : Set (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
    {r : MvPolynomial σ k}
    (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder p G r) :
    r = 0 ↔ p ∈ I := by
  refine remainder_eq_zero_iff_mem_ideal_of_isGroebner₀ ?_ h hr
  simp [em']

lemma isRemainder_zero_iff_mem_ideal_of_isGroebner' {p : MvPolynomial σ k}
    {G : Set (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
    (h : m.IsGroebnerBasis G I) :
    m.IsRemainder p G 0 ↔ p ∈ I := by
  refine m.isRemainder_zero_iff_mem_ideal_of_isGroebner₀ ?_ h
  simp [em']

lemma exists_degree_le_degree_of_isRemainder_zero' (p : MvPolynomial σ k) (hp : p ≠ 0)
    (B : Set (MvPolynomial σ k)) (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree p :=
  m.exists_degree_le_degree_of_isRemainder_zero₀ p hp B (by simp [isRegular_iff_ne_zero, em']) h

/-- A set of polynomials is a Gröbner basis of an ideal if and only if it is a subset of this ideal
and 0 is a remainder of each member of this ideal on division by this set.

It is a variant of `MonomialOrder.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero`,
over a field and without hypothesis on leading coefficients in the set. -/
theorem isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero'
    (G : Set (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k)) :
    m.IsGroebnerBasis G I ↔ G ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G 0 :=
  m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero₀ G I (by simp [em'])

set_option maxHeartbeats 0 in
/-- Buchberger Criterion: a basis of an ideal is a Gröbner basis of it if and only if 0 is a
remainder of echo sPolynomial between two polynomials on the basis. -/
theorem isGroebnerBasis_iff_isRemainder_sPolynomial_zero (G : Set (MvPolynomial σ k)) :
    m.IsGroebnerBasis G (Ideal.span G) ↔
    ∀ (g₁ g₂ : G), m.IsRemainder (m.sPolynomial g₁ g₂ : MvPolynomial σ k) G 0 := by
  classical
  constructor
  · intro h g₁ g₂
    rw [m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero'] at h
    apply h.2
    apply m.sPolynomial_mem_ideal
    <;> exact Set.mem_of_mem_of_subset (by simp) h.1
  intro hG
  rw [isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero']
  exists Ideal.subset_span
  intro p hp
  simp_rw [isRemainder_def'', add_zero]
  refine ⟨?_, by simp⟩
  -- todo: Ideal.mem_span_iff_exists_finset_subset
  apply Submodule.mem_span_iff_exists_finset_subset.mp at hp
  obtain ⟨f, T, hT, ⟨hf', hf⟩⟩ := hp
  refine WellFoundedLT.induction
      (C := fun (a : m.syn) ↦
        (∃ (g : MvPolynomial σ k → MvPolynomial σ k) (G' : Finset (MvPolynomial σ k)),
          ↑G' ⊆ G ∧
          p = ∑ g' ∈ G', (g g') * g' ∧
          ∀ g' ∈ G', (m.toSyn <| m.degree <| g' * g g') ≤ a) →
        ∃ (g : MvPolynomial σ k → MvPolynomial σ k) (G' : Finset (MvPolynomial σ k)),
          ↑G' ⊆ G ∧
          p = ∑ g' ∈ G', (g g') * g' ∧
          ∀ g' ∈ G', (m.toSyn <| m.degree <| g' * g g') ≤ m.toSyn (m.degree p))
      (T.sup fun g' ↦ (m.toSyn <| m.degree <| g' * (f g'))) ?_ ?_
  · intro a h ⟨g, G', hG', hg, hg₂⟩
    by_cases ha : m.toSyn (m.degree p) < a
    · simp_rw [← and_imp, ← exists_imp] at h
      apply h
      clear h
      let gg'deg := fun g' ↦ m.toSyn <| m.degree <| g g' * g'
      have hp := calc
        p = ∑ g' ∈ G', g g' * g' := hg
        _ = ∑ g' ∈ G',
              (if gg'deg g' = a then m.leadingTerm (g g') else 0) * g' +
            ∑ g' ∈ G',
              (if gg'deg g' = a then g g' - m.leadingTerm (g g') else g g') * g' := by
          simp [← Finset.sum_add_distrib, ← add_mul, ite_add_ite]
        _ = ∑ g' ∈ G',
              monomial (m.degree (g g')) (if gg'deg g' = a then m.leadingCoeff (g g') else 0) * g'
            + _ := by
          congr 2
          rw [funext_iff]
          intro x
          by_cases h : gg'deg x = a <;> simp [h, leadingTerm]

      have a_gt_zero : 0 < a := bot_lt_of_lt ha

      obtain ⟨c, hc⟩ := by
        apply m.sPolynomial_decomposition' (ι:=MvPolynomial σ k) (d:=a) (B:=G')
          (fun g' ↦ monomial (m.degree (g g'))
            (if gg'deg g' = a then m.leadingCoeff (g g') else 0) * g')
        · intro g' hg'
          simp
          by_cases hg'₂ : g' = 0 <;> simp [hg'₂]
          by_cases hg'₃ : g g' = 0 <;> simp [hg'₃]
          by_cases hg'₄ : gg'deg g' = a <;> simp [hg'₄]
          have := m.leadingCoeff_ne_zero_iff.mpr hg'₃
          rw [← hg'₄, EmbeddingLike.apply_eq_iff_eq,
            degree_mul (monomial_eq_zero.not.mpr this) hg'₂,
            degree_mul hg'₃ hg'₂, degree_monomial]
          simp [this]
        · contrapose! ha
          rw [hp, m.degree_add_of_lt]
          ·exact ha
          refine lt_of_lt_of_le ?_ ha
          apply lt_of_le_of_lt m.degree_sum_le
          rw [Finset.sup_lt_iff a_gt_zero]
          intro g' hg'
          by_cases hg'₂ : g' = 0
          · simp [hg'₂, a_gt_zero]
          by_cases hg'₃ : g g' = 0
          · simp [hg'₃, a_gt_zero]
          by_cases hg'₄ : gg'deg g' = a
          · simp [hg'₄]
            by_cases h : g g' - m.leadingTerm (g g') = 0
            · simp [h, a_gt_zero]
            refine lt_of_lt_of_le ?_ (hg₂ g' hg')
            rw [degree_mul h hg'₂, degree_mul hg'₂ hg'₃, add_comm,
              AddEquiv.map_add, AddEquiv.map_add, add_lt_add_iff_left]
            exact m.degree_sub_leadingTerm_lt_degree (degree_ne_zero_of_sub_leadingTerm_ne_zero h)
          · simp [hg'₄]
            apply lt_of_le_of_ne (mul_comm (g g') g' ▸ hg₂ g' hg')
            exact hg'₄

      simp_rw [hc, m.sPolynomial_mul_monomial] at hp
      rw [← G'.sum_coe_sort] at hp
      conv at hp =>
        rhs
        arg 1
        arg 2
        intro g'
        rw [← G'.sum_coe_sort]

      simp_rw [isRemainder_def'₁] at hG
      simp [-Subtype.forall] at hG
      let q' (g'₁ g'₂ : G') := (hG ⟨g'₁, hG' g'₁.2⟩ ⟨g'₂, hG' g'₂.2⟩).choose
      have hq' (g'₁ g'₂ : G') := (hG ⟨g'₁, hG' g'₁.2⟩ ⟨g'₂, hG' g'₂.2⟩).choose_spec
      simp_rw
        [show ∀ (g'₁ g'₂ : G'), (hG ⟨g'₁, hG' g'₁.2⟩ ⟨g'₂, hG' g'₂.2⟩).choose = q' g'₁ g'₂ by
          intros; rfl] at hq'
      have hq'₁ (g'₁ g'₂) := (hq' g'₁ g'₂).1

      let G'' : Finset (MvPolynomial σ k) :=
        G'.attach.biUnion (fun b₁ ↦ G'.attach.biUnion fun b₂ ↦ (q' b₁ b₂).support) ∪ G'
      conv at hq' =>
        ext g'₁ g'₂
        simp [Finsupp.linearCombination_apply_of_mem_supported
            (l := (q' ↑g'₁ ↑g'₂)) (s := G'')
            (hs := by
              simp [Finsupp.mem_supported]
              simp [G'', Finset.subset_iff, ← Decidable.not_imp_not (a := Or _ _)]
              simp_intro ..)]
      clear_value q'
      clear hG
      simp_rw [(hq' _ _).2.1] at hp
      replace hq' (g'₁ g'₂ : G') := (hq' g'₁ g'₂).2.2

      simp_rw [Finset.mul_sum, ← mul_assoc, Finset.smul_sum,
        ←smul_mul_assoc, smul_monomial, Finset.sum_comm (t:=G''),
        ← Finset.sum_mul] at hp
      convert_to
        p = _ + ∑ g' ∈ G'',
          (if g' ∈ G' then
            if gg'deg g' = a then g g' - m.leadingTerm (g g') else g g'
          else 0) * g' using 2 at hp
      · simp [G'']
      simp_rw [← Finset.sum_add_distrib, ← add_mul] at hp
      letI g₂ := (?_ : MvPolynomial σ k → MvPolynomial σ k)
      replace hp : p = ∑ g' ∈ G'', g₂ g' * g' := by exact hp

      refine ⟨(G''.sup fun g' ↦ m.toSyn <| m.degree <| g₂ g' * g'), ?_, g₂, G'', ?_, hp, ?_⟩
      · simp [g₂, Finset.sup_lt_iff a_gt_zero, add_mul]
        clear hp g₂
        intro g' hg'
        apply lt_of_le_of_lt degree_add_le
        apply max_lt
        · simp_rw [Finset.sum_mul]
          refine lt_of_le_of_lt m.degree_sum_le <| (Finset.sup_lt_iff a_gt_zero).mpr ?_
          simp
          intro g'₁ hg'₁
          refine lt_of_le_of_lt m.degree_sum_le <| (Finset.sup_lt_iff a_gt_zero).mpr ?_
          simp
          intro g'₂ hg'₂
          obtain ⟨hq', hq'0⟩ := hq' ⟨g'₁, hg'₁⟩ ⟨g'₂, hg'₂⟩ g' <| by
            simp [G'', -Subtype.exists, -Finset.mem_attach, -Finsupp.mem_support_iff] at hg'
            rcases hg' with ⟨a, -, b, -, hh'⟩ | hg'
            · exact hq'₁ _ _ hh'
            · exact Set.mem_of_subset_of_mem hG' hg'
          by_cases hgg'₂ : gg'deg g'₂ ≠ a
          · simp [hgg'₂, a_gt_zero]
          by_cases hgg'₁ : gg'deg g'₁ ≠ a
          · simp [hgg'₁, a_gt_zero]
          by_cases hspoly : m.sPolynomial g'₁ g'₂ = 0
          · simp [hspoly] at hq'0
            simp [hq'0, a_gt_zero]
          simp at hq'
          rw [mul_assoc]
          apply lt_of_le_of_lt degree_mul_le
          rw [AddEquiv.map_add]
          refine add_lt_of_add_lt_right ?_ (degree_monomial_le _)
          apply lt_of_le_of_lt (add_le_add_right (mul_comm g' (q' _ _ g') ▸ hq') _)
          apply lt_of_lt_of_le (add_lt_add_right (m.degree_sPolynomial_lt_sup_degree hspoly) _)
          push_neg at hgg'₁ hgg'₂
          unfold gg'deg at hgg'₁ hgg'₂
          rw [← AddEquiv.map_add]
          have :
              (m.degree (g g'₁) + m.degree g'₁) ⊔ (m.degree (g g'₂) + m.degree g'₂)
                - m.degree g'₁ ⊔ m.degree g'₂ + m.degree g'₁ ⊔ m.degree g'₂
              = (m.degree (g g'₁) + m.degree g'₁) ⊔ (m.degree (g g'₂) + m.degree g'₂) := by
            rw [Finsupp.ext_iff]
            intro x
            simp
            apply Nat.sub_add_cancel
            apply max_le_max <;> simp
          rw [this]
          rw [m.degree_mul'] at hgg'₁ hgg'₂
          · rw [← hgg'₁, m.toSyn.injective.eq_iff] at hgg'₂
            simp [← hgg'₁, hgg'₂]
          · contrapose! hgg'₂
            simp [hgg'₂, ne_of_lt a_gt_zero]
          · contrapose! hgg'₁
            simp [hgg'₁, ne_of_lt a_gt_zero]
        · by_cases hg'G' : g' ∉ G'
          · simp [hg'G', a_gt_zero]
          push_neg at hg'G'
          simp [hg'G']
          by_cases h : gg'deg g' ≠ a
          · simp [h]
            exact lt_of_le_of_ne (mul_comm (g g') g' ▸ hg₂ g' hg'G') h
          push_neg at h
          simp [h]
          by_cases hLTgg' : g g' - m.leadingTerm (g g') = 0
          · simp [hLTgg', a_gt_zero]
          unfold gg'deg at h
          rw [← h] at ⊢ a_gt_zero
          apply ne_of_lt at a_gt_zero
          rw [ne_eq, eq_comm, toSyn_eq_zero_iff] at a_gt_zero
          obtain ⟨gg'_ne_zero, g_ne_zero⟩ := mul_ne_zero_iff.mp <|
            m.ne_zero_of_degree_ne_zero a_gt_zero
          rw [degree_mul hLTgg' g_ne_zero, AddEquiv.map_add,
            degree_mul gg'_ne_zero g_ne_zero, AddEquiv.map_add]
          simp [m.degree_sub_leadingTerm_lt_degree (degree_ne_zero_of_sub_leadingTerm_ne_zero hLTgg')]
      · simp [G'', hG', hq'₁]
      · intro g'
        rw [mul_comm]
        exact Finset.le_sup (α:=m.syn) (f:=fun g' ↦ m.toSyn <| m.degree <| g₂ g' * g')
    · exists g, G', hG', hg
      exact fun g' hg' ↦ le_trans (hg₂ g' hg') (not_lt.mp ha)
  · exists f, T, hT, hf.symm
    intro g' hg'
    apply Finset.le_sup hg'

/-- Buchberger Criterion: a basis of an ideal is a Gröbner basis of it if and only if any
remainder of echo sPolynomial between two polynomials on the basis is 0.

It is a variant of `MonomialOrder.isGroebnerBasis_iff_isRemainder_sPolynomial_zero`. -/
theorem isGroebnerBasis_iff_isRemainder_sPolynomial_zero' (G : Set (MvPolynomial σ k)) :
    m.IsGroebnerBasis G (Ideal.span G) ↔
    ∀ (g₁ g₂ : G) (r : MvPolynomial σ k),
      m.IsRemainder (m.sPolynomial g₁ g₂ : MvPolynomial σ k) G r → r = 0 := by
  constructor
  · intro h g₁ g₂ r hr
    apply (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h hr).mpr
    rw [m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero'] at h
    apply m.sPolynomial_mem_ideal
    <;> exact Set.mem_of_subset_of_mem h.1 (by simp)
  · rw [isGroebnerBasis_iff_isRemainder_sPolynomial_zero]
    intro h g₁ g₂
    obtain ⟨r, hr⟩ := m.div_set'' G (m.sPolynomial (R := k) ↑g₁ ↑g₂)
    rwa [h g₁ g₂ r hr] at hr

end Field

end MonomialOrder
