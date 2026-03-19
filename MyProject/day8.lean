import Mathlib

open Polynomial
universe u v w x
variable {R : Type u} [CommSemiring R]
variable {σ : Type*}
noncomputable instance commSemiring [CommSemiring R] : CommSemiring (MvPolynomial σ R) where
  mul_comm:= by
    intro a b
    rw[mul_comm]
#check Polynomial
#check MvPolynomial
#check monomial
example : monomial 2 3=3*X^2:=by
  simp only [Polynomial.X]
  have h1:(monomial 1) 1 ^ 2= (monomial 2) 1:=by simp only [monomial_pow, one_mul, one_pow]
  have h2:3=C 3:=by rfl
  rw[h1,h2,mul_comm,monomial_mul_C]
  simp only [one_mul]

noncomputable def polyOfCoeffs (n : ℕ) (a : Fin (n + 1) → R) [CommSemiring R] : R[X] :=
  ∑ i : Fin (n+1), C (a i) * X^(n - i)

#check MonomialOrder
#check LinearOrder
#check LinearOrderedCancelAddCommMonoid

#check WellFoundedLT
#check Finsupp.lex_def

#check Finsupp.Lex
#check Pi.Lex

open Finsupp
variable {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)
noncomputable def Lex2 (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)
/-- The lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
theorem a:WellFoundedLT (Fin 5):=by exact Finite.to_wellFoundedLT
noncomputable def MonomialOrder.lex1 :
    MonomialOrder (Fin 6) :=by exact lex

#check Ring
example :WellFoundedGT (Fin 6):=by exact Finite.to_wellFoundedGT



example (n : ℕ):IsOrderedCancelAddMonoid (Fin n→₀ ℕ):=by
  exact isOrderedCancelAddMonoid
