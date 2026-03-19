import Mathlib

def RLex (β : Type*) := β
variable {α : Type*}
@[match_pattern] def toRLex : (α →₀ ℕ) ≃ RLex (α →₀ ℕ) := Equiv.refl _
@[match_pattern] def ofRLex : RLex (α →₀ ℕ) ≃ (α →₀ ℕ) := Equiv.refl _

/-- 在 `RLex` 上把 `LT` 实例设成 `Finsupp.Lex (· < ·) (· > ·)`. -/
instance [LT α] : LT (RLex (α →₀ ℕ)) :=
  ⟨fun a b => Finsupp.Lex (· < ·) (· > ·) (ofRLex a) (ofRLex b)⟩
