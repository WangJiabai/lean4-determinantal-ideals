import Mathlib
open MvPolynomial Finsupp

structure S where
  σ:Fin 3 →₀ ℕ
  nature:σ 0 =2∧σ 1=3∧σ 2 =1
lemma sigma_as_sum (S : S) :
    S.σ = (single (0 : Fin 3) 2) + (single 1 3) + (single 2 1) := by
  -- 两个 finsupp 相等，用 ext 化成点值相等
  ext i
  -- Fin 3 只有 0,1,2 三个点，逐点讨论
  fin_cases i
  <;>
  simp only [Fin.zero_eta, Fin.isValue, S.nature.1, Finsupp.coe_add, Pi.add_apply,
    single_eq_same, ne_eq, one_ne_zero, not_false_eq_true, single_eq_of_ne, add_zero, Fin.reduceEq]
  simp only [Fin.mk_one, Fin.isValue,Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, single_eq_of_ne, single_eq_same,
    zero_add, Fin.reduceEq, add_zero];rw[S.nature.2.1]
  simp only [Fin.reduceFinMk, Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, single_eq_of_ne,
    add_zero, single_eq_same, zero_add,S.nature.2.2]

lemma lex_refl {σ} [LinearOrder σ] {m : σ →₀ ℕ} :
  ¬ Finsupp.Lex (· > ·) (· < ·) m m :=
by
  -- 右字典序是严格序，所以反身性是“不成立”的，反而要证明 irreflexive。
  intro h
  obtain ⟨i, hi1, hi2⟩ := h
  have : m i < m i := hi2
  exact lt_irrefl _ this

lemma lex_add_compat {σ} [LinearOrder σ]
  {m₁ m₂ k : σ →₀ ℕ}
  (h : Finsupp.Lex (· > ·) (· < ·) m₁ m₂) :
  Finsupp.Lex (· > ·) (· < ·) (m₁ + k) (m₂ + k) :=
by
  obtain ⟨i, hi_eq, hi_lt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [Finsupp.add_apply, Finsupp.add_apply, hi_eq j hj]
  · simp [Finsupp.add_apply, hi_lt]


section
  /-- 变量索引类型：三个变量 x,y,z 对应 0,1,2 -/
  abbrev σ := Fin 3

  /-- x^3 y z 的指数向量：[3,1,1] -/
noncomputable def e1 : σ →₀ ℕ := single 0 3 + single 1 1 + single 2 1

  /-- y^2 z^2 的指数向量：[0,2,2] -/
noncomputable def e2 : σ →₀ ℕ := single 1 2 + single 2 2

  /-!
  在右字典序（索引用 (· > ·)）+ 指数按 (· < ·) 比较下，证明 e1 < e2。
  直觉：先比 z（index=2）：e1 的 z 次数 = 1，e2 的 z 次数 = 2，所以 e1 < e2。
  -/
  lemma rightLex_example :
      Finsupp.Lex (· > ·) (· < ·) e1 e2 := by
    classical
    -- 选“分歧点” i = 2（也就是 z）
    refine ⟨(2 : σ), ?_ , ?_⟩
    -- 1) 先验相等性：对所有 j，若 j > 2 则 e1 j = e2 j（在 Fin 3 里根本没有 j > 2，故平凡成立）
    · intro j hj
      have hj' : (j : ℕ) ≤ 2 := by
        -- 在 Fin 3 里任何 j 都 ≤ 2
        simpa [Fin.last] using (Fin.le_last j)
      have : False := (Nat.not_lt.mpr hj') hj
      exact this.elim
    -- 2) 在 i=2 处，值满足  e1 2 < e2 2
    ·
      have h1 : e1 (2 : σ) = 1 := by
        -- e1 的 z 次数：single 2 1 贡献 1，其余在 2 处为 0
        simp only [e1, Fin.isValue, add_assoc, add_apply, ne_eq, Fin.reduceEq, not_false_eq_true,
          single_eq_of_ne, single_eq_same, zero_add]
      have h2 : e2 (2 : σ) = 2 := by
        -- e2 的 z 次数：single 2 2 贡献 2
        simp only [e2, Fin.isValue, add_apply, ne_eq, Fin.reduceEq, not_false_eq_true,
          single_eq_of_ne, single_eq_same, zero_add]
      -- 从 h1, h2 得到 1 < 2
      simp only [Fin.isValue, h1, h2, Nat.one_lt_ofNat]
end




/- 指数向量（只看单项式的次数，不看系数） -/
noncomputable def x2yz  : Fin 3 →₀ ℕ := single 0 2 + single 1 1 + single 2 1   -- x^2 y z

noncomputable def xy3   : Fin 3 →₀ ℕ := single 0 1 + single 1 3                -- x y^3



noncomputable def x3yz  : Fin 3 →₀ ℕ := single 0 3 + single 1 1 + single 2 1   -- x^3 y z
noncomputable def y2z2  : Fin 3 →₀ ℕ :=              single 1 2 + single 2 2  -- y^2 z^2

lemma example2 :toLex y2z2 < toLex x3yz :=by
  apply lex_lt_iff.mpr
  simp only [ofLex_toLex]
  use 0
  constructor
  · -- 对所有 j<0：在 Fin 3 里根本不存在，所以平凡成立
    intro j hj
    by_contra
    exact Nat.not_succ_le_zero j hj
  · -- 在 i=0 处：0 < 3
    have h1:y2z2 0=0:=by simp [y2z2]
    have h2:x3yz 0=3:=by simp [x3yz]
    rw[h1,h2]
    simp






section
  set_option linter.unusedVariables false
  /- 下面三个引理对应链：e_y2z2 > e_x3yz > e_x2yz > e_xy3，
     我们分别证明 `RLEX` 下的严格小于关系： -/

  /- 先比 z 次数：1 < 2，所以 `x^3yz < y^2z^2` -/
  lemma lex_x3yz_lt_y2z2 : Finsupp.Lex (· > ·) (· < ·) x3yz y2z2 := by
    refine ⟨(2 : σ), ?_, ?_⟩
    · -- 对所有 j>2：在 Fin 3 里根本不存在，所以平凡成立
      intro j hj
      have hjle : j ≤ (2 : σ) := by simpa using (Fin.le_last j)
      exact (not_lt_of_ge hjle hj).elim
    · -- 在 i=2 处：1 < 2
      simp only [x3yz, Fin.isValue, add_apply, ne_eq, Fin.reduceEq, not_false_eq_true,
       single_eq_of_ne,  single_eq_same, zero_add, y2z2, Nat.one_lt_ofNat]


  /- z、y 次数都相同：在 i=0 处 2 < 3，所以 `x^2yz < x^3yz` -/
  lemma lex_x2yz_lt_x3yz : Finsupp.Lex (· > ·) (· < ·) x2yz x3yz := by
    refine ⟨(0 : σ), ?eq_high, ?lt_at_i⟩
    · -- 需证对所有 j>0（即 j=1 或 2）两边相等
      intro j hj
      -- 把 j 枚举为 0/1/2 三种可能
      -- j=0 与假设 j>0 矛盾；j=1,2 直接 `simp`
      -- （这段是最直接可靠的 Fin 3 穷举）
      have : j = 0 ∨ j = 1 ∨ j = 2 := by
        -- Fin 3 只有 0,1,2
        fin_cases j <;> simp
      rcases this with rfl | h1 | h2
      · -- j=0，不可能，因为假设 j>0
        exact (lt_irrefl (0 : σ) (by simp only [Fin.isValue, gt_iff_lt, lt_self_iff_false] at hj)).elim
      · -- j=1
        simp [x2yz, x3yz, Finsupp.add_apply, add_assoc,h1]
      · -- j=2
        simp [x2yz, x3yz, Finsupp.add_apply, add_assoc,h2]
    · -- i=0 处 2 < 3
      simp [x2yz, x3yz, Finsupp.add_apply, add_comm,  add_assoc]

  /- 比 z 次数：0 < 1，所以 `xy^3 < x^2yz` -/
  lemma lex_xy3_lt_x2yz : Finsupp.Lex (· > ·) (· < ·) xy3 x2yz := by
    classical
    refine ⟨(2 : σ), ?eq_high, ?lt_at_i⟩
    · -- 对所有 j>2：不存在
      intro j hj
      have hjle : j ≤ (2 : σ) := by simpa using (Fin.le_last j)
      exact (not_lt_of_ge hjle hj).elim
    · -- i=2 处：0 < 1
      simp [xy3, x2yz, Finsupp.add_apply, add_assoc]


  /-- 把三个比较串起来：`y^2z^2 > x^3yz > x^2yz > xy^3`。 -/
  theorem right_lex_descending_chain :
      Finsupp.Lex (· > ·) (· < ·) x3yz y2z2 ∧
      Finsupp.Lex (· > ·) (· < ·) x2yz x3yz ∧
      Finsupp.Lex (· > ·) (· < ·) xy3  x2yz := by
    exact ⟨lex_x3yz_lt_y2z2, ⟨lex_x2yz_lt_x3yz, lex_xy3_lt_x2yz⟩⟩
end


noncomputable def p : MvPolynomial (Fin 3) ℝ :=
  monomial (Finsupp.single 0 2 + Finsupp.single 1 1) (3 : ℝ)

#check MonomialOrder

private def toDualEquiv (α : Type*) : α ≃ OrderDual α :=
{ toFun := OrderDual.toDual, invFun := OrderDual.ofDual,
  left_inv := by intro x; rfl, right_inv := by intro x; rfl }

noncomputable def MonomialOrderlex (n:ℕ) :
  MonomialOrder (Fin n) where
  syn := Lex (OrderDual (Fin n) →₀ ℕ)
  acm:=by infer_instance
  lo:=by infer_instance
  iocam:=by infer_instance
  toSyn:=
  (Finsupp.domCongr (toDualEquiv (Fin n))).trans {
    toEquiv  := toLex
    map_add' := toLex_add }
  toSyn_monotone:=by
    intro x y h
    have h' :
      (Finsupp.domCongr (toDualEquiv (Fin n))) x ≤
      (Finsupp.domCongr (toDualEquiv (Fin n))) y := by
      intro i; simpa using h (OrderDual.ofDual i)
    exact Finsupp.toLex_monotone h'
  wf:=by infer_instance

example : LinearOrder (Lex (OrderDual σ →₀ ℕ)) := by exact Lex.linearOrder
example (n:ℕ): LinearOrder (OrderDual (Fin n)):=by infer_instance
#check IsNoetherian

instance  {n : ℕ} :
  IsNoetherianRing (MvPolynomial (Fin n) ℝ ) :=by
    exact isNoetherianRing_fin
#check refl
#check unique
#check EuclideanGeometry.oangle
#check Finsupp
#check Matrix.det
#check DegLex
--尝试证明分次逆字典序是项序


lemma grlex1:toDegLex y2z2 < toDegLex x3yz:=by
  -- 比较度（degree），由于 degree(y2z2) < degree(x3yz)，所以 y2z2 < x3yz
  refine DegLex.lt_iff.mpr ?_
  left
  simp only [y2z2, Fin.isValue, ofDegLex_toDegLex, degree_add, degree_single, Nat.reduceAdd, x3yz,
    Nat.lt_add_one]

lemma grlex2:toDegLex y2z2 < toDegLex xy3:=by
  -- 比较度（degree），由于 degree(y2z2) < degree(x3yz)，所以 y2z2 < x3yz
  refine DegLex.lt_iff.mpr ?_
  right
  constructor
  ·
    simp only [xy3, Fin.isValue, ofDegLex_toDegLex, degree_add, degree_single, Nat.reduceAdd, y2z2]
  ·
    simp only [ofDegLex_toDegLex,lex_lt_iff]
    let i:=(0:Fin 3)
    use i
    unfold i
    constructor
    ·
      simp only [Fin.isValue, Fin.not_lt_zero, ofLex_toLex, IsEmpty.forall_iff, implies_true]
    ·
      simp only [y2z2, Fin.isValue, toLex_add, ofLex_add, ofLex_toLex, Finsupp.coe_add,
        Pi.add_apply, ne_eq, one_ne_zero, not_false_eq_true, single_eq_of_ne, Fin.reduceEq,
        add_zero, xy3, single_eq_same, zero_lt_one]


section
  set_option linter.unusedVariables false
  /- 下面我们证明这几个单项式的排序：
     证明 2x^3yz > 4y^2z^2 > x^2yz > 3xy^3 -/

  /-- 2x^3yz 和 4y^2z^2，先比较总次数，再比较字典序 -/
  lemma grevlex_x3yz_gt_y2z2 : Finsupp.DegLex (· > ·) (· < ·) y2z2 x3yz := by
    simp only [gt_iff_lt, degLex_def]
    refine Prod.lex_def.mpr ?_
    left
    simp only [y2z2, Fin.isValue, degree_add, degree_single, Nat.reduceAdd, x3yz, Nat.lt_add_one]

  /-- x^2yz 和 2x^3yz，首先比较总次数（x^3yz 总次数大） -/
  lemma grevlex_x2yz_lt_x3yz : Finsupp.DegLex (· > ·) (· < ·) x2yz x3yz := by
    simp only [gt_iff_lt, degLex_def]
    refine Prod.lex_def.mpr ?_
    left
    simp only [x2yz, Fin.isValue, degree_add, degree_single, Nat.reduceAdd, x3yz, Nat.lt_add_one]

  /-- y^2z^2 和 3xy^3，先比较总次数（y^2z^2 总次数大） -/
  lemma grevlex_y2z2_gt_xy3 : Finsupp.DegLex (· > ·) (· < ·) xy3 y2z2 := by
    simp only [gt_iff_lt, degLex_def]
    refine Prod.lex_def.mpr ?_
    right
    constructor
    ·
      simp only [xy3, Fin.isValue, degree_add, degree_single, Nat.reduceAdd, y2z2]
    ·
      simp only [lex_def]
      let j:=(2:Fin 3)
      use j
      unfold j
      constructor
      ·
        intro d hd
        simp only [xy3, Fin.isValue, Finsupp.coe_add, Pi.add_apply, y2z2]
        have hjle : d ≤ (2 : σ) := by simpa using (Fin.le_last d)
        exact (not_lt_of_ge hjle hd).elim
      ·
        simp only [xy3, Fin.isValue, Finsupp.coe_add, Pi.add_apply, ne_eq, Fin.reduceEq,
          not_false_eq_true, single_eq_of_ne, add_zero, y2z2, single_eq_same, zero_add,
          Nat.ofNat_pos]

  lemma grevlex_x2yz_gt_xy3 : Finsupp.DegLex (· > ·) (· < ·) xy3 x2yz := by
    simp only [gt_iff_lt, degLex_def]
    refine Prod.lex_def.mpr ?_
    right
    constructor
    ·
      simp only [xy3, Fin.isValue, degree_add, degree_single, Nat.reduceAdd, x2yz]
    ·
      simp only [lex_def]
      let j:=(2:Fin 3)
      use j
      unfold j
      constructor
      ·
        intro d hd
        simp only [xy3, Fin.isValue, Finsupp.coe_add, Pi.add_apply, x2yz]
        have hjle : d ≤ (2 : σ) := by simpa using (Fin.le_last d)
        exact (not_lt_of_ge hjle hd).elim
      ·
        simp only [xy3, Fin.isValue, Finsupp.coe_add, Pi.add_apply, ne_eq, Fin.reduceEq,
          not_false_eq_true, single_eq_of_ne, add_zero, x2yz, single_eq_same, zero_add, zero_lt_one]


  lemma grevlex_y2z2_gt_x2yz : Finsupp.DegLex (· > ·) (· < ·) x2yz y2z2 := by
    simp only [gt_iff_lt, degLex_def]
    refine Prod.lex_def.mpr ?_
    right
    constructor
    ·
      simp only [y2z2, Fin.isValue, degree_add, degree_single, Nat.reduceAdd, x2yz]
    ·
      simp only [lex_def]
      let j:=(2:Fin 3)
      use j
      unfold j
      constructor
      ·
        intro d hd
        simp only [y2z2, Fin.isValue, Finsupp.coe_add, Pi.add_apply, x2yz]
        have hjle : d ≤ (2 : σ) := by simpa using (Fin.le_last d)
        exact (not_lt_of_ge hjle hd).elim
      ·
        simp only [x2yz, Fin.isValue, Finsupp.coe_add, Pi.add_apply, ne_eq, Fin.reduceEq,
          not_false_eq_true, single_eq_of_ne, add_zero, single_eq_same, zero_add, y2z2,
          Nat.one_lt_ofNat]

  /-- 最后把这些比较连接起来：2x^3yz > 4y^2z^2 > x^2yz > 3xy^3 -/
  theorem grevlex_descending_chain :
      Finsupp.DegLex (· > ·) (· < ·) y2z2 x3yz ∧
      Finsupp.DegLex (· > ·) (· < ·) x2yz y2z2 ∧
      Finsupp.DegLex (· > ·) (· < ·) xy3 x2yz:= by
    exact ⟨grevlex_x3yz_gt_y2z2, ⟨grevlex_y2z2_gt_x2yz, grevlex_x2yz_gt_xy3⟩⟩
end

variable {α : Type*}

open scoped Function in  def grevLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) (s_val : ℕ → ℕ → Prop):
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s_val)) on (fun x ↦ (x.degree, x))

theorem grevLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop}{s_val : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    grevLex r s s_val a b ↔ Prod.Lex s (Finsupp.Lex r s_val) (a.degree, a) (b.degree, b) :=
  Iff.rfl

lemma grevLex1:grevLex (· < ·) (· < ·) (· > ·) x2yz xy3:=by
  simp only [gt_iff_lt, grevLex_def]
  refine Prod.lex_def.mpr ?_
  right
  constructor
  ·
    simp only [x2yz, Fin.isValue, degree_add, degree_single, Nat.reduceAdd, xy3]
  ·
    simp only [lex_def]
    let j:=(0:Fin 3)
    use j
    unfold j
    constructor
    ·
      simp only [Fin.isValue, Fin.not_lt_zero, IsEmpty.forall_iff, implies_true]
    ·
      simp only [xy3, Fin.isValue, Finsupp.coe_add, Pi.add_apply, single_eq_same, ne_eq,
        one_ne_zero, not_false_eq_true, single_eq_of_ne, add_zero, x2yz, Fin.reduceEq,
        Nat.one_lt_ofNat]



noncomputable def e:Fin 3 →₀ ℕ :=single 1 2 + single 2 3

example :e 2 = 3  :=by
  simp [e]


variable {n : ℕ}
def PAF (a : Fin n →₀ ℤ) (s : Fin n) : ℤ :=
  ∑ x , a x * a (x + s)

def IsLegendrePair (a b : Fin n  →₀ ℤ) : Prop :=
  (∀ i , a i = 1 ∨ a i = -1) ∧
  (∀ i , b i = 1 ∨ b i = -1) ∧
  (∀ (s : Fin n), 1 ≤ s.val ∧ s.val ≤ (n - 1) / 2 → (PAF a s) + (PAF b s) = -2)

lemma Islp_iff (a b : Fin n  →₀ ℤ):
  IsLegendrePair a b ↔
  (∀ i , a i = 1 ∨ a i = -1) ∧
  (∀ i , b i = 1 ∨ b i = -1) ∧
  (∀ (s : Fin n), 1 ≤ s.val ∧ s.val ≤ (n - 1) / 2 → (PAF a s) + (PAF b s) = -2):=Iff.rfl

noncomputable def s1:Fin 7 →₀ ℤ :=single 0 1 + single 1 1 + single 2 1 + single 3 (-1) +single 4 1 + single 5 (-1) +single 6 (-1)

example :IsLegendrePair s1 s1:=by
  refine (Islp_iff s1 s1).mpr ?_
  split_ands
  ·
    simp [s1]
    intro i
    fin_cases i
    simp;simp;simp;simp;simp;simp;simp
  ·
    simp [s1]
    intro i
    fin_cases i
    simp;simp;simp;simp;simp;simp;simp
  ·
    simp
    intro s hs1 hs2
    fin_cases s
    ·
      linarith
    ·
      simp [PAF]
      have : (Finset.univ : Finset (Fin 7)) = {0,1,2,3,4,5,6} :=rfl
      simp [this,s1]
    ·
      simp [PAF]
      have : (Finset.univ : Finset (Fin 7)) = {0,1,2,3,4,5,6} :=rfl
      simp [this,s1]
    ·
      simp [PAF]
      have : (Finset.univ : Finset (Fin 7)) = {0,1,2,3,4,5,6} :=rfl
      simp [this,s1]
    ·
      linarith
    ·
      linarith
    ·
      linarith


example (α β : Type*) [LinearOrder α] [LinearOrder β] : LinearOrder (α ×ₗ β):=by exact Prod.Lex.instLinearOrder α β


#check MvPolynomial

set_option linter.style.commandStart false

noncomputable def mo : MvPolynomial (Fin 3) ℝ:=C 3 * X 0 ^ 2

open MonomialOrder
