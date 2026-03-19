import Mathlib
open MvPolynomial Finsupp Real
open scoped BigOperators

namespace MonomialOrder

example (x : ℝ) : x^3 + x^2 + x + 1 = 0 ↔ x = -1 ∨ x = 1:=by
  constructor
  · intro p
    have h1:x≠0:=by
      intro p1
      subst p1
      simp at p
    have h2:x^2 + x + 1 + 1/x = 0:=by field_simp;simp only [mul_zero];rw[←p];ring
    have h3:x^2 + x + 1 = - (1/x):=by linarith
    have h4:x^3 - (1/x) = 0:=by linarith
    field_simp at h4
    simp only [mul_zero] at h4
    rw[show x^4-1=(x^2+1)*(x^2-1) by ring] at h4
    have h5:x^2+1 >0:=by positivity
    simp only [mul_eq_zero] at h4
    cases h4 with
    | inl h=>
      rw [h] at h5
      simp only [gt_iff_lt, lt_self_iff_false] at h5
    | inr h=>
      rw[show x^2-1=(x+1)*(x-1) by ring] at h
      simp only [mul_eq_zero] at h
      cases h with
      |inl l=>
        left
        linarith
      |inr r=>
        right
        linarith
  · intro p
    cases p with
    |inl l=>
      subst l
      ring
    |inr r=>
      subst r
      ring_nf
      simp_all
      sorry

section
variable {σ R : Type*} [CommSemiring R]
variable (m : MonomialOrder σ)



/-- `leadingMonomial`：**系数规范为 1** 的首项（零多项式的首项约定为 `0`）。 -/
noncomputable def leadingMonomial (f : MvPolynomial σ R) : MvPolynomial σ R :=by
  classical
  exact if h : f = 0 then 0 else monomial (m.degree f) (1 : R)


@[simp] lemma leadingMonomial_of_ne {f : MvPolynomial σ R} (hf : f ≠ 0) :
    m.leadingMonomial f = monomial (m.degree f) (1 : R) := by
  simp [leadingMonomial, hf]

/-! ### Groebner 基的定义 -/
/-- `G` 是理想 `I` 的 Gröbner 基。 -/
def IsGroebnerBasis (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingMonomial '' I) = Ideal.span (m.leadingMonomial '' G)

/-- Groebner 基的一个直接推论：对任意 `f ∈ ⟨G⟩`，其首项都落在由 `G` 首项生成的理想中。 -/
lemma IsGroebnerBasis.leadingMonomial_mem_span_image
    {G : Set (MvPolynomial σ R)} (hG : m.IsGroebnerBasis G (Ideal.span G))
    {f : MvPolynomial σ R} (hf : f ∈ Ideal.span G) :
    m.leadingMonomial f ∈ Ideal.span (m.leadingMonomial '' G) := by
  have hx :
      m.leadingMonomial f ∈
        Ideal.span (m.leadingMonomial '' (↑(Ideal.span G) : Set (MvPolynomial σ R))) := by
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  -- 再用 GroebnerBasis₂ 的等式部分改写到目标
  simpa [hG.2] using hx

end


section Ring

variable {σ ι R : Type*} [CommRing R]
/-! ### 首项可约性 -/
/-- 首项可约性：存在某个 `i` 使 `LM(b i) ≤ LM(f)` 且 `LM(f) ≠ 0` -/
def HeadReducible
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (f : MvPolynomial σ R) : Prop :=
  f ≠ 0 ∧ ∃ i, m.degree (b i) ≤ m.degree f


/-- 从 `HeadReducible` 中挑一个可约的下标（非构造性选择） -/
noncomputable def chooseHead (m : MonomialOrder σ)
(b : ι → MvPolynomial σ R) (f : MvPolynomial σ R) (h : HeadReducible m b f) :
{ i : ι // m.degree (b i) ≤ m.degree f } :=
⟨Classical.choose h.2, Classical.choose_spec h.2⟩



section TerminationInstances

variable (m : MonomialOrder σ) in
/-- 在 `m.syn` 上用 `<` 做良基关系（来自 `m.wf`） -/
instance : WellFoundedRelation m.syn where
  rel := (· < ·)
  wf  := (m.wf).wf

/-! ### 对一族多项式的“约化到余式” -/
/-- 对一族多项式的“完全首项约化”————返回余式。 -/
noncomputable def reduceFamily
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    MvPolynomial σ R → MvPolynomial σ R
| f =>
  by
    by_cases hf0 : f = 0
    · exact 0
    · by_cases h : HeadReducible m b f
      · by_cases hdeg0 : m.degree f = 0
        · exact 0
        · let i := (m.chooseHead b f h).val
          have hi := (m.chooseHead b f h).property
          exact reduceFamily m b hb (m.reduce (hb i) f)
      · by_cases hdeg0 : m.degree f = 0
        · exact f
        · exact m.leadingTerm f + reduceFamily m b hb (m.subLTerm f)
termination_by f => m.toSyn (m.degree f)
decreasing_by
  · -- 分支：`deg f ≠ 0` 且可约 ⇒ 一步 `reduce` 后首项严格下降
    -- 这里 `h : HeadReducible m b f`，取出选到的下标与 `deg f ≠ 0`
    let i := (chooseHead (m := m) (b := b) f h).val
    have hi := (chooseHead (m := m) (b := b) f h).property
    exact m.degree_reduce_lt (hb i) hi hdeg0
  · -- 分支：不可约且 `deg f ≠ 0` ⇒ 去掉首项后严格下降
    exact m.degree_sub_LTerm_lt (f := f) hdeg0

end TerminationInstances

/-- 若 `f = 0`，完全约化的余式就是 `0`。 -/
@[simp] lemma reduceFamily_eq_zero
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    m.reduceFamily b hb 0 = 0 := by
  simp [reduceFamily]


lemma reduce_eq_zero_of_deg0_head
    (m : MonomialOrder σ)
    {f h : MvPolynomial σ R}
    (hf0 : m.degree f = 0) (hh0 : m.degree h = 0)
    (uh : IsUnit (m.leadingCoeff h)) :
    m.reduce uh f = 0 := by
  classical
  have hfC  : f = C (m.leadingCoeff f)     := m.eq_C_of_degree_eq_zero hf0
  have hhC  : h = C (m.leadingCoeff h)     := m.eq_C_of_degree_eq_zero hh0
  unfold MonomialOrder.reduce
  rw [hf0, hh0, tsub_self,hfC]
  set a : R := ((↑(uh.unit⁻¹) : R) * m.leadingCoeff f) with ha
  have hEq :
      (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * h
        = (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * C (m.leadingCoeff h) := by
    conv_lhs=>
      rw [hhC]
  calc
    (C : R →+* MvPolynomial σ R) (m.leadingCoeff f)
      - (monomial (0 : σ →₀ ℕ)
           (↑uh.unit⁻¹ * m.leadingCoeff ((C : R →+* MvPolynomial σ R) (m.leadingCoeff f))))
           * h
        = (C : R →+* MvPolynomial σ R) (m.leadingCoeff f)
          - (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * h := by
            simp [MonomialOrder.leadingCoeff, MonomialOrder.degree_C, ha]
    _   = (C : R →+* MvPolynomial σ R) (m.leadingCoeff f)
          - (C : R →+* MvPolynomial σ R) (m.leadingCoeff f) := by
            rw [(hEq.trans (show (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * C (m.leadingCoeff h)
        = C (a * m.leadingCoeff h) by simp)).trans
        (show (C : R →+* MvPolynomial σ R) (a * m.leadingCoeff h)
    = (C : R →+* MvPolynomial σ R) (m.leadingCoeff f) by rw[show a * m.leadingCoeff h
          = m.leadingCoeff f * (((↑(uh.unit⁻¹) : R) * m.leadingCoeff h)) by ring];simp)]
    _   = 0 := by
            simp



/-- **常数情形：一步约化为 0**
若 `m.degree f = 0`，且某个生成元也满足 `m.degree (b i) ≤ m.degree f`（于是 `m.degree (b i) = 0`），
再加上 `hb i : IsUnit (lc(b i))`，则一步头部约化 `reduce (hb i) f = 0`。 -/
lemma reduce_const_step_to_zero
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R} (hdeg0 : m.degree f = 0)
    {i : ι} (hi : m.degree (b i) ≤ m.degree f) :
    m.reduce (hb i) f = 0 := by
  classical
  -- 先把 b i 也压到常数
  have hbi0 : m.degree (b i) = 0 := by
    have : m.degree (b i) ≤ 0 := by simpa [hdeg0] using hi
    exact le_antisymm this (by simp)
  -- 把 f 与 b i 都写成常数多项式
  have hfC  : f   = C (m.leadingCoeff f)     := m.eq_C_of_degree_eq_zero hdeg0
  have hbiC : b i = C (m.leadingCoeff (b i)) := m.eq_C_of_degree_eq_zero hbi0
  -- 单位的“反乘恒等式”，降到 `R` 上使用
  have hunit_R : ( (↑((hb i).unit⁻¹) : R) * (m.leadingCoeff (b i)) ) = 1 := by
    simp
  exact reduce_eq_zero_of_deg0_head m hdeg0 hbi0 (hb i)





/-- 若 `m.degree f = 0` 且 **不可首项约化**，余式就是 `f` 本身。 -/
lemma reduceFamily_eq_notHead_deg0
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R}
    (hf0 : f ≠ 0) (hnot : ¬ HeadReducible m b f) (hdeg0 : m.degree f = 0) :
    m.reduceFamily b hb f = f := by
  simp [reduceFamily, hf0, hnot, hdeg0]



/-- 关键小引理：做一步 `reduce` 后，差值属于 `Ideal.span (Set.range b)`。 -/
lemma sub_reduce_mem_span_range
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (i : ι) (f : MvPolynomial σ R) :
    f - m.reduce (hb i) f ∈ Ideal.span (Set.range b) := by
    classical
        -- 令 t 为“配平的那个倍数乘 b i”
        set t :
            MvPolynomial σ R :=
          MvPolynomial.monomial (m.degree f - m.degree (b i))
            ((hb i).unit⁻¹ * m.leadingCoeff f) * b i with ht
        -- 先把差改写成 t：f - (f - t) = t
        have hdiff : f - m.reduce (hb i) f = t := by
          -- 这里只展开 `reduce` 自身一次；用 `sub_sub_cancel` 结束
          simp only [reduce, sub_sub_cancel]
          rw [ht]
        -- 只需证 t ∈ span(range b)
        -- 因为 b i ∈ span(range b)，而理想对环元素的标量乘法（即乘法）闭合
        have hbmem : b i ∈ Ideal.span (Set.range b) :=
          Ideal.subset_span ⟨i, rfl⟩
        have : t ∈ Ideal.span (Set.range b) := by
          -- 用 `I.smul_mem`，并把 `•` 改写成乘法
          -- 先把 t 的“系数部分”命名出来，便于 `smul` 写法
          set c :
              MvPolynomial σ R :=
            MvPolynomial.monomial (m.degree f - m.degree (b i))
              ((hb i).unit⁻¹ * m.leadingCoeff f) with hc
          -- a • x ∈ I
          have hx : c • b i ∈ Ideal.span (Set.range b) :=
            (Ideal.span (Set.range b)).smul_mem c hbmem
          -- 把 `•` 换成 `*`
          simpa [ht, hc, smul_eq_mul] using hx
        -- 回代差等式
        simpa [hdiff] using this

set_option linter.unusedVariables false in
lemma reduceFamily_eq_head_step
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R}
    (hf0 : f ≠ 0) (h : HeadReducible m b f) :
    ∃ (i : ι)
      (hi : m.degree (b i) ≤ m.degree f ),
      m.reduceFamily b hb f = m.reduceFamily b hb (m.reduce (hb i) f) := by
  by_cases hdegpos : m.degree f ≠ 0
  · refine ⟨(m.chooseHead b f h).val, (m.chooseHead b f h).property, ?_⟩
    -- 只改写左边：展开一次定义，并用 hf0 / h 选中“可头约”分支
    conv_lhs =>
      unfold MonomialOrder.reduceFamily
      -- 这里的 `simp` 只用 `hf0` 和 `h` 做**分支选择**，
      -- 不会在子项里继续展开 `reduceFamily`（因为我们没把它放进 simp 集）
      simp [hf0, h,hdegpos]
  · simp only [ne_eq, not_not] at hdegpos
    -- 用 reduceFamily 定义里真的用到的下标，避免不匹配
    refine ⟨(m.chooseHead b f h).val, (m.chooseHead b f h).property, ?_⟩
    -- 记号
    set i := (m.chooseHead b f h).val
    have hi : m.degree (b i) ≤ m.degree f := (m.chooseHead b f h).property
    -- 展开左边一次定义，并只用 hf0/h 选分支（不展开递归体）
    conv_lhs =>
      unfold MonomialOrder.reduceFamily
      simp [hf0, h]      -- 选中“可头约化”分支；留下 `if m.degree f = 0 then … else …`
    -- 由 hi 与 deg f = 0 推出 deg(b i) = 0
    have hbi0 : m.degree (b i) = 0 := by
      have : m.degree (b i) ≤ 0 := by simpa [hdegpos] using hi
      exact le_antisymm this (by simp)
    -- 常数对常数做一步 reduce（且 lc(b i) 为单位）得到 0
    have hred0 : m.reduce (hb i) f = 0 :=
      reduce_eq_zero_of_deg0_head (m := m) hdegpos hbi0 (hb i)
    -- 现在把 `if` 用 hdeg0 挑成 then 分支，并把右边的 reduceFamily(0) 化成 0
    simp only [hdegpos, hred0, reduceFamily_eq_zero]
    simp only [↓reduceIte]

/-- 若不可首项约化且 `m.degree f ≠ 0`，则“剥掉首项并递归处理剩余”。 -/
lemma reduceFamily_eq_notHead_degpos
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R} (hf0 : f ≠ 0) (hnot : ¬ HeadReducible m b f)
    (hdegpos : m.degree f ≠ 0) :
    m.reduceFamily b hb f =
      m.leadingTerm f + m.reduceFamily b hb (m.subLTerm f) := by
  classical
  -- 只改写左边：展开一次定义，并用 `hf0` / `hnot` / `hdegpos` 选中目标分支
  conv_lhs =>
    unfold MonomialOrder.reduceFamily
    -- 这里的 `simp` 只做“分支选择”，不会深入右侧的递归调用
    simp [hf0, hnot, hdegpos]
  -- 现在左右两边完全相同

/-- **常数且可首约 ⇒ `reduceFamily` 直接归零**
假设 `deg f = 0`、`f ≠ 0` 且满足“头可约”（存在某个 `i` 使 `deg (b i) ≤ deg f`；是否把 `f ≠ 0`
包含在 `HeadReducible` 的定义里都无所谓），则 `reduceFamily b hb f = 0`。 -/
lemma reduceFamily_const_head_case_zero
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R} (hf0 : f ≠ 0) (hdeg0 : m.degree f = 0)
    (hhead : ∃ i, m.degree (b i) ≤ m.degree f) :
    m.reduceFamily b hb f = 0 := by
  classical
  rcases hhead with ⟨i, hi⟩
  have hred0 : m.reduce (hb i) f = 0 :=
    reduce_const_step_to_zero (m := m) (b := b) (hb := hb) (f := f) hdeg0 hi
  unfold MonomialOrder.reduceFamily
  simp only [hf0, dite_false]
  have : HeadReducible m b f := by
    exact ⟨hf0,i, hi⟩
  simp [this, hdeg0]

/-- 在 `d ≠ degree f` 时，`initTerm f` 在指数 `d` 处的系数为 `0`。 -/
lemma coeff_initTerm_of_ne_degree (m : MonomialOrder σ)
    (f : MvPolynomial σ R) {d : σ →₀ ℕ} (hne : d ≠ m.degree f) :
    (m.leadingTerm f).coeff d = 0 := by
  classical
  simp only [leadingTerm, coeff_monomial, ite_eq_right_iff, leadingCoeff_eq_zero_iff]
  intro p
  subst p
  simp_all only [ne_eq, not_true_eq_false]

/-- 在已知 `f ≠ 0` 的前提下，“不可首项约化” ⇔ 对所有 `i` 都有 `¬ LM(b i) ≤ LM(f)`。 -/
lemma not_headReducible_iff_forall
(m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
{f : MvPolynomial σ R} (hf0 : f ≠ 0) :
(¬ HeadReducible m b f) ↔ (∀ i, ¬ (m.degree (b i) ≤ m.degree f)) := by
  classical
  unfold HeadReducible
  constructor
  · intro hnot i hi
    exact hnot ⟨hf0, ⟨i, hi⟩⟩
  · intro hAll ⟨_, ⟨i, hi⟩⟩
    exact hAll i hi





def μ {σ R : Type*} [CommRing R] (m : MonomialOrder σ)
  (f : MvPolynomial σ R) : m.syn :=
  m.toSyn (m.degree f)

-- 良基
lemma wf_μ
  {σ R : Type*} [CommRing R]
  (m : MonomialOrder σ) :
  WellFounded (fun f g : MvPolynomial σ R => m.μ f < m.μ g) := by
  simpa [Function.onFun] using ((m.wf).wf).onFun

/-- `reduceFamily` 的结果对 `b` 不再可首项约化。 -/
lemma reduceFamily_not_headReducible
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (f : MvPolynomial σ R) :
    ¬ HeadReducible m b (m.reduceFamily b hb f) :=
sorry


/-**重要结论**-/
/-- 对给定的一组多项式 b 和任意多项式 f ,f 减去它对 b 做多项式约化得到的余式，属于由 b 生成的理想 -/
lemma reduceFamily_sub_mem_span_range
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (f : MvPolynomial σ R) :
    f - m.reduceFamily b hb f ∈ Ideal.span (Set.range b) :=
by
  classical
  refine
    ((wf_μ (σ := σ) (R := R) (m := m)).induction
      f
      (C := fun y => y - m.reduceFamily b hb y ∈ Ideal.span (Set.range b))
      ?step)
  intro f IH
  by_cases hf0 : f = 0
  · simp only [hf0, reduceFamily_eq_zero, sub_self, zero_mem]
  · by_cases h : HeadReducible m b f
    · by_cases hdeg0 : m.degree f = 0
      · rcases h with ⟨h, ⟨i, hi⟩⟩
        have h0 : m.degree (b i) = 0 :=
          le_antisymm (by simpa [hdeg0] using hi) (by simp)
        have : (1 : MvPolynomial σ R) ∈ Ideal.span (Set.range b) := by
          have hbmem : b i ∈ Ideal.span (Set.range b) := Ideal.subset_span ⟨i, rfl⟩
          have hbi : b i = C (m.leadingCoeff (b i)) :=
            (m.degree_eq_zero_iff (f := b i)).1 h0
          have hc_mem :
          (C (m.leadingCoeff (b i)) : MvPolynomial σ R) ∈ Ideal.span (Set.range b) := by
            rw[←hbi]
            exact hbmem
          have hunit :
            IsUnit (C (m.leadingCoeff (b i)) : MvPolynomial σ R) := by
            simpa using IsUnit.map (C : R →+* MvPolynomial σ R) (hb i)
          have Itop : Ideal.span (Set.range b) = (⊤ : Ideal (MvPolynomial σ R)) :=
            by exact Ideal.eq_top_of_isUnit_mem (Ideal.span (Set.range b)) hc_mem hunit
          have one_mem : (1 : MvPolynomial σ R) ∈ Ideal.span (Set.range b) :=by
            simp [Itop]
          exact one_mem
        have hfmem : f ∈ Ideal.span (Set.range b) := by
          simpa using Ideal.mul_mem_left (I := Ideal.span (Set.range b)) f this
        simp only [reduceFamily, hf0, ↓reduceDIte, HeadReducible, ne_eq, not_false_eq_true, hdeg0,
          nonpos_iff_eq_zero, true_and, dite_eq_ite]
        simp_all only [not_false_eq_true, ne_eq, le_refl]
        split
        next h_1 => simp_all only [sub_zero]
        next h_1 => simp_all only [not_exists, sub_self, zero_mem]
      · rcases m.reduceFamily_eq_head_step (b := b) (hb := hb)
            hf0 h with ⟨i, hi, hdef⟩
        have μlt : m.toSyn (m.degree (m.reduce (hb i) f)) < m.toSyn (m.degree f) :=
          m.degree_reduce_lt (hb i) hi hdeg0
        have IH' := IH (m.reduce (hb i) f) μlt
        simpa [hdef, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using Ideal.add_mem _ (sub_reduce_mem_span_range m b hb i f) IH'
    · by_cases hdeg0 : m.degree f = 0
      · simp [reduceFamily_eq_notHead_deg0 (m := m) (b := b) (hb := hb) hf0 h hdeg0]
      · have μlt : μ m (m.subLTerm f) < μ m f :=
          m.degree_sub_LTerm_lt (f := f) hdeg0
        have IH' := IH (m.subLTerm f) μlt
        simpa [reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb) hf0 h hdeg0,
               MonomialOrder.subLTerm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using IH'



/-- 若 `e ≤ d` 不成立，则对任意 `p`，`coeff d (p * monomial e 1) = 0`。 -/
lemma coeff_mul_monomial_one_of_not_le
{d e : σ →₀ ℕ} (p : MvPolynomial σ R) (hne : ¬ e ≤ d) :
coeff d (p * monomial e (1 : R)) = 0 := by
  classical
  -- 展开卷积求和
  simp only [coeff_mul, coeff_monomial]  -- 目标变成对 antidiagonal 的求和
  -- 关键：对每个 (a,b) ∈ antidiagonal d，有 b ≤ d
  have hb_le : ∀ x ∈ Finset.antidiagonal d, x.2 ≤ d := by
    intro x hx
    -- antidiagonal 的定义：x.1 + x.2 = d
    have hxsum : x.1 + x.2 = d := by
      simpa [Finset.mem_antidiagonal] using hx
    -- 用 Finsupp 的“≤ ↔ 存在加数”等价：x.2 ≤ d ↔ ∃ c, x.2 + c = d
    exact Finset.antidiagonal.snd_le hx
  -- 每一项都为 0：因为 e ≤ d 不成立，而任意项的第二坐标 b ≤ d，所以 e ≠ b
  refine Finset.sum_eq_zero ?all_zero
  intro x hx
  have hx2le : x.2 ≤ d := hb_le x hx
  have hne' : e ≠ x.2 := by
    intro heq
    -- 若 e = x.2，则由 x.2 ≤ d 得 e ≤ d，与假设矛盾
    exact hne (by simpa [heq] using hx2le)
  -- 该项 if 为假，等于 0
  simp [hne']

/-- 若 `initMonomial r ∈ ⟨ initMonomial ∘ b ⟩`，则存在 `i` 使 `degree (b i) ≤ degree r`。
-/
lemma leadingMonomial_mem_span_image_implies_exists_le
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    {r : MvPolynomial σ R} (hr : r ≠ 0) :
    m.leadingMonomial r ∈ Ideal.span (m.leadingMonomial '' (Set.range b)) →
    ∃ i, m.degree (b i) ≤ m.degree r := by
  classical
  -- 记 d = LM(r)
  set d := m.degree r with hd
  -- initMonomial r = monomial d 1
  have h_init : m.leadingMonomial r = monomial d (1 : R) := by
    simp [MonomialOrder.leadingMonomial, hr, hd]
  intro hx
  -- 反证：假设不存在 i 使 LM(b i) ≤ d
  by_contra hnone
  have hall : ∀ i, ¬ m.degree (b i) ≤ d := by
    intro i; exact not_exists.mp hnone i
  -- 定义理想 J：满足 “对任意 z，coeff d (z * y) = 0” 的元素组成的理想
  let J : Ideal (MvPolynomial σ R) :=
  { carrier   := {y | ∀ z, coeff d (z * y) = 0}
  , zero_mem' := by intro z; simp
  , add_mem'  := by
      intro x y hx hy z
      -- hx : ∀ z, coeff d (z * x) = 0
      -- hy : ∀ z, coeff d (z * y) = 0
      have hx0 := hx z
      have hy0 := hy z
      -- 目标：coeff d (z * (x + y)) = 0
      -- 展开乘法分配与“系数线性”，再把 hx0, hy0 代入即可。
      simp [mul_add, coeff_add, hx0, hy0]
  , smul_mem' := by
      -- 对 Ideal 而言 `smul_mem'` 就是左乘闭合：a * x ∈ J
      intro a x hx z
      -- 把左乘的 a 并到左边的 z 里
      simpa [mul_left_comm, mul_assoc] using hx (z * a) }
  -- 生成元都在 J ⇒ 整个 span 都包含在 J
  have hspan_to_J : Ideal.span (m.leadingMonomial '' Set.range b) ≤ J := by
    refine Ideal.span_le.mpr ?_
    intro y hy
    rcases hy with ⟨p, ⟨i, rfl⟩, rfl⟩
    -- 只需证 ∀ z, coeff d (z * initMonomial (b i)) = 0
    by_cases hbi0 : b i = 0
    · intro z
      simp [MonomialOrder.leadingMonomial, hbi0]
    · have hmono :
          m.leadingMonomial (b i) = monomial (m.degree (b i)) (1 : R) := by
        simp [MonomialOrder.leadingMonomial, hbi0]
      have hnotle : ¬ m.degree (b i) ≤ d := hall i
      intro z
      -- 用小引理把系数化为 0
      simpa [hmono, mul_comm, mul_left_comm, mul_assoc]
        using coeff_mul_monomial_one_of_not_le  (p := z)
              (d := d) (e := m.degree (b i)) hnotle
  -- 由 hx 得到 initMonomial r ∈ J
  have hmemJ : m.leadingMonomial r ∈ J := hspan_to_J hx
  -- 取 z = 1，得到系数为 0
  have : coeff d (1 * m.leadingMonomial r) = 0 := hmemJ 1
  -- 但 monomial d 1 在 d 处的系数是 1，矛盾
  have hone_eq_zero : (1 : R) = 0 := by
  -- 把系数等式化到 `monomial d 1` 上
    simpa [h_init] using this
  classical
  -- 按环是否平凡分支
  cases subsingleton_or_nontrivial R with
  | inl hsub =>
      -- 平凡环：MvPolynomial 也平凡，r = 0，与 hr 矛盾
      haveI := hsub
      exact hr (Subsingleton.elim _ _)
  | inr _ =>
      -- 非平凡环：直接用 one_ne_zero
      exact (one_ne_zero : (1 : R) ≠ 0) hone_eq_zero

/-- 若 `b` 是 Groebner 基，且 `f `属于 `b` 生成的理想，则 `f `模 `b `的余式为0。 -/
lemma remainder_eq_zero_of_mem_span
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hGB : m.IsGroebnerBasis (Set.range b) (Ideal.span (Set.range b)))
    {f : MvPolynomial σ R}
    (hf : f ∈ Ideal.span (Set.range b)) :
    m.reduceFamily b hb f = 0 := by
  classical
  -- 记 r 为算法给出的“标准余式”
  set r := m.reduceFamily b hb f with hr
  -- 1) 已证：`f - r ∈ ⟨range b⟩`
  have h_sub : f - r ∈ Ideal.span (Set.range b) :=
    reduceFamily_sub_mem_span_range (m := m) (b := b) (hb := hb) (f := f)
  -- 2) 由 `f ∈ I` 与 `f - r ∈ I` 推出 `r ∈ I`
  have hr_mem : r ∈ Ideal.span (Set.range b) := by
    -- r = f - (f - r)
    have : r = f - (f - r) := by ring
    -- 理想对减法封闭
    rw[this]
    exact (Submodule.sub_mem_iff_left (Ideal.span (Set.range b)) h_sub).mpr hf
  -- 3) Gröbner 基把“首单项式”拉进首项理想
  have hin :
      m.leadingMonomial r ∈ Ideal.span (m.leadingMonomial '' Set.range b) :=
    (IsGroebnerBasis.leadingMonomial_mem_span_image m (G := Set.range b) hGB hr_mem)
  -- 4) 若 r ≠ 0，由“单项式理想判定”得到 ∃i，LM(b i) ≤ LM(r)，从而 `r` 可头约化；与算法规格矛盾
  by_contra hr0
  have hr_ne : r ≠ 0 := by simp [hr0]  -- 假设 `m.reduceFamily b hb f ≠ 0`
  obtain ⟨i, hi⟩ :=
    (leadingMonomial_mem_span_image_implies_exists_le
        (m := m) (b := b) (r := r) hr_ne) hin
  -- 余式 `r` 是“完全约化”的：不可头部约化
  have hNotHR : ¬ HeadReducible m b r :=
    reduceFamily_not_headReducible (m := m) (b := b) (hb := hb) (f := f)
  -- 但上一步给出了“可头约化”的证据
  have hHR : HeadReducible m b r := ⟨hr_ne, ⟨i, hi⟩⟩
  exact (hNotHR hHR).elim


/-! 完全不可约：`r` 的任一单项式都不被任意 `LM(b i)` 整除（逐点 ≤）。 -/
def NoDivisible
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (r : MvPolynomial σ R) : Prop :=
  ∀ {d : σ →₀ ℕ}, d ∈ r.support → ∀ i, ¬ (m.degree (b i) ≤ d)


/-- `reduceFamily` 产出的余式满足完全不可约。 -/
lemma reduceFamily_noDivisible
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (f : MvPolynomial σ R) :
    NoDivisible m b (m.reduceFamily b hb f) := by
  classical
  change ∀ {d : σ →₀ ℕ},d ∈ (m.reduceFamily b hb f).support → ∀ i, ¬ (m.degree (b i) ≤ d)
  have wfμ := wf_μ (σ := σ) (R := R) (m := m)
  refine
    (wfμ.induction
      (C := fun g =>
        ∀ d : σ →₀ ℕ,
          d ∈ (m.reduceFamily b hb g).support → ∀ i, ¬ (m.degree (b i) ≤ d))
      f
      ?step)
  intro g IH
  by_cases hg0 : g = 0
  · -- g = 0 ⇒ 余式 = 0 ⇒ 支撑为空，性质平凡
    simp [hg0, reduceFamily_eq_zero]     -- 目标是 “∀ {d}, d ∈ ∅ → …”
  · by_cases h : HeadReducible m b g
    · -- 可头约：一跳到更小的参数，直接用 IH
      by_cases hdeg0 : m.degree g = 0
      · -- 已有：hg0 : g ≠ 0,  hdeg0 : m.degree g = 0，且我们知道 g 是“可头约”的（存在某 i 使 ≤）
        have hhead : ∃ i, m.degree (b i) ≤ m.degree g := by
          -- 若定义是 `g ≠ 0 ∧ ∃ i, ...` 则 `rcases h with ⟨_, ⟨i, hi⟩⟩; exact ⟨i, hi⟩`
          rcases h with ⟨_, ⟨i, hi⟩⟩; exact ⟨i, hi⟩
        -- 于是 reduceFamily 直接为 0
        have : m.reduceFamily b hb g = 0 :=
          reduceFamily_const_head_case_zero (m := m) (b := b) (hb := hb) hg0 hdeg0 hhead
        intro d a i
        simp_all only [MvPolynomial.mem_support_iff, ne_eq,
        nonpos_iff_eq_zero, MvPolynomial.support_zero,Finset.notMem_empty]
      -- 非常数情形：这时才用 degree_reduce_lt
      · have hdegpos : m.degree g ≠ 0 := by simpa using hdeg0
        rcases m.reduceFamily_eq_head_step (b := b) (hb := hb) (f := g) hg0 h with ⟨i, hi, hdef⟩
        have μlt :
            m.toSyn (m.degree (m.reduce (hb i) g))
              < m.toSyn (m.degree g) :=
          m.degree_reduce_lt (hb i) (by exact hi) hdegpos
        -- 把 IH 固定在更小的参数上，得到“局部版”的归纳结论
        have IH' :=
          IH (m.reduce (hb i) g) μlt
        -- 开始证明当前目标的“∀ d ∈ support …, ∀ j, …”
        intro d hd j
        simp_all only [MvPolynomial.mem_support_iff, ne_eq, not_false_eq_true]
    · -- 不可首项约化
      by_cases hdeg0 : m.degree g = 0
      · -- (常数) 分支：此时 `reduceFamily = g`；需要证明：`support g ⊆ {0}` 且 `∀ i, ¬ LM(b i) ≤ 0`
        have rdef : m.reduceFamily b hb g = g :=
          reduceFamily_eq_notHead_deg0 (m := m) (b := b) (hb := hb) hg0 h hdeg0
        intro d hd i hle
        have d_eq_zero : d = 0 := by
          -- `∀ c∈support g, c ≼[m] 0`
          have h_all := (m.degree_le_iff).1 (by simp [hdeg0] : m.degree g ≼[m] 0)
          have : d ≼[m] 0 := h_all d (by simpa [rdef] using hd)
          refine m.toSyn.injective ?_
          apply le_antisymm
          · simpa using this
          · -- `⊥ ≤ toSyn d`
            simp
        -- 再用“不可头约（在 deg=0 下）推出 ∀ i, ¬ LM(b i) ≤ 0” 来矛盾
        have not_le0 : ∀ j, ¬ (m.degree (b j) ≤ 0) := by
          intro j hj
          -- 若 `LM(b j) ≤ 0`，由于 `hg0 : g ≠ 0` 与 `hdeg0 : deg g = 0`，可推出 `HeadReducible m b g`，与 h 矛盾
          exact h ⟨hg0, ⟨j, by simpa [hdeg0] using hj⟩⟩
        -- 把 `d` 变成 0 完成矛盾
        have : ¬ (m.degree (b i) ≤ d) := by simpa [d_eq_zero] using not_le0 i
        exact this hle
      · -- 一般不可约（deg g ≠ 0）：r = initTerm g + tail
        have rdef :
          m.reduceFamily b hb g =
            m.leadingTerm g + m.reduceFamily b hb (m.subLTerm g) :=
          reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb) hg0 h hdeg0
        intro d hd i hle
        have hsplit :
            d = m.degree g ∨
            d ∈ (m.reduceFamily b hb (m.subLTerm g)).support := by
          classical
          -- 对 `d = degree g` 分类讨论
          by_cases hdeg : d = m.degree g
          · -- 左支：正好就是首项位置
            exact Or.inl hdeg
          · -- 右支：先把 hd 改写到 “首項+尾項” 的支撑上
            have hsum :
                d ∈ (m.leadingTerm g + m.reduceFamily b hb (m.subLTerm g)).support := by
              simpa [rdef] using hd
            -- 用“支撑剥离”把 membership 从 `initTerm g + tail` 推到 `tail`
            have htail :
                d ∈ (m.reduceFamily b hb (m.subLTerm g)).support :=by
                  have support_split_on_initTerm_add
                      (f p : MvPolynomial σ R) {d : σ →₀ ℕ} (hne : d ≠ m.degree f) :
                      d ∈ (m.leadingTerm f + p).support ↔ d ∈ p.support := by
                    -- 用“系数不为 0”刻画支撑，`initTerm f` 在该处系数为 0，化简为 p 的系数
                    have h0 : (m.leadingTerm f).coeff d = 0 :=
                      m.coeff_initTerm_of_ne_degree f hne
                    simp [MvPolynomial.mem_support_iff, coeff_add, h0]
                  exact
                    (support_split_on_initTerm_add g
                          (m.reduceFamily b hb (m.subLTerm g)) hdeg).mp hsum
            exact Or.inr htail
        cases hsplit with
        | inl hdeg_eq =>
            -- 首项：用“不可头约 ⇒ ∀j ¬ LM(b j) ≤ LM(g)”
            have hforall :
              ∀ j, ¬ (m.degree (b j) ≤ m.degree g) :=
              (not_headReducible_iff_forall (m := m) (b := b) (f := g) (by
              subst hdeg_eq
              simp_all only [MvPolynomial.mem_support_iff, ne_eq, coeff_add,
              not_false_eq_true])).1 h
            subst hdeg_eq
            simp_all only [MvPolynomial.mem_support_iff, ne_eq, coeff_add]
        | inr hd_tail =>
            -- 落在 tail：用 IH 作用在 `subLTerm g`
            have μlt : μ m (m.subLTerm g) < μ m g :=
              m.degree_sub_LTerm_lt (f := g) hdeg0
            have IH' := IH (m.subLTerm g) μlt
            -- 注意把 `hd` 改写为 tail 的支撑
            have : d ∈ (m.reduceFamily b hb (m.subLTerm g)).support := by
              simpa [rdef] using hd_tail
            exact IH (m.subLTerm g) μlt d hd_tail i hle

/-- 余式唯一性：
若 `b` 是 Gröbner 基，且 `f-r` 属于`b`生成的理想并且`r`**完全不可约**，
则 `r` 等于算法的余式 `reduceFamily b hb f`。 -/
theorem reduceFamily_unique
    (m : MonomialOrder σ) {b : ι → MvPolynomial σ R}
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hGB : m.IsGroebnerBasis (Set.range b) (Ideal.span (Set.range b)))
    (f r : MvPolynomial σ R)
    (h : f - r ∈ Ideal.span (Set.range b) ∧ NoDivisible m b r) :
    r = m.reduceFamily b hb f := by
  classical
  rcases h with ⟨h_congr, hNoDiv⟩
  -- 记 r₀ 为算法余式
  set r₀ := m.reduceFamily b hb f with hr₀
  have h_spec₁ : f - r₀ ∈ Ideal.span (Set.range b) :=
    reduceFamily_sub_mem_span_range (m := m) (b := b) (hb := hb) (f := f)
  have hNoDiv₀ : NoDivisible m b r₀ :=
    reduceFamily_noDivisible (m := m) (b := b) (hb := hb) (f := f)
  -- 考虑差 s
  set s := r - r₀ with hs
  -- 若 s = 0 则已证
  by_cases hs0 : s = 0
  · rw[hs0] at hs
    have hs:=sub_eq_zero.mp hs.symm
    exact hs
       -- `sub_eq` 只是你若自定义了 `f - g := f + (-g)` 时的化简别名
  · -- s ∈ ⟨range b⟩（两条同余相减）
    have hs_mem : s ∈ Ideal.span (Set.range b) := by
      -- s = (f - r₀) - (f - r)
      have hrepr : s = (f - r₀) - (f - r) := by
        simp [hs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        ring_nf
      -- ⟨range b⟩ 对减法封闭
      have hsub : (f - r₀) - (f - r) ∈ Ideal.span (Set.range b) :=
        Ideal.sub_mem _ h_spec₁ h_congr
      simpa [hrepr] using hsub
    -- Gröbner 基推出：in(s) ∈ ⟨in ∘ b⟩
    have hin : m.leadingMonomial s ∈ Ideal.span (m.leadingMonomial '' Set.range b) :=
      (IsGroebnerBasis.leadingMonomial_mem_span_image (m := m) (G := Set.range b) hGB hs_mem)
    -- 单项式理想刻画：∃ i, LM(b i) ≤ LM(s)（逐点 ≤）
    have hs_ne : s ≠ 0 := hs0
    obtain ⟨i, hi_div⟩ :=
      leadingMonomial_mem_span_image_implies_exists_le
      (m := m) (b := b) (r := s) (hr := by exact hs_ne) hin
    -- 记 d = LM(s)
    set d := m.degree s with hd
    have hd_in : d ∈ s.support :=
      degree_mem_support (m := m) (p := s) (by simpa [hs] using hs_ne)
    -- 在 d 处的系数：`coeff s d = coeff r d - coeff r₀ d` 非零
    have hcd_ne : s.coeff d ≠ 0 := by
      simpa [d] using (coeff_degree_ne_zero_iff (m := m) (f := s)).2 (by simpa [hs] using hs_ne)
    -- 至少一侧在 d 处系数非零 ⇒ d ∈ 支撑(r) ∪ 支撑(r₀)
    have hcase : r.coeff d ≠ 0 ∨ r₀.coeff d ≠ 0 := by
      by_contra hboth
      push_neg at hboth
      have : s.coeff d = 0 := by simp [hs, coeff_sub, hboth.left, hboth.right]
      exact hcd_ne this
    -- 两个对称分支：只要落在谁的支撑里，就与其“完全不可约”矛盾
    rcases hcase with hrd_ne | hr0d_ne
    · -- d ∈ support r
      have hdr : d ∈ r.support := by simpa [Finsupp.mem_support_iff] using hrd_ne
      -- hi_div : LM(b i) ≤ d（逐点 ≤），与 `r` 的完全不可约矛盾
      exact False.elim ((hNoDiv hdr i) hi_div)
    · -- d ∈ support r₀
      have hdr0 : d ∈ r₀.support := by simpa [Finsupp.mem_support_iff] using hr0d_ne
      exact False.elim ((hNoDiv₀ hdr0 i) hi_div)

/-- 在单项式序 `m` 下，`r` 是多项式 `f` 关于集合 `B` 的余式————满足
* 存在有限支撑的系数族 `g : B →₀ MvPolynomial σ R`，使得
  `f = Finsupp.linearCombination _ (fun b ↦ (b : MvPolynomial σ R)) g + r`，
  即 `f` 可以写成 “商 + 余式” 的分解；
* 同时 `r` 对 `B` 不可约。
-/
def IsRemainder
    (m : MonomialOrder σ)
    (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) : Prop :=
  (∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r
    ∧ ∀ (b : B), m.degree ((b : MvPolynomial σ R) * g b) ≼[m] m.degree f) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)

section Certificate

/-- 一步约化后的严格下降 or 常数归零 -/
lemma mu_lt_after_one_reduce_or_const_zero
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {g : MvPolynomial σ R}
    {i : ι} (hi : m.degree (b i) ≤ m.degree g) :
    m.toSyn (m.degree (m.reduce (hb i) g)) < m.toSyn (m.degree g)
    ∨ m.reduce (hb i) g = 0 := by
  classical
  by_cases hdeg0 : m.degree g = 0
  · -- 常数：一步归零
    right
    exact reduce_const_step_to_zero (m := m) (b := b) (hb := hb)
      (f := g) (hdeg0 := hdeg0) (i := i) hi
  · -- 非常数：严格下降
    left
    exact m.degree_reduce_lt (hb i) hi (by simpa using hdeg0)


/-- 用良基递归构造 `f - r` 的线性组合（`r = reduceFamily b hb f`），
并同时保证每项 `degree ((b' : _) * g b') ≤ degree f`。 -/
lemma reduceFamily_linearCertificate {m}
  (f : MvPolynomial σ R) (b : ι → MvPolynomial σ R)
   (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
  ∃ g : (Set.range b) →₀ MvPolynomial σ R,
    let r := m.reduceFamily b hb f
    f = Finsupp.linearCombination (MvPolynomial σ R)
    (fun s : (Set.range b) => (s : MvPolynomial σ R))
 g + r
    ∧ ∀ s : (Set.range b),
         m.degree ((s : MvPolynomial σ R) * g s) ≼[m] m.degree f := by
  sorry


end Certificate

/-! ## `reduceFamily` 产生的余式满足 `IsRemainder` -/
theorem IsRemainder_reduceFamily
  (m : MonomialOrder σ)
  {b : ι → MvPolynomial σ R}
  (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
  (f : MvPolynomial σ R) :
  m.IsRemainder f (Set.range b) (m.reduceFamily b hb f) := by
  classical
  obtain ⟨g, hEq, hbd⟩ :=
    m.reduceFamily_linearCertificate (b := b) (hb := hb) f
  refine And.intro ?h1 ?h2
  · refine ⟨g, ?_, ?_⟩
    · simpa using hEq
    · intro bB
      rcases bB with ⟨p, hp⟩
      exact hbd ⟨p, hp⟩
  · -- 第二部分：逐项完全不可约（对每个支撑指数 c 与任意 b∈B）
    intro c hc bB hb0 hbB
    have hND:m.NoDivisible b (m.reduceFamily b hb f) := m.reduceFamily_noDivisible b hb f
    simp only [NoDivisible, MvPolynomial.mem_support_iff, ne_eq] at hND
    have hcoeff :
        coeff c (m.reduceFamily b hb f) ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hc
    -- bB ∈ Set.range b，所以存在 i 使得 bB = b i
    rcases hb0 with ⟨i, rfl⟩
    -- 用 `NoDivisible` 的结论（已被你 `simp` 成“系数非零 → …”的形态）
    exact hND hcoeff i

/-- 从 `IsRemainder` 直接得到：`f - r ∈ Ideal.span (Set.range b)`。 -/
lemma IsRemainder.mem_span_range
    (m : MonomialOrder σ)
    {b : ι → MvPolynomial σ R}
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R} :
      f - m.reduceFamily b hb f ∈ Ideal.span (Set.range b) := by
  classical
  have h:=m.IsRemainder_reduceFamily hb f
  rcases h with ⟨⟨g, hfr, _degreeBound⟩, _noDiv⟩
  -- 把 `f = LC g + r` 改写成 `f - r = LC g`
  have hEq :
      f - m.reduceFamily b hb f
        = Finsupp.linearCombination (MvPolynomial σ R)
            (fun s : Set.range b => (s : MvPolynomial σ R)) g := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using congrArg (fun x => x - m.reduceFamily b hb f) hfr
  -- 证明右侧（线性组合）在 `span (range b)` 里
  have hLC_mem :
      Finsupp.linearCombination (MvPolynomial σ R)
        (fun s : Set.range b => (s : MvPolynomial σ R)) g
        ∈ Ideal.span (Set.range b) := by
    -- 展开成有限求和，再逐项落入理想
    simp only [linearCombination, coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
      smul_eq_mul]
    -- 目标现在是： `∑ s ∈ g.support, g s * (s : _) ∈ span (range b)`
    -- 用加法封闭性（对 Finset 的逐项成员性做 `sum_mem`）
    refine (Ideal.span (Set.range b)).sum_mem ?term_mem
    intro s hs
    have hs' : (s : MvPolynomial σ R) ∈ Ideal.span (Set.range b) :=
      Ideal.subset_span s.property
    -- 理想对环乘法封闭：`a * x ∈ I`
    exact Ideal.mul_mem_left _ _ hs'
  -- 回代等式
  rw[hEq]
  exact hLC_mem




/-**S多项式部分**-/
variable (m : MonomialOrder σ)


/-- S 多项式是两项在 `⟨range b⟩` 里的差，因此本身也在 `⟨range b⟩`。 -/
lemma sPolynomial_mem_span_range
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (f g : ι) :
    m.sPolynomial (b f) (b g) ∈ Ideal.span (Set.range b) := by
  have hf : b f ∈ Ideal.span (Set.range b) := by
    exact Ideal.subset_span ⟨f, rfl⟩
  have hg : b g ∈ Ideal.span (Set.range b) := by
    exact Ideal.subset_span ⟨g, rfl⟩
  simp [sPolynomial, hf, hg, Ideal.mul_mem_left, Ideal.sub_mem]



end Ring


section

variable {σ R : Type*} (m : MonomialOrder σ)
variable [CommSemiring R]

lemma leadingTerm_eq_C_mul_leadingMonomial
    {f : MvPolynomial σ R} (hf : f ≠ 0) :
    m.leadingTerm f = MvPolynomial.C (m.leadingCoeff f) * m.leadingMonomial f := by
    simp [leadingTerm, MonomialOrder.leadingMonomial, hf,
          MvPolynomial.C_mul_monomial]

end









section Field

variable {σ ι R : Type*}
variable [Field R]

variable (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)



lemma span_leadingTerm_image_eq_span_leadingMonomial_image_on_set
    (m : MonomialOrder σ) (S : Set (MvPolynomial σ R)) :
    Ideal.span (m.leadingTerm '' S) = Ideal.span (m.leadingMonomial '' S) := by
    classical
    -- 目标是证明两个理想相等：分别由 S 中多项式的 leadingTerm / leadingMonomial 生成
    apply le_antisymm
    · -- ⊆：证明 span(leadingTerm '' S) ≤ span(leadingMonomial '' S)
      -- 只需证明：leadingTerm '' S 的每个生成元都属于右侧理想（Ideal.span_le）
      refine Ideal.span_le.2 ?_
      intro t ht
      -- t 来自 leadingTerm '' S，因此存在 f∈S 使 t = leadingTerm f
      rcases ht with ⟨f, hfS, heq⟩
      subst heq
      by_cases hf : f = 0
      · -- 边界情况：f=0 时，leadingTerm/leadingMonomial 都化简为 0，结论直接成立
        simp [leadingTerm, leadingMonomial, hf]
      -- 先把 leadingMonomial f 作为右侧理想的生成元放进去
      have hin : m.leadingMonomial f ∈ Ideal.span (m.leadingMonomial '' S) :=
        Ideal.subset_span ⟨f, hfS, rfl⟩
      -- 用已知引理：leadingTerm f = C(leadingCoeff f) * leadingMonomial f
      have hlt := m.leadingTerm_eq_C_mul_leadingMonomial (hf:=hf)
      -- 因为右侧是理想，左乘任意多项式仍在其中，所以 leadingTerm f 也在右侧理想
      simpa [hlt] using Ideal.mul_mem_left _ _ hin
    · -- ⊇：证明 span(leadingMonomial '' S) ≤ span(leadingTerm '' S)
      -- 证明方式对称：把 leadingMonomial 写成（可逆系数）乘 leadingTerm
      refine Ideal.span_le.2 ?_
      intro t ht
      -- t 来自 leadingMonomial '' S，因此存在 f∈S 使 t = leadingMonomial f
      rcases ht with ⟨f, hfS, rfl⟩
      by_cases hf : f = 0
      · -- 边界情况：f=0 时直接化简
        simp [leadingTerm, leadingMonomial, hf]
      -- 下面要用到“首项系数可逆”：在域上，leadingCoeff f ≠ 0 ⇒ IsUnit
      have hlc_ne : m.leadingCoeff f ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf
      have hunit : IsUnit (m.leadingCoeff f) :=
        isUnit_iff_ne_zero.mpr hlc_ne
      -- 从 IsUnit 取出单位元 u（其值等于 leadingCoeff f）
      rcases hunit with ⟨u, hu⟩
      -- 将 leadingMonomial f 写成 C(u⁻¹) * leadingTerm f（对应“除以首项系数”）
      have hinit :
        m.leadingMonomial f = MvPolynomial.C (↑(u⁻¹) : R) * m.leadingTerm f := by
        -- 先用引理：leadingTerm f = C(lc) * leadingMonomial f
        have h1 := m.leadingTerm_eq_C_mul_leadingMonomial (hf:=hf)
        -- 再左乘 C(u⁻¹)，把等式整理成 leadingMonomial f = C(u⁻¹) * leadingTerm f
        rw[h1,←hu,←mul_assoc]
        simp_all only [Units.val_inv_eq_inv_val,ne_eq, leadingCoeff_eq_zero_iff,
        not_false_eq_true, leadingMonomial_of_ne ,
        C_mul_leadingCoeff_monomial_degree, monomial_eq_zero, one_ne_zero, right_eq_mul₀]
        refine map_mul_eq_one C ?_
        have h2: m.leadingCoeff f ≠ 0 := by
          simp_all only [ne_eq, leadingCoeff_eq_zero_iff, not_false_eq_true]
        exact inv_mul_cancel₀ h2
      -- leadingTerm f 本身是左侧理想的生成元，因此属于 span(leadingTerm '' S)
      have hlt : m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' S) :=
        Ideal.subset_span ⟨f, hfS, rfl⟩
      -- 理想对左乘封闭：C(u⁻¹) * leadingTerm f 也在左侧理想中
      simpa [hinit] using Ideal.mul_mem_left _ (MvPolynomial.C (↑(u⁻¹) : R)) hlt




end Field






end MonomialOrder
