import Mathlib

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.cdot false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.flexible false
open MvPolynomial Finsupp
open scoped BigOperators

namespace MonomialOrder

section
variable {σ R : Type*} [CommSemiring R]
variable (m : MonomialOrder σ)

/-- `leadingMonomial`：**系数规范为 1** 的首项（零多项式的首项约定为 `0`）。 -/
noncomputable def leadingMonomial (f : MvPolynomial σ R) : MvPolynomial σ R :=by
  classical
  exact if h : f = 0 then 0 else MvPolynomial.monomial (m.degree f) (1 : R)

@[simp] lemma leadingMonomial_zero :
    m.leadingMonomial (0 : MvPolynomial σ R) = 0 := by
  simp [leadingMonomial]

@[simp] lemma leadingMonomial_of_ne {f : MvPolynomial σ R} (hf : f ≠ 0) :
    m.leadingMonomial f = MvPolynomial.monomial (m.degree f) (1 : R) := by
  simp [leadingMonomial, hf]


/-! ### 首项理想（inₘ(I)） -/



/-- 用“系数 1 的首项”生成的首项理想。 -/
def initIdeal₁ (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  Ideal.span {t | ∃ f ∈ I, t = m.leadingMonomial f}

lemma initIdeal₁_def (I : Ideal (MvPolynomial σ R)) :
    m.initIdeal₁ I = Ideal.span {t | ∃ f ∈ I, t = m.leadingMonomial f} := rfl

lemma leadingMonomial_mem_initIdeal {I : Ideal (MvPolynomial σ R)} {f : MvPolynomial σ R}
    (hfI : f ∈ I) : m.leadingMonomial f ∈ m.initIdeal₁ I := by
  -- 直接由生成元属于 `Ideal.span` 推出
  refine Ideal.subset_span ?_
  refine ⟨f, hfI, rfl⟩

/-- `inₘ` 的单调性：若 `I ≤ J` 则 `inₘ(I) ≤ inₘ(J)`。 -/
lemma initIdeal₁_mono {I J : Ideal (MvPolynomial σ R)} (hIJ : I ≤ J) :
    m.initIdeal₁ I ≤ m.initIdeal₁ J := by
  -- 目标是：Ideal.span S ≤ Ideal.span T，只需证 S ⊆ Ideal.span T
  -- 用 span_le 的 ↔.mpr（也就是 .2）
  refine Ideal.span_le.2 ?_
  intro t ht
  rcases ht with ⟨f, hfI, rfl⟩
  -- 生成元在目标 span 内
  exact Ideal.subset_span ⟨f, hIJ hfI, rfl⟩

/-! ### Groebner 基的定义 -/

/-- 给定项序 `m`，一个集合 `G : Set (MvPolynomial σ R)` 称为 **Grobner 基**，
若由 `G` 生成的理想的首项理想，正好由 `G` 的首项生成。
`IsGroebnerBasis m G : Prop`。 -/
def IsGroebnerBasis (G : Set (MvPolynomial σ R)) : Prop :=
  m.initIdeal₁ (Ideal.span G) = Ideal.span (m.leadingMonomial '' G)



/-- `G` 是理想 `I` 的 Gröbner 基。 -/
def IsGroebnerBasis₂ (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingMonomial '' ↑I) = Ideal.span (m.leadingMonomial '' G)

lemma initIdeal₁_eq_span_leadingMonomial_image
    (I : Ideal (MvPolynomial σ R)) :
    m.initIdeal₁ I = Ideal.span (m.leadingMonomial '' (↑I : Set (MvPolynomial σ R))) := by
  classical
  -- 先把 span 的生成集合改写成 image 的形式
  have hset :
      {t : MvPolynomial σ R | ∃ f ∈ I, t = m.leadingMonomial f}
        = (m.leadingMonomial '' (↑I : Set (MvPolynomial σ R))) := by
    ext t
    constructor
    · rintro ⟨f, hfI, rfl⟩
      exact ⟨f, hfI, rfl⟩
    · rintro ⟨f, hfI, hft⟩
      exact ⟨f, hfI, hft.symm⟩
  -- 用 hset 改写 initIdeal₁
  simp [initIdeal₁, hset]


private lemma initSet_eq_image (G : Set (MvPolynomial σ R)):
  {t | ∃ f ∈ Ideal.span G, t = m.leadingMonomial f}
    = (m.leadingMonomial '' (↑(Ideal.span G))) := by
  ext t; constructor
  · intro ht; rcases ht with ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩
  · intro ht; rcases ht with ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩

lemma isGroebnerBasis_iff_for_span2 (G : Set (MvPolynomial σ R)) :
    m.IsGroebnerBasis G ↔ m.IsGroebnerBasis₂ G (Ideal.span G) := by
  classical
  constructor
  · -- `→`
    intro h
    refine And.intro ?subset ?eq
    · -- `G ⊆ span G`
      exact Ideal.subset_span
    · -- 由 `initIdeal₁ (span G)` 的定义改写成像集后与 `h` 相同
      simpa [IsGroebnerBasis,
             initIdeal₁, initSet_eq_image] using h
  · -- `←`
    rintro ⟨_, hEq⟩
    -- 只需把左侧再次改写回 `initIdeal₁ (span G)`
    simpa [IsGroebnerBasis,initIdeal₁, initSet_eq_image] using hEq


/-- `IsGroebnerBasis` 的充要定义就是上面那条等式，放个 `_iff` 方便改写。 -/
lemma isGroebnerBasis_iff (G : Set (MvPolynomial σ R)) :
    m.IsGroebnerBasis G ↔
      m.initIdeal₁ (Ideal.span G) = Ideal.span (m.leadingMonomial '' G) := Iff.rfl

/-- 基础性质：`G ⊆ H` 且 `G` 是 Groebner 基、且 `span G = span H`，则 `H` 也是 Groebner 基。 -/
lemma IsGroebnerBasis.of_span_eq
    {G H : Set (MvPolynomial σ R)}
    (hG : m.IsGroebnerBasis G)
    (hspan : Ideal.span G = Ideal.span H)
    (hIm : Ideal.span (m.leadingMonomial '' G) ≤ Ideal.span (m.leadingMonomial '' H))
    (hIm' : Ideal.span (m.leadingMonomial '' H) ≤ Ideal.span (m.leadingMonomial '' G)) :
    m.IsGroebnerBasis H := by
  -- 仅做等式替换与两侧包含
  have := hG
  dsimp [IsGroebnerBasis] at this ⊢
  simpa [hspan] using le_antisymm
    (calc
      m.initIdeal₁ (Ideal.span H)
          = m.initIdeal₁ (Ideal.span G) := by simp [hspan]
      _ = Ideal.span (m.leadingMonomial '' G) := this
      _ ≤ Ideal.span (m.leadingMonomial '' H) := hIm)
    (calc
      m.initIdeal₁ (Ideal.span H)
          = m.initIdeal₁ (Ideal.span G) := by simp [hspan]
      _ = Ideal.span (m.leadingMonomial '' G) := this
      _ ≥ Ideal.span (m.leadingMonomial '' H) := hIm')

/-- `G` 是 Groebner 基 ⇒ `inₘ(⟨G⟩)` 由 `G` 的首项生成；这是定义的拆解形式。 -/
lemma IsGroebnerBasis.initIdeal_span_eq
    {G : Set (MvPolynomial σ R)} (hG : m.IsGroebnerBasis G) :
    m.initIdeal₁ (Ideal.span G) = Ideal.span (m.leadingMonomial '' G) := hG

/-- Groebner 基的一个直接推论：对任意 `f ∈ ⟨G⟩`，其首项都落在由 `G` 首项生成的理想中。 -/
lemma IsGroebnerBasis.leadingMonomial_mem_span_image
    {G : Set (MvPolynomial σ R)} (hG : m.IsGroebnerBasis₂ G (Ideal.span G))
    {f : MvPolynomial σ R} (hf : f ∈ Ideal.span G) :
    m.leadingMonomial f ∈ Ideal.span (m.leadingMonomial '' G) := by
  have hx :
      m.leadingMonomial f ∈
        Ideal.span (m.leadingMonomial '' (↑(Ideal.span G) : Set (MvPolynomial σ R))) := by
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  -- 再用 GroebnerBasis₂ 的等式部分改写到目标
  simpa [hG.2] using hx


lemma leadingTerm_eq_C_mul_leadingMonomial
    {f : MvPolynomial σ R} (hf : f ≠ 0) :
    m.leadingTerm f = MvPolynomial.C (m.leadingCoeff f) * m.leadingMonomial f := by
    classical
    simp [leadingTerm, MonomialOrder.leadingMonomial, hf,
          MvPolynomial.C_mul_monomial]




end





section Ring

variable {σ ι R : Type*} [CommRing R]
/-! ### 头部可约性谓词 -/

/-- 首项可约性：存在某个 `i` 使 `LM(b i) ≤ LM(f)` 且 `LM(f) ≠ 0` -/
def HeadReducible
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (f : MvPolynomial σ R) : Prop :=
  f ≠ 0 ∧ ∃ i, m.degree (b i) ≤ m.degree f

/-! 完全不可约：`r` 的任一单项式都不被任意 `LM(b i)` 整除（逐点 ≤）。 -/
def NoDivisible
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (r : MvPolynomial σ R) : Prop :=
  ∀ {d : σ →₀ ℕ}, d ∈ r.support → ∀ i, ¬ (m.degree (b i) ≤ d)

/-- 从 `HeadReducible` 中挑一个可约的下标（非构造性选择） -/
noncomputable def chooseHead
(m : MonomialOrder σ)
(b : ι → MvPolynomial σ R)
(f : MvPolynomial σ R)
(h : HeadReducible m b f) :
{ i : ι // m.degree (b i) ≤ m.degree f } :=
⟨Classical.choose h.2, Classical.choose_spec h.2⟩

/-- 若可首项约化，则 `f ≠ 0`。 -/
lemma headReducible_ne_zero
(m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
{f : MvPolynomial σ R} (h : HeadReducible m b f) :
f ≠ 0 := h.1

/-- 在已知 `f ≠ 0` 的前提下，“不可首项约化” ⇔ 对所有 `i` 都有 `¬ LM(b i) ≤ LM(f)`。 -/
lemma not_headReducible_iff_forall
(m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
{f : MvPolynomial σ R} (hf0 : f ≠ 0) :
(¬ HeadReducible m b f) ↔ (∀ i, ¬ (m.degree (b i) ≤ m.degree f)) := by
  classical
  unfold HeadReducible
  constructor
  ·
    intro hnot i hi
    exact hnot ⟨hf0, ⟨i, hi⟩⟩
  ·
    intro hAll ⟨_, ⟨i, hi⟩⟩
    exact hAll i hi

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
    classical
    by_cases hf0 : f = 0
    · exact 0
    · by_cases h : HeadReducible m b f
      ·
        by_cases hdeg0 : m.degree f = 0
        · exact 0
        ·
          let i := (m.chooseHead b f h).val
          have hi := (m.chooseHead b f h).property
          exact reduceFamily m b hb (m.reduce (hb i) f)
      ·
        by_cases hdeg0 : m.degree f = 0
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


/-- 若 `m.degree f = 0` 且 **不可首项约化**，余式就是 `f` 本身。 -/
lemma reduceFamily_degree_zero_notHR
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R} (hf0 : f ≠ 0)
    (hdeg0 : m.degree f = 0) (hnot : ¬ HeadReducible m b f) :
    m.reduceFamily b hb f = f := by
  simp [reduceFamily, hf0, hdeg0, hnot]



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
  -- 直接按定义算 `reduce`；避免大 `simp`，逐步改写
  -- 注意：`monomial 0 c = C c`，并用 `map_mul` / `map_sub` 把“减去常数×常数”合并成一次 `C`。
  exact reduce_eq_zero_of_deg0_head m hdeg0 hbi0 (hb i)


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
  -- 从“存在性”中取一个下标 i
  rcases hhead with ⟨i, hi⟩
  -- 一步约化到 0
  have hred0 : m.reduce (hb i) f = 0 :=
    reduce_const_step_to_zero (m := m) (b := b) (hb := hb) (f := f) hdeg0 hi
  -- 现在展开一次 `reduceFamily`，选中“头可约”分支（不需要知道它内部具体选的是谁），
  -- 再用 hred0 把递归目标化成 `reduceFamily ... 0 = 0`。
  -- 这里用 `by_cases` 选择分支，避免大 `simp`。
  unfold MonomialOrder.reduceFamily
  -- 分支选取：`f ≠ 0`
  simp only [hf0, dite_false]
  -- 再分支：我们只需要“存在一个可头约的 i”，因此把“头可约”当成 `True` 来选中左分支即可；
  -- 具体选到哪个 i 并不重要，因为对每个满足条件的 i 约化结果都是 0。
  have : HeadReducible m b f := by
    -- 这里 `HeadReducible` 的具体定义有两种写法：
    -- 1) 若你用 `∃ i, degree (b i) ≤ degree f`（或再加上 `f ≠ 0`），则直接用上面的见证 `⟨i, hi⟩` 即可。
    -- 2) 若你用更强的旧版（还要求 `degree f ≠ 0`），则常数情形本身不可能 `HeadReducible`，此引理就不会被调用。
    exact ⟨hf0,i, hi⟩
  -- 选中“头可约”分支（`reduce` 后递归）
  simp [this, hdeg0]





/-- 若 `m.degree f = 0` 且 **不可首项约化**，余式就是 `f` 本身。 -/
lemma reduceFamily_eq_notHead_deg0
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R}
    (hf0 : f ≠ 0) (hnot : ¬ HeadReducible m b f) (hdeg0 : m.degree f = 0) :
    m.reduceFamily b hb f = f := by
  simp [reduceFamily, hf0, hnot, hdeg0]


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
  ·
    refine ⟨(m.chooseHead b f h).val, (m.chooseHead b f h).property, ?_⟩
    -- 只改写左边：展开一次定义，并用 hf0 / h 选中“可头约”分支
    conv_lhs =>
      unfold MonomialOrder.reduceFamily
      -- 这里的 `simp` 只用 `hf0` 和 `h` 做**分支选择**，
      -- 不会在子项里继续展开 `reduceFamily`（因为我们没把它放进 simp 集）
      simp [hf0, h,hdegpos]
  ·
    simp at hdegpos
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



def μ {σ R : Type*} [CommRing R] (m : MonomialOrder σ)
  (f : MvPolynomial σ R) : m.syn :=
  m.toSyn (m.degree f)

-- 良基
lemma wf_μ
  {σ R : Type*} [CommRing R]
  (m : MonomialOrder σ) :
  WellFounded (fun f g : MvPolynomial σ R => m.μ f < m.μ g) := by
  simpa [Function.onFun] using ((m.wf).wf).onFun



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
    · -- 这里再分 `deg f = 0` 与否
      by_cases hdeg0 : m.degree f = 0
      ·
        -- 此时 `reduceFamily ... f = 0`，而基中含单位常数 ⇒ 理想为 ⊤ ⇒ 结论平凡
        -- 构造：从 `h` 得到某 i 使 `degree (b i) ≤ 0`，进而 `degree (b i) = 0`
        rcases h with ⟨h, ⟨i, hi⟩⟩
        have h0 : m.degree (b i) = 0 :=
          le_antisymm (by simpa [hdeg0] using hi) (by simp)
        -- `b i = C (lc (b i))`，且 `lc (b i)` 为单位 ⇒ `1 ∈ ⟨range b⟩`
        have : (1 : MvPolynomial σ R) ∈ Ideal.span (Set.range b) := by
          -- `C (m.leadingCoeff (b i)) ∈ ⟨range b⟩` 且其为单位
          have hbmem : b i ∈ Ideal.span (Set.range b) := Ideal.subset_span ⟨i, rfl⟩
          have hbi : b i = C (m.leadingCoeff (b i)) :=
            (m.degree_eq_zero_iff (f := b i)).1 h0
          have hc_mem :
          (C (m.leadingCoeff (b i)) : MvPolynomial σ R) ∈ Ideal.span (Set.range b) := by
            rw[←hbi]
            exact hbmem
          have hunit :
            IsUnit (C (m.leadingCoeff (b i)) : MvPolynomial σ R) := by
          -- 关键是把 `_` 写全：R →+* MvPolynomial σ R
            simpa using IsUnit.map (C : R →+* MvPolynomial σ R) (hb i)
          have Itop : Ideal.span (Set.range b) = (⊤ : Ideal (MvPolynomial σ R)) :=
            by exact Ideal.eq_top_of_isUnit_mem (Ideal.span (Set.range b)) hc_mem hunit
          have one_mem : (1 : MvPolynomial σ R) ∈ Ideal.span (Set.range b) :=by
            simp [Itop]
          exact one_mem
          -- 单位在理想里 ⇒ 1 在理想里
        -- 因为 1 在理想里，所以任意 `f` 都在理想里
        have hfmem : f ∈ Ideal.span (Set.range b) := by
          simpa using Ideal.mul_mem_left (I := Ideal.span (Set.range b)) f this
        -- 目标 `f - 0 ∈ I`
        simp [reduceFamily,HeadReducible, hf0, hdeg0]
        simp_all only [not_false_eq_true, ne_eq, le_refl]
        split
        next h_1 => simp_all only [sub_zero]
        next h_1 => simp_all only [not_exists, sub_self, zero_mem]
      · -- `deg f ≠ 0`：用一步 `reduce` + 归纳假设
        rcases m.reduceFamily_eq_head_step (b := b) (hb := hb)
            hf0 h with ⟨i, hi, hdef⟩
        have μlt : m.toSyn (m.degree (m.reduce (hb i) f)) < m.toSyn (m.degree f) :=
          m.degree_reduce_lt (hb i) hi hdeg0
        have IH' := IH (m.reduce (hb i) f) μlt
        simpa [hdef, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using Ideal.add_mem _ (sub_reduce_mem_span_range m b hb i f) IH'
    · -- 不可头约
      by_cases hdeg0 : m.degree f = 0
      · simp [reduceFamily_eq_notHead_deg0 (m := m) (b := b) (hb := hb) hf0 h hdeg0]
      ·
        have μlt : μ m (m.subLTerm f) < μ m f :=
          m.degree_sub_LTerm_lt (f := f) hdeg0
        have IH' := IH (m.subLTerm f) μlt
        /-simp at IH'
        simp [reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb) hf0 h hdeg0,←sub_sub,initTerm]
        have h1:f - (monomial (m.degree f)) (m.leadingCoeff f)=m.subLTerm f:=rfl
        rw[h1]
        exact IH'-/
        -- 用 subLTerm = f - initTerm 改造
        simpa [reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb) hf0 h hdeg0,
               MonomialOrder.subLTerm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using IH'


lemma degree_initTerm
    (m : MonomialOrder σ) (f : MvPolynomial σ R) :
    m.degree (m.leadingTerm f) = m.degree f := by
  classical
  by_cases hf : f = 0
  · -- 零多项式：两边度都为 0
    simp [MonomialOrder.leadingTerm, hf, m.degree_zero]
  -- 非零情形：设 a = degree f, r = leadingCoeff f
  set a := m.degree f with ha
  set r := m.leadingCoeff f
  have hr : r ≠ 0 := by
    -- `leadingCoeff f ≠ 0` ↔ `f ≠ 0`
    intro p
    have h1:=leadingCoeff_eq_zero_iff.mp p
    subst h1
    simp_all only [not_true_eq_false]
  -- 先证：μ(deg (initTerm f)) ≤ μ a
  have hle : m.toSyn (m.degree (m.leadingTerm f)) ≤ m.toSyn a := by
    -- 用 `degree_le_iff`，只需对支撑中的每个指数组 b 证 `μ b ≤ μ a`
    rw [degree_le_iff]
    intro b hb
    -- b 在 `initTerm f` 的支撑上 ⇒ 其系数 ≠ 0
    have hbne : (m.leadingTerm f).coeff b ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using hb
    -- 计算系数：单项式的系数公式
    have hba : b = a := by
      -- 若 b ≠ a，则系数应为 0，矛盾
      by_contra hne
      have : (m.leadingTerm f).coeff b = 0 := by
        simp [MonomialOrder.leadingTerm, coeff_monomial]
        intro p
        rw [←ha] at p
        exact (hne p.symm).elim
      exact hbne this
    simp [hba]
  -- 再证：μ a ≤ μ(deg (initTerm f))，用 `le_degree` 和 `a ∈ support`
  have hge : m.toSyn a ≤ m.toSyn (m.degree (m.leadingTerm f)) := by
    -- a 在支撑上，因为该处系数就是 r 且 r ≠ 0
    have : (m.leadingTerm f).coeff a ≠ 0 := by
      simpa [MonomialOrder.leadingTerm, a, r, coeff_monomial] using hr
    have : a ∈ (m.leadingTerm f).support := by
      simpa [Finsupp.mem_support_iff] using this
    simpa using (m.le_degree this)
  -- 两边夹出 μ-相等，再用 `toSyn` 单射性还原成度的相等
  have : m.toSyn (m.degree (m.leadingTerm f)) = m.toSyn a := le_antisymm hle hge
  simp [ha]



/-- 辅助：首项的 μ-度等于原多项式的 μ-度。 -/
lemma mu_degree_initTerm
    (m : MonomialOrder σ) (f : MvPolynomial σ R) :
    m.toSyn (m.degree (m.leadingTerm f)) = m.toSyn (m.degree f) := by
  rw[degree_initTerm]


-- 最高项 + 更小尾项不改变最高项
lemma mu_degree_initTerm_add_of_lt
    (m : MonomialOrder σ) {f g : MvPolynomial σ R}
    (hlt : m.toSyn (m.degree g) < m.toSyn (m.degree f)) :
    m.toSyn (m.degree (m.leadingTerm f + g)) = m.toSyn (m.degree f) := by
  classical
  -- 把 `<` 改写到 `initTerm f` 上
  have hlt' :
      m.degree g ≺[m] m.degree (m.leadingTerm f) := by
    -- `≺[m]` 就是 μ-序上的 `<`；用上一条把右侧换成 `μ(deg f)`
    simpa [m.mu_degree_initTerm f] using hlt
  -- “小 + 大 = 大” 用在 `g + initTerm f`
  have hdeg :
      m.degree (g + m.leadingTerm f) = m.degree (m.leadingTerm f) :=
    m.degree_add_eq_right_of_lt hlt'
  -- 交换加数，映到 μ 上
  have hμ :
      m.toSyn (m.degree (m.leadingTerm f + g))
        = m.toSyn (m.degree (m.leadingTerm f)) := by
    simpa [add_comm] using congrArg m.toSyn hdeg
  -- 再把 `μ(deg initTerm f)` 换回 `μ(deg f)`
  simpa [m.mu_degree_initTerm f] using hμ


lemma mu_reduceFamily_lt_of_lt
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {g F : MvPolynomial σ R}
    (hlt : m.toSyn (m.degree g) < m.toSyn (m.degree F)) :
    m.toSyn (m.degree (m.reduceFamily b hb g)) < m.toSyn (m.degree F) := by
  classical
  have wfμ := wf_μ (σ := σ) (R := R) (m := m)
  refine
    (wfμ.induction
      (C := fun g =>
        ∀ F : MvPolynomial σ R,
          m.toSyn (m.degree g) < m.toSyn (m.degree F) →
          m.toSyn (m.degree (m.reduceFamily b hb g)) < m.toSyn (m.degree F))
      g
      ?step) F hlt
  -- 归纳步：先引入 `g IH F' hlt'`
  intro g2 IH F' hlt'
  by_cases hg0 : g2 = 0
  · simpa [hg0, reduceFamily_eq_zero] using hlt'
  · by_cases h : HeadReducible m b g2
    · -- `deg g2 ≠ 0` 从 `HeadReducible` 里取出
      · by_cases hdeg0 : m.degree g2 = 0
        -- (A) deg g2 = 0：一步 reduce 就变成 0
        · rcases h with ⟨hg2_ne, ⟨i, hi⟩⟩
          -- 从 hi : degree (b i) ≤ degree g2 = 0 得到 degree (b i) = 0
          have hbi0 : m.degree (b i) = 0 := by
            have : m.degree (b i) ≤ 0 := by simpa [hdeg0] using hi
            exact le_antisymm this (by simp)
          -- 一步约化为 0
          have hred0 : m.reduce (hb i) g2 = 0 :=
            reduce_eq_zero_of_deg0_head (m := m) (f := g2) (h := b i) hdeg0 hbi0 (hb i)
          -- 用“单步等式”把 reduceFamily 也化为 0
          rcases m.reduceFamily_eq_head_step (b := b) (hb := hb) (f := g2) hg2_ne ⟨hg2_ne, ⟨i, hi⟩⟩ with
            ⟨i', hi', hdef⟩
          have : m.reduceFamily b hb g2 = 0 := by
            -- 对 choose 出来的 i' 做同样的度数=0 推理
            have hbi0' : m.degree (b i') = 0 := by
              have : m.degree (b i') ≤ 0 := by simpa [hdeg0] using hi'
              exact le_antisymm this (by simp)
            have hred0' : m.reduce (hb i') g2 = 0 :=
              reduce_eq_zero_of_deg0_head (m := m) (f := g2) (h := b i') hdeg0 hbi0' (hb i')
            simp [hdef, hred0', reduceFamily_eq_zero]
          -- 结论：μ(deg 0) < μ(deg F')，而 hlt' 正好是 0 < μ(deg F')（因为 deg g2 = 0）
          simpa [this, m.degree_zero,hdeg0] using hlt'
        -- (B) deg g2 ≠ 0：回到你原来的“严降 + 归纳”
        · rcases m.reduceFamily_eq_head_step (b := b) (hb := hb) (f := g2) hg0 h with
            ⟨i, hi, hdef⟩
          have μlt :
              m.toSyn (m.degree (m.reduce (hb i) g2))
                < m.toSyn (m.degree g2) :=
            m.degree_reduce_lt (hb i) hi (by exact hdeg0)   -- 这里用到 deg g2 ≠ 0
          have IH' := IH (m.reduce (hb i) g2) μlt F' (lt_trans μlt hlt')
          simpa [hdef] using IH'
    · by_cases hdeg0 : m.degree g2 = 0
      · simpa [reduceFamily_eq_notHead_deg0 (m := m) (b := b) (hb := hb) hg0 h hdeg0] using hlt'
      ·
        have μlt_sub :
            m.toSyn (m.degree (m.subLTerm g2)) < m.toSyn (m.degree g2) :=
          m.degree_sub_LTerm_lt (f := g2) hdeg0
        have μlt_tail :
            m.toSyn (m.degree (m.reduceFamily b hb (m.subLTerm g2))) <
            m.toSyn (m.degree g2) :=
          (IH (m.subLTerm g2) μlt_sub) g2 μlt_sub
        have mu_eq :
            m.toSyn (m.degree (m.reduceFamily b hb g2)) =
            m.toSyn (m.degree g2) := by
          have rdef :
            m.reduceFamily b hb g2 =
              m.leadingTerm g2 + m.reduceFamily b hb (m.subLTerm g2) :=
            reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb) hg0 h hdeg0
          simpa [rdef] using
            mu_degree_initTerm_add_of_lt (m := m) (f := g2)
              (g := m.reduceFamily b hb (m.subLTerm g2)) μlt_tail
        simpa [mu_eq] using hlt'



/-- `reduceFamily` 的结果对 `b` 不再可首项约化。 -/
lemma reduceFamily_not_headReducible
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (f : MvPolynomial σ R) :
    ¬ HeadReducible m b (m.reduceFamily b hb f) :=
by
  classical
  have wfμ := wf_μ (σ := σ) (R := R) (m := m)
  refine
    (wfμ.induction
      (C := fun f => ¬ HeadReducible m b (m.reduceFamily b hb f))
      f
      ?step)
  intro f IH
  by_cases hf0 : f = 0
  · simp [hf0, HeadReducible]
  · by_cases h : HeadReducible m b f
    ·
      by_cases hdeg0 : m.degree f = 0
      ·
        rcases m.reduceFamily_eq_head_step (b := b) (hb := hb) hf0 h with ⟨i, hi, hdef⟩
        -- deg(b i) = 0
        have hbi0 : m.degree (b i) = 0 := by
          have : m.degree (b i) ≤ 0 := by simpa [hdeg0] using hi
          exact le_antisymm this (by simp)
        -- 常数对常数，且 lc(b i) 为单位 ⇒ 一步 reduce 直接为 0
        have hred0 : m.reduce (hb i) f = 0 :=
          reduce_eq_zero_of_deg0_head (m := m) hdeg0 hbi0 (hb i)
        -- 用定义性等式 + reduceFamily(0)=0
        have hRF0 : m.reduceFamily b hb f = 0 := by
          simp [hdef, hred0, reduceFamily_eq_zero]
        -- 0 不可头约（由 HeadReducible 的定义）
        simp [hRF0, HeadReducible]
      ·
        rcases m.reduceFamily_eq_head_step (b := b) (hb := hb) hf0 h with ⟨i, hi, hdef⟩
        have μlt : μ m (m.reduce (hb i) f) < μ m f :=
          m.degree_reduce_lt (hb i) hi hdeg0
        have IH' := IH (m.reduce (hb i) f) μlt
        simpa [hdef] using IH'
    · by_cases hdeg0 : m.degree f = 0
      · have rdef :
        m.reduceFamily b hb f = f :=
          reduceFamily_eq_notHead_deg0 (m := m) (b := b) (hb := hb) hf0 h hdeg0
        simpa [rdef] using h
      ·
        set r := m.reduceFamily b hb f with hr
        intro hex
        rcases hex with ⟨_hdeg_r_ne0, i, hi⟩
        -- 得到 μ 版严格小于：
        have h_tail_mu_lt :
          m.toSyn (m.degree (m.reduceFamily b hb (m.subLTerm f))) <
          m.toSyn (m.degree f) :=
          mu_reduceFamily_lt_of_lt (m := m) (b := b) (hb := hb)
            (m.degree_sub_LTerm_lt (f := f) hdeg0)
        -- 得到 μ 上的“相等”（先在 reduceFamily 上，再转成 r 上）
        have mu_eq₀ :
          m.toSyn (m.degree (m.reduceFamily b hb f)) =
          m.toSyn (m.degree f) := by
          have rdef :
            m.reduceFamily b hb f =
              m.leadingTerm f + m.reduceFamily b hb (m.subLTerm f) :=
            reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb) hf0 h hdeg0
          simpa [rdef] using
            mu_degree_initTerm_add_of_lt (m := m) h_tail_mu_lt
        have mu_eq :
          m.toSyn (m.degree r) = m.toSyn (m.degree f) := by
          simpa [hr] using mu_eq₀
        -- 用 toSyn 的单射性拉回 raw degree 的相等，并同样先改写到 r 上
        have deg_r_eq : m.degree r = m.degree f :=
          m.toSyn.injective mu_eq
        -- 现在就能把 hi : ≤ m.degree r 改写成 ≤ m.degree f
        have h_le : m.degree (b i) ≤ m.degree f := by
          simpa [deg_r_eq] using hi
        -- 把 `¬ HeadReducible m b f`（且 `degree f ≠ 0`）改写成“对所有 i 都不是 ≤ degree f”
        have hnotf :
            ∀ i, ¬ (m.degree (b i) ≤ m.degree f) := by
          intro j hj
          exact h ⟨by exact hf0, j, hj⟩
        -- 矛盾
        exact (hnotf i) h_le

/-- 在 `d ≠ degree f` 时，`initTerm f` 在指数 `d` 处的系数为 `0`。 -/
lemma coeff_initTerm_of_ne_degree(m : MonomialOrder σ)
    (f : MvPolynomial σ R) {d : σ →₀ ℕ} (hne : d ≠ m.degree f) :
    (m.leadingTerm f).coeff d = 0 := by
  classical
  -- `initTerm f = monomial (degree f) (leadingCoeff f)`
  -- 用 `coeff_monomial` 配合 `hne` 直接得到 0
  simp [MonomialOrder.leadingTerm, coeff_monomial]
  intro p
  subst p
  simp_all only [ne_eq, not_true_eq_false]



/-- `reduceFamily` 产出的余式满足完全不可约。 -/
lemma reduceFamily_noDivisible
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (f : MvPolynomial σ R) :
    NoDivisible m b (m.reduceFamily b hb f) := by
  classical
  -- 先把目标改写成展开形，避免 `refine` 对隐式参数的误解
  change ∀ {d : σ →₀ ℕ},d ∈ (m.reduceFamily b hb f).support → ∀ i, ¬ (m.degree (b i) ≤ d)
  -- 在 μ 上做良基归纳：C g := “对 reduceFamily g 的每个支撑指数都不可被任何 LM(b i) 覆盖”
  have wfμ := wf_μ (σ := σ) (R := R) (m := m)
  refine
    (wfμ.induction
      (C := fun g =>
        ∀ d : σ →₀ ℕ,
          d ∈ (m.reduceFamily b hb g).support → ∀ i, ¬ (m.degree (b i) ≤ d))
      f
      ?step)
  -- 归纳步
  intro g IH
  by_cases hg0 : g = 0
  · -- g = 0 ⇒ 余式 = 0 ⇒ 支撑为空，性质平凡
    simp [hg0, reduceFamily_eq_zero]     -- 目标是 “∀ {d}, d ∈ ∅ → …”
  · by_cases h : HeadReducible m b g
    · -- 可头约：一跳到更小的参数，直接用 IH
      by_cases hdeg0 : m.degree g = 0
      ·
        -- 已有：hg0 : g ≠ 0,  hdeg0 : m.degree g = 0，且我们知道 g 是“可头约”的（存在某 i 使 ≤）
        have hhead : ∃ i, m.degree (b i) ≤ m.degree g := by
          -- 若定义是 `g ≠ 0 ∧ ∃ i, ...` 则 `rcases h with ⟨_, ⟨i, hi⟩⟩; exact ⟨i, hi⟩`
          rcases h with ⟨_, ⟨i, hi⟩⟩; exact ⟨i, hi⟩
        -- 于是 reduceFamily 直接为 0
        have : m.reduceFamily b hb g = 0 :=
          reduceFamily_const_head_case_zero (m := m) (b := b) (hb := hb) hg0 hdeg0 hhead
        intro d a i
        simp_all only [MvPolynomial.mem_support_iff, ne_eq, nonpos_iff_eq_zero, MvPolynomial.support_zero,
          Finset.notMem_empty]
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
        -- 用 hdef 把 support 改写到 IH' 所在的那个 reduceFamily 上
        -- 套用 IH'
        simp_all only [MvPolynomial.mem_support_iff, ne_eq, not_false_eq_true]
    · -- 不可头约
      by_cases hdeg0 : m.degree g = 0
      · -- (常数) 分支：此时 `reduceFamily = g`；需要证明：`support g ⊆ {0}` 且 `∀ i, ¬ LM(b i) ≤ 0`
        -- 把目标改写到 `g`
        have rdef : m.reduceFamily b hb g = g :=
          reduceFamily_eq_notHead_deg0 (m := m) (b := b) (hb := hb) hg0 h hdeg0
        -- 取任意支撑单项 d 与任意 i
        intro d hd i hle
        -- 先证 d = 0：由 `deg g = 0` 用 `degree_le_iff` 压到 0，再用“≤ ⊥ ⇒ 等于 ⊥”
        have d_eq_zero : d = 0 := by
          -- `∀ c∈support g, c ≼[m] 0`
          have h_all := (m.degree_le_iff).1 (by simp [hdeg0] : m.degree g ≼[m] 0)
          have : d ≼[m] 0 := h_all d (by simpa [rdef] using hd)
          -- 小引理：`d ≼[m] 0` ⇒ `d = 0`
          --（若你文件里已有类似 `eq_of_le_bot`/`bot_eq_zero` 引理，直接用即可）
          -- 这里给一个常用写法：
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
        -- 把支撑分成“首项”或“落在 tail 的余式”
        -- 你可以用你已有的支撑分裂引理；若没有，用 `mem_support_iff` + 系数计算做一个：
        -- 我们直接假设你有 `support_split_on_initTerm_add`：
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
              simp_all only [MvPolynomial.mem_support_iff, ne_eq, coeff_add, not_false_eq_true])).1 h
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










/-**S多项式部分**-/
variable (m : MonomialOrder σ)

/-- S 多项式是两项在 `⟨range b⟩` 里的差，因此本身也在 `⟨range b⟩`。 -/
lemma sPolynomial_mem_span_range
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (f g : ι) :
    m.sPolynomial (b f) (b g) ∈ Ideal.span (Set.range b) := by
  classical
  -- 先把 b f, b g 放进 span(range b)
  have hf : b f ∈ Ideal.span (Set.range b) := by
    exact Ideal.subset_span ⟨f, rfl⟩
  have hg : b g ∈ Ideal.span (Set.range b) := by
    exact Ideal.subset_span ⟨g, rfl⟩
  simp [MonomialOrder.sPolynomial, hf, hg, Ideal.mul_mem_left, Ideal.sub_mem]


/-! ### 辅助：乘以 `monomial e 1` 时的系数为零判定 -/
/-- 若 `e ≤ d` 不成立，则对任意 `p`，`coeff d (p * monomial e 1) = 0`。 -/
lemma coeff_mul_monomial_one_of_not_le
{d e : σ →₀ ℕ} (p : MvPolynomial σ R) (hne : ¬ e ≤ d) :
coeff d (p * monomial e (1 : R)) = 0 := by
  classical
  -- 展开卷积求和
  simp [coeff_mul, coeff_monomial]  -- 目标变成对 antidiagonal 的求和
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


/-! ### 通用“1=0 / 0=1 ⇒ False（或在平凡环分支反证）”小引理 -/
-- 当目标需要 `False`，但手里只有 `1 = 0` 时的统一收尾。
lemma false_of_one_eq_zero_or_subsingleton
    {r : MvPolynomial σ R} (hr : r ≠ 0) (h : (1 : R) = 0) : False := by
  classical
  -- 按环是否平凡分支
  cases subsingleton_or_nontrivial R with
  | inl hsub =>
      -- 平凡环：MvPolynomial 也平凡，r = 0，与 hr 矛盾
      haveI := hsub
      exact hr (Subsingleton.elim _ _)
  | inr _ =>
      -- 非平凡环：直接用 one_ne_zero
      exact (one_ne_zero : (1 : R) ≠ 0) h



/-! ### 关键：单项式理想的“成员 ⇒ 存在”方向 -/

/-- 若 `initMonomial r ∈ ⟨ initMonomial ∘ b ⟩`，则存在 `i` 使 `degree (b i) ≤ degree r`。-/
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
  exact false_of_one_eq_zero_or_subsingleton hr hone_eq_zero





/-! ### 反向（需要生成元首系数是单位） -/

/-- 若存在 `i` 使 `degree (b i) ≤ degree r`，并且 `lc(b i)` 皆为单位，
则 `initMonomial r ∈ ⟨ initMonomial ∘ b ⟩`。 -/
lemma leadingMonomial_mem_span_image_of_exists_le_of_units
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {r : MvPolynomial σ R} (hr : r ≠ 0) :
    (∃ i, m.degree (b i) ≤ m.degree r) →
    m.leadingMonomial r ∈ Ideal.span (m.leadingMonomial '' (Set.range b)) := by
  intro h
  rcases h with ⟨i, hi⟩
  -- b i ≠ 0 (lc 是单位 ⇒ lc ≠ 0 ⇒ 多项式 ≠ 0)
  have hbi0 : b i ≠ 0 := by
    intro h0
    have := hb i
    simp only [h0, leadingCoeff_zero, isUnit_zero_iff] at this
    exact false_of_one_eq_zero_or_subsingleton hr (id (Eq.symm this))
  -- 把 initMonomial 都写成 monomial _ 1
  have r_mono  : m.leadingMonomial r   = monomial (m.degree r) (1 : R) := by
    simp [leadingMonomial, hr]
  have bi_mono : m.leadingMonomial (b i) = monomial (m.degree (b i)) (1 : R) := by
    simp [leadingMonomial, hbi0]
  -- 拼成目标单项式
  have hmul :
      monomial (m.degree r - m.degree (b i)) (1 : R)
        * m.leadingMonomial (b i) = m.leadingMonomial r := by
    have : monomial (m.degree r - m.degree (b i)) (1 : R)
            * monomial (m.degree (b i)) (1 : R)
          = monomial (m.degree r) (1 : R) := by
      -- 这里用到 (d - e) + e = d（在 finsupp 上对应 tsub_add_cancel_of_le）
      simp [tsub_add_cancel_of_le hi]
    simpa [r_mono, bi_mono, mul_comm, mul_left_comm, mul_assoc] using this
  -- 生成元在 span 里
  have hin : m.leadingMonomial (b i) ∈ Ideal.span (m.leadingMonomial '' (Set.range b)) :=
    Ideal.subset_span ⟨b i, ⟨i, rfl⟩, rfl⟩
  -- 理想对左乘闭合
  have hmem :
      monomial (m.degree r - m.degree (b i)) (1 : R) * m.leadingMonomial (b i)
      ∈ Ideal.span (m.leadingMonomial '' (Set.range b)) :=
    Ideal.mul_mem_left (I := Ideal.span (m.leadingMonomial '' (Set.range b)))
      _ hin
  simpa [hmul] using hmem



/-! ### 命题2.3.14 -/
lemma leadingMonomial_mem_span_image_iff_exists_le
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {r : MvPolynomial σ R} (hr : r ≠ 0) :
    m.leadingMonomial r ∈ Ideal.span (m.leadingMonomial '' (Set.range b))
      ↔ ∃ i, m.degree (b i) ≤ m.degree r := by
  constructor
  · exact leadingMonomial_mem_span_image_implies_exists_le (m := m) (b := b) hr
  · exact leadingMonomial_mem_span_image_of_exists_le_of_units (m := m) (b := b) (hb := hb) hr





/-- 余式唯一性：
若 `b` 是 Gröbner 基，且 `f-r` 属于`b`生成的理想并且`r`**完全不可约**，
则 `r` 等于算法的余式 `reduceFamily b hb f`。 -/
theorem reduceFamily_unique
    (m : MonomialOrder σ) {b : ι → MvPolynomial σ R}
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hGB : m.IsGroebnerBasis₂ (Set.range b) (Ideal.span (Set.range b)))
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
  ·
    rw[hs0] at hs
    have hs:=sub_eq_zero.mp hs.symm
    exact hs
       -- `sub_eq` 只是你若自定义了 `f - g := f + (-g)` 时的化简别名
  ·
    -- s ∈ ⟨range b⟩（两条同余相减）
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
      leadingMonomial_mem_span_image_implies_exists_le (m := m) (b := b) (r := s) (hr := by exact hs_ne) hin
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


/--
**唯一余式（一般形式）**：若 `G = range b` 是 Gröbner 基，且 `r₁, r₂` 满足：
1) `f - rᵢ ∈ ⟨range b⟩`；
2) `NoDivisible m b rᵢ`；
则 `r₁ = r₂`。-/
lemma unique_remainder_of_GB
    (m : MonomialOrder σ) {b : ι → MvPolynomial σ R}(hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hGB : m.IsGroebnerBasis₂ (Set.range b) (Ideal.span (Set.range b)))
    {f r₁ r₂ : MvPolynomial σ R}
    (h₁ : f - r₁ ∈ Ideal.span (Set.range b) ∧ NoDivisible m b r₁)
    (h₂ : f - r₂ ∈ Ideal.span (Set.range b) ∧ NoDivisible m b r₂) :
    r₁ = r₂ := by
  classical
  -- 先把两边都“压”到算法余式
  have h1 : r₁ = m.reduceFamily b hb f :=
    reduceFamily_unique (m := m) (b := b) hb hGB f r₁ h₁
  have h2 : r₂ = m.reduceFamily b hb f :=
    reduceFamily_unique (m := m) (b := b) hb hGB f r₂ h₂
  -- 等式传递得到 r₁ = r₂
  exact h1.trans h2.symm


/-- `reduceFamily` 计算得到的 r₀ 的确满足“余式规格”。 -/
lemma reduceFamily_isRemainder
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (f : MvPolynomial σ R) :
  (f - (m.reduceFamily b hb f) ∈ Ideal.span (Set.range b)) ∧ NoDivisible m b (m.reduceFamily b hb f) :=
by
  refine ⟨?mem, ?nf⟩
  · -- 与 `⟨range b⟩` 同余
    exact reduceFamily_sub_mem_span_range (m := m) (b := b) (hb := hb) (f := f)
  · -- 不可头约化
    (expose_names; exact @reduceFamily_noDivisible σ ι R inst m b hb f)


/-- 若 `b` 是 Groebner 基，则“f 的余式存在唯一”。 -/
theorem remainder_exists_unique_of_GB
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hGB : m.IsGroebnerBasis₂ (Set.range b) (Ideal.span (Set.range b)))
    (f : MvPolynomial σ R) :
  ∃! r, (f - r ∈ Ideal.span (Set.range b)) ∧ NoDivisible m b r :=
by
  classical
  -- 取算法余式 r₀ 作见证
  set r₀ := m.reduceFamily b hb f with hr₀
  refine ⟨r₀, ?hR0, ?uniq⟩
  · -- r₀ 满足规格
    simpa [hr₀] using reduceFamily_isRemainder (m := m) (b := b) (hb := hb) f
  · -- 唯一性：任意满足规格的 r 都必须等于 r₀
    intro r hr
    -- 这一步正是你前面证明/准备证明的“算法余式唯一性”：
    --   reduceFamily_unique：若 r 也满足规格，则 r = reduceFamily ...
    exact reduceFamily_unique (m := m) (b := b) hb hGB f r hr
    -- 如果你想直接把唯一性塞进这个定理里，也可以把


/-- 若 `b` 是 Groebner 基，且 `f `属于 `b` 生成的理想，则 `f `模 `b `的余式为0。 -/
lemma remainder_eq_zero_of_mem_span
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hGB : m.IsGroebnerBasis₂ (Set.range b) (Ideal.span (Set.range b)))
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
        simp only [linearCombination_apply, sum, coe_mk, smul_eq_mul, id_eq]
        apply Finset.sum_nbij (↑·)
        · simp_intro ..
        · simp_intro b _ b₁ _ h [Subtype.ext_iff]
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
        simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, Finset.filter_and,
          Finset.filter_mem_eq_inter, Finset.inter_self, Finset.inter_filter, onFinset_apply, id_eq,
          smul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.filter_inter]
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
      · simp only [linearCombination_apply, sum, id_eq, smul_eq_mul] at hsum
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
        simp only at h₂
        by_cases h' : (Finsupp.embDomain idx g) i = 0
        · simp [h']
        simp only at h'
        convert h₂
        generalize_proofs hbi
        convert_to g.embDomain idx (hbi.choose) = _
        · simp only [embDomain_eq_mapDomain, mapDomain, sum_apply, single_apply] at ⊢ h'
          congr
          ext
          congr
          obtain ⟨a, ha, ha'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
          simp [idx] at ha'
          convert_to i = Set.rangeSplitting b ⟨b i, hbi⟩
          simp [← ha'.1, Set.apply_rangeSplitting]
        · exact Finsupp.embDomain_apply_self idx g ⟨b i, hbi⟩
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
          simp only [g']
          rw [Finset.sum_filter]
          suffices (g.support.filter (fun i => b' i = x)) = ∅ by
            rw [← Finset.sum_filter, this, Finset.sum_empty]
          ext i
          simp only [Finsupp.mem_support_iff, ne_eq] at hx
          simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, Finset.notMem_empty,
            iff_false, not_and]
          exact hx i
        simp only [Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, Finset.mem_singleton,
          b_support]
        use i
        constructor
        · exact Finsupp.mem_support_iff.mp hi
        · exact hb'x.symm
      use Finsupp.onFinset b_support g' mem_support
      split_ands
      · simp only [h₁, linearCombination_apply, sum, smul_eq_mul, onFinset_apply, add_left_inj]
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
        simp only [onFinset, coe_mk, g']
        rw [Finset.mul_sum]
        have sum_eq : (∑ i ∈ g.support.filter (fun i => b' i = b1), ↑b1 * g i) =
            (∑ i ∈ g.support.filter (fun i => b' i = b1), b i * g i) := by
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [Finset.mem_filter] at hi
          congr
          exact Subtype.ext_iff.mp hi.2.symm
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
  suffices g b = 0 ∨ b.1 = 0 by
    by_cases h : g b = 0
    ·simp [h]
    ·simp [this.resolve_left h]
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
     MvPolynomial.mem_support_iff, ne_eq, not_false_eq_true, implies_true,
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


/-- 用良基递归构造 `f - r` 的线性组合证书（`r = reduceFamily b hb f`），
并同时保证每项 `degree ((b' : _) * g b') ≤ degree f`。 -/
lemma reduceFamily_linearCertificate
  (f : MvPolynomial σ R)(b : ι → MvPolynomial σ R)(hb : ∀ i, IsUnit (m.leadingCoeff (b i)))  :
  ∃ g : (Set.range b) →₀ MvPolynomial σ R,
    let r := m.reduceFamily b hb f
    f = Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R))
 g + r
    ∧ ∀ s : (Set.range b),
         m.degree ((s : MvPolynomial σ R) * g s) ≼[m] m.degree f := by
  classical
  -- 良基归纳（用 μ := m.toSyn ∘ m.degree）
  have wfμ := m.wf_μ (σ := σ) (R := R)
  refine
    (wfμ.induction
      (C := fun f =>
        ∃ g : (Set.range b) →₀ MvPolynomial σ R,
          let r := m.reduceFamily b hb f
          f = Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R))
 g + r
          ∧ ∀ s : (Set.range b),
               m.degree ((s : MvPolynomial σ R) * g s) ≼[m] m.degree f)
      f
      ?step)
  -- 归纳步
  intro g IH
  by_cases hg0 : g = 0
  · -- g=0：r=0，取 g≡0 即可
    refine ⟨0, ?_⟩
    intro r
    simp [hg0]
    subst hg0
    simp_all only [Subtype.forall, Set.mem_range, forall_exists_index, reduceFamily_eq_zero, r]  -- r=0
  -- g ≠ 0
  by_cases h : HeadReducible m b g
  · -- 头约一步：把 “一步差” 写成某个 `single`，其余由 IH 提供
    rcases m.reduceFamily_eq_head_step (b := b) (hb := hb)
              (hf0 := hg0) (h := h) with ⟨i, hi, hdef⟩
    -- 记 r' 与证书 g'（归纳）：
    set g' := m.reduce (hb i) g
    -- 用统一的“二选一”引理，避免手工 `by_cases`
    have hstep :
      m.toSyn (m.degree g') < m.toSyn (m.degree g) ∨ g' = 0 :=
      mu_lt_after_one_reduce_or_const_zero (m := m) (b := b) (hb := hb)
        (g := g) (i := i) hi
    -- 本步一次配平的“系数多项式”
    let t : MvPolynomial σ R :=
      monomial (m.degree g - m.degree (b i))
               ((hb i).unit⁻¹ * m.leadingCoeff g)
    -- 线性组合里用到的“单点”键
    let s₀ : Set.range b := ⟨b i, ⟨i, rfl⟩⟩
    have coe_s₀ : ((s₀ : Set.range b) : MvPolynomial σ R) = b i := rfl
    -- `g' = g - t * (b i)` 的计算（直接来自 reduce 的定义）
    have hreduce : g' = g - t * b i := by
      simp [g', t, MonomialOrder.reduce]
    -- 把 `g = g' + t * b i` 写出来（便于拼接等式）
    have g_eq : g = g' + t * b i := by
      -- 由上一式两边加上 `t * b i`
      have := congrArg (fun x => x + t * b i) hreduce
      -- 右侧展开并化简到 `g`
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
    -- 线性组合：单点的线性组合就是“系数乘基向量”（此处为左乘）
    have lin_single :
        Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R))
          (Finsupp.single s₀ t)
        = t * (s₀ : MvPolynomial σ R) := by
      -- `•` 与乘法一致
      simp [Finsupp.linearCombination_single, smul_eq_mul]
    -- 两种情形分开处理
    cases hstep with
    | inl μlt =>
        -- 归纳假设给 `g'`
        rcases IH g' μlt with ⟨gcert', hEq', hBd'⟩
        -- 把归纳给的 `r'` 与当前的 `r` 对齐
        -- `r = reduceFamily g = reduceFamily g'`
        have hr :
          m.reduceFamily b hb g = m.reduceFamily b hb g' := hdef
        -- 目标证书：把上一步证书加上这次配平的“单点”
        let gcert := gcert' + Finsupp.single s₀ t
        refine ⟨gcert, ?eq_goal , ?bd_goal⟩
        · let r' := m.reduceFamily b hb g'
          have hEqg' : g' =
              Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert' + r' := by
            simpa [r'] using hEq'
          -- 我们的目标里也有一个 `let r := reduceFamily g`，先把它换成“无 let”的形状
          change g =
              Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert
              + m.reduceFamily b hb g
          -- 串起等式链
          have : g =
                Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert
                + m.reduceFamily b hb g := by
            calc
              g = g' + t * (b i) := by simp [g_eq]
              _ = (Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert' + r') + t * (b i) := by
                    -- 给 hEqg' 两边同时加上 t * (b i)
                    simpa using congrArg (fun x => x + t * (b i)) hEqg'
              _ = (Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert' + t * (b i)) + r' := by
                    -- 交换和结合，换成 (LC + t*b i) + r'
                    simp [add_comm, add_left_comm]
              _ = Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R))
                      (gcert' + Finsupp.single s₀ t) + r' := by
                    -- 线性组合同态性 + 单点公式
                    simp [map_add, lin_single]
                    exact rfl
              _ = Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert
                    + m.reduceFamily b hb g := by
                    -- gcert 的定义 & r 与 r' 由 hr 相等
                    simp [gcert, hr, r']
          exact this
        · -- 度不等式部分
          intro s
          -- 分两类：来自旧证书的项，或刚加的单点
          by_cases hs : s = s₀
          · -- 新增的“单点”项：证明 `deg (t * b i) ≤ deg g`
            subst hs
            -- 把 (↑s₀) 与 gcert s₀ 的具体值写出来
            -- s₀ 就是 ⟨b i, ⟨i, rfl⟩⟩，所以强制类型后等于 b i
            have coe_s₀ : ((s₀ : Set.range b) : MvPolynomial σ R) = b i := rfl
            -- gcert = gcert' + single s₀ t ⇒ gcert s₀ = gcert' s₀ + t
            have val_s₀ : gcert s₀ = gcert' s₀ + t := by
              simp [gcert, Finsupp.add_apply, Finsupp.single_eq_same]
            -- 先把目标中的乘积改写成“老项 + 新增单点”的和
            have rewrite :
                ((s₀ : MvPolynomial σ R) * gcert s₀)
                  = (b i) * gcert' s₀ + (b i) * t := by
              simp [coe_s₀, val_s₀, mul_add, add_comm]
            -- （A）旧证书对应的一项：用 IH 的度上界 + μ 严格变小
            have hleft :
                m.toSyn (m.degree ((b i) * gcert' s₀)) ≤ m.toSyn (m.degree g) :=
              le_trans
                (by simpa [coe_s₀] using hBd' s₀)
                (le_of_lt μlt)
            -- 三段式：乘法 ≤，单项式 ≤ 指数，最后 `(d - e) + e ≤ d`
            have h₁ :
              m.toSyn (m.degree (t * b i))
                ≤ m.toSyn (m.degree t + m.degree (b i)) :=
              m.degree_mul_le (f := t) (g := b i)
            have h₂ :
              m.toSyn (m.degree t + m.degree (b i))
                ≤ m.toSyn ((m.degree g - m.degree (b i)) + m.degree (b i)) := by
              -- 由 `degree_monomial_le` 把 `deg t` 压到 `deg g - deg(b i)`
              have ht : m.toSyn (m.degree t)
                        ≤ m.toSyn (m.degree g - m.degree (b i)) := by
                -- 展开 t 的定义
                simpa [t] using (m.degree_monomial_le
                  ((hb i).unit⁻¹ * m.leadingCoeff g))
              -- 把 `≤` 右边加上 `deg (b i)`，再用同构的加法性
              simpa [map_add] using add_le_add_right ht (m.toSyn (m.degree (b i)))
            have h₃ :
              m.toSyn ((m.degree g - m.degree (b i)) + m.degree (b i))
                ≤ m.toSyn (m.degree g) := by
              -- 先在指数向量上做“点态”证明
              have hpt :
                (m.degree g - m.degree (b i)) + m.degree (b i) ≤ m.degree g := by
                classical
                -- Finsupp 的 ≤ 是逐坐标的：引入一个坐标 a
                intro a
                -- 用自然数恒等式 `Nat.sub_add_cancel (hi a)`，得到等式，从而得到 ≤
                have : (m.degree g a - m.degree (b i) a) + m.degree (b i) a
                        = m.degree g a :=
                  Nat.sub_add_cancel (hi a)
                -- 把等式转成 ≤，并把左右两边还原成 Finsupp 的逐点取值
                simpa [Finsupp.add_apply, Finsupp.sub_apply] using (le_of_eq this)
              -- 利用 `toSyn` 的单调性把 `hpt` 映到 `syn` 里
              exact m.toSyn_monotone hpt
            have hright :
              m.toSyn (m.degree ((b i) * t)) ≤ m.toSyn (m.degree g) :=
            le_trans (by simpa [mul_comm] using h₁) (le_trans h₂ h₃)
            -- 把两项的上界合到和上：degree_add_le 再用 sup_le_iff
            have hsum :
                m.toSyn (m.degree ((b i) * gcert' s₀ + (b i) * t))
                  ≤ m.toSyn (m.degree g) := by
              refine le_trans (m.degree_add_le) ?_
              -- `sup_le_iff`：分别给出左、右两项的 ≤
              exact sup_le hleft hright
            -- 用 rewrite 改回目标的样子
            simpa [rewrite]
              -- 目标正是 `m.toSyn (m.degree ((↑s₀) * gcert s₀)) ≤ m.toSyn (m.degree g)`
              using hsum
          · -- 旧证书项：用归纳的上界再接 `μlt` 得到 ≤ `deg g`
            have hold : m.toSyn (m.degree ((s : MvPolynomial σ R) * gcert' s))
                          ≤ m.toSyn (m.degree g') := hBd' s
            have : m.toSyn (m.degree ((s : MvPolynomial σ R) * gcert s))
                    ≤ m.toSyn (m.degree g') := by
              -- `gcert = gcert' + single s₀ t`，当 `s ≠ s₀` 时该坐标不变
              have : gcert s = gcert' s := by
                simp [gcert, hs]
              simpa [this]
            exact le_trans this (le_of_lt μlt)
    | inr hred0 =>
        -- 一步就归零：这时 r = 0（用 hdef + reduceFamily(0)=0）
        have hr :
          m.reduceFamily b hb g = 0 := by simpa [g', hred0] using hdef
        -- 取“只有一个坐标”的证书
        let gcert := Finsupp.single s₀ t
        refine ⟨gcert, ?eq_goa , ?bd_goa⟩
        · -- 等式：g = (单点线性组合) + 0
          -- 由 g = 0 + t*b i 与线性组合单点定理得到
          have : Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert
                 = t * (b i) := by
            simp [gcert]
            exact rfl
          simpa [g_eq, this,hred0] using hr
        · -- 度不等式：唯一的坐标同上一个“单点”分支
          intro s
          by_cases hs : s = s₀
          · subst hs
            -- 仍然是证明 `deg (t * b i) ≤ deg g`
            -- 展开 (↑s₀) 与 gcert s₀
            -- s₀ 对应的底元就是 b i
            have coe_s₀ : ((s₀ : Set.range b) : MvPolynomial σ R) = b i := rfl
            -- gcert = single s₀ t ⇒ gcert s₀ = t
            have val_s₀ : gcert s₀ = t := by
              simp [gcert, Finsupp.single_eq_same]
            -- 把目标里的 (↑s₀) * gcert s₀ 改写成 (b i) * t
            have rewrite :
                ((s₀ : MvPolynomial σ R) * gcert s₀) = (b i) * t := by
              simp [coe_s₀, val_s₀]
            -- （1）乘法度上界：deg ((b i) * t) ≤ deg(b i) + deg t
            have h₁ :
              m.toSyn (m.degree (t * b i))
                ≤ m.toSyn (m.degree t + m.degree (b i)) :=
              m.degree_mul_le (f := t) (g := b i)
            have h₂ :
              m.toSyn (m.degree t + m.degree (b i))
                ≤ m.toSyn ((m.degree g - m.degree (b i)) + m.degree (b i)) := by
              have ht : m.toSyn (m.degree t)
                        ≤ m.toSyn (m.degree g - m.degree (b i)) := by
                simpa [t] using (m.degree_monomial_le
                  ((hb i).unit⁻¹ * m.leadingCoeff g))
              simpa [map_add] using add_le_add_right ht (m.toSyn (m.degree (b i)))
            have h₃ :
              m.toSyn ((m.degree g - m.degree (b i)) + m.degree (b i))
                ≤ m.toSyn (m.degree g) := by
              -- 先在指数向量上做“点态”证明
              have hpt :
                (m.degree g - m.degree (b i)) + m.degree (b i) ≤ m.degree g := by
                classical
                -- Finsupp 的 ≤ 是逐坐标的：引入一个坐标 a
                intro a
                -- 用自然数恒等式 `Nat.sub_add_cancel (hi a)`，得到等式，从而得到 ≤
                have : (m.degree g a - m.degree (b i) a) + m.degree (b i) a
                        = m.degree g a :=
                  Nat.sub_add_cancel (hi a)
                -- 把等式转成 ≤，并把左右两边还原成 Finsupp 的逐点取值
                simpa [Finsupp.add_apply, Finsupp.sub_apply] using (le_of_eq this)
              -- 利用 `toSyn` 的单调性把 `hpt` 映到 `syn` 里
              exact m.toSyn_monotone hpt
            exact
              (by
                simpa [rewrite,mul_comm] using le_trans h₁ (le_trans h₂ h₃))
          · -- 该坐标为 0
            have : gcert s = 0 := by simp [gcert, hs]
            simp [this]
  -- 不可头约
  · by_cases hdeg0 : m.degree g = 0
    · -- 常数：r = g，证书取 0
      refine ⟨0, ?_⟩
      have : m.reduceFamily b hb g = g :=by exact reduceFamily_degree_zero_notHR m b hb hg0 hdeg0 h
      simp [this, map_zero]
    · -- 度非零：把首项剥入余式，对 `subLTerm g` 做归纳
      have μlt_sub :
        m.toSyn (m.degree (m.subLTerm g)) < m.toSyn (m.degree g) :=
        m.degree_sub_LTerm_lt (f := g) hdeg0
      -- 归纳假设给 `subLTerm g`
      rcases IH (m.subLTerm g) μlt_sub with ⟨gcert', hEq', hBd'⟩
      -- `r = initTerm g + reduceFamily(subLTerm g)`
      have rdef :
        m.reduceFamily b hb g =
          m.leadingTerm g + m.reduceFamily b hb (m.subLTerm g) :=
        reduceFamily_eq_notHead_degpos m b hb hg0 h hdeg0
      · -- 这一步只需要 `¬ g = 0`，由“不可头部约化 + deg g ≠ 0” 得出
        -- 若 g = 0 与 hdeg0 矛盾（deg 0 = 0）
        -- 选取证书：直接复用 IH 给 subLTerm g 的证书
        refine ⟨gcert', ?eq_go, ?bd_go⟩
        · -- `?eq_goal`
          have : g = m.leadingTerm g + m.subLTerm g := by
            -- subLTerm 的定义是 g - initTerm g
            -- 所以 g = initTerm g + (g - initTerm g)
            simp [subLTerm,leadingTerm]
          calc
            g
                = m.leadingTerm g + m.subLTerm g := this
            _   = m.leadingTerm g + ((Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert')
                                  + m.reduceFamily b hb (m.subLTerm g)) := by
                  -- 用 hEq' 改写 subLTerm g
                  exact congrArg (HAdd.hAdd (m.leadingTerm g)) hEq'
            _   = (Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert')
                  + (m.leadingTerm g + m.reduceFamily b hb (m.subLTerm g)) := by
                  -- 交换加数的结合顺序
                  ac_rfl
            _   = (Finsupp.linearCombination (MvPolynomial σ R) (fun s : (Set.range b) => (s : MvPolynomial σ R)) gcert')
                  + (m.reduceFamily b hb g) := by
                  -- 用 rdef : reduceFamily g = initTerm g + reduceFamily (subLTerm g)
                  simp [rdef]
        -- 度不等式部分：IH 给到的是 ≤ deg(subLTerm g)，我们用 μlt_sub : deg(subLTerm g) < deg g 抬到 ≤ deg g
        · -- `?bd_goal`
          intro s
          exact le_trans (hBd' s) (le_of_lt μlt_sub)


end Certificate

/-! ## `reduceFamily` 产生的余式满足 `IsRemainder` -/
theorem IsRemainder_reduceFamily
  {b : ι → MvPolynomial σ R}
  (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
  (f : MvPolynomial σ R) :
  m.IsRemainder f (Set.range b) (m.reduceFamily b hb f) := by
  classical
  obtain ⟨g, hEq, hbd⟩ :=
    m.reduceFamily_linearCertificate (b := b) (hb := hb) f
  refine And.intro ?h1 ?h2
  ·
    refine ⟨g, ?_, ?_⟩
    · simpa using hEq
    ·
      intro bB
      rcases bB with ⟨p, hp⟩
      exact hbd ⟨p, hp⟩
  · -- 第二部分：逐项完全不可约（对每个支撑指数 c 与任意 b∈B）
    -- 直接调用上面完成的 `reduceFamily_noDivisible`
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
    -- `•` 在这里就是乘法（`smul_eq_mul`）
    simp only [linearCombination, coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
      smul_eq_mul]
    -- 目标现在是： `∑ s ∈ g.support, g s * (s : _) ∈ span (range b)`
    -- 用加法封闭性（对 Finset 的逐项成员性做 `sum_mem`）
    refine (Ideal.span (Set.range b)).sum_mem ?term_mem
    intro s hs
    -- 生成元 `s.val` 本来就在 `span (range b)` 里
    have hs' : (s : MvPolynomial σ R) ∈ Ideal.span (Set.range b) :=
      Ideal.subset_span s.property
    -- 理想对环乘法封闭：`a * x ∈ I`
    exact Ideal.mul_mem_left _ _ hs'
  -- 回代等式
  simpa [hEq] using hLC_mem











lemma span_leadingMonomial_eq_span_monomial {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p)) :
    Ideal.span (m.leadingMonomial '' B) =
      Ideal.span ((fun p ↦ MvPolynomial.monomial (m.degree p) (1 : R)) '' B) := by
  classical
  -- 分情况：R 是否平凡
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      -- 平凡环：所有理想相等，命题平凡成立
      haveI := hR
      simpa using
        (Subsingleton.elim
          (Ideal.span (m.leadingMonomial '' B))
          (Ideal.span ((fun p ↦ MvPolynomial.monomial (m.degree p) (1 : R)) '' B)))
  | inr _ =>
      -- 非平凡环：按生成元逐点相等证明两边 span 相等
      apply le_antisymm
      · refine Ideal.span_mono ?subset
        intro x hx
        rcases hx with ⟨p, hpB, rfl⟩
        -- 由 LC 单位得 LC ≠ 0，从而 p ≠ 0
        have hp0 : p ≠ 0 := by
          have : m.leadingCoeff p ≠ 0 := (hB p hpB).ne_zero
          intro h; subst h; simp at this
        exact ⟨p, hpB, by simp [leadingMonomial, hp0]⟩
      · refine Ideal.span_mono ?_
        intro x hx
        rcases hx with ⟨p, hpB, hx⟩
        have hp0 : p ≠ 0 := by
          have : m.leadingCoeff p ≠ 0 := (hB p hpB).ne_zero
          intro h; subst h; simp at this
        exact ⟨p, hpB, by simpa [leadingMonomial, hp0] using hx⟩








/--
The leading term in a multivariate polynomial is zero if and only if this polynomial is zero.
-/
@[simp]
lemma leadingMonomial_eq_zero_iff (p : MvPolynomial σ R) : m.leadingMonomial p = 0 ↔ p = 0 := by
  simp [leadingMonomial, monomial_eq_zero]
  apply Iff.intro
  · intro a
    by_contra h
    have :=a h
    exact false_of_one_eq_zero_or_subsingleton h (a h)
  · intro a a_1
    subst a
    simp_all only [not_true_eq_false]


/--
The leading terms of non-zero polynomials within a set `B` is equal to the leading terms
of all polynomials in B, excluding zero.
-/
lemma image_leadingMonomial_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
    m.leadingMonomial '' (B \ {0}) = (m.leadingMonomial '' B) \ {0} := by
  ext x : 1
  simp_all only [Set.mem_image, Set.mem_diff, Set.mem_singleton_iff, ne_eq]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨left, right_1⟩ := left
    subst right
    simp_all only [leadingMonomial_eq_zero_iff, not_false_eq_true, and_true]
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
    simp_all only [leadingMonomial_eq_zero_iff]
    apply Exists.intro
    · apply And.intro
      on_goal 2 => { rfl
      }
      · simp_all only [not_false_eq_true, and_self]


lemma span_leadingMonomial_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
    Ideal.span (m.leadingMonomial '' (B \ {0})) = Ideal.span (m.leadingMonomial '' B) :=
  m.image_leadingMonomial_sdiff_singleton_zero B ▸ Ideal.span_sdiff_singleton_zero


open Classical in
@[simp]
lemma isGroebnerBasis_sdiff_singleton_zero₂ (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) :
    m.IsGroebnerBasis₂ (G \ {0}) I ↔ m.IsGroebnerBasis₂ G I := by
  simp [IsGroebnerBasis₂, m.span_leadingMonomial_sdiff_singleton_zero]

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



/--
若 `f ∈ ⟨range b⟩`、`f ≠ 0` 且 `reduceFamily b hb f = 0`，
则存在某个下标 `i` 使得 `m.degree (b i) ≤ m.degree f`。
直观上：`f` 是由 `b i` 线性组合得到的非零多项式，
而余式为 0，意味着在“最高项层面”必然某个 `LM(b i)` 参与了构成 `LM(f)`，
从而得到 `LM(b i) ≤ LM(f)`。
-/
lemma exists_le_of_remainder_zero
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R}
    (hf0 : f ≠ 0)
    (hfrem : m.reduceFamily b hb f = 0) :
    ∃ i, m.degree (b i) ≤ m.degree f := by
  classical
  -- 分情形证明：若 `f` 不可头约，则与 `hfrem` 矛盾；从而 `f` 必可头约，结论即出
  by_contra hnone
  -- hnone: ¬ (∃ i, degree (b i) ≤ degree f)  ⇒  ¬ HeadReducible m b f
  -- （此处使用你当前的 HeadReducible 定义：`HeadReducible m b f := f ≠ 0 ∧ ∃ i, …`）
  have hNotHR : ¬ HeadReducible m b f := by
    intro hHR
    rcases hHR with ⟨_, ⟨i, hi⟩⟩
    exact hnone ⟨i, hi⟩
  -- 先排除“常数分支”：若 deg f = 0，则 reduceFamily 必等于 f 本身，与 hfrem 矛盾
  have hdegpos : m.degree f ≠ 0 := by
    intro hdeg0
    have : m.reduceFamily b hb f = f :=
      reduceFamily_eq_notHead_deg0 (m := m) (b := b) (hb := hb)
        (f := f) hf0 hNotHR hdeg0
    -- 与给定的余式为 0 矛盾
    exact (by
      have : f = 0 := by simpa [this] using hfrem
      exact hf0 this)
  -- 此时走“非零度且不可头约”的分支：
  --    r = initTerm f + reduceFamily(subLTerm f)
  have rdef :
      m.reduceFamily b hb f =
        m.leadingTerm f + m.reduceFamily b hb (m.subLTerm f) :=
    reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb)
      (f := f) hf0 hNotHR hdegpos
  -- 尾项严格更小（在 μ 上）：μ( reduceFamily(subLTerm f) ) < μ(f)
  have μlt_tail :
      m.toSyn (m.degree (m.reduceFamily b hb (m.subLTerm f)))
        < m.toSyn (m.degree f) :=
    mu_reduceFamily_lt_of_lt (m := m) (b := b) (hb := hb)
      (m.degree_sub_LTerm_lt (f := f) hdegpos)
  -- “首项 + 更小尾项”的 μ-不变性：μ(deg r) = μ(deg f)
  have mu_eq :
      m.toSyn (m.degree (m.reduceFamily b hb f))
        = m.toSyn (m.degree f) := by
    simpa [rdef] using
      mu_degree_initTerm_add_of_lt (m := m) (f := f)
        (g := m.reduceFamily b hb (m.subLTerm f)) μlt_tail
  -- 因为 μ(deg r) = μ(deg f) 且 deg f ≠ 0，所以 r ≠ 0
  have r_ne0 : m.reduceFamily b hb f ≠ 0 := by
    intro hr0
    -- 若 r = 0，则 μ(deg 0) = μ(deg f)，由 toSyn 的单射性得 deg f = 0，矛盾
    have : m.toSyn (m.degree (0:MvPolynomial σ R)) = m.toSyn (m.degree f) := by
      simpa [hr0] using mu_eq
    have : m.degree f = (m.degree 0) := m.toSyn.injective this.symm
    rw[show (m.degree 0) = 0 by exact degree_zero] at this
    exact hdegpos this
  -- 但已知余式为 0，矛盾
  exact r_ne0 hfrem


/--
在单位假设下，如果 `f ∈ ⟨range b⟩`、`f ≠ 0` 且余式为 `0`，
则 `initMonomial f ∈ ⟨ initMonomial ∘ b ⟩`。
-/
lemma leadingMonomial_mem_span_image_of_remainder_zero
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R}
    (hf0 : f ≠ 0)
    (hfrem : m.reduceFamily b hb f = 0) :
    m.leadingMonomial f ∈ Ideal.span (m.leadingMonomial '' (Set.range b)) := by
  classical
  -- 第一步：由“余式为 0”得到 ∃ i, LM(b i) ≤ LM(f)
  have hExists :
      ∃ i, m.degree (b i) ≤ m.degree f :=
    exists_le_of_remainder_zero (m := m) (b := b) (hb := hb)
      (f := f) hf0 hfrem
  -- 第二步：用你已有的等价 `initMonomial_mem_span_image_iff_exists_le`
  have hIff :
      m.leadingMonomial f ∈ Ideal.span (m.leadingMonomial '' (Set.range b))
        ↔ ∃ i, m.degree (b i) ≤ m.degree f :=
    m.leadingMonomial_mem_span_image_iff_exists_le
      (b := b) (hb := hb) (r := f) hf0
  -- 取 `↔` 的右向左
  exact hIff.mpr hExists



/-如果“对多项式集合b里的每个多项式f，f模b的余式都是 0”，
那么 `b` 就是 Gröbner 基。-/
lemma isGroebnerBasis_of_all_remainders_zero
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hrem : ∀ f ∈ Ideal.span (Set.range b),m.reduceFamily b hb f = 0) :
    m.IsGroebnerBasis₂ (Set.range b) (Ideal.span (Set.range b)):= by
  classical
  -- 用 Groebner 基的等价刻画：inₘ(⟨G⟩) = ⟨ initMonomial '' G ⟩
  apply (m.isGroebnerBasis_iff_for_span2 (Set.range b)).1
  apply (m.isGroebnerBasis_iff (Set.range b)).2
  -- 现在目标是一个理想等式，拆成双向包含
  refine le_antisymm ?hInitLE ?hSpanLE
  ·
    -- 把左边改写成生成元的 span 方便用 `Ideal.span_le`
    change
      Ideal.span {t | ∃ f ∈ Ideal.span (Set.range b), t = m.leadingMonomial f}
        ≤ Ideal.span (m.leadingMonomial '' (Set.range b))
    refine Ideal.span_le.2 ?_
    intro t ht
    rcases ht with ⟨f, hfI, rfl⟩
    -- 分 f = 0 / f ≠ 0 两种情况
    by_cases hf0 : f = 0
    · -- 若 f = 0，则 initMonomial f = 0，而 0 属于任意理想
      simp [hf0]
    · -- 若 f ≠ 0，则用我们的技术引理
      have hfrem : m.reduceFamily b hb f = 0 := hrem f hfI
      exact leadingMonomial_mem_span_image_of_remainder_zero
        (m := m) (b := b) (hb := hb)
        (f := f) hf0 hfrem
  ·
    refine Ideal.span_le.2 ?_
    intro t ht
    rcases ht with ⟨g, hg, rfl⟩
    rcases hg with ⟨i, rfl⟩
    -- b i ∈ ⟨range b⟩
    have hbI : b i ∈ Ideal.span (Set.range b) :=
      Ideal.subset_span ⟨i, rfl⟩
    -- 因此其首单项在 inₘ(⟨range b⟩) 中
    exact m.leadingMonomial_mem_initIdeal (I := Ideal.span (Set.range b)) hbI


end Ring

section Field
variable {σ ι R : Type*}
variable [Field R]

variable (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)


lemma span_leadingTerm_image_eq_span_leadingMonomial_image_on_set(m : MonomialOrder σ) (S : Set (MvPolynomial σ R)) :
    Ideal.span (m.leadingTerm '' S) = Ideal.span (m.leadingMonomial '' S) := by
    classical
    apply le_antisymm
    · -- ⊆
      refine Ideal.span_le.2 ?_
      intro t ht
      rcases ht with ⟨f, hfS, rfl⟩
      by_cases hf : f = 0
      · simp [leadingTerm, leadingMonomial, hf]
      -- leadingTerm f = C(lc f) * initMonomial f，乘单位不会跳出理想
      have hin : m.leadingMonomial f ∈ Ideal.span (m.leadingMonomial '' S) :=
        Ideal.subset_span ⟨f, hfS, rfl⟩
      have hlt := m.leadingTerm_eq_C_mul_leadingMonomial (hf:=hf)
      simpa [hlt] using Ideal.mul_mem_left _ _ hin
    · -- ⊇（对称地用逆单位）
      refine Ideal.span_le.2 ?_
      intro t ht
      rcases ht with ⟨f, hfS, rfl⟩
      by_cases hf : f = 0
      · simp [leadingTerm, leadingMonomial, hf]
      have hlc_ne : m.leadingCoeff f ≠ 0 :=m.leadingCoeff_ne_zero_iff.mpr hf
      have hunit : IsUnit (m.leadingCoeff f) :=
        isUnit_iff_ne_zero.mpr hlc_ne
      rcases hunit with ⟨u, hu⟩
      -- 由 (1) 得 leadingTerm f = C(u) * initMonomial f，移项得到
      have hinit :
        m.leadingMonomial f = MvPolynomial.C (↑(u⁻¹) : R) * m.leadingTerm f := by
        have h1 := m.leadingTerm_eq_C_mul_leadingMonomial (hf:=hf)
        -- 把等式左乘 C(u⁻¹)
        simp_all only [ ne_eq, not_false_eq_true, leadingMonomial_of_ne,
          leadingCoeff_eq_zero_iff, Units.val_inv_eq_inv_val, leadingTerm]
        ext m_1 : 1
        simp_all only [coeff_monomial, coeff_C_mul, mul_ite, mul_one, mul_zero, ne_eq, leadingCoeff_eq_zero_iff,
          not_false_eq_true, inv_mul_cancel₀]
      have hlt : m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' S) :=
        Ideal.subset_span ⟨f, hfS, rfl⟩
      have hmul :
          MvPolynomial.C (↑(u⁻¹) : R) * m.leadingTerm f
            ∈ Ideal.span (m.leadingTerm '' S) :=
        Ideal.mul_mem_left
          (Ideal.span (m.leadingTerm '' S))     -- 把理想显式给出
          (MvPolynomial.C (↑(u⁻¹) : R))         -- 把“要左乘的元素”也显式给出
          hlt
      -- 用 hinit 把目标从 `initMonomial f` 改写成 `C(u⁻¹) * leadingTerm f`
      simpa [hinit] using hmul

lemma span_leadingTerm_image_eq_span_leadingMonomial_image_on_ideal(m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) :
    Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) =
    Ideal.span (m.leadingMonomial '' (I : Set (MvPolynomial σ R))) := by
    classical
    simpa using
      m.span_leadingTerm_image_eq_span_leadingMonomial_image_on_set
        (S := (I : Set (MvPolynomial σ R)))


lemma isGroebnerBasisFor₂_iff_isGroebnerBasis1(m : MonomialOrder σ)
  (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) :
    m.IsGroebnerBasis₂ G I ↔ G ⊆ I ∧ Ideal.span (m.leadingTerm '' ↑I) = Ideal.span (m.leadingTerm '' G) := by
    classical
    -- 展开定义，只需把两侧的 span 都改写成对方
    unfold IsGroebnerBasis₂
    constructor
    · rintro ⟨hsub, hspan⟩
      refine ⟨hsub, ?_⟩
      -- 左边：I 上的像
      have hI :
        Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) =
        Ideal.span (m.leadingMonomial '' (I : Set (MvPolynomial σ R))) :=
        m.span_leadingTerm_image_eq_span_leadingMonomial_image_on_ideal I
      -- 右边：G 上的像
      have hG :
        Ideal.span (m.leadingTerm '' G) =
        Ideal.span (m.leadingMonomial '' G) :=
        m.span_leadingTerm_image_eq_span_leadingMonomial_image_on_set G
      -- 链式替换
      calc
        Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))
            = Ideal.span (m.leadingMonomial '' (I : Set (MvPolynomial σ R))) := hI
        _ = Ideal.span (m.leadingMonomial '' G) := hspan
        _ = Ideal.span (m.leadingTerm '' G) := hG.symm
    · rintro ⟨hsub, hspan⟩
      refine ⟨hsub, ?_⟩
      -- 同理反向替换
      have hI :=
        (m.span_leadingTerm_image_eq_span_leadingMonomial_image_on_ideal I).symm
      have hG :=
        (m.span_leadingTerm_image_eq_span_leadingMonomial_image_on_set G).symm
      calc
        Ideal.span (m.leadingMonomial '' (I : Set (MvPolynomial σ R)))
            = Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) := hI
        _ = Ideal.span (m.leadingTerm '' G) := hspan
        _ = Ideal.span (m.leadingMonomial '' G) := hG.symm

lemma Grobner_def_eq(m : MonomialOrder σ)
  (G : Set (MvPolynomial σ R)) :
  m.IsGroebnerBasis₂ G (Ideal.span G)
  = (G ⊆ (Ideal.span G) ∧ Ideal.span (m.leadingTerm '' ↑(Ideal.span G)) = Ideal.span (m.leadingTerm '' G)) := by
    classical
    apply propext
    exact m.isGroebnerBasisFor₂_iff_isGroebnerBasis1 (G:=G) (I:=Ideal.span G)

/--域R上的神中神定理，证明了两种等价的定义-/
lemma Grobner_def_eq₂(m : MonomialOrder σ)
  (G : Set (MvPolynomial σ R)) :
  m.IsGroebnerBasis G
  = (G ⊆ (Ideal.span G) ∧ Ideal.span (m.leadingTerm '' ↑(Ideal.span G)) = Ideal.span (m.leadingTerm '' G)) := by
    classical
    apply propext
    constructor
    ·
      intro p
      exact m.isGroebnerBasisFor₂_iff_isGroebnerBasis1 (G:=G) (I:=Ideal.span G).mp ((m.isGroebnerBasis_iff_for_span2 G).mp p)
    ·
      intro p
      exact (m.isGroebnerBasis_iff_for_span2 G).mpr (m.isGroebnerBasisFor₂_iff_isGroebnerBasis1 (G:=G) (I:=Ideal.span G).mpr p)



lemma degree_sub_leadingTerm_le1 (f : MvPolynomial σ R) :
      m.degree (f - m.leadingTerm f) ≼[m] m.degree f := by
    apply le_trans degree_sub_le
    simp [degree_leadingTerm]

lemma degree_sub_leadingTerm (f : MvPolynomial σ R) :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f ∨ f - m.leadingTerm f = 0 := by
    classical
    rw [or_iff_not_imp_right]
    intro h
    apply lt_of_le_of_ne (m.degree_sub_leadingTerm_le1 f) ?_
    simp_intro h'
    apply m.degree_mem_support at h
    rw [h', MvPolynomial.mem_support_iff] at h
    simp [leadingTerm, leadingCoeff] at h




theorem degree_sub_leadingMonomial_le (f : MvPolynomial σ R) :
    m.degree (f - m.leadingMonomial f) ≼[m] m.degree f := by
  classical
  -- 把 `≼[m]` 改写成 `toSyn _ ≤ toSyn _`
  by_cases hf0 : f = 0
  · -- 零情形，直接化简
    simp [hf0, leadingMonomial, sub_self]
  ·
    -- 关键：`deg (initMonomial f) ≤ deg f`
    have hdeg_init_le :
        m.toSyn (m.degree (m.leadingMonomial f)) ≤ m.toSyn (m.degree f) := by
      -- 用 `degree_le_iff`：对 `initMonomial f` 的每个支撑单项 `b`，证 `toSyn b ≤ toSyn (deg f)`
      refine (m.degree_le_iff (f := m.leadingMonomial f)).2 ?_
      intro b hb
      have hbne : (m.leadingMonomial f).coeff b ≠ 0 := by
        simpa [Finsupp.mem_support_iff] using hb
      -- 展开 `initMonomial` 后的系数：只有在 `b = deg f` 时系数为 1，否则为 0
      have hcoeff :
          (m.leadingMonomial f).coeff b
            = (if b = m.degree f then (1 : R) else 0) := by
        have hmk : m.leadingMonomial f
              = MvPolynomial.monomial (m.degree f) (1 : R) :=
          m.leadingMonomial_of_ne (f := f) hf0
        -- 注意 `coeff_monomial` 的形状是 `coeff _ (monomial _ _) = ite _ _ _`
        simp [hmk, MvPolynomial.coeff_monomial, eq_comm]
      -- 由 `hbne` 推出 `b = deg f`
      have hb_eq : b = m.degree f := by
        classical
        by_contra hne
        have : (m.leadingMonomial f).coeff b = 0 := by
          simp [hcoeff, hne]
        exact hbne this
      -- 得到所需的 ≤（实际上是相等）
      simp [hb_eq]
    -- 套用三角不等式：`deg(f - g) ≤ deg f ⊔ deg g`，再用上面的界把 `⊔` 收到 `deg f`
    exact
      (le_trans (m.degree_sub_le (f := f) (g := m.leadingMonomial f))
                (sup_le le_rfl hdeg_init_le))




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
  obtain ⟨b, hb⟩ := Finset.mem_biUnion.mp <| hsum.symm ▸ Finset.mem_of_subset MvPolynomial.support_sum this
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
lemma term_notMem_span_leadingTerm_of_isRemainder {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)} (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingMonomial '' B) := by
  classical
  intro s hs
  rw [m.span_leadingMonomial_eq_span_monomial hB, ← Set.image_image (monomial · 1) _ _,
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
  simp [hq0] at hB



/-- Given a remainder `r` of a polynomial `p` on division by a Gröbner basis `G` of an ideal `I`,
the remainder `r` is 0 if and only if `p` is in the ideal `I`.

Any leading coefficient of polynomial in the Gröbner basis `G` is required to be a unit. -/
theorem remainder_eq_zero_iff_mem_ideal_of_isGroebner
    {p : MvPolynomial σ R} {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    {r : MvPolynomial σ R} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) (h : m.IsGroebnerBasis₂ G I)
    (hr : m.IsRemainder p G r) :
    r = 0 ↔ p ∈ I := by
  constructor
  · rw [← m.mem_ideal_iff_of_isRemainder h.1 hr]
    simp_intro ..
  · intro h_p_mem
    by_contra hr_ne_zero
    -- 我们处在 `by_contra hr_ne_zero` 分支，所以 `r ≠ 0`
    have hcoeff_ne : r.coeff (m.degree r) ≠ 0 := by
      -- 等价于 `m.leadingCoeff r ≠ 0`
      simpa [MonomialOrder.leadingCoeff] using
        (m.leadingCoeff_ne_zero_iff.mpr hr_ne_zero)
    have hsupp : m.degree r ∈ r.support := by
      simpa [MvPolynomial.mem_support_iff] using hcoeff_ne
    -- 由“余式的每个项都不在 span(initMonomial '' G)”得到顶项也不在
    have h_term_not_mem :
        monomial (m.degree r) (r.coeff (m.degree r))
          ∉ Ideal.span (m.leadingMonomial '' (↑G)) :=
      term_notMem_span_leadingTerm_of_isRemainder
        (m := m) (p := p) (r := r) (B := (↑G))
        hG hr (s := m.degree r) hsupp
    have h₃: m.leadingMonomial r ∉ Ideal.span (m.leadingMonomial '' ↑G) := by
      intro hmem
      -- 理想对标量封闭：把 `initMonomial r` 乘上系数 `r.coeff (m.degree r)`
      have hsmul :
          (r.coeff (m.degree r)) • m.leadingMonomial r
            ∈ Ideal.span (m.leadingMonomial '' (↑G)) :=
              Submodule.smul_of_tower_mem (Ideal.span (m.leadingMonomial '' G)) (coeff (m.degree r) r)
                hmem
      -- 把 `•` 改写成 `C _ * _`，并用 `r ≠ 0` 展开 `initMonomial`
      have : (r.coeff (m.degree r)) • m.leadingMonomial r
              = monomial (m.degree r) (r.coeff (m.degree r)) := by
        have hr0 : r ≠ 0 := hr_ne_zero
        -- `initMonomial r = monomial (degree r) 1` 当 `r ≠ 0`
        have hin : m.leadingMonomial r
            = monomial (m.degree r) (1 : R) := by
          simp [MonomialOrder.leadingMonomial, hr0]
        -- `r • monomial s 1 = monomial s r`
        simp [leadingMonomial,hr0, smul_eq_C_mul,C_mul_monomial]   -- 也可用 `monomial 0 r * monomial s 1 = monomial s r`
      -- 得到顶项落入理想，与上面的 `h_term_not_mem` 矛盾
      exact h_term_not_mem (by simpa [this] using hsmul)
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
    have h₄: m.leadingMonomial r ∈ Ideal.span (m.leadingMonomial '' ↑G) := by
      rw [←h_span]
      apply Ideal.subset_span
      apply Set.mem_image_of_mem
      exact h₂
    exact h₃ h₄


theorem isRemainder_zero_iff_mem_ideal_of_isGroebner {p : MvPolynomial σ R}
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (h : m.IsGroebnerBasis₂ G I) :
    m.IsRemainder p G 0 ↔ p ∈ I := by
  constructor
  · intro hr
    apply (m.remainder_eq_zero_iff_mem_ideal_of_isGroebner hG h hr).mp rfl
  · intro hp
    have hor: ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0 := by
      exact fun g a ↦ Or.symm (Or.inr (hG g a))
    have h₁:  ∃ (r : MvPolynomial σ R), m.IsRemainder p G r := by
      exact m.div_set'₀ hor p
    obtain ⟨r, hr⟩ := h₁
    have h₂: r = 0 := by
      exact (m.remainder_eq_zero_iff_mem_ideal_of_isGroebner hG h hr).mpr hp
    rw [h₂] at hr
    exact hr





/-- Gröbner basis of any ideal spans the ideal. -/
theorem ideal_eq_span_of_isGroebner {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) (h : m.IsGroebnerBasis₂ G I) :
    I = Ideal.span G := by
  apply le_antisymm
  · intro p hp
    rw [← m.isRemainder_zero_iff_mem_ideal_of_isGroebner hG h] at hp
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


theorem isGroebnerBasis_iff_span_eq_and_degree_le (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis₂ G I ↔
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
        rw [←hp'₁, leadingMonomial, SetLike.mem_coe,
          m.span_leadingMonomial_eq_span_monomial (by
          intro p_1 a
          subst hp'₁ hG'
          simp_all only [isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff, SetLike.mem_coe, not_false_eq_true]),
          ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
        intro j hj
        simp at hj
        simp
        subst hp'₁ hG'
        simp_all only [isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff, SetLike.mem_coe]
        split at hj
        next h =>
          subst h
          simp_all only [coeff_zero, not_true_eq_false]
        next h =>
          simp_all only [coeff_monomial, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]
          subst hj
          simp_all only [not_false_eq_true]
      · rw [hG']
        apply Ideal.span_mono
        exact Set.image_mono (hG' ▸ Submodule.subset_span)

/-- A set of polynomials is a Gröbner basis of an ideal if and only if it is a subset of this ideal
and 0 is a remainder of each member of this ideal on division by this set.

Any leading coefficient of polynomial in the set is required to be a unit. -/
theorem isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero
    (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R))
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis₂ G I ↔ G ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G 0 := by
  classical
  constructor
  · intro h
    exists h.1
    intro p h_p_in_I
    rwa [m.isRemainder_zero_iff_mem_ideal_of_isGroebner hG h]
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
      apply (m.mem_ideal_iff_of_isRemainder h1 h_remainder).mp
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
    (I : Ideal (MvPolynomial σ R)) :
    m.IsGroebnerBasis₂ G I ↔ G ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G 0 := by
  rw [← m.isGroebnerBasis_sdiff_singleton_zero₂]
  convert m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero (G \ {0}) I _ using 2
  · simp
  · simp [m.isRemainder_sdiff_singleton_zero_iff_isRemainder]
  ·
    intro g a
    simp_all only [isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff, Set.mem_diff, Set.mem_singleton_iff,
      not_false_eq_true]






set_option maxHeartbeats 0 in
/-- **S 对准则**。 -/
theorem Buchberger_Criterion
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    (∀ i j, m.reduceFamily b hb (m.sPolynomial (b i) (b j)) = 0) ↔  m.IsGroebnerBasis₂ (Set.range b) (Ideal.span (Set.range b)) := by
  classical
  constructor
  ·
    have h1:∀ i j,m.IsRemainder (m.sPolynomial (b i) (b j) : MvPolynomial σ R) (Set.range b) (m.reduceFamily b hb (m.sPolynomial (b i) (b j) : MvPolynomial σ R)):=by
      exact fun i j ↦ IsRemainder_reduceFamily m hb (m.sPolynomial (b i) (b j))
    intro hS
    set G:=(Set.range b)
    have hG :
        ∀ (g₁ g₂ : G),
          m.IsRemainder (m.sPolynomial (g₁ : MvPolynomial σ R) (g₂ : MvPolynomial σ R)) G 0 :=by
      intro g₁ g₂
      -- g₁,g₂ 都来自 `range b`，各自存在索引
      rcases g₁.property with ⟨i, a⟩
      rcases g₂.property with ⟨j, b⟩
      -- 现在目标就是 h i j
      simp_all only [G]
      obtain ⟨val, property⟩ := g₁
      obtain ⟨val_1, property_1⟩ := g₂
      subst a b
      simp_all only
    rw [isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero₀]
    exists Ideal.subset_span
    intro p hp
    simp_rw [isRemainder_def'', add_zero]
    refine ⟨?_, by simp⟩
    -- todo: Ideal.mem_span_iff_exists_finset_subset
    apply Submodule.mem_span_iff_exists_finset_subset.mp at hp
    obtain ⟨f, T, hT, ⟨hf', hf⟩⟩ := hp
    refine WellFoundedLT.induction
        (C := fun (a : m.syn) ↦
          (∃ (g : MvPolynomial σ R → MvPolynomial σ R) (G' : Finset (MvPolynomial σ R)),
            ↑G' ⊆ G ∧
            p = ∑ g' ∈ G', (g g') * g' ∧
            ∀ g' ∈ G', (m.toSyn <| m.degree <| g' * g g') ≤ a) →
          ∃ (g : MvPolynomial σ R → MvPolynomial σ R) (G' : Finset (MvPolynomial σ R)),
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
            rw [_root_.funext_iff]
            intro x
            by_cases h : gg'deg x = a <;> simp [h, leadingTerm]
        have a_gt_zero : 0 < a := bot_lt_of_lt ha
        obtain ⟨c, hc⟩ := by
          apply m.sPolynomial_decomposition' (ι:=MvPolynomial σ R) (d:=a) (B:=G')
            (fun g' ↦ monomial (m.degree (g g'))
              (if gg'deg g' = a then m.leadingCoeff (g g') else 0) * g')
          · intro g' hg'
            simp only [mul_eq_zero, monomial_eq_zero, ite_eq_right_iff, leadingCoeff_eq_zero_iff]
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
            ·
              subst hp
              simp_all only [implies_true, Subtype.forall, Set.mem_range,
                forall_exists_index, forall_apply_eq_imp_iff, ne_eq,
                Function.support_subset_iff, Finset.mem_coe, smul_eq_mul, ite_mul, zero_mul, degree_zero, map_zero,
                leadingCoeff_zero,  sub_self, ite_self, G, leadingTerm, gg'deg]
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
        simp_rw [hc, sPolynomial_mul_monomial] at hp
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
        let G'' : Finset (MvPolynomial σ R) :=
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
        simp at hp
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
        letI g₂ := (?_ : MvPolynomial σ R → MvPolynomial σ R)
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
            · simp [] at hq'0
              subst hf
              simp_all only [Function.support_subset_iff, ne_eq, SetLike.mem_coe, Subtype.forall, Set.mem_range,
                forall_exists_index, forall_apply_eq_imp_iff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach,
                Finsupp.mem_support_iff, true_and, Subtype.exists, Finsupp.coe_zero, Pi.zero_apply, mul_zero,
                degree_zero, map_zero, le_refl, forall_const, Decidable.not_not, smul_eq_mul, mul_ite, ↓reduceIte,
                zero_mul, G, gg'deg, G'']
            simp at hq'
            rw [mul_assoc]
            apply lt_of_le_of_lt degree_mul_le
            rw [AddEquiv.map_add]
            refine add_lt_of_add_lt_right ?_ (degree_monomial_le _)
            apply lt_of_le_of_lt (add_le_add_right (mul_comm g' (q' _ _ g') ▸ hq') _)
            apply lt_of_lt_of_le (add_lt_add_right (degree_sPolynomial_lt_sup_degree hspoly) _)
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
  ·
    classical
    intro hGB i j
    set s := m.sPolynomial (b i) (b j)
    set r := m.reduceFamily b hb s with hr
    -- 1) `s ∈ ⟨range b⟩`
    have hs : s ∈ Ideal.span (Set.range b) :=by
      classical
      dsimp [s, MonomialOrder.sPolynomial]
      refine Ideal.sub_mem (Ideal.span (Set.range b)) ?_ ?_
      · -- monomial(...) * (b i) ∈ span(range b)
        refine Ideal.mul_mem_left (Ideal.span (Set.range b)) _ ?_
        exact Ideal.subset_span ⟨i, rfl⟩
      · -- monomial(...) * (b j) ∈ span(range b)
        refine Ideal.mul_mem_left (Ideal.span (Set.range b)) _ ?_
        exact Ideal.subset_span ⟨j, rfl⟩
    -- 2) `s - r ∈ ⟨range b⟩` ⇒ `r ∈ ⟨range b⟩`
    have hsr : s - r ∈ Ideal.span (Set.range b) :=
      reduceFamily_sub_mem_span_range (m := m) (b := b) (hb := hb) (f := s)
    have hr_mem : r ∈ Ideal.span (Set.range b) := by
      -- r = s - (s - r)
      have : r = s - (s - r) := by ring
      rw[this]
      exact (Submodule.sub_mem_iff_left (Ideal.span (Set.range b)) hsr).mpr hs
    -- 3) 用 Groebner 基定义把 `initMonomial r` 拉进“首单项式理想”
    have hin : m.leadingMonomial r ∈ Ideal.span (m.leadingMonomial '' Set.range b) := by
      exact (IsGroebnerBasis.leadingMonomial_mem_span_image m (G := Set.range b) hGB hr_mem)
    -- 4) 若 r ≠ 0，则“单项式理想判定”推出 `∃ i, degree (b i) ≤ degree r`，即可头约化；矛盾
    -- 分情况：若 deg r = 0，则用“单项式理想成员 ⇒ 存在 k，使 degree(b k) ≤ 0” 推出矛盾
    by_cases hr0 : r = 0
    · simpa [hr, hr0]
    ·
      obtain ⟨k, hk⟩ :=
        (leadingMonomial_mem_span_image_iff_exists_le (m := m) (b := b) (hb := hb)
          (r := r) hr0).1 hin
      have hHR : HeadReducible m b r := ⟨hr0, ⟨k, hk⟩⟩
      have hNotHR : ¬ HeadReducible m b r :=
        reduceFamily_not_headReducible (m := m) (b := b) (hb := hb) (f := s)
      exact (hNotHR hHR).elim



end Field


end MonomialOrder
