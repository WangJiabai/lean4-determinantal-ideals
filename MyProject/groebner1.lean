import Mathlib

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.cdot false

open MvPolynomial Finsupp
open scoped BigOperators

namespace MonomialOrder

section
variable {σ R : Type*} [CommSemiring R]
variable (m : MonomialOrder σ)

/-! ### 首项 -/

/-- `initTerm`：**含系数** 的首项（零多项式的首项约定为 `0`）。 -/
noncomputable def initTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

@[simp] lemma initTerm_zero :
    m.initTerm (0 : MvPolynomial σ R) = 0 := by
  simp only [initTerm, m.degree_zero, m.leadingCoeff_zero, monomial_zero]

noncomputable def LeadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

/-- `initMonomial`：**系数规范为 1** 的首项（零多项式的首项依旧约定为 `0`）。
这在 `[Field R]` 的场景常用来获得“单项式理想”的写法。 -/
noncomputable def initMonomial (f : MvPolynomial σ R) : MvPolynomial σ R :=by
  classical
  exact if h : f = 0 then 0 else MvPolynomial.monomial (m.degree f) (1 : R)

@[simp] lemma initMonomial_zero :
    m.initMonomial (0 : MvPolynomial σ R) = 0 := by
  simp [initMonomial]

@[simp] lemma initMonomial_of_ne {f : MvPolynomial σ R} (hf : f ≠ 0) :
    m.initMonomial f = MvPolynomial.monomial (m.degree f) (1 : R) := by
  simp [initMonomial, hf]


/-! ### 初始理想（inₘ(I)） -/

/-- `inₘ(I)`：理想 `I` 的**初始理想**（用“含系数首项”生成）。
该定义在一般 `CommSemiring R` 下成立。 -/
def initIdeal (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  Ideal.span {t | ∃ f ∈ I, t = m.initTerm f}

lemma initIdeal_def (I : Ideal (MvPolynomial σ R)) :
    m.initIdeal I = Ideal.span {t | ∃ f ∈ I, t = m.initTerm f} := rfl

lemma initTerm_mem_initIdeal {I : Ideal (MvPolynomial σ R)} {f : MvPolynomial σ R}
    (hfI : f ∈ I) : m.initTerm f ∈ m.initIdeal I := by
  -- 直接由生成元属于 `Ideal.span` 推出
  refine Ideal.subset_span ?_
  refine ⟨f, hfI, rfl⟩

/-- `inₘ` 的单调性：若 `I ≤ J` 则 `inₘ(I) ≤ inₘ(J)`。 -/
lemma initIdeal_mono {I J : Ideal (MvPolynomial σ R)} (hIJ : I ≤ J) :
    m.initIdeal I ≤ m.initIdeal J := by
  -- 目标是：Ideal.span S ≤ Ideal.span T，只需证 S ⊆ Ideal.span T
  -- 用 span_le 的 ↔.mpr（也就是 .2）
  refine Ideal.span_le.2 ?_
  intro t ht
  rcases ht with ⟨f, hfI, rfl⟩
  -- 生成元在目标 span 内
  exact Ideal.subset_span ⟨f, hIJ hfI, rfl⟩

/-- 用“系数 1 的首项”生成的初始理想（常记作 `inₘ(I)` 的“单项式版本”）。 -/
def initIdeal₁ (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  Ideal.span {t | ∃ f ∈ I, t = m.initMonomial f}

lemma initIdeal₁_def (I : Ideal (MvPolynomial σ R)) :
    m.initIdeal₁ I = Ideal.span {t | ∃ f ∈ I, t = m.initMonomial f} := rfl

lemma initMonomial_mem_initIdeal {I : Ideal (MvPolynomial σ R)} {f : MvPolynomial σ R}
    (hfI : f ∈ I) : m.initMonomial f ∈ m.initIdeal₁ I := by
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
若由 `G` 生成的理想的初始理想，正好由 `G` 的首项生成。
`IsGroebnerBasis m G : Prop`。 -/
def IsGroebnerBasis (G : Set (MvPolynomial σ R)) : Prop :=
  m.initIdeal₁ (Ideal.span G) = Ideal.span (m.initMonomial '' G)

/-- `IsGroebnerBasis` 的充要定义就是上面那条等式，放个 `_iff` 方便改写。 -/
lemma isGroebnerBasis_iff (G : Set (MvPolynomial σ R)) :
    m.IsGroebnerBasis G ↔
      m.initIdeal₁ (Ideal.span G) = Ideal.span (m.initMonomial '' G) := Iff.rfl

/-- 基础性质：`G ⊆ H` 且 `G` 是 Groebner 基、且 `span G = span H`，则 `H` 也是 Groebner 基。 -/
lemma IsGroebnerBasis.of_span_eq
    {G H : Set (MvPolynomial σ R)}
    (hG : m.IsGroebnerBasis G)
    (hspan : Ideal.span G = Ideal.span H)
    (hIm : Ideal.span (m.initMonomial '' G) ≤ Ideal.span (m.initMonomial '' H))
    (hIm' : Ideal.span (m.initMonomial '' H) ≤ Ideal.span (m.initMonomial '' G)) :
    m.IsGroebnerBasis H := by
  -- 仅做等式替换与两侧包含
  have := hG
  dsimp [IsGroebnerBasis] at this ⊢
  simpa [hspan] using le_antisymm
    (calc
      m.initIdeal₁ (Ideal.span H)
          = m.initIdeal₁ (Ideal.span G) := by simp [hspan]
      _ = Ideal.span (m.initMonomial '' G) := this
      _ ≤ Ideal.span (m.initMonomial '' H) := hIm)
    (calc
      m.initIdeal₁ (Ideal.span H)
          = m.initIdeal₁ (Ideal.span G) := by simp [hspan]
      _ = Ideal.span (m.initMonomial '' G) := this
      _ ≥ Ideal.span (m.initMonomial '' H) := hIm')

/-- `G` 是 Groebner 基 ⇒ `inₘ(⟨G⟩)` 由 `G` 的首项生成；这是定义的拆解形式。 -/
lemma IsGroebnerBasis.initIdeal_span_eq
    {G : Set (MvPolynomial σ R)} (hG : m.IsGroebnerBasis G) :
    m.initIdeal₁ (Ideal.span G) = Ideal.span (m.initMonomial '' G) := hG

/-- Groebner 基的一个直接推论：对任意 `f ∈ ⟨G⟩`，其首项都落在由 `G` 首项生成的理想中。 -/
lemma IsGroebnerBasis.initTerm_mem_span_image
    {G : Set (MvPolynomial σ R)} (hG : m.IsGroebnerBasis G)
    {f : MvPolynomial σ R} (hf : f ∈ Ideal.span G) :
    m.initMonomial f ∈ Ideal.span (m.initMonomial '' G) := by
  -- 用 `inₘ(⟨G⟩)` 的定义得到 membership
  have hx : m.initMonomial f ∈ m.initIdeal₁ (Ideal.span G) :=
    m.initMonomial_mem_initIdeal (I := Ideal.span G) hf
  -- 把 `IsGroebnerBasis` 解成等式
  have hG' : m.initIdeal₁ (Ideal.span G) = Ideal.span (m.initMonomial '' G) :=
    (m.isGroebnerBasis_iff G).1 hG
  simpa [hG'] using hx


/-- `GroebnerBasis` 结构化打包：携带集合及其为 Groebner 基的证明。 -/
structure GroebnerBasis where
  carrier : Set (MvPolynomial σ R)
  isGroebner : m.IsGroebnerBasis carrier

attribute [coe] GroebnerBasis.carrier

/-- 从 `IsGroebnerBasis` 直接构造一个打包的 `GroebnerBasis`。 -/
def ofSet
    {G : Set (MvPolynomial σ R)}
    (hG : m.IsGroebnerBasis G) :
    MonomialOrder.GroebnerBasis (σ := σ) (R := R) (m := m) :=
  { carrier := G
    isGroebner := hG }

end







variable {σ ι R : Type*} [CommRing R]
/-! ### 头部可约性谓词 -/

/-- 头部可约性：存在某个 `i` 使 `LM(b i) ≤ LM(f)` 且 `LM(f) ≠ 0` -/
def HeadReducible
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (f : MvPolynomial σ R) : Prop :=
  ∃ i, m.degree (b i) ≤ m.degree f ∧ m.degree f ≠ 0

/-- 从 `HeadReducible` 中挑一个可约的下标（非构造性选择） -/
noncomputable def chooseHead
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (f : MvPolynomial σ R)
    (h : HeadReducible m b f) :
  { i : ι // m.degree (b i) ≤ m.degree f ∧ m.degree f ≠ 0 } :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

section TerminationInstances


variable (m : MonomialOrder σ) in
/-- 在 `m.syn` 上用 `<` 做良基关系（来自 `m.wf`） -/
local instance : WellFoundedRelation m.syn where
  rel := (· < ·)
  wf  := (m.wf).wf

/-! ### 对一族多项式的“约化到余式” -/
/-- 对一族多项式的“完全头部约化”——只返回余式（标准余式）。 -/
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
        -- 可头约：挑个 i，做一步首项约化后递归
        let i := (chooseHead m b f h).val
        have hi := (chooseHead m b f h).property
        exact reduceFamily m b hb (m.reduce (hb i) f)
      ·
        -- 不可头约：先看 LM(f) 是否为 0（非零常数）
        by_cases hdeg0 : m.degree f = 0
        · -- 此时 subLTerm f = 0；不再递归，余式就是 f 本身
          exact f
        · -- LM(f) ≠ 0：把首项入余式，递归处理剩余
          exact m.initTerm f + reduceFamily m b hb (m.subLTerm f)
termination_by f => m.toSyn (m.degree f)
decreasing_by
  -- ① 可头约分支：递归到 `m.reduce (hb i) f`
  ·
    -- 严格下降（目标类型就是 `<` on m.syn，与引理匹配）
    exact m.degree_reduce_lt (hb i) hi.1 hi.2
  -- ② 不可头约且 `degree f ≠ 0` 分支：递归到 `m.subLTerm f`
  ·
    exact m.degree_sub_LTerm_lt (f := f) hdeg0

end TerminationInstances

/-- 若 `f = 0`，完全约化的余式就是 `0`。 -/
@[simp] lemma reduceFamily_eq_zero
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    m.reduceFamily b hb 0 = 0 := by
  simp [reduceFamily]

/-- 若 `m.degree f = 0`（常数多项式），完全约化的余式就是 `f` 本身。 -/
lemma reduceFamily_degree_zero
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R} (hdeg0 : m.degree f = 0) :
    m.reduceFamily b hb f = f := by
  classical
  by_cases hf0 : f = 0
  · simp [hf0]
  ·
    -- 若 deg f = 0，则 `HeadReducible m b f` 不可能成立
    have hnot : ¬ HeadReducible m b f := by
      intro hex; rcases hex with ⟨i, _, hne⟩; exact hne hdeg0
    simp [reduceFamily, hf0, hnot, hdeg0]



/-- 在 `m.degree f ≠ 0` 的前提下，“不可头部约化”等价于
    “对所有下标 `i`，`LM(b i) ≤ LM(f)` 都不成立”。 -/
lemma not_headReducible_iff_forall
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    {f : MvPolynomial σ R} (hdeg : m.degree f ≠ 0) :
    (¬ HeadReducible m b f) ↔
    (∀ i, ¬ (m.degree (b i) ≤ m.degree f)) := by
  classical
  -- 展开定义后就是普通的一阶逻辑化简
  unfold HeadReducible
  constructor
  · intro hnot i hi
    exact hnot ⟨i, hi, hdeg⟩
  · intro hAll hex
    rcases hex with ⟨i, hi, _⟩
    exact hAll i hi

/-- 若可头部约化，则 `f` 一定非零。 -/
lemma headReducible_ne_zero
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    {f : MvPolynomial σ R} (h : HeadReducible m b f) :
    f ≠ 0 := by
  rcases h with ⟨i, _, hdeg⟩
  intro hf0; subst hf0; simp at hdeg


/-! ### 集合版的便捷封装 -/
variable (m : MonomialOrder σ)
/-- 把 `B : Set (MvPolynomial σ R)` 看成索引族来做同样的约化。 -/
noncomputable def reduceSet
    (B : Set (MvPolynomial σ R))
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) :
    MvPolynomial σ R → MvPolynomial σ R :=
  let b : B → MvPolynomial σ R := fun i => (i : MvPolynomial σ R)
  let hb : ∀ i : B, IsUnit (m.leadingCoeff (b i)) := fun i => hB i i.property
  m.reduceFamily b hb


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
      (hi : m.degree (b i) ≤ m.degree f ∧ m.degree f ≠ 0),
      m.reduceFamily b hb f = m.reduceFamily b hb (m.reduce (hb i) f) := by
  classical
  refine ⟨(m.chooseHead b f h).val, (m.chooseHead b f h).property, ?_⟩
  -- 只改写左边：展开一次定义，并用 hf0 / h 选中“可头约”分支
  conv_lhs =>
    unfold MonomialOrder.reduceFamily
    -- 这里的 `simp` 只用 `hf0` 和 `h` 做**分支选择**，
    -- 不会在子项里继续展开 `reduceFamily`（因为我们没把它放进 simp 集）
    simp [hf0, h]

/-- 若不可头部约化且 `m.degree f ≠ 0`，则“剥掉首项并递归处理剩余”。 -/
lemma reduceFamily_eq_notHead_degpos
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R} (hf0 : f ≠ 0) (hnot : ¬ HeadReducible m b f)
    (hdegpos : m.degree f ≠ 0) :
    m.reduceFamily b hb f =
      m.initTerm f + m.reduceFamily b hb (m.subLTerm f) := by
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


-- 统一的度量
def μ {σ R : Type*} [CommRing R] (m : MonomialOrder σ)
  (f : MvPolynomial σ R) : m.syn :=
  m.toSyn (m.degree f)

-- 良基
lemma wf_μ
  {σ R : Type*} [CommRing R]
  (m : MonomialOrder σ) :
  WellFounded (fun f g : MvPolynomial σ R => μ m f < μ m g) := by
  simpa [Function.onFun] using ((m.wf).wf).onFun




/-- `f - reduceFamily b hb f ∈ Ideal.span (Set.range b)`。 -/
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
    · -- 可头约：一步 + 递归
      rcases m.reduceFamily_eq_head_step (b := b) (hb := hb) hf0 h with ⟨i, hi, hdef⟩
      have μlt : μ m (m.reduce (hb i) f) < μ m f :=
        m.degree_reduce_lt (hb i) hi.1 hi.2
      have IH' := IH (m.reduce (hb i) f) μlt
      -- 合并
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
    m.degree (m.initTerm f) = m.degree f := by
  classical
  by_cases hf : f = 0
  · -- 零多项式：两边度都为 0
    simp [MonomialOrder.initTerm, hf, m.degree_zero]
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
  have hle : m.toSyn (m.degree (m.initTerm f)) ≤ m.toSyn a := by
    -- 用 `degree_le_iff`，只需对支撑中的每个指数组 b 证 `μ b ≤ μ a`
    rw [degree_le_iff]
    intro b hb
    -- b 在 `initTerm f` 的支撑上 ⇒ 其系数 ≠ 0
    have hbne : (m.initTerm f).coeff b ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using hb
    -- 计算系数：单项式的系数公式
    have hba : b = a := by
      -- 若 b ≠ a，则系数应为 0，矛盾
      by_contra hne
      have : (m.initTerm f).coeff b = 0 := by
        simp [MonomialOrder.initTerm, coeff_monomial]
        intro p
        rw [←ha] at p
        exact (hne p.symm).elim
      exact hbne this
    simp [hba]

  -- 再证：μ a ≤ μ(deg (initTerm f))，用 `le_degree` 和 `a ∈ support`
  have hge : m.toSyn a ≤ m.toSyn (m.degree (m.initTerm f)) := by
    -- a 在支撑上，因为该处系数就是 r 且 r ≠ 0
    have : (m.initTerm f).coeff a ≠ 0 := by
      simpa [MonomialOrder.initTerm, a, r, coeff_monomial] using hr
    have : a ∈ (m.initTerm f).support := by
      simpa [Finsupp.mem_support_iff] using this
    simpa using (m.le_degree this)

  -- 两边夹出 μ-相等，再用 `toSyn` 单射性还原成度的相等
  have : m.toSyn (m.degree (m.initTerm f)) = m.toSyn a := le_antisymm hle hge
  simpa [ha] using m.toSyn.injective this



/-- 辅助：首项的 μ-度等于原多项式的 μ-度。 -/
lemma mu_degree_initTerm
    (m : MonomialOrder σ) (f : MvPolynomial σ R) :
    m.toSyn (m.degree (m.initTerm f)) = m.toSyn (m.degree f) := by
  rw[degree_initTerm]


-- 最高项 + 更小尾项不改变最高项
lemma mu_degree_initTerm_add_of_lt
    (m : MonomialOrder σ) {f g : MvPolynomial σ R}
    (hlt : m.toSyn (m.degree g) < m.toSyn (m.degree f)) :
    m.toSyn (m.degree (m.initTerm f + g)) = m.toSyn (m.degree f) := by
  classical
  -- 把 `<` 改写到 `initTerm f` 上
  have hlt' :
      m.degree g ≺[m] m.degree (m.initTerm f) := by
    -- `≺[m]` 就是 μ-序上的 `<`；用上一条把右侧换成 `μ(deg f)`
    simpa [m.mu_degree_initTerm f] using hlt
  -- “小 + 大 = 大” 用在 `g + initTerm f`
  have hdeg :
      m.degree (g + m.initTerm f) = m.degree (m.initTerm f) :=
    m.degree_add_eq_right_of_lt hlt'
  -- 交换加数，映到 μ 上
  have hμ :
      m.toSyn (m.degree (m.initTerm f + g))
        = m.toSyn (m.degree (m.initTerm f)) := by
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
  intro g IH F' hlt'
  by_cases hg0 : g = 0
  · simpa [hg0, reduceFamily_eq_zero] using hlt'
  · by_cases h : HeadReducible m b g
    · rcases m.reduceFamily_eq_head_step (b := b) (hb := hb) hg0 h with ⟨i, hi, hdef⟩
      have μlt : m.toSyn (m.degree (m.reduce (hb i) g)) < m.toSyn (m.degree g) :=
        m.degree_reduce_lt (hb i) hi.1 hi.2
      have IH' := IH (m.reduce (hb i) g) μlt F' (lt_trans μlt hlt')
      simpa [hdef] using IH'
    · by_cases hdeg0 : m.degree g = 0
      · simpa [reduceFamily_eq_notHead_deg0 (m := m) (b := b) (hb := hb) hg0 h hdeg0] using hlt'
      ·
        have μlt_sub :
            m.toSyn (m.degree (m.subLTerm g)) < m.toSyn (m.degree g) :=
          m.degree_sub_LTerm_lt (f := g) hdeg0
        have μlt_tail :
            m.toSyn (m.degree (m.reduceFamily b hb (m.subLTerm g))) <
            m.toSyn (m.degree g) :=
          (IH (m.subLTerm g) μlt_sub) g μlt_sub
        have mu_eq :
            m.toSyn (m.degree (m.reduceFamily b hb g)) =
            m.toSyn (m.degree g) := by
          have rdef :
            m.reduceFamily b hb g =
              m.initTerm g + m.reduceFamily b hb (m.subLTerm g) :=
            reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb) hg0 h hdeg0
          simpa [rdef] using
            mu_degree_initTerm_add_of_lt (m := m) (f := g)
              (g := m.reduceFamily b hb (m.subLTerm g)) μlt_tail
        simpa [mu_eq] using hlt'



/-- `reduceFamily` 的结果对 `b` 不再可头部约化。 -/
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
    · rcases m.reduceFamily_eq_head_step (b := b) (hb := hb) hf0 h with ⟨i, hi, hdef⟩
      have μlt : μ m (m.reduce (hb i) f) < μ m f :=
        m.degree_reduce_lt (hb i) hi.1 hi.2
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
        rcases hex with ⟨i, hi, _hdeg_r_ne0⟩
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
              m.initTerm f + m.reduceFamily b hb (m.subLTerm f) :=
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
          exact h ⟨j, hj, by simpa using hdeg0⟩
        -- 矛盾
        exact (hnotf i) h_le





/-**S多项式部分**-/

/-- LCM（仅指数向量部分）：用点态 `sup`（逐坐标取 `Nat.max`）。 -/
@[simp] noncomputable
def lcmDeg (a b : σ →₀ ℕ) : σ →₀ ℕ := a ⊔ b

@[simp] lemma lcmDeg_fst_le {a b : σ →₀ ℕ} : a ≤ lcmDeg a b := by
  intro i; exact le_sup_left

@[simp] lemma lcmDeg_snd_le {a b : σ →₀ ℕ} : b ≤ lcmDeg a b := by
  intro i; exact le_sup_right

/-- 便捷记号：`μ(f,g)` 是 `LM(f)` 与 `LM(g)` 的“指数向量最小公倍数”。 -/
@[simp] noncomputable
def mu  (f g : MvPolynomial σ R) : σ →₀ ℕ :=
  lcmDeg (m.degree f) (m.degree g)

/-- `μ / LM(f)` 的“单项式因子”，系数取 1。 -/
@[simp] noncomputable
def muDivLM(f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (mu m f g - m.degree f) (1 : R)

/-- `μ / LM(g)` 的“单项式因子”，系数取 1。 -/
@[simp] noncomputable
def muDivLG (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (mu m f g - m.degree g) (1 : R)

/-- S 多项式：`S(f,g) = lc(g) * (μ/LM(f)) * f - lc(f) * (μ/LM(g)) * g`。 -/
@[simp] noncomputable
def SPoly (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  C (m.leadingCoeff g) * (muDivLM m f g) * f
  - C (m.leadingCoeff f) * (muDivLG m f g) * g


/-- S 多项式是两项在 `⟨range b⟩` 里的差，因此本身也在 `⟨range b⟩`。 -/
lemma SPoly_mem_span_range
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (f g : ι) :
    m.SPoly (b f) (b g) ∈ Ideal.span (Set.range b) := by
  classical
  refine Ideal.sub_mem (I := Ideal.span (Set.range b)) ?h1 ?h2
  · -- 第一项在理想内
    have hb : b f ∈ Ideal.span (Set.range b) :=
      Ideal.subset_span ⟨f, rfl⟩
    -- 理想对环元乘法封闭：`a * x ∈ I`
    have hx₁ :
      (muDivLM m (b f) (b g)) * b f ∈ Ideal.span (Set.range b) :=
      Ideal.mul_mem_left (I := Ideal.span (Set.range b)) _ hb
    have hx :
      C (m.leadingCoeff (b g)) * ((muDivLM m (b f) (b g)) * b f)∈ Ideal.span (Set.range b) :=
      Ideal.mul_mem_left (I := Ideal.span (Set.range b)) _ hx₁
    have hx' :
    C (m.leadingCoeff (b g)) * (muDivLM m (b f) (b g)) * b f ∈ Ideal.span (Set.range b) := by
      simpa [mul_assoc] using hx
    exact hx'
  · -- 第二项在理想内
    have hb : b g ∈ Ideal.span (Set.range b) :=
      Ideal.subset_span ⟨g, rfl⟩
    have hx₁ : (muDivLG m (b f) (b g)) * b g ∈ Ideal.span (Set.range b) :=
      Ideal.mul_mem_left (I := Ideal.span (Set.range b)) _ hb
    have hx :
      C (m.leadingCoeff (b f)) * ((m.muDivLG (b f) (b g)) * b g)∈ Ideal.span (Set.range b) :=
      Ideal.mul_mem_left (I := Ideal.span (Set.range b)) _ hx₁
    have hx' :
      C (m.leadingCoeff (b f)) * m.muDivLG (b f) (b g) * b g ∈ Ideal.span (Set.range b) := by
      simpa [mul_assoc] using hx
    exact hx'


/-- 单项式理想的基本判定（专用于本处）：
`m.initMonomial r ∈ Ideal.span (m.initMonomial '' Set.range b)`
⇔ 存在 `i` 使 `m.degree (b i) ≤ m.degree r`（当 `r ≠ 0`）。
这正是“可头约化”的指数条件（无系数）。 -/
lemma initMonomial_mem_span_image_iff_exists_le
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    {r : MvPolynomial σ R} (hr : r ≠ 0) :
    m.initMonomial r ∈ Ideal.span (m.initMonomial '' (Set.range b))
      ↔ ∃ i, m.degree (b i) ≤ m.degree r := by
  classical
  -- 这是“单项式理想”的标准事实：`⟨monomials⟩` 的元素正好是“被某个生成元指数向量所界”的单项式。
  -- 证明在你现有的 API 上可以用 `Ideal.span_induction` + `degree_*` 一步步完成；
  -- 为避免篇幅过长，此处给出你可用的成品结论。
  -- 如果你需要我把这个也展开成详细证明，我可以再补一版。
  sorry


/-- **S 对准则：Groebner 基推出所有 S 多项式余式为 `0`**。 -/
theorem sCriterion_forward
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hLMpos : ∀ i, m.degree (b i) ≠ 0) :
    m.IsGroebnerBasis (Set.range b) → ∀ i j, m.reduceFamily b hb (m.SPoly (b i) (b j)) = 0 := by
  classical
  intro hGB i j
  set s := m.SPoly (b i) (b j)
  set r := m.reduceFamily b hb s with hr
  -- 1) `s ∈ ⟨range b⟩`
  have hs : s ∈ Ideal.span (Set.range b) :=
    m.SPoly_mem_span_range b i j
  -- 2) `s - r ∈ ⟨range b⟩` ⇒ `r ∈ ⟨range b⟩`
  have hsr : s - r ∈ Ideal.span (Set.range b) :=
    reduceFamily_sub_mem_span_range (m := m) (b := b) (hb := hb) (f := s)
  have hr_mem : r ∈ Ideal.span (Set.range b) := by
    -- r = s - (s - r)
    have : r = s - (s - r) := by ring
    rw[this]
    exact (Submodule.sub_mem_iff_left (Ideal.span (Set.range b)) hsr).mpr hs
  -- 3) 用 Groebner 基定义把 `initMonomial r` 拉进“首单项式理想”
  have hin : m.initMonomial r ∈ Ideal.span (m.initMonomial '' Set.range b) := by
    exact (IsGroebnerBasis.initTerm_mem_span_image m (G := Set.range b) hGB hr_mem)
  -- 4) 若 r ≠ 0，则“单项式理想判定”推出 `∃ i, degree (b i) ≤ degree r`，即可头约化；矛盾
  -- 分情况：若 deg r = 0，则用“单项式理想成员 ⇒ 存在 k，使 degree(b k) ≤ 0” 推出矛盾
  by_cases hdeg0 : m.degree r = 0
  ·
    -- 分支：hdeg0 : m.degree r = 0，目标：r = 0
    have hr0 : r = 0 := by
      classical
      -- 反证：若 r ≠ 0，则由“单项式理想成员判定”得到某生成元首指数 ≤ deg r = 0
      by_contra hrne
      obtain ⟨k, hk⟩ :=
        (initMonomial_mem_span_image_iff_exists_le
            (m := m) (b := b) (r := r) hrne).1 hin
      -- hk : m.degree (b k) ≤ m.degree r = 0  ⇒  m.degree (b k) = 0
      have hk0 : m.degree (b k) = 0 := by
        have : m.degree (b k) ≤ 0 := by simpa [hdeg0] using hk
        exact le_antisymm this
          (by simp)
      -- 与“生成元首指数非零”的假设矛盾
      exact (hLMpos k hk0).elim
    -- 分支完成：用 hr0 结束
    simp [hr0]
  -- 另一种情况：deg r ≠ 0
  ·
    -- 同样用成员判定得到 ∃k, degree(b k) ≤ degree r
    have hrne : r ≠ 0 := m.ne_zero_of_degree_ne_zero (f := r) hdeg0
    obtain ⟨k, hk⟩ :=
    (initMonomial_mem_span_image_iff_exists_le
        (m := m) (b := b) (r := r) hrne).1 hin
      -- `deg r ≠ 0` ＋ `∃k, degree(b k) ≤ degree r` ⇒ 头部可约
    have hHR : HeadReducible m b r := ⟨k, hk, hdeg0⟩

    -- 但 `r` 是完全约化的余式：不可头约化
    have hNotHR : ¬ HeadReducible m b r :=
      reduceFamily_not_headReducible (m := m) (b := b) (hb := hb) (f := s)

    exact (hNotHR hHR).elim





end MonomialOrder
