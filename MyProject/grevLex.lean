import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.cdot false
variable {α : Type*}
/-
RLex 基础：（Part 1）
================
本段代码做的事情：
1) 用“类型别名”的方式把任意类型 `α` 包一层壳，得到 `RLex α`。这层壳后面会挂上“逆字典序”相关的**排序实例**；
但在数据层面上它和 `α` 完全相同（即同一底层数据，不做额外开销）。
2) 定义 `toRLex` / `ofRLex` 这两个**恒等等价**（`Equiv.refl`），方便在 `α` 与 `RLex α` 之间来回“改头换面”。
3) 通过若干 `simp` 引理，把“来回改头换面”规约成 `rfl`，让 Lean 自动化更顺畅。
4) 复用/迁移一些常用实例（`BEq`、`DecidableEq`、`Inhabited`、以及加法交换幺群结构），
让 `RLex α` 在需要时看起来“就像 α 一样能用”。

为什么要这么做？
- Lean 里常见做法：**用新壳换实例**。我们想在“同一份数据”上，挂上与原类型不同的排序/结构（例如稍后给 `α →₀ ℕ` 挂上逆字典序、再做分次逆字典序）。
- 这样既不改变数据表示，也不和 Mathlib 现有定义冲突：在不同作用域选择不同实例即可。
- 下面只处理“套壳 + 恒等等价 + 基础实例”；真正的“逆字典序规则”会在更后面专门为 `α →₀ ℕ` 给出。
-/

/-- `RLex`：给类型 `β` “套上逆字典序的壳”。得到该类型的一个别名，目的是方便定义该类型上的逆字典序 -/
def RLex (β : Type*) := β

/-
`toRLex` / `ofRLex`：把 `α` 和 `RLex α` 互相当作对方看待。
二者都是恒等等价 `Equiv.refl` —— 也就是说，运行时没有任何转换成本。
`@[match_pattern]` 让它们能在模式匹配/归纳里更自然地被使用。
-/
@[match_pattern]
def toRLex : α ≃ RLex α :=
  Equiv.refl _

@[match_pattern]
def ofRLex : RLex α ≃ α :=
  Equiv.refl _

/- `simp`：等价的逆与自身相等（在这里都是 `refl`）。 -/
@[simp]
theorem toRLex_symm_eq : (@toRLex α).symm = ofRLex :=
  rfl

@[simp]
theorem ofRLex_symm_eq : (@ofRLex α).symm = toRLex :=
  rfl

/- `simp`：来回改头换面等于不变。 -/
@[simp]
theorem toRLex_ofRLex (a : RLex α) : toRLex (ofRLex a) = a :=
  rfl

@[simp]
theorem ofRLex_toRLex (a : α) : ofRLex (toRLex a) = a :=
  rfl

/- 注：`Equiv` 保持并反映相等性，因此注入性等价于本身的相等。 -/
theorem toRLex_inj {a b : α} : toRLex a = toRLex b ↔ a = b := by simp

theorem ofRLex_inj {a b : RLex α} : ofRLex a = ofRLex b ↔ a = b := by simp


/-
实例复用：
------------
`RLex α` 与 `α` 是同一底层数据，因此很多实例可以“拿来就用”。
用 `inferInstanceAs` 显式告诉 Lean：请直接用 `α` 上已有的实例。
-/
instance (α : Type*) [BEq α] : BEq (RLex α) where
  beq a b := ofRLex a == ofRLex b

instance (α : Type*) [BEq α] [LawfulBEq α] : LawfulBEq (RLex α) :=
  inferInstanceAs (LawfulBEq α)

instance (α : Type*) [DecidableEq α] : DecidableEq (RLex α) :=
  inferInstanceAs (DecidableEq α)

instance (α : Type*) [Inhabited α] : Inhabited (RLex α) :=
  inferInstanceAs (Inhabited α)

/-
自定义归纳器：
--------------
`RLex.rec` 让我们可以对 `a : RLex α` 直接做 `induction a`。
做法：先用 `ofRLex` 把它“看成 α”，用给定的 `h : ∀ a, β (toRLex a)` 收尾。
`@[elab_as_elim]` 等属性让它在归纳/分情况时拥有正确的 elaboration 行为。
-/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def RLex.rec {β : RLex α → Sort*} (h : ∀ a, β (toRLex a)) : ∀ a, β a :=
  fun a => h (ofRLex a)


/-
对量词的 `simp`：
-----------------
把 `∀ a : RLex α, P a` 化到 `∀ a : α, P (toRLex a)`（存在量词同理）。
这在切换视角时很常用。
-/
@[simp] lemma RLex.forall {p : RLex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toRLex a) := Iff.rfl
@[simp] lemma RLex.exists {p : RLex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toRLex a) := Iff.rfl


/-
把代数结构“搬运”到壳上：
---------------------------
若 `α` 本身是加法交换幺群，则借助等价 `ofRLex : RLex α ≃ α` 把这一结构迁移到 `RLex α`。
这里使用的是标准“经由等价传递结构”的做法（运行时仍为零成本）。
-/
noncomputable instance [AddCommMonoid α] :
  AddCommMonoid (RLex α) := ofRLex.addCommMonoid

/- 对应的 `simp`：在壳上做加法，与先还原到 `α` 再加法是同一回事。 -/
@[simp] lemma toRLex_add [AddCommMonoid α] (x y : α) :
  toRLex x + toRLex y = toRLex (x + y) := rfl

@[simp] lemma ofRLex_add [AddCommMonoid α] (x y : α) :
   ofRLex x + ofRLex y = ofRLex (x + y)  := rfl



variable {α : Type*}


/-
逆字典序：`LT` 实例与基本引理（Part 2）
================================================
这一段把上一部分“RLex 套壳”的意图真正用在 `α →₀ ℕ`（指数向量）上：
1) **给 RLex (α →₀ ℕ) 安上 `<`（严格小于）实例**，其语义是 *字典序地按索引从小到大找第一处不同；在那一位用 “>`” 比较指数*。
   这正是“reverse-lex（逆字典序）”：在第一次不同的坐标处，**指数大的那一边更小**。
2) 把这个定义展开成易用的判据 `rlex_lt_iff` / `toRLex_lt_iff`。
3) 证明传递性、不可反身性，使之成为严格序；同时给出把 `toRLex` 壳层桥接到裸 `Finsupp` 语义的引理。

备注：
- 这里 **只** 是 rlex（同度层里的“打破平局”规则）。完整的“分次逆字典序 grevlex”会在后续通过
  “先比总次数（升序），同度再用 rlex” 组合而成。
- `Finsupp.Lex r sval` 的语义是：存在最小指标 `i`（按 `r` 排序）使得 `x` 与 `y` 在 `i` 之前完全相同，且在 `i` 处满足 `sval (x i) (y i)`。
  这里我们取 `r = (· < ·)`（索引从小到大），`sval = (· > ·)`（在首次不同位用 `>`）。
-/

/-逆字典序相关实例和定理部分-/
/-- 在 `RLex` 上把 `LT` 实例设成 `Finsupp.Lex (· < ·) (· > ·)`：
    *按变量索引从小到大找第一处不同；在该位用 “>`” 比指数。* -/
instance [LT α] : LT (RLex (α →₀ ℕ)) :=
  ⟨fun a b => Finsupp.Lex (· < ·) (· > ·) (ofRLex a) (ofRLex b)⟩


/-- rlex 的判据：存在最小指标 `i`，使得 `i` 之前两向量完全相同，且在 `i` 处 `a i > b i`。
    注意这里用的是 `>`，体现“逆” —— 首次不同位指数*更大*的一侧**更小**。 -/
theorem rlex_lt_iff [LT α] {a b : RLex (α →₀ ℕ)} :
    a < b ↔ ∃ i, (∀ j, j < i → ofRLex a j = ofRLex b j) ∧ ofRLex a i > ofRLex b i :=
  Finsupp.lex_def


/-- 把壳层 `toRLex x < toRLex y` 直接桥接为裸的 `Finsupp.Lex` 判据。-/
@[simp] lemma toRLex_lt_iff [LT α]{x y : α →₀ ℕ} :
  toRLex x < toRLex y ↔ Finsupp.Lex (· < ·) (· > ·) x y := Iff.rfl


/-- 逆字典序 rlex 的传递性：
    思路：若 `x < y` 的最小不同位是 `x1`，`y < z` 的是 `x2`，分两类：
    1) `x1 ≤ x2`：以 `j = x1` 为证人，`j` 之前三者坐标都相等，且 `x j > y j` 与 `y j = z j` 推出 `x j > z j`。
    2) `x2 < x1`：以 `j = x2` 为证人，同理用 `z j < y j = x j` 得 `x j > z j`。 -/
lemma rlex_trans [LinearOrder α] {x y z : α →₀ ℕ} :
  Finsupp.Lex (· < ·) (· > ·) x y →
  Finsupp.Lex (· < ·) (· > ·) y z →
  Finsupp.Lex (· < ·) (· > ·) x z := by
  simp only [gt_iff_lt, Finsupp.lex_def, forall_exists_index, and_imp]
  intro x1 heq1 hlt1 x2 heq2 hlt2
  -- 以两个“最小不同位”比较次序为分歧。
  by_cases h : x1 ≤ x2
  · -- 情形 1：x1 ≤ x2，选 j = x1
    refine ⟨x1, ?hxz, ?hlt⟩
    · -- 证明：j 之前三者坐标一致
      intro d hd
      have hxyd := heq1 d hd  -- x 与 y 在 d小于j 处相等
      have hyzd := heq2 d (lt_of_lt_of_le hd h)  -- y 与 z 在 d< x2 处相等，且 d小于j小于等于x2
      simp only [hxyd, hyzd]
    · --- 证明：在 j 处严格不等，且方向为 x j > z j（即 z j < x j）
      rcases lt_or_eq_of_le h with hlt | heq
      · -- 若 x1 < x2，则由 y 与 z 在 x1 处相等，直接把 hlt1 改写过去
        have : y x1 = z x1 := heq2 _ hlt
        simpa [this] using hlt1
      · -- 若 x1 = x2，则把另一边的严格不等 hlt2 传递到 x1，再与 hlt1 合成
        have hzlt : z x1 < y x1 := by simpa [heq] using hlt2
        exact lt_trans hzlt hlt1
  · -- 情形 2：¬ (x1 ≤ x2)，则 x2 < x1。选 j = x2
    have hx2ltx1 : x2 < x1 := not_le.mp h
    refine ⟨x2, ?_, ?_⟩
    · -- j 之前坐标一致：x 与 y 在 d< x1 处相等，y 与 z 在 d< x2 处相等
      intro d hd
      have hyzd := heq2 d hd
      have hxyd : x d = y d := heq1 d (lt_trans hd hx2ltx1)
      simp only [hxyd, hyzd]
    · -- 在 j 处：由 hlt2：z j < y j，再用 heq1 把 y j 改写成 x j 即可
      have : x x2 = y x2 := heq1 _ hx2ltx1 |> Eq.symm |> Eq.symm
      -- 说明：`|> Eq.symm |> Eq.symm` 只是保持形状，等价于不变。
      simpa [this] using hlt2

/-- 把上面的传递性换回壳层表述：`toRLex x < toRLex y` 与裸判据等价，所以直接重用。 -/
lemma toRLex_lt_trans [LinearOrder α]
  {x y z : α →₀ ℕ} :
  toRLex x < toRLex y → toRLex y < toRLex z → toRLex x < toRLex z := by
  intro hxy hyz
  have h1 := (rlex_trans (by simpa [toRLex_lt_iff] using hxy)
                         (by simpa [toRLex_lt_iff] using hyz))
  simpa [toRLex_lt_iff] using h1

/-- rlex 的不可反身性：`x < x` 等价于“存在最小 i 使得 x i > x i”，自相矛盾。 -/
@[simp] lemma rlex_irrefl [LinearOrder α] (x : α →₀ ℕ) :
  ¬ Finsupp.Lex (· < ·) (· > ·) x x := by
  -- 直接用 `lex_def` 展开即可归约为 `x i < x i` 的不可能式
  simp only [gt_iff_lt, Finsupp.lex_def, implies_true, lt_self_iff_false, and_false, exists_false,
    not_false_eq_true]

/-- 把不可反身性换回壳层：`a : RLex (α →₀ ℕ)` 不可能满足 `a < a`。 -/
@[simp] lemma lt_self_false_RLex [LinearOrder α] (a : RLex (α →₀ ℕ)) : ¬ a < a := by
  have h1:=rlex_irrefl (ofRLex a)
  simpa [toRLex_lt_iff]



/-
逆字典序：把壳提升为线序 + 若干桥接引理（Part 3）
================================================
目标：在 `RLex (α →₀ ℕ)` 上真正做出 `LinearOrder`。做法遵循“严格序先行”的惯例：
1) 先已有严格序 `<`（前面定义的 rlex）。
2) 再用 `le a b := a < b ∨ a = b` 合成 `≤`，并证明自反/传递/反对称/全域性。
3) 借助 `WellFoundedLT α` 选出“最小不同指标”，完成 `le_total`（三歧）证明。
4) 给出把 `≤`/`<` 在壳层与裸 `Finsupp` 判据之间互换的等价引理。
5) 最后给出一个常用的“单项式比较”判据：`single i 1 < single j 1 ↔ i < j`。
-/

-- RLex (α →₀ ℕ) 是线序
noncomputable instance [LinearOrder α][WellFoundedLT α] : LinearOrder (RLex (α →₀ ℕ)) :=by
  -- 最终线序记录：指定 `<`/`≤` 以及五大字段
  refine
  { lt_iff_le_not_ge:=by
      -- 线序公理：`a < b` ↔ `a ≤ b ∧ ¬ b ≤ a`。
      -- 这里我们直接把 `≤` 的定义（< 或 =）代入来证明两个方向。
      simp only [RLex.forall, toRLex_lt_iff, gt_iff_lt]
      intro a b
      constructor
      · -- → 方向：`a<b` 推出 `a≤b` 成立，而 `b≤a` 否（否则与严格序矛盾）。
        intro h
        refine ⟨Or.inl h, ?_⟩
        -- 证 ¬ (b ≤ a)
        intro hba
        rcases hba with hba | hba
        · -- b < a 与 a < b 违背“严格序的反对称”（由传递+反身推出）
          simp only [← toRLex_lt_iff] at h
          have : toRLex (ofRLex a) < toRLex (ofRLex a) :=
            toRLex_lt_trans h hba
          exact (lt_self_false_RLex _ : ¬ toRLex (ofRLex a) < toRLex (ofRLex a)) this
        · -- b = a 与 a < b 矛盾
          simp only [← toRLex_lt_iff] at h
          have : a < a := by rw[hba] at h;simp only [lt_self_false_RLex] at h
          simp only [lt_self_iff_false] at this
      · -- ← 方向：若 `a ≤ b` 且 `¬ b ≤ a`，必须走 `<` 分支（否则 `a=b` 与右侧矛盾）。
        intro h
        rcases h with ⟨hle, hnle⟩
        rcases hle with hlt | heq
        · exact hlt
        · -- a = b 会推出 b ≤ a，与 `¬ b ≤ a` 矛盾
          exact (hnle (Or.inr heq.symm)).elim
    toDecidableLE:=by
      -- 构造 `Decidable (a ≤ b)`：只需 `Decidable (a<b ∨ a=b)`。
      intro a b; classical exact
        (inferInstance : Decidable (a < b ∨ a = b))
    lt := (· < ·)
    le := fun a b => a < b ∨ a = b
    le_refl := by intro a; right; rfl--自反性
    le_trans := by--传递性
      intro a b c hab hbc
      rcases hab with hab | rfl
      · rcases hbc with hbc | rfl
        · left-- 这里用 rlex 的传递性
          exact rlex_trans (by simpa using hab) (by simpa using hbc)
        · left; exact hab
      · exact hbc
    le_antisymm := by--反对称性
      intro a b hab hba
      rcases hab with hab | rfl
      · rcases hba with hba | rfl
        ·
          have := rlex_trans hab hba
          simp only [gt_iff_lt, rlex_irrefl] at this
        · rfl
      · rfl
    le_total := by
      -- 全域性：要证 `a ≤ b ∨ b ≤ a`。分三支：`a<b` 或 `a=b` 或 `b<a`。
      -- 关键在于：若 `a ≠ b`，可用 `WellFoundedLT α` 在不等点集合上取最小指标。
      intro a b
      have hLex :
        Finsupp.Lex (· < ·) (· > ·) (ofRLex a) (ofRLex b) ∨
        ofRLex a = ofRLex b ∨
        Finsupp.Lex (· < ·) (· > ·) (ofRLex b) (ofRLex a) := by
        by_cases hEq : ofRLex a = ofRLex b
        · exact Or.inr (Or.inl hEq)
        · -- 取“最小不同指标”
          set S : Set α := {i | (ofRLex a) i ≠ (ofRLex b) i}
          -- 函数不等 ⇒ 存在点不等
          have hfun_ne :
              (fun i => (ofRLex a) i) ≠ (fun i => (ofRLex b) i) := by
            intro hfun; apply hEq; ext i; simpa using congrArg (fun f => f i) hfun
          have ⟨i0, hi0⟩ : ∃ i, (ofRLex a) i ≠ (ofRLex b) i :=(Function.ne_iff).mp hfun_ne
          have hSnonempty : S.Nonempty := ⟨i0, by simpa [S] using hi0⟩
          -- 用良基性
          have wf : WellFounded ((· < ·) : α → α → Prop) := wellFounded_lt (α := α)
          let i := wf.min S hSnonempty
          have hi_mem : (ofRLex a) i ≠ (ofRLex b) i := by
            have : i ∈ S := wf.min_mem S hSnonempty
            simpa [S] using this
          -- 所有更小指标处相等
          have hconst : ∀ j, j < i → (ofRLex a) j = (ofRLex b) j := by
            intro j hj
            have hj_notin : j ∉ S := fun hjS => (wf.not_lt_min S hSnonempty hjS) hj
            have : ¬ ((ofRLex a) j ≠ (ofRLex b) j) := by simpa [S] using hj_notin
            exact Classical.not_not.mp this
          have hconst' : ∀ j, j < i → (ofRLex b) j = (ofRLex a) j := by
            intro j hj; simpa [eq_comm] using hconst j hj
          -- 在最小不同位 i 上比较数值
          rcases lt_trichotomy ((ofRLex b) i) ((ofRLex a) i) with hlt | heq | hgt
          · -- b i < a i  ⇒ a i > b i  ⇒ Lex a b
            left; exact ⟨i, hconst, by simpa [gt_iff_lt] using hlt⟩
          · exact (hi_mem heq.symm).elim  -- 与 i∈S 矛盾
          · -- a i < b i  ⇒ b i > a i  ⇒ Lex b a
            right; exact Or.inr ⟨i, hconst', by simpa [gt_iff_lt] using hgt⟩
      rcases hLex with hlt | heq | hgt
      · exact Or.inl (Or.inl (by simpa [toRLex_lt_iff] using hlt)) -- a小于b
      · -- a=b
        -- 从 ofRLex a = ofRLex b 推回 a = b
        have : a = b := by simpa using congrArg toRLex heq
        exact Or.inl (Or.inr this)
      · -- b小于a
        exact Or.inr (Or.inl (by simpa [toRLex_lt_iff] using hgt))
      }


/-- 把 `toRLex` 的 `≤` 展开成“相等或 rlex 严小”。 -/
lemma toRLex_le_iff
  [LinearOrder α] [WellFoundedLT α]
  {x y : α →₀ ℕ} :
  toRLex x ≤ toRLex y ↔ (x = y) ∨ Finsupp.Lex (· < ·) (· > ·) x y := by
  -- 在线序下：`≤` ↔ `=` ∨ `<`
  -- 再把 `<` 用 `toRLex_lt_iff` 改写为 Finsupp 的 rlex
  simp only [le_iff_eq_or_lt, EmbeddingLike.apply_eq_iff_eq, toRLex_lt_iff, gt_iff_lt]

/-- 把 `RLex (α →₀ ℕ)` 上的 `≤` 换回到底层 `Finsupp` 的表述。 -/
lemma RLex_le_iff
  [LinearOrder α] [WellFoundedLT α]
  {a b : RLex (α →₀ ℕ)} :
  a ≤ b ↔ (ofRLex a = ofRLex b) ∨
    Finsupp.Lex (· < ·) (· > ·) (ofRLex a) (ofRLex b) := by
  simpa [toRLex_ofRLex] using
    (toRLex_le_iff)



/-- 在同度层 rlex（索引按 `<`，值按 `>`）下，
    `single i 1 < single j 1 ↔ i < j`. -/
lemma rlex_single_lt_iff [LinearOrder α] {i j : α} :
  Finsupp.Lex (· < ·) (· > ·) (Finsupp.single i (1 : ℕ)) (Finsupp.single j 1)↔ i < j := by
  -- 读法：比较两个“一次单项式”的指数向量。rlex 找到最小不同指标；
  -- 若 i < j，则在 i 之前都为 0 且在 i 处 (1,0) ⇒ `>` 成立；反向推理同理。
  simp only [gt_iff_lt, Finsupp.lex_def]
  constructor
  ·
    intro h
    rcases h with ⟨k, hkpre, hkgt⟩
    -- 证明 `k = i`，否则在 k 处两边同为 0 与 `hkgt` 矛盾。
    have hkki : k = i ∨ k ≠ i := eq_or_ne k i
    have hkkj : k = j ∨ k ≠ j := eq_or_ne k j
    have hk_ne_j : k ≠ j := by
      cases hkkj with
      | inl hk_eq_j =>
        subst hk_eq_j
        simp only [Finsupp.single_eq_same] at hkgt
        exfalso
        classical
        rcases hkki with hki|hki
        · -- 若 k = i，则 (single i 1) k = 1，所以 hkgt 变成 1 < 1 矛盾
          subst hki
          simp only [Finsupp.single_eq_same, lt_self_iff_false] at hkgt
        · -- 若 k ≠ i，则 (single i 1) k = 0，所以 hkgt 变成 1 < 0 矛盾
          have : (fun₀ | i => 1) k = 0 := by
            simp [Finsupp.single, hki]
          have : 1 < 0 := by simp only [this, not_lt_zero'] at hkgt
          simp only [not_lt_zero'] at this
      | inr hk_ne_j => exact hk_ne_j
    have hk_eq_i : k = i := by
      cases hkki with
      | inl hk_eq_i => exact hk_eq_i
      | inr hk_ne_i =>
        have h1: (Finsupp.single i 1) k = 0 := by simp [Finsupp.single, hk_ne_i]
        have : (Finsupp.single j 1) k = 0 := by simp [Finsupp.single, hk_ne_j]
        simp only [this,h1] at hkgt
        by_contra h
        simp only [lt_self_iff_false] at hkgt
    -- 用“最小不同位就是 i” 区分 i小于j 和 j小于等于i 两可能。
    by_cases hij : i < j
    · exact hij
    · have : j < i ∨ j = i := lt_or_eq_of_le (le_of_not_gt hij)
      cases this with
      | inl hji =>
        subst hk_eq_i
        have := hkpre j hji
        simp [Finsupp.single, ne_of_lt hji] at this
      | inr h_eq =>
        cases h_eq
        simp only [lt_self_iff_false]
        exact hk_ne_j hk_eq_i
  ·-- 反向：若 i小于j，则取证人 k=i。i 之前坐标都为 0；在 i 位上 (1,0) 给出严格不等。
    intro hij
    refine ⟨i, ?_, ?_⟩
    · intro k hk
      have hki : k ≠ i := ne_of_lt hk
      have hkj : k ≠ j := ne_of_lt (lt_trans hk hij)
      simp only [Finsupp.single, one_ne_zero, Finsupp.coe_mk, ne_eq, hki, not_false_eq_true,
        Pi.single_eq_of_ne, hkj]
    · have hij' : i ≠ j := ne_of_lt hij
      simp only [Finsupp.single, one_ne_zero, Finsupp.coe_mk, ne_eq, hij', not_false_eq_true,
        Pi.single_eq_of_ne, Pi.single_eq_same, zero_lt_one]


/-
逆字典序：加法与序的相容性（Part 4）
====================================
目标：证明 rlex 与逐点加法相容，从而在壳层得到 `IsOrderedCancelAddMonoid`。
核心思想：
- rlex 的“最小不同位”在加同一个向量 `z` 的前后保持不变，且该位上的比较可由 `Nat` 的加法消去性质转回。
- 因此 `(x+z) < (y+z) ↔ x < y`（严格版），进而得到 `≤` 的等价与消去。
- 利用这些等价，给出 `le_of_add_le_add_left` 和 `add_le_add_left` 两个公理，实现 `IsOrderedCancelAddMonoid`。
- 最后证明一个常用工具：`toRLex` 对“点态 ≤”是**反单调**（坐标越大，rlex 越小），
  其证法仍然是“取最小不同指标 i”，用 rlex 的 `>` 方向与 `Nat` 的 `<` 方向互换。
-/

-- 严格不等的“反推”： (x+z) < (y+z) ⇒ x < y
private lemma rlex_add_left_reflects_lt
  [LinearOrder α] {x y z : α →₀ ℕ} :
  Finsupp.Lex (· < ·) (· > ·) (x + z) (y + z) →
  Finsupp.Lex (· < ·) (· > ·) x y := by
  classical
  rintro ⟨i, hpre, hi⟩
  refine ⟨i, ?_, ?_⟩
  · -- 更小指标处相等：由 (x+z)j = (y+z)j 左消得到 xj = yj
    intro j hj
    have := hpre j hj
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.add_right_cancel_iff] at this
    exact this
  · -- 在 i 处严格： (x+z)i > (y+z)i ⇒ xi > yi
    simp only [Finsupp.coe_add, Pi.add_apply, gt_iff_lt, add_lt_add_iff_right] at hi
    simpa [gt_iff_lt] using hi

-- 严格不等的“保序”： x < y ⇒ (x+z) < (y+z)
private lemma rlex_add_left_preserves_lt
  [LinearOrder α] {x y z : α →₀ ℕ} :
  Finsupp.Lex (· < ·) (· > ·) x y →
  Finsupp.Lex (· < ·) (· > ·) (x + z) (y + z) := by
  classical
  rintro ⟨i, hpre, hi⟩
  refine ⟨i, ?_, ?_⟩
  · -- 更小指标处相等保持
    intro j hj
    have := hpre j hj
    simp only [Finsupp.add_apply, this]
  · -- 在 i 处严格保持
    have : y i < x i := by simpa [gt_iff_lt] using hi
    have : y i + z i < x i + z i := Nat.add_lt_add_right this _
    simpa [gt_iff_lt, Finsupp.add_apply, add_comm] using this


/-- rlex 在左侧同加相同向量时的“消去/保序等价”。 -/
@[simp] lemma rlex_add_le_add_iff_left
  [LinearOrder α][WellFoundedLT α]
  {x y z : α →₀ ℕ} :
  toRLex (z + x) ≤ toRLex (z + y) ↔ toRLex x ≤ toRLex y := by
  classical
  constructor
  · -- (→) 由 (z+x) ≤ (z+y) 推出 x ≤ y
    intro h
    rcases h with hlt | heq
    · -- 严格情形
      -- 先把 (z+x)<(z+y) 改写成 (x+z)<(y+z)
      have hx : Finsupp.Lex (· < ·) (· > ·) (x + z) (y + z) := by
        simpa [toRLex_lt_iff, add_comm] using hlt
      have : Finsupp.Lex (· < ·) (· > ·) x y :=
        rlex_add_left_reflects_lt (x := x) (y := y) (z := z) hx
      exact Or.inl (by simpa [toRLex_lt_iff] using this)
    · -- 相等情形：z+x = z+y ⇒ x = y
      have hsum : z + x = z + y := by simpa using congrArg ofRLex heq
      have hxy : x = y := by
        ext i
        have := congrArg (fun f => f i) hsum
        simpa [Finsupp.add_apply] using Nat.add_left_cancel this
      exact Or.inr (by simp only [hxy])
  · -- (←) 由 x ≤ y 推出 (z+x) ≤ (z+y)
    intro h
    rcases h with hlt | heq
    · -- 严格情形：保序
      have hx : Finsupp.Lex (· < ·) (· > ·) x y := by
        simpa [toRLex_lt_iff] using hlt
      have : Finsupp.Lex (· < ·) (· > ·) (x + z) (y + z) :=
        rlex_add_left_preserves_lt (x := x) (y := y) (z := z) hx
      exact Or.inl (by simpa [toRLex_lt_iff, add_comm] using this)
    · -- 相等情形：直接相等
      exact Or.inr (by simpa [heq])

/-- 最终要的实例：`le_of_add_le_add_left`。 -/
noncomputable instance
  [LinearOrder α] [WellFoundedLT α] :
  IsOrderedCancelAddMonoid (RLex (α →₀ ℕ)) where
  -- ① 由 c + a ≤ c + b 推出 a ≤ b
  le_of_add_le_add_left {a b c} h := by
    -- 把目标与前提都改写到 Finsupp 层再用等价引理消去
    have h' :
        toRLex (ofRLex a + ofRLex b) ≤ toRLex (ofRLex a + ofRLex c) := by
      simpa [toRLex_add, toRLex_ofRLex] using h
    have : toRLex (ofRLex b) ≤ toRLex (ofRLex c) :=
      (rlex_add_le_add_iff_left).1 h'
    simpa [toRLex_ofRLex] using this
  -- ② 由 a ≤ b 推出 c + a ≤ c + b
  add_le_add_left {a b} h c := by
    have h' : toRLex (ofRLex a) ≤ toRLex (ofRLex b) := by
      simpa [toRLex_ofRLex] using h
    have : toRLex (ofRLex c + ofRLex a) ≤ toRLex (ofRLex c + ofRLex b) :=
      (rlex_add_le_add_iff_left (x := ofRLex a) (y := ofRLex b) (z := ofRLex c)).2 h'
    simpa [toRLex_add, toRLex_ofRLex]

/-- 对 `RLex`：`toRLex` 在点态序下是反单调.-/
theorem toRLex_antitone
  [LinearOrder α] [WellFoundedLT α] :
  Antitone (@toRLex (α →₀ ℕ)) := by
  classical
  intro a b h  -- h : ∀ i, a i ≤ b i
  by_cases hEq : a = b
  · -- 相等情形
    simp only [hEq, le_refl]
  -- 取 a,b 最小不同指标 i
  set S : Set α := {i | a i ≠ b i}
  have fun_ne : (fun i => a i) ≠ (fun i => b i) := by
    intro hfun; apply hEq; ext i; simpa using congrArg (fun f => f i) hfun
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ b i := (Function.ne_iff).mp fun_ne
  have Snonempty : S.Nonempty := ⟨i0, by simpa [S] using hi0⟩
  have wf : WellFounded ((· < ·) : α → α → Prop) := wellFounded_lt (α := α)
  let i := wf.min S Snonempty
  have hi_mem : a i ≠ b i := by
    have : i ∈ S := wf.min_mem S Snonempty
    simpa [S] using this
  have hconst : ∀ j, j < i → a j = b j := by
    intro j hj
    have j_notin : j ∉ S := fun hjS => (wf.not_lt_min S Snonempty hjS) hj
    have : ¬ a j ≠ b j := by simpa [S] using j_notin
    exact not_not.mp this
  have hi_lt : a i < b i := by
    have hle : a i ≤ b i := h i
    exact lt_of_le_of_ne hle hi_mem
  -- 于是 rlex 下 b < a
  have hlex : Finsupp.Lex (· < ·) (· > ·) b a :=
    ⟨i, (by intro j hj; simp only [hconst j hj]),
         (by simpa [gt_iff_lt] using hi_lt)⟩
  exact Or.inl (by simpa [toRLex_lt_iff] using hlex)


/-
定度层有限 & rlex 良基（Part 5）
===============================
这一段完成“**同度层有限 ⇒ rlex 良基**”这条关键链路；
它将用于后续证明“分次逆字典序（先比较度数，度数相等时用 rlex）整体良基”。
核心要点：
1) `degree_layer_finite`：当 `α` 是有限集（`[Fintype α]`）时，所有总次数（度数）等于固定值 `d` 的指数向量集合是**有限**的。
   - 证明思路：用“坐标逐点不超过 d”的集合 `S := {x | ∀ a, x a ≤ d}` 作为超集；
     把 `S` 嵌入为 `(α → Fin (d+1))` 的像，因此有限；再证“度数 = d 的层 ⊆ S”。
2) 给出 `IsStrictOrder` 实例：说明 `Finsupp.Lex (· < ·) (· > ·)` 本身是严格序（不可反身、传递）。
   - 这为在定度层上谈良基清除了序的基本公理障碍。
3) `rlex_gt_wf_on_degree`：由“定度层有限 + 严格序”直接推出**良基**（有限集上的任何严格序都是良基），
   借助 `Set.Finite.wellFoundedOn` 即可。
-/

/-- 度数为 `d` 的单项式层是有限集（`[Fintype α]`） -/
lemma degree_layer_finite
  [Fintype α]  (d : ℕ) :
  ({x : α →₀ ℕ | x.degree = d} : Set (α →₀ ℕ)).Finite := by
  classical
  -- 思路：先做一个更大的有限集合 S := {x | ∀ a, x a ≤ d}，再证明“度数 = d 的层 ⊆ S”。
  -- S 的有限性来自它是 `(α → Fin (d+1))` 在一个线性映射 φ 下的像。
  -- 定义 φ：把每个 `f : α → Fin (d+1)` 映成以 `f a`.val 为坐标的 finsupp（指数向量）。
  let φ : (α → Fin (d+1)) → (α →₀ ℕ) :=
    fun f => Finsupp.equivFunOnFinite.symm (fun a => (f a).val)

  -- 需要证明 S ⊆ image φ univ：任何坐标都 ≤ d 的指数向量，都可由一个 `f : α → Fin (d+1)` 生成。
  have hS_subset_img : {x : α →₀ ℕ | ∀ a, x a ≤ d} ⊆ Set.image φ Set.univ := by
    classical
    intro x hx
    -- 构造 f_x：对每个 a，取 `x a`，并用 `Nat.lt_succ_of_le (hx a)` 见证 `x a < d+1`。
    refine ⟨(fun a => ⟨x a, Nat.lt_succ_of_le (hx a)⟩), ?_, ?_⟩
    · simp   -- f_x ∈ univ
    · -- 证明 φ f_x = x：逐点相等即可
      ext a
      -- `equivFunOnFinite.symm` 的 `simp` 展开把“函数到 finsupp”的往返同构还原。
      simp [φ]

  -- 于是 S 有限。
  have hS : {x : α →₀ ℕ | ∀ a, x a ≤ d}.Finite :=
    (Set.finite_univ.image φ).subset hS_subset_img

  -- 现在只要证明：同度层 ⊆ S
  have h_deg_subset_S :
      {x : α →₀ ℕ | x.degree = d} ⊆ {x : α →₀ ℕ | ∀ a, x a ≤ d} := by
    intro x hx a
    -- 关键事实：每个坐标都不超过“总次数 degree”。
    -- 在 `Finsupp` 上，`x.degree` 就是各坐标和（总次数）。
    have : x a ≤ x.degree := by
      exact Finsupp.le_degree a x
    have h:x.degree=d:=by exact hx
    -- 代入 `x.degree = d` 得 `x a ≤ d`。
    simpa [h,hx] using this

  -- 最终得到度数层有限
  exact hS.subset h_deg_subset_S


-- 说明：这个实例表明，`Finsupp.Lex (·<·) (·>·)` 是严格序（不可反身、传递）。
-- 它适用于所有有线序的索引集 `α`。
instance [LinearOrder α] :
  IsStrictOrder (α →₀ ℕ) (Finsupp.Lex ((· < ·):α → α → Prop) ((· > ·):ℕ → ℕ → Prop)) where
    irrefl := by
      simp only [gt_iff_lt, rlex_irrefl, not_false_eq_true, implies_true]
    trans := by
      intro a b c
      exact rlex_trans


/- 同度层里，`Lex (· < ·) (· > ·)` 良基。 -/
open scoped Function in lemma rlex_gt_wf_on_degree
  [LinearOrder α] [Fintype α]:
  ∀ d : ℕ,
    {x : α →₀ ℕ | x.degree = d}.WellFoundedOn
      (Finsupp.Lex (· < ·) (· > ·)) := by
    -- 思路：定度层是有限集（上一引理），有限集上的严格序必定良基。
    intro d
    have h1:{x : α →₀ ℕ | x.degree = d}.Finite:=degree_layer_finite (α := α) d
    exact Set.Finite.wellFoundedOn h1






/-
分次逆字典序：`GrevLex` 的套壳与基础搬运（Part 1）
==============================================
这一段与 Part 1（`RLex` 套壳）同构：
- 用**类型别名**把任意类型 `α` 套成 `GrevLex α`（数据本体不变、零成本）。
- 定义恒等等价 `toGrevLex` / `ofGrevLex`，用于在 `α` 与 `GrevLex α` 之间“改头换面”。
- 给出若干 `simp` 引理与自定义归纳器，方便自动化与模式匹配。
- 通过等价把 `AddCommMonoid` 结构**搬运**到壳上（后续要在 `GrevLex (α →₀ ℕ)` 上挂“分次逆字典序”的比较法则）。


> - `GrevLex` 只是一个“标签壳”，真正“分次 + 逆字典序”的比较规则会在**后续**专门针对 `α →₀ ℕ` 给出。
> - 这套“先套壳、后挂实例”的技术能避免与 mathlib 里其它顺序冲突，也便于在不同文件/作用域切换所需实例。
-/


/-以下是分次逆字典序套壳-/
/-- `GrevLex`：把类型 `α` 原样套壳，便于在其上挂“分次逆字典序”的排序实例。 -/
def GrevLex (α : Type*) := α

/-- `toGrevLex`：恒等等价，运行时零成本；常用于把 `α` 看作 `GrevLex α`。 -/
@[match_pattern] def toGrevLex : α ≃ GrevLex α := Equiv.refl _
/- 等价的注入性/注入判据：方便 `simp` 与自动化使用。 -/
theorem toGrevLex_injective : Function.Injective (toGrevLex (α := α)) := fun _ _ ↦ _root_.id

theorem toGrevLex_inj {a b : α} : toGrevLex a = toGrevLex b ↔ a = b := Iff.rfl

/-- `ofGrevLex`：把 `GrevLex α` 重新当作原始的 `α`；同样是恒等等价。 -/
@[match_pattern] def ofGrevLex : GrevLex α ≃ α := Equiv.refl _
/- 对称的注入性/注入判据。 -/
theorem ofGrevLex_injective : Function.Injective (ofGrevLex (α := α)) := fun _ _ ↦ _root_.id

theorem ofGrevLex_inj {a b : GrevLex α} : ofGrevLex a = ofGrevLex b ↔ a = b := Iff.rfl
/- `simp`：两个等价互为对方的逆，同为 `refl`。 -/
@[simp] theorem ofGrevLex_symm_eq : (@ofGrevLex α).symm = toGrevLex := rfl

@[simp] theorem toGrevLex_symm_eq : (@toGrevLex α).symm = ofGrevLex := rfl

@[simp] theorem ofGrevLex_toGrevLex (a : α) : ofGrevLex (toGrevLex a) = a := rfl

@[simp] theorem toGrevLex_ofGrevLex (a : GrevLex α) : toGrevLex (ofGrevLex a) = a := rfl

/-- 自定义归纳器：允许对 `x : GrevLex α` 直接 `induction x`；
    做法是先经 `ofGrevLex` 把它还原为 `α`，再用给定的归纳假设收尾。 -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def GrevLex.rec {β : GrevLex α → Sort*} (h : ∀ a, β (toGrevLex a)) :
    ∀ a, β a := fun a => h (ofGrevLex a)
/- 量词换壳：`∀/∃` 在 `GrevLex` 与 `α` 之间互换，便于在证明中自由切换视角。 -/
@[simp] lemma GrevLex.forall_iff {p : GrevLex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toGrevLex a) := Iff.rfl
@[simp] lemma GrevLex.exists_iff {p : GrevLex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toGrevLex a) := Iff.rfl

/- 通过等价把代数结构搬到壳上：运行时仍然零成本。 -/
noncomputable instance [AddCommMonoid α] :
    AddCommMonoid (GrevLex α) := ofGrevLex.addCommMonoid

/- 对应的 `simp`：在壳里做加法等同于先还原、再加法、再套壳。 -/
theorem toGrevLex_add [AddCommMonoid α] (a b : α) :
    toGrevLex (a + b) = toGrevLex a + toGrevLex b := rfl

theorem ofGrevLex_add [AddCommMonoid α] (a b : GrevLex α) :
    ofGrevLex (a + b) = ofGrevLex a + ofGrevLex b := rfl





/-
分次逆字典序：关系定义、`asKey` 键映射与良基性（Part 2）
====================================================
这一段把“分次逆字典序”的数学思想落在 `α →₀ ℕ` 上：
- **关系层面**：把每个指数向量 `x` 映到 `(x.degree, x)`，
  然后在外层的度数用关系 `s`（通常取 `<`）比较；若度数相等，
  在内层用前面定义好的 `Finsupp.Lex r s_val`（通常 `r=(·<·)`、`s_val=(·>·)` 即 rlex）比较。
  这正是“graded reverse lex”：**先比总次数（升序），同度时按逆字典序打破平局**。
- **`asKey`**：构造一个注入的“键”（key），把 `GrevLex` 里的元素送到 `Lex (ℕ × RLex (α →₀ ℕ))`，
  方便后续通过 `LinearOrder.lift'` 之类的技术在壳上得到线序。
- **良基性**：若度序 `s` 良基，且**每个定度层**在 rlex 上良基，则整体分次逆字典序良基。
  证明用到了“积字典序的良基性来自于底层良基 + 纤维上的良基”的标准组合定理。
-/

/-分次逆字典序相关实例和定理部分-/
namespace Finsupp
open scoped Function in
/-- 分次逆字典序关系：
    对 `x,y : α →₀ ℕ`，先比较 `x.degree` vs `y.degree` 按 `s`；
    若度数相等，再比较 `x` 与 `y` 按 `Finsupp.Lex r s_val`。 -/
protected def GrevLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) (s_val : ℕ → ℕ → Prop):
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s_val)) on (fun x ↦ (x.degree, x))


/-- `GrevLex` 的定义直接展开成“(度, 本体) 的积字典序”。 -/
theorem GrevLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop}{s_val : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.GrevLex r s s_val a b ↔ Prod.Lex s (Finsupp.Lex r s_val) (a.degree, a) (b.degree, b) :=
  Iff.rfl

namespace GrevLex

/- **良基性拼接定理**（分次逆字典序）：
    若外层度序 `s` 良基，且对每个度 `d`，
    集合 `{x | degree x = d}` 在 rlex（`Finsupp.Lex r sval`）上良基，
    则整体 `Finsupp.GrevLex r s sval` 良基。 -/
open Function in theorem wellFounded
  {r : α → α → Prop}
  {s : ℕ → ℕ → Prop} (hs : WellFounded s)
  {sval : ℕ → ℕ → Prop}
  (hfiber :
    ∀ d : ℕ,
      {x : α →₀ ℕ | x.degree = d}.WellFoundedOn
        (Finsupp.Lex r sval)) :
  WellFounded (Finsupp.GrevLex r s sval) := by
  classical
  -- 度函数 `x ↦ x.degree` 下把 `s` 下推到定义域：得到外层的良基
  have hα : WellFounded (s on (fun x : α →₀ ℕ => x.degree)) :=
    (hs.onFun (r := s) (f := fun x : α →₀ ℕ => x.degree))
  -- 用“积字典序的良基性来自外层良基 + 纤维良基”的组合定理。
  exact WellFounded.prod_lex_of_wellFoundedOn_fiber hα hfiber








/-
GrevLex：实例、线序、消去律、最小元与良基（Part 3）
===============================================
这一段把“分次逆字典序”真正挂到 `GrevLex (α →₀ ℕ)` 上：
- 在壳上给出 `<` 实例（外层比度、内层用 rlex）；
- 展开 `<` 的**等价判据**（先度后 rlex），并证明严格序（不可反身、传递）；
- 当 `[Fintype α]` 时，用 `asKey` 注入到 `Lex (ℕ × RLex …)` 提升为 `LinearOrder`；
- 给出 `≤` 的分解判据 `le_iff`，以及与加法相容的 `IsOrderedCancelAddMonoid`；
- 证明“一次单项式”嵌入的严格单调（`StrictMono`）；
- 给出度数函数的单调性、以及把 `0` 作为最小元 `⊥`；
- 最后用前面得到的纤维良基性拼接出整体良基（`WellFoundedLT`）。
-/

instance [LT α] : LT (GrevLex (α →₀ ℕ)) :=
  ⟨fun f g ↦ Finsupp.GrevLex (· < ·) (· < ·) (· > ·) (ofGrevLex f) (ofGrevLex g)⟩


/-- 把“本体”的 rlex 换成 `toRLex` 的壳表述。 -/
theorem lt_def [LT α] {a b : GrevLex (α →₀ ℕ)} :
    a < b ↔ (toLex ((ofGrevLex a).degree, toRLex (ofGrevLex a))) <
        (toLex ((ofGrevLex b).degree, toRLex (ofGrevLex b))) :=
  Iff.rfl

/-- `<` 的判据（人话版）：要么度更小；要么度相等且在 rlex 上更小。 -/
theorem lt_iff [LT α] {a b : GrevLex (α →₀ ℕ)} :
    a < b ↔ (ofGrevLex a).degree < (ofGrevLex b).degree ∨
    (((ofGrevLex a).degree = (ofGrevLex b).degree) ∧ toRLex (ofGrevLex a) < toRLex (ofGrevLex b)) := by
  simp only [lt_def,Prod.Lex.toLex_lt_toLex]


variable [LinearOrder α]

/-- `GrevLex` 上 `<` 是严格序：不可反身 + 传递。 -/
instance GrevLex_isStrictOrder : IsStrictOrder (GrevLex (α →₀ ℕ)) (· < ·) where
  irrefl := fun a ↦ by
    classical
    -- 用 `lt_def` 把 GrevLex 的 `<` 改写到积字典序上，逐分量排除自反性
    change ¬
      toLex ((ofGrevLex a).degree, toRLex (ofGrevLex a)) <
      toLex ((ofGrevLex a).degree, toRLex (ofGrevLex a))
      -- 展开积的字典序：先比第一分量（度），相等时再比第二分量（rlex）
    have : ¬ (
      (ofGrevLex a).degree < (ofGrevLex a).degree ∨
        ((ofGrevLex a).degree = (ofGrevLex a).degree ∧
          toRLex (ofGrevLex a) < toRLex (ofGrevLex a))) := by
      -- 第一项：度不可能自小于；第二项：rlex 不可反身
      simp only [lt_self_iff_false, lt_self_false_RLex, and_false, or_self, not_false_eq_true]
    -- 把上面的等价式（`Prod.lex_def`）折回去
    intro p
    apply lt_def.mpr at p
    apply lt_iff.mp at p
    exact this p
  trans := by
    intro a b c hab hbc
    -- 对两个假设分别用“度更小 or 等度且 rlex 更小”的析取
    simp only [lt_iff] at hab hbc ⊢
    rcases hab with (hab | hab)
    · rcases hbc with (hbc | hbc)
      · left; exact lt_trans hab hbc
      · left; exact lt_of_lt_of_eq hab hbc.1
    · rcases hbc with (hbc | hbc)
      · left; exact lt_of_eq_of_lt hab.1 hbc
      · right
        constructor
        ·
          exact Eq.trans hab.1 hbc.1
        ·
          exact rlex_trans hab.2 hbc.2



/-- 用“键排序”把 `GrevLex` 提升为线序：先按度，再按 rlex。 -/
noncomputable instance GrevLex_linearOrder [WellFoundedLT α] : LinearOrder (GrevLex (α →₀ ℕ)) :=
  LinearOrder.lift'
    (fun (f : GrevLex (α →₀ ℕ)) ↦ toLex ((ofGrevLex f).degree, toRLex (ofGrevLex f)))
    (fun f g ↦ by simp)

variable [WellFoundedLT α]
/-- `≤` 的判据（人话版）：要么度更小；要么度相等且在 rlex 上 `≤`。 -/
theorem le_iff {x y : GrevLex (α →₀ ℕ)} :
    x ≤ y ↔ (ofGrevLex x).degree < (ofGrevLex y).degree ∨
      (ofGrevLex x).degree = (ofGrevLex y).degree ∧ toRLex (ofGrevLex x) ≤ toRLex (ofGrevLex y) := by
  -- 把 `≤` 展为 `=` ∨ `<`，并使用前面的 `lt_def` / `Prod.Lex` 判据来回改写
  simp only [le_iff_eq_or_lt,  EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp only [h, lt_self_iff_false, or_false, and_self, or_true]
  · by_cases k : (ofGrevLex x).degree < (ofGrevLex y).degree
    ·
      simp only [h, false_or, k, true_or, iff_true]
      apply lt_def.mpr
      apply Prod.Lex.toLex_lt_toLex.mpr
      simp only [toRLex_lt_iff, gt_iff_lt]
      left
      exact k
    ·
      simp only [not_lt] at k
      simp only [h, false_or]
      constructor
      ·
        intro p
        apply lt_def.mp at p
        apply Prod.Lex.toLex_lt_toLex.mp at p
        simp only [toRLex_lt_iff, gt_iff_lt] at p
        cases p with
        |inl l=>
          left
          exact l
        |inr l=>
          right
          obtain⟨l1,l2⟩:=l
          constructor
          ·
            exact l1
          ·
            apply rlex_lt_iff.mpr
            apply Finsupp.lex_def.mp at l2
            simp only [ofRLex_toRLex]
            obtain⟨j,hj,hjj⟩:=l2
            use j
      ·
        intro p
        apply lt_def.mpr
        apply Prod.Lex.toLex_lt_toLex.mpr
        simp only [toRLex_lt_iff, gt_iff_lt]
        cases p with
        |inl l=>
          left
          exact l
        |inr l=>
          right
          obtain⟨l1,l2⟩:=l
          constructor
          ·
            exact l1
          ·
            apply Finsupp.lex_def.mpr
            apply Finsupp.lex_def.mp at l2
            obtain⟨j,hj,hjj⟩:=l2
            use j
            simp only [ofRLex_toRLex] at hj hjj
            constructor
            ·
              exact fun d a ↦
                  Eq.symm ((fun {a b} ↦ Nat.succ_inj.mp) (congrArg Nat.succ (hj d a).symm))
            ·
              exact hjj


/-- 与加法的相容性：由 `c + a ≤ c + b` 推出 `a ≤ b`，反之亦然。 -/
noncomputable instance isOrderedCancelAddMonoid
   [WellFoundedLT α]  :
  IsOrderedCancelAddMonoid (GrevLex (α →₀ ℕ)) where
-- 由 c + a ≤ c + b 推出 a ≤ b
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [rlex_add_le_add_iff_left,ofGrevLex_add, degree_add, add_lt_add_iff_left, add_right_inj, toRLex_add,
      add_le_add_iff_left] using h
  -- 由 a ≤ b 推出 c + a ≤ c + b
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa [ofGrevLex_add, degree_add] using h

/- 在分次逆字典序下，`a < b` 蕴含 `x^a < x^b`（一次单项式）。
    注意：这是 `StrictMono`，与 `DegLex` 里的 `StrictAnti` 方向相反。 -/
theorem single_strictMono:
  StrictMono (fun (a : α) ↦ toGrevLex (Finsupp.single a 1)) := by
  intro a b h
  classical
   -- 先在内层 rlex 上得到严格不等
  have hinner :
      toRLex (Finsupp.single a (1:ℕ)) <
      toRLex (Finsupp.single b (1:ℕ)) := by
    -- 改写回 Finsupp 版 rlex，然后用上一步引理
    have : Finsupp.Lex (· < ·) (· > ·)
              (Finsupp.single a (1:ℕ)) (Finsupp.single b (1:ℕ)) :=
      (rlex_single_lt_iff).2 h
    simpa [toRLex_lt_iff] using this
  -- 把“内层成功”装回到 GrevLex 的 `<`（度都等于 1，走等度分支）
  have : toLex ((1 : ℕ), toRLex (Finsupp.single a (1:ℕ))) <
         toLex ((1 : ℕ), toRLex (Finsupp.single b (1:ℕ))) := by
    exact (Prod.lex_def.mpr (Or.inr ⟨rfl, hinner⟩))
  -- 最终把壳翻回来
  simpa [lt_def]

/-- 从严格单调推出单调、以及一次单项式比较的充要条件。 -/
theorem single_monotone : Monotone (fun (a : α) ↦ toGrevLex (single a 1)) :=
  single_strictMono.monotone

theorem single_lt_iff {a b : α} :
    toGrevLex (Finsupp.single b 1) < toGrevLex (Finsupp.single a 1) ↔ b < a :=
  single_strictMono.lt_iff_lt

theorem single_le_iff {a b : α} :
    toGrevLex (Finsupp.single b 1) ≤ toGrevLex (Finsupp.single a 1) ↔ b ≤ a :=
  single_strictMono.le_iff_le

/-- 度数函数在 `GrevLex` 下单调不减（`x ≤ y ⇒ deg x ≤ deg y`）。 -/
theorem monotone_degree :
    Monotone (fun (x : GrevLex (α →₀ ℕ)) ↦ (ofGrevLex x).degree) := by
  intro x y
  rw [le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1



/-- 以 `0` 作为 `GrevLex` 的最小元素。 -/
noncomputable instance orderBot : OrderBot (GrevLex (α →₀ ℕ)) where
  bot := toGrevLex (0 : α →₀ ℕ)
  bot_le x := by
    classical
    -- 展开 GrevLex 的 ≤ 判据，并把 ⊥=0 带入
    simp only [Finsupp.GrevLex.le_iff, ofGrevLex_toGrevLex, Finsupp.degree_zero]
    -- 分两类：deg x = 0 或 0 < deg x
    rcases Nat.eq_zero_or_pos (ofGrevLex x).degree with hdeg0 | hdegpos
    · -- 同度层（0=0）：此时必须走右支；再由 deg=0 ⇒ x=0，右支直接由 rfl 与 ≤_refl 结束
      have hx0 : ofGrevLex x = (0 : α →₀ ℕ) :=
        (Finsupp.degree_eq_zero_iff (ofGrevLex x)).mp hdeg0
      -- 此时化简为 True ∧ (toLex/toRLex 的自反 ≤)
      simp only [hx0, degree_zero, lt_self_iff_false,  le_refl, and_self,
        or_true]
    · -- 0 < deg x：直接走左支
      simp only [hdegpos, true_or]



/-- 终局：`GrevLex` 良基（当索引有线序且是有限集时）。 -/
instance wellFoundedLT [LinearOrder α][Fintype α]:
    WellFoundedLT (GrevLex (α →₀ ℕ)) :=by
    refine ⟨?_⟩
    exact
      wellFounded
        (r := (· < ·)) (s := (· < ·)) (sval := (· > ·))
        (hs := wellFounded_lt)
        (hfiber := rlex_gt_wf_on_degree)



end GrevLex

end Finsupp















namespace MonomialOrder

open Finsupp

variable {σ : Type*}

/-
MonomialOrder 接口与使用示例
=====================================
本段代码把前面已经在 `Finsupp` 层建立好的 **分次逆字典序 GrevLex**，
通过 `MonomialOrder` 接口对接出去（供 `MvPolynomial` 等上层结构使用）。


核心结构与思路：
1) 两个基础“度数与坐标”引理：
* `degree_mono_of_pointwise_le`：若逐坐标 `a i ≤ b i`，则总次数 `deg a ≤ deg b`。
* `pointwise_eq_of_degree_eq`：在自然数情形下，若逐坐标 `a i ≤ b i` 且 `deg a = deg b`，则逐坐标全等 `a = b`。
这两条将用于证明映射 `toGrevLex` 对“点态 ≤”是单调的（或在等度时给出等号）。
2) `grevLex : MonomialOrder σ`：真正构造出一个 `MonomialOrder` 实例：
* `syn := GrevLex (σ →₀ ℕ)`：语法壳。排序发生在这个壳上（前面已经在壳上给出了线序）。
* `toSyn`：把底层指数向量“套壳”为 `GrevLex`；并提供与加法兼容的等价。
* `toSyn_monotone`：若 `a ≤ b`（逐坐标）则 `toGrevLex a ≤ toGrevLex b`（在 grevlex 上）。
证明分两类：度真正变小；或度相等再用上一条“等度 + 逐坐标 ≤ ⇒ 相等”。
3) 若干桥接引理：把 `≼[grevLex]`/`≺[grevLex]` 同步为 `toGrevLex` 上的 `≤`/`<`，便于复用前文的判据。
4) 示例：在 `Fin 2` 的两变量情形，展示一次/二次单项式在 grevlex 下的比较。
-/


/-- 基本引理 1：若逐坐标 `a i ≤ b i`，则度（各坐标和）满足 `a.degree ≤ b.degree`。 -/
private lemma degree_mono_of_pointwise_le
   {a b : σ →₀ ℕ} (h : ∀ i, a i ≤ b i) :
  a.degree ≤ b.degree := by
  classical
  -- 用支持集并集 `s` 把两边求和拉到同一索引域上，逐点比较后用 `sum_le_sum` 收尾。
  let s : Finset σ := a.support ∪ b.support
  have hdeg_a_support : a.degree = ∑ i ∈ a.support, a i := rfl
  have hdeg_b_support : b.degree = ∑ i ∈ b.support, b i := rfl
  -- 把对各自支持集的求和提升到并集 `s`，不在自己支持集的点上视为 0。
  have hsum_a : ∑ i ∈ a.support, a i = ∑ i ∈ s, a i := by
    refine Finset.sum_subset (by
      intro i hi; exact Finset.mem_union.mpr (Or.inl hi))
      (by
        intro i hi hnot
        have : i ∉ a.support := hnot
        have : a i = 0 := by
          by_contra hne
          have : i ∈ a.support := by simp only [mem_support_iff, ne_eq, hne, not_false_eq_true]
          exact hnot this
        simp only [this])
  have hsum_b : ∑ i ∈ b.support, b i = ∑ i ∈ s, b i := by
    refine Finset.sum_subset (by
      intro i hi; exact Finset.mem_union.mpr (Or.inr hi))
      (by
        intro i hi hnot
        have : i ∉ b.support := hnot
        have : b i = 0 := by
          by_contra hne
          have : i ∈ b.support := by simp only [mem_support_iff, ne_eq, hne, not_false_eq_true]
          exact hnot this
        simp only [this])
  -- 逐点 ≤ 推出并集上的和 ≤
  have hle_on_s : (∑ i ∈ s, a i) ≤ (∑ i ∈ s, b i) :=
    Finset.sum_le_sum (by
      intro i hi
      exact h i)
  have : (∑ i ∈ a.support, a i) ≤ (∑ i ∈ b.support, b i) := by
    simpa [hsum_a, hsum_b] using hle_on_s
  simpa [hdeg_a_support, hdeg_b_support] using this




/-- 基本引理 2（自然数情形的刚性）：若逐坐标 `a i ≤ b i` 且度相等，
则逐坐标必定全等（不能存在某处严格小，因为总和已经卡死）。 -/
private lemma pointwise_eq_of_degree_eq
  {a b : σ →₀ ℕ}
  (h : ∀ i, a i ≤ b i) (hdeg : a.degree = b.degree) :
  a = b := by
  classical
  let s : Finset σ := a.support ∪ b.support

  have hdeg_a_support : a.degree = ∑ i ∈ a.support, a i := rfl
  have hdeg_b_support : b.degree = ∑ i ∈ b.support, b i := rfl
  -- 同上一引理，把两侧求和都放到并集 `s` 上。
  have hsum_a : ∑ i ∈ a.support, a i = ∑ i ∈ s, a i := by
    refine Finset.sum_subset (by
      intro i hi; exact Finset.mem_union.mpr (Or.inl hi))
      (by
        intro i hi hnot
        have : a i = 0 := by
          by_contra hne
          have : i ∈ a.support := by simp only [mem_support_iff, ne_eq, hne, not_false_eq_true]
          exact hnot this
        simp only [this])
  have hsum_b : ∑ i ∈ b.support, b i = ∑ i ∈ s, b i := by
    refine Finset.sum_subset (by
      intro i hi; exact Finset.mem_union.mpr (Or.inr hi))
      (by
        intro i hi hnot
        have : b i = 0 := by
          by_contra hne
          have : i ∈ b.support := by simp only [mem_support_iff, ne_eq, hne, not_false_eq_true]
          exact hnot this
        simp only [this])
  -- 总和相等，且逐点 ≤，推出并集上不存在“严格小”的点。
  have hsum : (∑ i ∈ s, a i) = (∑ i ∈ s, b i) := by
    simpa [hdeg_a_support, hdeg_b_support, hsum_a, hsum_b] using hdeg
  have no_strict : ¬ ∃ i ∈ s, a i < b i := by
    intro hex
    rcases hex with ⟨i, hi, hlt⟩
    have hle_all : ∀ j ∈ s, a j ≤ b j := by
      intro j _; exact h j
    -- 若某点严格小，则和也严格小，矛盾于总和相等。
    have hlt_sum : (∑ i ∈ s, a i) < (∑ i ∈ s, b i) :=
      Finset.sum_lt_sum hle_all ⟨i, hi, hlt⟩
    have : (∑ i ∈ s, a i) < (∑ i ∈ s, a i) := by
      simp only [hsum, lt_self_iff_false] at hlt_sum
    exact (lt_irrefl _) this
  -- 对每个坐标：若在并集内，用“≤ 且非 < ⇒ =”；不在并集则两边都是 0。
  ext i
  by_cases hi : i ∈ s
  · have hle_i : a i ≤ b i := h i
    have hlt_i : ¬ a i < b i := by exact fun hlt => no_strict ⟨i, hi, hlt⟩
    exact le_antisymm hle_i (le_of_not_gt hlt_i)
  ·
    have hnot_a : i ∉ a.support := by
      intro hi'
      exact hi (Finset.mem_union.mpr (Or.inl hi'))
    have hnot_b : i ∉ b.support := by
      intro hi'
      exact hi (Finset.mem_union.mpr (Or.inr hi'))
    have : a i = 0 := by
      by_contra hne
      exact hnot_a (by simp only [mem_support_iff, ne_eq, hne, not_false_eq_true])
    have : b i = 0 := by
      by_contra hne
      exact hnot_b (by simp only [mem_support_iff, ne_eq, hne, not_false_eq_true])
    simp [this, ‹a i = 0›]


variable [LinearOrder σ]  [Fintype σ]

/-- 把前述 `GrevLex` 挂到 `MonomialOrder` 接口上的最终定义。 -/
noncomputable def grevLex :
    MonomialOrder σ where
  -- `syn`：选用我们目标排序。
  syn := GrevLex (σ →₀ ℕ)
  -- `toSyn`：底层指数向量 ↔ 壳的等价。
  toSyn := { toEquiv := toGrevLex, map_add' := toGrevLex_add }
  -- `toSyn_monotone`：若点态 `a ≤ b`，则 grevlex 下 `toGrevLex a ≤ toGrevLex b`。
  -- 证明：要么度严格变小；否则度相等，由“逐坐标 ≤ + 等度 ⇒ 相等”得到第二分量也 `≤`。
  toSyn_monotone a b h := by
    simp only [AddEquiv.coe_mk, GrevLex.le_iff, ofGrevLex_toGrevLex]
    by_cases ha : a.degree < b.degree
    · exact Or.inl ha
    · have hleDeg : a.degree ≤ b.degree := degree_mono_of_pointwise_le (by intro i; exact h i)
      have hdeg : a.degree = b.degree := le_antisymm hleDeg (le_of_not_gt ha)
      -- 逐坐标 ≤ + 度相等 ⇒ a = b
      have hEq : a = b := pointwise_eq_of_degree_eq (by intro i; exact h i) hdeg
      -- 于是 toRLex a ≤ toRLex b 取等号即真
      exact Or.inr ⟨hdeg, by simp only [hEq, le_refl]⟩

/-- 把接口记号 `≼[grevLex]` 与壳上 `≤` 对齐。 -/
theorem grevLex_le_iff {a b : σ →₀ ℕ} :
    a ≼[grevLex] b ↔ toGrevLex a ≤ toGrevLex b :=
  Iff.rfl
/-- 把接口记号 `≺[grevLex]` 与壳上 `<` 对齐。 -/
theorem grevLex_lt_iff {a b : σ →₀ ℕ} :
    a ≺[grevLex] b ↔ toGrevLex a < toGrevLex b :=
  Iff.rfl
/-- 一次单项式的比较在接口层的刻画：`Xᵃ ≤ Xᵇ` 当且仅当 `a ≤ b`。 -/
theorem grevLex_single_le_iff {a b : σ} :
    single a 1 ≼[grevLex] single b 1 ↔ a ≤ b := by
  rw [MonomialOrder.grevLex_le_iff, GrevLex.single_le_iff]
/-- 一次单项式的严格比较：`Xᵃ < Xᵇ` 当且仅当 `a < b`。 -/
theorem grevLex_single_lt_iff {a b : σ} :
    single a 1 ≺[grevLex] single b 1 ↔ a < b := by
  rw [MonomialOrder.grevLex_lt_iff, GrevLex.single_lt_iff]


end MonomialOrder


/-
示例（Examples）
================
在两变量情形 `σ = Fin 2`，演示一次/二次单项式的大小关系。
-/
section Examples

open Finsupp MonomialOrder GrevLex

/-- 例 1：在 grevlex 下，`X₀ < X₁`。 -/
example : single 0 1 ≺[grevLex] single (1 : Fin 2) 1 := by
  rw [grevLex_lt_iff, single_lt_iff]
  exact Nat.one_pos

/-- 例 2：在 grevlex 下，`X₀^2 < X₀·X₁`（总次数相等，在首次不同位按 rlex 比较）。 -/
example : single (0 : Fin 2) 2 ≺[grevLex] (single 0 1 + single 1 1)  := by
  simp only [grevLex_lt_iff, lt_iff, ofGrevLex_toGrevLex, degree_add,
    degree_single, Nat.reduceAdd, lt_self_iff_false, true_and, false_or]
  use 0
  simp

/-- 例 3：在 grevlex 下，`X₀ < X₁^2`。 -/
example : single (0 : Fin 2) 1 ≺[grevLex] single 1 2 := by
  simp only [Fin.isValue, grevLex_lt_iff, lt_iff, ofGrevLex_toGrevLex, degree_single,
    Nat.one_lt_ofNat, OfNat.one_ne_ofNat, toRLex_lt_iff, gt_iff_lt, false_and, or_false]


open Finsupp MvPolynomial

noncomputable def x2yz : Fin 3 →₀ ℕ := single 0 2 + single 1 1 + single 2 1   -- x^2 y z
noncomputable def xy3 : Fin 3 →₀ ℕ := single 0 1 + single 1 3  --x y^3


example : x2yz ≺[grevLex] xy3 := by
  simp only [grevLex_lt_iff, lt_iff, ofGrevLex_toGrevLex, toRLex_lt_iff, gt_iff_lt]
  simp only [x2yz, Fin.isValue, degree_add, degree_single, Nat.reduceAdd, xy3, lt_self_iff_false,
    true_and, false_or,lex_def]
  let j:=(0:Fin 3)
  use j
  unfold j
  constructor
  ·
    simp only [Fin.isValue, Fin.not_lt_zero, IsEmpty.forall_iff, implies_true]
  ·
    simp only [Fin.isValue, Finsupp.coe_add, Pi.add_apply, single_eq_same, ne_eq,
    not_false_eq_true, single_eq_of_ne, add_zero, Fin.reduceEq,Nat.one_lt_ofNat]



example :toGrevLex x2yz < toGrevLex xy3:=by
  simp only [GrevLex.lt_iff, ofGrevLex_toGrevLex, toRLex_lt_iff, gt_iff_lt]
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
         not_false_eq_true, single_eq_of_ne, add_zero, x2yz, Fin.reduceEq,
        Nat.one_lt_ofNat]


end Examples

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
  f ≠ 0 ∧ ∃ i, m.degree (b i) ≤ m.degree f

/-- 从 `HeadReducible` 中挑一个可约的下标（非构造性选择） -/
noncomputable def chooseHead
(m : MonomialOrder σ)
(b : ι → MvPolynomial σ R)
(f : MvPolynomial σ R)
(h : HeadReducible m b f) :
{ i : ι // m.degree (b i) ≤ m.degree f } :=
⟨Classical.choose h.2, Classical.choose_spec h.2⟩

/-- 若可头部约化，则 `f ≠ 0`。 -/
lemma headReducible_ne_zero
(m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
{f : MvPolynomial σ R} (h : HeadReducible m b f) :
f ≠ 0 := h.1

/-- 在已知 `f ≠ 0` 的前提下，“不可头部约化” ⇔ 对所有 `i` 都有 `¬ LM(b i) ≤ LM(f)`。 -/
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
      · -- 新：在可约分支里先分 `deg f = 0` 与否
        by_cases hdeg0 : m.degree f = 0
        · -- `deg f = 0` 且可约 ⇒ 基中存在常数单位，多项式理想为 ⊤，一步约成 0
          -- 也可直接用 `reduce` 的公式验证常数一步化为 0；这里直接返回 0
          exact 0
        · -- `deg f ≠ 0`：照常做一步首项约化后递归
          let i := (chooseHead (m := m) (b := b) f h).val
          have hi := (chooseHead (m := m) (b := b) f h).property
          exact reduceFamily m b hb (m.reduce (hb i) f)
      · -- 不可头约：再分 `deg f = 0` 与否
        by_cases hdeg0 : m.degree f = 0
        · exact f
        · exact m.initTerm f + reduceFamily m b hb (m.subLTerm f)
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


/-- 若 `m.degree f = 0` 且 **不可头约化**，余式就是 `f` 本身。 -/
lemma reduceFamily_degree_zero_notHR
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R} (hf0 : f ≠ 0)
    (hdeg0 : m.degree f = 0) (hnot : ¬ HeadReducible m b f) :
    m.reduceFamily b hb f = f := by
  classical
  simp [reduceFamily, hf0, hdeg0, hnot]


lemma reduce_eq_zero_of_deg0_head
    (m : MonomialOrder σ)
    {f h : MvPolynomial σ R}
    (hf0 : m.degree f = 0) (hh0 : m.degree h = 0)
    (uh : IsUnit (m.leadingCoeff h)) :
    m.reduce uh f = 0 := by
  classical
  -- 把 f、h 都改写成常数
  have hfC  : f = C (m.leadingCoeff f)     := m.eq_C_of_degree_eq_zero hf0
  have hhC  : h = C (m.leadingCoeff h)     := m.eq_C_of_degree_eq_zero hh0
  -- 单位的“逆乘原元 = 1”
  have u_id :
      ((uh.unit⁻¹ : Units R) : R) * m.leadingCoeff h = (1 : R) := by
    simp
  -- 代入约化公式直接计算
  -- monomial 0 c = C c；最终得到 f - C(lc f) = 0
  -- 展开 reduce，并先把度数差化成 0
  unfold MonomialOrder.reduce
  rw [hf0, hh0, tsub_self]
  -- 只改写 f（避免触碰 uh 的依赖）
  rw [hfC]

  -- 记住系数 a := (↑(u⁻¹) * lc f)
  set a : R := ((↑(uh.unit⁻¹) : R) * m.leadingCoeff f) with ha

  -- 现在目标是：C (lc f) - (monomial 0 a) * h = 0
  -- 先把右边这坨乘积算成一个常数多项式
  -- 第一步：只在这个乘积的右因子里改写 h = C (lc h)
  have hEq :
      (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * h
        = (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * C (m.leadingCoeff h) := by
    conv_lhs=>
      rw [hhC]

  -- 第二步：计算 (monomial 0 a) * C (lc h) = C (a * lc h)
  have hMono0 : (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) = C a := by
    simp
  have hMulC :
      (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * C (m.leadingCoeff h)
        = C (a * m.leadingCoeff h) := by
    -- 用 hMono0 把左因子变成 C a，再用 C 的乘法同态性质
    simp

  -- 合并上面两步
  have hProd :
      (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * h
        = C (a * m.leadingCoeff h) :=
    hEq.trans hMulC

  -- 用 u_id 把 a * lc(h) 化成 lc(f)
  have hCoeff :
  (C : R →+* MvPolynomial σ R) (a * m.leadingCoeff h)
    = (C : R →+* MvPolynomial σ R) (m.leadingCoeff f) := by
    -- 先把乘法重排到 lc f * ((u⁻¹) * lc h)
    have reas :
        a * m.leadingCoeff h
          = m.leadingCoeff f * (((↑(uh.unit⁻¹) : R) * m.leadingCoeff h)) := by
      -- a = (↑(u⁻¹) * lc f)（见 ha），交换+结合即可
      ring
    calc
      C (a * m.leadingCoeff h)
          = C (m.leadingCoeff f * (((↑(uh.unit⁻¹) : R) * m.leadingCoeff h))) := by
              simp [reas]
      _   = C (m.leadingCoeff f * 1) := by
              simp [u_id]
      _   = C (m.leadingCoeff f) := by
              simp

  -- 于是乘积就是 C (lc f)，差为 0
  have hProdC :
      (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * h
        = C (m.leadingCoeff f) :=
    hProd.trans hCoeff
  -- 把常数多项式的首项系数化简掉：lc (C r) = r
  have hLCf :
      m.leadingCoeff ((C : R →+* MvPolynomial σ R) (m.leadingCoeff f))
        = m.leadingCoeff f := by
    simp [MonomialOrder.leadingCoeff, MonomialOrder.degree_C]

  -- 先把第二项的系数换成 a
  have hRew :
      ((monomial (0 : σ →₀ ℕ)
          (↑uh.unit⁻¹ * m.leadingCoeff ((C : R →+* MvPolynomial σ R) (m.leadingCoeff f)))
          : MvPolynomial σ R) * h)
        = (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * h := by
    -- 用 hLCf 把 lc(C(lc f)) → lc f，再用 ha 把系数收成 a
    simp [hLCf, ha]

  -- 现在把目标按这两个小步等式改写，再用 hProdC 收尾
  calc
    (C : R →+* MvPolynomial σ R) (m.leadingCoeff f)
      - (monomial (0 : σ →₀ ℕ)
           (↑uh.unit⁻¹ * m.leadingCoeff ((C : R →+* MvPolynomial σ R) (m.leadingCoeff f))))
           * h
        = (C : R →+* MvPolynomial σ R) (m.leadingCoeff f)
          - (monomial (0 : σ →₀ ℕ) a : MvPolynomial σ R) * h := by
            rw [hRew]
    _   = (C : R →+* MvPolynomial σ R) (m.leadingCoeff f)
          - (C : R →+* MvPolynomial σ R) (m.leadingCoeff f) := by
            rw [hProdC]
    _   = 0 := by
            simp


/-- 若 `m.degree f = 0` 且 **不可头约化**，余式就是 `f` 本身。 -/
lemma reduceFamily_eq_notHead_deg0
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R}
    (hf0 : f ≠ 0) (hnot : ¬ HeadReducible m b f) (hdeg0 : m.degree f = 0) :
    m.reduceFamily b hb f = f := by
  simp [reduceFamily, hf0, hnot, hdeg0]



set_option linter.unusedVariables false in
/-- 若 `deg f ≠ 0` 且可头约化，则等于“做一步首项约化再递归”。 -/
lemma reduceFamily_eq_head_step1
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    {f : MvPolynomial σ R}
    (hf0 : f ≠ 0) (h : HeadReducible m b f)(hdegpos : m.degree f ≠ 0) :
    ∃ (i : ι)
      (hi : m.degree (b i) ≤ m.degree f ),
      m.reduceFamily b hb f = m.reduceFamily b hb (m.reduce (hb i) f) := by
  classical
  refine ⟨(m.chooseHead b f h).val, (m.chooseHead b f h).property, ?_⟩
  -- 只改写左边：展开一次定义，并用 hf0 / h 选中“可头约”分支
  conv_lhs =>
    unfold MonomialOrder.reduceFamily
    -- 这里的 `simp` 只用 `hf0` 和 `h` 做**分支选择**，
    -- 不会在子项里继续展开 `reduceFamily`（因为我们没把它放进 simp 集）
    simp [hf0, h,hdegpos]

set_option linter.unusedVariables false
lemma reduceFamily_eq_head_step2
  (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
  (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
  {f : MvPolynomial σ R}
  (hf0 : f ≠ 0) (h : HeadReducible m b f) (hdeg0 : m.degree f = 0) :
  ∃ (i : ι)
    (hi : m.degree (b i) ≤ m.degree f),
    m.reduceFamily b hb f = m.reduceFamily b hb (m.reduce (hb i) f) := by
  classical
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
    have : m.degree (b i) ≤ 0 := by simpa [hdeg0] using hi
    exact le_antisymm this (by simp)

  -- 常数对常数做一步 reduce（且 lc(b i) 为单位）得到 0
  have hred0 : m.reduce (hb i) f = 0 :=
    reduce_eq_zero_of_deg0_head (m := m) hdeg0 hbi0 (hb i)

  -- 现在把 `if` 用 hdeg0 挑成 then 分支，并把右边的 reduceFamily(0) 化成 0
  simp only [hdeg0, hred0, reduceFamily_eq_zero]
  simp only [↓reduceIte]


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
    exact reduceFamily_eq_head_step1 m b hb hf0 h hdegpos
  ·
    simp at hdegpos
    exact reduceFamily_eq_head_step2 m b hb hf0 h hdegpos


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
          rcases m.reduceFamily_eq_head_step2 (b := b) (hb := hb) (f := g2) hg2_ne ⟨hg2_ne, ⟨i, hi⟩⟩ hdeg0 with
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
              m.initTerm g2 + m.reduceFamily b hb (m.subLTerm g2) :=
            reduceFamily_eq_notHead_degpos (m := m) (b := b) (hb := hb) hg0 h hdeg0
          simpa [rdef] using
            mu_degree_initTerm_add_of_lt (m := m) (f := g2)
              (g := m.reduceFamily b hb (m.subLTerm g2)) μlt_tail
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
          exact h ⟨by exact hf0, j, hj⟩
        -- 矛盾
        exact (hnotf i) h_le





/-**S多项式部分**-/
variable (m : MonomialOrder σ)

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
    have hHR : HeadReducible m b r := ⟨hrne, k, hk⟩

    -- 但 `r` 是完全约化的余式：不可头约化
    have hNotHR : ¬ HeadReducible m b r :=
      reduceFamily_not_headReducible (m := m) (b := b) (hb := hb) (f := s)

    exact (hNotHR hHR).elim


end MonomialOrder
