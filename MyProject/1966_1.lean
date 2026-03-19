import Mathlib

/-
We encode the counts as nonnegative integers (ℤ with ≥ 0).
Variables:
  a   : only A
  b   : only B
  c   : only C
  ab  : exactly A&B
  ac  : exactly A&C
  bc  : exactly B&C
  abc : all three
Constraints:
  (T) a + b + c + ab + ac + bc + abc = 25
  (A) a = (ab + ac + abc) + 1
  (S) b + c = a                        -- "half of one-solvers didn't do A" ⇒ b + c = a
  (R) b + bc = 2 * (c + bc)            -- among non-A solvers: #B is twice #C

Goal: b = 6.
-/

set_option linter.unusedVariables false theorem contest_onlyB_is6
    {a b c ab ac bc abc : ℤ}
    -- nonnegativity (all are counts)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hab0 : 0 ≤ ab) (hac0 : 0 ≤ ac) (hbc0 : 0 ≤ bc) (habc0 : 0 ≤ abc)
    -- constraints from the statement
    (hTotal  : a + b + c + ab + ac + bc + abc = 25)
    (hA      : a = ab + ac + abc + 1)
    (hSingle : b + c = a)
    (hRatio  : b + bc = 2 * (c + bc)) :
    b = 6 := by

  -- From hA: ab + ac + abc = a - 1
  have hA' : ab + ac + abc = a - 1 := by
    linarith [hA]

  -- Rewrite the total using hA'
  have h_step1 : a + b + c + (a - 1) + bc = 25 := by
    -- This is hTotal with (ab+ac+abc) replaced by (a-1)
    linarith

  -- Add 1 to both sides to get a + a + b + c + bc = 26
  have h_step2 : a + a + b + c + bc = 26 := by
    -- h_step1 + 1 on both sides
    have := congrArg (fun t => t + 1) h_step1
    -- simplify LHS and RHS
    simpa [add_assoc, add_comm, add_left_comm] using this

  -- Replace a with (b + c) to eliminate a
  have h_bc3b3c : 2 * (b + c) + b + c + bc = 26 := by
    linarith

  -- From ratio: b + bc = 2c + 2bc ⇒ bc = b - 2c
  have h_bc_eq : bc = b - 2 * c := by
    -- b + bc = 2*c + 2*bc  ⇒ b - 2*c = bc
    linarith [hRatio]

  -- Substitute bc into the previous equation and simplify:
  -- 2*(b+c) + b + c + (b - 2c) = 26  ⇒  4b + c = 26
  have h_4b_plus_c : 4 * b + c = 26 := by
    linarith
  -- From h_4b_plus_c, express c explicitly
  have hc_def : c = 26 - 4 * b := by linarith [h_4b_plus_c]

  /- Upper bound b ≤ 6:
     If b ≥ 7 then c = 26 - 4b ≤ 26 - 28 = -2 < 0, contradicting hc0. -/
  have hb_le_6 : b ≤ 6 := by
    by_contra h
    have hb_ge_7 : 7 ≤ b := by
      -- h : ¬ b ≤ 6  ⇒ 6 < b ⇒ 7 ≤ b
      have hb_gt_6 : 6 < b := lt_of_not_ge h
      -- 6 < b ↔ 7 ≤ b
      exact (Int.add_one_le_iff.mpr hb_gt_6)
    -- Then c ≤ 26 - 4*7 = -2
    have hc_le_neg2 : c ≤ -2 := by
      have : c = 26 - 4 * b := hc_def
      linarith
    -- But c ≥ 0 from nonnegativity
    have : False := by linarith [hc0, hc_le_neg2]
    exact this.elim

  /- Lower bound b ≥ 6:
     From bc ≥ 0 and bc = b - 2c we have b ≥ 2c.
     Using c = 26 - 4b, this gives b ≥ 2*(26 - 4b) ⇒ 9b ≥ 52 ⇒ b ≥ 6. -/
  have hb_ge_2c : b ≥ 2 * c := by
    -- bc = b - 2c ≥ 0  ⇒ b - 2c ≥ 0  ⇒ b ≥ 2c
    have : 0 ≤ bc := hbc0
    simpa [h_bc_eq] using this
  have hb_ge_6 : 6 ≤ b := by
    -- substitute c = 26 - 4b
    have hb_ge_52_over_9 : 9 * b ≥ 52 := by
      have := hb_ge_2c
      -- b ≥ 2*(26 - 4b)
      have : b ≥ 2 * (26 - 4 * b) := by simpa [hc_def]
      linarith
    -- Prove by contradiction: if b ≤ 5 then 9b ≤ 45 < 52
    by_contra h
    have hb_le_5 : b ≤ 5 := by
      -- h : ¬ (6 ≤ b)  ⇒ b < 6  ⇒ b ≤ 5
      have hb_lt_6 : b < 6 := lt_of_not_ge h
      exact (Int.lt_add_one_iff.mp hb_lt_6)
    have : 9 * b ≤ 45 := by linarith
    have : False := by linarith [hb_ge_52_over_9, this]
    exact this.elim

  -- Conclude b = 6
  exact le_antisymm hb_le_6 hb_ge_6
