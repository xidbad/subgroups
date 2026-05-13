import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup


open MatrixGroups Matrix Complex

variable (n : ℕ) [NeZero n]


-- [位数2の巡回群] --

def I₂ : SL(2, ℂ) := by
  refine ⟨(1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
  simp

def minusI₂ : SL(2, ℂ) := by
  refine ⟨(-1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
  simp [det_fin_two]

lemma aux : minusI₂⁻¹ = minusI₂ := by
  have h : minusI₂ * minusI₂ = 1 := by
    simp [minusI₂]
    aesop
  apply inv_eq_iff_mul_eq_one.mpr h

instance sl_cyclic : Subgroup SL(2, ℂ) where
  carrier := {I₂, minusI₂}                    -- {I₂, -I₂} が SL(2, ℂ) の部分群であること

  one_mem' := by left; rfl                    -- 単位元が含まれること

  mul_mem' := by                              -- 乗法に関して閉じていること
    intro A B HA HB
    simp [I₂, minusI₂] at *
    rcases HA with rfl | rfl                  -- A = I₂ ∨ A = -I₂
    · rcases HB with rfl | rfl                -- A = I₂ ∧ (B = I₂ ∨ B = -I₂)
      · left                                  -- A = I₂, B = I₂ の場合 A * B = I₂
        simp; rfl                             -- 左辺の type は Matrix 2 2 ℂ かつ行列式が 1, 右辺は SL(2,ℂ)
      · right                                 -- A = I₂, B = -I₂ の場合 A * B = -I₂
        simp; rfl
    · rcases HB with rfl | rfl                -- A = -I₂ ∧ (B = I₂ ∨ B = -I₂)
      · right                                 -- A = -I₂, B = I₂ の場合 A * B = -I₂
        simp; rfl
      · left; aesop                           -- A = -I₂, B = -I₂ の場合 A * B = I₂

  inv_mem' := by                              -- 逆元に関して閉じていること
    intro x hx
    rcases hx with hid | hminusid             -- x = I₂ ∨ x = -I₂
    · left                                    -- x = I₂ の場合 x⁻¹ = I₂
      rw [hid]; simp [I₂]
      aesop
    · rw [hminusid]                           -- x = -I₂ の場合 x⁻¹ = -I₂
      simp [I₂]
      right; rw [aux]


-- [位数nの巡回群] --

noncomputable def ζ : ℂ := exp (2 * (Real.pi : ℂ) * I / n)  -- ζ = e^(2πi/n)

-- 1. 生成元 M : 回転に対応する行列
noncomputable def M : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![ζ n, (ζ n)⁻¹]  -- !![ζ n, 0; 0, (ζ n)⁻¹]
  ⟨M, by simp [M, ζ]⟩

-- A n のべき乗全体の集合（Set）を定義
def cyclicSet : Set (SL(2, ℂ)) :=
  {g | ∃ k : ℤ, g = M n ^ k}

-- cyclicSet が SL(2, ℂ)の部分群であること
instance cyclic_subgroup : Subgroup SL(2, ℂ) where
  carrier := cyclicSet n

  one_mem' := ⟨0, by simp only [zpow_zero]⟩  -- k = 0

  mul_mem' := by               -- A n ^ k * A n ^ m = A n ^ (k + m)
    intro a b ⟨k, hk⟩ ⟨m, hm⟩
    use k + m
    rw [hk, hm, zpow_add]

  inv_mem' := by       -- (A n ^ k)⁻¹ = A n ^ (-k)
    intro a ⟨k, hk⟩
    use -k
    rw [hk, zpow_neg]

-- 2. 巡回群から SL(2, ℂ) への群準同型
noncomputable def cyclicSubgroup : Subgroup SL(2, ℂ) :=
  Subgroup.zpowers (M n)  -- M n を生成元とする巡回群, Subgroup.closure {M n}

-- 3. この部分群が位数 n の巡回群であることを示す
theorem finite_cyclic_subgroup_exists :
    ∃ (G : Subgroup SL(2, ℂ)), IsCyclic G ∧ Nat.card G = n := by
  -- let G := cyclicSubgroup n
  use cyclicSubgroup n
  constructor
  · exact Subgroup.isCyclic_zpowers (M n) -- zpowers で生成されているので定義から巡回群
  · rw [cyclicSubgroup, Nat.card_zpowers (M n)]  -- M n のみで生成される → 位数が元の位数と等しい
    · rw [orderOf_eq_iff]
      constructor
      · rw [M]
        ext i j
        simp [diagonal_pow]
        fin_cases i <;> fin_cases j <;> simp [ζ, ← exp_nsmul, ← mul_div_assoc]
        <;> rw [mul_comm, mul_div_assoc, div_self, mul_one, exp_two_pi_mul_I]
        <;> exact NeZero.out
      · intro k hk kpos
        contrapose! hk
        sorry
      · exact Nat.pos_of_neZero n


-- [BinaryDihedralGroup₄ₙ] --

noncomputable def ω : ℂ := exp ((Real.pi : ℂ) * I / n)  -- ω = e^(πi/n)

-- 1. 生成元 A : 回転に対応する行列
noncomputable def A : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![ω n, (ω n)⁻¹]  -- !![ω n, 0; 0, (ω n)⁻¹]
  ⟨M, by simp [M, ω]⟩

-- 2. 生成元 j : 四元数の j に相当する行列
noncomputable def j : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
  ⟨M, by simp [det_fin_two, M]⟩

lemma h₁ (k : ℤ) : j * A n ^ k = A n ^ (-k) * j := by
  rw [A, j, zpow_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · rw [adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    sorry
  · sorry
  · sorry
  · sorry

lemma h₂ : j * j = A n ^ n := by
  have h : j * j = minusI₂ := by
    simp [j, minusI₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h, A, minusI₂]
  ext i j
  simp only [neg_apply, SpecialLinearGroup.coe_pow]
  rw [diagonal_pow]
  fin_cases i <;> fin_cases j <;> simp [ω, ← exp_nsmul, ← mul_div_assoc, mul_comm]
  <;> rw [mul_comm, exp_pi_mul_I]
  rw [inv_neg, inv_one]

lemma h₃ (k : ℤ) : j⁻¹ * A n ^ (-k) = A n ^ k * j⁻¹ := by
  have h := h₁ n k
  apply_fun (λ x => j⁻¹ * x * j⁻¹) at h
  simp [← mul_assoc] at h
  rw [h, zpow_neg]

lemma h₄ : j⁻¹ = (A n ^ n)⁻¹ * j := by
  have h := h₂ n
  apply_fun (λ x => x * j⁻¹) at h
  rw [mul_assoc, mul_inv_cancel, mul_one] at h
  nth_rw 2 [h]
  rw [← mul_assoc, inv_mul_cancel, one_mul]

-- バイナリー二面体群の定義
def binary_dihedral_set : Set (SL(2, ℂ)) :=
  {M | ∃ k : ℤ, M = (A n) ^ k ∨ M = ((A n) ^ k) * j}  -- Subgroup.closure {A n, j} : A n と j によって生成される最小の部分群

-- binary_dihedral_set n が SL(2, ℂ) の部分群であること
def binary_dihedral_subgrup : Subgroup SL(2, ℂ) where
  carrier := binary_dihedral_set n

  one_mem' := by
    rw [binary_dihedral_set, Set.mem_setOf_eq]
    use 0; left
    rw [zpow_zero]

  mul_mem' := by
    rintro M N ⟨k, (hMA | hMB)⟩ ⟨l, (hNA | hNB)⟩
    -- rw [binary_dihedral_set, Set.mem_setOf_eq]
    · use k + l; left
      simp only [hMA, hNA]
      rw [zpow_add]
    · use k + l; right
      simp only [hMA, hNB]
      rw [← mul_assoc, zpow_add]
    · use k - l; right
      rw [hMB, hNA]
      rw [mul_assoc, h₁, ← mul_assoc, zpow_sub, zpow_neg]
    · use k - l + n; left
      rw [hMB, hNB]
      simp [mul_assoc, ← mul_assoc j, h₁, h₂ n, zpow_sub, zpow_add]

  inv_mem' := by
    rintro M ⟨k, (hMA | hMB)⟩
    · use -k; left
      simp only [hMA, A, zpow_neg]
    · use k - n; right
      rw [hMB, _root_.mul_inv_rev, ← zpow_neg, h₃, h₄ n, ← mul_assoc, mul_left_inj]
      rw [zpow_sub, zpow_natCast]


-- [BinaryTetrahedralGroup₂₄] --

def i : SL(2, ℂ) := ⟨!![I, 0; 0, -I], by simp⟩  -- 四元数のi

noncomputable def B : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![(1/2)*(1+I), (1/2)*(1+I); (1/2)*(-1+I), (1/2)*(1-I)]
  ⟨M, by simp [M, det_fin_two]; ring_nf; rw [I_sq]; norm_num⟩

/-- BT24 を SL(2, ℂ) の部分群として定義する -/
def BT24 : Subgroup SL(2, ℂ) :=
  Subgroup.closure {i, j, B}

-- BT24 が部分群であることは、Subgroup.closure の定義から自動的に導かれる

instance : Subgroup SL(2, ℂ) where
  carrier := {M | M ∈ BT24}

  one_mem' := BT24.one_mem

  mul_mem' := by
    intro a b ha hb
    exact BT24.mul_mem ha hb

  inv_mem' := by
    intro x hx
    exact BT24.inv_mem hx


-- [BinaryOctahedralGroup₄₈] --

-- 八面体群特有の生成元 (1+i)/√2 に相当する行列
noncomputable def C : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![(1/(Real.sqrt 2))*(1 + I), 0; 0, (1/(Real.sqrt 2))*(1 - I)]
  ⟨M, by simp [M]; field_simp; ring_nf; rw [I_sq]; norm_num; rw [← Complex.ofReal_pow]; rw [Real.sq_sqrt (by norm_num)]; norm_num⟩


noncomputable def BO48 : Subgroup SL(2, ℂ) :=
  Subgroup.closure {i, j, B, C}

instance : Subgroup SL(2, ℂ) where
  carrier := {M | M ∈ BO48}

  one_mem' := BO48.one_mem

  mul_mem' := by
    intro a b ha hb
    exact BO48.mul_mem ha hb

  inv_mem' := by
    intro x hx
    exact BO48.inv_mem hx


-- [BinaryIcosahedralGroup₁₂₀] --
noncomputable def D : SL(2, ℂ) :=
  let phi : ℂ := (1 + Real.sqrt 5) / 2
  let inv2 : ℂ := (1 : ℂ) / 2
  let M : Matrix (Fin 2) (Fin 2) ℂ := inv2 • !![phi + I * (phi - 1), 1; -1, phi - I * (phi - 1)]
  ⟨M, by simp [M, phi, inv2]; field_simp; norm_num; ring_nf; rw [I_sq]; norm_num; rw [← Complex.ofReal_pow]; rw [Real.sq_sqrt (by norm_num)]; norm_num⟩


/-- BI120 を生成元からなる部分群として定義 -/
noncomputable def BI120 : Subgroup SL(2, ℂ) :=
  Subgroup.closure {i, j, B, D}

instance : Subgroup SL(2, ℂ) where
  carrier := {M | M ∈ BI120}

  one_mem' := BI120.one_mem

  mul_mem' := by
    intro a b ha hb
    exact BI120.mul_mem ha hb

  inv_mem' := by
    intro x hx
    exact BI120.inv_mem hx


-- [SU(2)の性質] --

def SU (n : ℕ) := specialUnitaryGroup (Fin n) ℂ

instance SU2 : Subgroup SL(2, ℂ) where
  carrier := {M : SL(2, ℂ) | M.val ∈ SU 2}  -- SU(2) の行列を SL(2, ℂ) の部分集合として定義

  one_mem' := by simp[SU]                 -- 単位元が含まれること

  mul_mem' := by                           -- 乗法に関して閉じていること
    intro A B HA HB
    simp only [Set.mem_setOf_eq] at *
    sorry

  inv_mem' := by                          -- 逆元に関して閉じていること
    intro A HA
    simp [SU] at *
    sorry


theorem conjugate_finite_subgroup_into_SU2 (G : Subgroup SL(2, ℂ)) [Finite G] :
    ∃ P : SL(2, ℂ), ∀ g ∈ G, (P * g * P⁻¹ : SL(2, ℂ)).val ∈ SU 2 := by
  sorry


#min_imports
