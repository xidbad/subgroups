import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Int.Star
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

open MatrixGroups Matrix Complex SpecialLinearGroup

noncomputable section

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


variable (n : ℕ) (hn : n ≠ 0)


-- [位数nの巡回群] --

def ζ : ℂ := exp (2 * (Real.pi : ℂ) * I / n)  -- ζ = e^(2πi/n)

-- 1. 生成元 M : 回転に対応する行列
def M : SL(2, ℂ) :=
  let N : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(ζ n), (ζ n)⁻¹]  -- !![ζ n, 0; 0, (ζ n)⁻¹]
  ⟨N, by simp [N, ζ]⟩

-- A n のべき乗全体の集合（Set）を定義
def cyclicSet : Set (SL(2, ℂ)) := {g | ∃ k : ℤ, g = M n ^ k}

-- cyclicSet が SL(2, ℂ)の部分群であること
instance cyclic_subgroup : Subgroup SL(2, ℂ) where
  carrier := cyclicSet n

  one_mem' := ⟨0, by simp only [zpow_zero]⟩  -- k = 0

  mul_mem' := by               -- A n ^ k * A n ^ m = A n ^ (k + m)
    intro a b ⟨k, hk⟩ ⟨m, hm⟩
    use k + m
    rw [hk, hm, _root_.zpow_add]

  inv_mem' := by       -- (A n ^ k)⁻¹ = A n ^ (-k)
    intro a ⟨k, hk⟩
    use -k
    rw [hk, _root_.zpow_neg]

-- 2. 巡回群から SL(2, ℂ) への群準同型
def cyclicSubgroup : Subgroup SL(2, ℂ) :=
  Subgroup.zpowers (M n)  -- M n を生成元とする巡回群, Subgroup.closure {M n}

lemma pow_ne_one (k : ℕ) (hk : 0 < k ∧ k < n) (hlt : 1 < n) :
    (exp (2 * Real.pi * I / n)) ^ k ≠ 1 := by
  have hprim : IsPrimitiveRoot (exp (2 * Real.pi * I / n)) n := by
    refine (isPrimitiveRoot_iff (exp (2 * Real.pi * I/n)) n ?_).mpr ?_
    · exact Nat.ne_zero_of_lt hlt
    · use 1
      constructor
      · assumption
      · refine exists_prop.mpr ?_
        constructor
        · exact Nat.gcd_one_left n
        · congr; simp only [Nat.cast_one, one_div]
  obtain ⟨h1, h2⟩ := hprim
  specialize h2 k
  by_contra
  specialize h2 this
  obtain ⟨m, hm⟩ := h2
  rw [hm] at hk
  obtain ⟨pos, div⟩ := hk
  have aux : m ≥ 1 := by
    refine Nat.one_le_iff_ne_zero.mpr ?_
    by_contra
    rw [this] at pos
    norm_num at pos
  have aux2 : n * m ≥ n := by exact Nat.le_mul_of_pos_right n aux
  linarith

-- 3. この部分群が位数 n の巡回群であることを示す
theorem finite_cyclic_subgroup_exists (hn : n ≠ 0) :
    ∃ (G : Subgroup SL(2, ℂ)), IsCyclic G ∧ Nat.card G = n := by
  use cyclicSubgroup n
  constructor
  · exact Subgroup.isCyclic_zpowers (M n)        -- zpowers で生成されているので定義から巡回群
  · rw [cyclicSubgroup, Nat.card_zpowers (M n)]  -- M n のみで生成される → 位数が元の位数と等しい
    · rw [orderOf_eq_iff]
      constructor
      · rw [M]
        ext i j
        simp [diagonal_pow]
        fin_cases i <;> fin_cases j <;> simp [ζ, ← exp_nsmul, ← mul_div_assoc]
        <;> rw [mul_comm, mul_div_assoc, div_self, mul_one, exp_two_pi_mul_I]
        <;> exact Nat.cast_ne_zero.mpr hn
      · intro k hk kpos heq
        rw [M] at heq
        have h : ζ n ^ k = 1 := by
          apply_fun (fun M : SL(2, ℂ) => (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) at heq
          simp [one_apply_eq, diagonal_pow] at heq
          exact heq
        absurd h
        rw [ζ]
        apply pow_ne_one
        use kpos
        contrapose! h
        interval_cases n
        · linarith
        · linarith
      · exact Nat.zero_lt_of_ne_zero hn


-- [BinaryDihedralGroup₄ₙ] --

def ω : ℂ := exp ((Real.pi : ℂ) * I / n)  -- ω = e^(πi/n)

-- 1. 生成元 A : 回転に対応する行列
def A : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![ω n, (ω n)⁻¹]  -- !![ω n, 0; 0, (ω n)⁻¹]
  ⟨M, by simp [M, ω]⟩

-- 2. 生成元 j : 四元数の j に相当する行列
def j : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
  ⟨M, by simp [det_fin_two, M]⟩


lemma h₁ (k : ℤ) : j * A n ^ k = A n ^ (-k) * j := by
  have h₀ : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  have h₁ : Finset.univ.erase (1 : Fin 2) = {0} := by decide
  induction k with
  | zero =>
  · rw [zpow_zero, mul_one, neg_zero, zpow_zero, one_mul]
  | succ a ha =>
  · rw [_root_.zpow_add, zpow_one, ← mul_assoc, ha, neg_add, _root_.zpow_add, _root_.zpow_neg]
    rw [mul_assoc, mul_assoc, mul_right_inj, _root_.zpow_neg, zpow_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp [j, A] <;> simp [h₀, h₁]
  | pred a ha =>
  · rw [_root_.zpow_sub, zpow_one, ← mul_assoc, ha, neg_neg, neg_sub, sub_neg_eq_add]
    rw [add_comm, _root_.zpow_add, zpow_one, mul_assoc, mul_assoc, mul_right_inj]
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, j]
    <;> simp [h₀, h₁]

lemma h₂ (hn : n ≠ 0) : j * j = A n ^ n := by
  have h : j * j = minusI₂ := by
    simp [j, minusI₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h, A, minusI₂]
  ext i j
  simp only [neg_apply, SpecialLinearGroup.coe_pow]
  rw [diagonal_pow]
  fin_cases i <;> fin_cases j <;> simp [ω, ← exp_nsmul, ← mul_div_assoc]
  <;> rw [mul_comm, mul_div_assoc, div_self (by simp [hn]), mul_one, exp_pi_mul_I]
  rw [inv_neg, inv_one]

lemma h₃ (k : ℤ) : j⁻¹ * A n ^ (-k) = A n ^ k * j⁻¹ := by
  have h := h₁ n k
  apply_fun (λ x => j⁻¹ * x * j⁻¹) at h
  simp [← mul_assoc] at h
  rw [h, _root_.zpow_neg]

lemma h₄ (hn : n ≠ 0) : j⁻¹ = (A n ^ n)⁻¹ * j := by
  have h := h₂ n hn
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
      rw [_root_.zpow_add]
    · use k + l; right
      simp only [hMA, hNB]
      rw [← mul_assoc, _root_.zpow_add]
    · use k - l; right
      rw [hMB, hNA]
      rw [mul_assoc, h₁, ← mul_assoc, _root_.zpow_sub, _root_.zpow_neg]
    · use k - l + n; left
      rw [hMB, hNB]
      simp [mul_assoc, ← mul_assoc j, h₁, h₂ n hn, _root_.zpow_sub, _root_.zpow_add]

  inv_mem' := by
    rintro M ⟨k, (hMA | hMB)⟩
    · use -k; left
      simp only [hMA, A, _root_.zpow_neg]
    · use k - n; right
      rw [hMB, _root_.mul_inv_rev, ← _root_.zpow_neg, h₃, h₄ n hn, ← mul_assoc, mul_left_inj]
      rw [_root_.zpow_sub, _root_.zpow_natCast]


-- [BinaryTetrahedralGroup₂₄] --

def i : SL(2, ℂ) := ⟨!![I, 0; 0, -I], by simp⟩  -- 四元数のi

def B : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![(1/2)*(1+I), (1/2)*(1+I); (1/2)*(-1+I), (1/2)*(1-I)]
  ⟨M, by simp [M, det_fin_two]; ring_nf; rw [I_sq]; norm_num⟩

/-- BT24 を SL(2, ℂ) の部分群として定義する -/
def BT24 : Subgroup SL(2, ℂ) :=
  Subgroup.closure {i, j, B}

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
def C : SL(2, ℂ) :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![(1/(Real.sqrt 2))*(1 + I), 0; 0, (1/(Real.sqrt 2))*(1 - I)]
  ⟨M, by simp [M]; ring_nf; rw [I_sq]; norm_num; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num⟩


def BO48 : Subgroup SL(2, ℂ) :=
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
def D : SL(2, ℂ) :=
  let phi : ℂ := (1 + Real.sqrt 5) / 2
  let inv2 : ℂ := (1 : ℂ) / 2
  let M : Matrix (Fin 2) (Fin 2) ℂ := inv2 • !![phi + I * (phi - 1), 1; -1, phi - I * (phi - 1)]
  ⟨M, by simp [M, phi, inv2]; ring_nf; rw [I_sq]; norm_num; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num⟩


/-- BI120 を生成元からなる部分群として定義 -/
def BI120 : Subgroup SL(2, ℂ) :=
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

instance : Subgroup SL(2, ℂ) where
  carrier := {M : SL(2, ℂ) | M.val ∈ SU 2}  -- SU(2) の行列を SL(2, ℂ) の部分集合として定義

  one_mem' := by  -- 単位元が含まれること
    simp only [Set.mem_setOf_eq, SpecialLinearGroup.coe_one, one_mem]

  mul_mem' := by  -- 乗法に関して閉じていること
    intro A B HA HB
    rw [SU, Set.mem_setOf_eq] at *
    -- rw [Set.mem_setOf_eq, SpecialLinearGroup.coe_mul]
    exact mul_mem HA HB

  inv_mem' := by  -- 逆元に関して閉じていること
    intro A HA
    constructor
    · rcases HA with ⟨hA_unitary, hA_det⟩
      have := hA_unitary
      simp only [SetLike.mem_coe] at *
      rw [mem_unitaryGroup_iff] at hA_unitary
      -- apply inv_eq_right_inv at hA_unitary
      apply_fun (λ x => A⁻¹.val * x) at hA_unitary
      rw [mul_one, ← mul_assoc, ← coe_mul, inv_mul_cancel, coe_one, one_mul] at hA_unitary
      -- rw [coe_inv'] at hA_unitary
      rw [← hA_unitary, Unitary.star_mem_iff]
      exact this
    · exact A⁻¹.prop

-- -- もう一つの部分群の定義を使う
def SU2_subgroup : Subgroup SL(2, ℂ) := by
  refine Subgroup.ofDiv {M : SL(2, ℂ) | M.val ∈ SU 2} ?_ ?_

    -- 2. 空ではない（1 を含む）の証明
  · have := one_mem (SU 2); exact ⟨1, this⟩

    -- 3. A ∈ SU 2, B ∈ SU 2 ⇒ A * B⁻¹ ∈ SU 2 の証明
  · intro A HA B HB
    rw [Set.mem_setOf_eq] at *
    have hB_inv : B⁻¹.val ∈ SU 2 := by
      constructor
      · rcases HB with ⟨hB_unitary, hB_det⟩
        have := hB_unitary
        simp only [SetLike.mem_coe] at *
        rw [mem_unitaryGroup_iff] at hB_unitary
        apply_fun (λ x => B⁻¹.val * x) at hB_unitary
        rw [mul_one, ← mul_assoc, ← coe_mul, inv_mul_cancel, coe_one, one_mul] at hB_unitary
        rw [← hB_unitary, Unitary.star_mem_iff]
        exact this
      · exact B⁻¹.prop
    exact mul_mem HA hB_inv

instance : Subgroup SL(2, ℂ) := SU2_subgroup

-- n*n の場合
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (ρ : Representation ℂ G V)  -- ρ : G →* (V →ₗ[ℂ] V) は G の ℂ-線型表現

/-- The G-averaged inner product: `⟨u, v⟩_G = (1/|G|) ∑_{g ∈ G} ⟨ρ(g)(u), ρ(g)(v)⟩`. -/
def averagedInner (u v : V) : ℂ :=
  ((Fintype.card G : ℂ)⁻¹) * ∑ g : G, @inner ℂ V _ (ρ g u) (ρ g v)

set_option quotPrecheck false

notation "⟪"u", "v"⟫_G" => averagedInner ρ u v


-- 第一引数の加法性
lemma averagedInner_add_left (u v w : V) : ⟪u + v, w⟫_G = ⟪u, w⟫_G + ⟪v, w⟫_G := by
  simp [averagedInner, map_add, Finset.sum_add_distrib, ← mul_add]

-- 第一引数のスカラー同次性
lemma averagedInner_smul_left (c : ℂ) (u v : V) :
    ⟪c • u, v⟫_G = (starRingEnd ℂ) c * ⟪u, v⟫_G := by
  simp [averagedInner, mul_left_comm, Finset.mul_sum]
  ac_rfl

-- 共役対称性
lemma averagedInner_conj_symm (u v : V) : ⟪u, v⟫_G = (starRingEnd ℂ) (⟪v, u⟫_G) := by
  simp only [averagedInner, map_mul, map_inv₀, map_natCast, map_sum, inner_conj_symm]

-- 非負性
lemma averagedInner_self_nonneg (u : V) : 0 ≤ (⟪u, u⟫_G).re := by
  simp [averagedInner]
  apply mul_nonneg
  · exact inv_nonneg.2 (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro g gmem; norm_cast
    exact sq_nonneg _
  -- exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => by norm_cast; positivity)

-- 正定値性
lemma averagedInner_self_eq_zero {u : V} (h : ⟪u, u⟫_G = 0) : u = 0 := by
  simp_all [averagedInner, inner_self_eq_norm_sq_to_K]
  norm_cast at h
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h
  simpa using h 1 (Finset.mem_univ 1)


-- G-不変性(ユニタリ性)
theorem averagedInner_invariant (g : G) (u v : V) :
    ⟪ρ g u, ρ g v⟫_G = ⟪u, v⟫_G := by
  unfold averagedInner
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulRight g)]; simp [mul_assoc]


@[reducible]
def averagedInnerCore : InnerProductSpace.Core ℂ V where
  inner := averagedInner ρ
  conj_inner_symm := by
    intro x y
    exact Eq.symm (averagedInner_conj_symm ρ x y)
  re_inner_nonneg := by
    intro x
    exact averagedInner_self_nonneg ρ x
  add_left := by
    intro x y z
    exact averagedInner_add_left ρ x y z
  smul_left := by
    intro x y r
    exact averagedInner_smul_left ρ r x y
  definite := by
    intro x h
    exact averagedInner_self_eq_zero ρ h


/-- H = (1/|G|) * Σ_{g ∈ G} gᴴ * g, where gᴴ = conjTranspose g. -/
def gramMatrix (G : Subgroup SL(2, ℂ)) [Fintype G] : Matrix (Fin 2) (Fin 2) ℂ :=
  (((Fintype.card G : ℂ)⁻¹) : ℂ) • ∑ g : G, (g : SL(2, ℂ)).val.conjTranspose * (g : SL(2, ℂ)).val


/-- The Gram matrix is Hermitian. 随伴行列が元と等しい.-/
lemma gramMatrix_isHermitian (G : Subgroup SL(2, ℂ)) [Fintype G] :
    (gramMatrix G).IsHermitian := by
  unfold gramMatrix; simp [IsHermitian, Matrix.conjTranspose_sum]


/-- G-invariance of the Gram matrix: gᴴ H g = H for all g ∈ G. G-不変性 -/
lemma gramMatrix_conjTranspose_mul (G : Subgroup SL(2, ℂ)) [Fintype G] (g : SL(2, ℂ))
    (hg : g ∈ G) : g.val.conjTranspose * gramMatrix G * g.val = gramMatrix G := by
  have h_inner : (g.val.conjTranspose * gramMatrix G * g.val) =
      (((Fintype.card G : ℂ)⁻¹) : ℂ) • ∑ h : G,
        (h.val * g.val).conjTranspose * (h.val * g.val) := by
    simp [gramMatrix, mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul]
  rw [h_inner]
  refine' congr_arg _ _
  apply Finset.sum_bij (fun h _ => ⟨h.val * g, by exact G.mul_mem h.2 hg⟩)
  all_goals generalize_proofs at *
  · aesop
  · aesop
  · exact fun b _ => ⟨⟨b.val * g⁻¹, by simpa using G.mul_mem b.2 (G.inv_mem hg)⟩,
      Finset.mem_univ _, by ext; simp only [inv_mul_cancel_right]⟩
  · aesop


-- The Gram matrix has positive eigenvalues. 正定値性
lemma gramMatrix_eigenvalues_pos (G : Subgroup SL(2, ℂ)) [Fintype G] [Nontrivial G]
    (i : Fin 2) : 0 < (gramMatrix_isHermitian G).eigenvalues i := by
  have h_pos_def : ∀ v : Fin 2 → ℂ, v ≠ 0 → 0 < (∑ x : G, (star v ⬝ᵥ (x.val.val.conjTranspose * x.val.val).mulVec v)).re := by
    intro v hv_ne_zero
    have h_pos_def : 0 < (∑ x : G, (∑ i : Fin 2, star (x.val.val.mulVec v i) * (x.val.val.mulVec v i))).re := by
      simp
      refine' lt_of_lt_of_le _ (Finset.single_le_sum (fun x _ => _) (Finset.mem_univ 1)) <;> norm_num [hv_ne_zero]
      · contrapose! hv_ne_zero; ext i; fin_cases i <;> norm_num [Complex.ext_iff] at * <;> constructor <;> nlinarith
      · nlinarith
    convert h_pos_def using 3 ; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring
    simp [Matrix.mul_apply, Fin.sum_univ_succ]; ring
  contrapose! h_pos_def;
  refine' ⟨(Matrix.IsHermitian.eigenvectorBasis (gramMatrix_isHermitian G)) i, _, _ ⟩ <;> simp_all [Matrix.IsHermitian.eigenvalues_eq];
  · exact ne_of_apply_ne Norm.norm (by simp);
  · convert mul_nonpos_of_nonpos_of_nonneg h_pos_def (Nat.cast_nonneg (Fintype.card G)) using 1;
    unfold gramMatrix; norm_num [Matrix.mulVec, dotProduct]; ring
    simp [Matrix.sum_apply, Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_comm]; ring


/-- Key algebraic lemma: if Bᴴ * B = H and gᴴ * H * g = H,
    then (B * g * B⁻¹) is unitary (i.e., M * Mᴴ = 1). B * g * B⁻¹ がユニタリ -/
lemma unitary_of_conjTranspose_invariant
    (B g H : Matrix (Fin 2) (Fin 2) ℂ) (hB_inv : IsUnit B)
    (hBH : B.conjTranspose * B = H)
    (hgH : g.conjTranspose * H * g = H) :
    (B * g * B⁻¹) * (B * g * B⁻¹).conjTranspose = 1 := by
  simp_all [mul_assoc, Matrix.isUnit_iff_isUnit_det]
  simp_all [← mul_assoc, ← hBH]
  simp_all [← Matrix.mul_assoc, mul_eq_one_comm]
  simp_all [Matrix.conjTranspose_nonsing_inv]


/- There exists a matrix B with B^* B = H and B invertible,
    given H is Hermitian with all positive eigenvalues. -/
lemma exists_conjTranspose_mul_self_eq
    (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian) (hpos : ∀ i : Fin 2, 0 < hH.eigenvalues i) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℂ, B.conjTranspose * B = H ∧ IsUnit B := by
  -- Since $D$ has positive entries on the diagonal, it is Hermitian with positive eigenvalues. Therefore, $D^{1/2}$ exists and is invertible.
  obtain ⟨D_half, hD_half⟩ : ∃ D_half : Matrix (Fin 2) (Fin 2) ℂ, D_half.conjTranspose * D_half = Matrix.diagonal (ofReal ∘ (hH.eigenvalues)) ∧ IsUnit D_half := by
    refine' ⟨Matrix.diagonal fun i => Real.sqrt (hH.eigenvalues i), _, _ ⟩ <;> simp_all [Matrix.isUnit_iff_isUnit_det];
    · exact ⟨mod_cast Real.mul_self_sqrt hpos.1.le, mod_cast Real.mul_self_sqrt hpos.2.le ⟩;
    · exact ⟨ne_of_gt <| Real.sqrt_pos.mpr hpos.1, ne_of_gt <| Real.sqrt_pos.mpr hpos.2 ⟩;
  -- By the spectral theorem, we can write $H = U * D * U^{-1}$ where $U$ is unitary and $D$ is diagonal with positive entries.
  obtain ⟨U, D, hU, hD⟩ : ∃ U : Matrix (Fin 2) (Fin 2) ℂ, ∃ D : Matrix (Fin 2) (Fin 2) ℂ, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧ D = Matrix.diagonal (ofReal ∘ (hH.eigenvalues)) ∧ H = U * D * U.conjTranspose := by
    refine' ⟨hH.eigenvectorUnitary, _, _, _, rfl, _ ⟩;
    · simp [Matrix.IsHermitian.eigenvectorUnitary]
    · simp [Matrix.IsHermitian.eigenvectorUnitary]
    · convert hH.spectral_theorem using 1
  refine' ⟨D_half * Uᴴ, _, _ ⟩ <;> simp_all [← mul_assoc]
  · simp [mul_assoc, hD_half.1]
  · exact IsUnit.of_mul_eq_one_right Uᴴ hU


/- If B is invertible and BgB⁻¹ is unitary for all g ∈ G (a subgroup of SL(2,ℂ)),
    then there exists P ∈ SL(2,ℂ) with PgP⁻¹ ∈ SU(2) for all g ∈ G. -/
lemma exists_SL_from_invertible (G : Subgroup SL(2, ℂ)) [Fintype G]
    (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : IsUnit B)
    (hU : ∀ g ∈ G, (B * (g : SL(2, ℂ)).val * B⁻¹) *
      (B * (g : SL(2, ℂ)).val * B⁻¹).conjTranspose = 1) :
    ∃ P : SL(2, ℂ), ∀ g ∈ G, (P * g * P⁻¹ : SL(2, ℂ)).val ∈ SU 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c^2 = B.det ∧ c ≠ 0 := by
    simp_all [Matrix.isUnit_iff_isUnit_det]
    exact ⟨(det B) ^ (1 / 2 : ℂ), by rw [← Complex.cpow_nat_mul]; norm_num, by aesop⟩
  refine' ⟨⟨c⁻¹ • B, _ ⟩, _⟩
  all_goals simp_all [sq]
  · grind
  · intro g hg; specialize hU g hg; simp_all [Matrix.inv_def, Matrix.adjugate_smul]
    constructor
    · simp_all [← mul_assoc, ← smul_assoc, Matrix.mem_unitaryGroup_iff]
      convert hU using 2; simp [← hc.1, mul_comm]
      ring
    · simp_all [← mul_assoc, ← pow_two, Matrix.det_adjugate]
      rw [inv_mul_cancel₀]; aesop

/-- Main theorem: every finite subgroup of SL(2,ℂ) can be conjugated into SU(2). -/
theorem conjugate_finite_subgroup_into_SU2 (G : Subgroup SL(2, ℂ)) [Finite G] :
    ∃ P : SL(2, ℂ), ∀ g ∈ G, (P * g * P⁻¹ : SL(2, ℂ)).val ∈ SU 2 := by
  cases nonempty_fintype G
  -- Handle trivial case
  by_cases hG : Nontrivial G
  · -- Get the Gram matrix and its properties
    have hH := gramMatrix_isHermitian G
    have hpos := gramMatrix_eigenvalues_pos G
    -- Get B with B^* B = gramMatrix G
    obtain ⟨B, hBH, hB_inv⟩ := exists_conjTranspose_mul_self_eq _ hH hpos
    -- Show BgB⁻¹ is unitary for all g ∈ G
    have hU : ∀ g ∈ G, (B * (g : SL(2, ℂ)).val * B⁻¹) *
        (B * (g : SL(2, ℂ)).val * B⁻¹).conjTranspose = 1 := by
      intro g hg
      exact unitary_of_conjTranspose_invariant B g.val (gramMatrix G) hB_inv hBH
        (gramMatrix_conjTranspose_mul G g hg)
    -- Get P ∈ SL(2,ℂ)
    exact exists_SL_from_invertible G B hB_inv hU
  · -- Trivial group case: P = 1 works
    have : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG
    exact ⟨1, fun g hg => by
      have h := Subsingleton.elim (⟨g, hg⟩ : G) ⟨1, G.one_mem⟩
      have : g = 1 := congr_arg Subtype.val h
      subst this; simp⟩


end

#min_imports
