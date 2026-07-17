import Mathlib.Algebra.Quaternion
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup


open MatrixGroups Matrix Complex SpecialLinearGroup Quaternion

set_option quotPrecheck false


noncomputable section


variable (G : Subgroup SL(2, ℂ)) [Fintype G]


notation "⟪"u", "v"⟫" => star u ⬝ᵥ v  -- 標準内積

/- `Definition8` -/
abbrev SU (n : ℕ) := specialUnitaryGroup (Fin n) ℂ


/- `Proposition10` -/
/-- 部分群 `G ≤ SL(2, ℂ)` の `ℂ² = (Fin 2 → ℂ)` 上への標準表現：
`ρ g u = g *ᵥ u`（`g` を行列とみなした行列・ベクトル積）。 -/
def ρ {G : Subgroup SL(2, ℂ)} (g : G) (u : Fin 2 → ℂ) : Fin 2 → ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u


/-- `G`-平均エルミート内積
`⟪u, v⟫_G = (1/|G|) ∑_{g ∈ G} ⟪ρ g u, ρ g v⟫`。 -/
def avgInner (u v : Fin 2 → ℂ) : ℂ := (Fintype.card G : ℂ)⁻¹ * ∑ g : G, ⟪ρ g u, ρ g v⟫

notation "⟪"u", "v"⟫_G" => avgInner G u v


-- 第一引数の加法性
lemma avgInner_add_left (u v w : Fin 2 → ℂ) : ⟪u + v, w⟫_G = ⟪u, w⟫_G + ⟪v, w⟫_G := by
  simp [avgInner, ρ, mulVec_add, Finset.sum_add_distrib]; ring

-- 第一引数のスカラー同次性
lemma avgInner_smul_left (c : ℂ) (u v : Fin 2 → ℂ) :
    ⟪c • u, v⟫_G = (starRingEnd ℂ) c * ⟪u, v⟫_G := by
  simp [avgInner, ρ, mulVec_smul, Finset.mul_sum _ _ _, mul_left_comm]

-- 共役対称性
lemma avgInner_conj_symm (u v : Fin 2 → ℂ) : ⟪u, v⟫_G = (starRingEnd ℂ) (⟪v, u⟫_G) := by
  simp [avgInner, mul_comm]

-- 非負性
lemma avgInner_self_nonneg (u : Fin 2 → ℂ) : 0 ≤ (⟪u, u⟫_G).re := by
  simp_all [avgInner, ρ]
  apply mul_nonneg
  · exact inv_nonneg.2 (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro g gmem
    apply add_nonneg
    · apply add_nonneg
      · apply mul_self_nonneg
      · apply mul_self_nonneg
    · apply add_nonneg
      · apply mul_self_nonneg
      · apply mul_self_nonneg


-- 正定値性
lemma avgInner_self_eq_zero {u : Fin 2 → ℂ} (h : ⟪u, u⟫_G = 0) : u = 0 := by
  contrapose! h
  refine' ne_of_apply_ne Complex.re _
  simp [avgInner]
  refine' ne_of_gt (lt_of_lt_of_le _ (Finset.single_le_sum (fun x _ => _) (Finset.mem_univ 1)))
  · unfold ρ; simp
    exact not_le.mp fun h' => h <| by ext i; fin_cases i <;> norm_num [Complex.ext_iff] <;> constructor <;> nlinarith
  · nlinarith


-- G-不変性(ユニタリ性)
theorem avgInner_invariant (g : G) (u v : Fin 2 → ℂ) : ⟪ρ g u, ρ g v⟫_G = ⟪u, v⟫_G := by
  simp only [avgInner, ρ]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulRight g)]
  simp [Matrix.mulVec_mulVec, dotProduct_comm]


@[reducible]
def avgInnerCore : InnerProductSpace.Core ℂ (Fin 2 → ℂ) where
  inner := avgInner G
  conj_inner_symm := by
    intro x y
    exact Eq.symm (avgInner_conj_symm G x y)
  re_inner_nonneg := by
    intro x
    exact avgInner_self_nonneg G x
  add_left := by
    intro x y z
    exact avgInner_add_left G x y z
  smul_left := by
    intro x y r
    exact avgInner_smul_left G r x y
  definite := by
    intro x h
    exact avgInner_self_eq_zero G h


/- ⟪,⟫_G における正規直交基底 v₁, v₂ としたとき, Uv₁ = e₁, Uv₂ = e₂ となるように `U` を取る。
　　平均内積から標準内積へ変換する基底変換行列 -/
theorem conj_mem_SU (g : G) (U : Matrix (Fin 2) (Fin 2) ℂ) (hUinv : IsUnit U.det)
    (hg : ∀ u v, ⟪ρ g u, ρ g v⟫_G = ⟪u, v⟫_G) (hU : ∀ u v, ⟪u, v⟫_G = ⟪(U *ᵥ u), (U *ᵥ v)⟫)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1) : U * g * U⁻¹ ∈ SU 2 := by
  set gm : Matrix (Fin 2) (Fin 2) ℂ := ((g : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) with hgm  -- gm = g.val.val
  -- `U` を経由して、`gm = g` が標準内積を「`U`-座標」で保つことを取り出す。
  have hp : ∀ u v : Fin 2 → ℂ,
      star (U *ᵥ (gm *ᵥ u)) ⬝ᵥ (U *ᵥ (gm *ᵥ v)) = star (U *ᵥ u) ⬝ᵥ (U *ᵥ v) := by  -- gm が標準内積を保つことを `U` を経由して書き換える。
    intro u v
    have h := hg u v
    rw [hU (ρ g u) (ρ g v), hU u v] at h
    exact h
  -- Step 1: 共役 `C = U g U⁻¹` がユニタリであること。
  have h_unitary : (U * gm * U⁻¹)ᴴ * (U * gm * U⁻¹) = 1 := by
    have h_unitary : ∀ x y : Fin 2 → ℂ,
        star x ⬝ᵥ ((U * gm * U⁻¹)ᴴ * (U * gm * U⁻¹)) *ᵥ y = star x ⬝ᵥ y := by  -- xᴴ · ((Cᴴ * C) *ᵥ y) = xᴴ · y
      intro x y
      have h_step1 : star ((U * gm * U⁻¹).mulVec x) ⬝ᵥ (U * gm * U⁻¹).mulVec y = star x ⬝ᵥ y := by  -- ⟪C x, C y⟫ = ⟪x, y⟫
        convert hp (U⁻¹ *ᵥ x) (U⁻¹ *ᵥ y) using 1 <;>
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUinv]
      rw [← h_step1]
      simp [Matrix.dotProduct_mulVec, Matrix.star_mulVec]  -- v · (A *ᵥ w) = (vᴴ ᵥ* A) · w
    ext i j
    specialize h_unitary (Pi.single i 1) (Pi.single j 1)  -- 標準基底 e_i, e_j を代入する。ij成分だけ取り出せる
    fin_cases i <;> fin_cases j <;> simp_all  -- i, j = 0, 1 の場合をそれぞれ計算する。
  -- Step 2: 行列式が `1` であること。
  have hdet2 : (U * gm * U⁻¹).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, hdet, mul_one,
        Ring.mul_inverse_cancel _ hUinv]
  exact Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff'.mpr h_unitary, hdet2⟩


/-  `Quaternion` -/
/- `Definition12` -/
namespace Quaternion

/-- `ℍ[ℝ] : Type := Quaternion ℝ, a + b i + c j + d k (a, b, c, d ∈ ℝ)`
    `⟨a, b, c, d⟩` --/

-- i, j, k の定義
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

def qk : ℍ[ℝ]  := ⟨0, 0, 0, 1⟩


/-- 任意の四元数は実数係数の基底の線形結合として表される。 -/
lemma H_eq (a b c d : ℝ) :
    (⟨a, b, c, d⟩ : ℍ[ℝ]) = a • (1 : ℍ[ℝ]) + b • qi + c • qj + d • qk := by
  ext <;> simp [qi, qj, qk]


/-- 実数体上の4次元ベクトル空間である。 -/
lemma finrank_H : Module.finrank ℝ ℍ[ℝ] = 4 := by
  rw [finrank_eq_four]


/-`The multiplication law` -/

/-- `i² = -1`. -/
lemma qi_mul_qi : qi * qi = -1 := by rw [qi]; ext <;> simp

/-- `j² = -1`. -/
lemma qj_mul_qj : qj * qj = -1 := by rw [qj]; ext <;> simp

/-- `k² = -1`. -/
lemma qk_mul_qk : qk * qk = -1 := by rw [qk]; ext <;> simp

/-- `ij = k`. -/
lemma qi_mul_qj : qi * qj = qk := by rw [qi, qj, qk]; ext <;> simp

/-- `jk = i`. -/
lemma qj_mul_qk : qj * qk = qi := by rw [qi, qj, qk]; ext <;> simp

/-- `ki = j`. -/
lemma qk_mul_qi : qk * qi = qj := by rw [qi, qj, qk]; ext <;> simp

/-- `ji = -k`. -/
lemma qj_mul_qi : qj * qi = -qk := by rw [qi, qj, qk]; ext <;> simp

/-- `kj = -i`. -/
lemma qk_mul_qj : qk * qj = -qi := by rw [qi, qj, qk]; ext <;> simp

/-- `ik = -j`. -/
lemma qi_mul_qk : qi * qk = -qj := by rw [qi, qj, qk]; ext <;> simp

/-- 以上の6つの関係式は `ijk = -1` で表される. -/
theorem qi_mul_qj_mul_qk : qi * qj * qk = -1 := by rw [qi, qj, qk]; ext <;> simp

/- 加法 -/
def qadd (x y : ℍ[ℝ]) : ℍ[ℝ] :=
  ⟨x.re + y.re, x.imI + y.imI, x.imJ + y.imJ, x.imK + y.imK⟩


/- スカラー倍 -/
def qsmul (r : ℝ) (x : ℍ[ℝ]) : ℍ[ℝ] :=
  ⟨r * x.re, r * x.imI, r * x.imJ, r * x.imK⟩


/- 乗法 -/
def qmul (x y : ℍ[ℝ]) : ℍ[ℝ] :=
  ⟨x.re * y.re - x.imI * y.imI - x.imJ * y.imJ - x.imK * y.imK,
   x.re * y.imI + x.imI * y.re + x.imJ * y.imK - x.imK * y.imJ,
   x.re * y.imJ - x.imI * y.imK + x.imJ * y.re + x.imK * y.imI,
   x.re * y.imK + x.imI * y.imJ - x.imJ * y.imI + x.imK * y.re⟩


/- 共役 -/
lemma conj_components (q : ℍ[ℝ]) :
    (star q).re = q.re ∧ (star q).imI = -q.imI ∧
      (star q).imJ = -q.imJ ∧ (star q).imK = -q.imK := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [re_star, imI_star, imJ_star, imK_star]


def norm (q : ℍ[ℝ]) : ℝ := Real.sqrt (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2)

notation "‖"q"‖" => norm q

lemma norm_eq (q : ℍ[ℝ]) : ‖q‖ = Real.sqrt (q * star q).re := by
  rw [norm]
  congr 1
  simp; ring

/- q⁻¹ = star q / ‖q‖² -/
lemma inv_eq (q : ℍ[ℝ]) : q⁻¹ = (normSq q)⁻¹ • star q :=
  Quaternion.inv_def q


lemma star_mul_comm (q p : ℍ[ℝ]) : star (q * p) = star p * star q :=
  star_mul q p


/-- `ℍ[ℝ] = ℝ ⊕ ℝ³` -/
theorem real_add_imaginary (q : ℍ[ℝ]) :
    (↑q.re : ℍ[ℝ]) + (q - ↑q.re) = q ∧ (q - (↑q.re : ℍ[ℝ])).re = 0 := by
  refine ⟨by abel, by simp⟩

end Quaternion


/- `Proposition13` -/
-- 3次元球面 : {(x₁, x₂, x₃, x₄) ∈ ℝ⁴ | x₁² + x₂² + x₃² + x₄² = 1}
def S₃ := {x : Fin 4 → ℝ | (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 = 1}

-- 単位四元数 : {q ∈ ℍ[ℝ] | q * star q = 1}
def U : Submonoid ℍ[ℝ] := unitary ℍ[ℝ]



/- `SU 2 ↦ S₃` -/
/- SU 2 = {!![a, b; -star b, star a] | a, b ∈ ℂ, |a|² + |b|² = 1}
    a = u₁ + iv₁, b = u₂ + iv₂ → u₁² + v₁² + u₂² + v₂² = 1
    → (u₁, v₁, u₂, v₂) ∈ S₃ -/
def SU2_to_S₃ (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ
  | 0 => (M 0 0).re  -- x 0 = u₁
  | 1 => (M 0 0).im  -- x 1 = v₁
  | 2 => (M 0 1).re  -- x 2 = u₂
  | 3 => (M 0 1).im  -- x 3 = v₂

/- u₁² + v₁² + u₂² + v₂² = 1 -/
lemma SU2_norm (M : SU 2) : (M.val 0 0).re ^ 2 + (M.val 0 0).im ^ 2 +
    (M.val 0 1).re ^ 2 + (M.val 0 1).im ^ 2 = 1 := by
  obtain ⟨h₁, h₂⟩ := M.2                           -- .2 ↔ .property (.1 ↔ .val)
  have := congr_fun (congr_fun h₁.2 0) 0           -- h₁.2 の両辺の 0 0 成分
  simp [Matrix.mul_apply, Complex.ext_iff] at this -- 行列の積の成分, 実部•虚部
  linarith

def SU2_to_S₃' (M : SU 2) : S₃ := ⟨SU2_to_S₃ M, SU2_norm M⟩


/- `S₃ ↦ SU 2` -/
def S₃_to_SU2 (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨x 0, x 1⟩, ⟨x 2, x 3⟩; ⟨-x 2, x 3⟩, ⟨x 0, -x 1⟩]

lemma S₃_mem_SU2 (x : S₃) : S₃_to_SU2 x ∈ SU 2 := by
  constructor
  · apply mem_unitaryGroup_iff.mpr
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, S₃_to_SU2, Complex.ext_iff, Complex.mul_conj]
    <;> ring_nf <;> norm_num <;> linarith [x.2.symm]
  · simp [det_fin_two, S₃_to_SU2, Complex.ext_iff]
    ring_nf; norm_num
    exact x.2

def S₃_to_SU2' (x : S₃) : SU 2 := ⟨S₃_to_SU2 x, S₃_mem_SU2 x⟩


-- (star M.val) k j = star (M.val j k)
lemma SU2_form (M : SU 2) : M.val 1 0 = - star (M.val 0 1) ∧ M.val 1 1 = star (M.val 0 0) := by
  obtain ⟨h_unitary, h_det⟩ : (∀ i j, ∑ k, M.val i k * star (M.val j k) = if i = j then 1 else 0)
      ∧ (M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0 = 1) := by
    obtain ⟨h_unitary, h_det⟩ := M.2
    simp_all [Matrix.mem_unitaryGroup_iff, Fin.sum_univ_two, ← Matrix.ext_iff]
    simp_all [Matrix.mul_apply, Matrix.det_fin_two]
  simp_all [Fin.forall_fin_two, Complex.ext_iff]
  grind


lemma SU2_left_inv_S₃ (M : SU 2) : S₃_to_SU2' (SU2_to_S₃' M) = M := by
  ext i j; fin_cases i <;> fin_cases j
  <;> simp [S₃_to_SU2', SU2_to_S₃', SU2_form, S₃_to_SU2, SU2_to_S₃]

lemma SU2_right_inv_S₃ (x : S₃) : SU2_to_S₃' (S₃_to_SU2' x) = x := by
  ext i; fin_cases i <;> simp [SU2_to_S₃', S₃_to_SU2', S₃_to_SU2, SU2_to_S₃]


def SU2_equiv_S₃ : SU 2 ≃ S₃ where
  toFun := SU2_to_S₃'
  invFun := S₃_to_SU2'
  left_inv := SU2_left_inv_S₃
  right_inv := SU2_right_inv_S₃


/- `SU 2 ↦ U` -/
/-  !![a, b; -star b, star a] ∈ SU 2 ↦ a + bj ∈ U
    a = u₁ + iv₁, b = u₂ + iv₂ → u₁² + v₁² + u₂² + v₂² = 1
    !![u₁ + iv₁, u₂ + iv₂; -u₂ + iv₂, u₁ - iv₁] ∈ SU 2 ↦ (u₁ + iv₁) + (u₂ + iv₂)j
    = u₁ + iv₁ + ju₂ + kv₂ ∈ U, (∵ ij = k, u₁² + u₂² + v₁² + v₂² = 1) -/
def SU2_to_U (M : Matrix (Fin 2) (Fin 2) ℂ) : ℍ[ℝ] :=
  ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩  -- u₁ + iv₁ + ju₂ + kv₂

lemma SU2_mem_U (M : SU 2) : SU2_to_U M.val ∈ U := by
  constructor <;> ext
  <;> simp [mul_comm, SU2_to_U, ← SU2_norm M] <;> ring

def SU2_to_U' (M : SU 2) : U := ⟨SU2_to_U M.val, SU2_mem_U M⟩


/- `U ↦ SU 2` -/
def U_to_SU2 (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

lemma U_mem_SU2 (q : U) : U_to_SU2 q.val ∈ SU 2 := by
  constructor <;> simp [U_to_SU2]
  · apply Matrix.mem_unitaryGroup_iff.mpr
    simp [← ext_iff, Fin.forall_fin_two]
    have h_norm : q.val.re^2 + q.val.imI^2 + q.val.imJ^2 + q.val.imK^2 = 1 := by
      have h := congr_arg (fun x : ℍ[ℝ] => x.re) q.2.2  -- q * star q = 1 の実部
      simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
        Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_one] at h
      linarith [h]
    simp [vecMul, dotProduct, Complex.ext_iff]
    ring_nf; norm_num; exact h_norm
  · have hq : star q.val * q.val = 1 := q.2.1
    simp_all [Complex.ext_iff, Quaternion.ext_iff]
    constructor <;> linarith

def U_to_SU2' (q : U) : SU 2 := ⟨U_to_SU2 q.val, U_mem_SU2 q⟩


lemma SU2_left_inv_U (M : SU 2) : U_to_SU2' (SU2_to_U' M) = M := by
  ext i j; fin_cases i <;> fin_cases j
  <;> simp [U_to_SU2', SU2_to_U', SU2_form, U_to_SU2, SU2_to_U]


lemma SU2_right_inv_U (q : U) : SU2_to_U' (U_to_SU2' q) = q := by
  simp [U_to_SU2', SU2_to_U', U_to_SU2, SU2_to_U]

-- 準同型
lemma SU2_map_mul_U (M N : SU 2) : SU2_to_U' (M * N) = SU2_to_U' M * SU2_to_U' N := by
  apply Subtype.ext
  apply Quaternion.ext_iff.mpr
  simp [SU2_to_U', SU2_to_U, Matrix.mul_apply, Fin.sum_univ_two]
  have hM := SU2_form M
  have hN := SU2_form N
  simp_all [Complex.ext_iff]
  exact ⟨by ring, by ring, by ring, by ring⟩


def SU2_equiv_U : SU 2 ≃* U where  -- 積の構造を保つ
  toFun := SU2_to_U'
  invFun := U_to_SU2'
  left_inv := SU2_left_inv_U
  right_inv := SU2_right_inv_U
  map_mul' := SU2_map_mul_U


/- `Definition14` -/
/-- SO(3) := {R ∈ O(3) | det R = 1}, O(3) := {Q ∈ GL(3, ℝ) | Qᵗ = Q⁻¹} --/
def SO3 := specialOrthogonalGroup (Fin 3) ℝ  -- 特殊直交群、回転群


/- `Theorem15`-/
def minusI : SU 2 := ⟨-1, by
  constructor
  · simp [Matrix.mem_unitaryGroup_iff]
  · simp [Matrix.det_fin_two]⟩


/- {I, -I} : -I によって生成される最小の部分群 -/
def plusminusI : Subgroup (SU 2) := Subgroup.closure {minusI}


-- structure SU2SO3DoubleCover where
--   toMonoidHom : SU 2 →* SO3
--   surjective : Function.Surjective toMonoidHom
--   ker_eq_plusminusI : toMonoidHom.ker = plusminusI


-- variable (π : SU2SO3DoubleCover)


-- lemma kernel_eq : π.toMonoidHom.ker = plusminusI :=
--   π.ker_eq_plusminusI

-- def quotientKernelEquivSO3 : SU 2 ⧸ π.toMonoidHom.ker ≃* SO3 :=
--   QuotientGroup.quotientKerEquivOfSurjective π.toMonoidHom π.surjective


/-- `実四元数 ℝ`  -/
def real := {x : ℍ[ℝ] | x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0}

/-- `純虚四元数 ℝ³` -/
def PureImaginary := {x : ℍ[ℝ] | x.re = 0}


def rotate (q : U) (x : PureImaginary) : ℍ[ℝ] :=
  q.val * x.val * star q.val


lemma prop1 (q : U) (x : PureImaginary) (q_real : q.val.im = 0) : rotate q x = x := by
  sorry


lemma prop2 (q : U) (x : PureImaginary) (q_im : q.val.re = 0) : rotate q x = -rotate q x := by
  sorry




theorem theorem_15 : ∃ π : SU 2 →* SO3, Function.Surjective π ∧ MonoidHom.ker π = plusminusI := by
  sorry



theorem homomor (π : SU 2 →* SO3) (hsurj : Function.Surjective π) :
    Nonempty (SU 2 ⧸ MonoidHom.ker π ≃* SO3) := by
  sorry



theorem Theorem15
    {SU2 SO3 : Type*} [Group SU2] [Group SO3]
    (K : Subgroup SU2) [K.Normal] (piHom : SU2 →* SO3)
    (hker : MonoidHom.ker piHom = K) (hsurj : Function.Surjective piHom) :
    Nonempty (SU2 ⧸ K ≃* SO3) := by
  refine ⟨?_⟩
  convert QuotientGroup.quotientKerEquivOfSurjective piHom hsurj <;> exact hker.symm


theorem Theorem15_quotient_kernel
    {SU2 SO3 : Type*} [Group SU2] [Group SO3]
    (piHom : SU2 →* SO3) (hsurj : Function.Surjective piHom) :
    Nonempty (SU2 ⧸ MonoidHom.ker piHom ≃* SO3) := by
  exact ⟨ QuotientGroup.quotientKerEquivOfSurjective _ hsurj ⟩


end

#min_imports
