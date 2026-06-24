import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RepresentationTheory.Basic

open MatrixGroups Matrix Complex SpecialLinearGroup

set_option quotPrecheck false

noncomputable section


variable (G : Subgroup SL(2, ℂ)) [Fintype G]


notation "⟪"u", "v"⟫" => star u ⬝ᵥ v  -- 標準内積

def SU (n : ℕ) := specialUnitaryGroup (Fin n) ℂ

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
  simp [avgInner, ρ, Matrix.mulVec_add, Finset.sum_add_distrib]; ring

-- 第一引数のスカラー同次性
lemma avgInner_smul_left (c : ℂ) (u v : Fin 2 → ℂ) :
    ⟪c • u, v⟫_G = (starRingEnd ℂ) c * ⟪u, v⟫_G := by
  simp [avgInner, ρ, Matrix.mulVec_smul, Finset.mul_sum _ _ _, mul_left_comm]

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
  contrapose! h with h_nonzero
  unfold avgInner
  obtain ⟨g, hg⟩ : ∃ g : G, ρ g u ≠ 0 := by exact ⟨1, by simpa [ρ] using h_nonzero⟩
  refine' ne_of_apply_ne Complex.re _; norm_num [Complex.ext_iff] at *
  -- apply lt_of_lt_of_le
  -- · exact lt_of_le_of_ne (by exact inv_nonneg.2 (Nat.cast_nonneg _)) (by norm_num)
  -- · apply Finset.single_le_sum (fun x _ => by nlinarith) (by exact Finset.mem_univ g)

  exact ne_of_gt <| lt_of_lt_of_le (by exact lt_of_le_of_ne (by nlinarith ) <| Ne.symm <| by intro H; exact hg <| by ext i; fin_cases i <;> norm_num [ Complex.ext_iff ] <;> constructor <;> nlinarith ) <| Finset.single_le_sum ( fun x _ => by nlinarith ) <| Finset.mem_univ g


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


end


#min_imports
