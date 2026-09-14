import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
このファイルは単体で完結しています（他のプロジェクト内ファイルを import しません）。
補助的な名前空間 ``（四元数の共役作用の行列表示）と `SU`（SU(2) と単位四元数の対応）
を先に定義し、そのあとで元の内容と `pre15` / `theorem_15` の証明を置いています。
-/


/-!
# The rotation attached to a quaternion

For a quaternion `q`, conjugation `x ↦ q * x * star q` preserves the purely imaginary
quaternions, which we identify with `ℝ³` via the basis `𝑖, 𝑗, 𝑘`.  This file defines the
resulting `ℝ`-linear endomorphism `.conjLin q` of `ℝ³` and its matrix
`.conjMatrix q` (the matrix is *not* postulated by an ad-hoc formula: it is the matrix
of the conjugation map, obtained through `LinearMap.toMatrix'`; the explicit entries are then
computed in `conjMatrix_eq`).

We prove that the assignment is multiplicative, that for a unit quaternion the matrix lies in
`SO(3)`, that its kernel is `{1, -1}`, and that it is surjective onto `SO(3)`.
-/

open Quaternion Matrix

noncomputable section


/-- The purely imaginary quaternion with coordinates `v` in the basis `𝑖, 𝑗, 𝑘`. -/
def ofVec (v : Fin 3 → ℝ) : ℍ[ℝ] := ⟨0, v 0, v 1, v 2⟩

/-- The coordinates of the imaginary part of a quaternion in the basis `𝑖, 𝑗, 𝑘`. -/
def toVec (x : ℍ[ℝ]) : Fin 3 → ℝ := ![x.imI, x.imJ, x.imK]

@[simp] lemma toVec_zero (x : ℍ[ℝ]) : toVec x 0 = x.imI := rfl
@[simp] lemma toVec_one (x : ℍ[ℝ]) : toVec x 1 = x.imJ := rfl
@[simp] lemma toVec_two (x : ℍ[ℝ]) : toVec x 2 = x.imK := rfl

@[simp] lemma toVec_ofVec (v : Fin 3 → ℝ) : toVec (ofVec v) = v := by
  funext i; fin_cases i <;> rfl

@[simp] lemma ofVec_re (v : Fin 3 → ℝ) : (ofVec v).re = 0 := rfl

lemma ofVec_toVec {x : ℍ[ℝ]} (hx : x.re = 0) : ofVec (toVec x) = x := by
  apply Quaternion.ext <;> simp [ofVec, hx]

/-- Conjugation by `q` preserves the purely imaginary quaternions. -/
lemma conj_re (q x : ℍ[ℝ]) (hx : x.re = 0) : (q * x * star q).re = 0 := by
  simp [hx]; ring

/-- The `ℝ`-linear endomorphism of `ℝ³` given by the conjugation action `x ↦ q * x * star q`
on the purely imaginary quaternions. -/
def conjLin (q : ℍ[ℝ]) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := toVec (q * ofVec v * star q)
  map_add' v w := by
    have : ofVec (v + w) = ofVec v + ofVec w := by apply Quaternion.ext <;> simp [ofVec]
    funext i
    fin_cases i <;> simp [this, mul_add, add_mul, toVec]
  map_smul' c v := by
    have : ofVec (c • v) = c • ofVec v := by apply Quaternion.ext <;> simp [ofVec]
    funext i
    fin_cases i <;>
      simp [this, toVec]

@[simp] lemma conjLin_apply (q : ℍ[ℝ]) (v : Fin 3 → ℝ) :
    conjLin q v = toVec (q * ofVec v * star q) := rfl

/-- The matrix of the conjugation action of `q` on the purely imaginary quaternions,
written in the basis `𝑖, 𝑗, 𝑘`. -/
def conjMatrix (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ := LinearMap.toMatrix' (conjLin q)

/-- The matrix `conjMatrix q` really does implement the conjugation action. -/
lemma conjMatrix_mulVec (q : ℍ[ℝ]) (v : Fin 3 → ℝ) :
    conjMatrix q *ᵥ v = toVec (q * ofVec v * star q) :=
  LinearMap.toMatrix'_mulVec (conjLin q) v

/-- The conjugation action written out on a purely imaginary quaternion. -/
lemma conjMatrix_mulVec_toVec (q x : ℍ[ℝ]) (hx : x.re = 0) :
    conjMatrix q *ᵥ toVec x = toVec (q * x * star q) := by
  rw [conjMatrix_mulVec, ofVec_toVec hx]

/-- The entries of `conjMatrix q`. -/
lemma conjMatrix_eq (q : ℍ[ℝ]) :
    conjMatrix q =
      !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2,
          2 * (q.imI * q.imJ - q.re * q.imK),
          2 * (q.imI * q.imK + q.re * q.imJ);
         2 * (q.imI * q.imJ + q.re * q.imK),
          q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
          2 * (q.imJ * q.imK - q.re * q.imI);
         2 * (q.imI * q.imK - q.re * q.imJ),
          2 * (q.imJ * q.imK + q.re * q.imI),
          q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjMatrix, LinearMap.toMatrix'_apply, conjLin, ofVec, toVec] <;>
    ring

@[simp] lemma conjMatrix_00 (q : ℍ[ℝ]) :
    conjMatrix q 0 0 = q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2 := by
  rw [conjMatrix_eq]; rfl
@[simp] lemma conjMatrix_01 (q : ℍ[ℝ]) :
    conjMatrix q 0 1 = 2 * (q.imI * q.imJ - q.re * q.imK) := by rw [conjMatrix_eq]; rfl
@[simp] lemma conjMatrix_02 (q : ℍ[ℝ]) :
    conjMatrix q 0 2 = 2 * (q.imI * q.imK + q.re * q.imJ) := by rw [conjMatrix_eq]; rfl
@[simp] lemma conjMatrix_10 (q : ℍ[ℝ]) :
    conjMatrix q 1 0 = 2 * (q.imI * q.imJ + q.re * q.imK) := by rw [conjMatrix_eq]; rfl
@[simp] lemma conjMatrix_11 (q : ℍ[ℝ]) :
    conjMatrix q 1 1 = q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2 := by rw [conjMatrix_eq]; rfl
@[simp] lemma conjMatrix_12 (q : ℍ[ℝ]) :
    conjMatrix q 1 2 = 2 * (q.imJ * q.imK - q.re * q.imI) := by rw [conjMatrix_eq]; rfl
@[simp] lemma conjMatrix_20 (q : ℍ[ℝ]) :
    conjMatrix q 2 0 = 2 * (q.imI * q.imK - q.re * q.imJ) := by rw [conjMatrix_eq]; rfl
@[simp] lemma conjMatrix_21 (q : ℍ[ℝ]) :
    conjMatrix q 2 1 = 2 * (q.imJ * q.imK + q.re * q.imI) := by rw [conjMatrix_eq]; rfl
@[simp] lemma conjMatrix_22 (q : ℍ[ℝ]) :
    conjMatrix q 2 2 = q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2 := by rw [conjMatrix_eq]; rfl

lemma conjMatrix_mul (p q : ℍ[ℝ]) : conjMatrix (p * q) = conjMatrix p * conjMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjMatrix_eq, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[simp] lemma conjMatrix_one : conjMatrix (1 : ℍ[ℝ]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] lemma conjMatrix_neg (q : ℍ[ℝ]) : conjMatrix (-q) = conjMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The coordinate form of `‖q‖ = 1`. -/
def IsUnitQ (q : ℍ[ℝ]) : Prop := q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1

lemma isUnitQ_iff_normSq (q : ℍ[ℝ]) : IsUnitQ q ↔ Quaternion.normSq q = 1 := by
  rw [IsUnitQ, Quaternion.normSq_def']

lemma IsUnitQ.mul {p q : ℍ[ℝ]} (hp : IsUnitQ p) (hq : IsUnitQ q) : IsUnitQ (p * q) := by
  rw [isUnitQ_iff_normSq] at hp hq ⊢
  rw [map_mul, hp, hq, one_mul]

lemma conjMatrix_mul_transpose {q : ℍ[ℝ]} (hq : IsUnitQ q) :
    conjMatrix q * (conjMatrix q)ᵀ = 1 := by
  have h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := hq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjMatrix_eq, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 + 1) * h

lemma conjMatrix_transpose_mul {q : ℍ[ℝ]} (hq : IsUnitQ q) :
    (conjMatrix q)ᵀ * conjMatrix q = 1 := by
  have h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := hq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjMatrix_eq, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 + 1) * h

lemma conjMatrix_det {q : ℍ[ℝ]} (hq : IsUnitQ q) : (conjMatrix q).det = 1 := by
  have h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := hq
  simp [conjMatrix_eq, Matrix.det_fin_three]
  linear_combination ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) ^ 2 +
    (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) + 1) * h

/-- The matrix of a unit quaternion determines the quaternion up to sign. -/
lemma conjMatrix_eq_one_iff {q : ℍ[ℝ]} (hq : IsUnitQ q) :
    conjMatrix q = 1 ↔ q = 1 ∨ q = -1 := by
  have h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := hq
  constructor
  · intro hM
    have e00 := congrFun (congrFun hM 0) 0
    have e11 := congrFun (congrFun hM 1) 1
    have e22 := congrFun (congrFun hM 2) 2
    simp at e00 e11 e22
    have hb : q.imI = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hc : q.imJ = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hd : q.imK = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have ha : q.re = 1 ∨ q.re = -1 := by
      have hfac : (q.re - 1) * (q.re + 1) = 0 := by
        rw [hb, hc, hd] at h; nlinarith
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases ha with ha | ha
    · left; apply Quaternion.ext <;> simp [ha, hb, hc, hd]
    · right; apply Quaternion.ext <;> simp [ha, hb, hc, hd]
  · rintro (rfl | rfl) <;> simp


/-! ### Surjectivity onto `SO(3)` -/

/-- Every unit vector of `ℝ³` is the image of the third basis vector under some rotation
coming from a unit quaternion. -/
lemma exists_conjMatrix_col2 {v0 v1 v2 : ℝ} (h : v0 ^ 2 + v1 ^ 2 + v2 ^ 2 = 1) :
    ∃ q : ℍ[ℝ], IsUnitQ q ∧ conjMatrix q 0 2 = v0 ∧ conjMatrix q 1 2 = v1 ∧
      conjMatrix q 2 2 = v2 := by
  rcases eq_or_ne v2 (-1) with hv2 | hv2
  · have hv0 : v0 = 0 := by nlinarith [sq_nonneg v0, sq_nonneg v1]
    have hv1 : v1 = 0 := by nlinarith [sq_nonneg v0, sq_nonneg v1]
    exact ⟨⟨0, 1, 0, 0⟩, by simp [IsUnitQ], by simp [hv0], by simp [hv1], by simp [hv2]⟩
  · have hge : -1 ≤ v2 := by nlinarith [sq_nonneg v0, sq_nonneg v1, sq_nonneg (v2 + 1)]
    have hpos : 0 < 2 * (1 + v2) := by
      rcases hge.lt_or_eq with h' | h'
      · linarith
      · exact absurd h'.symm hv2
    have hn2 : Real.sqrt (2 * (1 + v2)) ^ 2 = 2 * (1 + v2) := Real.sq_sqrt hpos.le
    have hnpos : 0 < Real.sqrt (2 * (1 + v2)) := Real.sqrt_pos.mpr hpos
    have hne : Real.sqrt (2 * (1 + v2)) ≠ 0 := ne_of_gt hnpos
    set n := Real.sqrt (2 * (1 + v2)) with hn
    refine ⟨⟨(1 + v2) / n, -v1 / n, v0 / n, 0⟩, ?_, ?_, ?_, ?_⟩
    · show ((1 + v2) / n) ^ 2 + (-v1 / n) ^ 2 + (v0 / n) ^ 2 + (0 : ℝ) ^ 2 = 1
      field_simp
      nlinarith [hn2, h]
    · rw [conjMatrix_02]
      show 2 * (-v1 / n * 0 + (1 + v2) / n * (v0 / n)) = v0
      field_simp
      linear_combination (-v0) * hn2
    · rw [conjMatrix_12]
      show 2 * (v0 / n * 0 - (1 + v2) / n * (-v1 / n)) = v1
      field_simp
      linear_combination (-v1) * hn2
    · rw [conjMatrix_22]
      show ((1 + v2) / n) ^ 2 - (-v1 / n) ^ 2 - (v0 / n) ^ 2 + (0 : ℝ) ^ 2 = v2
      field_simp
      nlinarith [hn2, h]

/-- A rotation matrix fixing the third basis vector comes from a unit quaternion. -/
lemma exists_conjMatrix_of_col2_eq_e2 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    (h02 : R 0 2 = 0) (h12 : R 1 2 = 0) (h22 : R 2 2 = 1) :
    ∃ q : ℍ[ℝ], IsUnitQ q ∧ conjMatrix q = R := by
  have e : ∀ i j, (Rᵀ * R) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by rw [hR]
  have e20 := e 2 0
  have e21 := e 2 1
  have e00 := e 0 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h22] at e20 e21 e00 e11
  have hdet' : R 0 0 * R 1 1 - R 0 1 * R 1 0 = 1 := by
    rw [Matrix.det_fin_three] at hdet
    rw [h02, h12, h22, e20, e21] at hdet
    linarith
  have h11 : R 1 1 = R 0 0 := by nlinarith [sq_nonneg (R 1 1 - R 0 0), sq_nonneg (R 0 1 + R 1 0)]
  have h01 : R 0 1 = -R 1 0 := by nlinarith [sq_nonneg (R 1 1 - R 0 0), sq_nonneg (R 0 1 + R 1 0)]
  have hcs : R 0 0 ^ 2 + R 1 0 ^ 2 = 1 := by rw [e20] at e00; linear_combination e00
  rcases eq_or_ne (R 0 0) (-1) with hc | hc
  · have hs : R 1 0 = 0 := by nlinarith
    refine ⟨⟨0, 0, 0, 1⟩, by simp [IsUnitQ], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h02, h12, h22, e20, e21, hc, hs, h11, h01]
  · have hcge : -1 ≤ R 0 0 := by nlinarith [sq_nonneg (R 1 0), sq_nonneg (R 0 0 + 1)]
    have hpos : 0 < (1 + R 0 0) / 2 := by
      rcases hcge.lt_or_eq with h' | h'
      · linarith
      · exact absurd h'.symm hc
    have hw2 : Real.sqrt ((1 + R 0 0) / 2) ^ 2 = (1 + R 0 0) / 2 := Real.sq_sqrt hpos.le
    have hwpos : 0 < Real.sqrt ((1 + R 0 0) / 2) := Real.sqrt_pos.mpr hpos
    set w := Real.sqrt ((1 + R 0 0) / 2) with hwdef
    have hwne : w ≠ 0 := ne_of_gt hwpos
    set z := R 1 0 / (2 * w) with hzdef
    have hz2 : z ^ 2 = (1 - R 0 0) / 2 := by
      rw [hzdef, div_pow]
      rw [show (2 * w) ^ 2 = 4 * w ^ 2 by ring, hw2]
      field_simp
      rw [div_eq_iff (show (1 + R 0 0) ≠ 0 from fun hz => hc (by linarith))]
      linear_combination 4 * hcs
    have hwz : 2 * (w * z) = R 1 0 := by
      rw [hzdef]
      field_simp
    refine ⟨⟨w, 0, 0, z⟩, ?_, ?_⟩
    · show w ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + z ^ 2 = 1
      rw [hw2, hz2]; ring
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h02, h12, h22, e20, e21, h11, h01] <;>
        linarith [hw2, hz2, hwz]

/-- Every element of `SO(3)` is the rotation attached to a unit quaternion. -/
theorem exists_conjMatrix {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) :
    ∃ q : ℍ[ℝ], IsUnitQ q ∧ conjMatrix q = R := by
  have e : ∀ i j, (Rᵀ * R) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by rw [hR]
  have hcol : R 0 2 ^ 2 + R 1 2 ^ 2 + R 2 2 ^ 2 = 1 := by
    have := e 2 2
    simp [Matrix.mul_apply, Fin.sum_univ_three] at this
    nlinarith [this]
  obtain ⟨q₁, hq₁, hc0, hc1, hc2⟩ := exists_conjMatrix_col2 hcol
  set M := conjMatrix q₁ with hMdef
  have hM : Mᵀ * M = 1 := conjMatrix_transpose_mul hq₁
  have hM' : M * Mᵀ = 1 := conjMatrix_mul_transpose hq₁
  set N := Mᵀ * R with hNdef
  have hNN : Nᵀ * N = 1 := by
    rw [hNdef, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc M Mᵀ R, hM', Matrix.one_mul, hR]
  have hNdet : N.det = 1 := by
    rw [hNdef, Matrix.det_mul, Matrix.det_transpose, hMdef, conjMatrix_det hq₁, hdet, one_mul]
  have hcolN : ∀ i, N i 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 := by
    intro i
    have : N i 2 = (Mᵀ * M) i 2 := by
      rw [hNdef]
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
      rw [← hc0, ← hc1, ← hc2]
    rw [this, hM]
  obtain ⟨q₂, hq₂, hq₂R⟩ := exists_conjMatrix_of_col2_eq_e2 hNN hNdet
    (by simpa using hcolN 0) (by simpa using hcolN 1) (by simpa using hcolN 2)
  refine ⟨q₁ * q₂, ?_, ?_⟩
  · exact hq₁.mul hq₂
  · rw [conjMatrix_mul, hq₂R, hNdef, ← Matrix.mul_assoc, ← hMdef, hM', Matrix.one_mul]




/-!
# `SU(2)` and the unit quaternions

We identify the special unitary group `SU(2)` with the group of unit quaternions, by sending
the matrix `!![a + b i, c + d i; -c + d i, a - b i]` to the quaternion `a + b𝑖 + c𝑗 + d𝑘`.
-/


/-- The entries of a matrix in `SU(2)` satisfy `A 1 1 = conj (A 0 0)` and
`A 1 0 = - conj (A 0 1)`. -/
lemma entries {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    A 1 1 = star (A 0 0) ∧ A 1 0 = -star (A 0 1) := by
  obtain ⟨hU, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
  rw [Matrix.det_fin_two] at hdet
  have hstar : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hAB : A * !![A 1 1, -A 0 1; -A 1 0, A 0 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | ring1
        | linear_combination hdet
  have hSB : star A = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    calc star A = star A * (A * !![A 1 1, -A 0 1; -A 1 0, A 0 0]) := by rw [hAB, mul_one]
      _ = (star A * A) * !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by rw [Matrix.mul_assoc]
      _ = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by rw [hstar, Matrix.one_mul]
  have e00 := congrFun (congrFun hSB 0) 0
  have e01 := congrFun (congrFun hSB 0) 1
  simp at e00 e01
  refine ⟨e00.symm, ?_⟩
  have := congrArg star e01
  simpa using this

/-- The quaternion attached to a `2 × 2` complex matrix. -/
def toQuat (A : Matrix (Fin 2) (Fin 2) ℂ) : ℍ[ℝ] :=
  ⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩

/-- The matrix in `SU(2)` attached to a quaternion. -/
def ofQuat (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

@[simp] lemma toQuat_ofQuat (q : ℍ[ℝ]) : toQuat (ofQuat q) = q := rfl

lemma toQuat_mul {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    toQuat (A * B) = toQuat A * toQuat B := by
  obtain ⟨hB11, hB10⟩ := entries hB
  apply Quaternion.ext <;>
    simp [toQuat, Matrix.mul_apply, Fin.sum_univ_two, hB11, hB10, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;>
    ring

lemma normSq_toQuat {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) : Quaternion.normSq (toQuat A) = 1 := by
  obtain ⟨hU, -⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
  have h : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have e := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply] at e
  have er := congrArg Complex.re e
  simp [Complex.add_re, Complex.mul_re] at er
  rw [Quaternion.normSq_def']
  show (A 0 0).re ^ 2 + (A 0 0).im ^ 2 + (A 0 1).re ^ 2 + (A 0 1).im ^ 2 = 1
  nlinarith [er]

lemma ofQuat_mem {q : ℍ[ℝ]} (hq : Quaternion.normSq q = 1) :
    ofQuat q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hq; exact hq
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ofQuat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Complex.ext_iff] <;>
      constructor <;>
      first
        | ring1
        | linear_combination h
  · rw [Matrix.det_fin_two]
    simp [ofQuat, Complex.ext_iff]
    constructor
    · linear_combination h
    · ring

/-- Only `1` and `-1` are sent to `±1`. -/
lemma eq_one_of_toQuat_eq_one {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (h : toQuat A = 1) : A = 1 := by
  obtain ⟨h11, h10⟩ := entries hA
  rw [Quaternion.ext_iff] at h
  simp only [toQuat, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
    Quaternion.imK_one] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ha : A 0 0 = 1 :=
    Complex.ext (by rw [h1, Complex.one_re]) (by rw [h2, Complex.one_im])
  have hb : A 0 1 = 0 :=
    Complex.ext (by rw [h3, Complex.zero_re]) (by rw [h4, Complex.zero_im])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ha, hb, h11, h10]

lemma eq_neg_one_of_toQuat_eq_neg_one {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (h : toQuat A = -1) : A = -1 := by
  obtain ⟨h11, h10⟩ := entries hA
  rw [Quaternion.ext_iff] at h
  simp only [toQuat, Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
    Quaternion.imK_neg, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
    Quaternion.imK_one, neg_zero] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ha : A 0 0 = -1 :=
    Complex.ext (by rw [h1, Complex.neg_re, Complex.one_re])
      (by rw [h2, Complex.neg_im, Complex.one_im, neg_zero])
  have hb : A 0 1 = 0 :=
    Complex.ext (by rw [h3, Complex.zero_re]) (by rw [h4, Complex.zero_im])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ha, hb, h11, h10]






abbrev SU (n : ℕ) := specialUnitaryGroup (Fin n) ℂ

/- `Definition14` -/
/-- SO(3) := {R ∈ O(3) | det R = 1}, O(3) := {Q ∈ GL(3, ℝ) | Qᵗ = Q⁻¹} --/
abbrev SO (n : ℕ)  := specialOrthogonalGroup (Fin n) ℝ  -- 特殊直交群、回転群


-- abbrev U := {q : ℍ[ℝ] | ‖q‖ = 1}

-- 単位四元数 : {q ∈ ℍ[ℝ] | q * star q = 1}
abbrev U : Submonoid ℍ[ℝ] := unitary ℍ[ℝ]


/- `Theorem15`
    π : SU 2 → SO 3, ker π = {-I, I} となる全射準同型写像が存在する.
    ⟹ SU 2 ⧸ ker π ≃* SO 3
    U ≃* SU 2 より, h : U → SO 3, ker h = {-1, 1} を満たす全射準同型があれば, π = h ∘ f⁻¹ (f = U_to_SU 2)
-/

/-  q = a + bi + cj + dk ∈ U → a² + (b² + c² + d²) = 1 = cos²θ + sin²θ
    a = cosθ, √(b² + c² + d²) = sinθ なる θ ∈ [0, π] がただ一つ定まる.
    ここで, I := (1 / √(b² + c² + d²)) * (bi + cj + dk) = b'i + c'j + d'k (正規化) とする.
    I² = -1 を満たし、虚数単位 i とみなせる. q = cosθ + simθI と表せる.
    I に沿って, 標準直交基底 J, K を作り, それぞれに r_q を作用させる. (四元数の規則を満たす)
    r_q q I = I, r_q q J = (cos2θ)J + (sin2θ)K, r_q q K = (-sin2θ)J + (cos2θ)K
    ∴ (r_q q J, r_q q K)ᵗ = !![cos2θ, sin2θ; -sin2θ, cos2θ] * (J, K)ᵗ
    → r_q q x は I で定義される軸の周りに, JK平面(R²) を 2θ 回転させる変換
    軸を一つ決めて(= I), 回転を φ ∈ [0, 2π]とすると, θ = φ/2, q = cos(φ/2) + sin(φ/2)I とすれば
    SO 3 の任意の元を表せる → 全射性
    ker h = {q ∈ U | h q = r_q q x = q * x * qᴴ = x} (SO3 の単位元は恒等変換)
    θ = 0, π のとき i.e. q = -1, 1. -/


/-- `実四元数 ℝ`  -/
def real := {x : ℍ[ℝ] | x.im = 0}-- ∧ x.imJ = 0 ∧ x.imK = 0} -- {x.im = 0}?


/-- `純虚四元数`, ℝ³ とみなせる` -/
def PureImaginary := {x : ℍ[ℝ] | x.re = 0}


variable (q : U) (x : PureImaginary)

/-- U の ℝ³ への作用 -/
def r_q (q : U) (x : ℍ[ℝ]) : ℍ[ℝ] := (q : ℍ[ℝ]) * x * star (q : ℍ[ℝ])

/-- h(q) = r_q(x) と定義 -/
def h (q : U) : ℍ[ℝ] → ℍ[ℝ] := fun x => r_q q x


/-- r_q : 純虚四元数を保つ -/
lemma r_q_pureim (q : U) (x : PureImaginary) : r_q q x ∈ PureImaginary := by
  have h : x.val.re = 0 := x.prop
  simp [r_q, PureImaginary, h]; ring_nf


/-- h が準同型写像であること -/
lemma h_homomor (q p : U) : h (q * p) = h q ∘ h p := by
  funext x
  simp [h, r_q, Function.comp_apply]
  noncomm_ring


/-- 長さを変えない isometry -/
lemma isometry (q : U) (x : PureImaginary) : ‖r_q q x‖ = ‖x.val‖ := by
  have hqSq : Quaternion.normSq q.val = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    norm_num
  have hSq : ‖r_q q x‖ * ‖r_q q x‖ = ‖x.val‖ * ‖x.val‖ := by
    repeat rw [← Quaternion.normSq_eq_norm_mul_self]
    rw [r_q, map_mul, map_mul, hqSq, one_mul, normSq_star, hqSq, mul_one]
  nlinarith [norm_nonneg (r_q q x), norm_nonneg x.val]


/- 虚部の大きさ -/
def imagNorm (q : ℍ[ℝ]) : ℝ :=
  Real.sqrt (q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2)


/-- q = a + (bi + cj + dk) ∈ U の偏角, θ = arccos(a) ∈ [0, π], ‖a‖ ≤ 1 -/
def quaternionAngle (q : U) : ℝ := Real.arccos q.val.re


/-- (0 でない) q ∈ U の虚部の正規化, 回転軸 -/
def quaternionAxis (q : U) : ℍ[ℝ] := (imagNorm q)⁻¹ • q.val.im


/-- q ∈ U, normSq = q * star q -/
lemma unitQuaternion_normSq (q : U) : Quaternion.normSq q.val = 1 := by
  norm_num [Quaternion.normSq_eq_norm_mul_self]

/-- q = a + bi + cj + dk ∈ U → a² + b² + c² + d² = 1 -/
lemma unitQuaternion_coordinate_equation (q : U) :
    q.val.re ^ 2 + (q.val.imI ^ 2 + q.val.imJ ^ 2 + q.val.imK ^ 2) = 1 := by
  have := unitQuaternion_normSq q
  simp [normSq] at this
  linarith


/-- q ∈ U の偏角が [0, π] であること, Icc : Interval Closed Closed -/
lemma quaternionAngle_mem (q : U) : quaternionAngle q ∈ Set.Icc (0 : ℝ) Real.pi := by
  rw [quaternionAngle]
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩


/-- q = a + bi + cj + dk ∈ U, a = cosθ であること -/
lemma quaternionAngle_cos (q : U) : Real.cos (quaternionAngle q) = q.val.re := by
  rw [quaternionAngle]
  apply Real.cos_arccos
  · have h := unitQuaternion_normSq q
    simp [Quaternion.normSq] at h
    nlinarith [sq_nonneg (q.val.re + 1)]
  · have h := unitQuaternion_normSq q
    simp [Quaternion.normSq] at h
    nlinarith [sq_nonneg (q.val.re - 1)]


/-- q = a + bi + cj + dk ∈ U, sinθ = √(b² + c² + d²) であること -/
lemma quaternionAngle_sin (q : U) :
    Real.sin (quaternionAngle q) = imagNorm q.val := by
  rw [quaternionAngle, imagNorm, Real.sin_arccos]
  congr 1
  have h := unitQuaternion_coordinate_equation q
  linarith


/-- cosθ = a なる θ ∈ [0, π] が唯一つ定まること -/
lemma quaternionAngle_unique (q : U) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hcos : Real.cos θ = q.val.re) : θ = quaternionAngle q := by
  rw [quaternionAngle, ← hcos]
  exact (Real.arccos_cos hθ.1 hθ.2).symm


/-- 正規化した回転軸は純虚四元数 -/
lemma quaternionAxis_re (q : U) : (quaternionAxis q).re = 0 := by
  simp [quaternionAxis]


/-- 虚部が0でないならば, 正規化した回転軸は単位ベクトル -/
lemma quaternionAxis_normSq (q : U) (h : imagNorm q.val ≠ 0) :
    Quaternion.normSq (quaternionAxis q) = 1 := by
  simp [quaternionAxis, imagNorm, Quaternion.normSq_def]
  ring_nf
  have hsum : q.val.imI ^ 2 + q.val.imJ ^ 2 + q.val.imK ^ 2 ≥ 0 := by
    linarith [sq_nonneg (q.val.imI), sq_nonneg (q.val.imJ), sq_nonneg (q.val.imK)]
  have hsum_pos : q.val.imI ^ 2 + q.val.imJ ^ 2 + q.val.imK ^ 2 > 0 := by
    contrapose! h
    rw [imagNorm, Real.sqrt_eq_zero_of_nonpos h]
  rw [inv_pow, Real.sq_sqrt hsum]
  field_simp


/-- 回転軸を2乗すると -1 -/
lemma quaternionAxis_sq (q : U) (h : imagNorm q.val ≠ 0) :
    quaternionAxis q ^ 2 = (-1 : ℍ[ℝ]) := by
  have hNorm := quaternionAxis_normSq q h
  have hRe := quaternionAxis_re q
  simp only [sq]
  simp [Quaternion.normSq] at hNorm
  rw [hRe] at hNorm
  simp [Quaternion.ext_iff, hRe]
  exact ⟨by linarith, by ring, by ring, by ring⟩


/-- q ∈ U (虚部が0でない) は q = cosθ + sinθI (θ ∈ [0, π]) と表せる -/
lemma unitQuaternion_axis_angle (q : U) (h : imagNorm q.val ≠ 0) :
    q.val = (Real.cos (quaternionAngle q) : ℍ[ℝ]) +
      Real.sin (quaternionAngle q) • quaternionAxis q := by
  rw [quaternionAngle_cos, quaternionAngle_sin, quaternionAxis]
  rw [smul_smul, mul_inv_cancel₀ h, one_smul, re_add_im]


/-- 四元数の正規直交基底とその乗法規則. I を固定し, それに準じて J, K を作れる
`I² = J² = K² = -1` and `IJ = K`, `JK = I`, `KI = J`. -/
structure QuaternionFrame where
  I : ℍ[ℝ]  -- 単位純虚四元数
  J : ℍ[ℝ]
  K : ℍ[ℝ]
  star_I : star I = -I
  star_J : star J = -J
  star_K : star K = -K
  I_sq : I * I = -1
  J_sq : J * J = -1
  K_sq : K * K = -1
  IJ : I * J = K
  JI : J * I = -K
  JK : J * K = I
  KJ : K * J = -I
  KI : K * I = J
  IK : I * K = -J
  -- `IJK : I * J * K = -1`


/-- 上の基底を F とし, q ∈ U を改めて定める -/
def frameQuaternion (F : QuaternionFrame) (θ : ℝ) : ℍ[ℝ] :=
  (Real.cos θ : ℍ[ℝ]) + Real.sin θ • F.I

/-- star q = cosθ - sinθI -/
lemma frameQuaternion_star (F : QuaternionFrame) (θ : ℝ) :
    star (frameQuaternion F θ) = (Real.cos θ : ℍ[ℝ]) - Real.sin θ • F.I := by
  simp [frameQuaternion, F.star_I, sub_eq_add_neg]


/-- q = cosθ + sinθI → ‖q‖² = 1 → q ∈ U -/
lemma frameQuaternion_normSq (F : QuaternionFrame) (θ : ℝ) :
    Quaternion.normSq (frameQuaternion F θ) = 1 := by
  rw [Quaternion.normSq_def, frameQuaternion_star]
  simp [frameQuaternion, mul_sub, add_mul, Quaternion.re_add, Quaternion.re_sub,
    Quaternion.re_mul, Quaternion.re_smul, Quaternion.re_coe, Quaternion.imI_coe,
    Quaternion.imJ_coe, Quaternion.imK_coe, zero_mul, mul_zero, sub_zero]
  have hs := congrArg (fun x : ℍ[ℝ] => x.re) F.I_sq
  have hr := congrArg (fun x : ℍ[ℝ] => x.re) F.star_I
  simp only [Quaternion.re_mul, Quaternion.re_neg, Quaternion.re_one, Quaternion.re_star] at hs hr
  nlinarith [Real.sin_sq_add_cos_sq θ]


/-- r_q q I = (cosθ + sinθI) * I * (cosθ - sinθI) = I → I は回転軸 -/
lemma frame_conj_I (F : QuaternionFrame) (θ : ℝ) :
    frameQuaternion F θ * F.I * star (frameQuaternion F θ) = F.I := by
  have hre : F.I.re = 0 := by
    have h := congrArg (fun x : ℍ[ℝ] => x.re) F.star_I
    simp at h
    linarith
  have hn : F.I.imI ^ 2 + F.I.imJ ^ 2 + F.I.imK ^ 2 = 1 := by
    have h := congrArg (fun x : ℍ[ℝ] => x.re) F.I_sq
    simp [hre] at h
    nlinarith [h]
  have hsc := Real.sin_sq_add_cos_sq θ
  rw [frameQuaternion_star, frameQuaternion]
  apply Quaternion.ext <;> simp [hre]
  · ring
  · linear_combination (Real.sin θ ^ 2 * F.I.imI) * hn + F.I.imI * hsc
  · linear_combination (Real.sin θ ^ 2 * F.I.imJ) * hn + F.I.imJ * hsc
  · linear_combination (Real.sin θ ^ 2 * F.I.imK) * hn + F.I.imK * hsc


/-- r_q(J) = (cos2θ)J + (sin2θ)K → JK平面で2θ回転 -/
lemma frame_conj_J (F : QuaternionFrame) (θ : ℝ) :
    frameQuaternion F θ * F.J * star (frameQuaternion F θ) =
      Real.cos (2 * θ) • F.J + Real.sin (2 * θ) • F.K := by
  rw [frameQuaternion]
  simp
  rw [F.star_I]
  simp only [add_mul, mul_add, mul_assoc, smul_mul_assoc, mul_smul_comm]
  rw [show F.J * (-F.I) = -(F.J * F.I) by rw [mul_neg]]
  rw [F.JI]
  simp
  rw [F.IK]
  have h1 : ∀ (q : ℍ[ℝ]) (r : ℝ), q * ↑r = r • q := by
    intro q r
    rw [show (r : ℍ[ℝ]) = r • (1 : ℍ[ℝ]) by simp [Quaternion.ext_iff]]
    rw [mul_smul_comm, mul_one]
  have h2 : ∀ (q : ℍ[ℝ]) (r : ℝ), ↑r * q = r • q := by
    intro q r
    rw [show (r : ℍ[ℝ]) = r • (1 : ℍ[ℝ]) by simp [Quaternion.ext_iff]]
    rw [smul_mul_assoc, one_mul]
  rw [h1 F.J (Real.cos θ)]
  simp only [mul_smul_comm]
  rw [h2 F.J (Real.cos θ), h2 F.K (Real.cos θ)]
  simp [smul_smul]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  rw [F.IJ]
  module


/-- r_q(K) = (-sin2θ)J + (cos2θ)K → JK平面で2θ回転 -/
lemma frame_conj_K (F : QuaternionFrame) (θ : ℝ) :
    frameQuaternion F θ * F.K * star (frameQuaternion F θ) =
      (-Real.sin (2 * θ)) • F.J + Real.cos (2 * θ) • F.K := by
  rw [frameQuaternion]
  simp
  rw [F.star_I]
  simp only [add_mul, mul_add, mul_assoc, smul_mul_assoc, mul_smul_comm]
  rw [show F.K * (-(F.I : ℍ[ℝ])) = -(F.K * F.I) by rw [mul_neg]]
  rw [F.KI]
  simp
  rw [F.IJ]
  -- Goal: quaternion times real scalar needs simplification
  -- Quaternion * real = real • Quaternion
  have h1 : ∀ (q : ℍ[ℝ]) (r : ℝ), q * ↑r = r • q := by
    intro q r
    rw [show (r : ℍ[ℝ]) = r • (1 : ℍ[ℝ]) by simp [Quaternion.ext_iff]]
    rw [mul_smul_comm, mul_one]
  rw [h1 (F.K) (Real.cos θ)]
  simp
  -- Need: r • q = q * r, which follows from h1 if we can show commutativity for scalars
  have h2 : ∀ (q : ℍ[ℝ]) (r : ℝ), ↑r * q = r • q := by
    intro q r
    rw [show (r : ℍ[ℝ]) = r • (1 : ℍ[ℝ]) by simp [Quaternion.ext_iff]]
    rw [smul_mul_assoc, one_mul]
  rw [h2 (F.K) (Real.cos θ)]
  rw [h2 (F.J) (Real.cos θ)]
  rw [F.IK]
  simp [smul_smul]
  -- Now need to use trig identities: cos²θ - sin²θ = cos(2θ), 2sinθ cosθ = sin(2θ)
  have sin2θ : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have cos2θ : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := Real.cos_two_mul' θ
  rw [sin2θ, cos2θ]
  module


lemma frameQuaternion_norm (F : QuaternionFrame) (θ : ℝ) :
    ‖frameQuaternion F θ‖ = 1 := by
  have h := frameQuaternion_normSq F θ
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  have := mul_self_eq_one_iff (a := ‖frameQuaternion F θ‖)
  rw [this] at h
  rcases h with h | h <;> linarith [norm_nonneg (frameQuaternion F θ)]


/-- 3次元空間における「任意の軸u周りの角度φの回転」は, 対応する単位四元数 q = cos(φ/2) + sin(φ/2)u
    による共役作用 x ↦ q * x * star q として表せる. 全射性 -/
theorem frameRotation_represented (F : QuaternionFrame) (φ : ℝ) :
    ∃ q : U,
      q.val = frameQuaternion F (φ / 2) ∧
      q.val * F.I * star q.val = F.I ∧
      q.val * F.J * star q.val = Real.cos φ • F.J + Real.sin φ • F.K ∧
      q.val * F.K * star q.val = (-Real.sin φ) • F.J + Real.cos φ • F.K := by
  let q : U := ⟨frameQuaternion F (φ / 2), by
    have hs : ‖frameQuaternion F (φ / 2)‖ * ‖frameQuaternion F (φ / 2)‖ = 1 := by
      rw [← Quaternion.normSq_eq_norm_mul_self]
      exact frameQuaternion_normSq F (φ / 2)
    constructor <;> simp only [star_mul_self, self_mul_star]
    <;> simp only [normSq_eq_norm_mul_self, hs, coe_one]⟩
  refine ⟨q, rfl, ?_, ?_, ?_⟩
  · exact frame_conj_I F (φ / 2)
  · simpa only [show 2 * (φ / 2) = φ by ring] using frame_conj_J F (φ / 2)
  · simpa only [show 2 * (φ / 2) = φ by ring] using frame_conj_K F (φ / 2)


/-- ker h = {-1, 1} であること, 回転群の単位元は恒等変換 -/
lemma conjugation_kernel (q : U) :
    (∀ x : PureImaginary, r_q q x = x.val) ↔ q.val = (1 : ℍ[ℝ]) ∨ q.val = (-1 : ℍ[ℝ]) := by
  constructor
  · intro h
    let hI : PureImaginary := ⟨(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), by rfl⟩
    let hJ : PureImaginary := ⟨(⟨0, 0, 1, 0⟩ : ℍ[ℝ]), by rfl⟩
    have hqI : q.val * ⟨0, 1, 0, 0⟩ * star q.val = ⟨0, 1, 0, 0⟩ := by
      have := h hI; simp [r_q] at this; exact this
    have hqJ : q.val * ⟨0, 0, 1, 0⟩ * star q.val = ⟨0, 0, 1, 0⟩ := by
      have := h hJ; simp [r_q] at this; exact this
    have hq_normSq : Quaternion.normSq q.val = 1 := unitQuaternion_normSq q
    have h_comm_I : q.val * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * q.val := by
      have : q.val * ⟨0, 1, 0, 0⟩ * star q.val * q.val = ⟨0, 1, 0, 0⟩ * q.val := by
        rw [hqI]
      simp [mul_assoc] at this
      exact this
    have h_comm_J : q.val * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * q.val := by
      have : q.val * ⟨0, 0, 1, 0⟩ * star q.val * q.val = ⟨0, 0, 1, 0⟩ * q.val := by
        rw [hqJ]
      simp [mul_assoc] at this
      exact this
    have h_eq_I := Quaternion.ext_iff.mp h_comm_I
    have h_eq_J := Quaternion.ext_iff.mp h_comm_J
    obtain ⟨h_I_re, h_I_i, h_I_j, h_I_k⟩ := h_eq_I
    obtain ⟨h_J_re, h_J_i, h_J_j, h_J_k⟩ := h_eq_J
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      zero_mul, one_mul, add_zero, mul_zero] at h_I_re h_I_i h_I_j h_I_k h_J_re h_J_i h_J_j h_J_k
    have h_imK : q.val.imK = 0 := by linarith
    have h_imJ : q.val.imJ = 0 := by linarith
    have h_imI : q.val.imI = 0 := by linarith
    have h_re_sq : q.val.re ^ 2 = 1 := by
      have := unitQuaternion_coordinate_equation q
      rw [h_imI, h_imJ, h_imK, zero_pow, add_zero, add_zero, add_zero] at this
      exact this
      norm_num
    have h_re : q.val.re = 1 ∨ q.val.re = -1 := sq_eq_one_iff.mp h_re_sq
    rcases h_re with h_re | h_re
    · left; exact Quaternion.ext_iff.mpr ⟨h_re, h_imI, h_imJ, h_imK⟩
    · right; rw [Quaternion.ext_iff]; simp [h_re, h_imI, h_imJ, h_imK]
  · intro h x
    rcases h with hq | hq <;> simp [r_q, hq]


def minusone : U := ⟨-1, by constructor <;> simp⟩

def plusminusone : Subgroup U := Subgroup.closure {minusone}


/- `Theorem15`-/
def minusI : SU 2 := ⟨-1, by
  constructor
  · simp [Matrix.mem_unitaryGroup_iff]
  · simp [Matrix.det_fin_two]⟩


/- {I, -I} : -I によって生成される最小の部分群 -/
def plusminusI : Subgroup (SU 2) := Subgroup.closure {minusI}



/-! ### 単位四元数から SO(3) への準同型 -/


/-- 単位四元数の座標表示 -/
lemma isUnitQ_of_mem_U (q : U) : IsUnitQ q.val := by
  have := unitQuaternion_coordinate_equation q
  show q.val.re ^ 2 + q.val.imI ^ 2 + q.val.imJ ^ 2 + q.val.imK ^ 2 = 1
  linarith


/-- ノルムが 1 の四元数は単位四元数 -/
lemma mem_U_of_normSq {q : ℍ[ℝ]} (h : Quaternion.normSq q = 1) : q ∈ U := by
  constructor
  · rw [Quaternion.star_mul_self, h]; norm_num
  · rw [Quaternion.self_mul_star, h]; norm_num


/-- `q ↦ (x ↦ q x q⁻¹)` の行列表示. これが求める準同型 `h : U →* SO 3` -/
def hMat : U →* SO 3 where
  toFun q := ⟨conjMatrix q.val, by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    exact ⟨(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr (conjMatrix_mul_transpose (isUnitQ_of_mem_U q)),
      conjMatrix_det (isUnitQ_of_mem_U q)⟩⟩
  map_one' := by ext i j; simp [conjMatrix_one]
  map_mul' p q := by ext i j; simp [conjMatrix_mul]


/-- `hMat q` は `r_q q` (純虚四元数 ≅ ℝ³ 上の共役作用) の行列表示になっている -/
lemma hMat_apply_eq_conj (q : U) (x : ℍ[ℝ]) (hx : x.re = 0) :
    (hMat q).val *ᵥ toVec x = toVec (r_q q x) :=
  conjMatrix_mulVec_toVec q.val x hx


lemma hMat_surjective : Function.Surjective hMat := by
  intro R
  have hR : R.valᵀ * R.val = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.specialUnitaryGroup_le_unitaryGroup R.2)
  have hdet : R.val.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp R.2).2
  obtain ⟨q, hq, hqR⟩ := exists_conjMatrix hR hdet
  refine ⟨⟨q, mem_U_of_normSq ((isUnitQ_iff_normSq q).mp hq)⟩, ?_⟩
  exact Subtype.ext hqR

/-- `-1` で生成される部分群は `{1, -1}` -/
lemma minusone_mul_minusone : minusone * minusone = 1 := by
  apply Subtype.ext
  show (-1 : ℍ[ℝ]) * (-1 : ℍ[ℝ]) = 1
  norm_num

lemma minusone_inv : minusone⁻¹ = minusone := inv_eq_of_mul_eq_one_right minusone_mul_minusone

lemma mem_plusminusone (q : U) : q ∈ plusminusone ↔ q = 1 ∨ q = minusone := by
  constructor
  · intro hq
    induction hq using Subgroup.closure_induction with
    | mem x hx => exact Or.inr hx
    | one => exact Or.inl rfl
    | mul x y _ _ ihx ihy =>
        rcases ihx with rfl | rfl <;> rcases ihy with rfl | rfl <;>
          simp [minusone_mul_minusone]
    | inv x _ ihx =>
        rcases ihx with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr minusone_inv
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure rfl

/-- `hMat` の核は `{1, -1}` -/
lemma hMat_ker : hMat.ker = plusminusone := by
  ext q
  rw [MonoidHom.mem_ker, mem_plusminusone]
  constructor
  · intro hq
    have h1 : conjMatrix q.val = 1 := congrArg Subtype.val hq
    rcases (conjMatrix_eq_one_iff (isUnitQ_of_mem_U q)).mp h1 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact map_one hMat
    · apply Subtype.ext
      show conjMatrix (-1 : ℍ[ℝ]) = 1
      simp

lemma pre15 : ∃ h : U →* SO 3, Function.Surjective h ∧ h.ker = plusminusone :=
  ⟨hMat, hMat_surjective, hMat_ker⟩


/-! ### SU(2) と単位四元数群の同一視 -/

/-- SU(2) から単位四元数群 U への準同型 -/
def fSU : SU 2 →* U where
  toFun A := ⟨toQuat A.val, mem_U_of_normSq (normSq_toQuat A.2)⟩
  map_one' := by
    apply Subtype.ext
    show toQuat (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    apply Quaternion.ext <;> simp [toQuat]
  map_mul' A B := Subtype.ext (toQuat_mul B.2)

lemma fSU_surjective : Function.Surjective fSU := by
  intro q
  exact ⟨⟨ofQuat q.val, ofQuat_mem (unitQuaternion_normSq q)⟩,
    Subtype.ext (toQuat_ofQuat q.val)⟩

lemma minusI_mul_minusI : minusI * minusI = 1 := by
  apply Subtype.ext
  show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
  norm_num

lemma minusI_inv : minusI⁻¹ = minusI := inv_eq_of_mul_eq_one_right minusI_mul_minusI

lemma mem_plusminusI (A : SU 2) : A ∈ plusminusI ↔ A = 1 ∨ A = minusI := by
  constructor
  · intro hA
    induction hA using Subgroup.closure_induction with
    | mem x hx => exact Or.inr hx
    | one => exact Or.inl rfl
    | mul x y _ _ ihx ihy =>
        rcases ihx with rfl | rfl <;> rcases ihy with rfl | rfl <;>
          simp [minusI_mul_minusI]
    | inv x _ ihx =>
        rcases ihx with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr minusI_inv
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure rfl

lemma fSU_minusI : fSU minusI = minusone := by
  apply Subtype.ext
  show toQuat (-1 : Matrix (Fin 2) (Fin 2) ℂ) = -1
  apply Quaternion.ext <;> simp [toQuat]

/-- π = h ∘ f⁻¹ : SU 2 → U → SO3, f = U_to_SU2 -/
theorem theorem_15 : ∃ π : SU 2 →* SO 3, Function.Surjective π ∧ π.ker = plusminusI := by
  refine ⟨hMat.comp fSU, hMat_surjective.comp fSU_surjective, ?_⟩
  ext A
  rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    ← MonoidHom.mem_ker, hMat_ker, mem_plusminusone, mem_plusminusI]
  constructor
  · rintro (h | h)
    · left
      apply Subtype.ext
      exact eq_one_of_toQuat_eq_one A.2 (congrArg Subtype.val h)
    · right
      apply Subtype.ext
      exact eq_neg_one_of_toQuat_eq_neg_one A.2 (congrArg Subtype.val h)
  · rintro (rfl | rfl)
    · exact Or.inl (map_one fSU)
    · exact Or.inr fSU_minusI


def theorem15 [plusminusI.Normal] (π : SU 2 →* SO 3) (surj : Function.Surjective π)
    (kern : π.ker = plusminusI) : SU 2 ⧸ plusminusI ≃* SO 3 :=
  (QuotientGroup.quotientMulEquivOfEq kern.symm).trans (QuotientGroup.quotientKerEquivOfSurjective π surj)


/-- `plusminusI = {I, -I}` は正規部分群 -/
instance plusminusI_normal : plusminusI.Normal := by
  obtain ⟨π, -, kern⟩ := theorem_15
  rw [← kern]
  infer_instance

/-- `Theorem15` の結論 : `SU(2) / {±I} ≃ SO(3)` -/
theorem SU2_quotient_mulEquiv_SO3 : Nonempty (SU 2 ⧸ plusminusI ≃* SO 3) := by
  obtain ⟨π, surj, kern⟩ := theorem_15
  exact ⟨theorem15 π surj kern⟩




/-- **Key algebraic step.** A `2 × 2` complex matrix of determinant `1` which squares to the
identity and is not the identity must be `-I₂`.
This is the computation in the proof of Proposition 16: writing `M = !![a, b; -b̄, ā]`, the
condition `M ^ 2 = I₂` forces `b = 0` and `a = ±1`.  (Only `det M = 1` is needed; unitarity of
`M` is not used.) -/
theorem eq_neg_one_of_det_one_of_sq_eq_one
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hdet : M.det = 1) (hsq : M * M = 1) (hne : M ≠ 1) :
    M = -1 := by
  set a := M 0 0 with ha_def
  set b := M 0 1 with hb_def
  set c := M 1 0 with hc_def
  set d := M 1 1 with hd_def
  have hd : a * d - b * c = 1 := by rw [Matrix.det_fin_two] at hdet; exact hdet
  have e00 : a * a + b * c = 1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] using this
  have e01 : a * b + b * d = 0 := by
    have := congrFun (congrFun hsq 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] using this
  have e10 : c * a + d * c = 0 := by
    have := congrFun (congrFun hsq 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] using this
  -- The trace cannot vanish: otherwise `det M = -1`.
  have hsum : a + d ≠ 0 := by
    intro h
    have h2 : (0 : ℂ) = 2 := by linear_combination hd + e00 - a * h
    norm_num at h2
  have hb : b = 0 := by
    rcases mul_eq_zero.1 (show b * (a + d) = 0 by linear_combination e01) with h | h
    · exact h
    · exact absurd h hsum
  have hc : c = 0 := by
    rcases mul_eq_zero.1 (show c * (a + d) = 0 by linear_combination e10) with h | h
    · exact h
    · exact absurd h hsum
  have haa : a * a = 1 := by rw [hb, hc] at e00; linear_combination e00
  have had : a * d = 1 := by rw [hb, hc] at hd; linear_combination hd
  have hda : d = a := by
    rcases mul_eq_zero.1 (show a * (d - a) = 0 by linear_combination had - haa) with h | h
    · exact absurd haa (by rw [h]; norm_num)
    · linear_combination h
  rcases mul_eq_zero.1 (show (a - 1) * (a + 1) = 0 by linear_combination haa) with h | h
  · -- `a = 1` would give `M = I₂`, which is excluded.
    refine absurd ?_ hne
    have ha : a = 1 := by linear_combination h
    rw [Matrix.eta_fin_two M, ← ha_def, ← hb_def, ← hc_def, ← hd_def, ha, hb, hc, hda, ha]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have ha : a = -1 := by linear_combination h
    rw [Matrix.eta_fin_two M, ← ha_def, ← hb_def, ← hc_def, ← hd_def, ha, hb, hc, hda, ha]
    ext i j
    fin_cases i <;> fin_cases j <;> simp


/-- **Proposition 16.** Let `U ∈ SU(2)` be of order `2`.  Then `U = -I₂`.
In other words, `-I₂` is the unique element of order `2` in `SU(2)`. -/
theorem su_two_orderOf_eq_two (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (hU : orderOf U = 2) :
    (U : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  have hsq : U ^ 2 = 1 := by
    have h := pow_orderOf_eq_one U
    rwa [hU] at h
  have hne : U ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hU
    exact absurd hU (by norm_num)
  have hdet : (U : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2
  have hsq' : (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have : ((U ^ 2 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [hsq]; rfl
    simpa [pow_two] using this
  have hne' : (U : Matrix (Fin 2) (Fin 2) ℂ) ≠ 1 := by
    intro h
    exact hne (Subtype.ext h)
  exact eq_neg_one_of_det_one_of_sq_eq_one _ hdet hsq' hne'


/-- Conversely, `-I₂` really is an element of `SU(2)` of order `2`, so Proposition 16 says
precisely that it is the unique such element. -/
theorem neg_one_mem_su_two_and_orderOf_eq_two :
    ∃ U : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      (U : Matrix (Fin 2) (Fin 2) ℂ) = -1 ∧ orderOf U = 2 := by
  have hmem : (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      simp
    · simp [Matrix.det_fin_two]
  refine ⟨⟨-1, hmem⟩, rfl, ?_⟩
  have hne : (⟨-1, hmem⟩ : Matrix.specialUnitaryGroup (Fin 2) ℂ) ≠ 1 := by
    intro h
    have := congrArg (fun x : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (x : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
    simp at this
    norm_num at this
  have hsq : (⟨-1, hmem⟩ : Matrix.specialUnitaryGroup (Fin 2) ℂ) ^ 2 = 1 := by
    apply Subtype.ext
    show (-1 : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 = 1
    simp
  exact orderOf_eq_prime hsq hne



end
