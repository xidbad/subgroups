import Mathlib.Algebra.Quaternion
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup


open Quaternion Matrix


/-- `SU n` is the special unitary group of `n × n` complex matrices. -/
abbrev SU (n : ℕ) : Submonoid (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.specialUnitaryGroup (Fin n) ℂ
-- 3次元球面 : {(x₁, x₂, x₃, x₄) ∈ ℝ⁴ | x₁² + x₂² + x₃² + x₄² = 1}
def S₃ := {x : Fin 4 → ℝ | (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 = 1}
-- 単位四元数 : {q ∈ ℍ[ℝ] | q * star q = 1}
def U : Submonoid ℍ[ℝ] := unitary ℍ[ℝ]
/-! ## Auxiliary structural lemmas for `SU 2` -/
/-
The first row of an `SU 2` matrix has unit norm:
`|M₀₀|² + |M₀₁|² = 1`.
-/
lemma SU2_norm (M : SU 2) : (M.val 0 0).re ^ 2 + (M.val 0 0).im ^ 2 +
    (M.val 0 1).re ^ 2 + (M.val 0 1).im ^ 2 = 1 := by
  have := M.2;
  obtain ⟨ h₁, h₂ ⟩ := this;
  have := h₁;
  replace := congr_fun ( congr_fun this.2 0 ) 0; simp_all +decide [ Matrix.mul_apply, Complex.ext_iff ];
  linarith
/-
For `M ∈ SU 2`, the entry `M₁₀` equals `-conj M₀₁`.
-/
lemma SU2_entry_10 (M : SU 2) : M.val 1 0 = - (starRingEnd ℂ) (M.val 0 1) := by
  have h_star_conj : M.val.conjTranspose = M.val⁻¹ := by
    rw [ Matrix.inv_eq_left_inv ];
    convert M.2.1.1;
  replace h_star_conj := congr_fun ( congr_fun h_star_conj 1 ) 0; simp_all +decide [ Matrix.inv_def ] ;
  simp_all +decide [ Matrix.det_fin_two, Matrix.adjugate_fin_two ];
  have := M.2.2; simp_all +decide [ Matrix.det_fin_two ] ;
/-
For `M ∈ SU 2`, the entry `M₁₁` equals `conj M₀₀`.
-/
lemma SU2_entry_11 (M : SU 2) : M.val 1 1 = (starRingEnd ℂ) (M.val 0 0) := by
  obtain ⟨h₁, h₂⟩ := M;
  convert congr_arg ( fun m : Matrix ( Fin 2 ) ( Fin 2 ) ℂ => ( starRingEnd ℂ ) ( m 0 0 ) ) ( Matrix.inv_eq_left_inv ( show h₁ * h₁.conjTranspose = 1 from by
                                                                                                                        exact h₂.1.2 ) ) using 1;
  rw [ Matrix.inv_def ] ; simp +decide [ Matrix.det_fin_two, Matrix.adjugate_fin_two ] ; ring_nf;
  have := h₂.2; simp_all +decide [ Matrix.det_fin_two ] ;
/-! ## SU 2 ↔ S³ -/
-- /- SU 2 ↦ S³ -/
-- def SU2_to_S₃ (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ
--   | 0 => (M 0 0).re  -- u₁
--   | 1 => (M 0 0).im  -- v₁
--   | 2 => (M 0 1).re  -- u₂
--   | 3 => (M 0 1).im  -- v₂
/-- The underlying point on `S³` associated to an `SU 2` matrix. -/
def SU2_to_S₃_fun (M : SU 2) : Fin 4 → ℝ := fun i =>
  match i with
  | 0 => (M.val 0 0).re
  | 1 => (M.val 0 0).im
  | 2 => (M.val 0 1).re
  | 3 => (M.val 0 1).im

lemma SU2_to_S₃_mem (M : SU 2) : SU2_to_S₃_fun M ∈ S₃ := by
  convert SU2_norm M using 1

/- SU 2 ↦ S³ -/
def SU2_to_S₃ (M : SU 2) : S₃ := ⟨SU2_to_S₃_fun M, SU2_to_S₃_mem M⟩

-- /- S³ ↦ SU 2 -/
-- def S₃_to_SU2 (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
--   !![⟨x 0, x 1⟩, ⟨x 3, x 4⟩; ⟨-x 3, x 4⟩, ⟨x 0, -x 1⟩]

/-- The `SU 2` matrix associated to a point on `S³`.
Note: the original draft used the out-of-range index `x 4` (a `Fin 4` index, which
wraps around to `x 0`); the mathematically correct definition uses the components
`x 2` and `x 3`, giving the standard quaternionic parametrization
`!![a, b; -conj b, conj a]` with `a = x₀ + i x₁`, `b = x₂ + i x₃`. -/
def S₃_to_SU2_mat (x : S₃) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨x.val 0, x.val 1⟩, ⟨x.val 2, x.val 3⟩; ⟨-x.val 2, x.val 3⟩, ⟨x.val 0, -x.val 1⟩]

lemma S₃_to_SU2_mem (x : S₃) : S₃_to_SU2_mat x ∈ SU 2 := by
  constructor;
  · refine' ⟨ _, _ ⟩;
    · ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, S₃_to_SU2_mat, Complex.ext_iff ];
      · exact ⟨ by linarith [ x.2.symm ], by ring ⟩;
      · constructor <;> ring;
      · constructor <;> ring;
      · exact ⟨ by linarith [ x.2.symm ], by ring ⟩;
    · ext i j ; fin_cases i <;> fin_cases j <;> simp +decide [ S₃_to_SU2_mat, Matrix.mul_apply, Fin.sum_univ_succ ];
      · simp +decide [ Complex.ext_iff ];
        exact ⟨ by linarith [ x.2.symm ], by ring ⟩;
      · simp +decide [ Complex.ext_iff ];
        constructor <;> ring;
      · simp +decide [ Complex.ext_iff ];
        constructor <;> ring;
      · norm_num [ Complex.ext_iff ];
        exact ⟨ by linarith [ x.2.symm ], by ring ⟩;
  · simp +decide [ S₃_to_SU2_mat, Matrix.det_fin_two ];
    norm_num [ Complex.ext_iff ];
    exact ⟨ by linarith [ x.2.symm ], by ring ⟩

/- S³ ↦ SU 2 -/
def S₃_to_SU2 (x : S₃) : SU 2 := ⟨S₃_to_SU2_mat x, S₃_to_SU2_mem x⟩

/-! ## SU 2 ↔ U (unit quaternions) -/
-- /- SU 2 ↦ U -/
-- def SU2_to_U (M : Matrix (Fin 2) (Fin 2) ℂ) : ℍ[ℝ] :=
--   ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩

/-- The unit quaternion associated to an `SU 2` matrix. -/
def SU2_to_U_quat (M : SU 2) : ℍ[ℝ] :=
  ⟨(M.val 0 0).re, (M.val 0 0).im, (M.val 0 1).re, (M.val 0 1).im⟩

lemma SU2_to_U_mem (M : SU 2) : SU2_to_U_quat M ∈ U := by
  have h_norm : (SU2_to_U_quat M).re^2 + (SU2_to_U_quat M).imI^2 + (SU2_to_U_quat M).imJ^2 + (SU2_to_U_quat M).imK^2 = 1 := by
    convert SU2_norm M using 1;
  constructor;
  · ext <;> simp +decide [ *, mul_comm ];
    linarith;
  · ext <;> simp +decide [ * ] <;> ring_nf!;
    exact h_norm

/- SU 2 ↦ U -/
def SU2_to_U (M : SU 2) : U := ⟨SU2_to_U_quat M, SU2_to_U_mem M⟩

-- /- U ↦ SU 2 -/
-- def U_to_SU2 (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
--   !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]
/-- The `SU 2` matrix associated to a unit quaternion. -/

def U_to_SU2_mat (q : U) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.val.re, q.val.imI⟩, ⟨q.val.imJ, q.val.imK⟩; ⟨-q.val.imJ, q.val.imK⟩, ⟨q.val.re, -q.val.imI⟩]

lemma U_to_SU2_mem (q : U) : U_to_SU2_mat q ∈ SU 2 := by
  simp +decide [ Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.det_fin_two ];
  simp +decide [ ← Matrix.ext_iff, Fin.forall_fin_two, U_to_SU2_mat ];
  have hq : q.val.re ^ 2 + q.val.imI ^ 2 + q.val.imJ ^ 2 + q.val.imK ^ 2 = 1 := by
    have := q.2;
    convert congr_arg ( fun x : ℍ[ℝ] => x.re ) ( this.2 ) using 1;
    simp +decide [ Quaternion.re_mul, star ] ; ring;
  norm_num [ Complex.ext_iff, Matrix.vecMul, dotProduct ];
  grind

/- U ↦ SU 2 -/
def U_to_SU2 (q : U) : SU 2 := ⟨U_to_SU2_mat q, U_to_SU2_mem q⟩

/-! ## The equivalences -/
lemma SU2_equiv_S₃_left_inv (M : SU 2) : S₃_to_SU2 (SU2_to_S₃ M) = M := by
  ext i j ; fin_cases i <;> fin_cases j <;> simp +decide [ S₃_to_SU2, S₃_to_SU2_mat, SU2_to_S₃, SU2_to_S₃_fun ];
  · convert SU2_entry_10 M |> Eq.symm using 1;
    exact Complex.ext ( by norm_num ) ( by norm_num );
  · convert SU2_entry_11 M |> Eq.symm using 1

lemma SU2_equiv_S₃_right_inv (x : S₃) : SU2_to_S₃ (S₃_to_SU2 x) = x := by
  exact Subtype.ext ( by ext i; fin_cases i <;> rfl )

/- SU 2 = {!![a, b; -star b, star a] | a, b ∈ ℂ, |a|² + |b|² = 1}
    a = u₁ + iv₁, b = u₂ + iv₂ → u₁² + v₁² + u₂² + v₂² = 1 -/
def SU2_equiv_S₃ : SU 2 ≃ S₃ where
  toFun M := SU2_to_S₃ M
  invFun x := S₃_to_SU2 x
  left_inv := SU2_equiv_S₃_left_inv
  right_inv := SU2_equiv_S₃_right_inv

lemma SU2_equiv_U_left_inv (M : SU 2) : U_to_SU2 (SU2_to_U M) = M := by
  apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [U_to_SU2, U_to_SU2_mat, SU2_to_U, SU2_to_U_quat, Complex.ext_iff];
  · have := SU2_entry_10 M; simp_all +decide [ Complex.ext_iff ] ;
  · have := SU2_entry_11 M; simp_all +decide [ Complex.ext_iff ] ;

lemma SU2_equiv_U_right_inv (q : U) : SU2_to_U (U_to_SU2 q) = q := by
  convert Subtype.ext ?_;
  convert Quaternion.ext_iff.mpr ?_ ; aesop

lemma SU2_equiv_U_map_mul (M N : SU 2) : SU2_to_U (M * N) = SU2_to_U M * SU2_to_U N := by
  unfold SU2_to_U;
  ext;
  · simp +decide [ SU2_to_U_quat, Matrix.mul_apply ];
    rw [ SU2_entry_10 N ] ; norm_num ; ring;
  · simp +decide [ SU2_to_U_quat, Matrix.mul_apply ];
    rw [ show ( N : Matrix ( Fin 2 ) ( Fin 2 ) ℂ ) 1 0 = - ( starRingEnd ℂ ) ( N.val 0 1 ) from SU2_entry_10 N ] ; norm_num ; ring;
  · simp +decide [ SU2_to_U_quat, Matrix.mul_apply ];
    rw [ show ( N : Matrix ( Fin 2 ) ( Fin 2 ) ℂ ) 1 1 = ( starRingEnd ℂ ) ( N.val 0 0 ) from SU2_entry_11 N ] ; norm_num ; ring;
  · simp +decide [ SU2_to_U_quat, Matrix.mul_apply, Fin.sum_univ_two ];
    rw [ SU2_entry_11 N ] ;
    norm_num [ Complex.ext_iff ] ; ring

/- (u₁ + iv₁) + (u₂ + iv₂)j = u₁ + iv₁ + ju₂ + kv₂ (∵ ij = k)
    u₁² + v₁² + u₂² + v₂² = 1 -/
def SU2_equiv_U : SU 2 ≃* U where  -- 乗法の保存
  toFun M := SU2_to_U M
  invFun q := U_to_SU2 q
  left_inv := SU2_equiv_U_left_inv
  right_inv := SU2_equiv_U_right_inv
  map_mul' := SU2_equiv_U_map_mul

#min_imports
