import Mathlib.Analysis.Quaternion


open Quaternion Matrix


noncomputable section


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
  rw [frameQuaternion_star, frameQuaternion]
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  simp [mul_assoc, F.I_sq, smul_smul]
  have cos_comm : ∀ q : ℍ[ℝ], (Real.cos θ : ℍ[ℝ]) * q = q * (Real.cos θ : ℍ[ℝ]) := by
    intro q
    simp [Quaternion.ext_iff, mul_comm]
  conv_lhs =>
    lhs
    rw [show (Real.cos θ : ℍ[ℝ]) = Real.cos θ • (1 : ℍ[ℝ]) from by simp [Algebra.smul_def]]
  rw [smul_mul_assoc, mul_smul, smul_smul]
  simp [smul_smul]
  have h1 : Real.sin θ • (Real.cos θ : ℍ[ℝ]) = (Real.sin θ * Real.cos θ : ℝ) • (1 : ℍ[ℝ]) := by
    rw [show (Real.cos θ : ℍ[ℝ]) = Real.cos θ • (1 : ℍ[ℝ]) from by simp [Algebra.smul_def]]
    rw [smul_smul]
  rw [h1]
  ring_nf
  have h2 : Real.cos θ ^ 2 • F.I + -((Real.cos θ * Real.sin θ : ℝ) • (1 : ℍ[ℝ])) -
      (-((Real.cos θ * Real.sin θ : ℝ) • (1 : ℍ[ℝ])) + -(Real.sin θ ^ 2 • F.I)) =
      Real.cos θ ^ 2 • F.I + Real.sin θ ^ 2 • F.I := by module
  rw [h2]
  rw [← add_smul]
  rw [show (Real.cos θ ^ 2 + Real.sin θ ^ 2 : ℝ) = 1 by linarith [Real.cos_sq_add_sin_sq θ]]
  simp



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
  have h1 : ∀ (q : ℍ[ℝ]) (r : ℝ), q * ↑r = r • q := by
    intro q r
    rw [show (r : ℍ[ℝ]) = r • (1 : ℍ[ℝ]) by simp [Quaternion.ext_iff]]
    rw [mul_smul_comm, mul_one]
  rw [h1 (F.K) (Real.cos θ)]
  simp
  have h2 : ∀ (q : ℍ[ℝ]) (r : ℝ), ↑r * q = r • q := by
    intro q r
    rw [show (r : ℍ[ℝ]) = r • (1 : ℍ[ℝ]) by simp [Quaternion.ext_iff]]
    rw [smul_mul_assoc, one_mul]
  rw [h2 (F.K) (Real.cos θ)]
  rw [h2 (F.J) (Real.cos θ)]
  rw [F.IK]
  simp [smul_smul]
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


lemma pre15 : ∃ h : U →* SO 3, Function.Surjective h ∧ h.ker = plusminusone := by
  sorry


/-- π = h ∘ f⁻¹ : SU 2 → U → SO3, f = U_to_SU2 -/
theorem theorem_15 : ∃ π : SU 2 →* SO 3, Function.Surjective π ∧ π.ker = plusminusI := by
  sorry


def theorem15 [plusminusI.Normal] (π : SU 2 →* SO 3) (surj : Function.Surjective π)
    (kern : π.ker = plusminusI) : SU 2 ⧸ plusminusI ≃* SO 3 :=
  (QuotientGroup.quotientMulEquivOfEq kern.symm).trans (QuotientGroup.quotientKerEquivOfSurjective π surj)


end

#min_imports
