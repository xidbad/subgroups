import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RepresentationTheory.Basic


open MatrixGroups Matrix Complex SpecialLinearGroup

noncomputable section


variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (ρ : Representation ℂ G V)  -- ρ : G →* (V →ₗ[ℂ] V) は G の ℂ-線型表現


def SU (n : ℕ) := specialUnitaryGroup (Fin n) ℂ


/-- The G-averaged inner product: `⟨u, v⟩_G = (1/|G|) ∑_{g ∈ G} ⟨ρ(g)(u), ρ(g)(v)⟩`. -/
def averagedInner (u v : V) : ℂ :=
  ((Fintype.card G : ℂ)⁻¹) * ∑ g : G, @inner ℂ V _ (ρ g u) (ρ g v)

set_option quotPrecheck false

notation "⟪"u", "v"⟫_G" => averagedInner ρ u v

notation "⟪"u","v"⟫" => star u ⬝ᵥ v


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

end


noncomputable section


variable (G : Subgroup SL(2, ℂ)) [Fintype G]


-- Arithtotle approach

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
  -- all_goals generalize_proofs at *
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
    · conv_lhs => rw [hH.spectral_theorem]
      rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      rfl
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
    · simp_all +decide [ SetLike.mem_coe, Matrix.mem_unitaryGroup_iff ];
      convert hU using 1
      simp [← mul_assoc, ← smul_assoc, ← hc.1]
      ring_nf; rfl
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
