import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.Matrix.Order

open BigOperators Real Nat Matrix
open Classical Pointwise ComplexInnerProductSpace MatrixOrder ComplexOrder

noncomputable section



variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (ρ : Representation ℂ G V)

/-- The averaged Hermitian inner product over a finite group representation:
  `invariantInner ρ u v = ∑ g : G, ⟪ρ g u, ρ g v⟫_ℂ`. -/
def invariantInner (u v : V) : ℂ :=
  ∑ g : G, @inner ℂ V _ (ρ g u) (ρ g v)

/-! ### G-Invariance -/

/-
The averaged inner product is invariant under the group action:
  `invariantInner ρ (ρ h u) (ρ h v) = invariantInner ρ u v` for all `h : G`.
-/
theorem invariantInner_invariant (h : G) (u v : V) :
    invariantInner ρ (ρ h u) (ρ h v) = invariantInner ρ u v := by
  -- Let's denote the inner product by $\langle \cdot, \cdot \rangle$ and rewrite the sums accordingly.
  unfold invariantInner;
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulRight h)]; simp +decide [mul_assoc]

/-! ### Inner product axioms -/

theorem invariantInner_conj_symm (u v : V) :
    starRingEnd ℂ (invariantInner ρ v u) = invariantInner ρ u v := by
  simp +decide [invariantInner]

theorem invariantInner_add_left (u v w : V) :
    invariantInner ρ (u + v) w = invariantInner ρ u w + invariantInner ρ v w := by
  convert Finset.sum_add_distrib.symm using 1 ;
  convert Finset.sum_congr rfl fun g _ => ?_;
  convert Finset.sum_add_distrib.symm using 1;
  exacts [fun g => inner ℂ (ρ g u) (ρ g w), fun g => inner ℂ (ρ g v) (ρ g w), by simp +decide, by simp +decide [Finset.sum_add_distrib, invariantInner]]

theorem invariantInner_smul_left (u v : V) (r : ℂ) :
    invariantInner ρ (r • u) v = starRingEnd ℂ r * invariantInner ρ u v := by
  unfold invariantInner; simp +decide [ mul_comm];
  rw [Finset.sum_mul _ _ _]

theorem invariantInner_nonneg (u : V) :
    0 ≤ RCLike.re (invariantInner ρ u u) := by
  unfold invariantInner;
  simp +decide only [inner_self_eq_norm_sq_to_K];
  norm_cast ; exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem invariantInner_definite (u : V) (hu : invariantInner ρ u u = 0) : u = 0 := by
  contrapose! hu with h_nonzero
  generalize_proofs at *; (
  -- By definition of invariant inner product, we have:
  unfold invariantInner
  simp_all +decide;
  exact_mod_cast ne_of_gt (lt_of_lt_of_le (by simp [h_nonzero]) (Finset.single_le_sum (fun x _ => sq_nonneg (‖ρ x u‖)) (Finset.mem_univ 1))))

/-! ### Construction of InnerProductSpace.Core -/

/-- The averaged inner product forms a valid inner product space core.
This witnesses that the averaging construction produces a genuine Hermitian
inner product on `V`, which is `G`-invariant by `invariantInner_invariant`. -/
@[reducible]
def invariantInnerCore : @InnerProductSpace.Core ℂ V _ inferInstance inferInstance where
  inner := invariantInner ρ
  conj_inner_symm := invariantInner_conj_symm ρ
  add_left := invariantInner_add_left ρ
  smul_left := invariantInner_smul_left ρ
  re_inner_nonneg := invariantInner_nonneg ρ
  definite := invariantInner_definite ρ



/-- The underlying `2 × 2` complex matrix of an element of a subgroup of `SL(2, ℂ)`. -/
def toMat (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (g : G) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((g : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
/-- The averaged (Reynolds) Gram matrix `H = ∑_{g ∈ G} gᴴ * g`, encoding the `G`-invariant
Hermitian inner product `⟨·,·⟩_G`. -/
def H (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) [Fintype G] :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ g : G, (toMat G g)ᴴ * (toMat G g)
variable (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ))
/-- `toMat` is multiplicative. -/
lemma toMat_mul (g h : G) : toMat G (g * h) = toMat G g * toMat G h := by
  simp [toMat, Matrix.SpecialLinearGroup.coe_mul]
/-- Every element of `G` has determinant `1`. -/
lemma toMat_det (g : G) : (toMat G g).det = 1 :=
  g.1.2
/-- Every element of `G` is an invertible matrix. -/
lemma toMat_isUnit (g : G) : IsUnit (toMat G g) :=
  (Matrix.isUnit_iff_isUnit_det _).2 <| by simp [toMat_det]
/-- The averaged Gram matrix is positive definite: this is the statement that `⟨·,·⟩_G` is a
positive definite Hermitian inner product. -/
lemma H_posDef [Fintype G] : (H G).PosDef := by
  refine Matrix.posDef_sum ⟨1, Finset.mem_univ _⟩ ?_
  intro i _
  refine (Matrix.PosSemidef.posDef_iff_isUnit
    (Matrix.posSemidef_conjTranspose_mul_self _)).mpr ?_
  exact (Matrix.isUnit_iff_isUnit_det _).2 (by simp [toMat_det])
/-- **Invariance of the averaged form.**  For every `h ∈ G` we have `hᴴ * H * h = H`,
i.e. `⟨h u, h v⟩_G = ⟨u, v⟩_G`. -/
lemma H_invariant [Fintype G] (h : G) :
    (toMat G h)ᴴ * H G * (toMat G h) = H G := by
  convert Equiv.sum_comp (Equiv.mulRight h) (fun g => (toMat G g)ᴴ * (toMat G g)) using 1
  simp [H, Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc, toMat_mul]
/-- **Proposition 10.**  Every finite subgroup `G` of `SL(2, ℂ)` is conjugate to a subgroup
of `SU(2)`: there is an invertible matrix `P` with `P * g * P⁻¹ ∈ SU(2)` for all `g ∈ G`. -/
theorem conj_into_specialUnitaryGroup [Fintype G] :
    ∃ P : Matrix (Fin 2) (Fin 2) ℂ, IsUnit P ∧
      ∀ g : G, P * toMat G g * P⁻¹ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hpd := H_posDef G
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 2) (Fin 2) ℂ, P.PosDef ∧ P * P = H G :=
    ⟨_, hpd.isStrictlyPositive.sqrt.posDef, CFC.sqrt_mul_sqrt_self _⟩
  refine ⟨P, hP.1.isUnit, fun g => ?_⟩
  have h_unitary : (P * toMat G g * P⁻¹)ᴴ * (P * toMat G g * P⁻¹) = 1 := by
    have := hP.1.1
    simp_all only [Matrix.mul_assoc, Matrix.conjTranspose_mul]
    simp_all only [Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv]
    simp_all only [← mul_assoc, H_invariant]
    simp [← hP.2, hP.1.det_pos.ne']
  refine ⟨⟨h_unitary, by rw [← mul_eq_one_comm] at h_unitary; aesop⟩, ?_⟩
  rw [SetLike.mem_coe, MonoidHom.mem_mker]
  show (P * toMat G g * P⁻¹).det = 1
  simp only [Matrix.det_mul, Matrix.det_nonsing_inv]
  rw [mul_right_comm, Ring.mul_inverse_cancel P.det
    ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.isUnit), one_mul, toMat_det]


end

#min_imports
