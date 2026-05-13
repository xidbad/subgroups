import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup

open MatrixGroups Matrix

def SU (n : ℕ) := specialUnitaryGroup (Fin n) ℂ

instance SU2 : Subgroup SL(2, ℂ) where
  carrier := {M : SL(2, ℂ) | M.val ∈ SU 2}  -- SU(2) の行列を SL(2, ℂ) の部分集合として定義

  one_mem' := by simp [SU]                -- 単位元が含まれること

  mul_mem' := by                          -- 乗法に関して閉じていること
    intro A B HA HB
    simp [SU] at *
    sorry

  inv_mem' := by                          -- 逆元に関して閉じていること
    intro A HA
    simp [SU] at *
    sorry


theorem conjugate_finite_subgroup_into_SU2 (G : Subgroup SL(2, ℂ)) [Finite G] :
    ∃ P : SL(2, ℂ), ∀ g ∈ G, (P * g * P⁻¹ : SL(2, ℂ)).val ∈ SU 2 := by
  sorry

#min_imports
