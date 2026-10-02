import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open Quaternion Matrix Complex

noncomputable section

/- `SU(n)` — 特殊ユニタリ群 -/
abbrev SU (n : ℕ) := specialUnitaryGroup (Fin n) ℂ

/- `Definition14` -/
/-- SO(3) := {R ∈ O(3) | det R = 1}, O(3) := {Q ∈ GL(3, ℝ) | Qᵗ = Q⁻¹} --/
abbrev SO (n : ℕ) := specialOrthogonalGroup (Fin n) ℝ

-- 単位四元数 : {q ∈ ℍ[ℝ] | q * star q = 1}
abbrev U : Submonoid ℍ[ℝ] := unitary ℍ[ℝ]

end
