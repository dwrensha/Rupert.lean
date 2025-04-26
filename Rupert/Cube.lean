import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion

namespace Cube

def cube : Fin 8 → ℝ³ := ![
  ![ 1,  1,  1],
  ![ 1, -1,  1],
  ![-1, -1,  1],
  ![-1,  1,  1],
  ![ 1,  1, -1],
  ![ 1, -1, -1],
  ![-1, -1, -1],
  ![-1,  1, -1]]

section rotations
open Real
open Matrix
-- Rotate by just enough about the y-axis to bring (1, 0, √2/2) to (0, 0, z) for some z.
-- Take cos⁻¹ to find out the angle.
def outer_rot2 : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  sorry

-- Rotate 45° by x-axis
noncomputable
def outer_rot1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
 let q : Quaternion ℝ := ⟨cos (π/8), sin (π/8), 0, 0⟩
 have qnz : q.normSq ≠ 0 := by
   rw [Quaternion.normSq_def']
   simp only [q, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
              add_zero, cos_sq_add_sin_sq, one_ne_zero]
 let M := matrix_of_quat q
 let res := M *ᵥ ![1,1,1]
 have : res = ![1, √2, 0] := by
   simp only [res, M, matrix_of_quat, q, Matrix.mulVec]
   simp [Matrix.of_apply]
   ext i; fin_cases i
   · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Function.comp_apply, cons_val_zero,
     head_cons, tail_cons, add_zero]; sorry
   · sorry
   · sorry
 ⟨M, matrix_of_quat_is_s03 qnz⟩

noncomputable
def outer_rot := outer_rot2 * outer_rot1

end rotations

proof_wanted rupert : IsRupertPoly cube
