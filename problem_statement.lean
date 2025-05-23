import Mathlib

open scoped Matrix

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

def proj_xy (v : ℝ³) : ℝ² := ![v 0, v 1]

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- The Rupert Property for a convex polyhedron specified as
    an indexed finite set of vertices. -/
def IsRupert {ι : Type} [Fintype ι] (vertices : ι → ℝ³) : Prop :=
   ∃ inner_rotation ∈ SO3, ∃ inner_offset : ℝ², ∃ outer_rotation ∈ SO3,
   let hull := convexHull ℝ { vertices i | i }
   let inner_shadow := { inner_offset + proj_xy (inner_rotation *ᵥ p) | p ∈ hull }
   let outer_shadow := { proj_xy (outer_rotation *ᵥ p) | p ∈ hull }
   inner_shadow ⊆ interior outer_shadow

noncomputable def triakis_tetrahedron : Fin 8 → ℝ³ :=
  ![![   1,    1,    1],
    ![   1,   -1,   -1],
    ![  -1,    1,   -1],
    ![  -1,   -1,    1],
    ![-3/5,  3/5,  3/5],
    ![ 3/5, -3/5,  3/5],
    ![ 3/5,  3/5, -3/5],
    ![-3/5, -3/5, -3/5]]


theorem main_result : IsRupert triakis_tetrahedron := sorry
