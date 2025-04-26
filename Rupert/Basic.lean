import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Projects a vector from 3-space to 2-space by dropping the third coordinate. -/
def dropz {k : Type} [Field k] (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  ![v 0, v 1]

/-- The Rupert Property for a subset S of ℝ³. S has the Rupert property if there
    are rotations and translations such that one 2-dimensional "shadow" of S can
    be made to fit entirely inside the interior of another such "shadow". -/
def IsRupert (S : Set ℝ³) : Prop :=
   ∃ outer_rot ∈ SO3, ∃ inner_rot ∈ SO3, ∃ inner_offset : ℝ²,
   let outer_shadow := (fun p ↦ dropz (outer_rot *ᵥ p)) '' S
   let inner_shadow := (fun p ↦ inner_offset + dropz (inner_rot *ᵥ p)) '' S
   inner_shadow ⊆ interior outer_shadow

/-- The Rupert Property for a convex polyhedron given as an indexed finite set of vertices. -/
def IsRupertPoly {ι : Type} [Fintype ι] (v : ι → ℝ³) : Prop :=
   IsRupert (convexHull ℝ (Set.range v))

/-- Alternate formulation of the Rupert Property for polyhedra. This is equivalent to IsRupert and
    should be easier to prove. The inner shadow here only consists of the vertices, not
    the full convex hull; but properties of the convex hull imply that showing containment
    for those vertices suffices. -/
def IsRupertPoly' {ι : Type} [Fintype ι] (v : ι → ℝ³) : Prop :=
   ∃ outer_rot ∈ SO3, ∃ inner_rot ∈ SO3, ∃ inner_offset : ℝ²,
   let outer_shadow := Set.range (fun i ↦ dropz (outer_rot *ᵥ v i))
   let inner_shadow := Set.range (fun i ↦ inner_offset + dropz (inner_rot *ᵥ v i))
   inner_shadow ⊆ interior (convexHull ℝ outer_shadow)
