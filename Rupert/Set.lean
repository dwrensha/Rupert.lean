import Rupert.Basic

open scoped Matrix

/-- The Rupert Property for a pair of subsets X, Y of ℝ³. X has the
    Rupert property with respect to Y if there such that the shadow of
    X fits "comfortably" within the shadow of Y under affine
    transformations. By "comfortably" we mean the closure of one set is
    a subset of the interior of the other. This definition rules out
    trivial cases of a set fitting inside itself. -/
def IsRupertPair (inner outer : Set ℝ³) : Prop :=
   ∃ outer_rot ∈ SO3, ∃ inner_rot ∈ SO3, ∃ inner_offset : ℝ²,
   let outer_shadow := (fun p ↦ dropz (outer_rot *ᵥ p)) '' outer
   let inner_shadow := (fun p ↦ inner_offset + dropz (inner_rot *ᵥ p)) '' inner
   closure inner_shadow ⊆ interior outer_shadow

/-- The Rupert Property for a subset S of ℝ³. S has the Rupert property if there
    are rotations and translations such that one 2-dimensional "shadow" of S can
    be made to fit entirely inside the interior of another such "shadow". -/
def IsRupertSet (S : Set ℝ³) : Prop := IsRupertPair S S

/-- This is a lemma required for showing that the rupert property as defined
    for convex polyhedra is equivalent to the above property. -/
lemma affine_imp_closed {n m : ℕ} (f : E n →ᵃ[ℝ] E m) : IsClosedMap f :=
 sorry
