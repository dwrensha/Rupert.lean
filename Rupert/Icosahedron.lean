module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Rupert.Basic
public import Rupert.Convex
public meta import Rupert.MatrixSimps
public import Rupert.Quaternion
public import Rupert.Equivalences.RupertEquivRupertPrime

@[expose] public section

namespace Icosahedron

open scoped Matrix goldenRatio

noncomputable def icosahedron : Fin 12 → ℝ³ := ![
  !₂[ 1,  φ,  0],
  !₂[ 1, -φ,  0],
  !₂[-1,  φ,  0],
  !₂[-1, -φ,  0],
  !₂[ φ,  0,  1],
  !₂[ φ,  0, -1],
  !₂[-φ,  0,  1],
  !₂[-φ,  0, -1],
  !₂[ 0,  1,  φ],
  !₂[ 0,  1, -φ],
  !₂[ 0, -1,  φ],
  !₂[ 0, -1, -φ]]

proof_wanted rupert : IsRupert icosahedron
