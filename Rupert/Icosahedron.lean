import Mathlib.NumberTheory.Real.GoldenRatio
import Rupert.Basic
import Rupert.Convex
import Rupert.MatrixSimps
import Rupert.Quaternion
import Rupert.Equivalences.RupertEquivRupertPrime

namespace Icosahedron

open scoped Matrix goldenRatio

noncomputable def icosahedron : Fin 12 → ℝ³ := ![
  ![ 1,  φ,  0],
  ![ 1, -φ,  0],
  ![-1,  φ,  0],
  ![-1, -φ,  0],
  ![ φ,  0,  1],
  ![ φ,  0, -1],
  ![-φ,  0,  1],
  ![-φ,  0, -1],
  ![ 0,  1,  φ],
  ![ 0,  1, -φ],
  ![ 0, -1,  φ],
  ![ 0, -1, -φ]]

proof_wanted rupert : IsRupert icosahedron
