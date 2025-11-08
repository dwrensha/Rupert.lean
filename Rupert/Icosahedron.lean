import Mathlib.NumberTheory.Real.GoldenRatio
import Rupert.Basic
import Rupert.Convex
import Rupert.MatrixSimps
import Rupert.Quaternion
import Rupert.Equivalences.RupertEquivRupertPrime

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
