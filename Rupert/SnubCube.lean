import Rupert.Basic

namespace SnubCube

noncomputable abbrev cbrt (x : ℝ) : ℝ := x ^ (1/3 : ℝ)

/-- tribonacci constant-/
noncomputable def trib : ℝ :=
  (1 + cbrt (19 + 3 * √33) + cbrt (19 - 3 * √33) ) / 3

noncomputable def snub_cube : Fin 24 → ℝ³ :=
 ![ ![      -1,  1/trib,    trib],
    ![       1, -1/trib,    trib],
    ![       1,  1/trib,   -trib],
    ![      -1, -1/trib,   -trib],

    ![ -1/trib,    trib,       1],
    ![  1/trib,   -trib,       1],
    ![  1/trib,    trib,      -1],
    ![ -1/trib,   -trib,      -1],

    ![   -trib,       1,  1/trib],
    ![    trib,      -1,  1/trib],
    ![    trib,       1, -1/trib],
    ![   -trib,      -1, -1/trib],

    ![       1,   -trib, -1/trib],
    ![      -1,    trib, -1/trib],
    ![      -1,   -trib,  1/trib],
    ![      -1,    trib,  1/trib],

    ![  1/trib,      -1,   -trib],
    ![ -1/trib,       1,   -trib],
    ![ -1/trib,      -1,    trib],
    ![  1/trib,       1,    trib],

    ![     trib, -1/trib,     -1],
    ![    -trib,  1/trib,     -1],
    ![    -trib, -1/trib,      1],
    ![     trib,  1/trib,      1]
  ]

proof_wanted rupert : ¬ IsRupertPoly snub_cube
