import Rupert.Basic
import Rupert.Convex
import Rupert.FinCases
import Rupert.MatrixSimps
import Rupert.Quaternion
import Rupert.Equivalences.RupertEquivRupertPrime

namespace TriakisTetrahedron

open scoped Matrix

/- This is tom7's triakis tetrahedron scaled by 3/5, so that the
   first four vertices make up a regular tetrahedron with nice unit
   coordinates, and the remaining vertices represent the augmentations
   of each of the faces of that tetrahedron. -/

noncomputable def vertices : Fin 8 → ℝ³ :=
  ![![   1,    1,    1],
    ![   1,   -1,   -1],
    ![  -1,    1,   -1],
    ![  -1,   -1,    1],
    ![-3/5,  3/5,  3/5],
    ![ 3/5, -3/5,  3/5],
    ![ 3/5,  3/5, -3/5],
    ![-3/5, -3/5, -3/5]]

def inner_quat : Quaternion ℝ := ⟨0.144873924, 0.365747659, -0.854692880, -0.338733344⟩

def inner_offset : ℝ² := ![8.5629464761e-05, 8.9387250451e-05]

def outer_quat : Quaternion ℝ := ⟨0.858732110, -0.148912807, -0.352436516, -0.340870417⟩

noncomputable def inner_rot := matrix_of_quat inner_quat

lemma inner_rot_so3 : inner_rot ∈ SO3 := by
  have h : inner_quat.normSq ≠ 0 := by norm_num [inner_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

noncomputable def outer_rot := matrix_of_quat outer_quat

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
  have h : outer_quat.normSq ≠ 0 := by norm_num [outer_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

set_option maxHeartbeats 400000 in
theorem rupert : IsRupert vertices := by
  rw [rupert_iff_rupert']
  use inner_rot, inner_rot_so3, inner_offset, outer_rot, outer_rot_so3
  intro inner_shadow outer_shadow
  let ε₀ : ℝ := 0.006
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  have hb : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
    refine Convex.ball_in_hull_of_corners_in_hull hε₀ ?_ ?_ ?_ ?_ <;>
      apply mem_convexHull_iff_exists_fintype.mpr <;>
      use Fin 8, Fin.fintype 8
    <;> [
      use ![0, 0, 0,
            209107410810126884571/565617601328354816800,
            245824061168864729/35351100083022176050,
            0,
            70515401107905219313/113123520265670963360,
            0];
      use ![0,
            1051981313303264779479/2828088006641774084000,
            0,
            19719000787634436/6798288477504264625,
            353580717802170675829/565617601328354816800,
            0, 0, 0];
      use ![3938334956654107739/8031045263445271000,
            2045224314929433491/8031045263445271000,
            0,
            204748599186172977/803104526344527100,
            0, 0, 0, 0];
      use ![0,
            1095105012905906001/353511000830221760500,
            0,
            1052120747247162610137/2828088006641774084000,
            0, 0,
            353441283858272845171/565617601328354816800,
            0]
    ]
    all_goals
      use fun i ↦ proj_xy (outer_rot *ᵥ vertices i)
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply all_fin_8_vec <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
                   Fin.sum_univ_eight, ε₀, matrix_simps]
        norm_num
  intro v hv
  let ε₁ : ℝ := 1e-11
  have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
  refine Convex.mem_interior_hull hε₀.1 hε₁ hb ?_
  simp only [inner_shadow] at hv
  obtain ⟨y, hy⟩ := hv
  rw [mem_convexHull_iff_exists_fintype]
  fin_cases y <;>
    simp only [vertices, Fin.reduceFinMk, Matrix.cons_val] at hy <;>
    use Fin 8, Fin.fintype 8
  <;> [
    use ![320050956502833201167751985054675539223111361/
          158836228761182627011085302790150062539835294740000,
          37478789684155822552149249633100762035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          2646640498675699472588866429808865118371007380481/
          2647270479353043783518088379835834375663921579000,
          0, 0, 0, 0];
    use ![2690065380721338931107844675930079853008002249/
          1429526058850643643099767725111350562858517652660000,
          1429185801354497250493132886580886682858320659198011/
          1429526058850643643099767725111350562858517652660000,
          0,
          5626123846094521128395511429799165339066424329/
          23825434314177394051662795418522509380975294211000,
          0, 0, 0, 0];
    use ![282844578280123522478732365155221962237373746450249/
          298290854644984786267344341448022649016038391108000,
          0, 0, 0,
          1716079538871724601954309613272108094228427903699/
          33143428293887198474149371272002516557337599012000,
          0,
          78025750787118551159488667585696530439676223/
          14914542732249239313367217072401132450801919555400,
          0];
    use ![283117566838487610246913017563019376237373746450249/
          298290854644984786267344341448022649016038391108000,
          0, 0, 0,
          1574537650882650012051296636476848055851133291/
          298290854644984786267344341448022649016038391108000,
          0,
          758585663442314668520963629418339796530439676223/
          14914542732249239313367217072401132450801919555400,
          0];
    use ![15381264075549739501273188093551493041527383361/
          33143428293887198474149371272002516557337599012000,
          0, 0, 0,
          99383630567848375480456938122952631882685283711097/
          99430284881661595422448113816007549672012797036000,
          0,
          25526079328536174367806438713165510146558741/
          4971514244083079771122405690800377483600639851800,
          0];
    use ![31436375570010867744955561974649501075539223111361/
          158836228761182627011085302790150062539835294740000,
          65162484389967530498892502615908096362035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          3111868440060211438361861909979623255113022141443/
          7941811438059131350554265139507503126991764737000,
          0, 0, 0, 0];
    use ![31418176332786595227076851814129673475539223111361/
          158836228761182627011085302790150062539835294740000,
          62237357220617638995747652173682152362035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          1086344920129639879804346646705637278371007380481/
          2647270479353043783518088379835834375663921579000,
          0, 0, 0, 0];
    use ![46105713581088386527939179642742079124582150083/
          99430284881661595422448113816007549672012797036000,
          0, 0, 0,
          499295037844618876866011627687882685283711097/
          99430284881661595422448113816007549672012797036000,
          0,
          4969183993652133120852165431236855985510146558741/
          4971514244083079771122405690800377483600639851800,
          0]
  ]
  all_goals
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply all_fin_8_vec <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
