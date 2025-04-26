import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion
import Rupert.RelatingRupertDefs

namespace TriakisTetrahedron

open scoped Matrix

noncomputable def triakis_tetrahedron : Fin 8 → ℝ³ := ![
  ![ 5/3,  5/3,  5/3],
  ![ 5/3, -5/3, -5/3],
  ![-5/3,  5/3, -5/3],
  ![-5/3, -5/3,  5/3],
  ![-1,  1,  1],
  ![ 1, -1,  1],
  ![ 1,  1, -1],
  ![-1, -1, -1]]

def outer_quat : Quaternion ℝ :=
  ⟨0.858732110065,-0.148912807308,-0.352436516202,-0.340870416742⟩

noncomputable def outer_rot := matrix_of_quat outer_quat

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
  have h : outer_quat.normSq ≠ 0 := by norm_num [outer_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

def inner_quat : Quaternion ℝ :=
  ⟨0.144873924125,0.365747658601,-0.854692879512,-0.338733343572⟩

noncomputable def inner_rot := matrix_of_quat inner_quat

lemma inner_rot_so3 : inner_rot ∈ SO3 := by
  have h : inner_quat.normSq ≠ 0 := by norm_num [inner_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

def inner_offset : ℝ² := ![0.000142715774602, 0.000148978750753]

set_option maxHeartbeats 10000000 in
theorem rupert : IsRupertPoly triakis_tetrahedron := by
  rw [rupert_iff_rupert']
  use outer_rot, outer_rot_so3, inner_rot, inner_rot_so3, inner_offset
  intro outer_shadow inner_shadow
  let ε₀ : ℝ := 0.01
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  have hb : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
    refine Convex.ball_in_hull_of_corners_in_hull hε₀ ?_ ?_ ?_ ?_ <;>
      apply mem_convexHull_iff_exists_fintype.mpr <;>
      use Fin 8, inferInstance
    · use ![0, 0, 0,
            83642964337506769729117533/226247040567744020373512480,
            491648122303955969575009/70702200177420006366722650,
            0,
            705154011194322957708774591/1131235202838720101867562400,
            0]
      use fun i ↦ (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp [Fin.sum_univ_eight]
        simp [triakis_tetrahedron, dropz, outer_rot, matrix_of_quat, outer_quat,
              inner_offset, inner_rot, inner_quat]
        norm_num
    · use ![0,
            420792525388638879671739273/1131235202838720101867562400,
            0,
            205077608123644273950213/70702200177420006366722650,
            707161435720102913812619719/1131235202838720101867562400,
            0, 0, 0]
      use fun i ↦ (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp [Fin.sum_univ_eight]
        simp [triakis_tetrahedron, dropz, outer_rot, matrix_of_quat, outer_quat,
              inner_offset, inner_rot, inner_quat]
        norm_num
    · use ![140204724479442774822495653/285905211542650912387345000,
            9101248215348123613887828/35738151442831364048418125,
            0,
            72890501340423148653746723/285905211542650912387345000,
            0, 0, 0, 0]
      use fun i ↦ (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp [Fin.sum_univ_eight]
        simp [triakis_tetrahedron, dropz, outer_rot, matrix_of_quat, outer_quat,
              inner_offset, inner_rot, inner_quat]
        norm_num
    · use ![0,
            2190210027139292884895349/707022001774200063667226500,
            0,
            2104241494835000098649482803/5656176014193600509337812000,
            0, 0,
            706882567828297213521833281/1131235202838720101867562400,
            0]
      use fun i ↦ (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp [Fin.sum_univ_eight]
        simp [triakis_tetrahedron, dropz, outer_rot, matrix_of_quat, outer_quat,
              inner_offset, inner_rot, inner_quat]
        norm_num
  intro v hv
  let ε₁ : ℝ := 1e-12
  have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
  refine Convex.mem_interior_hull hε₀.1 hε₁ hb ?_
  simp only [Set.mem_range, inner_shadow] at hv
  obtain ⟨y, hy⟩ := hv
  rw [mem_convexHull_iff_exists_fintype]
  fin_cases y <;>
    simp only [triakis_tetrahedron, Fin.reduceFinMk, Matrix.cons_val, inner_shadow] at hy <;>
    use Fin 8, inferInstance
  · use ![1309493063853311989188997950220509368596236389211854804729/
          649784571686849234254536691595344803901954695176452885679250000,
          1686543416634666398765099635243795920564477511206069250952467/
          7147630288555341576799903607548792842921501646940981742471750000,
          0,
          3572964670357502261984628714468048310698941305414747171408972757/
          3573815144277670788399951803774396421460750823470490871235875000,
          0, 0, 0, 0]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_eight]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ triakis_tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, mul_neg,
        neg_mul, neg_neg, sub_neg_eq_add, triakis_tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_eight, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val, zero_mul, zero_smul, mul_one, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_empty,
        Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![1034476509223554955363512163103648633629773098563877142463/
          549817714504257044369223354426830218686269357456998595574750000,
          793992111220227290607894145967573982919877396429022896583439163/
          794181143172815730755544845283199204769055738548997971385750000,
          0,
          120559955619718222459754870179046372169135144963881629853251/
          510545020611095826914278829110628060208678689067212981605125000,
          0, 0, 0, 0]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_eight]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ triakis_tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, mul_neg,
        neg_mul, neg_neg, sub_neg_eq_add, triakis_tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_eight, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val, zero_mul, zero_smul, mul_one, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_empty,
        Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![1414222893034958061856881519121756171696833146925094746865900019/
          1491454274370391343811915434223195498887819783415795158934798000,
          0, 0, 0,
          33095819230038991888492400568667089679172534651805897163152859/
          639194689015882004490820900381369499523351335749626496686342000,
          0,
          2340939602690264565494132364835381875216690945995606462393/
          447436282311117403143574630266958649666345935024738547680439400,
          0]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_eight]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ triakis_tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, mul_neg,
        neg_mul, neg_neg, sub_neg_eq_add, triakis_tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_eight, Matrix.head_cons,
        Matrix.tail_cons, zero_mul, zero_smul, Matrix.cons_val, mul_one, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_empty,
        Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![74504622586102151151257093242532171524075492766057618256100001/
          78497593387915333884837654432799763099358935969252376786042000,
          0, 0, 0,
          138148166284005000918550599332158087652311301995790304503/
          26165864462638444628279218144266587699786311989750792262014000,
          0,
          36295966884675733805252777622450864554731693357170646900259/
          713614485344684853498524131207270573630535781538657970782200,
          0]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_eight]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ triakis_tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, mul_neg,
        neg_mul, neg_neg, sub_neg_eq_add, triakis_tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_eight, Matrix.head_cons,
        Matrix.tail_cons, zero_mul, zero_smul, Matrix.cons_val, mul_one, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_empty,
        Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![692851012939439664241609695880284494239256373468215080981/
          1492947221591983327139054488711907406294113897313108267202000,
          0, 0, 0,
          212964922683063932443797912372025709779587678884601965721050953/
          213064896338627334830273633460456499841117111916542165562114000,
          0,
          765742701731648075267953283112622096101410648665202154131/
          149145427437039134381191543422319549888781978341579515893479800,
          0]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_eight]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ triakis_tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, mul_neg,
        neg_mul, neg_neg, sub_neg_eq_add, triakis_tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_eight, Matrix.head_cons,
        Matrix.tail_cons, zero_mul, zero_smul, Matrix.cons_val, mul_one, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, neg_smul, one_smul,
        Matrix.mulVec_empty, Pi.add_apply, Pi.neg_apply, Function.comp_apply, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![42867784755506172728311986707219449917104854139463070618268243/
          216594857228949744751512230531781601300651565058817628559750000,
          139633895079558328180489994349276834694331845207009812821473927/
          340363347074063884609519219407085373472452459378141987736750000,
          0,
          466780265825485497495886360812622911179345451831915723802990919/
          1191271714759223596133317267924798807153583607823496957078625000,
          0, 0, 0, 0]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_eight]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ triakis_tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, mul_neg,
        neg_mul, neg_neg, sub_neg_eq_add, triakis_tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_eight, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val, zero_mul, zero_smul, mul_one, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, one_smul, neg_smul,
        Matrix.mulVec_empty, Pi.add_apply, Function.comp_apply, Pi.neg_apply, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![24803823425809017789896379120112785875580692232004935621102667/
          125397022606234062750875501886820927068798274507736521797750000,
          49134755637135819739085671233018500754292244201635194197385131/
          125397022606234062750875501886820927068798274507736521797750000,
          0,
          8576407257214870870315575255614940073154223012349398663210367/
          20899503767705677125145916981136821178133045751289420299625000,
          0, 0, 0, 0]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_eight]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ triakis_tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, mul_neg,
        neg_mul, neg_neg, sub_neg_eq_add, triakis_tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_eight, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val, zero_mul, zero_smul, mul_one, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, one_smul, neg_smul,
        Matrix.mulVec_empty, Pi.add_apply, Function.comp_apply, Pi.neg_apply, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![76842713830779121566728454953906367472732687454971873988891/
          165717141596710149312435048247021722098646642601755017659422000,
          0, 0, 0,
          832205023164634805250273294951855475077085579306671928519/
          165717141596710149312435048247021722098646642601755017659422000,
          0,
          788759365132648597886014616756061256550946822993908281492879/
          789129245698619758630643086890579629041174488579785798378200,
          0]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (triakis_tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_eight]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ triakis_tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, mul_neg,
        neg_mul, neg_neg, sub_neg_eq_add, triakis_tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_eight, Matrix.head_cons,
        Matrix.tail_cons, zero_mul, zero_smul, Matrix.cons_val, mul_one, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, neg_smul, one_smul,
        Matrix.mulVec_empty, Pi.add_apply, Pi.neg_apply, Function.comp_apply, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
