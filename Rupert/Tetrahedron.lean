import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion
import Rupert.RelatingRupertDefs

namespace Tetrahedron

open scoped Matrix

def tetrahedron : Fin 4 → ℝ³ := ![
  ![ 1,  1,  1],
  ![ 1, -1, -1],
  ![-1,  1, -1],
  ![-1, -1,  1]]

def outer_quat : Quaternion ℝ :=
  ⟨0.3389904789675945, -0.4261829733457893, 0.1736023394555525, -0.8205581978964213⟩

noncomputable def outer_rot := matrix_of_quat outer_quat

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
  have h : outer_quat.normSq ≠ 0 := by norm_num [outer_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

def inner_quat : Quaternion ℝ :=
  ⟨0.8577016212029301, -0.1191615236085398, 0.4439711748359327, 0.2302999265999848⟩

noncomputable def inner_rot := matrix_of_quat inner_quat

lemma inner_rot_so3 : inner_rot ∈ SO3 := by
  have h : inner_quat.normSq ≠ 0 := by norm_num [inner_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

def inner_offset : ℝ² := ![0.09841265604345877,-0.165800542996898]

set_option maxHeartbeats 10000000 in
theorem rupert : IsRupertPoly tetrahedron := by
  rw [rupert_iff_rupert']
  use outer_rot, outer_rot_so3, inner_rot, inner_rot_so3, inner_offset
  intro outer_shadow inner_shadow
  let ε₀ : ℝ := 0.001
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  have hb : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
    refine Convex.ball_in_hull_of_corners_in_hull hε₀ ?_ ?_ ?_ ?_ <;>
      apply mem_convexHull_iff_exists_fintype.mpr <;>
      use Fin 4, inferInstance
    · use ![3617692820440792570723946381530661/10825143580288773493049423263931750,
            28853668423492178798094341203953803/86601148642310187944395386111454000,
            0,
            28805937655291668580509473855254909/86601148642310187944395386111454000]
      use fun i ↦ (dropz (outer_rot *ᵥ (tetrahedron i)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_four]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, dropz, outer_rot, matrix_of_quat,
          outer_quat, even_two, Even.neg_pow, neg_mul, sub_neg_eq_add, mul_neg, neg_neg, tetrahedron,
          Fin.isValue, Matrix.cons_mulVec, Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero,
          Matrix.empty_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_cons,
          smul_eq_mul, Matrix.smul_empty, Fin.sum_univ_four, Matrix.head_cons, mul_one,
          Matrix.tail_cons, Matrix.add_cons, Matrix.empty_add_empty, Matrix.cons_val, zero_mul]
        norm_num
    · use ![14453062835504034374561893618111559/43300574321155093972197693055727000,
            28924377969556131455075376623438997/86601148642310187944395386111454000,
            0,
            5754129000349197548039244450358377/17320229728462037588879077222290800]
      use fun i ↦ (dropz (outer_rot *ᵥ (tetrahedron i)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_four]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, dropz, outer_rot, matrix_of_quat,
          outer_quat, even_two, Even.neg_pow, neg_mul, sub_neg_eq_add, mul_neg, neg_neg, tetrahedron,
          Fin.isValue, Matrix.cons_mulVec, Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero,
          Matrix.empty_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_cons,
          smul_eq_mul, Matrix.smul_empty, Fin.sum_univ_four, Matrix.head_cons, mul_one,
          Matrix.tail_cons, Matrix.add_cons, Matrix.empty_add_empty, Matrix.cons_val, zero_mul]
        norm_num
    · use ![3620915846390810535401128268562339/10825143580288773493049423263931750,
            28924450122247859295397377743840197/86601148642310187944395386111454000,
            0,
           28709371748935844365788982219115091/86601148642310187944395386111454000]
      use fun i ↦ (dropz (outer_rot *ᵥ (tetrahedron i)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_four]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, dropz, outer_rot, matrix_of_quat,
          outer_quat, even_two, Even.neg_pow, neg_mul, sub_neg_eq_add, mul_neg, neg_neg, tetrahedron,
          Fin.isValue, Matrix.cons_mulVec, Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero,
          Matrix.empty_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_cons,
          smul_eq_mul, Matrix.smul_empty, Fin.sum_univ_four, Matrix.head_cons, mul_one,
          Matrix.tail_cons, Matrix.add_cons, Matrix.empty_add_empty, Matrix.cons_val, zero_mul]
        norm_num
    · use ![14501371831822378049938404982260441/43300574321155093972197693055727000,
            28853740576183906638416342324355003/86601148642310187944395386111454000,
            0,
            5748932880496305041220446764515623/17320229728462037588879077222290800]
      use fun i ↦ (dropz (outer_rot *ᵥ (tetrahedron i)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_four]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, dropz, outer_rot, matrix_of_quat,
          outer_quat, even_two, Even.neg_pow, neg_mul, sub_neg_eq_add, mul_neg, neg_neg, tetrahedron,
          Fin.isValue, Matrix.cons_mulVec, Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero,
          Matrix.empty_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_cons,
          smul_eq_mul, Matrix.smul_empty, Fin.sum_univ_four, Matrix.head_cons, mul_one,
          Matrix.tail_cons, Matrix.add_cons, Matrix.empty_add_empty, Matrix.cons_val, zero_mul]
        norm_num
  intro v hv
  let ε₁ : ℝ := 0.00001
  have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
  refine Convex.mem_interior_hull hε₀.1 hε₁ hb ?_
  simp only [Set.mem_range, inner_shadow] at hv
  obtain ⟨y, hy⟩ := hv
  rw [mem_convexHull_iff_exists_fintype]
  fin_cases y <;>
    simp only [tetrahedron, Fin.reduceFinMk, Matrix.cons_val, inner_shadow] at hy <;>
    use Fin 4, inferInstance
  · use ![24419762003513985479446993192034104101803115609735060626411685853698932075803/
          5094134272401397362124160033006247763499653762616164782597202714604400000000000,
          230409983468138546843093944744735640055655643438309323417206877017616228497521/
          48111268128235419531172622533947895544163396646930445168973581193486000000000000,
          0,
          26803252720787927505825797680094096268019775262787608903547648471915690294817441/
          27062588322132423486284600175345691243591910613898375407547639421335875000000000]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, neg_mul,
        sub_neg_eq_add, mul_neg, neg_neg, tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_four, Matrix.head_cons,
        mul_one, Matrix.tail_cons, Matrix.cons_val, zero_mul, zero_smul, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, one_smul,
        Matrix.mulVec_empty, Pi.add_apply, Function.comp_apply, ε₁, inner_shadow, outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![4183611374521617762351928650236500798224660804096493226244818085853698932075803/
          5094134272401397362124160033006247763499653762616164782597202714604400000000000,
          25102339214950593199584615702794485893116570304996511060364674831052848685492563/
          144333804384706258593517867601843686632490189940791335506920743580458000000000000,
          0,
          130464292183092898867863776690314648064043159948909319303666809415690294817441/
          27062588322132423486284600175345691243591910613898375407547639421335875000000000]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, neg_mul,
        sub_neg_eq_add, mul_neg, neg_neg, tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_four, Matrix.head_cons,
        mul_one, Matrix.tail_cons, Matrix.cons_val, zero_mul, zero_smul, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, one_smul, neg_smul,
        Matrix.mulVec_empty, Pi.add_apply, Function.comp_apply, Pi.neg_apply, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![8149233408515772505369007668071732737002684771295565308694441951232977358601/
          1698044757467132454041386677668749254499884587538721594199067571534800000000000,
          142949325340764770430692464525851563328993579567048454817611738831052848685492563/
          144333804384706258593517867601843686632490189940791335506920743580458000000000000,
          0,
          14412379254534322913938279670958875434403795170474117459791191323965588313049/
          3006954258014713720698288908371743471510212290433152823060848824592875000000000]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, neg_mul,
        sub_neg_eq_add, mul_neg, neg_neg, tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_four, Matrix.head_cons,
        mul_one, Matrix.tail_cons, Matrix.cons_val, zero_mul, zero_smul, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, neg_smul, one_smul,
        Matrix.mulVec_empty, Pi.add_apply, Pi.neg_apply, Function.comp_apply, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![85389834878147286665060941385126660155497490856303099963877032772524468001547/
          103961923926559129839268572102168321704074566584003362910146994175600000000000,
          14144294721423687846667989826219510591782196043919743728224535327609156846787/
          2945587844585842012112609542894769114948779386546761949120831501642000000000000,
          0,
          96012167809420975391727790091867668740856553045172694953017069579912046833009/
          552297720859845377271114289292769209052896134977517865460155906557875000000000]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four]; simp; norm_num
    · exact fun i ↦ ⟨dropz (outer_rot *ᵥ tetrahedron i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [dropz, outer_rot, matrix_of_quat, outer_quat, even_two, Even.neg_pow, neg_mul,
        sub_neg_eq_add, mul_neg, neg_neg, tetrahedron, Fin.isValue, Matrix.cons_mulVec,
        Matrix.cons_dotProduct, Matrix.dotProduct_empty, add_zero, Matrix.empty_mulVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, Fin.sum_univ_four, Matrix.head_cons,
        mul_one, Matrix.tail_cons, Matrix.cons_val, zero_mul, zero_smul, inner_offset, inner_rot,
        inner_quat, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, neg_smul, one_smul,
        Matrix.mulVec_empty, Pi.add_apply, Pi.neg_apply, Function.comp_apply, ε₁, inner_shadow,
        outer_shadow]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add,Matrix.vec2_add, Matrix.vec2_add]
      norm_num
