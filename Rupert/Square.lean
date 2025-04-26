import Rupert.Basic
import Rupert.Convex
import Rupert.RelatingRupertDefs

namespace Square

open Matrix
open Real

/--
A square in the xy-plane, centered at the origin and with side length 2.
-/
abbrev square : Fin 4 → ℝ³ := ![ ![-1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, 0] ]

/-- square root of one-half -/
noncomputable def rh : ℝ := √2/2

-- A simple algebraic fact about √2/2 that arises multiple times
-- FIXME: is there a systematic naming convention that would give me a less
-- opaque name for this
theorem rh_lemma : rh * rh + rh * rh  = 1 := by
  calc rh * rh + rh * rh
       _ = 2 * (√2 / 2)^2 := by rw[rh]; ring
       _ = 2 * ((√2 * √2) / 2^2) := by rw[div_pow]; ring
       _ = 2 * (2 / 2^2) := by rw[mul_self_sqrt (by norm_num)]
       _ = 1 := by norm_num

abbrev inner_rot : Matrix (Fin 3) (Fin 3) ℝ :=
   !![1, 0, 0;
      0, 0,-1;
      0, 1, 0]

lemma inner_rot_so3 : inner_rot ∈ SO3 := by
  dsimp only [inner_rot]
  rw [mem_specialOrthogonalGroup_iff]
  constructor
  · constructor <;> (ext i j; fin_cases i, j) <;>
     simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul]
  · simp [det_succ_row_zero, Fin.sum_univ_three]

noncomputable abbrev outer_rot : Matrix (Fin 3) (Fin 3) ℝ :=
   !![ rh, rh, 0;
      -rh, rh, 0;
        0,  0, 1]

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
  dsimp only [outer_rot]
  rw [mem_specialOrthogonalGroup_iff]
  constructor
  · constructor <;> (ext i j; fin_cases i, j) <;>
     simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, rh_lemma]
  · simp [det_succ_row_zero, Fin.sum_univ_three, rh_lemma]

lemma fst_abs_le_norm (v : EuclideanSpace ℝ (Fin 2)) : |v 0| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h : ‖v 0‖ ^ 2 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by nlinarith
  have h1 : √(‖v 0‖ ^ 2) ≤ √(‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := sqrt_le_sqrt h
  have h2 : 0 ≤ ‖v 0‖ := norm_nonneg (v 0)
  rw [Real.sqrt_sq h2] at h1
  rw [←norm_eq_abs]
  linarith

lemma snd_abs_le_norm (v : ℝ²) : |v 1| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h : ‖v 1‖ ^ 2 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by nlinarith
  have h1 : √(‖v 1‖ ^ 2) ≤ √(‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := sqrt_le_sqrt h
  have h2 : 0 ≤ ‖v 1‖ := norm_nonneg _
  rw [Real.sqrt_sq h2] at h1
  rw [←norm_eq_abs]
  linarith

set_option maxHeartbeats 10000000 in
theorem square_is_rupert : IsRupertPoly square := by
/-

The diagram shows the (x,y) plane, the z axis runs through the
screen. The rotation inner_rot rotates about the x axis, creating the
horizontal slot shape.  The rotation outer_rot rotates the (x,y) plane
by π/4 radians. No offset translation is needed.

      +
     / \
    /   \
   /     \
  + ----- +
   \     /
    \   /
     \ /
      +
-/
 rw [rupert_iff_rupert']
 let inner_offset : ℝ² := 0
 use outer_rot, outer_rot_so3, inner_rot, inner_rot_so3, inner_offset

 intro outer_shadow inner_shadow x hx

 obtain ⟨ε₀, hε₀0, hε₀⟩ : ∃ ε₀, 0 < ε₀ ∧ ε₀ < √2/2 := by
   use 0.00001
   have h : 1 / 2 < √2 / 2 := by
     suffices H : 1 < √2 by linarith
     suffices H : 1^2 < √2^2 by
       have h2 : 0 ≤ √2 := by positivity
       exact lt_of_pow_lt_pow_left₀ 2 h2 H
     rw [Real.sq_sqrt (by norm_num)]
     norm_num
   constructor
   · norm_num
   · linarith
 have zero_in_outer : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
   intro v hv
   simp only [Metric.mem_ball, dist_zero_right, outer_rot, inner_rot] at hv
   rw [mem_convexHull_iff_exists_fintype]
   use Fin 4, inferInstance
   use ![1/4 + v 0 / (2 * √2), 1/4 - v 0 / (2*√2),
         1/4 + v 1 / (2 * √2), 1/4 - v 1 / (2 * √2)]
   use ![![√2, 0],![-√2, 0], ![0, √2],![0, -√2]]
   obtain ⟨h2', h0'⟩ := abs_le.mp (fst_abs_le_norm v)
   obtain ⟨h4', h3'⟩ := abs_le.mp (snd_abs_le_norm v)
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i
     fin_cases i
     · simp
       suffices H : 0 * (2 * √2) ≤ (4⁻¹ + v 0 / (2 * √2)) * (2 * √2) by
         have : 0 < 2 * √2 := by positivity
         exact le_of_mul_le_mul_right H this
       rw [zero_mul]
       ring_nf
       rw [mul_assoc]
       simp
       linarith
     · simp
       suffices H : v 0 / (2 * √2) * (2 * √2) ≤ 4⁻¹ * (2 * √2) by
         have : 0 < 2 * √2 := by positivity
         exact le_of_mul_le_mul_right H this
       simp
       linarith
     · simp
       suffices H : 0 * (2 * √2) ≤ (4⁻¹ + v 1 / (2 * √2)) * (2 * √2) by
         have : 0 < 2 * √2 := by positivity
         exact le_of_mul_le_mul_right H this
       rw [zero_mul]
       ring_nf
       rw [mul_assoc]
       simp
       linarith
     · simp
       suffices H : v 1 / (2 * √2) * (2 * √2) ≤ 4⁻¹ * (2 * √2) by
         have : 0 < 2 * √2 := by positivity
         exact le_of_mul_le_mul_right H this
       simp
       linarith
   · simp [Fin.sum_univ_four]
     ring
   · intro i
     fin_cases i
     · simp [outer_shadow, dropz, rh]
       use 3; simp
     · simp [outer_shadow, dropz, rh]
       use 0; simp; ring_nf
     · simp [outer_shadow, dropz, rh]
       use 2; simp
     · simp [outer_shadow, dropz, rh]
       use 1; simp[neg_div']; ring_nf
   · rw [Fin.sum_univ_four]
     ext i
     fin_cases i
     · simp; field_simp; ring_nf
     · simp; field_simp; ring_nf

 -- subset_interior_hull
 let ε₁ : ℝ := 0.001
 have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num

 have negx_in_outer : ![-1, 0] ∈ interior (convexHull ℝ outer_shadow) := by
   apply Convex.mem_interior_hull hε₀0 hε₁ zero_in_outer
   rw [mem_convexHull_iff_exists_fintype]
   -- we need to write (-1,0) as a convex combination of
   -- (-(1-ε)√2, 0), ((1-ε)√2, 0)
   use Fin 2, inferInstance
   use ![((1-ε₁)* √2 - 1) / (2 * (1 - ε₁) * √2),
         ((1-ε₁)* √2 + 1) /(2 * (1 - ε₁) * √2)]
   use ![![(1-ε₁) * √2, 0], ![-(1-ε₁) * √2, 0]]
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i; fin_cases i
     · simp [ε₁]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ ((1 - 1e-3) * √2 - 1) from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 by linarith only [H]
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
     · simp [ε₁]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ ((1 - 1e-3) * √2 + 1) from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 by linarith only [H]
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
   · field_simp; ring
   · intro i
     fin_cases i
     · unfold outer_shadow dropz outer_rot rh
       simp only [Fin.isValue, cons_mulVec, cons_dotProduct, zero_mul, dotProduct_empty, add_zero,
         neg_mul, one_mul, zero_add, empty_mulVec, cons_val_zero, cons_val_one, Nat.succ_eq_add_one,
         Nat.reduceAdd, neg_sub, Fin.zero_eta, Set.mem_image, Set.mem_insert_iff,
         Set.mem_singleton_iff, exists_eq_or_imp, head_cons, mul_neg, mul_one, tail_cons,
         add_neg_cancel, neg_add_cancel, exists_eq_left]
       use ![√2, 0]
       constructor
       · rw [Set.mem_range]
         use 3; simp
       · ext i
         fin_cases i <;> simp
     · simp only [dropz, mulVec, outer_rot, rh, Fin.isValue, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, cons_dotProduct, zero_mul, dotProduct_empty, add_zero,
        cons_val_one, neg_mul, Nat.succ_eq_add_one, Nat.reduceAdd, neg_sub, Fin.mk_one,
        Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, head_cons,
        mul_neg, mul_one, tail_cons, neg_neg, add_neg_cancel, neg_add_cancel, add_halves,
        exists_eq_left, outer_shadow]
       use ![-√2, 0]
       constructor
       · rw [Set.mem_range]
         use 0
         simp
         ring_nf
       · ext i; fin_cases i
         · simp; ring
         · simp
   · ext i
     fin_cases i
     · field_simp; ring
     · field_simp
 have posx_in_outer : ![1, 0] ∈ interior (convexHull ℝ outer_shadow) := by
   apply Convex.mem_interior_hull hε₀0 hε₁ zero_in_outer
   rw [mem_convexHull_iff_exists_fintype]
   -- we need to write (1,0) as a convex combination of
   -- (-(1-ε)√2, 0), ((1-ε)√2, 0)
   use Fin 2, inferInstance
   use ![((1-ε₁)* √2 + 1) / (2 * (1 - ε₁) * √2),
         ((1-ε₁)* √2 - 1) /(2 * (1 - ε₁) * √2)]
   use ![![(1-ε₁) * √2, 0], ![-(1-ε₁) * √2, 0]]
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i; fin_cases i
     · simp [ε₁]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ ((1 - 1e-3) * √2 + 1) from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 by linarith only [H]
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
     · simp [ε₁]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ ((1 - 1e-3) * √2 - 1) from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 by linarith only [H]
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
   · field_simp; ring
   · intro i
     fin_cases i
     · unfold outer_shadow dropz outer_rot rh
       simp only [Fin.isValue, cons_mulVec, cons_dotProduct, zero_mul, dotProduct_empty, add_zero,
         neg_mul, one_mul, zero_add, empty_mulVec, cons_val_zero, cons_val_one, Nat.succ_eq_add_one,
         Nat.reduceAdd, neg_sub, Fin.zero_eta, Set.mem_image, Set.mem_insert_iff,
         Set.mem_singleton_iff, exists_eq_or_imp, head_cons, mul_neg, mul_one, tail_cons,
         add_neg_cancel, neg_add_cancel, exists_eq_left]
       use ![√2, 0]
       constructor
       · use 3; simp
       · ext i
         fin_cases i <;> simp
     · simp only [dropz, mulVec, outer_rot, rh, Fin.isValue, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, cons_dotProduct, zero_mul, dotProduct_empty, add_zero,
        cons_val_one, neg_mul, Nat.succ_eq_add_one, Nat.reduceAdd, neg_sub, Fin.mk_one,
        Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, head_cons,
        mul_neg, mul_one, tail_cons, neg_neg, add_neg_cancel, neg_add_cancel, add_halves,
        exists_eq_left, outer_shadow]
       use ![-√2, 0]
       constructor
       · use 0; simp; ring_nf
       · ext i; fin_cases i
         · simp; ring
         · simp
   · ext i
     fin_cases i
     · field_simp; ring
     · field_simp

 -- we have y ∈ ℝ³ that came from the square, which after being rotated by
 -- inner_rot and projected, is x
 rw [Set.mem_range] at hx
 obtain ⟨y, proj_rot_y_eq_x⟩ := hx
 rw [← proj_rot_y_eq_x]; unfold inner_offset; simp;
 fin_cases y
 all_goals (simp[inner_rot, dropz, Matrix.mulVec])
 · exact negx_in_outer
 · exact posx_in_outer
 · exact negx_in_outer
 · exact posx_in_outer
