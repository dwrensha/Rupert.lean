import Rupert.Basic
import Rupert.Convex
import Rupert.Equivalences.RupertEquivRupertPrime

namespace Square

open Matrix
open Real

/--
A square in the xy-plane, centered at the origin and with side length 2.
-/
abbrev vertices : Fin 4 → ℝ³ := ![ ![-1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, 0] ]

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
     simp [Matrix.mul_apply, Fin.sum_univ_three]
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
     simp [Matrix.mul_apply, Fin.sum_univ_three, rh_lemma]
  · simp [det_succ_row_zero, Fin.sum_univ_three, rh_lemma]

set_option maxHeartbeats 10000000 in
theorem square_is_rupert : IsRupert vertices := by
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
 use inner_rot, inner_rot_so3, inner_offset, outer_rot, outer_rot_so3

 intro inner_shadow outer_shadow x hx

 obtain ⟨ε₀, hε₀0, hε₀⟩ : ∃ ε₀, 0 < ε₀ ∧ ε₀ < √2/2 := by
   use 0.00001
   have h : 1 / 2 < √2 / 2 := by
     suffices H : 1 < √2 by linarith
     exact one_lt_sqrt_two
   constructor
   · norm_num
   · linarith
 have zero_in_outer : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
   intro v hv
   simp only [Metric.mem_ball, dist_zero_right] at hv
   rw [mem_convexHull_iff_exists_fintype]
   use Fin 4, inferInstance
   use ![1/4 + v 0 / (2 * √2), 1/4 - v 0 / (2*√2),
         1/4 + v 1 / (2 * √2), 1/4 - v 1 / (2 * √2)]
   use ![![√2, 0],![-√2, 0], ![0, √2],![0, -√2]]
   obtain ⟨h2', h0'⟩ := abs_le.mp (Real.norm_eq_abs _ ▸ (PiLp.norm_apply_le v 0))
   obtain ⟨h4', h3'⟩ := abs_le.mp (Real.norm_eq_abs _ ▸ (PiLp.norm_apply_le v 1))
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
     · simp [outer_shadow, proj_xy, rh]
       use 3; simp
     · simp [outer_shadow, proj_xy, rh]
       use 0; simp; ring_nf
     · simp [outer_shadow, proj_xy, rh]
       use 2; simp
     · simp [outer_shadow, proj_xy, rh]
       use 1; simp[neg_div']; ring_nf
   · rw [Fin.sum_univ_four]
     ext i
     fin_cases i <;> (simp; grind)

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
       positivity
   · simp only [Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one,
                cons_val_fin_one]
     field_simp; ring
   · intro i
     fin_cases i
     · unfold outer_shadow proj_xy outer_rot rh
       simp only [Fin.isValue, cons_mulVec, cons_dotProduct, zero_mul, dotProduct_of_isEmpty, add_zero,
         neg_mul, one_mul, zero_add, empty_mulVec, cons_val_zero, cons_val_one, neg_sub, Fin.zero_eta, Set.mem_image]
       use ![√2, 0]
       constructor
       · rw [Set.mem_setOf]
         use 3; simp
       · ext i
         fin_cases i <;> simp
     · simp only [proj_xy, mulVec, outer_rot, rh, Fin.isValue, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, cons_dotProduct, zero_mul, dotProduct_of_isEmpty, add_zero,
        cons_val_one, neg_mul, neg_sub, Fin.mk_one, Set.mem_image, outer_shadow]
       use ![-√2, 0]
       constructor
       · rw [Set.mem_setOf]
         use 0
         simp
         ring_nf
       · ext i; fin_cases i
         · simp; ring
         · simp
   · ext i
     fin_cases i
     · simp; field_simp; ring
     · simp
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
       positivity
     · simp [ε₁]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ ((1 - 1e-3) * √2 - 1) from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 by linarith only [H]
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
   · simp; field_simp; ring
   · intro i
     fin_cases i
     · unfold outer_shadow proj_xy outer_rot rh
       simp only [Fin.isValue, cons_mulVec, cons_dotProduct, zero_mul, dotProduct_of_isEmpty, add_zero,
         neg_mul, one_mul, zero_add, empty_mulVec, cons_val_zero, cons_val_one, neg_sub, Fin.zero_eta, Set.mem_image]
       use ![√2, 0]
       constructor
       · use 3; simp
       · ext i
         fin_cases i <;> simp
     · simp only [proj_xy, mulVec, outer_rot, rh, Fin.isValue, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, cons_dotProduct, zero_mul, dotProduct_of_isEmpty, add_zero,
        cons_val_one, neg_mul, neg_sub, Fin.mk_one, Set.mem_image, outer_shadow]
       use ![-√2, 0]
       constructor
       · use 0; simp; ring_nf
       · ext i; fin_cases i
         · norm_num
         · simp
   · ext i
     fin_cases i
     · simp; field_simp; ring
     · simp

 -- we have y ∈ ℝ³ that came from the square, which after being rotated by
 -- inner_rot and projected, is x
 rw [Set.mem_setOf] at hx
 obtain ⟨y, proj_rot_y_eq_x⟩ := hx
 rw [← proj_rot_y_eq_x]; unfold inner_offset; simp;
 fin_cases y
 all_goals (simp [proj_xy])
 · exact negx_in_outer
 · exact posx_in_outer
 · exact negx_in_outer
 · exact posx_in_outer
