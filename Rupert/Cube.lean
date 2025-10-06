
import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion
import Rupert.MatrixSimps
import Rupert.Equivalences.RupertEquivRupertPrime

namespace Cube
open Matrix

def cube : Fin 8 → ℝ³ := ![
  ![ 1,  1,  1],
  ![ 1, -1,  1],
  ![-1, -1,  1],
  ![-1,  1,  1],
  ![ 1,  1, -1],
  ![ 1, -1, -1],
  ![-1, -1, -1],
  ![-1,  1, -1]]

noncomputable
abbrev outer_rot_denorm : Matrix (Fin 3) (Fin 3) ℝ :=
   !![ 0,  -√3, √3;
       2,   -1, -1;
      √2,   √2, √2]

noncomputable
abbrev outer_rot : Matrix (Fin 3) (Fin 3) ℝ :=
   (1/√6) • outer_rot_denorm

private
lemma outer_rot_o3_lemma1 : (star outer_rot_denorm) * outer_rot_denorm = 6 • 1 := by
  (ext i j; fin_cases i, j) <;>
  · simp only [mul_apply, of_apply, cons_val', star_apply, Fin.sum_univ_three, cons_val]
    norm_num

private
lemma outer_rot_o3_lemma2 : (outer_rot_denorm) * (star outer_rot_denorm) = 6 • 1 := by
  (ext i j; fin_cases i, j) <;>
  · simp only [mul_apply, of_apply, cons_val', star_apply, Fin.sum_univ_three, cons_val]
    try norm_num
    try ring_nf

lemma two_three_six : √3 * √2 = √6 := by calc √3 * √2
     _ = √(3 * 2) := (Real.sqrt_mul' 3 zero_le_two).symm
     _ = √6 := by norm_num

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
 have h : (6 : ℝ) • 1 = (6 : Matrix (Fin 3) (Fin 3) ℝ) :=
   Matrix.smul_one_eq_diagonal 6
 have h2: (√6)⁻¹ * (√6)⁻¹ * 6 = 1 := by
   rw [←mul_inv]; simp
 let r := (√6)⁻¹
 have hr : (√6)⁻¹ = r := rfl
 dsimp only [outer_rot]
 rw [Matrix.mem_specialOrthogonalGroup_iff]
 constructor
 · constructor
   · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, outer_rot_o3_lemma1, smul_smul]
     simp only [one_div, star_trivial, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
     rw [← h, smul_smul, h2, one_smul]
   · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, outer_rot_o3_lemma2, smul_smul]
     simp only [one_div, star_trivial, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
     rw [← h, smul_smul, h2, one_smul]
 · have : (Fin.succAbove 2 1 : Fin 3) = 1 := by rfl
   simp_all only [one_div, Matrix.smul_of, mul_zero,
     Matrix.det_succ_row_zero,
     Matrix.of_apply,
     Matrix.submatrix_apply, Fin.succ_zero_eq_one,
     Matrix.det_unique, Fin.default_eq_zero, Fin.succ_one_eq_two,
     Fin.sum_univ_two, Fin.val_zero, Fin.zero_succAbove,
     Fin.val_one, ne_eq, one_ne_zero, not_false_eq_true,
     Fin.succAbove_ne_zero_zero, Fin.sum_univ_three, Fin.one_succAbove_one,
     Fin.val_two, Fin.reduceEq, matrix_simps]
   ring_nf
   suffices h : (r * r * 6) * (√3 * √2) * r = 1 by (ring_nf at h; exact h)
   simp only [h2]
   rw [two_three_six]
   change 1 * √6 * (√6)⁻¹ = 1
   field_simp

def outer_shadow : Set ℝ² :=  {x | ∃ i, proj_xy (outer_rot *ᵥ cube i) = x}

def outer_shadow_denorm : Set ℝ² :=  {x | ∃ i, proj_xy (outer_rot_denorm *ᵥ cube i) = x}

noncomputable
def outer_shadow_points_denorm : Fin 8 → ℝ² := ![
  ![  0,       0 ],
  ![ √3 * 2,   2 ],
  ![ √3 * 2,  -2 ],
  ![  0,      -4 ],
  ![-√3 * 2,   2 ],
  ![  0,       4 ],
  ![  0,       0 ],
  ![-√3 * 2,  -2 ]]

lemma outer_shadow_points_in_shadow : ∀ (i : Fin 8), (1/√6) • (outer_shadow_points_denorm i) ∈ outer_shadow := by
  intro i
  have xfer (x : ℝ²) : x ∈ outer_shadow_denorm → (1/√6) • x ∈ outer_shadow := by
    simp only [outer_shadow, outer_rot, outer_shadow_denorm]
    intro ⟨w, hw⟩
    use w
    rw [← hw]
    change _ = _ • proj_xy_linear _
    simp only [ ← proj_xy_linear.map_smul, smul_mulVec]
    rfl
  apply xfer
  let j := i
  fin_cases i <;>
  · simp only [outer_shadow_denorm, cons_mulVec, cons_dotProduct, zero_mul, neg_mul, dotProduct_of_isEmpty,
    add_zero, zero_add, one_mul, empty_mulVec, outer_shadow_points_denorm, Fin.zero_eta,
    Fin.isValue, cons_val_zero, Set.mem_setOf_eq];
    use j;
    simp only [Fin.reduceFinMk, cons_val, cube, head_cons, j, proj_xy, tail_cons];
    ring_nf

---------------------------------------------------------------------------------
-- ++

noncomputable
def rpp := ((3:ℝ)/4) • (1/√6) • outer_shadow_points_denorm 1 +
           ((1:ℝ)/4) • (1/√6) • outer_shadow_points_denorm 5

theorem rpp_in_shadow : rpp ∈ convexHull ℝ outer_shadow := by
 rw [mem_convexHull_iff_exists_fintype]
 let coeffs : Fin 2 → ℝ := ![3/4, 1/4]
 let points := ![(1/√6) • outer_shadow_points_denorm 1, (1/√6) • outer_shadow_points_denorm 5]
 use Fin 2, inferInstance
 use coeffs, points
 refine ⟨?_, ?_, ?_, ?_⟩
 · intro i; fin_cases i <;>
   · simp only [Fin.mk_one, Fin.zero_eta, cons_val_one, cons_val_zero, coeffs]
     positivity
 · simp only [ Fin.sum_univ_two, cons_val_zero, cons_val_one, coeffs]; norm_num
 · intro i; fin_cases i <;> apply outer_shadow_points_in_shadow
 · simp only [Fin.sum_univ_two]
   rfl

theorem rpp_contains_cube : 1 < rpp 0 ∧ 1 < rpp 1 := by
 dsimp only [rpp, outer_shadow_points_denorm, Matrix.cons_val,
     PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
 constructor <;>
 · apply lt_of_mul_self_lt_mul_self₀ (by positivity)
   ring_nf
   norm_num

theorem rpp_contains_cube2 :-1 < rpp 0 ∧ -1 < rpp 1 := by
 dsimp only [rpp, outer_shadow_points_denorm, Matrix.cons_val,
     PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
 constructor
 · have : 0 < 3 / 4 * (1 / √6 * (√3 * 2)) + 1 / 4 * (1 / √6 * 0) + 1 := by positivity
   linarith
 · have : 0 < 3 / 4 * (1 / √6 * 2) + 1 / 4 * (1 / √6 * 4) + 1 := by positivity
   linarith


---------------------------------------------------------------------------------
-- +-

noncomputable
def rpn := ((3:ℝ)/4) • (1/√6) • outer_shadow_points_denorm 2 +
           ((1:ℝ)/4) • (1/√6) • outer_shadow_points_denorm 3

theorem rpn_in_shadow : rpn ∈ convexHull ℝ outer_shadow := by
 rw [mem_convexHull_iff_exists_fintype]
 let coeffs : Fin 2 → ℝ := ![3/4, 1/4]
 let points := ![(1/√6) • outer_shadow_points_denorm 2, (1/√6) • outer_shadow_points_denorm 3]
 use Fin 2, inferInstance
 use coeffs, points
 refine ⟨?_, ?_, ?_, ?_⟩
 · intro i; fin_cases i <;>
   · simp only [Fin.mk_one, Fin.zero_eta, cons_val_one, cons_val_zero, coeffs]
     positivity
 · simp only [ Fin.sum_univ_two, cons_val_zero, cons_val_one, coeffs]; norm_num
 · intro i; fin_cases i <;> apply outer_shadow_points_in_shadow
 · simp only [Fin.sum_univ_two]
   rfl

---------------------------------------------------------------------------------
-- -+

noncomputable
def rnp := ((3:ℝ)/4) • (1/√6) • outer_shadow_points_denorm 4 +
           ((1:ℝ)/4) • (1/√6) • outer_shadow_points_denorm 5

theorem rnp_in_shadow : rnp ∈ convexHull ℝ outer_shadow := by
 rw [mem_convexHull_iff_exists_fintype]
 let coeffs : Fin 2 → ℝ := ![3/4, 1/4]
 let points := ![(1/√6) • outer_shadow_points_denorm 4, (1/√6) • outer_shadow_points_denorm 5]
 use Fin 2, inferInstance
 use coeffs, points
 refine ⟨?_, ?_, ?_, ?_⟩
 · intro i; fin_cases i <;>
   · simp only [Fin.mk_one, Fin.zero_eta, cons_val_one, cons_val_zero, coeffs]
     positivity
 · simp only [ Fin.sum_univ_two, cons_val_zero, cons_val_one, coeffs]; norm_num
 · intro i; fin_cases i <;> apply outer_shadow_points_in_shadow
 · simp only [Fin.sum_univ_two]
   rfl

---------------------------------------------------------------------------------
-- --

noncomputable
def rnn := ((3:ℝ)/4) • (1/√6) • outer_shadow_points_denorm 7 +
           ((1:ℝ)/4) • (1/√6) • outer_shadow_points_denorm 3

theorem rnn_in_shadow : rnn ∈ convexHull ℝ outer_shadow := by
 rw [mem_convexHull_iff_exists_fintype]
 let coeffs : Fin 2 → ℝ := ![3/4, 1/4]
 let points := ![(1/√6) • outer_shadow_points_denorm 7, (1/√6) • outer_shadow_points_denorm 3]
 use Fin 2, inferInstance
 use coeffs, points
 refine ⟨?_, ?_, ?_, ?_⟩
 · intro i; fin_cases i <;>
   · simp only [Fin.mk_one, Fin.zero_eta, cons_val_one, cons_val_zero, coeffs]
     positivity
 · simp only [ Fin.sum_univ_two, cons_val_zero, cons_val_one, coeffs]; norm_num
 · intro i; fin_cases i <;> apply outer_shadow_points_in_shadow
 · simp only [Fin.sum_univ_two]
   rfl

theorem rnn_contains_cube : -1 > rnn 0 ∧ -1 > rnn 1 := by
 dsimp only [rnn, outer_shadow_points_denorm, Matrix.cons_val,
     PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
 constructor <;>
 · apply neg_lt_neg_iff.mp
   simp only [neg_neg, neg_mul, mul_neg, mul_zero, add_zero, neg_add_rev]
   apply lt_of_mul_self_lt_mul_self₀ (by positivity)
   ring_nf
   norm_num

theorem rnn_contains_cube2 : rnn 0 < 1 ∧ rnn 1 < 1 := by
 dsimp only [rnn, outer_shadow_points_denorm, Matrix.cons_val,
     PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
 constructor
 · have : 0 < 3 / 4 * (1 / √6 * (√3 * 2)) + 1 / 4 * (1 / √6 * 0) + 1 := by positivity
   linarith
 · have : 0 < 3 / 4 * (1 / √6 * 2) + 1 / 4 * (1 / √6 * 4) + 1 := by positivity
   linarith

---------------------------------------------------------------------------------

@[simp]
def extract (v : ℝ²) : ℝ × ℝ := ⟨v 0, v 1⟩
@[simp]
def inject (v : ℝ × ℝ) : ℝ² := ![v.1, v.2]

def open_rectangle (xmin xmax ymin ymax : ℝ) : Set ℝ² := inject '' (Set.prod (Set.Ioo xmin xmax) (Set.Ioo ymin ymax))
def closed_rectangle (xmin xmax ymin ymax : ℝ) : Set ℝ² := inject '' (Set.prod (Set.Icc xmin xmax) (Set.Icc ymin ymax))
def rect_vertices (xmin xmax ymin ymax : ℝ) : Fin 4 → ℝ² := ![![xmin,ymin], ![xmax,ymin], ![xmin,ymax], ![xmax,ymax]]

def closed_rectangle_is_convex_hull (xmin xmax ymin ymax : ℝ) (xlt : xmin < xmax) (ylt : ymin < ymax) :
    closed_rectangle xmin xmax ymin ymax
    = convexHull ℝ (Set.range (rect_vertices xmin xmax ymin ymax)) := by
  let prodset : Set (ℝ × ℝ) := {xmin, xmax} ×ˢ {ymin, ymax}
  have lemma1 (S : Set (ℝ × ℝ)):  inject '' (convexHull ℝ S) = convexHull ℝ (inject '' S)  :=
     IsLinearMap.image_convexHull (LinearEquiv.finTwoArrow ℝ ℝ).symm.isLinear S
  have lemma2 : Set.range (rect_vertices xmin xmax ymin ymax) = inject '' prodset := by
    ext p; constructor
    · intro ⟨w, e⟩ ;
      rw[← e];
      fin_cases w
      all_goals simp only [Set.mem_image, Prod.exists]
      · use xmin, ymin
        refine ⟨?_, rfl⟩
        exact Set.mk_mem_prod (Set.mem_insert xmin {xmax}) (Set.mem_insert ymin {ymax})
      · use xmax, ymin
        refine ⟨?_, rfl⟩
        exact Set.mk_mem_prod (Set.mem_insert_of_mem xmin rfl) (Set.mem_insert ymin {ymax})
      · use xmin, ymax
        refine ⟨?_, rfl⟩
        exact Set.mk_mem_prod (Set.mem_insert xmin {xmax}) (Set.mem_insert_of_mem ymin rfl)
      · use xmax, ymax
        refine ⟨?_, rfl⟩
        exact Set.mk_mem_prod (Set.mem_insert_of_mem xmin rfl) (Set.mem_insert_of_mem ymin rfl)
    · intro ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hp⟩⟩; rw [← hp]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      match hx, hy with
      | Or.inl hx0, Or.inl hy0 => rw [← hx0, ← hy0]; use 0; rfl
      | Or.inr hx0, Or.inl hy0 => rw [← hx0, ← hy0]; use 1; rfl
      | Or.inl hx0, Or.inr hy0 => rw [← hx0, ← hy0]; use 2; rfl
      | Or.inr hx0, Or.inr hy0 => rw [← hx0, ← hy0]; use 3; rfl
  have xmin_fact : (xmin ⊓ xmax) = xmin := min_eq_left_of_lt xlt
  have xmax_fact : (xmin ⊔ xmax) = xmax := max_eq_right_of_lt xlt
  have ymin_fact : (ymin ⊓ ymax) = ymin := min_eq_left_of_lt ylt
  have ymax_fact : (ymin ⊔ ymax) = ymax := max_eq_right_of_lt ylt
  have intervalx : convexHull ℝ {xmin, xmax} = Set.Icc xmin xmax := by
    rw [convexHull_pair, segment_eq_Icc', xmin_fact, xmax_fact]
  have intervaly : convexHull ℝ {ymin, ymax} = Set.Icc ymin ymax := by
    rw [convexHull_pair, segment_eq_Icc', ymin_fact, ymax_fact]
  rw [lemma2, ← lemma1, convexHull_prod, intervalx, intervaly]
  ext; exact ⟨id, id⟩

lemma vector_ext (v : ℝ²) : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl

def open_rectangle_is_interior (xmin xmax ymin ymax : ℝ) :
    interior (closed_rectangle xmin xmax ymin ymax) = open_rectangle xmin xmax ymin ymax := by
  simp only [closed_rectangle, open_rectangle]
  have transfer_int (X : Set (ℝ × ℝ)) : interior (inject '' X) = inject '' (interior X) := by
   ext p; constructor
   · intro h
     simp only [inject, Set.mem_image, Prod.exists, mem_interior] at h ⊢
     let ⟨U,⟨U_fits,⟨U_open,p_in_U⟩⟩⟩ := h
     use p 0, p 1
     refine ⟨⟨ extract '' U,  ⟨ ?_, ⟨ ?_, ?_⟩ ⟩⟩ , ?_⟩
     · intro x ⟨hx1, hx2, hx3⟩
       rw [← hx3]
       subst hx3
       have hx1_in_X := U_fits hx2
       simp_all only [Set.exists_subset_image_iff, Set.mem_image, Prod.exists, extract, Fin.isValue]
       obtain ⟨w, ⟨left, ⟨left_1, ⟨w_3, ⟨w_4, ⟨left_3, right⟩⟩⟩⟩⟩⟩ := h
       obtain ⟨w_1, ⟨w_2, ⟨left_2, right_1⟩⟩⟩ := hx1_in_X
       subst right right_1
       simp_all only [Fin.isValue, cons_val_zero, cons_val_one, cons_val_fin_one]
     · exact Homeomorph.finTwoArrow.isOpen_image.mpr U_open
     · rw [Set.mem_image]
       use ![p 0, p 1]
       simp_all only [Set.exists_subset_image_iff, Set.mem_image, Prod.exists, Fin.isValue, extract, cons_val_zero,
         cons_val_one, cons_val_fin_one, and_true]
       let ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, right⟩⟩⟩⟩⟩⟩ := h
       subst right
       simp_all only [Fin.isValue, cons_val_zero, cons_val_one, cons_val_fin_one]
     · apply vector_ext
   · intro h
     simp only [inject, Set.mem_image, Prod.exists, mem_interior] at h ⊢
     let ⟨p0,⟨p1 ,⟨ U, ⟨U_fits,U_open,p_in_U⟩ ⟩ , pext ⟩⟩ := h
     refine ⟨?_ , ⟨?_, ⟨?_, ?_⟩⟩ ⟩
     · exact inject '' U
     · intro x hx
       exact Set.image_mono U_fits hx
     · exact Homeomorph.finTwoArrow.symm.isOpen_image.mpr U_open
     · rw [Set.mem_image]
       use (p0, p1);
       subst pext
       simp_all only [inject, and_self]

  rw [transfer_int]
  let xint := Set.Icc xmin xmax
  let yint := Set.Icc ymin ymax

  -- FIXME: I don't know why I can't simply `apply interior_prod_eq` here, instead of have : ... rw [this].
  have : interior (xint.prod yint) = (interior xint) ×ˢ (interior yint) :=
      interior_prod_eq xint yint
  rw [this]
  --

  congr!
  · simp only [interior_Icc, xint]
  · simp only [interior_Icc, yint]

lemma nontrivial_rectangle0 : rnn 0 < rpp 0 := by
  simp only [rnn, rpp, outer_shadow_points_denorm, neg_mul, cons_val, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, mul_neg, mul_zero, add_zero, neg_lt_self_iff]
  positivity

lemma nontrivial_rectangle1 : rnn 1 < rpp 1 := by
  simp only [rnn, rpp, outer_shadow_points_denorm]
  simp only [one_div, neg_mul, Fin.isValue, cons_val, PiLp.add_apply, PiLp.smul_apply, cons_val_one,
    cons_val_fin_one, smul_eq_mul, mul_neg, cons_val_zero, add_neg_lt_iff_lt_add]
  field_simp
  norm_num

def closed_mediant : Set ℝ² := closed_rectangle (rnn 0) (rpp 0) (rnn 1) (rpp 1)
def open_mediant : Set ℝ² := open_rectangle (rnn 0) (rpp 0) (rnn 1) (rpp 1)

lemma rect_fact1 : ![rpp 0, rnn 1] = rpn := by
  have coord0 : rpp 0 = rpn 0 := by
    simp only [Fin.isValue, rpp, one_div, outer_shadow_points_denorm, neg_mul, cons_val_one,
      cons_val_zero, cons_val, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_zero, add_zero,
      rpn]
  have coord1 : rnn 1 = rpn 1 := by
    simp only [Fin.isValue, rnn, one_div, outer_shadow_points_denorm, neg_mul, cons_val,
      PiLp.add_apply, PiLp.smul_apply, cons_val_one, cons_val_fin_one, smul_eq_mul, mul_neg, rpn]
  rw [← vector_ext rpn, coord0, coord1]

lemma rect_fact2 : ![rnn 0, rpp 1] = rnp := by
  have coord0 : rnn 0 = rnp 0 := by
    simp only [Fin.isValue, rnn, one_div, outer_shadow_points_denorm, neg_mul, cons_val,
      PiLp.add_apply, PiLp.smul_apply, cons_val_zero, smul_eq_mul, mul_neg, mul_zero, add_zero, rnp]
  have coord1 : rpp 1 = rnp 1 := by
    simp only [Fin.isValue, rpp, one_div, outer_shadow_points_denorm, neg_mul, cons_val,
      PiLp.add_apply, PiLp.smul_apply, cons_val_one, cons_val_fin_one, smul_eq_mul, rnp]
  rw [← vector_ext rnp, coord0, coord1]

lemma mediant_sub_hull_outer : Set.range (rect_vertices (rnn 0) (rpp 0) (rnn 1) (rpp 1)) ⊆ convexHull ℝ outer_shadow := by
  intro x ⟨i, hx⟩
  fin_cases i <;>
  · rw [← hx]
    simp only [rect_vertices, vector_ext, rect_fact1, rect_fact2, Fin.isValue]
    try apply rnn_in_shadow
    try apply rpn_in_shadow
    try apply rnp_in_shadow
    try apply rpp_in_shadow

lemma mediant_sub_outer : closed_mediant ⊆ convexHull ℝ outer_shadow := by
  have : Convex ℝ (convexHull ℝ outer_shadow) := by apply convex_convexHull
  rw [closed_mediant, closed_rectangle_is_convex_hull _ _ _ _ nontrivial_rectangle0 nontrivial_rectangle1]
  apply (Convex.convexHull_subset_iff this).mpr
  exact mediant_sub_hull_outer


theorem rupert : IsRupert cube := by
  rw [rupert_iff_rupert']
  use 1, Submonoid.one_mem SO3, 0, outer_rot, outer_rot_so3
  intro inner_shadow outshad x hx
  let ⟨w, p⟩ := hx
  simp only [Matrix.one_mulVec, zero_add] at p
  fin_cases w
  · apply (show interior closed_mediant ⊆ interior (convexHull ℝ outer_shadow) by
                 apply interior_mono; exact mediant_sub_outer)
    rw [closed_mediant, open_rectangle_is_interior]
    use extract x
    simp only [Set.prod, Set.mem_Ioo, Set.mem_setOf_eq, proj_xy, cube, ← p]
    simp only [Fin.isValue, extract, Fin.zero_eta, cons_val_zero, cons_val_one, cons_val_fin_one,
      inject, and_true]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩
    · exact rnn_contains_cube2.1
    · exact rpp_contains_cube.1
    · exact rnn_contains_cube2.2
    · exact rpp_contains_cube.2

  · apply (show interior closed_mediant ⊆ interior (convexHull ℝ outer_shadow) by
                 apply interior_mono; exact mediant_sub_outer)
    rw [closed_mediant, open_rectangle_is_interior]
    use extract x
    simp only [Set.prod, Set.mem_Ioo, Set.mem_setOf_eq, proj_xy, cube, ← p]
    simp only [Fin.isValue, extract, Fin.mk_one, cons_val_one, cons_val_zero, cons_val_fin_one,
      inject, and_true]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩
    · exact rnn_contains_cube2.1
    · exact rpp_contains_cube.1
    · exact rnn_contains_cube.2
    · exact rpp_contains_cube2.2
  · apply (show interior closed_mediant ⊆ interior (convexHull ℝ outer_shadow) by
                 apply interior_mono; exact mediant_sub_outer)
    rw [closed_mediant, open_rectangle_is_interior]
    use extract x
    simp only [Set.prod, Set.mem_Ioo, Set.mem_setOf_eq, proj_xy, cube, ← p]
    simp only [Fin.isValue, extract, Fin.reduceFinMk, cons_val, cons_val_zero, cons_val_one,
      cons_val_fin_one, inject, and_true]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩
    · exact rnn_contains_cube.1
    · exact rpp_contains_cube2.1
    · exact rnn_contains_cube.2
    · exact rpp_contains_cube2.2
  · apply (show interior closed_mediant ⊆ interior (convexHull ℝ outer_shadow) by
                 apply interior_mono; exact mediant_sub_outer)
    rw [closed_mediant, open_rectangle_is_interior]
    use extract x
    simp only [Set.prod, Set.mem_Ioo, Set.mem_setOf_eq, proj_xy, cube, ← p]
    simp only [Fin.isValue, extract, Fin.reduceFinMk, cons_val, cons_val_zero, cons_val_one,
      cons_val_fin_one, inject, and_true]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩
    · exact rnn_contains_cube.1
    · exact rpp_contains_cube2.1
    · exact rnn_contains_cube2.2
    · exact rpp_contains_cube.2

  · apply (show interior closed_mediant ⊆ interior (convexHull ℝ outer_shadow) by
                 apply interior_mono; exact mediant_sub_outer)
    rw [closed_mediant, open_rectangle_is_interior]
    use extract x
    simp only [Set.prod, Set.mem_Ioo, Set.mem_setOf_eq, proj_xy, cube, ← p]
    simp only [Fin.isValue, extract, cons_val_zero, cons_val_one, cons_val_fin_one,
      inject, and_true]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩
    · exact rnn_contains_cube2.1
    · exact rpp_contains_cube.1
    · exact rnn_contains_cube2.2
    · exact rpp_contains_cube.2

-- second half of points, same as the first:
  · apply (show interior closed_mediant ⊆ interior (convexHull ℝ outer_shadow) by
                 apply interior_mono; exact mediant_sub_outer)
    rw [closed_mediant, open_rectangle_is_interior]
    use extract x
    simp only [Set.prod, Set.mem_Ioo, Set.mem_setOf_eq, proj_xy, cube, ← p]
    simp only [Fin.isValue, extract, cons_val_one, cons_val_zero, cons_val_fin_one,
      inject, and_true]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩
    · exact rnn_contains_cube2.1
    · exact rpp_contains_cube.1
    · exact rnn_contains_cube.2
    · exact rpp_contains_cube2.2
  · apply (show interior closed_mediant ⊆ interior (convexHull ℝ outer_shadow) by
                 apply interior_mono; exact mediant_sub_outer)
    rw [closed_mediant, open_rectangle_is_interior]
    use extract x
    simp only [Set.prod, Set.mem_Ioo, Set.mem_setOf_eq, proj_xy, cube, ← p]
    simp only [Fin.isValue, extract, Fin.reduceFinMk, cons_val, cons_val_zero, cons_val_one,
      cons_val_fin_one, inject, and_true]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩
    · exact rnn_contains_cube.1
    · exact rpp_contains_cube2.1
    · exact rnn_contains_cube.2
    · exact rpp_contains_cube2.2
  · apply (show interior closed_mediant ⊆ interior (convexHull ℝ outer_shadow) by
                 apply interior_mono; exact mediant_sub_outer)
    rw [closed_mediant, open_rectangle_is_interior]
    use extract x
    simp only [Set.prod, Set.mem_Ioo, Set.mem_setOf_eq, proj_xy, cube, ← p]
    simp only [Fin.isValue, extract, Fin.reduceFinMk, cons_val, cons_val_zero, cons_val_one,
      cons_val_fin_one, inject, and_true]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩
    · exact rnn_contains_cube.1
    · exact rpp_contains_cube2.1
    · exact rnn_contains_cube2.2
    · exact rpp_contains_cube.2
