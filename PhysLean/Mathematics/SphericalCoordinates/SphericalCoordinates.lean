/-
Copyright (c) 2025 Liam O'Connor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liam O'Connor
-/

import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.TODO.Basic
import PhysLean.SpaceAndTime.Space.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.PartialOrder

namespace PhysLean.Mathematics.SphericalCoordinates

structure Spherical where
  r     : Real
  theta : Real
  phi   : Real
  r_bounds     : r ≥ 0
  theta_bounds : 0 ≤ theta ∧ theta ≤ Real.pi
  phi_bounds : -Real.pi < phi ∧ phi ≤ Real.pi
  r_zero_bound  : r = 0 → theta = 0 ∧ phi = 0
  theta_zero_bound : theta = 0 → phi = 0
  theta_pi_bound : theta = Real.pi → phi = 0

namespace Spherical

open EuclideanSpace
open Mathlib
open Real

abbrev Vec3 := Space 3

open Fin

def x (v : Vec3) : ℝ := v.val ⟨0, by decide⟩
def y (v : Vec3) : ℝ := v.val ⟨1, by decide⟩
def z (v : Vec3) : ℝ := v.val ⟨2, by decide⟩

noncomputable def atan2 (y x : ℝ) : ℝ :=
  if y = 0 ∧ x < 0 then
    Real.pi
  else
    2 * Real.arctan (y / (Real.sqrt (x^2 + y^2) + x))

lemma atan2_empty_zero : atan2 0 0 = 0 := by simp [atan2]

theorem atan2_lower_bound (y x : ℝ) : -Real.pi < atan2 y x := by
  unfold atan2
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [h]
    linarith [Real.pi_pos]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    simp [h]
    generalize y / (Real.sqrt (x^2 + y^2) + x) = u
    have h := Real.neg_pi_div_two_lt_arctan u
    linarith

theorem atan2_upper_bound (y x : ℝ) : atan2 y x ≤ Real.pi := by
  unfold atan2
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    simp [h]
    generalize y / (√(x^2 + y^2) + x) = u
    have h := Real.arctan_lt_pi_div_two u
    linarith

theorem atan2_bounds (y x : ℝ) :
  -Real.pi < atan2 y x ∧ atan2 y x ≤ Real.pi := by
  exact ⟨atan2_lower_bound y x, atan2_upper_bound y x⟩

lemma neg_div_sqrt_sq (x : ℝ) (hx : x < 0) : x / Real.sqrt (x^2) = -1 := by
  rw [Real.sqrt_sq_eq_abs x]
  rw [abs_of_neg hx]
  have h : x ≠ 0 := ne_of_lt hx
  field_simp [h]

/--theorem one_sub_u_sq_eq (x y : ℝ) (u : ℝ) (h : u = y / (Real.sqrt (x^2 + y^2) + x)) :
  1 - u^2 = ((Real.sqrt (x^2 + y^2) + x)^2 - y^2) / (Real.sqrt (x^2 + y^2) + x)^2 := by
    rw [h]
    field_simp--/

lemma non_zero_square_positive (y : ℝ) (h_y_nonzero: y ≠ 0) : y^2 > 0 := by
    have ha : y^2 = 0 ↔ y = 0 := by simp
    have hb : y^2 ≥ 0 := by nlinarith
    have hc : y^2 ≠ 0 := by simp [ha, h_y_nonzero]
    have h0 : (y^2 : ℝ) > 0 := sq_pos_of_ne_zero h_y_nonzero
    simp [h0]

theorem sqrt_x2_y2_add_x_ne_zero {x y : ℝ} (h : x^2 + y^2 > 0) (hx : x ≥ 0 ∨ y ≠ 0) :
  Real.sqrt (x^2 + y^2) + x > 0 := by
  cases hx with
  | inl h_x_nonneg =>
    have hpos : Real.sqrt (x^2 + y^2) > 0 := Real.sqrt_pos.mpr h
    have hsum : Real.sqrt (x^2 + y^2) + x > 0 := by linarith
    linarith
  | inr h_y_nonzero =>
    have h_sq_lt_sum : x^2 ≤ x^2 + y^2 := by nlinarith
    have h0 : (y^2 : ℝ) > 0 := by simp [non_zero_square_positive, h_y_nonzero]
    have h1 : (x^2 + y^2) > x^2 := by nlinarith [h0]
    have h2 : |x| ≤ √(x^2 + y^2) := abs_le_sqrt (show x^2 ≤ x^2 + y^2 from h_sq_lt_sum)
    have h3 : |x| ≠ √(x^2 + y^2) := by
      intro h_eq
      rw [← Real.sqrt_sq_eq_abs] at h_eq
      have h_sq := congr_arg (fun z => z^2) h_eq
      simp only at h_sq
      have h_x_sq_pos : x^2 ≥ 0 := by nlinarith
      have h_y_sq_pos : y^2 ≥ 0 := by nlinarith
      have h_sum_sq_pos : x^2 + y^2 ≥ 0 := by nlinarith
      simp [h_x_sq_pos, h_sum_sq_pos] at h_sq
      exact h_y_nonzero h_sq
    have h4 : |x| < √(x^2 + y^2) := by simp [lt_of_le_of_ne , h2, h3]
    have h5 : -x ≤ |x| := by exact neg_le_abs (x : ℝ)
    have h6 : -x < √(x^2 + y^2) := by linarith [h4, h5]
    linarith [h4]

lemma pos_square_sum (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  x^2 + y^2 > 0 := by
    by_cases h_x_non_zero : x ≠ 0
    · have hx1 : x^2 > 0 := by simp [h_x_non_zero, sq_pos_of_ne_zero]
      nlinarith [hx1]
    · have h_x_zero : x = 0 := by simpa using h_x_non_zero
      have h_y_non_zero : y ≠ 0 := by
        cases h_not_both_zero with
        | inl hy => exact hy
        | inr hx => cases hx (by simp [h_x_zero])
      have hy1 : y^2 > 0 := by simp [h_y_non_zero, sq_pos_of_ne_zero]
      nlinarith [hy1]


theorem cos_atan2 (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  Real.cos (atan2 y x) = x / Real.sqrt (x^2 + y^2) := by
  unfold atan2
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [h]
    simp [neg_div_sqrt_sq, h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    generalize h_u : y / (√(x^2 + y^2) + x) = u
    have h_non_neg : 0 ≤  (1 + u^2) := by nlinarith
    have h_pos : 0 < (1 + u^2) := by nlinarith
    have h_one_plus_u_sq_non_zero : 1 + u^2 ≠ 0 := by linarith [h_pos]
    simp [h, Real.cos_two_mul, Real.cos_arctan, h_non_neg, sq_sqrt]
    field_simp
    have h_two_sub : 2 - (1 + u^2) = 1 - u^2 := by linarith;
    simp [h_two_sub]

    have h_nonzero : 1 + u^2 ≠ 0 := by nlinarith;
    have h_pos_sq_sum : x^2 + y^2 > 0 := by simp [pos_square_sum, h_not_both_zero]
    have h_non_neg_sq_sum : x^2 + y^2 ≥ 0 := by linarith [h_pos_sq_sum]
    have h_pos_rt_sq_sum : √(x^2 + y^2) > 0 := by simp [h_pos_sq_sum]
    have h_non_zero_rt_sq_sum : √(x^2 + y^2) ≠ 0 := by linarith [h_pos_rt_sq_sum]
    have h_reverse : x ≥ 0 ∨ y ≠ 0 := by
      by_cases hx : x ≥ 0
      · exact Or.inl hx
      · exact Or.inr (by
          intro hy_eq
          apply h
          constructor
          · exact hy_eq
          · linarith)

    have h_denom_pos : Real.sqrt (x^2 + y^2) + x > 0 := by exact sqrt_x2_y2_add_x_ne_zero h_pos_sq_sum h_reverse
    have h_denom_non_zero : Real.sqrt (x^2 + y^2) + x ≠ 0 := by nlinarith [h_denom_pos]
    have h_collect_terms : 1 - u^2 = (1 + u^2) * x / √(x^2 + y^2) ↔ (1 - u^2) / (1 + u^2) = x / √(x^2 + y^2) := by
      field_simp [h_one_plus_u_sq_non_zero, h_non_zero_rt_sq_sum];
    simp [h_collect_terms]

    have h_one_sub_u_sq : 1 - u^2 = ((√(x^2 + y^2) + x)^2 - y^2) / ((√(x^2 + y^2) + x)^2 ) := by
      simp [← h_u]
      field_simp
    have h_one_plus_u_sq : 1 + u^2 = ((√(x^2 + y^2) + x)^2 + y^2) / ((√(x^2 + y^2) + x)^2 ) := by
      simp [← h_u]
      field_simp
    have h_u_division : (1 - u^2) / (1 + u^2) = ((√(x^2 + y^2) + x)^2 - y^2) / ((√(x^2 + y^2) + x)^2 + y^2) := by
      simp [h_one_sub_u_sq, h_one_plus_u_sq]
      field_simp
    simp [h_u_division]

    have h_bracket_sq_expansion : (√(x^2 + y^2) + x)^2 = 2 * x^2 + y^2 + 2 * x * √(x^2 + y^2) := by
      ring_nf
      field_simp
      simp [sq_sqrt, h_non_neg_sq_sum]
      linarith
    have h_numerator_expansion : ((√(x^2 + y^2) + x)^2 - y^2) = 2 * x * (√(x^2 + y^2) + x) := by
      simp [h_bracket_sq_expansion]
      linarith
    have h_denominator_expansion : ((√(x^2 + y^2) + x)^2 + y^2) = 2 * √(x^2 + y^2) * (√(x^2 + y^2) + x) := by
      simp [h_bracket_sq_expansion]
      linarith
    simp [h_numerator_expansion, h_denominator_expansion]
    field_simp

theorem sin_atan2 (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  Real.sin (atan2 y x) = y / Real.sqrt (x^2 + y^2) := by
  unfold atan2
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    generalize h_u : y / (√(x^2 + y^2) + x) = u
    have h_non_neg : 0 ≤ 1 + u^2 := by nlinarith
    have h_pos : 0 < 1 + u^2 := by nlinarith
    have h_one_plus_u_sq_non_zero : 1 + u^2 ≠ 0 := by linarith [h_pos]

    simp [h, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    field_simp [h_one_plus_u_sq_non_zero]
    simp [sq_sqrt, h_non_neg]
    simp [← h_u]
    field_simp

    have h_reverse : x ≥ 0 ∨ y ≠ 0 := by
      by_cases hx : x ≥ 0
      · exact Or.inl hx
      · exact Or.inr (by
          intro hy_eq
          apply h
          constructor
          · exact hy_eq
          · linarith)

    have h_pos_sq_sum : x^2 + y^2 > 0 := by simp [pos_square_sum, h_not_both_zero]
    have h_non_zero_sq_sum : x^2 + y^2 ≠ 0 := by linarith [h_pos_sq_sum]
    have h_denom_pos : Real.sqrt (x^2 + y^2) + x > 0 := by exact sqrt_x2_y2_add_x_ne_zero h_pos_sq_sum h_reverse
    have h_denom_non_zero : Real.sqrt (x^2 + y^2) + x ≠ 0 := by linarith [h_denom_pos]

    --have h_bracket_sq_expansion : (√(x^2 + y^2) + x)^2 = x^2 + y^2 + 2 * x * √(x^2+y^2) + x^2 := by ring_nf
    --have h_denominator_expansion : (√(x^2 + y^2) + x)^2 + y^2 = 2 * √(x^2+y^2) * (√(x^2+y^2)+x) := by linarith [h_bracket_sq_expansion]
    --have h_numerator_expansion : 2 * y * (√(x^2+y^2)+x) = 2 * y * (√(x^2+y^2)+x) := by rfl

    by_cases h_y_zero : y = 0
    · simp [h_y_zero]
    · field_simp [h_y_zero]

      /-have h_one_plus_u_sq : 1 + (y / (√(x^2 + y^2) + x))^2 = ((√(x^2 + y^2) + x)^2 + y^2) / ((√(x^2 + y^2) + x)^2 ) := by
        have h_join_numerator (a : ℝ) (b : ℝ) (h_b_non_zero : b ≠ 0) : 1 + a / b = (b + a) / b := by
          simp [add_div, h_b_non_zero]
        field_simp [h_join_numerator, h_denom_non_zero]-/
      ring_nf
      have h_sq_sqrt_sum : √(x^2 + y^2) ^ 2 = x^2 + y^2 := Real.sq_sqrt (by nlinarith [h_pos_sq_sum])
      linarith [h_sq_sqrt_sum]


noncomputable def toVec3 (s : Spherical) : Vec3 :=
  ⟨![
    s.r * Real.sin s.theta * Real.cos s.phi,
    s.r * Real.sin s.theta * Real.sin s.phi,
    s.r * Real.cos s.theta
  ]⟩

lemma r_non_neg_spherical (x : ℝ) (y : ℝ) (z : ℝ) : Real.sqrt (x*x + y*y + z*z) ≥ 0 := sqrt_nonneg (x*x + y*y + z*z)

lemma sq_le_then_le_sqrt (a : ℝ) (b : ℝ) (h_a : 0 ≤ a) (h_b : 0 ≤ b) :
  a^2 ≤ b → a ≤ sqrt b := by
  intro h_sq
  exact (le_sqrt h_a h_b).mpr h_sq


theorem theta_zero_implies_phi_zero
  (x : ℝ) (y : ℝ) (z : ℝ) (s : Spherical)
  (h_r_val : s.r = √(x^2 + y^2 + z^2)) (h_r_non_zero : s.r ≠ 0)
  (h_theta_def : s.theta = Real.arccos (z / s.r)) (h_theta_zero : s.theta = 0)
  (h_phi_def : s.phi = atan2 x y) :
  s.theta = 0 → s.phi = 0 := by
    intro h_theta
    simp [h_phi_def]

    -- -1 ≤ z / r ≤ 1
    have h_r_nonneg : 0 ≤ s.r := s.r_bounds
    have r_pos : 0 < s.r := lt_of_le_of_ne h_r_nonneg h_r_non_zero.symm
    have h_abs_z_over_r_bounds : abs (z / s.r) ≤ 1 := by
      simp [abs_div, abs_of_pos, r_pos]
      field_simp
      simp [h_r_val]
      simp [abs_le]
      have h_sq : z^2 ≤ x^2 + y^2 + z^2 := by nlinarith
      constructor
      · have h_sum_non_neg : 0 ≤ x^2 + y^2 + z^2 := by nlinarith
        have h_sqrt : Real.sqrt (z^2) ≤ Real.sqrt (x^2 + y^2 + z^2) := Real.sqrt_le_sqrt h_sq
        simp [neg_le]
        have neg_z_le_sqrt : -z ≤ Real.sqrt (x^2 + y^2 + z^2) := by
          have h_sqrt_nonneg : 0 ≤ Real.sqrt (x^2 + y^2 + z^2) := Real.sqrt_nonneg _
          by_cases hz : z ≥ 0
          · have : -z ≤ 0 := neg_nonpos.mpr hz
            linarith
          · have h_minus_z_non_neg: 0 ≤ -z := by linarith
            have : (-z)^2 = z^2 := by ring
            have : z^2 ≤ x^2 + y^2 + z^2 := by nlinarith
            have h_sum_ge_zero : 0 ≤ x^2 + y^2 + z^2 := by linarith
            have h_case_resolved : -z ≤ sqrt (x^2 + y^2 + z^2) :=
              sq_le_then_le_sqrt (-z : ℝ) (x^2 + y^2 + z^2) h_minus_z_non_neg h_sum_ge_zero (by
                rw [neg_sq]
                exact h_sq)
            simp [h_case_resolved]
        simp [neg_z_le_sqrt]
      · have h_z_below : z ≤ sqrt (x^2 + y^2 + z^2) := by
          have h_sum_ge_zero : 0 ≤ x^2 + y^2 + z^2 := by nlinarith
          have h_z_le_sqrt : z ≤ Real.sqrt (x^2 + y^2 + z^2) := by
            have h_sqrt_nonneg : 0 ≤ Real.sqrt (x^2 + y^2 + z^2) := Real.sqrt_nonneg _
            by_cases h_z : z ≥ 0
            · have h_z2 : 0 ≤ z := by simp [h_z]
              exact sq_le_then_le_sqrt z (x^2 + y^2 + z^2) h_z2 h_sum_ge_zero h_sq
            · have h_minus_z_non_neg: 0 ≤ -z := by linarith
              have : (-z)^2 = z^2 := by ring
              have : z^2 ≤ x^2 + y^2 + z^2 := by nlinarith
              have h_sum_ge_zero : 0 ≤ x^2 + y^2 + z^2 := by linarith
              have h_z_le_sqrt_sum : -z ≤ sqrt (x^2 + y^2 + z^2) :=
                sq_le_then_le_sqrt (-z : ℝ) (x^2 + y^2 + z^2) h_minus_z_non_neg h_sum_ge_zero (by
                  rw [neg_sq]
                  exact h_sq)
              have h_z_le_neg_z : z ≤ -z := by linarith [h_z]
              linarith [h_z_le_sqrt_sum, h_z_le_neg_z]
          simp [h_z_le_sqrt]
        simp [h_z_below]

    have h_lower_bound : -1 ≤ z / s.r := (abs_le.mp h_abs_z_over_r_bounds).1
    have h_upper_bound : z / s.r ≤ 1  := (abs_le.mp h_abs_z_over_r_bounds).2

    have h_z_div_r : z / s.r = 1 := by
      have h_fraction_div_zero : Real.arccos (z / s.r) = 0 → (z / s.r) = 1 := by
        intro h_frac_div
        have h_cos_theta : z / s.r = Real.cos s.theta  := by simp [h_theta_def, Real.cos_arccos, h_lower_bound, h_upper_bound]
        simp [h_cos_theta, h_theta_zero]
      apply h_fraction_div_zero
      simp [← h_theta_zero, h_theta_def]

    have h_z_r : z = s.r := by
      have h_fun := congrArg (fun t => t * s.r) h_z_div_r
      field_simp [h_r_non_zero] at h_fun
      simpa using h_fun

    have h_r_square : s.r^2 = x^2 + y^2 + z^2 := by
      have h_sum_ge_zero : 0 ≤ x^2 + y^2 + z^2 := by nlinarith
      have h_sum_sq : √(x^2 + y^2 + z^2)^2 = x^2 + y^2 + z^2 := by simpa using Real.sq_sqrt h_sum_ge_zero
      simp [h_r_val, h_sum_sq]

    have h_x_y_sq : x^2 + y^2 = 0 := by
      have h_add_z : x^2 + y^2 + z^2 = z^2 → x^2 + y^2 = 0 := by
        intro _
        linarith
      apply h_add_z
      simp [h_r_square.symm]
      have h_r_eq_z_then_r_sq_eq_z_sq : s.r = z → s.r^2 = z^2 := by
        intro _
        nlinarith
      apply h_r_eq_z_then_r_sq_eq_z_sq
      simp [h_z_r]

    have h_x_0 : x = 0 := by nlinarith [h_x_y_sq]
    have h_y_0 : y = 0 := by nlinarith [h_x_y_sq]

    simp [atan2_empty_zero, h_x_0, h_y_0]


noncomputable def Vec3.toSpherical (v : Vec3) : Spherical :=
  let x := x v
  let y := y v
  let z := z v
  let r := Real.sqrt (x*x + y*y + z*z)
  if hr : r = 0 then
    { r := 0,
      theta := 0,
      phi := 0,
      r_bounds := by linarith,
      theta_bounds := ⟨by simp, by linarith [Real.pi_pos]⟩,
      phi_bounds := ⟨by linarith [Real.pi_pos], by apply Real.pi_nonneg⟩,
      r_zero_bound := by simp,
      theta_zero_bound := by simp,
      theta_pi_bound := by simp
    }
  else
    let theta := Real.arccos (z / r)
    let phi   := atan2 y x
    { r := r,
      theta := theta,
      phi := phi,
      r_bounds := by apply Real.sqrt_nonneg,
      theta_bounds := ⟨Real.arccos_nonneg (z / r), Real.arccos_le_pi (z / r)⟩,
      phi_bounds := by simpa using atan2_bounds y x,
      r_zero_bound := by
        intro h0
        exfalso
        exact hr h0,
      theta_zero_bound := by
        intro h_theta

        exact h_phi
      theta_pi_bound := by simp
    }


/- noncomputable def tempInv (s : Spherical) : Vec3 :=
  let r := s.r
  let theta := s.theta
  let phi := s.phi
  let z := r * Real.cos theta
  let y_squared :=
    if (-Real.pi / 2) < phi ∧ phi < (Real.pi / 2) then
      (r*r)*((Real.sin theta)*(Real.sin theta))*((Real.tan phi)*(Real.tan phi)) / ((Real.tan phi)*(Real.tan phi) + 1)
    else if (Real.pi / 2) < phi ∧ phi < (3 * Real.pi / 2) then
      (r*r)*((Real.sin theta)*(Real.sin theta))*(((Real.tan phi) - Real.pi)*((Real.tan phi) - Real.pi)) / (((Real.tan phi) - Real.pi)*((Real.tan phi) - Real.pi) + 1)
    else if (-3 * Real.pi / 2) < phi ∧ phi < (-Real.pi / 2) then
      (r*r)*((Real.sin theta)*(Real.sin theta))*(((Real.tan phi) + Real.pi)*((Real.tan phi) + Real.pi)) / (((Real.tan phi) + Real.pi)*((Real.tan phi) + Real.pi) + 1)
    else if abs phi = Real.pi / 2 then
      r * r * (sin theta) * (sin theta)
    else
      0
  let y :=
    if ((-Real.pi / 2) < phi ∧ phi < (Real.pi / 2) ∧ (Real.tan phi) > 0)
      ∨ (Real.pi / 2) < phi ∧ phi < (3 * Real.pi / 2)
      ∨ phi = Real.pi / 2 then
      sqrt y_squared
    else
      -sqrt y_squared
  let x_squared := r * r * (sin theta) * (sin theta) - y_squared
  let x :=
    if (-Real.pi / 2) < phi ∧ phi < (Real.pi / 2) then
      sqrt x_squared
    else
      -sqrt x_squared

  ⟨![x, y, z]⟩
-/

--theorem toVec3_leftInverse : Function.LeftInverse Spherical.toVec3 Spherical.Vec3.toSpherical :=




noncomputable def euclidDist (v1 v2 : Vec3) : ℝ := ‖v2 - v1‖

noncomputable def sphericalDist (s1 s2 : Spherical) : ℝ :=
  let v1 := toVec3 s1
  let v2 := toVec3 s2
  euclidDist v1 v2

noncomputable def sphericalAdd (s1 s2 : Spherical) : Vec3 :=
  let v1 := toVec3 s1
  let v2 := toVec3 s2
  ⟨![
    v1.val ⟨0, by decide⟩ + v2.val ⟨0, by decide⟩,
    v1.val ⟨1, by decide⟩ + v2.val ⟨1, by decide⟩,
    v1.val ⟨2, by decide⟩ + v2.val ⟨2, by decide⟩
  ]⟩

noncomputable def sphericalDotProduct (s1 s2 : Spherical) : ℝ :=
  let v1 := toVec3 s1
  let v2 := toVec3 s2
  v1.val ⟨0, by decide⟩ * v2.val ⟨0, by decide⟩ +
  v1.val ⟨1, by decide⟩ * v2.val ⟨1, by decide⟩ +
  v1.val ⟨2, by decide⟩ * v2.val ⟨2, by decide⟩

noncomputable def sphericalCrossProduct (s1 s2 : Spherical) : Vec3 :=
  let v1 := toVec3 s1
  let v2 := toVec3 s2
  ⟨![
    v1.val ⟨1, by decide⟩ * v2.val ⟨2, by decide⟩ - v1.val ⟨2, by decide⟩ * v2.val ⟨1, by decide⟩,
    v1.val ⟨2, by decide⟩ * v2.val ⟨0, by decide⟩ - v1.val ⟨0, by decide⟩ * v2.val ⟨2, by decide⟩,
    v1.val ⟨0, by decide⟩ * v2.val ⟨1, by decide⟩ - v1.val ⟨1, by decide⟩ * v2.val ⟨0, by decide⟩
  ]⟩

noncomputable def unitSphericalVector (s : Spherical) : Spherical :=
  { r := 1,
    theta := s.theta,
    phi := s.phi,
    r_bounds := by linarith,
    theta_bounds := s.theta_bounds,
    phi_bounds := s.phi_bounds,
    r_zero_bound := by simp,
    theta_zero_bound := s.theta_zero_bound,
    theta_pi_bound := s.theta_pi_bound
  }


end Spherical
end PhysLean.Mathematics.SphericalCoordinates
