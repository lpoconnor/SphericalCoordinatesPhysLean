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
import Mathlib.Tactic.LinearCombination'
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
    linarith [Real.neg_pi_div_two_lt_arctan u]

theorem atan2_upper_bound (y x : ℝ) : atan2 y x ≤ Real.pi := by
  unfold atan2
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    simp [h]
    generalize y / (√(x^2 + y^2) + x) = u
    linarith [Real.arctan_lt_pi_div_two u]

theorem atan2_bounds (y x : ℝ) :
  -Real.pi < atan2 y x ∧ atan2 y x ≤ Real.pi := by
  exact ⟨atan2_lower_bound y x, atan2_upper_bound y x⟩

lemma neg_div_sqrt_sq (x : ℝ) (hx : x < 0) : x / Real.sqrt (x^2) = -1 := by
  rw [Real.sqrt_sq_eq_abs x]
  rw [abs_of_neg hx]
  field_simp [hx, ne_of_lt]

/--theorem one_sub_u_sq_eq (x y : ℝ) (u : ℝ) (h : u = y / (Real.sqrt (x^2 + y^2) + x)) :
  1 - u^2 = ((Real.sqrt (x^2 + y^2) + x)^2 - y^2) / (Real.sqrt (x^2 + y^2) + x)^2 := by
    rw [h]
    field_simp--/

lemma non_zero_square_positive (y : ℝ) (h_y_nonzero: y ≠ 0) : y^2 > 0 := by simp [sq_pos_of_ne_zero, h_y_nonzero]

theorem sqrt_x2_y2_add_x_ne_zero {x y : ℝ} (h : x^2 + y^2 > 0) (hx : x ≥ 0 ∨ y ≠ 0) :
  Real.sqrt (x^2 + y^2) + x > 0 := by
  cases hx with
  | inl h_x_nonneg =>
    linarith [Real.sqrt_pos.mpr h]
  | inr h_y_nonzero =>
    have h_le : |x| ≤ √(x^2 + y^2) := (by nlinarith [abs_le_sqrt (show x^2 ≤ x^2 + y^2 from (by nlinarith))])
    have h_ne : |x| ≠ √(x^2 + y^2) := by
      intro h_eq
      rw [← Real.sqrt_sq_eq_abs] at h_eq
      rw [Real.sqrt_inj (by nlinarith [Real.sqrt_nonneg]) (by nlinarith [Real.sqrt_nonneg])] at h_eq
      rw [add_comm] at h_eq
      rw [← sub_eq_iff_eq_add] at h_eq
      rw [sub_self] at h_eq
      rw [eq_comm] at h_eq
      simp at h_eq
      contradiction
    have h_lt : |x| < √(x^2 + y^2) := by simp [lt_of_le_of_ne , h_le, h_ne]
    have h_le_abs : -x ≤ |x| := (by exact neg_le_abs (x : ℝ))
    linarith [h_lt, h_le_abs]

lemma pos_square_sum (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  x^2 + y^2 > 0 := by
    by_cases h_x_non_zero : x ≠ 0
    · nlinarith [sq_pos_of_ne_zero h_x_non_zero]
    · have h_y_non_zero : y ≠ 0 := by
        cases h_not_both_zero with
        | inl hy => exact hy
        | inr hx =>
            rw [ne_eq, not_not] at h_x_non_zero
            exact (hx h_x_non_zero).elim
      nlinarith [h_y_non_zero, sq_pos_of_ne_zero h_y_non_zero]

theorem cos_atan2_non_empty (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  Real.cos (atan2 y x) = x / Real.sqrt (x^2 + y^2) := by
  unfold atan2
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [h]
    simp [neg_div_sqrt_sq, h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    generalize h_u : y / (√(x^2 + y^2) + x) = u
    simp [h, Real.cos_two_mul, Real.cos_arctan]
    have h_non_neg : 0 ≤ (1 + u^2) := by nlinarith
    simp [h_non_neg, sq_sqrt]
    field_simp
    rw [tsub_add_eq_tsub_tsub]
    norm_num
    rw [not_and_or, ← ne_eq, not_lt, Or.comm] at h

    have h_pos_sq_sum : x^2 + y^2 > 0 := by simp [pos_square_sum, h_not_both_zero]
    have h_pos_rt_sq_sum : √(x^2 + y^2) > 0 := by simp [pos_square_sum, h_not_both_zero]
    have h_denom_non_zero : Real.sqrt (x^2 + y^2) + x ≠ 0 := by exact ne_of_gt (sqrt_x2_y2_add_x_ne_zero h_pos_sq_sum h)
    have h_collect_terms : 1 - u^2 = (1 + u^2) * x / √(x^2 + y^2) ↔ (1 - u^2) / (1 + u^2) = x / √(x^2 + y^2) := by
      have h_non_zero_rt_sq_sum : √(x^2 + y^2) ≠ 0 := by linarith [h_pos_rt_sq_sum]
      have h_one_plus_u_sq_non_zero : 1 + u^2 ≠ 0 := by nlinarith;
      field_simp [h_one_plus_u_sq_non_zero, h_non_zero_rt_sq_sum];

    simp [h_collect_terms]

    have h_u_division : (1 - u^2) / (1 + u^2) = ((√(x^2 + y^2) + x)^2 - y^2) / ((√(x^2 + y^2) + x)^2 + y^2) := by
      simp [← h_u]
      field_simp
    simp [h_u_division]

    have h_bracket_sq_expansion : (√(x^2 + y^2) + x)^2 = 2 * x^2 + y^2 + 2 * x * √(x^2 + y^2) := by
      ring_nf
      field_simp
      have h_non_neg_sq_sum : x^2 + y^2 ≥ 0 := by linarith [sq_nonneg x, sq_nonneg y]
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

theorem cos_atan2 (y x : ℝ) :
  Real.cos (atan2 y x) = if y ≠ 0 ∨ x ≠ 0 then x / Real.sqrt (x^2 + y^2) else 1 := by
    by_cases h_non_empty: y ≠ 0 ∨ x ≠ 0
    · simp [h_non_empty]
      exact cos_atan2_non_empty y x h_non_empty
    · simp [h_non_empty]
      rw [not_or, ne_eq, ne_eq, not_not, not_not] at h_non_empty
      simp [atan2_empty_zero, h_non_empty]

theorem sin_atan2_non_empty (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  Real.sin (atan2 y x) = y / Real.sqrt (x^2 + y^2) := by
  unfold atan2
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    generalize h_u : y / (√(x^2 + y^2) + x) = u
    have h_one_plus_u_sq_non_zero : 1 + u^2 ≠ 0 := by nlinarith
    field_simp [h_one_plus_u_sq_non_zero]

    simp [h, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    field_simp [h_one_plus_u_sq_non_zero]
    have h_non_neg : 0 ≤ 1 + u^2 := by nlinarith
    simp [sq_sqrt, h_non_neg]
    simp [← h_u]
    field_simp

    rw [not_and_or, ← ne_eq, not_lt, Or.comm] at h

    have h_pos_sq_sum : x^2 + y^2 > 0 := by simp [pos_square_sum, h_not_both_zero]
    have h_denom_non_zero : Real.sqrt (x^2 + y^2) + x ≠ 0 := by exact ne_of_gt (sqrt_x2_y2_add_x_ne_zero h_pos_sq_sum h)

    by_cases h_y_zero : y = 0
    · simp [h_y_zero]
    · field_simp [h_y_zero]
      ring_nf
      have h_sq_sqrt_sum : √(x^2 + y^2) ^ 2 = x^2 + y^2 := Real.sq_sqrt (by nlinarith [h_pos_sq_sum])
      linarith [h_sq_sqrt_sum]

theorem sin_atan2 (y x : ℝ) :
  Real.sin (atan2 y x) = if y ≠ 0 ∨ x ≠ 0 then y / Real.sqrt (x^2 + y^2) else 0 := by
    by_cases h_non_empty: y ≠ 0 ∨ x ≠ 0
    · simp [h_non_empty]
      exact sin_atan2_non_empty y x h_non_empty
    · simp [h_non_empty]
      rw [not_or, ne_eq, ne_eq, not_not, not_not] at h_non_empty
      simp [atan2_empty_zero, h_non_empty]


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

lemma abs_z_over_r_bounds (x : ℝ) (y : ℝ) (z : ℝ)
  (r : ℝ) (h_r_def : r = √(x^2+y^2+z^2)) (h_r_non_zero : r ≠ 0) :
  abs (z / r) ≤ 1 := by
    have h_r_nonneg : 0 ≤ r := by simp [h_r_def]
    have r_pos : 0 < r := lt_of_le_of_ne h_r_nonneg h_r_non_zero.symm
    have h_sq : z^2 ≤ x^2 + y^2 + z^2 := by nlinarith
    simp [abs_div, abs_of_pos, r_pos]
    field_simp
    simp [h_r_def]
    simp [abs_le]
    constructor
    · simp [neg_le]
      have neg_z_le_sqrt : -z ≤ Real.sqrt (x^2 + y^2 + z^2) := by
        by_cases hz : z ≥ 0
        · linarith
        · have h_case_resolved : -z ≤ sqrt (x^2 + y^2 + z^2) :=
            sq_le_then_le_sqrt (-z : ℝ) (x^2 + y^2 + z^2) (by linarith) (by nlinarith) (by
              rw [neg_sq]
              exact h_sq)
          simp [h_case_resolved]
      simp [neg_z_le_sqrt]
    · have h_z_below : z ≤ sqrt (x^2 + y^2 + z^2) := by
        by_cases h_z : z ≥ 0
        · exact sq_le_then_le_sqrt z (x^2 + y^2 + z^2) (by simp [h_z]) (by nlinarith) h_sq
        · have h_z_le_sqrt_sum : -z ≤ sqrt (x^2 + y^2 + z^2) :=
            sq_le_then_le_sqrt (-z : ℝ) (x^2 + y^2 + z^2) (by linarith) (by nlinarith) (by
              rw [neg_sq]
              exact h_sq)
          linarith [h_z_le_sqrt_sum, h_z]
      simp [h_z_below]

theorem theta_zero_implies_phi_zero
  (x : ℝ) (y : ℝ) (z : ℝ) (r : ℝ) (theta : ℝ) (phi : ℝ)
  (h_r_val : r = √(x^2 + y^2 + z^2)) (h_r_bounds : 0 ≤ r) (h_r_non_zero : r ≠ 0)
  (h_theta_def : theta = Real.arccos (z / r))
  (h_phi_def : phi = atan2 y x) :
  theta = 0 → phi = 0 := by
    intro h_theta
    simp [h_phi_def]

    -- -1 ≤ z / r ≤ 1
    have h_abs_z_over_r_bounds : abs (z / r) ≤ 1 := abs_z_over_r_bounds x y z r h_r_val h_r_non_zero

    have h_z_div_r : z / r = 1 := by
      have h_fraction_div_zero : Real.arccos (z / r) = 0 → (z / r) = 1 := by
        intro h_frac_div
        have h_cos_theta : z / r = Real.cos theta := by simp [h_theta_def, Real.cos_arccos, (abs_le.mp h_abs_z_over_r_bounds).1, (abs_le.mp h_abs_z_over_r_bounds).2]
        simp [h_cos_theta, h_theta]
      apply h_fraction_div_zero
      simp [← h_theta, h_theta_def]

    have h_z_r : z = r := (by field_simp at h_z_div_r; simp [h_z_div_r])

    have h_r_square : r^2 = x^2 + y^2 + z^2 := by
      have h_sum_sq : √(x^2 + y^2 + z^2)^2 = x^2 + y^2 + z^2 := by simpa using Real.sq_sqrt (by nlinarith)
      simp [h_r_val, h_sum_sq]

    have h_x_y_sq : x^2 + y^2 = 0 := by
      have h_add_z : x^2 + y^2 + z^2 = z^2 → x^2 + y^2 = 0 := by
        intro _
        linarith
      apply h_add_z
      simp [h_r_square.symm]
      rw [sq_eq_sq₀ (by linarith) (by linarith)]
      simp [h_z_r]

    have h_x_0 : x = 0 := by nlinarith [h_x_y_sq]
    have h_y_0 : y = 0 := by nlinarith [h_x_y_sq]

    simp [atan2_empty_zero, h_x_0, h_y_0]

theorem theta_pi_implies_phi_zero
  (x : ℝ) (y : ℝ) (z : ℝ) (r : ℝ) (theta : ℝ) (phi : ℝ)
  (h_r_val : r = √(x^2 + y^2 + z^2)) (h_r_bounds : 0 ≤ r) (h_r_non_zero : r ≠ 0)
  (h_theta_def : theta = Real.arccos (z / r))
  (h_phi_def : phi = atan2 y x) :
  theta = Real.pi → phi = 0 := by
    intro h_theta

    -- -1 ≤ z / r ≤ 1
    have r_pos : 0 < r := lt_of_le_of_ne h_r_bounds h_r_non_zero.symm
    have h_abs_z_over_r_bounds : abs (z / r) ≤ 1 := by
      simp [abs_div, abs_of_pos, r_pos]
      field_simp
      simp [h_r_val]
      simp [abs_le]
      have h_sq : z^2 ≤ x^2 + y^2 + z^2 := by nlinarith
      constructor
      · simp [neg_le]
        have neg_z_le_sqrt : -z ≤ Real.sqrt (x^2 + y^2 + z^2) := by
          by_cases hz : z ≥ 0
          · linarith
          · have h_case_resolved : -z ≤ sqrt (x^2 + y^2 + z^2) :=
              sq_le_then_le_sqrt (-z : ℝ) (x^2 + y^2 + z^2) (by linarith) (by nlinarith) (by
                rw [neg_sq]
                exact h_sq)
            simp [h_case_resolved]
        simp [neg_z_le_sqrt]
      · have h_z_below : z ≤ sqrt (x^2 + y^2 + z^2) := by
          by_cases h_z : z ≥ 0
          · exact sq_le_then_le_sqrt z (x^2 + y^2 + z^2) (by simp [h_z]) (by nlinarith) h_sq
          · have h_z_le_sqrt_sum : -z ≤ sqrt (x^2 + y^2 + z^2) :=
              sq_le_then_le_sqrt (-z : ℝ) (x^2 + y^2 + z^2) (by linarith) (by nlinarith) (by
                rw [neg_sq]
                exact h_sq)
            linarith [h_z_le_sqrt_sum, h_z]
        simp [h_z_below]

    have h_z_div_r : z / r = -1 := by
      have h_fraction_div_pi : Real.arccos (z / r) = Real.pi → z / r = -1 := by
        intro h_frac
        have h_cos_theta : z / r = Real.cos theta := by simp [h_theta_def, Real.cos_arccos, (abs_le.mp h_abs_z_over_r_bounds).1, (abs_le.mp h_abs_z_over_r_bounds).2]
        simp [h_cos_theta, h_theta]
      apply h_fraction_div_pi
      simp [← h_theta, h_theta_def]

    have h_z_r : z = -r := (by field_simp at h_z_div_r; simp [h_z_div_r])

    have h_r_square : r^2 = x^2 + y^2 + z^2 := by
      have h_sum_sq : √(x^2 + y^2 + z^2)^2 = x^2 + y^2 + z^2 := by simpa using Real.sq_sqrt (by nlinarith)
      simp [h_r_val, h_sum_sq]

    have h_x_y_sq : x^2 + y^2 = 0 := by
      have h_add_z : x^2 + y^2 + z^2 = z^2 → x^2 + y^2 = 0 := by
        intro _
        linarith
      apply h_add_z
      simp [h_r_square.symm]
      rw [sq_eq_sq_iff_eq_or_eq_neg.mpr]
      simp [h_z_r]

    have h_x_0 : x = 0 := by nlinarith [h_x_y_sq]
    have h_y_0 : y = 0 := by nlinarith [h_x_y_sq]

    simp [h_phi_def, h_x_0, h_y_0, atan2_empty_zero]


lemma sq_eq_pow_two (a : ℝ) : a * a = a^2 := by linarith

noncomputable def Vec3.toSpherical (v : Vec3) : Spherical :=
  let x := x v
  let y := y v
  let z := z v
  let r := Real.sqrt (x*x + y*y + z*z)
  if hr : r = 0 then
    { r := r,
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
      theta_zero_bound := theta_zero_implies_phi_zero x y z r theta phi (by simp [r, sq_eq_pow_two]) (by apply Real.sqrt_nonneg) (by simp [hr]) (by simp [theta]) (by simp [phi])
      theta_pi_bound   := theta_pi_implies_phi_zero   x y z r theta phi (by simp [r, sq_eq_pow_two]) (by apply Real.sqrt_nonneg) (by simp [hr]) (by simp [theta]) (by simp [phi])
    }

lemma cancel_last_term (a b : ℝ) (h_b : b = 1) : a * b = a := by
  simp [h_b]

lemma equal_Vec3s
  (v : Vec3) (v_new : Vec3)
  (h_x : x v = x v_new) (h_y : y v = y v_new) (h_z : z v = z v_new) :
  v = v_new := by
    ext i : 3
    fin_cases i
    · simp
      change Spherical.x v = Spherical.x v_new
      exact h_x
    · simp
      exact h_y
    · simp
      exact h_z


theorem toVec3_leftInverse : Function.LeftInverse toVec3 Vec3.toSpherical := by
  intro v
  let x_og := Spherical.x v
  let y_og := Spherical.y v
  let z_og := Spherical.z v
  let s := Vec3.toSpherical v
  let r := s.r
  have h_r_def : r = Real.sqrt (x_og*x_og + y_og*y_og + z_og*z_og) := by
    subst r
    change (v.toSpherical).r = Real.sqrt (x_og*x_og + y_og*y_og + z_og*z_og)
    simp [Vec3.toSpherical, x_og, y_og, z_og]
    by_cases h_sqrt_sum_zero : Real.sqrt (x v * x v + y v * y v + z v * z v) = 0
    · simp [h_sqrt_sum_zero]
    · simp [h_sqrt_sum_zero]
  have h_r_non_neg : 0 ≤ r := by simp [h_r_def]
  have h_sum_non_neg : 0 ≤ x_og*x_og + y_og*y_og + z_og*z_og := by nlinarith
  have h_sum_sq_non_neg : 0 ≤ x_og^2 + y_og^2 + z_og^2 := by nlinarith
  have h_r_sq : r^2 = x_og*x_og + y_og*y_og + z_og*z_og := by simp [h_r_def, Real.sq_sqrt, h_sum_non_neg]

  have h_all_v_zero : r = 0 → x_og = 0 ∧ y_og = 0 ∧ z_og = 0 := by
      intro h_r_zero
      have h_sq : x_og^2 + y_og^2 + z_og^2 = 0 := by
        have h_r_sq : r^2 = 0 := by simp [h_r_zero]
        linarith [h_r_def]
      exact ⟨(by nlinarith), (by nlinarith), (by nlinarith)⟩

  by_cases h_r : r = 0
  · have h_all_zero : s.theta = 0 ∧ s.phi = 0 := s.r_zero_bound h_r
    let v_new := toVec3 s
    let x_new := Spherical.x v_new
    let y_new := Spherical.y v_new
    let z_new := Spherical.z v_new

    have h_coords_unchanged : x_new = x_og ∧ y_new = y_og ∧ z_new = z_og := by
      have h_x_formula : x_new = s.r * Real.sin s.theta * Real.cos s.phi := (by simp [x_new, Spherical.x]; rfl)
      have h_y_formula : y_new = s.r * Real.sin s.theta * Real.sin s.phi := (by simp [y_new, Spherical.y]; rfl)
      have h_z_formula : z_new = s.r * Real.cos s.theta := (by simp [z_new, Spherical.z]; rfl)
      simp [h_x_formula, h_y_formula, h_z_formula, h_all_zero.1, h_all_zero.2]
      simp [h_all_v_zero, h_r, r]

    change v_new = v
    exact equal_Vec3s v_new v (by simp [h_coords_unchanged.1, x_og, x_new]) (by simp [h_coords_unchanged.2, y_og, y_new]) (by simp [h_coords_unchanged.2.2, z_og, z_new])

  · let v_new := toVec3 s
    let x_new := Spherical.x v_new
    let y_new := Spherical.y v_new
    let z_new := Spherical.z v_new

    have h_r_non_zero : √(x v * x v + y v * y v + z v * z v) ≠ 0 := by
      change √(x_og * x_og + y_og * y_og + z_og * z_og) ≠ 0
      intro h_eq
      rw [h_r_def.symm] at h_eq
      contradiction
    have h_theta_def : s.theta = Real.arccos (z_og / r) := by
      change v.toSpherical.theta = Real.arccos (z_og / r)
      simp [Vec3.toSpherical, z_og, h_r_non_zero]
      change arccos (z_og / √(x_og * x_og + y_og * y_og + z_og * z_og)) = arccos (z_og / r)
      rw [h_r_def.symm]
    have h_phi_def : s.phi = atan2 y_og x_og := by
      change v.toSpherical.phi = atan2 y_og x_og
      simp [Vec3.toSpherical, x_og, y_og, h_r_non_zero]

    have h_term_one_max : y_og ≠ 0 ∨ x_og ≠ 0 → z_og^2 / (x_og^2 + y_og^2 + z_og^2) ≤ 1 := by
      intro h_non_empty
      rw [div_le_one, add_comm, ← sub_nonneg, add_comm, add_sub_assoc]
      simp
      nlinarith []
      cases h_non_empty with
      | inr h_y => nlinarith [h_y, sq_pos_iff.mpr h_y]
      | inl h_x => nlinarith [h_x, sq_pos_iff.mpr h_x]

    have h_x : x_new = x_og := by
      have h_x_formula : x_new = s.r * Real.sin s.theta * Real.cos s.phi := by (simp [x_new, Spherical.x]; rfl)
      simp [h_x_formula, h_theta_def, h_phi_def]
      simp [Real.sin_arccos, cos_atan2]
      by_cases h_non_empty : y_og ≠ 0 ∨ x_og ≠ 0
      · simp [h_non_empty, r, h_r_def]
        field_simp
        have h_sq_sqrt_sum : √(x_og^2 + y_og^2 + z_og^2) ^ 2 = x_og ^ 2 + y_og ^ 2 + z_og ^ 2 := by simp [Real.sq_sqrt, h_sum_sq_non_neg]
        simp [h_sq_sqrt_sum]
        by_cases h_x_zero : x_og = 0
        · simp [h_x_zero]
        · simp [mul_div_assoc]
          let large_term := √(x_og ^ 2 + y_og ^ 2 + z_og ^ 2) * (√(1 - z_og ^ 2 / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) / √(x_og ^ 2 + y_og ^ 2))
          have h_large_term_one : large_term = 1 := by
            change √(x_og ^ 2 + y_og ^ 2 + z_og ^ 2) * (√(1 - z_og ^ 2 / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) / √(x_og ^ 2 + y_og ^ 2)) = 1
            rw [← sqrt_div, ← sqrt_mul]
            have h_one_merge : (1 - z_og ^ 2 / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) = ((x_og ^ 2 + y_og ^ 2) / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) := by
              field_simp
              linarith
            simp [h_one_merge]
            field_simp
            nlinarith
            simp [h_term_one_max, h_non_empty]
          rw [mul_assoc]
          change x_og * large_term = x_og
          simp [h_large_term_one]
      · simp [h_non_empty, r, h_r_def]
        have h_xy_zero : y_og = 0 ∧ x_og = 0 := by
          push_neg at h_non_empty
          exact h_non_empty
        have h_x_zero : x_og = 0 := h_xy_zero.2
        have h_y_zero : y_og = 0 := h_xy_zero.1
        simp [h_x_zero, h_y_zero]
        have h_second_case : z_og ≠ 0 → √(1 - (z_og / √(z_og * z_og)) ^ 2) = 0 := by
          intro h_z_non_neg
          have h_z_pos : 0 ≤ z_og^2 := by nlinarith
          have h_z_sq_sqrt : √(z_og ^ 2) ^ 2 = z_og^2 := by simp [h_z_pos]
          have h_term_zero : 0 = 1 - (z_og / √(z_og * z_og)) ^ 2 := by
            field_simp [h_z_sq_sqrt]
            simp [h_z_sq_sqrt]
          simp [h_term_zero.symm]
        by_cases hz : z_og = 0
        · left
          simp [hz]
        · right
          exact h_second_case hz

    have h_y : y_new = y_og := by
      have h_y_formula : y_new = s.r * Real.sin s.theta * Real.sin s.phi := by
        simp [y_new, Spherical.y]
        rfl
      simp [h_y_formula, h_theta_def, h_phi_def]
      simp [Real.sin_arccos, sin_atan2]
      by_cases h_non_empty : y_og ≠ 0 ∨ x_og ≠ 0
      · simp [h_non_empty, r, h_r_def]
        field_simp
        have h_sq_sqrt_sum : √(x_og^2 + y_og^2 + z_og^2) ^ 2 = x_og ^ 2 + y_og ^ 2 + z_og ^ 2 := by simp [Real.sq_sqrt, h_sum_sq_non_neg]
        simp [h_sq_sqrt_sum]
        by_cases h_y_zero : y_og = 0
        · simp [h_y_zero]
        · simp [mul_div_assoc]

          let large_term := √(x_og ^ 2 + y_og ^ 2 + z_og ^ 2) * (√(1 - z_og ^ 2 / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) / √(x_og ^ 2 + y_og ^ 2))
          have h_large_term_one : large_term = 1 := by
            change √(x_og ^ 2 + y_og ^ 2 + z_og ^ 2) * (√(1 - z_og ^ 2 / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) / √(x_og ^ 2 + y_og ^ 2)) = 1
            rw [← sqrt_div, ← sqrt_mul]
            have h_one_merge : (1 - z_og ^ 2 / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) = ((x_og ^ 2 + y_og ^ 2) / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) := by
              field_simp
              linarith
            simp [h_one_merge]
            field_simp
            nlinarith
            simp [h_term_one_max, h_non_empty]
          rw [mul_assoc]
          change y_og * large_term = y_og
          simp [h_large_term_one]
      · simp [h_non_empty]
        have h_xy_zero : y_og = 0 ∧ x_og = 0 := by
          push_neg at h_non_empty
          exact h_non_empty
        have h_y_zero : y_og = 0 := h_xy_zero.1
        simp [h_y_zero]


    have h_z : z_new = z_og := by
      have h_z_formula : z_new = s.r * Real.cos s.theta := by
        simp [z_new, Spherical.z]
        rfl

      simp [h_z_formula, h_theta_def]
      have h_abs_z_over_r_bounds : abs (z_og / r) ≤ 1 := abs_z_over_r_bounds x_og y_og z_og r (by simp [h_r_def, pow_two]) h_r
      simp [Real.cos_arccos, h_abs_z_over_r_bounds, abs_le.mp, r] -- |z / r| < 1 thingy
      field_simp [h_r, r]

    change v_new = v
    exact equal_Vec3s v_new v (by simp [h_x, x_og, x_new]) (by simp [h_y, y_og, y_new]) (by simp [h_z, z_og, z_new])


  /--⟨![
    s.r * Real.sin s.theta * Real.cos s.phi,
    s.r * Real.sin s.theta * Real.sin s.phi,
    s.r * Real.cos s.theta
  ]⟩--/






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
