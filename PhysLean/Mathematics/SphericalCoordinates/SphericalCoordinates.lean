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
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
namespace PhysLean.Mathematics.SphericalCoordinates

--#count_heartbeats

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

lemma atan2_empty_zero : atan2 0 0 = 0 := by simp only [atan2, lt_self_iff_false, and_false, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, sqrt_zero, div_zero, arctan_zero, mul_zero]

theorem atan2_lower_bound (y x : ℝ) : -Real.pi < atan2 y x := by
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [atan2, h]
    linarith [Real.pi_pos]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    simp [atan2, h]
    generalize y / (Real.sqrt (x^2 + y^2) + x) = u
    linarith [Real.neg_pi_div_two_lt_arctan u]

theorem atan2_upper_bound (y x : ℝ) : atan2 y x ≤ Real.pi := by
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [atan2, h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    simp [atan2, h]
    generalize y / (√(x^2 + y^2) + x) = u
    linarith [Real.arctan_lt_pi_div_two u]

theorem atan2_upper_bound' (y x : ℝ) (h_xy : (¬(y = 0 ∧ x < 0))) : atan2 y x < Real.pi := by
  simp [atan2, h_xy]
  generalize y / (√(x^2 + y^2) + x) = u
  linarith [Real.arctan_lt_pi_div_two u]

theorem atan2_bounds (y x : ℝ) :
  -Real.pi < atan2 y x ∧ atan2 y x ≤ Real.pi := by
  exact ⟨atan2_lower_bound y x, atan2_upper_bound y x⟩

lemma neg_div_sqrt_sq (x : ℝ) (h_x : x < 0) : x / Real.sqrt (x^2) = -1 := by
  rw [Real.sqrt_sq_eq_abs x]
  rw [abs_of_neg h_x]
  field_simp [h_x, ne_of_lt]

lemma non_zero_square_positive (y : ℝ) (h_y_nonzero: y ≠ 0) : y^2 > 0 := by simp [sq_pos_of_ne_zero, h_y_nonzero]

theorem sqrt_x2_y2_add_x_ne_zero {x y : ℝ} (h : x^2 + y^2 > 0) (h_x : x ≥ 0 ∨ y ≠ 0) :
  Real.sqrt (x^2 + y^2) + x > 0 := by
  cases h_x with
  | inl h_x_nonneg =>
    linarith [Real.sqrt_pos.mpr h]
  | inr h_y_nonzero =>
    have h_lt : |x| < √(x^2 + y^2) := by
      rw [← Real.sqrt_sq_eq_abs, sqrt_lt_sqrt_iff]
      simpa using sq_pos_of_ne_zero h_y_nonzero
      exact sq_nonneg x
    have h_le_abs : -x ≤ |x| := (by exact neg_le_abs (x : ℝ))
    linarith [h_lt, h_le_abs]

lemma pos_square_sum (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  0 < x^2 + y^2 := by
    by_cases h_x_non_zero : x ≠ 0
    · nlinarith [sq_pos_of_ne_zero h_x_non_zero]
    · simp [h_x_non_zero] at h_not_both_zero
      push_neg at h_not_both_zero
      nlinarith [h_not_both_zero, sq_pos_of_ne_zero h_not_both_zero]

theorem cos_atan2_non_empty (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  Real.cos (atan2 y x) = x / Real.sqrt (x^2 + y^2) := by
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [atan2,h]
    simp [neg_div_sqrt_sq, h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    simp [atan2]
    generalize h_u : y / (√(x^2 + y^2) + x) = u
    have h_non_neg : 0 ≤ (1 + u^2) := by nlinarith
    simp [h, Real.cos_two_mul, Real.cos_arctan, h_non_neg, sq_sqrt]
    field_simp
    rw [tsub_add_eq_tsub_tsub]
    norm_num
    rw [not_and_or, ← ne_eq, not_lt, Or.comm] at h

    have h_pos_rt_sq_sum : √(x^2 + y^2) > 0 := by simp [pos_square_sum, h_not_both_zero]
    have h_denom_non_zero : Real.sqrt (x^2 + y^2) + x ≠ 0 := by exact ne_of_gt (sqrt_x2_y2_add_x_ne_zero (by simp [pos_square_sum, h_not_both_zero]) h)
    have h_collect_terms : 1 - u^2 = (1 + u^2) * x / √(x^2 + y^2) ↔ (1 - u^2) / (1 + u^2) = x / √(x^2 + y^2) := by grind

    rw [← h_u]
    field_simp

    have h_bracket_sq_expansion : (√(x^2 + y^2) + x)^2 = 2 * x^2 + y^2 + 2 * x * √(x^2 + y^2) := by grind
    grind

theorem cos_atan2 (y x : ℝ) :
  Real.cos (atan2 y x) = if y ≠ 0 ∨ x ≠ 0 then x / Real.sqrt (x^2 + y^2) else 1 := by
    by_cases h_non_empty: y ≠ 0 ∨ x ≠ 0
    · simpa [h_non_empty] using cos_atan2_non_empty y x h_non_empty
    · push_neg at h_non_empty
      simp [atan2_empty_zero, h_non_empty]

theorem sin_atan2_non_empty (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  Real.sin (atan2 y x) = y / Real.sqrt (x^2 + y^2) := by
  by_cases h : y = 0 ∧ x < 0
  · -- atan2 = pi
    simp [atan2, h]
  · -- atan2 = 2 * arctan (y / (√(x^2 + y^2) + x))
    simp [atan2]
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

    have h_pos_sq_sum : 0 < x^2 + y^2 := by simp [pos_square_sum, h_not_both_zero]
    have h_denom_non_zero : Real.sqrt (x^2 + y^2) + x ≠ 0 := by exact ne_of_gt (sqrt_x2_y2_add_x_ne_zero h_pos_sq_sum h)

    by_cases h_y_zero : y = 0
    · simp [h_y_zero]
    · grind

theorem sin_atan2 (y x : ℝ) :
  Real.sin (atan2 y x) = if y ≠ 0 ∨ x ≠ 0 then y / Real.sqrt (x^2 + y^2) else 0 := by
    by_cases h_non_empty: y ≠ 0 ∨ x ≠ 0
    · simpa [h_non_empty] using sin_atan2_non_empty y x h_non_empty
    · push_neg at h_non_empty
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
  (r : ℝ) (h_r_def : r = √(x^2 + y^2 + z^2)) (h_r_non_zero : r ≠ 0) :
  abs (z / r) ≤ 1 := by
    have r_pos : 0 < r := lt_of_le_of_ne (by simp [h_r_def]) h_r_non_zero.symm
    have h_sq : z^2 ≤ x^2 + y^2 + z^2 := by nlinarith
    simp [abs_div, abs_of_pos, r_pos]
    field_simp
    simp [h_r_def, abs_le]
    have h_simplify (a : ℝ) : a ≤ √(x ^ 2 + y ^ 2 + a^2) := by
      by_cases h_a : a < 0
      · grind [sqrt_nonneg]
      · push_neg at h_a
        apply sq_le_then_le_sqrt (a) (x^2 + y^2 + a^2)
        exact h_a
        nlinarith
        nlinarith
    constructor
    · rw [← neg_le_neg_iff]
      simp
      grind [neg_sq]
    · by_cases h_z : z < 0
      · grind
      · exact h_simplify z

theorem theta_zero_or_pi_implies_phi_zero
  (x : ℝ) (y : ℝ) (z : ℝ) (r : ℝ) (theta : ℝ) (phi : ℝ)
  (h_r_val : r = √(x^2 + y^2 + z^2)) (h_r_bounds : 0 ≤ r) (h_r_non_zero : r ≠ 0)
  (h_theta_def : theta = Real.arccos (z / r))
  (h_phi_def : phi = atan2 y x) :
  theta = 0 ∨ theta = π → phi = 0 := by
    intro h_theta
    simp [h_phi_def]

    -- -1 ≤ z / r ≤ 1
    have h_abs_z_over_r_bounds : abs (z / r) ≤ 1 := abs_z_over_r_bounds x y z r h_r_val h_r_non_zero

    have h_z_div_r_pos : theta = 0 → z / r = 1 := by
      intro h_zero
      have h_fraction_div_zero : Real.arccos (z / r) = 0 → (z / r) = 1 := by
        intro h_frac_div
        have h_cos_theta : z / r = Real.cos theta := by simp [h_theta_def, Real.cos_arccos, (abs_le.mp h_abs_z_over_r_bounds).1, (abs_le.mp h_abs_z_over_r_bounds).2]
        simp [h_cos_theta, h_zero]
      apply h_fraction_div_zero
      simp [← h_zero, h_theta_def]

    have h_z_div_r_neg : theta = π → z / r = -1 := by
      intro h_pi
      have h_fraction_div_pi : Real.arccos (z / r) = Real.pi → z / r = -1 := by
        intro h_frac
        have h_cos_theta : z / r = Real.cos theta := by simp [h_theta_def, Real.cos_arccos, (abs_le.mp h_abs_z_over_r_bounds).1, (abs_le.mp h_abs_z_over_r_bounds).2]
        simp [h_cos_theta, h_pi]
      apply h_fraction_div_pi
      simp [← h_pi, h_theta_def]

    have h_z_r_pos : theta = 0 → z = r  := (by intro h_theta_zero; field_simp at h_z_div_r_pos; simp [h_theta_zero, h_z_div_r_pos])
    have h_z_r_neg : theta = π → z = -r := (by intro h_theta_pi; field_simp at h_z_div_r_neg; simp [h_theta_pi, h_z_div_r_neg])

    have h_r_square : r^2 = x^2 + y^2 + z^2 := by
      have h_sum_sq : √(x^2 + y^2 + z^2)^2 = x^2 + y^2 + z^2 := by simpa using Real.sq_sqrt (by nlinarith)
      simp [h_r_val, h_sum_sq]

    have h_x_y_sq : x^2 + y^2 = 0 := by
      have h_add_z : x^2 + y^2 + z^2 = z^2 → x^2 + y^2 = 0 := by
        intro _
        linarith
      apply h_add_z
      simp [h_r_square.symm]
      cases h_theta with
      | inl h_theta_zero =>
        rw [sq_eq_sq₀ (by linarith) (by grind)]
        simp [h_theta_zero, h_z_r_pos]
      | inr h_theta_pi =>
        rw [sq_eq_sq_iff_eq_or_eq_neg.mpr]
        simp [h_theta_pi, h_z_r_neg]

    have h_x_zero : x = 0 := by nlinarith [h_x_y_sq]
    have h_y_zero : y = 0 := by nlinarith [h_x_y_sq]

    simp [atan2_empty_zero, h_x_zero, h_y_zero]

theorem theta_zero_implies_phi_zero
  (x : ℝ) (y : ℝ) (z : ℝ) (r : ℝ) (theta : ℝ) (phi : ℝ)
  (h_r_val : r = √(x^2 + y^2 + z^2)) (h_r_bounds : 0 ≤ r) (h_r_non_zero : r ≠ 0)
  (h_theta_def : theta = Real.arccos (z / r))
  (h_phi_def : phi = atan2 y x) :
  theta = 0 → phi = 0 := by
    intro theta_zero
    exact theta_zero_or_pi_implies_phi_zero x y z r theta phi h_r_val h_r_bounds h_r_non_zero h_theta_def h_phi_def (by simp [theta_zero])

theorem theta_pi_implies_phi_zero
  (x : ℝ) (y : ℝ) (z : ℝ) (r : ℝ) (theta : ℝ) (phi : ℝ)
  (h_r_val : r = √(x^2 + y^2 + z^2)) (h_r_bounds : 0 ≤ r) (h_r_non_zero : r ≠ 0)
  (h_theta_def : theta = Real.arccos (z / r))
  (h_phi_def : phi = atan2 y x) :
  theta = Real.pi → phi = 0 := by
    intro theta_pi
    exact theta_zero_or_pi_implies_phi_zero x y z r theta phi h_r_val h_r_bounds h_r_non_zero h_theta_def h_phi_def (by simp [theta_pi])

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
      theta_zero_bound := theta_zero_implies_phi_zero x y z r theta phi (by simp [r, sq_eq_pow_two]) (by apply Real.sqrt_nonneg) (by simp [hr]) (by simp [theta]) (by simp [phi]),
      theta_pi_bound   := theta_pi_implies_phi_zero   x y z r theta phi (by simp [r, sq_eq_pow_two]) (by apply Real.sqrt_nonneg) (by simp [hr]) (by simp [theta]) (by simp [phi])
    }

lemma sum_triple_sq_non_zero (x y z : ℝ) (h_xyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : x^2 + y^2 + z^2 ≠ 0 := by
  rcases h_xyz with h_x | h_y | h_z
  · nlinarith [sq_pos_of_ne_zero h_x]
  · nlinarith [sq_pos_of_ne_zero h_y]
  · nlinarith [sq_pos_of_ne_zero h_z]

lemma sum_triple_sqrt_non_zero (x y z : ℝ) (h_xyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : √(x^2 + y^2 + z^2) ≠ 0 := by
  have h_xyz_pos : x^2 + y^2 + z^2 ≥ 0 := by nlinarith
  simp [sqrt_ne_zero h_xyz_pos, sum_triple_sq_non_zero x y z h_xyz]

lemma cancel_last_term (a b : ℝ) (h_b : b = 1) : a * b = a := by
  simp [h_b]

lemma equal_Vec3s
  (v : Vec3) (v_new : Vec3)
  (h_x : x v = x v_new) (h_y : y v = y v_new) (h_z : z v = z v_new) :
  v = v_new := by
    ext i : 3
    fin_cases i
    · simpa using h_x
    · simpa using h_y
    · simpa using h_z

lemma sin_zero_or_pi (x : ℝ) (h_x : x = 0 ∨ x = Real.pi) : Real.sin x = 0 := by
  cases h_x with
  | inl h_zero => simp [h_zero]
  | inr h_pi => simp [h_pi]

lemma Vec3_non_empty (v : Vec3) (h_v : v ≠ 0) :
  x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨h_x, h_y, h_z⟩

    have h_v_zero : v = 0 := by
      ext i
      fin_cases i
      · simp [x] at h_x
        simp [h_x]
      · simp [y] at h_y
        simp [h_y]
      · simp [z] at h_z
        simp [h_z]
    contradiction

lemma r_zero_then_Vec3_zero (r x y z: ℝ) (h_r_def : r = Real.sqrt (x*x + y*y + z*z)) :
  r = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  intro h_r_zero
  have h_sq : x^2 + y^2 + z^2 = 0 := by
    have h_r_sq : r^2 = 0 := by simp [h_r_zero]
    rw [← pow_two, ← pow_two, ← pow_two, h_r_zero, eq_comm, sqrt_eq_zero] at h_r_def
    exact h_r_def
    nlinarith
  exact ⟨(by nlinarith), (by nlinarith), (by nlinarith)⟩

theorem toVec3_leftInverse : Function.LeftInverse toVec3 Vec3.toSpherical := by
  intro v
  let x_og := Spherical.x v
  let y_og := Spherical.y v
  let z_og := Spherical.z v
  let s := Vec3.toSpherical v
  let r := s.r

  have h_r_def : r = Real.sqrt (x_og*x_og + y_og*y_og + z_og*z_og) := by
    simp [r, s, Vec3.toSpherical]
    split_ifs <;> rfl

  have h_sum_non_neg : 0 ≤ x_og*x_og + y_og*y_og + z_og*z_og := by nlinarith
  have h_sum_sq_non_neg : 0 ≤ x_og^2 + y_og^2 + z_og^2 := by nlinarith
  have h_r_sq : r^2 = x_og*x_og + y_og*y_og + z_og*z_og := by simp [h_r_def, Real.sq_sqrt, h_sum_non_neg]

  by_cases h_r : r = 0
  · let v_new := toVec3 s
    let x_new := Spherical.x v_new
    let y_new := Spherical.y v_new
    let z_new := Spherical.z v_new

    have h_coords_unchanged : x_new = x_og ∧ y_new = y_og ∧ z_new = z_og := by
      have h_x_formula : x_new = s.r * Real.sin s.theta * Real.cos s.phi := (by simp [x_new, Spherical.x]; rfl)
      have h_y_formula : y_new = s.r * Real.sin s.theta * Real.sin s.phi := (by simp [y_new, Spherical.y]; rfl)
      have h_z_formula : z_new = s.r * Real.cos s.theta := (by simp [z_new, Spherical.z]; rfl)
      simp [h_x_formula, h_y_formula, h_z_formula, s.r_zero_bound h_r]
      simp [r_zero_then_Vec3_zero r x_og y_og z_og h_r_def, h_r, r]

    simpa using equal_Vec3s v_new v (by simp [h_coords_unchanged.1, x_og, x_new]) (by simp [h_coords_unchanged.2, y_og, y_new]) (by simp [h_coords_unchanged.2.2, z_og, z_new])

  · let v_new := toVec3 s
    let x_new := Spherical.x v_new
    let y_new := Spherical.y v_new
    let z_new := Spherical.z v_new

    have h_r_non_zero : √(x v * x v + y v * y v + z v * z v) ≠ 0 := by
      simpa [h_r_def] using h_r
    have h_theta_def : s.theta = Real.arccos (z_og / r) := by
      simp [s, Vec3.toSpherical, x_og, y_og, z_og, h_r_non_zero, h_r_def]
    have h_phi_def : s.phi = atan2 y_og x_og := by
      simp [s, Vec3.toSpherical, x_og, y_og, h_r_non_zero]

    have h_term_one_max : y_og ≠ 0 ∨ x_og ≠ 0 → z_og^2 / (x_og^2 + y_og^2 + z_og^2) ≤ 1 := by
      intro h_non_empty
      rw [div_le_one, add_comm, ← sub_nonneg, add_comm, add_sub_assoc]
      simp
      nlinarith
      cases h_non_empty with
      | inr h_y => nlinarith [h_y, sq_pos_iff.mpr h_y]
      | inl h_x => nlinarith [h_x, sq_pos_iff.mpr h_x]

    let large_term := √(x_og ^ 2 + y_og ^ 2 + z_og ^ 2) * (√(1 - z_og ^ 2 / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) / √(x_og ^ 2 + y_og ^ 2))
    have h_large_term_one : x_og ≠ 0 ∨ y_og ≠ 0 → large_term = 1 := by
      intro h_xy
      subst large_term
      rw [← sqrt_div, ← sqrt_mul]
      have h_one_merge : (1 - z_og ^ 2 / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) = ((x_og ^ 2 + y_og ^ 2) / (x_og ^ 2 + y_og ^ 2 + z_og ^ 2)) := by grind
      rw [h_one_merge]
      have h_non_zero_duo : (x_og ^ 2 + y_og ^ 2) ≠ 0 := by
        have h_g_zero : y_og ^ 2 + x_og ^ 2 > 0 := pos_square_sum x_og y_og h_xy
        nlinarith [h_g_zero]
      grind
      nlinarith
      grind

    have h_x : x_new = x_og := by
      have h_x_formula : x_new = s.r * Real.sin s.theta * Real.cos s.phi := by (simp [x_new, Spherical.x]; rfl)
      simp [h_x_formula, h_theta_def, h_phi_def]
      simp [Real.sin_arccos, cos_atan2]
      grind

    have h_y : y_new = y_og := by
      have h_y_formula : y_new = s.r * Real.sin s.theta * Real.sin s.phi := by (simp [y_new, Spherical.y]; rfl)
      simp [h_y_formula, h_theta_def, h_phi_def]
      simp [Real.sin_arccos, sin_atan2]
      grind

    have h_z : z_new = z_og := by
      have h_z_formula : z_new = s.r * Real.cos s.theta := (by simp [z_new, Spherical.z]; rfl)
      simp [h_z_formula, h_theta_def]
      have h_abs_z_over_r_bounds : abs (z_og / r) ≤ 1 := abs_z_over_r_bounds x_og y_og z_og r (by simp [h_r_def, pow_two]) h_r
      simp [Real.cos_arccos, h_abs_z_over_r_bounds, abs_le.mp, r] -- |z / r| < 1 thingy
      field_simp [h_r, r]

    simpa using equal_Vec3s v_new v (by simp [h_x, x_og, x_new]) (by simp [h_y, y_og, y_new]) (by simp [h_z, z_og, z_new])

lemma r_new_def (v : Vec3) : (Vec3.toSpherical v).r = √(Spherical.x v * Spherical.x v + Spherical.y v * Spherical.y v + Spherical.z v * Spherical.z v) := by
  simp [Vec3.toSpherical]
  by_cases h_r_zero : √(Spherical.x v * Spherical.x v + Spherical.y v * Spherical.y v + Spherical.z v * Spherical.z v) = 0
  · simp [h_r_zero]
  · simp [h_r_zero]

lemma sin_zero_eq_zero_pi_left (x : ℝ) : x = 0 ∨ x = Real.pi → sin x = 0 := by
  intro h_x_vals
  cases h_x_vals with
  | inl h_x_zero => rw [h_x_zero]; simp
  | inr h_x_pi => rw [h_x_pi]; simp

lemma sin_zero_eq_zero_pi_right (x : ℝ) (h_x_bounds : -Real.pi < x ∧ x ≤ Real.pi) : sin x = 0 → x = 0 ∨ x = Real.pi := by
  intro h_sin_x
  have h_npi := (Real.sin_eq_zero_iff).mp h_sin_x
  rcases h_npi with ⟨k, hk⟩
  rw [← hk]
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_k_lower_bound : (-1 : ℝ) < k := by nlinarith
  have h_k_upper_bound : (k : ℝ) ≤ 1 := by nlinarith

  have h_k_non_neg : 0 ≤ k := by
    norm_cast at h_k_lower_bound

  have h_k_le_one : k ≤ 1 := by
    norm_cast at h_k_upper_bound

  have h_k : k = 0 ∨ k = 1 := by
    interval_cases k
    norm_num
    simp

  interval_cases k <;> simp

lemma sin_zero_eq_zero_pi_iff (x : ℝ) (h_x_bounds : -Real.pi < x ∧ x ≤ Real.pi) : sin x = 0 ↔ x = 0 ∨ x = Real.pi := by
  exact Iff.intro (sin_zero_eq_zero_pi_right x h_x_bounds) (sin_zero_eq_zero_pi_left x)

lemma sin_theta_pos' (s : Spherical) : sin s.theta ≠ 0 → 0 < sin s.theta := by
  intro h_sin_theta

  have h_theta_not_zero_or_pi : ¬(s.theta = 0 ∨ s.theta = Real.pi) := by
    intro h_theta_zero_or_pi
    have h_sin_theta_zero : sin s.theta = 0 := by
      cases h_theta_zero_or_pi with
      | inl h_zero => simp [h_zero]
      | inr h_pi => simp [h_pi]
    exact (h_sin_theta h_sin_theta_zero).elim

  push_neg at h_theta_not_zero_or_pi
  have h_theta_bounds : 0 < s.theta ∧ s.theta < Real.pi := by
    simp [(lt_of_le_of_ne s.theta_bounds.1 h_theta_not_zero_or_pi.1.symm), (lt_of_le_of_ne s.theta_bounds.2 h_theta_not_zero_or_pi.2)]

  exact sin_pos_of_pos_of_lt_pi h_theta_bounds.1 h_theta_bounds.2

lemma toVec3_rightInverse_on_radial_distance
  (s_og : Spherical) (s_new : Spherical) (v : Vec3) (x y z : ℝ)
  (h_x : x = Spherical.x v) (h_x_def : x = s_og.r * Real.sin s_og.theta * Real.cos s_og.phi)
  (h_y : y = Spherical.y v) (h_y_def : y = s_og.r * Real.sin s_og.theta * Real.sin s_og.phi)
  (h_z : z = Spherical.z v) (h_z_def : z = s_og.r * Real.cos s_og.theta)
  (h_s_new : s_new = Vec3.toSpherical v) :
  s_og.r = s_new.r := by

    have h_r_new_def : s_new.r = √(Spherical.x v * Spherical.x v + Spherical.y v * Spherical.y v + Spherical.z v * Spherical.z v) := by
      rw [h_s_new]
      exact r_new_def v
    simp [h_r_new_def]

    by_cases h_r_zero : s_og.r = 0
    · grind
    · by_cases h_theta_values : s_og.theta = 0 ∨ s_og.theta = Real.pi
      · cases h_theta_values with
        | inl h_theta_zero =>
          rw [h_theta_zero] at h_z_def
          simp at h_z_def
          rw [← pow_two, ← pow_two, ← pow_two, ← h_x, ← h_y, ← h_z]
          rw [h_x_def, h_y_def, h_z_def]
          field_simp
          simp [h_theta_zero, sqrt_sq s_og.r_bounds]
        | inr h_theta_pi =>
          rw [h_theta_pi] at h_z_def
          simp at h_z_def
          rw [← pow_two, ← pow_two, ← pow_two, ← h_x, ← h_y, ← h_z]
          rw [h_x_def, h_y_def, h_z_def]
          field_simp
          simp [h_theta_pi, sqrt_sq s_og.r_bounds]
      · push_neg at h_theta_values
        have h_theta_restricted_bounds : 0 < s_og.theta ∧ s_og.theta < π := by
          constructor
          · exact lt_of_le_of_ne s_og.theta_bounds.1 (h_theta_values.1.symm)
          · exact lt_of_le_of_ne s_og.theta_bounds.2 (h_theta_values.2)
        have h_sin_theta_non_zero : 0 ≠ sin s_og.theta := by
            have h_sin_theta_pos : 0 < sin s_og.theta := by
              exact sin_pos_of_mem_Ioo (h_theta_restricted_bounds)
            exact ne_of_lt h_sin_theta_pos

        by_cases h_phi_values : s_og.phi = 0 ∨ s_og.phi = Real.pi
        · cases h_phi_values with
          | inl h_phi_zero =>
            rw [h_phi_zero] at h_x_def
            simp at h_x_def
            have h_x_non_zero : x ≠ 0 := by
              rw [h_x_def]
              exact mul_ne_zero h_r_zero h_sin_theta_non_zero.symm

            rw [← pow_two, ← pow_two, ← pow_two, ← h_x, ← h_y, ← h_z]
            rw [h_x_def, h_y_def, h_z_def]
            field_simp
            simp [h_phi_zero, sqrt_sq s_og.r_bounds]

          | inr h_phi_pi =>
            rw [h_phi_pi] at h_x_def
            simp at h_x_def
            have h_x_non_zero : x ≠ 0 := by
              rw [h_x_def, neg_ne_zero]
              exact mul_ne_zero h_r_zero h_sin_theta_non_zero.symm
            rw [← pow_two, ← pow_two, ← pow_two, ← h_x, ← h_y, ← h_z]
            rw [h_x_def, h_y_def, h_z_def]
            field_simp
            simp [h_phi_pi, sqrt_sq s_og.r_bounds]

        · push_neg at h_phi_values
          rw [← h_x, ← h_y, ← h_z]
          have h_sin_phi_non_zero : sin s_og.phi ≠ 0 := by
            have h_sin_phi_pos : sin s_og.phi = 0 ↔ s_og.phi = 0 := by
              exact sin_eq_zero_iff_of_lt_of_lt (s_og.phi_bounds.1) (lt_of_le_of_ne s_og.phi_bounds.2 h_phi_values.2)
            grind

          have h_y_non_zero : y ≠ 0 := by
            rw [h_y_def, mul_comm]
            exact mul_ne_zero h_sin_phi_non_zero (mul_ne_zero h_r_zero h_sin_theta_non_zero.symm)
          rw [← pow_two, ← pow_two, ← pow_two, h_x_def, h_y_def, h_z_def]
          field_simp
          simp [sqrt_sq s_og.r_bounds]

lemma toVec3_rightInverse_on_theta
  (s_og : Spherical) (s_new : Spherical) (v : Vec3) (z : ℝ)
  (h_z : z = Spherical.z v) (h_z_def : z = s_og.r * Real.cos s_og.theta)
  (h_s_new : s_new = Vec3.toSpherical v)
  (h_r_same : s_og.r = s_new.r) :
  s_og.theta = s_new.theta := by

    have h_r_new_def : v.toSpherical.r = √(Spherical.x v * Spherical.x v + Spherical.y v * Spherical.y v + Spherical.z v * Spherical.z v) := by
      exact r_new_def v

    by_cases h_r_zero : s_og.r = 0
    · have h_r_new_zero : s_new.r = 0 := by rw [← h_r_same, h_r_zero]
      rw [h_s_new]
      simp [Vec3.toSpherical]
      simp [← h_r_new_def, h_r_new_zero, ← h_s_new]
      exact (s_og.r_zero_bound (by simp [h_r_zero])).1
    · push_neg at h_r_zero
      have h_r_new_non_zero : s_new.r ≠ 0 := (by rw [← h_r_same]; simp [h_r_zero])
      rw [h_s_new]
      simp [Vec3.toSpherical]
      simp [h_r_new_non_zero, ← h_r_new_def, ← h_s_new]
      simp [h_z_def, ← h_z, h_r_same]
      field_simp [h_r_zero]
      exact (arccos_cos (s_og.theta_bounds.1) (s_og.theta_bounds.2)).symm

lemma toVec3_rightInverse_on_phi
  (s_og : Spherical) (s_new : Spherical) (v : Vec3) (x y : ℝ)
  (h_x : x = Spherical.x v) (h_x_def : x = s_og.r * Real.sin s_og.theta * Real.cos s_og.phi)
  (h_y : y = Spherical.y v) (h_y_def : y = s_og.r * Real.sin s_og.theta * Real.sin s_og.phi)
  (h_s_new : s_new = Vec3.toSpherical v)
  (h_r_same : s_og.r = s_new.r)
  (h_phi_bounds : -Real.pi < s_og.phi ∧ s_og.phi ≤ Real.pi) :
  s_og.phi = s_new.phi := by

    have h_r_new_def : v.toSpherical.r = √(Spherical.x v * Spherical.x v + Spherical.y v * Spherical.y v + Spherical.z v * Spherical.z v) := by
      exact r_new_def v

    rw [h_s_new]
    simp [Vec3.toSpherical]
    by_cases h_r_zero : s_og.r = 0
    · have h_r_new_zero : s_new.r = 0 := by rw [← h_r_same, h_r_zero]
      simp [← h_r_new_def, h_r_new_zero, ← h_s_new]
      exact (s_og.r_zero_bound (by simp [h_r_zero])).2
    · push_neg at h_r_zero
      have h_r_new_non_zero : s_new.r ≠ 0 := by rw [← h_r_same]; exact h_r_zero
      have h_r_new_non_zero : s_new.r ≠ 0 := (by rw [← h_r_same]; simp [h_r_zero])
      simp [← h_r_new_def, atan2]

      by_cases h_atan2_case : Spherical.y v = 0 ∧ Spherical.x v < 0
      · simp [h_atan2_case]
        have h_phi_og_pi : s_og.phi = π := by
          by_cases h_sin_theta : sin s_og.theta = 0
          · have h_x_zero : Spherical.x v = 0 := by
              simp [h_x_def, h_sin_theta, ← h_x]
            linarith
          · push_neg at h_sin_theta
            have h_sin_phi_zero : sin s_og.phi = 0 := by grind
            have h_phi_zero_or_pi : s_og.phi = 0 ∨ s_og.phi = Real.pi := (sin_zero_eq_zero_pi_iff s_og.phi s_og.phi_bounds).mp h_sin_phi_zero

            have h_phi_non_zero : s_og.phi ≠ 0 := by
              have h_cos_phi_lt_zero : cos s_og.phi < 0 := by

                have h_x_def_lt_zero : s_og.r * sin s_og.theta * cos s_og.phi < 0 := by
                  rw [← h_x_def, h_x]
                  exact h_atan2_case.2
                have h_sin_theta_pos : 0 < sin s_og.theta := by
                  exact sin_theta_pos' s_og h_sin_theta

                rw [mul_comm] at h_x_def_lt_zero

                have h_product_pos : 0 < s_og.r * sin s_og.theta := by
                  simp [lt_of_le_of_ne s_og.r_bounds h_r_zero.symm, h_sin_theta_pos]
                nlinarith [h_product_pos, h_x_def_lt_zero]

              have h_phi_zero_case : s_og.phi = 0 → ¬(cos s_og.phi < 0) := by
                intro h_phi_zero
                simp [h_phi_zero]

              intro h_phi_zero
              exact (h_phi_zero_case h_phi_zero) h_cos_phi_lt_zero

            cases h_phi_zero_or_pi with
            | inl h_zero => exact (h_phi_non_zero h_zero).elim
            | inr h_pi => simp [h_pi]
        simp [← h_s_new, ← h_r_same, h_r_zero, h_phi_og_pi]
      · simp [h_atan2_case]
        simp [h_r_zero, ← h_s_new, ← h_r_same]
        simp [← h_x, h_x_def, ← h_y, h_y_def]
        field_simp
        rw [add_comm (cos s_og.phi ^ 2) (sin s_og.phi ^ 2), sin_sq_add_cos_sq s_og.phi]
        field_simp
        generalize h_u : s_og.r ^ 2 * sin s_og.theta ^ 2 = u
        have h_u_sq : u = (s_og.r * sin s_og.theta)^2 := by
          rw [← h_u]
          exact (mul_zpow s_og.r (sin s_og.theta) 2).symm
        rw [h_u_sq]

        by_cases h_theta_zero : s_og.theta = 0
        · simp [h_theta_zero]
          exact s_og.theta_zero_bound h_theta_zero
        · by_cases h_theta_pi : s_og.theta = Real.pi
          · simp [h_theta_pi]
            exact s_og.theta_pi_bound h_theta_pi
          · push_neg at h_theta_zero
            push_neg at h_theta_pi
            have h_theta_bounds : 0 < s_og.theta ∧ s_og.theta < Real.pi := by
              constructor
              · exact lt_of_le_of_ne s_og.theta_bounds.1 h_theta_zero.symm
              · exact lt_of_le_of_ne s_og.theta_bounds.2 h_theta_pi

            have h_sin_theta_pos : 0 < sin s_og.theta := by
              exact sin_pos_of_pos_of_lt_pi h_theta_bounds.1 h_theta_bounds.2

            have h_product_pos : 0 < s_og.r * sin s_og.theta := by
              simp [lt_of_le_of_ne s_og.r_bounds h_r_zero.symm, h_sin_theta_pos]

            have h_product_non_zero : 0 ≠ s_og.r * sin s_og.theta := by nlinarith [h_product_pos]

            simp [sqrt_sq (le_of_lt h_product_pos)]
            generalize h_u : s_og.r * sin s_og.theta = u

            rw [← mul_one_add u (cos s_og.phi)]
            field_simp [← h_u, h_product_non_zero]

            have h_phi_not_pi : s_og.phi ≠ Real.pi := by
              intro h_phi_pi
              have h_y_zero : y = 0 := by simp [h_y_def, h_phi_pi]
              have h_x_lt_zero : x < 0 := by
                rw [h_x_def, mul_comm]
                simp [h_phi_pi, h_product_pos]
              grind

            have h_phi_restrictive_bounds : -π < s_og.phi ∧ s_og.phi < π := by
              constructor
              · simp [h_phi_bounds]
              · exact lt_of_le_of_ne h_phi_bounds.2 h_phi_not_pi

            have h_phi_two : s_og.phi = (2 * (s_og.phi / 2)) := by grind

            have h_half_phi_bounds : -π / 2 < s_og.phi / 2 ∧ s_og.phi / 2 < π / 2 := by
              constructor
              · simp [div_lt_div_of_pos_right h_phi_restrictive_bounds.1]
              · simp [div_lt_div_of_pos_right h_phi_restrictive_bounds.2]
            have h_half_phi_Ioo : (s_og.phi / 2) ∈ Set.Ioo (-(π / 2)) (π / 2) := by grind

            have h_cos_half_non_zero : cos (s_og.phi / 2) ≠ 0 := by
              simp [ne_of_gt (cos_pos_of_mem_Ioo h_half_phi_Ioo)]

            rw [h_phi_two, cos_two_mul, sin_two_mul]
            simp
            field_simp [h_cos_half_non_zero]
            rw [← tan_eq_sin_div_cos, arctan_tan (by nlinarith [h_half_phi_bounds.1]) h_half_phi_bounds.2]
            field_simp

theorem toVec3_rightInverse : Function.RightInverse toVec3 Vec3.toSpherical := by
  intro s_og
  let r_og := s_og.r
  let theta_og := s_og.theta
  let phi_og := s_og.phi

  let v := s_og.toVec3
  let x := Spherical.x v
  let y := Spherical.y v
  let z := Spherical.z v

  have h_x_def : x = r_og * Real.sin theta_og * Real.cos phi_og := by
    simp [x, toVec3, v, Spherical.x, r_og, theta_og, phi_og]
  have h_y_def : y = r_og * Real.sin theta_og * Real.sin phi_og := by
    simp [y, toVec3, v, Spherical.y, r_og, theta_og, phi_og]
  have h_z_def : z = r_og * Real.cos theta_og := by
    simp [z, toVec3, v, Spherical.z, r_og, theta_og]

  let s_new := v.toSpherical
  let r_new := s_new.r
  let theta_new := s_new.theta
  let phi_new := s_new.phi
  have h_r_new_def : r_new = √(Spherical.x v * Spherical.x v + Spherical.y v * Spherical.y v + Spherical.z v * Spherical.z v) := by
    exact r_new_def v

  have h_r_same : r_og = r_new := by
    simpa using toVec3_rightInverse_on_radial_distance s_og s_new v x y z rfl rfl rfl rfl rfl rfl rfl

  have h_theta_same : theta_og = theta_new := by
    exact toVec3_rightInverse_on_theta s_og s_new v z rfl rfl rfl h_r_same

  have h_phi_bounds : -Real.pi < phi_og ∧ phi_og ≤ Real.pi := s_og.phi_bounds

  have h_phi_same : phi_og = phi_new := by
    exact toVec3_rightInverse_on_phi s_og s_new v x y rfl rfl rfl rfl rfl h_r_same h_phi_bounds

  change s_new = s_og
  cases s_og

  simp [s_new, r_og, r_new, theta_og, theta_new, phi_og, phi_new] at h_r_same h_theta_same h_phi_same ⊢
  simp [h_r_same, h_theta_same, h_phi_same]

theorem toVec3_inverse_Vec3.toSpherical :
  Function.LeftInverse toVec3 Vec3.toSpherical ∧ Function.RightInverse toVec3 Vec3.toSpherical := by
    constructor
    · exact toVec3_leftInverse
    · exact toVec3_rightInverse

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

noncomputable def x_hat : Vec3 := ⟨![1,0,0]⟩
noncomputable def y_hat : Vec3 := ⟨![0,1,0]⟩
noncomputable def z_hat : Vec3 := ⟨![0,0,1]⟩

noncomputable def r_hat (s : Spherical) : Vec3 :=
  ⟨![
    sin s.theta * cos s.phi,
    sin s.theta * sin s.phi,
    cos s.theta
  ]⟩

noncomputable def theta_hat (s : Spherical) : Vec3 :=
  ⟨![
    cos s.theta * cos s.phi,
    cos s.theta * sin s.phi,
    -sin s.theta
  ]⟩

noncomputable def phi_hat (s : Spherical) : Vec3 :=
  ⟨![
    -sin s.phi,
    cos s.phi,
    0
  ]⟩

noncomputable def Vec3_to_radial_distance (v : Vec3) : ℝ :=
  (Vec3.toSpherical v).r

theorem r_on_toSpherical: (r ∘ Vec3.toSpherical) = fun v => √((x v)^2 + (y v)^2 + (z v)^2) := by
  funext v
  let r_temp := √((x v)^2 + (y v)^2 + (z v)^2)
  by_cases r_temp = 0
  · simp [Vec3.toSpherical, ← pow_two]
    grind
  · simp [Vec3.toSpherical, ← pow_two]
    grind


theorem phi_on_toSpherical : (phi ∘ Vec3.toSpherical) = fun v => atan2 (y v) (x v) := by
  funext v
  simp [Vec3.toSpherical]
  let r_temp := √((x v)^2 + (y v)^2 + (z v)^2)
  by_cases h_r : √((x v)^2 + (y v)^2 + (z v)^2) = 0
  · simp [h_r, ← pow_two]
    rw [atan2]
    have h_xyz : x v = 0 ∧ y v = 0 ∧ z v = 0 := by
      apply r_zero_then_Vec3_zero r_temp (x v) (y v) (z v)
      simp [r_temp, ← pow_two, h_r]
      grind
    simp [h_xyz]
  · simp [← pow_two, h_r]

open Space

lemma x_space_def (v : Vec3) : x v = (v.val 0) := by rfl
lemma y_space_def (v : Vec3) : y v = (v.val 1) := by rfl
lemma z_space_def (v : Vec3) : z v = (v.val 2) := by rfl

lemma x_func : x = fun v => v 0 := rfl
lemma y_func : y = fun v => v 1 := rfl
lemma z_func : z = fun v => v 2 := rfl

lemma x_clm : x = Space.coordCLM 0 := by
    ext i
    simp [coordCLM, coord_apply, x]
lemma y_clm : y = Space.coordCLM 1 := by
    ext i
    simp [coordCLM, coord_apply, y]
lemma z_clm : z = Space.coordCLM 2 := by
    ext i
    simp [coordCLM, coord_apply, z]

theorem spherical_r_dx (v : Vec3) (h_v_non_zero : v ≠ 0) : ∂[0] (r ∘ Vec3.toSpherical) v = (x v) / √((x v)^2 + (y v)^2 + (z v)^2) := by
  rw [r_on_toSpherical]
  simp [sqrt_eq_rpow]
  simp [Space.deriv]
  generalize h_u : (2⁻¹ : ℝ)  = u

  have h_xyz : x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0 := by
    exact Vec3_non_empty v h_v_non_zero
  have h_sum_nonzero := sum_triple_sq_non_zero (x v) (y v) (z v) h_xyz
  have h_sq_sum_ge_zero : 0 ≤ (x v)^2 + (y v)^2 + (z v)^2 := by nlinarith
  have h_sqrt_sum_nonzero : √((x v)^2 + (y v)^2 + (z v)^2) ≠ 0 :=  by
    apply (sqrt_ne_zero h_sq_sum_ge_zero).mpr
    exact sum_triple_sq_non_zero (x v) (y v) (z v) h_xyz

  have h_s :
    (fun v => (x v ^ 2 + y v ^ 2 + z v ^ 2) ^ u) = (fun w => w ^ u) ∘ (fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) := by
      rfl

  rw [h_s]

  have h_fderiv_diffAt_1 : DifferentiableAt ℝ (fun w => w ^ u) ((fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) v) := by
    rw [x_clm, y_clm, z_clm]
    simp
    have h_non_zero : (coordCLM 0 v)^2 + (coordCLM 1 v)^2 + (coordCLM 2 v)^2 ≠ 0 := by
      rw [← x_clm, ← y_clm, ← z_clm]
      grind [sq_pos_of_ne_zero]
    simp [h_non_zero]

  have h_fderiv_diffAt_2 : DifferentiableAt ℝ (fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) v := by
    rw [x_clm, y_clm, z_clm]
    simp

  rw [fderiv_comp (g := fun w : ℝ => w ^ u) (f := fun v : Vec3 => x v ^ 2 + y v ^ 2 + z v ^ 2) (x := v) h_fderiv_diffAt_1 h_fderiv_diffAt_2]
  simp [ContinuousLinearMap.comp_apply]
  have h_deriv : (fderiv ℝ (fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) v) (basis 0) = 2 * x v := by
    change (fderiv ℝ ((fun v => x v ^ 2) + (fun v => y v ^ 2) + (fun v => z v ^ 2)) v) (basis 0) = 2 * x v
    rw [fderiv_add, fderiv_add]
    rw [fderiv_pow, fderiv_pow, fderiv_pow]
    simp [← deriv_eq_fderiv_basis]

    rw [x_func, y_func, z_func, Space.deriv_component 0 0 v, Space.deriv_component 1 0 v, Space.deriv_component 2 0 v]
    simp

    · rw [z_clm]
      fun_prop
    · rw [y_clm]
      fun_prop
    · rw [x_clm]
      fun_prop
    · rw [x_clm]
      fun_prop
    · rw [y_clm]
      fun_prop
    · rw [x_clm, y_clm]
      fun_prop
    · rw [z_clm]
      fun_prop

  simp [h_deriv]

  simp [h_sum_nonzero]
  rw [← h_u]
  norm_num
  rw [rpow_neg, ← sqrt_eq_rpow]
  simp [← div_eq_inv_mul]
  grind
  grind

lemma atan2_interior_dx (v : Vec3) (h_y_non_zero : y v ≠ 0) : (fderiv ℝ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) v) (basis 0) = - (y v) / (√((x v)^2 + (y v)^2) * (√((x v)^2 + (y v)^2) + (x v))) := by
  have h_inverse : (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) = (fun v => y v * (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) := by
    rfl
  simp [h_inverse]
  have h_split_f_mul : (fun v => y v * (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) = ((fun v => y v) * fun v => (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) := by
    funext v
    rfl
  rw [h_split_f_mul]

  have h_sum_non_zero : x v ^ 2 + y v ^ 2 ≠ 0 := by
    have h_y_pos : 0 < (y v) ^ 2 := by
      apply sq_pos_of_ne_zero
      simp [h_y_non_zero]
    have h_x_nonneg : 0 ≤ x v ^ 2 := by nlinarith
    nlinarith [h_y_pos, h_y_non_zero]
  have h_sum_sq_non_zero : √(x v ^ 2 + y v ^ 2) ≠ 0 := by
    rw [sqrt_ne_zero]
    exact h_sum_non_zero
    nlinarith
  have h_clm_non_zero : (coordCLM 0) v ^ 2 + (coordCLM 1) v ^ 2 ≠ 0 := by
    rw [← x_clm, ← y_clm]
    grind
  have h_denom_pos : 0 < √((x v)^2 + (y v)^2) + (x v) := by exact sqrt_x2_y2_add_x_ne_zero (x := x v) (y := y v) (by apply lt_of_le_of_ne; nlinarith; exact h_sum_non_zero.symm) (by right; exact h_y_non_zero)
  have h_denom_non_zero : 0 ≠ √((x v)^2 + (y v)^2) + (x v) := by nlinarith [h_denom_pos]

  rw [fderiv_mul (𝕜 := ℝ) (c := fun v => y v) (d := fun v => (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) (x := v) (by rw [y_clm]; fun_prop)
      (by rw [x_clm, y_clm]; apply DifferentiableAt.inv; simp; apply DifferentiableAt.sqrt; apply DifferentiableAt.add; simp; apply DifferentiableAt.pow; simp; exact h_clm_non_zero; rw [← x_clm, ← y_clm]; exact h_denom_non_zero.symm)]

  have h_deriv_1 : fderiv ℝ (fun v => y v) v (basis 0) = 0 := by
    rw [← deriv_eq_fderiv_basis, y_func, Space.deriv_component 1 0 v]
    simp

  have h_deriv_2 : fderiv ℝ (fun v => (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) v (basis 0) = - 1 / ((√((x v)^2 + (y v)^2)) * (√((x v)^2 + (y v)^2) + (x v))) := by
    have h_inv_sub : (fun v => (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) = (fun w => w⁻¹) ∘ (fun v => √(x v ^ 2 + y v ^ 2) + x v) := by
      rfl
    rw [h_inv_sub]
    rw [fderiv_comp (𝕜 := ℝ)]
    rw [fderiv_inv]
    simp
    have h_deriv_2_sub : fderiv ℝ (fun v => √(x v ^ 2 + y v ^ 2) + x v) v (basis 0) = ((x v) + √((x v)^2 + (y v)^2)) / (√((x v)^2 + (y v)^2)) := by
      have h_fun_sum : (fun v => √(x v ^ 2 + y v ^ 2) + x v) = (fun v => √(x v ^ 2 + y v ^ 2)) + (fun v => x v) := by rfl
      rw [h_fun_sum]
      rw [fderiv_add (𝕜 := ℝ) (f := fun v => √(x v ^ 2 + y v ^ 2)) (g := fun v => x v) (x := v) (by rw [x_clm, y_clm]; apply DifferentiableAt.sqrt; apply DifferentiableAt.add; apply DifferentiableAt.pow; simp; apply DifferentiableAt.pow; simp; exact h_clm_non_zero) (by rw [x_clm]; fun_prop)]
      simp
      have h_deriv_2_sub_a : (fderiv ℝ (fun v => x v)) v (basis 0) = 1 := by
        rw [← deriv_eq_fderiv_basis, x_func, Space.deriv_component 0 0 v]
        simp
      have h_deriv_2_sub_b : (fderiv ℝ (fun v => √(x v ^ 2 + y v ^ 2))) v (basis 0) = (x v) / √((x v)^2 + (y v)^2) := by
        have h_fun_split : (fun v => √(x v ^ 2 + y v ^ 2)) = (fun w => √(w)) ∘ (fun v => (x v)^2 + (y v)^2) := by
          rfl
        simp [h_fun_split]
        rw [fderiv_comp (𝕜 := ℝ)]
        have h_diff_1 : (fderiv ℝ (fun v => x v ^ 2 + y v ^ 2)) v (basis 0) = 2 * (x v) := by
          have h_fun_sum_2 : (fun v => x v ^ 2 + y v ^ 2) = (fun v => x v ^ 2) + (fun v => y v ^ 2) := by rfl
          rw [h_fun_sum_2, fderiv_add (𝕜 := ℝ)]
          have h_diff_1a : (fderiv ℝ (fun v => x v ^ 2)) v (basis 0) = 2 * x v := by
            rw [x_clm]
            simp [fderiv_pow 2]
            rw [← x_clm, x_func]
            simp
          have h_diff_1b : (fderiv ℝ (fun v => y v ^ 2)) v (basis 0) = 0 := by
            rw [y_clm]
            simp [fderiv_pow 2]
            rw [← y_clm, y_func]
            simp
            right
            rw [← y_space_def, y_func]
            simp [basis]
            rfl
          simp [h_diff_1a, h_diff_1b]
          · rw [x_clm]
            fun_prop
          · rw [y_clm]
            fun_prop

        simp [h_diff_1, sqrt_eq_rpow, h_sum_non_zero]
        rw [← one_div, ← sqrt_eq_rpow]
        norm_num
        rw [rpow_neg, ← one_div, ← sqrt_eq_rpow]
        grind
        nlinarith
        · rw [x_clm, y_clm]
          have h_sub_diff : DifferentiableAt ℝ (fun w => w) ((coordCLM 0) v ^ 2 + (coordCLM 1) v ^ 2) := by
            fun_prop
          exact DifferentiableAt.sqrt h_sub_diff h_clm_non_zero
        · rw [x_clm, y_clm]
          fun_prop

      simp [h_deriv_2_sub_a, h_deriv_2_sub_b]
      grind

    simp [h_deriv_2_sub]
    rw [← one_div]

    grind
    · rw [x_clm, y_clm]
      have h_sub_diff : DifferentiableAt ℝ (fun w => w) (√((coordCLM 0) v ^ 2 + (coordCLM 1) v ^ 2) + (coordCLM 0) v) := by
        fun_prop
      exact DifferentiableAt.inv h_sub_diff (by rw [← x_clm, ← y_clm]; exact h_denom_non_zero.symm)
    · rw [x_clm, y_clm]
      simp
      apply DifferentiableAt.sqrt
      fun_prop
      exact h_clm_non_zero

  simp [h_deriv_1, h_deriv_2]
  grind

theorem atan2_case_dx (v : Vec3) (h_y_non_zero : y v ≠ 0) : ∂[0] (fun v => 2 * Real.arctan (y v / (Real.sqrt ((x v)^2 + (y v)^2) + (x v)))) v = - (y v) / ((x v)^2 + (y v)^2) := by
  rw [Space.deriv]
  have h_s :
    (fun v => 2 * arctan (y v / (√(x v ^ 2 + y v ^ 2) + x v))) = (fun w => 2 * arctan w ) ∘ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) := by
      rfl

  simp [h_s]

  have h_sum_non_zero : x v ^ 2 + y v ^ 2 ≠ 0 := by
      have h_y_pos : 0 < (y v) ^ 2 := by
        apply sq_pos_of_ne_zero
        simp [h_y_non_zero]
      have h_x_nonneg : 0 ≤ x v ^ 2 := by nlinarith
      nlinarith [h_y_pos, h_y_non_zero]
  have h_sum_sq_non_zero : √(x v ^ 2 + y v ^ 2) ≠ 0 := by
    rw [sqrt_ne_zero]
    exact h_sum_non_zero
    nlinarith
  have h_denom_pos : 0 < √((x v)^2 + (y v)^2) + (x v) := by exact sqrt_x2_y2_add_x_ne_zero (x := x v) (y := y v) (by apply lt_of_le_of_ne; nlinarith; exact h_sum_non_zero.symm) (by right; exact h_y_non_zero)
  have h_denom_non_zero : 0 ≠ √((x v)^2 + (y v)^2) + (x v) := by nlinarith [h_denom_pos]

  have h_clm_non_zero : (coordCLM 0) v ^ 2 + (coordCLM 1) v ^ 2 ≠ 0 := by
    rw [← x_clm, ← y_clm]
    grind

  have h_diffAt_one : DifferentiableAt ℝ (fun w => 2 * arctan w) ((fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) v) := by
    simp
    rw [x_clm, y_clm]
    refine
      DifferentiableAt.fun_comp'
        ((coordCLM 1) v / (√((coordCLM 0) v ^ 2 + (coordCLM 1) v ^ 2) + (coordCLM 0) v)) ?_ ?_
    fun_prop
    apply DifferentiableAt.arctan
    fun_prop

  have h_diffAt_two :  DifferentiableAt ℝ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) v := by
    rw [x_clm, y_clm]
    refine DifferentiableAt.fun_mul ?_ ?_
    simp
    apply DifferentiableAt.inv
    simp
    apply DifferentiableAt.sqrt
    apply DifferentiableAt.add
    fun_prop
    fun_prop
    exact h_clm_non_zero
    rw [← x_clm, ← y_clm]
    exact h_denom_non_zero.symm

  rw [fderiv_comp (g := fun w : ℝ => 2 * arctan w) (f := fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) (x := v) h_diffAt_one h_diffAt_two]
  simp [ContinuousLinearMap.comp_apply]

  have h_fderiv : (fderiv ℝ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) v) (basis 0) = - (y v) / (√((x v)^2 + (y v)^2) * (√((x v)^2 + (y v)^2) + (x v))) := by exact atan2_interior_dx v h_y_non_zero
  simp [h_fderiv]
  rw [← one_div]

  generalize h_u : √(x v ^ 2 + y v ^ 2) = u
  have h_identity : 1 + (y v / (u + x v))^2 = 2 * u / (u + x v) := by
    rw [div_pow]
    nth_rw 2 [pow_two]
    rw [← one_div_mul_eq_div]
    field_simp
    rw [← div_self (a := (u + x v) ^ 2), ← add_div]
    apply eq_div_of_mul_eq
    grind
    rw [pow_two]
    field_simp
    rw [← h_u]
    field_simp
    grind
    grind

  grind

theorem spherical_phi_dx (v : Vec3) (h_v_non_zero : v ≠ 0) (h_y_non_zero : y v ≠ 0) : ∂[0] (phi ∘ Vec3.toSpherical) v = -(y v) / ((x v)^2 + (y v)^2) := by
  simp [Space.deriv, phi_on_toSpherical, atan2]

  have h_xyz : x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0 := by
    exact Vec3_non_empty v h_v_non_zero

  have h_atan2_case : ¬(y v = 0 ∧ x v < 0) := by simp [h_y_non_zero]

  sorry



end Spherical
end PhysLean.Mathematics.SphericalCoordinates
