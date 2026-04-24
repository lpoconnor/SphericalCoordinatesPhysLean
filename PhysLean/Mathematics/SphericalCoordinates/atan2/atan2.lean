/-
Copyright (c) 2025-2026 Liam O'Connor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liam O'Connor
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-
  This file contains:
  -atan2 definition
  -sin and cos identities on atan2
-/

open Mathlib
open Real
open Fin


lemma neg_div_sqrt_sq (x : ℝ) (h_x : x < 0) : x / Real.sqrt (x^2) = -1 := by
  rw [Real.sqrt_sq_eq_abs x]
  rw [abs_of_neg h_x]
  field_simp [h_x, ne_of_lt]

lemma pos_square_sum (y x : ℝ) (h_not_both_zero : y ≠ 0 ∨ x ≠ 0) :
  0 < x^2 + y^2 := by
    by_cases h_x_non_zero : x ≠ 0
    · nlinarith [sq_pos_of_ne_zero h_x_non_zero]
    · simp [h_x_non_zero] at h_not_both_zero
      push_neg at h_not_both_zero
      nlinarith [h_not_both_zero, sq_pos_of_ne_zero h_not_both_zero]

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

noncomputable def atan2 (y x : ℝ) : ℝ :=
  if y = 0 ∧ x < 0 then
    Real.pi
  else
    2 * arctan (y / (Real.sqrt (x^2 + y^2) + x))

lemma atan2_empty_zero : atan2 0 0 = 0 := by
  simp only [atan2, lt_self_iff_false, and_false, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, sqrt_zero, div_zero, arctan_zero, mul_zero]

theorem atan2_lower_bound (y x : ℝ) : -Real.pi < atan2 y x := by
  by_cases h : y = 0 ∧ x < 0
  · simp [atan2, h]
    linarith [Real.pi_pos]
  · simp [atan2, h]
    generalize y / (Real.sqrt (x^2 + y^2) + x) = u
    linarith [Real.neg_pi_div_two_lt_arctan u]

theorem atan2_upper_bound (y x : ℝ) : atan2 y x ≤ Real.pi := by
  by_cases h : y = 0 ∧ x < 0
  · simp [atan2, h]
  · simp [atan2, h]
    generalize y / (√(x^2 + y^2) + x) = u
    linarith [arctan_lt_pi_div_two u]

theorem atan2_bounds (y x : ℝ) :
  -Real.pi < atan2 y x ∧ atan2 y x ≤ Real.pi := by
  exact ⟨atan2_lower_bound y x, atan2_upper_bound y x⟩

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
