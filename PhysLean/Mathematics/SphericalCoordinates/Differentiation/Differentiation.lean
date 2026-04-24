/-
Copyright (c) 2025-2026 Liam O'Connor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liam O'Connor
-/

import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.TODO.Basic
import PhysLean.SpaceAndTime.Space.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.LinearCombination'
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.Module.LinearMap
import PhysLean.Mathematics.SphericalCoordinates.SphericalCoords

/-
  This file contains:
  -Derivatives: dr/dx, dtheta/dx, dphi/dx, same for y and z
-/

open Mathlib
open Real
open Fin
open PhysLean.Mathematics.SphericalCoordinates.Spherical

namespace PhysLean.Mathematics.SphericalCoordinates.Differentiation


theorem r_on_toSpherical: (r ∘ Vec3.toSpherical) = fun v => √((x v)^2 + (y v)^2 + (z v)^2) := by
  funext v
  let r_temp := √((x v)^2 + (y v)^2 + (z v)^2)
  by_cases r_temp = 0
  · simp [Vec3.toSpherical, ← pow_two]
    grind
  · simp [Vec3.toSpherical, ← pow_two]
    grind

theorem theta_on_toSpherical (v : Vec3) (h_v_non_zero : v ≠ 0) : (theta ∘ Vec3.toSpherical) v = (fun v => (arccos ((z v) / √((x v)^2 + (y v)^2 + (z v)^2)))) v := by
  have h_xyz : x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0 := by
    exact Vec3_non_empty v h_v_non_zero

  simp [Vec3.toSpherical, ← pow_two, r_non_zero (x v) (y v) (z v) h_xyz]

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

theorem spherical_r_deriv_general (k : Fin 3) (v : Vec3) (h_v_non_zero : v ≠ 0) : ∂[k] (r ∘ Vec3.toSpherical) v = (coordCLM k v) / √((x v)^2 + (y v)^2 + (z v)^2) := by
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

  have h_split :
    (fun v => (x v ^ 2 + y v ^ 2 + z v ^ 2) ^ u) = (fun w => w ^ u) ∘ (fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) := by
      rfl

  rw [h_split]

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
  have h_deriv : (fderiv ℝ (fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) v) (basis k) = 2 * (Space.coordCLM k v) := by
    change (fderiv ℝ ((fun v => x v ^ 2) + (fun v => y v ^ 2) + (fun v => z v ^ 2)) v) (basis k) = 2 * (Space.coordCLM k v)
    rw [fderiv_add, fderiv_add]
    rw [fderiv_pow, fderiv_pow, fderiv_pow]
    simp [← deriv_eq_fderiv_basis]
    rw [x_func, y_func, z_func, Space.deriv_component 0 k v, Space.deriv_component 1 k v, Space.deriv_component 2 k v]
    simp
    by_cases h_k : k = 0
    · simp [h_k]
      rw [← x_clm, x_space_def]
    · by_cases h_k_sub : k = 1
      · simp [h_k_sub]
        rw [← y_clm, y_space_def]
      · have h_k_2 : k = 2 := by
          grind
        simp [h_k_2]
        rw [← z_clm, z_space_def]

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
  by_cases h_k : k = 0
  · simp [h_k, ← x_clm]
    grind
  · by_cases h_k_sub : k = 1
    · simp [h_k_sub, ← y_clm]
      grind
    · have h_k_2 : k = 2 := by
        grind
      simp [h_k_2, ← z_clm]
      grind
  grind


theorem spherical_r_dx (v : Vec3) (h_v_non_zero : v ≠ 0) : ∂[0] (r ∘ Vec3.toSpherical) v = (x v) / √((x v)^2 + (y v)^2 + (z v)^2) := by
  nth_rw 1 [x_clm]
  exact spherical_r_deriv_general 0 v h_v_non_zero

theorem spherical_r_dy (v : Vec3) (h_v_non_zero : v ≠ 0) : ∂[1] (r ∘ Vec3.toSpherical) v = (y v) / √((x v)^2 + (y v)^2 + (z v)^2) := by
  nth_rw 1 [y_clm]
  exact spherical_r_deriv_general 1 v h_v_non_zero

theorem spherical_r_dz (v : Vec3) (h_v_non_zero : v ≠ 0) : ∂[2] (r ∘ Vec3.toSpherical) v = (z v) / √((x v)^2 + (y v)^2 + (z v)^2) := by
  nth_rw 1 [z_clm]
  exact spherical_r_deriv_general 2 v h_v_non_zero


open Topology

theorem spherical_theta_neighbourhood (h_xyz : x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0) : (theta ∘ Vec3.toSpherical) =ᶠ[𝓝 v] (fun v => arccos (z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2))) := by
  let s : Set Vec3 := {u | x u ≠ 0 ∨ y u ≠ 0 ∨ z u ≠ 0}
  let s_sub_x : Set Vec3 := {u | x u ≠ 0}
  let s_sub_y : Set Vec3 := {u | y u ≠ 0}
  let s_sub_z : Set Vec3 := {u | z u ≠ 0}
  have h_s_neighbourhood : s ∈ 𝓝 v := by
    by_cases h_x : x v ≠ 0
    · have h_x_continuousAt : ContinuousAt x v := by
        rw [x_func]
        fun_prop
      have h_neighbourhood_condition : ∀ᶠ u in 𝓝 v, x u ≠ 0 := by
        (expose_names; exact ContinuousAt.eventually_ne h_x_continuousAt h_x)
      have h_s_small_neighbourhood : s_sub_x ∈ 𝓝 v := by
        exact h_neighbourhood_condition
      have s_sub_x_subset_s : s_sub_x ⊆ s :=
        fun u hu => Or.inl hu
      exact Filter.mem_of_superset h_neighbourhood_condition s_sub_x_subset_s
    · by_cases h_y : y v ≠ 0
      · have h_y_continuousAt : ContinuousAt y v := by
          rw [y_func]
          fun_prop
        have h_neighbourhood_condition : ∀ᶠ u in 𝓝 v, y u ≠ 0 := by
          (expose_names; exact ContinuousAt.eventually_ne h_y_continuousAt h_y)
        have h_s_small_neighbourhood : s_sub_y ∈ 𝓝 v := by
          exact h_neighbourhood_condition
        have s_sub_y_subset_s : s_sub_y ⊆ s :=
          fun u hu => Or.inr (Or.inl hu)
        exact Filter.mem_of_superset h_neighbourhood_condition s_sub_y_subset_s
      · have h_z : z v ≠ 0 := by simp [h_x, h_y] at h_xyz; push_neg at h_xyz; exact h_xyz
        have h_z_continuousAt : ContinuousAt z v := by
          rw [z_func]
          fun_prop
        have h_neighbourhood_condition : ∀ᶠ u in 𝓝 v, z u ≠ 0 := by
          (expose_names; exact ContinuousAt.eventually_ne h_z_continuousAt h_z)
        have h_s_small_neighbourhood : s_sub_z ∈ 𝓝 v := by
          exact h_neighbourhood_condition
        have s_sub_z_subset_s : s_sub_z ⊆ s :=
          fun u hu => Or.inr (Or.inr hu)
        exact Filter.mem_of_superset h_neighbourhood_condition s_sub_z_subset_s
  have h_eq_on_s : Set.EqOn
    (theta ∘ Vec3.toSpherical)
    (fun v => arccos (z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)))
    s := by
      intro t h_t
      rw [theta_on_toSpherical]
      simp [s] at h_t
      exact Vec3_non_empty' t h_t

  exact Filter.eventuallyEq_of_mem h_s_neighbourhood h_eq_on_s

theorem spherical_theta_function_special_differential_case (v : Vec3) (k : ℝ) (h_k : k = 1 ∨ k = -1) (h_xy : x v ≠ 0 ∨ y v ≠ 0) (h_r_non_zero : √(x v ^ 2 + y v ^ 2 + z v ^ 2) ≠ 0) : (fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) v ≠ k := by
  field_simp
  rw [Ne, div_eq_iff]
  intro h_z
  have h_sq_equal : z v ^ 2 = x v ^ 2 + y v ^ 2 + z v ^ 2 := by
    simp [pow_two]
    grind [sq_sqrt, pow_two]
  simp at h_sq_equal
  cases h_xy with
  | inl h_x =>
    have h_x_sq : 0 < (x v)^2 := by
      have h_x_sq_non_zero : 0 ≠ (x v)^2 := by
        rw [pow_two, ne_comm, mul_self_ne_zero]
        simp [h_x]
      have h_x_sq_eq : 0 ≤ (x v)^2 := by nlinarith
      simp [lt_of_le_of_ne, h_x_sq_non_zero, h_x_sq_eq]
    have h_y_sq : 0 ≤ (y v)^2 := by nlinarith
    have h_contr : 0 < (x v)^2 + (y v)^2 := by
      exact add_pos_of_pos_of_nonneg h_x_sq h_y_sq
    grind
  | inr h_y =>
    have h_y_sq : 0 < (y v)^2 := by
      have h_y_sq_non_zero : 0 ≠ (y v)^2 := by
        rw [pow_two, ne_comm, mul_self_ne_zero]
        simp [h_y]
      have h_y_sq_eq : 0 ≤ (y v)^2 := by nlinarith
      simp [lt_of_le_of_ne, h_y_sq_non_zero, h_y_sq_eq]
    have h_x_sq : 0 ≤ (x v)^2 := by nlinarith
    have h_contr : 0 < (y v)^2 + (x v)^2 := by
      exact add_pos_of_pos_of_nonneg h_y_sq h_x_sq
    grind
  grind

theorem spherical_theta_dx_or_dy_differentiable (v : Vec3) (h_xy : x v ≠ 0 ∨ y v ≠ 0) :
  DifferentiableAt ℝ (fun w => arccos w) ((fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) v)
  ∧ DifferentiableAt ℝ (fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) v := by
  have h_xyz : x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0 := by
    cases h_xy with
    | inl h_x => simp [h_x]
    | inr h_y => simp [h_y]
  have h_r_non_zero := r_non_zero (x v) (y v) (z v) h_xyz

  have h_diffAt_1 : DifferentiableAt ℝ (fun w => arccos w) ((fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) v) := by
    rw [x_clm, y_clm, z_clm]
    refine differentiableAt_arccos.mpr ?_
    constructor
    rw [← x_clm, ← y_clm, ← z_clm]
    exact spherical_theta_function_special_differential_case v (-1) (by simp) (h_xy) (h_r_non_zero)
    rw [← x_clm, ← y_clm, ← z_clm]
    exact spherical_theta_function_special_differential_case v (1) (by simp) (h_xy) (h_r_non_zero)

  have h_diffAt_2 : DifferentiableAt ℝ (fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) v := by
    rw [x_clm, y_clm, z_clm]
    refine DifferentiableAt.fun_mul ?_ ?_
    fun_prop
    apply DifferentiableAt.inv
    apply DifferentiableAt.sqrt
    fun_prop
    rw [← x_clm, ← y_clm, ← z_clm]
    rw [← sqrt_ne_zero (x := x v ^ 2 + y v ^ 2 + z v ^ 2) (by nlinarith)]
    exact h_r_non_zero
    rw [← x_clm, ← y_clm, ← z_clm]
    exact h_r_non_zero

  simp [h_diffAt_1, h_diffAt_2]

theorem spherical_theta_dx_or_dy (k : Fin 3) (v : Vec3) (h_xy : x v ≠ 0 ∨ y v ≠ 0) (h_k_vals : k = 0 ∨ k = 1) : ∂[k] (theta ∘ Vec3.toSpherical) v = ((coordCLM k v) * (z v)) / (((x v)^2 + (y v)^2 + (z v)^2) * √((x v)^2 + (y v)^2)) := by
  have h_xyz : x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0 := by
    cases h_xy with
    | inl h_x => simp [h_x]
    | inr h_y => simp [h_y]
  rw [Space.deriv]
  have h_r_non_zero := r_non_zero (x v) (y v) (z v) h_xyz

  have h_neighbourhood : (theta ∘ Vec3.toSpherical) =ᶠ[𝓝 v] (fun v => arccos (z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2))) := by
    exact spherical_theta_neighbourhood h_xyz
  simp [h_neighbourhood.fderiv_eq]

  have h_split : (fun v => arccos (z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2))) = (fun w => (arccos w)) ∘ (fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) := by
    rfl
  rw [h_split]

  rw [fderiv_comp (g := fun w : ℝ => (arccos w)) (f := fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) (x := v) (spherical_theta_dx_or_dy_differentiable v h_xy).1 (spherical_theta_dx_or_dy_differentiable v h_xy).2]
  simp [ContinuousLinearMap.comp_apply]
  have h_deriv : (fderiv ℝ (fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) v) (basis k) = - (coordCLM k v) * (z v) / (((x v)^2 + (y v)^2 + (z v)^2) * √((x v)^2 + (y v)^2 + (z v)^2)) := by
    have h_split_sub : (fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) = (fun v => z v) / (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)) := by
      rfl
    rw [h_split_sub]
    simp [div_eq_mul_inv]
    rw [fderiv_mul]
    simp
    have h_split_inv : (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2))⁻¹ = (fun w => w⁻¹) ∘ (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)) := by rfl
    rw [h_split_inv]

    have h_diffAt_sub_1 : DifferentiableAt ℝ (fun w => w⁻¹) ((fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)) v) := by
      rw [x_clm, y_clm, z_clm]
      refine differentiableAt_inv ?_
      simp
      push_neg
      rw [← x_clm, ← y_clm, ← z_clm]
      exact h_r_non_zero

    have h_diffAt_sub_2 : DifferentiableAt ℝ (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)) v := by
      rw [x_clm, y_clm, z_clm]
      refine DifferentiableAt.sqrt ?_ ?_
      fun_prop
      rw [← x_clm, ← y_clm, ← z_clm]
      rw [← sqrt_ne_zero (x := x v ^ 2 + y v ^ 2 + z v ^ 2) (by nlinarith)]
      exact h_r_non_zero

    rw [fderiv_comp (g := fun w : ℝ => w⁻¹) (f := fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)) (x := v) h_diffAt_sub_1 h_diffAt_sub_2]
    simp [ContinuousLinearMap.comp_apply]
    rw [fderiv_sqrt]
    have h_triple_split : (fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) = (fun v => x v ^ 2) + (fun v => y v ^ 2) + (fun v => z v ^ 2) := by rfl
    rw [h_triple_split, fderiv_add, fderiv_add, fderiv_pow, fderiv_pow, fderiv_pow, ← deriv_eq_fderiv_basis]
    rw [x_func, y_func, z_func, Space.deriv_component 2 k v, ← x_func, ← y_func, ← z_func]
    simp [← deriv_eq_fderiv_basis]
    rw [x_func, y_func, z_func, Space.deriv_component 0 k v, Space.deriv_component 1 k v, Space.deriv_component 2 k v, ← x_func, ← y_func, ← z_func]
    simp
    rw [sq_sqrt]
    by_cases h_k : k = 0
    · simp [h_k]
      rw [← x_clm]
      grind
    · have h_k_1 : k = 1 := by
        simp [h_k] at h_k_vals
        simp [h_k_vals]
      simp [h_k_1]
      rw [← y_clm]
      grind
    · nlinarith
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
    · rw [x_clm, y_clm, z_clm]
      fun_prop
    · grind
    · rw [z_clm]
      fun_prop
    · rw [x_clm, y_clm, z_clm]
      have h_sum_non_zero : (coordCLM 0) v ^ 2 + (coordCLM 1) v ^ 2 + (coordCLM 2) v ^ 2 ≠ 0 := by
        rw [← x_clm, ← y_clm, ← z_clm]
        grind
      refine DifferentiableAt.inv ?_ ?_
      apply DifferentiableAt.sqrt
      fun_prop
      exact h_sum_non_zero
      rw [sqrt_ne_zero]
      exact h_sum_non_zero
      nlinarith

  simp [h_deriv]
  field_simp [sq_sqrt, div_zpow]
  have h_non_neg : 0 ≤ x v ^ 2 + y v ^ 2 + z v ^ 2 := by nlinarith
  have h_non_zero : 0 ≠ x v ^ 2 + y v ^ 2 + z v ^ 2 := by grind
  have h_sqrt_non_neg : 0 ≠ √(x v ^ 2 + y v ^ 2 + z v ^ 2) := by
    rw [ne_comm, sqrt_ne_zero h_non_neg]
    exact h_non_zero.symm
  have h_sq : √(x v ^ 2 + y v ^ 2 + z v ^ 2) ^ 2 = x v ^ 2 + y v ^ 2 + z v ^ 2 := by
    grind
  simp
  grind

theorem spherical_theta_dx (v : Vec3) (h_xy : x v ≠ 0 ∨ y v ≠ 0) : ∂[0] (theta ∘ Vec3.toSpherical) v = ((x v) * (z v)) / (((x v)^2 + (y v)^2 + (z v)^2) * √((x v)^2 + (y v)^2)) := by
  nth_rw 1 [x_clm]
  exact spherical_theta_dx_or_dy 0 v h_xy (by simp)

theorem spherical_theta_dy (v : Vec3) (h_xy : x v ≠ 0 ∨ y v ≠ 0) : ∂[1] (theta ∘ Vec3.toSpherical) v = ((y v) * (z v)) / (((x v)^2 + (y v)^2 + (z v)^2) * √((x v)^2 + (y v)^2)) := by
  nth_rw 1 [y_clm]
  exact spherical_theta_dx_or_dy 1 v h_xy (by simp)

lemma sq_duo_non_zero (h_xy : x v ≠ 0 ∨ y v ≠ 0) : 0 ≠ √((x v)^2 + (y v)^2) := by
  have h_sq_duo_pos : 0 < √((x v)^2 + (y v)^2) := by
    cases h_xy with
    | inl h_x =>
      have h_x_sq_pos : 0 < (x v)^2 := by exact zpow_two_pos_of_ne_zero h_x
      have h_y_non_neg : 0 ≤ (y v)^2 := by nlinarith
      have h_sum_pos : 0 < (x v)^2 + (y v)^2 := by nlinarith [h_x_sq_pos, h_y_non_neg]
      simp [sqrt_pos, h_sum_pos]
    | inr h_y =>
      have h_y_sq_pos : 0 < (y v)^2 := by exact zpow_two_pos_of_ne_zero h_y
      have h_x_non_neg : 0 ≤ (x v)^2 := by nlinarith
      have h_sum_pos : 0 < (x v)^2 + (y v)^2 := by nlinarith [h_y_sq_pos, h_x_non_neg]
      simp [sqrt_pos, h_sum_pos]
  grind


lemma spherical_theta_dz_sub_goals (v : Vec3) (h_xyz : x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0) :
  x v ^ 2 + y v ^ 2 + z v ^ 2 ≠ 0 ∧
  0 ≤ x v ^ 2 + y v ^ 2 ∧
  0 ≤ x v ^ 2 + y v ^ 2 + z v ^ 2 ∧
  DifferentiableAt ℝ z v ∧
  DifferentiableAt ℝ y v ∧
  DifferentiableAt ℝ x v ∧
  DifferentiableAt ℝ (fun v => x v ^ 2) v ∧
  DifferentiableAt ℝ (fun v => y v ^ 2) v ∧
  DifferentiableAt ℝ ((fun v => x v ^ 2) + fun v => y v ^ 2) v ∧
  DifferentiableAt ℝ (fun v => z v ^ 2) v ∧
  DifferentiableAt ℝ (fun v => (x v ^ 2 + y v ^ 2 + z v ^ 2)⁻¹) v ∧
  (x v ^ 2 + y v ^ 2 + z v ^ 2)⁻¹ ≠ 0 ∧
  DifferentiableAt ℝ (fun v => z v) v ∧
  DifferentiableAt ℝ (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)⁻¹) v
 := by
    have h_r_non_zero := r_non_zero (x v) (y v) (z v) h_xyz

    constructor
    grind [sqrt_ne_zero]
    constructor
    nlinarith
    constructor
    nlinarith
    constructor
    rw [z_clm]
    fun_prop
    constructor
    rw [y_clm]
    fun_prop
    constructor
    rw [x_clm]
    fun_prop
    constructor
    rw [x_clm]
    fun_prop
    constructor
    rw [y_clm]
    fun_prop
    constructor
    rw [x_clm, y_clm]
    fun_prop
    constructor
    rw [z_clm]
    fun_prop
    constructor
    apply DifferentiableAt.inv
    rw [x_clm, y_clm, z_clm]
    fun_prop
    grind [sqrt_ne_zero]
    constructor
    grind
    constructor
    rw [z_clm]
    fun_prop
    apply DifferentiableAt.sqrt
    apply DifferentiableAt.inv
    rw [x_clm, y_clm, z_clm]
    fun_prop
    grind [sqrt_ne_zero]
    grind


theorem spherical_theta_dz (v : Vec3) (h_xy : x v ≠ 0 ∨ y v ≠ 0) : ∂[2] (theta ∘ Vec3.toSpherical) v = - √((x v)^2 + (y v)^2) / (((x v)^2 + (y v)^2 + (z v)^2)) := by
  have h_xyz : x v ≠ 0 ∨ y v ≠ 0 ∨ z v ≠ 0 := by
    cases h_xy with
    | inl h_x => simp [h_x]
    | inr h_y => simp [h_y]
  rw [Space.deriv]
  have h_r_non_zero := r_non_zero (x v) (y v) (z v) h_xyz

  have h_neighbourhood : (theta ∘ Vec3.toSpherical) =ᶠ[𝓝 v] (fun v => arccos (z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2))) := by
    exact spherical_theta_neighbourhood h_xyz
  simp [h_neighbourhood.fderiv_eq]

  have h_split : (fun v => arccos (z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2))) = (fun w => (arccos w)) ∘ (fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) := by
    rfl
  rw [h_split]

  rw [fderiv_comp (g := fun w : ℝ => arccos w) (f := fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) (x := v) (spherical_theta_dx_or_dy_differentiable v h_xy).1 (spherical_theta_dx_or_dy_differentiable v h_xy).2]
  simp [ContinuousLinearMap.comp_apply]
  have h_div_split : (fun v => z v / √(x v ^ 2 + y v ^ 2 + z v ^ 2)) = (fun v => z v ) / (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)) := by rfl
  have h_inv_split : (fun v => z v ) / (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)) = (fun v => z v ) * (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2))⁻¹ := by rfl
  have h_inv_interior : (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2))⁻¹ = (fun v => √(x v ^ 2 + y v ^ 2 + z v ^ 2)⁻¹) := by
    ext v
    simp
  have h_triple_split : (fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) = (fun v => x v ^ 2) + (fun v => y v ^ 2) + (fun v => z v ^ 2) := by rfl
  rw [h_div_split, h_inv_split, h_inv_interior]
  rw [fderiv_mul, fderiv_sqrt, x_clm, y_clm, z_clm]
  field_simp
  simp
  have h_inverse_segregate : (fun v => (x v ^ 2 + y v ^ 2 + z v ^ 2)⁻¹) = (fun w => w⁻¹) ∘ (fun v => (x v ^ 2 + y v ^ 2 + z v ^ 2)) := by rfl
  rw [← x_clm, ← y_clm, ← z_clm, h_inverse_segregate]
  rw [fderiv_comp (g := fun w : ℝ => w⁻¹) (f := fun v => x v ^ 2 + y v ^ 2 + z v ^ 2) (x := v)
      (by rw [x_clm, y_clm, z_clm]; refine differentiableAt_inv ?_; rw [← x_clm, ← y_clm, ← z_clm]; simp; grind [sqrt_ne_zero])
      (by rw [x_clm, y_clm, z_clm]; fun_prop)]
  simp [ContinuousLinearMap.comp_apply]
  rw [h_triple_split, fderiv_add, fderiv_add, fderiv_pow, fderiv_pow, fderiv_pow]
  simp [← deriv_eq_fderiv_basis]
  rw [x_func, y_func, z_func, Space.deriv_component 2 2 v, Space.deriv_component 1 2 v, Space.deriv_component 0 2 v, ← x_func, ← y_func, ← z_func]
  simp
  field_simp
  rw [sq_sqrt]
  field_simp [h_r_non_zero]
  simp
  rw [sqrt_div]
  field_simp
  simp [z_func]
  have h_sq_duo_non_zero := sq_duo_non_zero h_xy
  have h_z_back : @Space.val 3 v 2 = z v := by rw [z_func]
  rw [h_z_back, ← neg_div, div_add_one]
  grind

  · exact (spherical_theta_dz_sub_goals v h_xyz).1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.2.2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.2.2.2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.2.2.2.2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.2.2.2.2.2.2.2.1
  · exact (spherical_theta_dz_sub_goals v h_xyz).2.2.2.2.2.2.2.2.2.2.2.2.1

  apply DifferentiableAt.sqrt
  apply DifferentiableAt.inv
  rw [x_clm, y_clm, z_clm]
  fun_prop
  grind [sqrt_ne_zero]
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

lemma atan2_interior_dy (v : Vec3) (h_y_non_zero : y v ≠ 0) : (fderiv ℝ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) v) (basis 1) = (x v) / ((√((x v)^2 + (y v)^2))*(√((x v)^2 + (y v)^2) + (x v))) := by
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

  rw [fderiv_mul]
  simp
  have h_split_inv_sqrt : (fun v => (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) = (fun w => w⁻¹) ∘ (fun v => √(x v ^ 2 + y v ^ 2) + x v) := by rfl
  rw [h_split_inv_sqrt]

  have h_diffAt_1 : DifferentiableAt ℝ (fun w => w⁻¹) ((fun v => √(x v ^ 2 + y v ^ 2) + x v) v) := by
    apply DifferentiableAt.inv
    simp
    grind

  have h_diffAt_2 : DifferentiableAt ℝ (fun v => √(x v ^ 2 + y v ^ 2) + x v) v := by
    apply DifferentiableAt.add
    apply DifferentiableAt.sqrt
    rw [x_clm, y_clm]
    fun_prop
    grind
    rw [x_clm]
    fun_prop

  rw [fderiv_comp (g := fun w : ℝ => w⁻¹) (f := (fun v => √(x v ^ 2 + y v ^ 2) + x v)) (x := v) h_diffAt_1 h_diffAt_2]
  simp [ContinuousLinearMap.comp_apply]
  have h_fun_add : (fun v => √(x v ^ 2 + y v ^ 2) + x v) = (fun v => √(x v ^ 2 + y v ^ 2)) + ((fun v => x v)) := by rfl
  rw [h_fun_add, fderiv_add, fderiv_sqrt]
  rw [← deriv_eq_fderiv_basis, x_func, y_func, Space.deriv_component 1 1 v, ← x_func, ← y_func]
  simp
  have h_quad_split : (fun v => x v ^ 2 + y v ^ 2) = (fun v => x v^2) + (fun v => y v^2) := by rfl
  rw [h_quad_split, fderiv_add, fderiv_pow 2]
  rw [x_func, y_func, ← Space.deriv, Space.deriv_component 0 1 v, ← x_func, ← y_func]
  simp
  rw [x_func, y_func, ← Space.deriv, Space.deriv_component 0 1 v, ← x_func, ← y_func, fderiv_pow]
  simp
  rw [x_func, y_func, ← Space.deriv, Space.deriv_component 1 1 v, ← x_func, ← y_func]
  simp
  field_simp
  rw [left_distrib, ← pow_two, sq_sqrt]
  have h_numerator : (-y v ^ 2 + (x v ^ 2 + y v ^ 2 + √(x v ^ 2 + y v ^ 2) * x v)) = (x v ^ 2 + √(x v ^ 2 + y v ^ 2) * x v) := by nlinarith
  rw [h_numerator, pow_two, pow_two, pow_two, ← right_distrib, mul_comm, add_comm]
  field_simp
  nlinarith

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
  · grind
  · apply DifferentiableAt.sqrt
    rw [x_clm, y_clm]
    fun_prop
    grind
  · rw [x_clm]
    fun_prop
  · rw [y_clm]
    fun_prop
  · apply DifferentiableAt.inv
    apply DifferentiableAt.add
    apply DifferentiableAt.sqrt
    rw [x_clm, y_clm]
    fun_prop
    grind
    rw [x_clm]
    fun_prop
    grind

lemma x_sq_y_sq_non_neg (v : Vec3) (h_y_non_zero : y v ≠ 0) : 0 ≠ (x v)^2 + (y v)^2 := by
  have h_y_sq : 0 ≠ (y v)^2 := by
    simp [h_y_non_zero, pow_two]
  have h_y_sq : 0 < (y v)^2 := by
    have h_y_nonneg : 0 ≤ (y v)^2 := by nlinarith
    simp [h_y_sq, h_y_nonneg, lt_of_le_of_ne]
  have h_x_sq : 0 ≤ (x v)^2 := by nlinarith
  nlinarith [h_y_sq, h_x_sq]

theorem atan2_case_dx_or_dy (k : Fin 3) (v : Vec3) (h_y_non_zero : y v ≠ 0) (h_k : k = 0 ∨ k = 1) : ∂[k] (fun v => 2 * Real.arctan (y v / (Real.sqrt ((x v)^2 + (y v)^2) + (x v)))) v = if k = 0 then - (y v) / ((x v)^2 + (y v)^2) else (x v) / ((x v)^2 + (y v)^2) := by
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

  have h_fderiv_x : (fderiv ℝ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) v) (basis 0) = - (y v) / (√((x v)^2 + (y v)^2) * (√((x v)^2 + (y v)^2) + (x v))) := by exact atan2_interior_dx v h_y_non_zero
  have h_fderiv_y : (fderiv ℝ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) v) (basis 1) =   (x v) / (√((x v)^2 + (y v)^2) * (√((x v)^2 + (y v)^2) + (x v))) := by exact atan2_interior_dy v h_y_non_zero

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

  by_cases h_k_0 : k = 0
  · simp [h_k_0, h_fderiv_x]
    rw [← one_div]
    grind
  · have h_k_1 : k = 1 := by grind
    simp [h_k_1, h_fderiv_y]
    rw [← one_div]
    grind

theorem atan2_case_dx (v : Vec3) (h_y_non_zero : y v ≠ 0) : ∂[0] (fun v => 2 * Real.arctan (y v / (Real.sqrt ((x v)^2 + (y v)^2) + (x v)))) v = - (y v) / ((x v)^2 + (y v)^2) := by
  exact atan2_case_dx_or_dy 0 v h_y_non_zero (by simp)

theorem atan2_case_dy (v : Vec3) (h_y_non_zero : y v ≠ 0) : ∂[1] (fun v => 2 * Real.arctan (y v / (Real.sqrt ((x v)^2 + (y v)^2) + (x v)))) v = (x v) / ((x v)^2 + (y v)^2) := by
  exact atan2_case_dx_or_dy 1 v h_y_non_zero (by simp)

lemma phi_neighbourhood (v : Vec3) (h_y_non_zero : y v ≠ 0) :
  (fun v => if y v = 0 ∧ x v < 0 then π
  else 2 * Real.arctan (y v / (Real.sqrt (x v ^ 2 + y v ^ 2) + x v)))
  =ᶠ[𝓝 v]
  (fun w => 2 * Real.arctan ((y w) / (Real.sqrt (x w ^ 2 + y w ^ 2) + x w))) := by
    let s : Set Vec3 := {u | (y u) ≠ 0}
    have h_s_neighbourhood : s ∈ 𝓝 v := by
      have h_y_continuousAt : ContinuousAt y v := by
        rw [y_func]
        fun_prop
      have h_neighbourhood_condition : ∀ᶠ u in 𝓝 v, y u ≠ 0 := by
        (expose_names; exact ContinuousAt.eventually_ne h_y_continuousAt h_y_non_zero)
      exact h_neighbourhood_condition
    have h_eq_on_s : Set.EqOn
      (fun v => if y v = 0 ∧ x v < 0 then π else 2 * Real.arctan (y v / (√(x v ^ 2 + y v ^ 2) + x v)))
      (fun w => 2 * Real.arctan (y w / (√(x w ^ 2 + y w ^ 2) + x w)))
      s := by
        intro t h_t
        simp
        grind
    exact Filter.eventuallyEq_of_mem h_s_neighbourhood h_eq_on_s



theorem spherical_phi_dx_or_dy (k : Fin 3) (v : Vec3) (h_y_non_zero : y v ≠ 0) (h_k : k = 0 ∨ k = 1) : ∂[k] (phi ∘ Vec3.toSpherical) v = if k = 0 then -(y v) / ((x v)^2 + (y v)^2) else (x v) / ((x v)^2 + (y v)^2) := by

  simp [Space.deriv, phi_on_toSpherical, atan2]

  have h_atan2_case : ¬(y v = 0 ∧ x v < 0) := by simp [h_y_non_zero]
  have h_atan2_case_dx : ∂[0] (fun v => 2 * Real.arctan (y v / (Real.sqrt ((x v)^2 + (y v)^2) + (x v)))) v = - (y v) / ((x v)^2 + (y v)^2) := by
    exact atan2_case_dx v h_y_non_zero
  have h_atan2_case_dy : ∂[1] (fun v => 2 * Real.arctan (y v / (Real.sqrt ((x v)^2 + (y v)^2) + (x v)))) v =   (x v) / ((x v)^2 + (y v)^2) := by
    exact atan2_case_dy v h_y_non_zero
  rw [Space.deriv] at h_atan2_case_dx
  rw [Space.deriv] at h_atan2_case_dy

  rw [←h_atan2_case_dx, ← h_atan2_case_dy]

  by_cases h_k_0 : k = 0
  · simp [h_k_0]
    rw [(phi_neighbourhood v h_y_non_zero).fderiv_eq]
  · have h_k_1 : k = 1 := by
      simp [h_k_0] at h_k
      exact h_k
    simp [h_k_1]
    rw [(phi_neighbourhood v h_y_non_zero).fderiv_eq]

theorem spherical_phi_dx (v : Vec3) (h_y_non_zero : y v ≠ 0) : ∂[0] (phi ∘ Vec3.toSpherical) v = -(y v) / ((x v)^2 + (y v)^2) := by
  exact spherical_phi_dx_or_dy 0 v h_y_non_zero (by simp)

theorem spherical_phi_dy (v : Vec3) (h_y_non_zero : y v ≠ 0) : ∂[1] (phi ∘ Vec3.toSpherical) v = (x v) / ((x v)^2 + (y v)^2) := by
  exact spherical_phi_dx_or_dy 1 v h_y_non_zero (by simp)



theorem spherical_phi_dz (v : Vec3) (h_y_non_zero : y v ≠ 0) : ∂[2] (phi ∘ Vec3.toSpherical) v = 0:= by
  simp [Space.deriv, phi_on_toSpherical, atan2]
  rw [(phi_neighbourhood v h_y_non_zero).fderiv_eq]

  have h_fun_split_1 : (fun w => 2 * arctan (y w / (√(x w ^ 2 + y w ^ 2) + x w))) = (fun w => 2 * w) ∘ (fun v => arctan (y v / (√(x v ^ 2 + y v ^ 2) + x v))) := by rfl
  have h_fun_split_2 : (fun w => arctan (y w / (√(x w ^ 2 + y w ^ 2) + x w))) = (fun w => arctan w) ∘ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) := by rfl
  rw [h_fun_split_1]

  have h_denom_non_zero : √(x v ^ 2 + y v ^ 2) + x v ≠ 0 := by
    have h_pos : 0 < (x v)^ 2 + (y v)^ 2 := by
      apply lt_of_le_of_ne
      nlinarith
      exact (x_sq_y_sq_non_neg v h_y_non_zero)
    nlinarith [sqrt_x2_y2_add_x_ne_zero (x := x v) (y := y v) h_pos (by simp [h_y_non_zero])]

  have h_diffAt_1 : DifferentiableAt ℝ (fun w => 2 * w) ((fun v => arctan (y v / (√(x v ^ 2 + y v ^ 2) + x v))) v) := by
    simp
    rw [x_clm, y_clm]
    refine Differentiable.differentiableAt ?_
    fun_prop

  have h_diffAt_2 : DifferentiableAt ℝ (fun v => arctan (y v / (√(x v ^ 2 + y v ^ 2) + x v))) v := by
    simp
    [x_clm, y_clm]
    refine DifferentiableAt.arctan ?_
    refine DifferentiableAt.fun_mul ?_ ?_
    fun_prop
    apply DifferentiableAt.inv
    apply DifferentiableAt.add
    apply DifferentiableAt.sqrt
    fun_prop
    rw [← x_clm, ← y_clm]
    exact (x_sq_y_sq_non_neg v h_y_non_zero).symm
    fun_prop
    rw [← x_clm, ← y_clm]
    exact h_denom_non_zero

  have h_diffAt_3 : DifferentiableAt ℝ (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) v := by
    refine DifferentiableAt.fun_mul ?_ ?_
    rw [y_clm]
    fun_prop
    apply DifferentiableAt.inv
    apply DifferentiableAt.add
    apply DifferentiableAt.sqrt
    rw [x_clm, y_clm]
    fun_prop
    exact (x_sq_y_sq_non_neg v h_y_non_zero).symm
    rw [x_clm]
    fun_prop
    exact h_denom_non_zero

  rw [fderiv_comp (g := fun w : ℝ => 2* w) (f := fun v : Vec3 => arctan (y v / (√(x v ^ 2 + y v ^ 2) + x v))) (x := v) h_diffAt_1 h_diffAt_2]
  simp [ContinuousLinearMap.comp_apply]
  rw [h_fun_split_2]
  rw [fderiv_comp (g := fun w : ℝ => arctan w) (f := fun v : Vec3 => y v / (√(x v ^ 2 + y v ^ 2) + x v)) (x := v) (by apply differentiableAt_arctan) h_diffAt_3]
  simp [ContinuousLinearMap.comp_apply]
  left
  left
  have h_fun_split_3 : (fun v => y v / (√(x v ^ 2 + y v ^ 2) + x v)) = (fun v => y v) * (fun v => (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) := by rfl
  have h_fun_split_4 : (fun v => (√(x v ^ 2 + y v ^ 2) + x v)⁻¹) = (fun w => w⁻¹) ∘ (fun v => (√(x v ^ 2 + y v ^ 2) + x v)) := by rfl
  have h_fun_split_5 : (fun v => (√(x v ^ 2 + y v ^ 2) + x v)) = (fun v => (√(x v ^ 2 + y v ^ 2))) + (fun v => (x v)) := by rfl
  rw [h_fun_split_3, fderiv_mul, h_fun_split_4]
  rw [fderiv_comp (g := fun w : ℝ => w⁻¹) (f := fun v : Vec3 => (√(x v ^ 2 + y v ^ 2) + x v)) (x := v) (by exact differentiableAt_inv h_denom_non_zero)
      (by apply DifferentiableAt.add; apply DifferentiableAt.sqrt; rw [x_clm, y_clm]; fun_prop; exact (x_sq_y_sq_non_neg v h_y_non_zero).symm; rw [x_clm]; fun_prop)]
  simp
  rw [h_fun_split_5, fderiv_add, fderiv_sqrt]
  rw [← Space.deriv, x_func, y_func, Space.deriv_component 1 2 v, ← x_func, ← y_func]
  simp
  rw [← Space.deriv, ← Space.deriv, x_func, y_func, Space.deriv_component 0 2 v, ← x_func, ← y_func, Space.deriv]
  simp
  right
  left
  right
  have h_sum_split : (fun v => x v ^ 2 + y v ^ 2) = (fun v => x v ^ 2) + (fun v => y v ^ 2) := by rfl
  rw [h_sum_split, fderiv_add, fderiv_pow 2, fderiv_pow 2]
  simp
  rw [x_func, y_func, ← Space.deriv, Space.deriv_component 0 2 v, ← Space.deriv, Space.deriv_component 1 2 v, ← x_func, ← y_func]
  simp

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
  · exact (x_sq_y_sq_non_neg v h_y_non_zero).symm
  · apply DifferentiableAt.sqrt
    rw [x_clm, y_clm]
    fun_prop
    exact (x_sq_y_sq_non_neg v h_y_non_zero).symm
  · rw [x_clm]
    fun_prop
  · rw [y_clm]
    fun_prop
  · apply DifferentiableAt.inv
    apply DifferentiableAt.add
    apply DifferentiableAt.sqrt
    rw [x_clm, y_clm]
    fun_prop
    exact (x_sq_y_sq_non_neg v h_y_non_zero).symm
    rw [x_clm]
    fun_prop
    exact h_denom_non_zero

end PhysLean.Mathematics.SphericalCoordinates.Differentiation
