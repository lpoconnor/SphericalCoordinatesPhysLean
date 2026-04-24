/-
Copyright (c) 2025-2026 Liam O'Connor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liam O'Connor
-/

import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.TODO.Basic
import PhysLean.SpaceAndTime.Space.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Function.Jacobian
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
import PhysLean.Mathematics.SphericalCoordinates.SphericalCoords

/-
  This file contains:
  -Jacobian
  -Jacobian Determinant
  -Triple Integral from Cartesian to Spherical Coordinates
-/

open Mathlib
open Real
open Fin
open MeasureTheory Real
open PhysLean.Mathematics.SphericalCoordinates.Spherical

namespace PhysLean.Mathematics.SphericalCoordinates.Integration


noncomputable def jacobian_inverse (v : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
Matrix.of fun i j =>
  match (i, j) with
  | (0, 0) => ∂[0] (r ∘ Vec3.toSpherical) v
  | (0, 1) => ∂[1] (r ∘ Vec3.toSpherical) v
  | (0, 2) => ∂[2] (r ∘ Vec3.toSpherical) v
  | (1, 0) => ∂[0] (theta ∘ Vec3.toSpherical) v
  | (1, 1) => ∂[1] (theta ∘ Vec3.toSpherical) v
  | (1, 2) => ∂[2] (theta ∘ Vec3.toSpherical) v
  | (2, 0) => ∂[0] (phi ∘ Vec3.toSpherical) v
  | (2, 1) => ∂[1] (phi ∘ Vec3.toSpherical) v
  | (2, 2) => ∂[2] (phi ∘ Vec3.toSpherical) v

theorem spherical_jacobian_det_r_theta (v : Vec3) (h_xy : x v ≠ 0 ∨ y v ≠ 0) :
  Matrix.det (jacobian_inverse v) =  ((r ∘ Vec3.toSpherical) v) ^ 2 * sin ((theta ∘ Vec3.toSpherical) v) := by sorry

theorem integrate_spherical_coord
  (f : ℝ × ℝ × ℝ → ℝ)
  (h_f : Integrable f) :
  (∫ z in (Set.univ : Set ℝ),
   ∫ y in (Set.univ : Set ℝ),
   ∫ x in (Set.univ : Set ℝ),
    f (x, y, z))
  =
  (∫ phi in Set.Icc 0 (2 * π),
   ∫ theta in Set.Icc 0 π,
   ∫ r in Set.Ici 0,
    (f (r * sin theta * cos phi, r * sin theta * sin phi, r * cos theta) * r^2 * sin theta)) :=
  by
    sorry

end PhysLean.Mathematics.SphericalCoordinates.Integration
