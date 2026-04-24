import PhysLean.Mathematics.SphericalCoordinates.SphericalCoords
import PhysLean.Mathematics.SphericalCoordinates.atan2.atan2
import PhysLean.Mathematics.SphericalCoordinates.Differentiation.Differentiation
import PhysLean.Mathematics.SphericalCoordinates.Integration.Integration
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

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Function.Jacobian
namespace PhysLean.Mathematics.SphericalCoordinates

#check Real
#check ℝ
#check Complex

example (x : ℝ) : x^2 ≥ 0 := by
  nlinarith

#check (by decide : True)

open PhysLean.Mathematics.SphericalCoordinates
open Spherical

noncomputable def s1 : Spherical := { r := 1, theta := 0, phi := 0, r_bounds := (by simp), theta_bounds := sorry, phi_bounds := sorry, r_zero_bound := sorry, theta_zero_bound := sorry, theta_pi_bound := sorry}
noncomputable def s2 : Spherical := { r := 2, theta := 1.0, phi := 0.0, r_bounds := (by simp), theta_bounds := sorry , phi_bounds := sorry, r_zero_bound := sorry, theta_zero_bound := sorry, theta_pi_bound := sorry}

noncomputable def s1Vec := toVec3 s1
noncomputable def s2Vec := toVec3 s2

#check s1Vec
#check euclidDist s1Vec s2Vec
