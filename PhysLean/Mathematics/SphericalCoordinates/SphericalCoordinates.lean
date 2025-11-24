/-
Copyright (c) 2025 Liam O'Connor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liam O'Connor
-/

import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.TODO.Basic
import Mathlib

/-
# Spherical Coordinates

This module implements the fundamentals of spherical coordinates

# Standard Notation
r  - radial distance from origin (>= 0)
θ  - polar angle measured from the positive z axis (0 <= θ <= pi)
φ  - azimuthal angle, measured from positive x axis (−pi < φ ≤ pi)

Cartesian to spherical conversion:
r = sqrt (x^2 + y^2 + z^2)
θ = arccos(z / r)
φ = atan2(y, x)

Spherical to cartesian conversion:
x = r sin θ cos φ
y = r sin θ sin φ
z = r cos θ
-/

structure Spherical where
  r     : Real
  theta : Real
  phi   : Real
deriving Repr, BEq

namespace Spherical

def toCartesianVec3 (s : Spherical) : Vec3 :=
  let x := s.r * Real.sin s.theta * Real.cos s.phi
  let y := s.r * Real.sin s.theta * Real.sin s.phi
  let z := s.r * Real.cos s.theta
  ⟨x, y, z⟩

def Vec3.toSpherical (v : Vec3) : Spherical :=
  let x := v.x
  let y := v.y
  let z := v.z
  let r := Real.sqrt (x*x + y*y + z*z)

  if h : r = 0 then
    -- Convention: θ = 0, φ = 0 at the origin
    { r := 0, theta := 0, phi := 0 }
  else
    let theta := Real.arccos (z / r)
    let phi   := Real.atan2 y x
    { r := r, theta := theta, phi := phi }










































end Spherical









