/-
Copyright (c) 2025 Liam O'Connor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liam O'Connor
-/

import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.TODO.Basic
import Mathlib
import PhysLean.SpaceAndTime.Space.Basic

structure Spherical where
  r     : Real
  theta : Real
  phi   : Real
deriving Repr

namespace Spherical

open EuclideanSpace

noncomputable def toCartesianSpace3 (s : Spherical) : Space 3 :=
  EuclideanSpace.vec #[ s.r * Real.sin(s.theta) * Real.cos(s.phi),
     s.r * Real.si(s.theta) * Real.sin(s.phi),
     s.r * Real.cos(s.theta) ]

noncomputable def Space.toSpherical (v : Space 3) : Spherical :=
  let x := v 0
  let y := v 1
  let z := v 2
  let r := Real.sqrt (x*x + y*y + z*z)
  if _ : r = 0 then
    { r := 0, theta := 0, phi := 0 }
  else
    let theta := Real.acos(z / r)
    let phi :=
      if x > 0 then Real.atan(y / x)
      else if x < 0 ∧ y ≥ 0 then Real.atan(y / x) + Real.pi
      else if x < 0 ∧ y < 0 then Real.atan(y / x) - Real.pi
      else if x = 0 ∧ y > 0 then Real.pi / 2
      else if x = 0 ∧ y < 0 then -Real.pi / 2
      else 0
    { r := r, theta := theta, phi := phi }

noncomputable def dist (s1 s2 : Spherical) : Real :=
  EuclideanSpace.dist (s1.toCartesianSpace3) (s2.toCartesianSpace3)

end Spherical
