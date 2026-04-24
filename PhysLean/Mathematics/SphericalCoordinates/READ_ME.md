Here are instructions to install and use the module, take from the user documentation section of the dissertation:

NOTE: Due to name changes, "PhysLib" may need to be substituted in place of "PhysLean"

1) Installation Guide

This Appendix assumes and highly recommends usage of Visual Studio Code
1. Install Visual Studio Code, if not already installed, from the official source:
https://code.visualstudio.com/download

2. Install the Lean 4 extension directly in Visual Studio Code.

3. Use git to clone PhysLean:
git clone https://github.com/leanprover-community/physlib

If the current version of PhysLean is no longer compatible, as PhysLean and mathlib are both updated frequently, try checking out this commit from inside the local repository:
   git checkout 351e3994565278d3950875966542efe97f489a8d

4. Add the SphericalCoordinates folder into:
PhysLean/Mathematics/

5. If you just want to compile PhysLean to prove that it works, enter the physlib directory and run the commands: 

lake update
lake build

You can also run this from your own project directory if it contains PhysLean in order to use it in your own project, but you must make sure it is configured properly for your set-up.


2) Usage Guide

The Spherical Coordinates module can then be accessed similarly to any module of PhysLean.
Here are the imports for each file:

import PhysLean.Mathematics.SphericalCoordinates.SphericalCoords
import PhysLean.Mathematics.SphericalCoordinates.atan2.atan2
import PhysLean.Mathematics.SphericalCoordinates.Differentiation.Differentiation
import PhysLean.Mathematics.SphericalCoordinates.Integration.Integration

You can then open what you need, for example:

open PhysLean.Mathematics.SphericalCoordinates.Spherical

And you can then freely call any properties of Spherical, such as calling r and Vec3.toSpherical
in this line:

(0, 0) => δ[0] (r ◦ Vec3.toSpherical) v