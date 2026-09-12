/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Square

namespace LatticeProb.Lattice.Planar

/-- The face on the right of the directed edge `v → v + dirVec a`. -/
def rightFace (v : Site) (a : Dir) : Site :=
  let d := dirVec a
  (v.1 + (d.1 + d.2 - 1) / 2, v.2 + (d.2 - d.1 - 1) / 2)

/-- The face on the left of the directed edge `v → v + dirVec a`. -/
def leftFace (v : Site) (a : Dir) : Site :=
  let d := dirVec a
  ((rightFace v a).1 - d.2, (rightFace v a).2 + d.1)

/-- The dual edge of `v → v + dirVec a`, from the right face to the left face. -/
def dualEdge (v : Site) (a : Dir) : Site × Site := (rightFace v a, leftFace v a)

/-- The tail of the primal edge whose rotation is the dual edge `f → g`. -/
def primalTail (f g : Site) : Site :=
  let δ := g - f
  (f.1 + (δ.1 - δ.2 + 1) / 2, f.2 + (δ.1 + δ.2 + 1) / 2)

/-- The direction of the primal edge whose rotation is the dual edge `f → g`:
`δ` rotated clockwise. -/
def primalDir (f g : Site) : Dir :=
  let δ := g - f
  dirOf (δ.2, -δ.1)

/-- The dual edge `f → g` is open: the primal edge it rotates has rank `2` or
`3` after the initial rotor. -/
def DualOpen (ρ : Config squareGraph) (f g : Site) : Prop :=
  let v := primalTail f g
  let a := primalDir f g
  rank clockwise ρ v (nbr v a) = 2 ∨ rank clockwise ρ v (nbr v a) = 3

end LatticeProb.Lattice.Planar
