import LatticeProb.Lattice.Planar.Metric
import LatticeProb.Lattice.Planar.FaceGeometry
import LatticeProb.Lattice.Planar.ActiveListLemma

/-!
# Square-lattice contours and separation

The namespace `LatticeProb.Lattice.Planar` uses sites `ℤ × ℤ` and clockwise
unit directions. It provides primal and dual edges, finite-set boundary
successors, discrete winding numbers, doubled simple closed walks, and
separation of their left and right sides. The contour context and its S/W
instances use a deterministic depth-first exploration of square-lattice faces.

`DoublyPeriodic` also describes periodic vertex embeddings of arbitrary graphs.
It does not impose noncrossing edges or supply faces for those graphs.
-/
