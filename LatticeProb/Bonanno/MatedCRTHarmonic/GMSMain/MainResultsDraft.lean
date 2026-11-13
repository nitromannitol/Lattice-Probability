/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.MainResultsDraft at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.OutDarts
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Recurrent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Seven definitions for the main results

Local copies, with the **same bodies, argument order and implicit-argument structure**, of the seven supporting
definitions of the draft surface v5 for the main results of Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT
maps* [18], with `dirichletEnergy` taking `_hD : IsOpen D`.
They live in the namespace `MatedCRTHarmonic.GMSMain.MainResults` so that they can coexist with the frozen versions that
will create (`Frozen/EnergyOn.lean`, …, `Frozen/MatedCRTCell.lean`); the theorems are then retargeted
to the frozen names by `rfl` (identical bodies, so the frozen and local constants unfold to the same term).

| draft (frozen-to-be) name | local name | body |
|---|---|---|
| `LFMultigraph.energyOn G S g` | `MainResults.energyOn G S g` | verbatim |
| `LFMultigraph.IsHarmonicExtension G H D f g` | `MainResults.IsHarmonicExtension G H D f g` | verbatim |
| `LFMultigraph.IsTutteEmbedding G H D Φ` | `MainResults.IsTutteEmbedding G H D Φ` | verbatim (dot notation unfolded) |
| `LFMultigraph.exitGreen G U x y` | `MainResults.exitGreen G U x y` | verbatim |
| `dirichletEnergy f D hD hf` | `MainResults.dirichletEnergy f D hD hf` | verbatim ( FIX: `_hD : IsOpen D`) |
| `HasBoundedConvexity C D` | `MainResults.HasBoundedConvexity C D` | verbatim |
| `MatedCRT.cell ε η x` | `MainResults.cell ε η x` | verbatim |

The only textual change is the namespace (and hence dot notation `G.energyOn` becoming `MainResults.energyOn G`).
Imports are the draft's imports.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

section Graph

variable {V E : Type*} (G : LFMultigraph V E)

/-- **[18] Definition 1.1 on the sub-graph induced by `S`** (draft `LFMultigraph.energyOn`, verbatim body):
`Energy(g; G(S)) = ∑_{{x,y} ∈ E(G(S))} (g(x) − g(y))²`, the sum over the edges of `G` with both ends in `S`, parallel
edges counted with multiplicity; a loop contributes `0`. `ℝ≥0∞`-valued. -/
def energyOn (S : Set V) (g : V → ℝ) : ℝ≥0∞ :=
  ∑' e : {e : E // G.src e ∈ S ∧ G.tgt e ∈ S}, ENNReal.ofReal ((g (G.src e.1) - g (G.tgt e.1)) ^ 2)

/-- **[18] (1.6): `g` is the discrete harmonic function `f_ε` with boundary data `f`** (draft
`LFMultigraph.IsHarmonicExtension`, verbatim body): at `x ∈ V(D)`, if `x ∈ V(∂D)` then `g(x)` is the least upper bound
of `f` on `H_x ∩ ∂D`, and otherwise `g` is discrete harmonic at `x`. -/
def IsHarmonicExtension (H : V → Set ℂ) (D : Set ℂ) (f : ℂ → ℝ) (g : V → ℝ) : Prop :=
  ∀ x ∈ verticesMeeting H D,
    (x ∈ verticesMeeting H (frontier D) → IsLUB (f '' (H x ∩ frontier D)) (g x)) ∧
      (x ∉ verticesMeeting H (frontier D) → ∑ d ∈ G.outDarts x, (g x - g (G.dtgt d)) = 0)

/-- **The Tutte embedding with identity boundary data** (draft `LFMultigraph.IsTutteEmbedding`, verbatim body):
`Φ = Φ₁ + iΦ₂`, where `Φ₁` (resp. `Φ₂`) is the function `f_ε` of (1.6) for `f(z) = Re z` (resp. `f(z) = Im z`). -/
def IsTutteEmbedding (H : V → Set ℂ) (D : Set ℂ) (Φ : V → ℂ) : Prop :=
  IsHarmonicExtension G H D (fun z => z.re) (fun x => (Φ x).re) ∧
    IsHarmonicExtension G H D (fun z => z.im) (fun x => (Φ x).im)

end Graph

/-- **[18] Definition 1.2 for differentiable functions** (draft `dirichletEnergy` as fixed by S1V/, verbatim
body): `Energy(f; D) = ∫_D |∇f(z)|² dz`, for an open `D` (`_hD`) and `f` differentiable on `D` (`_hf`), so that
`fderiv ℝ f z` is the pointwise gradient at every `z ∈ D`. -/
def dirichletEnergy (f : ℂ → ℝ) (D : Set ℂ) (_hD : IsOpen D) (_hf : DifferentiableOn ℝ f D) : ℝ≥0∞ :=
  ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)

/-- **`C`-bounded convexity** (draft `HasBoundedConvexity`, verbatim body): any two points `z, w ∈ D` are joined by a
path in `D` of Euclidean length at most `C|z − w|`. -/
def HasBoundedConvexity (C : ℝ) (D : Set ℂ) : Prop :=
  ∀ z ∈ D, ∀ w ∈ D, ∃ c : ℝ → ℂ, ContinuousOn c (Icc 0 1) ∧ c 0 = z ∧ c 1 = w ∧
    MapsTo c (Icc 0 1) D ∧ eVariationOn c (Icc 0 1) ≤ ENNReal.ofReal (C * dist z w)

/-- **The cells of [18] (1.3)** (draft `MatedCRT.cell`, verbatim body): `H^ε_x = η([ε(x − 1), εx])` for the index
`x : ℤ` of the vertex `εx`. -/
def cell (ε : ℝ) (η : C(ℝ, ℂ)) (x : ℤ) : Set ℂ := η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)

end MatedCRTHarmonic.GMSMain.MainResults
