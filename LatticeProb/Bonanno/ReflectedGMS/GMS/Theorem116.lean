/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.Theorem116 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.GeomTopTransfer
import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkIdentification
import LatticeProb.Bonanno.ReflectedGMS.GMS.InterpolatedConvergence
import Mathlib.Util.AssertNoSorry

/-!
# Gwynne–Miller–Sheffield, Theorem 1.16 — proved

`theorem1_16 : Theorem1_16` (statement: `ReflectedGMS/GMS/Theorem116Statement.lean`).

The proof is the manuscript's Corollary 22.1: GMS Theorem 1.16 is a short corollary of **Theorem 1.3
of the geometric-topology revision** (`GeomTop.geomReflectedInvarianceMainTheorem`), applied to the
image `μ.map GeomTop.toSing` of a GMS law `μ` in the singular configuration space `C_sing` (the case
of empty singular set):

* **inclusion** (`GeomTop/GMSInclusion.lean`, `GeomTop/GMSTopology.lean`, Proposition 2.5): every GMS
  cell configuration lies in `C_sing`, and the inclusion `toSing` is a topological embedding for
  GMS's `d^CC` and the geometric topology, hence Borel;
* **hypothesis transfer** (`GMS/GeomTopTransfer.lean`, Corollary 2.8): GMS's mass transport
  (Definition 1.2(4)), ergodicity modulo scaling, finite expectation and connectedness along lines
  give (1.4), ergodicity, (FE), and Definition 1.1 + (LCS) on a Borel probability-one set for the
  image law; the auxiliary coordinates of the image are GMS's labelled code (`GMS/CodingValid.lean`,
  with the bijection `cellEquiv` between labels and cells preserving cells and conductances), so the
  environment law `ν` produced by Theorem 1.3 has raw law `μ.map codeMap`, and its almost-sure
  conclusions pull back to `μ` (`ae_of_ae_of_map_val_eq`);
* **walk identification** (`GMS/Walk*.lean`): with empty singular set every graph end is at spatial
  infinity, so the exact-holding-time reflected walk never takes an end state; its jump chain has
  GMS's simple-random-walk law, its jump times are the partial sums of `Area/π`, and GMS's
  interpolated walk is almost surely its linear interpolation; recurrence and the discrete harmonic
  sublinear `φ_∞` follow;
* **convergence** (`GMS/InterpolatedConvergence.lean`): weak convergence in `C([0,∞), ℂ)` of the
  interpolation through an arbitrary point of each cell.

Notes recorded by the recursive fidelity audit (`outputs/gms/recursive-fidelity-audit.md`):

* the conclusion is **stronger** than GMS's in its quantifiers: one almost-sure event serves every
  starting cell `K₀`, every realization `Q` of the jump chain, and **every** point choice `p`, with one
  limit law;
* in the statement, `jumpCount` takes the value `0` on explosion paths and `interpolatedWalk` uses the
  placeholder `0` when the rescaled interpolation is not continuous; both situations are almost surely
  absent (the walk is recurrent and never explodes — proved here), so neither affects the theorem;
* GMS's `H₀` ("the cell containing `0`, chosen in some arbitrary manner") enters `FiniteExpectation`
  existentially, possibly non-measurably; under mass transport the origin lies in exactly one cell
  almost surely, so every choice gives the same expectations.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal

namespace ReflectedGMS.GMS

open Code EnvironmentLaws HarmonicMainStatement InvarianceMainStatement GeneralLaws
open EnvironmentFields StatementIngredients AreaClocks SpatialEnds

/-- **The per-configuration conclusions of Theorem 1.16**, from the reflected-walk conclusions at the
code of a configuration that is connected along lines. -/
theorem theorem1_16_conclusions_of_processConclusions {H : GMSSpace} (hL : H.1.LineConnected)
    (hv : Valid H.1.code) {Φ : CellField} {target : StatementIngredients.AnisotropicBrownianTarget}
    (hproc : EnvironmentProcessConclusions ⟨H.1.code, hv⟩ Φ target)
    (hdh : DiscreteHarmonicity Φ ⟨H.1.code, hv⟩) (hsub : SublinearCorrector Φ ⟨H.1.code, hv⟩)
    (z : CellField) (hz : IsCellRepresentative z) :
    (∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
        ∀ p : H.1.cells → Plane, (∀ K : H.1.cells, p K ∈ ((K : Cell) : Set Plane)) →
          ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) ∧
      H.1.Recurrent ∧
      ∃ φ : H.1.cells → Plane, H.1.DiscreteHarmonic φ ∧ H.1.SublinearToCentroid φ := by
  let e : Env := ⟨H.1.code, hv⟩
  have hgeo : GMSGeometry (decode e).toCellConfiguration := CellConfig.gmsGeometry_code H.2 hL
  let σ : Vertex e.val ≃ H.1.cells := CellConfig.cellEquiv H.2
  have hcell : ∀ v, ((σ v : H.1.cells) : Cell) = (decode e).cell v :=
    fun v => CellConfig.coe_cellEquiv H.2 v
  have hc : ∀ v w, H.1.c (σ v) (σ w) = (decode e).graph.c v w :=
    fun v w => (CellConfig.code_cond H.2 v w).symm
  obtain ⟨hnt, hrest⟩ := hproc
  haveI := hnt
  obtain ⟨D, hG, hmin, hpos, hwalk, -, hfix⟩ := hrest
  refine ⟨?_, WalkIdentification.recurrent_of_fixedStartConclusions σ hgeo hpos hwalk hfix hc,
    WalkIdentification.exists_discreteHarmonic_sublinearToCentroid σ hcell hc hdh hsub⟩
  intro K₀ Q hQ p hp G hGc hGb
  have hQ' : H.1.IsSRWLaw (σ (σ.symm K₀)) Q := by rwa [Equiv.apply_symm_apply]
  have hconv := InterpolatedConvergence.convergesWeaklyInC_interpolated e D hG Φ target
    (σ.symm K₀) (hfix (σ.symm K₀)) z hz (fun v => p (σ v))
    (fun v => by rw [← hcell v]; exact hp (σ v))
    (WalkIdentification.ae_exactAreaPath_ne_none hgeo hpos hwalk (hfix (σ.symm K₀)))
    (WalkIdentification.interpolation e D (σ.symm K₀) H.1 σ p)
    (WalkIdentification.ae_interpolation_segment σ hgeo hpos hwalk (hfix (σ.symm K₀)) hcell hc p)
    G hGc hGb
  refine hconv.congr (fun ε => ?_)
  exact (WalkIdentification.integral_interpolatedWalk_eq σ hgeo hpos hwalk (hfix (σ.symm K₀))
    hcell hc hQ' p ε hGc.measurable).symm

/-- **Gwynne–Miller–Sheffield, Theorem 1.16**, as a corollary of Theorem 1.3 of the
geometric-topology revision (Corollary 22.1). -/
theorem theorem1_16 : Theorem1_16 := by
  intro μ _ hMT hErg hFE hL
  obtain ⟨-, hvalid, -, ν, _, hν, hconc, -⟩ := GeomTop.geomReflectedInvarianceMainTheorem
    (μ.map GeomTop.toSing) (lcsOnMeasurableSet_map_toSing hL) (massTransport_map_toSing hMT)
    (finiteEnergyMoment_map_toSing hL hFE) (environmentErgodic_map_toSing hErg)
  rw [map_coords_map_toSing] at hν
  obtain ⟨Φ, target, hΦ, -, -, ⟨z, hz, -⟩, hproc⟩ := hconc.toReflectedInvarianceConclusions
  have key := ae_of_ae_of_map_val_eq hν (ae_of_ae_map measurable_toSing.aemeasurable hvalid)
    (hproc.and hΦ.2.2.2.2.1)
  have hall : ∀ᵐ H ∂μ,
      (∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
        ∀ p : H.1.cells → Plane, (∀ K : H.1.cells, p K ∈ ((K : Cell) : Set Plane)) →
          ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) ∧
      H.1.Recurrent ∧
      ∃ φ : H.1.cells → Plane, H.1.DiscreteHarmonic φ ∧ H.1.SublinearToCentroid φ := by
    filter_upwards [key, (connectedAlongLines_iff μ).1 hL] with H hH hLH
    obtain ⟨hv, hpe, -, -, -, hdh, hsub⟩ := hH
    exact theorem1_16_conclusions_of_processConclusions hLH hv hpe hdh hsub z hz
  exact ⟨target, hall.mono fun _ h => h.1, hall.mono fun _ h => h.2.1,
    hall.mono fun _ h => h.2.2⟩

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.theorem1_16
#print axioms ReflectedGMS.GMS.theorem1_16
