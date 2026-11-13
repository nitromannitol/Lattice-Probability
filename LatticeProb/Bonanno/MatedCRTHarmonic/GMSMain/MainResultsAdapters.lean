/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.MainResultsAdapters at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.MainResultsStatements
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T16DSurface
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsALemma27
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.TopoMain
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BStatement
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13Energy
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Recurrence
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Walk

/-!
# Adapters between the main-result definitions and their equivalent forms

Deterministic identities between the seven draft definitions (`MainResultsDraft`, verbatim copies of the draft surface v5)
and the vocabulary used in the [18] proofs:

* `energyOn_coe_finset`: `MainResults.energyOn G ↑S g = ofReal (GMS3.energy G S g)` for a `Finset S` (Definition 1.1);
* `exitGreen_coe_finset`: `MainResults.exitGreen G ↑U a a = GMS3.green G a U` (`rfl`; [18]);
* `dirichletEnergy_eq_eucEnergy`, `hasBoundedConvexity_iff`: `rfl` with `GMS3.eucEnergy` and T13I's
  `BoundedConvexityWith`;
* `cell_eq_cellAt`, `isHarmonicExtension_iff_t16d`, `isTutteEmbedding_iff_t16d`: `rfl` with T16D's local copies;
* `isHarmonicExtension_iff_t15b`: the `IsLUB` form is T15B's `sSup` form (compact cells, `f` continuous on `∂D`);
* `verticesMeeting_eq_vFin`, `isGMSDirichletSolution_of_isHarmonicExtension`: for a cellular embedding `H` and a
  bounded `D`, `V(D)` is the `Finset` `GMS3.vFin H D`, and every function `f_ε` of the draft (1.6) is a solution in
  T13I's sense (`IsGMSDirichletSolution`);
* `ofReal_le_div_deg`: the (1.8) normalizations `log ε⁻¹/A · deg(0) ≤ Gr` and `(1/A) log ε⁻¹ ≤ Gr / deg(0)` agree.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

section Graph

variable {V E : Type*} (G : LFMultigraph V E)

/-- **The draft energy on a finite vertex set is GMS3's energy**: `Energy(g; G(S))` of [18] Definition 1.1. -/
theorem energyOn_coe_finset (S : Finset V) (g : V → ℝ) :
    energyOn G (S : Set V) g = ENNReal.ofReal (GMS3.energy G S g) := by
  classical
  have hset : {e : E | G.src e ∈ (S : Set V) ∧ G.tgt e ∈ (S : Set V)} = ((edgesIn G S : Finset E) : Set E) := by
    ext e
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_edgesIn]
  have h1 : energyOn G (S : Set V) g =
      ∑' e : ({e : E | G.src e ∈ (S : Set V) ∧ G.tgt e ∈ (S : Set V)} : Set E),
        ENNReal.ofReal ((g (G.src e.1) - g (G.tgt e.1)) ^ 2) := rfl
  rw [h1, hset, Finset.tsum_subtype' (edgesIn G S)
    (fun e => ENNReal.ofReal ((g (G.src e) - g (G.tgt e)) ^ 2)), GMS3.energy,
    ENNReal.ofReal_sum_of_nonneg (fun e _ => sq_nonneg _)]

end Graph

section Embedding

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- For a bounded `D`, `V(D)` is GMS3's `Finset` `vFin H D`. -/
theorem verticesMeeting_eq_vFin {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    verticesMeeting H.cell D = (vFin H D : Set V) := by
  ext x
  rw [Finset.mem_coe, mem_vFin H hDb]
  rfl

/-- **Every function `f_ε` of the draft (1.6) solves T13I's Dirichlet problem** (`IsGMSDirichletSolution`). -/
theorem isGMSDirichletSolution_of_isHarmonicExtension {D : Set ℂ} (hDb : Bornology.IsBounded D) {f : ℂ → ℝ}
    {g : V → ℝ} (hg : IsHarmonicExtension G H.cell D f g) : GMSMain.IsGMSDirichletSolution H D f g := by
  refine ⟨fun x hx hxB => ?_, fun x hx hxB => ?_⟩
  · have hx' : x ∈ verticesMeeting H.cell D := (mem_vFin H hDb).mp hx
    have hlub := (hg x hx').1 hxB
    exact (hlub.csSup_eq (hxB.image f)).symm
  · have hx' : x ∈ verticesMeeting H.cell D := (mem_vFin H hDb).mp hx
    exact (hg x hx').2 hxB

/-- **The draft energy on `V(D)` is GMS3's energy on `vFin H D`.** -/
theorem energyOn_verticesMeeting {D : Set ℂ} (hDb : Bornology.IsBounded D) (g : V → ℝ) :
    energyOn G (verticesMeeting H.cell D) g = ENNReal.ofReal (GMS3.energy G (vFin H D) g) := by
  rw [verticesMeeting_eq_vFin H hDb, energyOn_coe_finset]

end Embedding

end MatedCRTHarmonic.GMSMain.MainResults
