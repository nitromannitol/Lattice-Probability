/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.WedgeFieldMol at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.Field
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIndep
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower2
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFF
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeRC3All2Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3

/-!
For `g : ℝ → ℝ` measurable, continuous on `(0, ∞)` with `|g t| ≤ C (1 − log t)` on `(0, 1]`
(the hypotheses of QuantumZipper's `F1.RC3Two` circle-smoothing lemmas, `WedgeRC3All2Basic.lean`),
and `f = rp g = g ∘ ‖·‖`:

* `locallyIntegrable_rp`: `f` is locally integrable on `ℂ`, so `ofFunC f` is the distribution
  `φ ↦ ∫ φ f`;
* `toFS_ofFunC_rp_fc`: for every folded circle `fc(w, ρ)`, `ρ > 0` (also through `0`),
  `toFS (ofFunC f) (fc w ρ) = ∫ f d fc(w, ρ)`.

Route (the radial-mollifier analogue of QZ `RC3Two.tendsto_integral_smoothFun_rp`):
`⟨ofFunC f, η_ε ∗ μ⟩ = ∫ (η_ε ⋆ f) dμ` (Fubini, `integral_molFun_mul`); `(η_ε ⋆ f)(z) → f(z)` at
every `z ≠ 0` (continuity); domination `|(η_ε ⋆ f)(z)| ≤ K (1 + log R' − log ‖z‖)` from the
mean-value inequality for the superharmonic function `−log|·|` under radial mollification
(`Bridge.lintegral_mul_ηε_le`, BridgeDet1.lean, adapted from QZ `K3.Kε_le`, with QZ's circle means
`CircleMV.integral_log_norm_sub_circleUnif`); dominated convergence on `fc(w, ρ)`, where `log‖·‖`
is integrable (QZ `CoordReg.integrable_log_norm_foldedCircle`).
Own elementary argument (cost rule; standard mollifier convergence).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open QuantumZipper QuantumZipper.K3

namespace MatedCRTHarmonic.MoTPort
namespace WedgeFieldMol

open QuantumZipper.F1.RC3Two

variable {g : ℝ → ℝ} {C : ℝ}

/-- the log-type majorant `1 + log R − log ‖u‖` -/
def logMaj (R : ℝ) (u : ℂ) : ℝ := 1 + Real.log R - Real.log ‖u‖

/-- the profile is dominated by a multiple of `1 + log R − log t` on `(0, R]` -/
theorem exists_bd (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) {R : ℝ} (hR : 1 ≤ R) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 < t → t ≤ R → |g t| ≤ K * (1 + Real.log R - Real.log t) := by
  have hC := nonneg_of_bd hbd
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := R)).exists_bound_of_continuousOn
    (hgc.mono fun t ht => lt_of_lt_of_le one_pos ht.1)
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  refine ⟨C + |M|, by positivity, fun t ht htR => ?_⟩
  rcases le_total t 1 with h1 | h1
  · have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le h1
    have := hbd t ht h1
    have p : 0 ≤ 1 - Real.log t := by linarith
    nlinarith [abs_nonneg M]
  · have hl : Real.log t ≤ Real.log R := Real.log_le_log ht htR
    have := hM t ⟨h1, htR⟩
    rw [Real.norm_eq_abs] at this
    have p : 1 ≤ 1 + Real.log R - Real.log t := by linarith
    nlinarith [le_abs_self M, abs_nonneg M]

theorem measurable_rp (hgm : Measurable g) : Measurable (rp g) := hgm.comp measurable_norm

theorem ae_ne_zero_volume : ∀ᵐ u : ℂ ∂volume, u ≠ 0 := by
  rw [ae_iff]; simp

/-- `rp g` is locally integrable on `ℂ` -/
theorem locallyIntegrable_rp (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) :
    LocallyIntegrable (rp g) volume := by
  rw [locallyIntegrable_iff]
  intro S hS
  obtain ⟨R₀, hR₀⟩ := hS.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hRdef
  have hR : 1 ≤ R := le_max_right _ _
  obtain ⟨K, hK, hKb⟩ := exists_bd hgc hbd hR
  have hsub : S ⊆ closedBall (0 : ℂ) R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  refine IntegrableOn.mono_set ?_ hsub
  have hlog : IntegrableOn (fun u : ℂ => Real.log ‖u‖) (closedBall (0 : ℂ) R) :=
    locallyIntegrable_log_norm.integrableOn_isCompact (isCompact_closedBall 0 R)
  have hmaj : IntegrableOn (fun u => K * logMaj R u) (closedBall (0 : ℂ) R) := by
    unfold logMaj
    exact ((integrableOn_const (isCompact_closedBall 0 R).measure_lt_top.ne).sub hlog).const_mul K
  refine hmaj.mono' (measurable_rp hgm).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_closedBall]
  filter_upwards [ae_ne_zero_volume] with u hu hub
  rw [Real.norm_eq_abs]
  exact hKb ‖u‖ (norm_pos_iff.2 hu) (by simpa using hub)

/-! ## Radial mollification -/

/-! ## Fubini and the limit -/

end WedgeFieldMol
end MatedCRTHarmonic.MoTPort
