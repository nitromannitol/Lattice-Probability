/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_13Scale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_13Conv
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6Law
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofTightA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinCmp
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFarA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Proof
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.13, packets 1 and 3: the scaled LFPP metric and its limit

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.13
(`lem-lfpp-coord`) T:1104–1119; DEC-78 §4.

* `map_lfppC_fieldScale`, `ae_lfppC_fieldScale` (eqn-scaled-lfpp-tight, T:1108–1111): with
  `h^r = h(r·) − h_r(0)`, `𝔞_{ε/r}⁻¹ D^{ε/r}_{h^r} =ᵈ 𝔞_{ε/r}⁻¹ D^{ε/r}_h` and a.s.
  `𝔞_{ε/r}⁻¹ D^{ε/r}_{h^r} = e^{−ξ h_r(0)} (r 𝔞_{ε/r}/𝔞_ε)⁻¹ 𝔞_ε⁻¹ D^ε_h(r·, r·)` (Lemma 2.6).
* `tendsto_law_scaled` (T:1114–1116): along a subsequence on which `r 𝔞_{ε/r}/𝔞_ε → 𝔠_r`, the
  laws of the left side converge to the law of `𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(r·, r·)`. The circle
  average is approximated a.s. by the continuous pairings `h ↦ ⟨h, σ_{0,r} * ψ_m⟩`
  (`CircleAvg.circleAverage_pairing`, `CircleAvg.ae_tendsto_mollAvg`), see `L2_13Conv`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint

namespace L213

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- `𝔞_{δ}⁻¹ D^δ_{h^r} =ᵈ 𝔞_δ⁻¹ D^δ_h` for a normalized whole-plane GFF (T:1105, `h^r =ᵈ h`). -/
theorem map_lfppC_fieldScale (hh : IsNormalizedWPGFF h P) (ξ : ℝ) {δ r : ℝ} (hδ : δ ≠ 0)
    (hr : 0 < r) :
    P.map (fun ω => lfppC ξ δ (fieldScale r (h ω))) = P.map (fun ω => lfppC ξ δ (h ω)) := by
  have hF : AEMeasurable (lfppC ξ δ) (P.map h) :=
    aemeasurable_lfppC (h := id) (isGFFPlusBddCont_of_wp (GM.isWholePlaneGFF_id_map hh.1)) hδ
  have hs := (isWholePlaneGFF_fieldScale hh.1 hr).measurable
  have hF' : AEMeasurable (lfppC ξ δ) (P.map fun ω => fieldScale r (h ω)) := by
    rw [map_fieldScale hh hr]; exact hF
  have e1 := AEMeasurable.map_map_of_aemeasurable hF' hs.aemeasurable
  have e2 := AEMeasurable.map_map_of_aemeasurable hF hh.1.measurable.aemeasurable
  rw [map_fieldScale hh hr] at e1
  exact e1.symm.trans e2

/-- **Lemma 2.6 for `lfppC`** (eqn-scaled-lfpp-tight, T:1108–1111). -/
theorem ae_lfppC_fieldScale (hh : IsWholePlaneGFF h P) (ξ : ℝ) {ε r : ℝ} (hε : 0 < ε)
    (hr : 0 < r) (ha : aEpsDF ξ ε ≠ 0) :
    ∀ᵐ ω ∂P, lfppC ξ (ε / r) (fieldScale r (h ω)) =
      ((r * aEpsDF ξ (ε / r) / aEpsDF ξ ε)⁻¹ * Real.exp (-ξ * circleAvg (h ω) r 0)) •
        (lfppC ξ ε (h ω)).comp (scaleArgs r) := by
  have hεr : ε / r ≠ 0 := div_ne_zero hε.ne' hr.ne'
  filter_upwards [lem2_6 hh ξ hε hr, hh.ae_tendstoLocallyUniformly_heatMollify ε hε.ne',
    (isWholePlaneGFF_fieldScale hh hr).ae_tendstoLocallyUniformly_heatMollify (ε / r) hεr]
    with ω h6 hc hc'
  ext p
  rw [ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul,
    lfppC_apply_of_continuous hc'.2, lfppC_apply_of_continuous hc.2]
  have e1 := h6 p.1 p.2
  simp only [fieldScale] at e1 ⊢
  rw [e1, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  show _ = _ * ((aEpsDF ξ ε)⁻¹ * (lfppDistE ξ ε (h ω) ((r : ℂ) * p.1) ((r : ℂ) * p.2)).toReal)
  rcases eq_or_ne (aEpsDF ξ (ε / r)) 0 with h0 | h0
  · simp [h0]
  · field_simp

end L213

end LQGMetric.DFGPS
