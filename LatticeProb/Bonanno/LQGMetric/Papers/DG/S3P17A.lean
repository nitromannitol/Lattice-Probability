/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18A
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17: `D^δ(K, ∂U)` is realized by paths in `Ū`

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17
(`prop-lfpp-lower0`, DG:1515–1591). DG apply Prop 3.16 (a bound for `D^δ(z,w;𝕊)`, paths in
`𝕊`) to `D^δ(K, ∂U)` for `K ⊂ U ⊂ 𝕊` (DG:1527, "By Proposition 3.16, it suffices …"); this uses
the implicit fact that a path from `z ∈ K` to `w ∈ ∂U` can be cut at its first exit from `U`,
which gives a path in `Ū ⊆ 𝕊` to a point of `∂U` with no larger LFPP length. Own elementary
argument (`LFPP.subPath`, `LFPP.lfppLen_subPath`).

* `p17_exit`: the cut path.
* `p17_setDist_ge`: `D^δ(K, ∂U) ≥ B` as soon as `D^δ(z, w'; S) ≥ B` for all `z ∈ K`,
  `w' ∈ ∂U`, where `Ū ⊆ S`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

/-- **first exit from `U`**: a DG path from `z ∈ U` to `w ∉ U` contains a DG path in `Ū` from
`z` to a point of `∂U` of no larger LFPP length (continuous `φ`). -/
theorem p17_exit {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {U S : Set ℂ} (hU : IsOpen U)
    {z w : ℂ} {p : ℝ → ℂ} (hp : IsDGPath S z w p) (hz : z ∈ U) (hw : w ∉ U) :
    ∃ w' ∈ frontier U, ∃ q, IsDGPath (closure U) z w' q ∧
      LQGDimension.lfppLength ξ φ q ≤ LQGDimension.lfppLength ξ φ p := by
  classical
  set T := {t ∈ Icc (0 : ℝ) 1 | p t ∉ U}
  have hT1 : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by rw [hp.target]; exact hw⟩
  have hTc : IsClosed T := hp.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
    hU.isClosed_compl
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set s := sInf T
  have hsT : s ∈ T := hTc.csInf_mem ⟨1, hT1⟩ hTb
  have hs0 : 0 < s := by
    rcases hsT.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hsT.2; rw [← h, hp.source]; exact hz
  have hs1 : s ≤ 1 := csInf_le hTb hT1
  have hbefore : ∀ t ∈ Icc (0 : ℝ) 1, t < s → p t ∈ U := fun t ht hts => by
    by_contra h
    exact absurd (csInf_le hTb ⟨ht, h⟩) (not_le.2 hts)
  -- `p s ∈ ∂U`
  have hps : p s ∈ frontier U := by
    rw [hU.frontier_eq]
    refine ⟨?_, hsT.2⟩
    have hcont : ContinuousWithinAt p (Ico 0 s) s :=
      (hp.continuousOn s hsT.1).mono (fun t ht => ⟨ht.1, ht.2.le.trans hs1⟩)
    have hmem : ∀ᶠ t in 𝓝[Ico 0 s] s, p t ∈ U :=
      eventually_nhdsWithin_of_forall fun t ht => hbefore t ⟨ht.1, ht.2.le.trans hs1⟩ ht.2
    have hne : (𝓝[Ico 0 s] s).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hs0.ne]
      exact ⟨hs0.le, le_rfl⟩
    exact mem_closure_of_tendsto hcont hmem
  have hpc : IsPiecewiseC1Path p z w :=
    ⟨hp.source, hp.target, hp.continuousOn, hp.piecewise_contDiff⟩
  have hsub := LFPP.isPiecewiseC1Path_subPath hpc le_rfl hs0 hs1
  have h0 : p 0 = z := hp.source
  refine ⟨p s, hps, LFPP.subPath p 0 s, ⟨by simpa [h0] using hsub.source, hsub.target,
    fun u hu => ?_, hsub.continuousOn, hsub.piecewise⟩, ?_⟩
  · show p ((s - 0) * u + 0) ∈ closure U
    have hu' : (s - 0) * u + 0 ∈ Icc (0 : ℝ) 1 :=
      ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    rcases (show (s - 0) * u + 0 ≤ s by nlinarith [hu.2]).lt_or_eq with h | h
    · exact subset_closure (hbefore _ hu' h)
    · rw [h]; exact frontier_subset_closure hps
  · have hq : IsDGPath univ (p 0) (p s) (LFPP.subPath p 0 s) :=
      ⟨hsub.source, hsub.target, mapsTo_univ _ _, hsub.continuousOn, hsub.piecewise⟩
    have e1 := t18_ofReal_lfppLength (ξ := ξ) hφ hq
    have e2 := t18_ofReal_lfppLength (ξ := ξ) hφ hp
    have hle : lfppLen ξ φ (LFPP.subPath p 0 s) ≤ lfppLen ξ φ p := by
      rw [LFPP.lfppLen_subPath p hs0, LFPP.lfppLen_eq]
      exact lintegral_mono_set (Icc_subset_Icc le_rfl hs1)
    rw [← e1, ← e2] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (lfppLength_nonneg _ _ _)).1 hle

/-- DG's `D^δ(K, ∂U)` read with paths stopped at `∂U`: the infimum of the LFPP lengths of the
DG paths in `Ū` from a point of `K` to a point of `∂U` (`⊤` if there is none). For a continuous
field it is `≤` the whole-plane `Blueprint.dgSetDist` (`p17SetDist_le`); for a field known only
on `𝕊 ⊇ Ū` (the circle averages of `h^{𝕊(1)}`) it is the meaningful one. -/
def p17SetDist (ξ : ℝ) (φ : ℂ → ℝ) (K U : Set ℂ) : ℝ≥0∞ :=
  ⨅ z ∈ K, ⨅ w ∈ frontier U, ⨅ q : {q : ℝ → ℂ // IsDGPath (closure U) z w q},
    ENNReal.ofReal (LQGDimension.lfppLength ξ φ q.1)

/-- **`D^δ(K, ∂U)` is realized by paths in `Ū`** (continuous field) -/
theorem p17SetDist_le {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {K U : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) : p17SetDist ξ φ K U ≤ Blueprint.dgSetDist ξ φ K U := by
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
  have hwU : w ∉ U := fun h => (hU.frontier_eq ▸ hw).2 h
  have hne : Nonempty {p : ℝ → ℂ // IsDGPath univ z w p} :=
    ⟨⟨_, t18_isDGPath_segment convex_univ (mem_univ z) (mem_univ w)⟩⟩
  unfold dgLFPP
  rw [Monotone.map_ciInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    (fun _ _ h => ENNReal.ofReal_le_ofReal h) (bddBelow_dg ξ φ univ z w)]
  refine le_iInf fun p => ?_
  obtain ⟨w', hw', q, hq, hlen⟩ := p17_exit hφ hU p.2 (hKU hz) hwU
  exact (iInf₂_le_of_le z hz (iInf₂_le_of_le w' hw' (iInf_le_of_le
      (⟨q, hq⟩ : {q : ℝ → ℂ // IsDGPath (closure U) z w' q}) le_rfl))).trans
    (ENNReal.ofReal_le_ofReal hlen)

/-- lower bounds for `p17SetDist` from lower bounds of `D(z, w; S)`, `Ū ⊆ S` -/
theorem p17SetDist_ge {ξ : ℝ} {φ : ℂ → ℝ} {K U S : Set ℂ} (hUS : closure U ⊆ S) {B : ℝ}
    (hB : ∀ z ∈ K, ∀ w ∈ frontier U, B ≤ dgLFPP ξ φ S z w) :
    ENNReal.ofReal B ≤ p17SetDist ξ φ K U := by
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => le_iInf fun q => ENNReal.ofReal_le_ofReal ?_
  have hqS : IsDGPath S z w q.1 :=
    ⟨q.2.source, q.2.target, q.2.mapsTo.mono_right hUS, q.2.continuousOn, q.2.piecewise_contDiff⟩
  exact (hB z hz w hw).trans (ciInf_le (bddBelow_dg ξ φ S z w) ⟨q.1, hqS⟩)

end LQGMetric.DG
