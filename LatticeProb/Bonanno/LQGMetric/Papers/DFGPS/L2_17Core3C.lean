/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3B
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2F

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the Weyl relation along one Skorokhod sample (item R1)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3 (T:1248–1251, "by the analog of Lemma 2.12 … along this same subsequence") and Step 4
(T:1271, `D_h = e^{ξφ𝔥}·D_{h−φ𝔥}`); Lemma 2.12 (T:1026–1051) in its form with fields varying
with `n` (`weyl_lfpp_varying`, L2_17Core2F.lean).

* `lfppC_apply_eq` — `lfppC ξ ε g = 𝔞_ε⁻¹ D^ε_g` when `g*_ε` is continuous.
* `weyl_of_sample` — deterministic: if `𝔞⁻¹D^{εₙ}_{gₙ} → D` (compact-open, `D` a length metric
  with the a.s. property `hA` of Lemma 2.8), `fₙ → F` with supports in a fixed compact and
  `𝔞⁻¹D^{εₙ}_{gₙ + fₙ} → a`, then `a = e^{ξF}·D`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.L217

open Blueprint MetricGeometry LFPP

theorem lfppC_apply_eq {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g)) (p : ℂ × ℂ) :
    lfppC ξ ε g p = (aEpsDF ξ ε)⁻¹ * lfppDist ξ ε g p := by
  have e : (fun p : ℂ × ℂ => (aEpsDF ξ ε)⁻¹ * lfppDist ξ ε g p) =
      fun p => (aEpsDF ξ ε)⁻¹ * lfppDReal ξ (heatMollify ε g) p := by
    funext p; simp only [lfppDist, lfppDReal, lfppDistE_eq_lfppDOn]
  have hcont : Continuous fun p : ℂ × ℂ => (aEpsDF ξ ε)⁻¹ * lfppDist ξ ε g p := by
    rw [e]; exact continuous_const.mul (continuous_lfppDReal hc)
  exact toCMap_apply_of_continuous hcont p

/-- a convergent sequence in `C(ℂ, ℝ)` with supports in a fixed compact is uniformly bounded -/
theorem exists_bound_of_tendsto_supp {f : ℕ → C(ℂ, ℝ)} {F : C(ℂ, ℝ)}
    (hf : Tendsto f atTop (𝓝 F)) {K : Set ℂ} (hK : IsCompact K)
    (hsupp : ∀ n, ∀ z ∉ K, f n z = 0) :
    ∃ M, (∀ n z, |f n z| ≤ M) ∧ ∀ z, |F z| ≤ M := by
  have hc : IsCompact (insert F (range f) ×ˢ K) := hf.isCompact_insert_range.prod hK
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (continuous_eval : Continuous fun p : C(ℂ, ℝ) × ℂ => p.1 p.2).continuousOn
  have hF0 : ∀ z ∉ K, F z = 0 := fun z hz =>
    tendsto_nhds_unique ((continuous_eval_const z).continuousAt.tendsto.comp hf)
      (by simp only [Function.comp_def, hsupp _ z hz]; exact tendsto_const_nhds)
  refine ⟨max C 0, fun n z => ?_, fun z => ?_⟩
  · by_cases hz : z ∈ K
    · exact (hC (f n, z) ⟨mem_insert_of_mem _ (mem_range_self n), hz⟩).trans (le_max_left _ _)
    · rw [hsupp n z hz, abs_zero]; exact le_max_right _ _
  · by_cases hz : z ∈ K
    · exact (hC (F, z) ⟨mem_insert _ _, hz⟩).trans (le_max_left _ _)
    · rw [hF0 z hz, abs_zero]; exact le_max_right _ _

/-- **The Weyl relation along one sample** (T:1248–1251 with Lemma 2.12): deterministic. -/
theorem weyl_of_sample (ξ : ℝ) {εs : ℕ → ℝ} (hεp : ∀ n, 0 < εs n)
    (hε0 : Tendsto εs atTop (𝓝 0)) {g : ℕ → DistC}
    (hreg : ∀ n, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => g n (heatTrunc (εs n ^ 2 / 2) z k)) (heatMollify (εs n) (g n))
        atTop ∧ Continuous (heatMollify (εs n) (g n)))
    {f : ℕ → C(ℂ, ℝ)} {F : C(ℂ, ℝ)} (hf : Tendsto f atTop (𝓝 F)) {K : Set ℂ} (hK : IsCompact K)
    (hsupp : ∀ n, ∀ z ∉ K, f n z = 0)
    (hreg' : ∀ n, Continuous (heatMollify (εs n) (addFun (g n) (f n))))
    {a : C(ℂ × ℂ, ℝ)} (ha : Tendsto (fun n => lfppC ξ (εs n) (addFun (g n) (f n))) atTop (𝓝 a))
    {D : ContMetric} (hD : D.IsLength)
    (hA : ∀ k r : ℕ, ∃ s : ℕ, D.1 ∈ agreeSetK ((k : ℝ) + 1) ((r : ℝ) + 1) s)
    (hb : Tendsto (fun n => lfppC ξ (εs n) (g n)) atTop (𝓝 D.1)) (u v : ℂ) :
    ENNReal.ofReal (a (u, v)) = weylScale ξ F D u v := by
  obtain ⟨M, hfM, hFM⟩ := exists_bound_of_tendsto_supp hf hK hsupp
  have hcv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF ξ (εs n))⁻¹ * lfppDist ξ (εs n) (g n) p) (fun p => D.1 p) atTop
        (closedBall 0 R ×ˢ closedBall 0 R) := fun R _ => by
    have := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hb _
      ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R))
    refine this.congr (Eventually.of_forall fun n => ?_)
    intro p _
    exact lfppC_apply_eq (hreg n).2 p
  have hfc : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(f n)) ⇑F atTop (closedBall 0 R) :=
    fun R _ => ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hf _
      (isCompact_closedBall (0 : ℂ) R)
  set R : ℝ := max ‖u‖ ‖v‖ + 1
  have hR : 0 < R := by positivity
  have huv : (u, v) ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R :=
    ⟨by rw [mem_closedBall, dist_zero_right]; linarith [le_max_left ‖u‖ ‖v‖],
      by rw [mem_closedBall, dist_zero_right]; linarith [le_max_right ‖u‖ ‖v‖]⟩
  have H := (weyl_lfpp_varying ξ hεp hε0 hreg hD hA hcv f F M hfM hFM hfc R hR).tendsto_at huv
  have H' : Tendsto (fun n => lfppC ξ (εs n) (addFun (g n) (f n)) (u, v)) atTop
      (𝓝 (a (u, v))) := (continuous_eval_const (u, v)).continuousAt.tendsto.comp ha
  have e : (fun n => lfppC ξ (εs n) (addFun (g n) (f n)) (u, v)) = fun n =>
      (aEpsDF ξ (εs n))⁻¹ * lfppDist ξ (εs n) (addFun (g n) (f n)) (u, v) := by
    funext n; exact lfppC_apply_eq (hreg' n) _
  rw [e] at H'
  have hau := tendsto_nhds_unique H' H
  simp only at hau
  rw [hau, ENNReal.ofReal_toReal (weylScale_ne_top hD u v)]

end L217

end LQGMetric.DFGPS
