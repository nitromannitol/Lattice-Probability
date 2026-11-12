/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core2F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_12

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.12 for a varying field (tool for step C5 (iii) of Lemma 2.17)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 2.12
(`lem-weyl-scaling`, T:1026–1031, proof T:1035–1048) and its use in Lemma 2.17, Step 3
(T:1248–1251: "By the analog of Lemma 2.12 …").

The proof of Lemma 2.12 (`lem2_12`) is deterministic once the field is fixed: it uses, for each
`n`, only that `heatMollify εₙ (field)` is continuous with the heat-truncation convergence, and,
for the limit `D`, that it is a length metric in the sets `agreeSetK` (eqn-square-bdy-weyl).
`weyl_lfpp_varying` states it for a **different field `gₙ` for each `n`**: this is what a
Skorokhod coupling of `(h, 𝔞⁻¹D^εₙ_h)` produces (the field of the `n`-th coordinate varies with
`n`; a coupling with a fixed field does not exist in general). Same proof as `lem2_12`
(`dfLem7_1`, DF = Dubédat–Falconet arXiv:1809.02607 Lemma 7.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

open Blueprint MetricGeometry LFPP

/-- **Lemma 2.12, deterministic form for varying fields** (T:1035–1048) -/
theorem weyl_lfpp_varying (ξ : ℝ) {εn : ℕ → ℝ} (hεp : ∀ n, 0 < εn n)
    (hε0 : Tendsto εn atTop (𝓝 0)) {g : ℕ → DistC}
    (hc : ∀ n, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => g n (heatTrunc (εn n ^ 2 / 2) z k)) (heatMollify (εn n) (g n))
        atTop ∧ Continuous (heatMollify (εn n) (g n)))
    {D : ContMetric} (hD : D.IsLength)
    (hA : ∀ k r : ℕ, ∃ s : ℕ, D.1 ∈ agreeSetK ((k : ℝ) + 1) ((r : ℝ) + 1) s)
    (hcv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF ξ (εn n))⁻¹ * lfppDist ξ (εn n) (g n) p) (fun p => D.1 p) atTop
        (closedBall 0 R ×ˢ closedBall 0 R))
    (fn : ℕ → C(ℂ, ℝ)) (f : C(ℂ, ℝ)) (M : ℝ) (hfnM : ∀ n z, |fn n z| ≤ M)
    (hfM : ∀ z, |f z| ≤ M)
    (hfconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop (closedBall 0 R))
    (R : ℝ) (hR : 0 < R) :
    TendstoUniformlyOn
      (fun n (p : ℂ × ℂ) => (aEpsDF ξ (εn n))⁻¹ * lfppDist ξ (εn n) (addFun (g n) (fn n)) p)
      (fun p => (weylScale ξ f D p.1 p.2).toReal) atTop
      (closedBall 0 R ×ˢ closedBall 0 R) := by
  set a : ℕ → ℝ := fun n => aEpsDF ξ (εn n)
  -- `𝔞_{ε_n} > 0` for large `n`
  have hpos : ∀ᶠ n in atTop, 0 < a n := by
    have h01 : ((0 : ℂ), (1 : ℂ)) ∈ closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1 :=
      ⟨mem_closedBall_self zero_le_one, by simp⟩
    have ht := (hcv 1 one_pos).tendsto_at h01
    have hD0 : 0 < D.1 (0, 1) := by
      refine lt_of_le_of_ne (dist_nonneg (x := D.pt 0) (y := D.pt 1)) fun h0 => ?_
      exact one_ne_zero (D.2.eq_of_eq_zero 0 1 h0.symm).symm
    filter_upwards [ht.eventually (lt_mem_nhds hD0)] with n hn
    refine lt_of_le_of_ne (aEpsDF_nonneg_sq _ _) fun h0 => ?_
    simp only [a, ← h0, inv_zero, zero_mul] at hn
    exact lt_irrefl _ hn
  set Dn : ℕ → ContMetric := fun n => if ha : 0 < a n then
    (lfppDistCM ξ (εn n) (g n) (hc n).2).smul (a n)⁻¹ (inv_pos.2 ha)
    else lfppDistCM ξ (εn n) (g n) (hc n).2
  have hDn : ∀ n (ha : 0 < a n),
      Dn n = (lfppDistCM ξ (εn n) (g n) (hc n).2).smul (a n)⁻¹ (inv_pos.2 ha) := by
    intro n ha; simp only [Dn, ha, ↓reduceDIte]
  have hDnlen : ∀ n, (Dn n).IsLength := by
    intro n
    by_cases ha : 0 < a n
    · rw [hDn n ha]; exact isLength_smul_L212 _ (isLength_lfppDistCM _ _ _ _)
    · simp only [Dn, ha, ↓reduceDIte]; exact isLength_lfppDistCM _ _ _ _
  set gn : ℕ → C(ℂ, ℝ) := fun n => mollCont (εn n) (hεp n).ne' (fn n) M (hfnM n)
  have hgM : ∀ n z, |gn n z| ≤ M := fun n z =>
    abs_heatMollify_ofCont_le (fn n) (hfnM n) (hεp n).ne' z
  have hgconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(gn n)) ⇑f atTop
      (closedBall 0 R) := fun R hR =>
    tendstoUniformlyOn_heatMollify_seq (fun n => (hεp n).ne') hε0 hfnM hfM hfconv hR
  have hDconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (closedBall 0 R ×ˢ closedBall 0 R) := by
    intro R hR
    refine (hcv R hR).congr ?_
    filter_upwards [hpos] with n hn p _
    rw [hDn n hn, ContMetric.smul_apply, lfppDistCM_coe]
  have hloc := loc_of_agree hA (Real.exp (2 * |ξ| * M))
  have key := (dfLem7_1 ξ M Dn D gn f hDnlen hD hDconv hgconv hgM hfM hloc).2.2 R hR
  refine key.congr ?_
  filter_upwards [hpos] with n hn p _
  beta_reduce
  rw [hDn n hn, weylScale_smul, ← lfppDistE_addFun_eq_weylScale ξ (hεp n).ne' (hc n).1 (hc n).2,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le)]
  rfl

/-- **the localization property (eqn-square-bdy-weyl) of a limit in law** of `𝔞⁻¹D^εₙ_h`, read
off a coupling `ρ` (Lemma 2.10 through `ae_agreeSetK`): the input `hA` of `weyl_lfpp_varying`. -/
theorem ae_agreeSetK_of_tendsto (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hεs0 : Tendsto εs atTop (𝓝 0)) {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {ρ : ProbabilityMeasure E} {π : E → C(ℂ × ℂ, ℝ)}
    (hπ : Continuous π)
    (hconv : ∀ f : C(ℂ × ℂ, ℝ) →ᵇ ℝ, Tendsto (fun n => ∫ ω, f (lfppC (xiGamma γ) (εs n) (h ω)) ∂P)
      atTop (𝓝 (∫ p, f (π p) ∂(ρ : Measure E)))) :
    ∀ᵐ p ∂(ρ : Measure E), ∀ k r : ℕ, ∃ s : ℕ,
      π p ∈ agreeSetK ((k : ℝ) + 1) ((r : ℝ) + 1) s := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hεs0.eventually (gt_mem_nhds one_pos))
  set ε' : ℕ → ℝ := fun n => εs (n + N0)
  have hεI : ∀ n, ε' n ∈ Ioo (0 : ℝ) 1 := fun n => ⟨hεs _, hN0 _ (by omega)⟩
  have hX : ∀ n, AEMeasurable (fun ω => lfppC (xiGamma γ) (ε' n) (h ω)) P := fun n =>
    aemeasurable_lfppC hh (hεI n).1.ne'
  let ν : ℕ → ProbabilityMeasure C(ℂ × ℂ, ℝ) := fun n =>
    ⟨P.map fun ω => lfppC (xiGamma γ) (ε' n) (h ω),
      (Measure.isProbabilityMeasure_map_iff (hX n)).2 inferInstance⟩
  have hlim : Tendsto ν atTop (𝓝 (ρ.map π)) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have e1 : ∀ n, ∫ x, f x ∂(ν n : Measure C(ℂ × ℂ, ℝ)) =
        ∫ ω, f (lfppC (xiGamma γ) (ε' n) (h ω)) ∂P := fun n =>
      integral_map (hX n) f.continuous.aestronglyMeasurable
    have e2 : ∫ x, f x ∂((ρ.map π : ProbabilityMeasure _) : Measure C(ℂ × ℂ, ℝ)) =
        ∫ p, f (π p) ∂(ρ : Measure E) :=
      integral_map hπ.aemeasurable f.continuous.aestronglyMeasurable
    simp only [e1, e2]
    exact (hconv f).comp (tendsto_add_atTop_nat N0)
  have := ae_agreeSetK h28 hγ hγ2 P h hh ε' ν (ρ.map π) (fun n => ⟨hεI n, rfl⟩)
    (hεs0.comp (tendsto_add_atTop_nat N0)) hlim
  exact ae_of_ae_map hπ.aemeasurable this

end L217

end LQGMetric.DFGPS
