/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_13 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_13Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.CoordApprox
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_14
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5Final
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenTrans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffRed
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.13 (`lem-lfpp-coord`): Axiom V for subsequential limits of LFPP

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 2.13 T:1060–1071,
proof T:1101–1119, in the form of DEC-78 (node `Lem2_13`). Steps of the paper:

1. (T:1106–1111) The laws of `𝔞_{ε/r}⁻¹ D^{ε/r}_{h^r} =ᵈ 𝔞_{ε/r}⁻¹ D^{ε/r}_h` lie in the set of laws of
   `𝔞_δ⁻¹ D^δ_h`, whose Prokhorov closure is tight and, at `δ → 0`, carried by continuous metrics
   (Lemma 2.5 A, `lem2_5`). We use the closed set `T = ⋂_m closure{law(𝔞_δ⁻¹ D^δ_h) : δ < 1/(m+1)}`
   (the limit points as `δ → 0`): it lies in the closure of a tight set, and each of its points is
   a limit along some `δ_j → 0` (first countability of the Prokhorov topology), hence carried by
   continuous metrics.
2. (T:1113–1116) `law(𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(r·, r·))` is the limit of the laws in 1. along a
   subsequence on which `r 𝔞_{ε/r}/𝔞_ε → 𝔠_r` (`L213.tendsto_law_scaled`), so it lies in `T`.
3. (T:1118) Hence the laws over `r > 0` are tight and their closure is carried by metrics.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint

namespace L213

/-- In a Polish space, a set of laws with compact closure is tight (mathlib's Prokhorov converse,
after choosing a complete metric). -/
theorem isTight_of_isCompact_closure {E : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] {S : Set (ProbabilityMeasure E)}
    (hc : IsCompact (closure S)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S} := by
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable E
  exact isTightMeasureSet_of_isCompact_closure hc

/-- the law of `f` under `P`, as a probability measure -/
def lawPM {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → E) : ProbabilityMeasure E := ⟨P.map f, inferInstance⟩

@[simp] lemma coe_lawPM {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → E) : (lawPM P f : Measure E) = P.map f := rfl

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **Limit identification** (T:1113–1116): along a subsequence `φ` with
`r 𝔞_{εn/r}/𝔞_{εn} → 𝔠_r`, `law(𝔞_{εn/r}⁻¹ D^{εn/r}_h) → law(𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(r·, r·))`. -/
theorem tendsto_law_scaled {γ : ℝ} (εn : ℕ → ℝ) (hε : ∀ n, 0 < εn n)
    (hεt : Tendsto εn atTop (𝓝 0)) (Dh : Ω → ContMetric) (hh : IsNormalizedWPGFF h P)
    (hDh : Measurable Dh)
    (hconv : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P)))
    {r cr : ℝ} (hr : 0 < r) (hcr : cr ≠ 0) (φs : ℕ → ℕ) (hφs : StrictMono φs)
    (hlim : Tendsto (fun k => r * aEpsDF (xiGamma γ) (εn (φs k) / r) /
      aEpsDF (xiGamma γ) (εn (φs k))) atTop (𝓝 cr)) :
    Tendsto (fun k => lawPM P (fun ω => lfppC (xiGamma γ) (εn (φs k) / r) (h ω))) atTop
      (𝓝 (lawPM P (fun ω => (cr⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0)) •
        (Dh ω).1.comp (scaleArgs r)))) := by
  set ξ := xiGamma γ
  have hgff := isGFFPlusBddCont_of_normalizedWP hh
  have hεφ : Tendsto (fun k => εn (φs k)) atTop (𝓝 0) := hεt.comp hφs.tendsto_atTop
  have hA : AEMeasurable (fun ω => circleAvg (h ω) r 0) P :=
    ((measurable_circleAvg_left r 0).comp hh.1.measurable).aemeasurable
  obtain ⟨gA, hgAc, hgAm, hgA⟩ := CoordApprox.exists_coord_circ hh.1 hr 0
  have hT := tendstoInDistribution_adjoin (P := P) (fun ω => pairJ ⊤ (h ω))
    ((measurable_pairJ ⊤).comp hh.1.measurable)
    (fun k ω => lfppC ξ (εn (φs k)) (h ω)) (fun ω => (Dh ω).1)
    (fun k => aemeasurable_lfppC hgff (hε _).ne')
    (measurable_subtype_coe.comp hDh).aemeasurable
    (fun φ hφ hb => (hconv φ hφ hb).comp hφs.tendsto_atTop)
    gA hgAc hgAm _ hA hgA _ _ (hlim.inv₀ hcr)
  set G : (ℝ × ℝ) × C(ℂ × ℂ, ℝ) → C(ℂ × ℂ, ℝ) := fun x =>
    (x.1.2 * Real.exp (-ξ * x.1.1)) • x.2.comp (scaleArgs r)
  have hG : Continuous G :=
    ((continuous_snd.comp continuous_fst).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.comp continuous_fst)))).smul
      ((ContinuousMap.continuous_precomp (scaleArgs r)).comp continuous_snd)
  have hT2 := (hT.continuous_comp hG).tendsto
  refine Tendsto.congr' ?_ hT2
  have hsmall : ∀ᶠ k in atTop, εn (φs k) < 1 := hεφ.eventually (gt_mem_nhds one_pos)
  filter_upwards [hsmall] with k hk
  obtain ⟨c0, hc0, hc0'⟩ := aEpsDF_ge_far γ (hε (φs k))
  have ha : aEpsDF ξ (εn (φs k)) ≠ 0 := (hc0.trans_le (hc0' _ ⟨le_rfl, hk⟩)).ne'
  apply Subtype.ext
  show P.map (G ∘ fun ω => ((circleAvg (h ω) r 0, _), lfppC ξ (εn (φs k)) (h ω))) =
    P.map (fun ω => lfppC ξ (εn (φs k) / r) (h ω))
  rw [← map_lfppC_fieldScale hh ξ (div_ne_zero (hε _).ne' hr.ne') hr]
  refine Measure.map_congr ?_
  filter_upwards [ae_lfppC_fieldScale hh.1 ξ (hε (φs k)) hr ha] with ω hω
  rw [hω]
  simp only [Function.comp, G]

end L213

end LQGMetric.DFGPS
