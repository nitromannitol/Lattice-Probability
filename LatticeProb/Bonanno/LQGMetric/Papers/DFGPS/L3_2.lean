/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Defs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightC
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.2: the events `E_r(z; C)` and their probability (task P2-DFA0, package DF-A1)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), (3.4) `eqn-annulus-event`,
T:1446–1450: `E_r(z; C)` is the event that
`sup_{u,v ∈ ∂B_r(z)} D_h(u, v; 𝔸_{r/2,2r}(z)) ≤ C 𝔠_r e^{ξ h_r(z)}` and
`D_h(∂B_r(z), ∂B_{2r}(z)) ≥ C⁻¹ 𝔠_r e^{ξ h_r(z)}` (`annEvent`; T:1448 prints `h_r(0)`, a misprint
for `h_r(z)` as its use at T:1542 shows, `blueprint/DFGPS.md` row L3.2).

`prob_annEvent`: the first sentence of the proof of Lemma 3.2 (T:1475): "By Axioms IV and V (also
see (1.4)), for each `p ∈ (0,1)` there exists `C > 1` such that for every `z ∈ ℂ` and `r > 0`,
`P[E_r(z; C)] ≥ p`." The tightness facts (1.4) are GM.S2.4a/c, proved in this library from the
weak-metric axioms (`GM.Tight.gm_S2_4a`, `GM.Tight.gm_S2_4c`; the task allowed the Blueprint
Props `GMS2_4a/c`, which are not needed), with `K₁ = ∂B_1(0)`, `K₂ = ∂B_2(0)` and
`K = ∂B_1(0) ⊂ U = 𝔸_{1/2,2}(0)`.

DFGPS Definition 3.7 (distance around an annulus) is `ContMetric.aroundDist`
(`LQGMetric/Topo/Disconnect.lean`, T:1655–1657); it is not redefined here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-- the event `E_r(z; C)` of DFGPS (3.4) (T:1446–1450, with `h_r(z)`), as a set of fields -/
def annEvent (ξ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (C r : ℝ) (z : ℂ) : Set DistC :=
  {g | internalDiam (D g) (Metric.sphere z r) (annulus z (r / 2) (2 * r)) ≤
      ENNReal.ofReal (C * scaleFac ξ c g r z) ∧
    ENNReal.ofReal (C⁻¹ * scaleFac ξ c g r z) ≤
      setDist (D g) (Metric.sphere z r) (Metric.sphere z (2 * r))}

namespace L32

lemma setDist_eq_iInf' (D : ContMetric) (A B : Set ℂ) :
    setDist D A B = ⨅ x ∈ A, ⨅ y ∈ B, ENNReal.ofReal (D.1 (x, y)) := by
  rw [setDist, MetricGeometry.setEDist_eq_iInf, iInf_image]
  refine iInf_congr fun x => iInf_congr fun _ => ?_
  rw [iInf_image]
  exact iInf_congr fun y => iInf_congr fun _ => ContMetric.edist_pt D x y

lemma mem_sphere_scale {r : ℝ} (hr : 0 < r) {z w : ℂ} {ρ : ℝ} (hw : w ∈ Metric.sphere z (r * ρ)) :
    ∃ u ∈ Metric.sphere (0 : ℂ) ρ, w = (r : ℂ) * u + z := by
  rw [← GM.Bilip.scaleSet_sphere hr] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  exact ⟨u, hu, rfl⟩

end L32

open L32 in
/-- **DFGPS Lemma 3.2, first step** (T:1475): for every `p < 1` there is `C > 1` with
`P[E_r(z; C)] ≥ p` for all `z ∈ ℂ`, `r > 0` (Axioms IV, V via GM.S2.4a/c). -/
theorem prob_annEvent {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ, 1 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        P {ω | h ω ∉ annEvent (xiGamma γ) D c C r z} < ε := by
  set K₁ : Set ℂ := Metric.sphere 0 1
  set K₂ : Set ℂ := Metric.sphere 0 2
  have hdisj : Disjoint K₁ K₂ := by
    rw [Set.disjoint_left]
    intro w h1 h2
    rw [mem_sphere_zero_iff_norm] at h1 h2
    linarith
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨s, hs, HA⟩ := GM.Tight.gm_S2_4a hD (isCompact_sphere 0 1) (isCompact_sphere 0 2) hdisj hε2
  have hUc : IsConnected (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) :=
    ⟨⟨1, show (1 / 2 : ℝ) < ‖(1 : ℂ) - 0‖ ∧ ‖(1 : ℂ) - 0‖ < 2 by norm_num⟩,
      GM.Bilip.isPreconnected_annulus_zero (by norm_num)⟩
  have hKU : K₁ ⊆ (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) := fun w hw =>
    show (1 / 2 : ℝ) < ‖w - 0‖ ∧ ‖w - 0‖ < 2 by
      have h1 := mem_sphere_zero_iff_norm.1 hw
      rw [sub_zero, h1]; norm_num
  obtain ⟨S, hS, HC⟩ := GM.Tight.gm_S2_4c hD (annulus 0 (1 / 2) 2).isOpen hUc
    (GM.Bilip.isBounded_annulus_zero _ _) (isCompact_sphere 0 1) hKU hε2
  set C := max (max S s⁻¹) 2 with hC_def
  have hC1 : 1 < C := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hCS : S ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCs : C⁻¹ ≤ s := by
    rw [inv_le_comm₀ (by linarith) hs]
    exact (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨C, hC1, fun P _ h hh r hr z => ?_⟩
  set Abad := {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₂, s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
    (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)}
  set Bbad := {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
    (D (h ω)).internal ((fun w => (r : ℂ) * w + z) '' (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ))
      ((r : ℂ) * u + z) ((r : ℂ) * v + z) ≤
      ENNReal.ofReal (S * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z))}
  have hsub : {ω | h ω ∉ annEvent (xiGamma γ) D c C r z} ⊆ Abad ∪ Bbad := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨hA, hB⟩ := hcon
    simp only [Abad, Bbad, mem_ofPred_eq, not_not] at hA hB
    apply hω
    set sc := scaleFac (xiGamma γ) c (h ω) r z with hsc
    have hU : (fun w => (r : ℂ) * w + z) '' (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) =
        (annulus z (r / 2) (2 * r) : Set ℂ) := by
      rw [← scaleSet, GM.Bilip.scaleSet_annulus hr]
      congr 2 <;> ring
    refine ⟨?_, ?_⟩
    · refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
      obtain ⟨u', hu', rfl⟩ := mem_sphere_scale hr (show u ∈ Metric.sphere z (r * 1) by
        rwa [mul_one])
      obtain ⟨v', hv', rfl⟩ := mem_sphere_scale hr (show v ∈ Metric.sphere z (r * 1) by
        rwa [mul_one])
      have := hB u' hu' v' hv'
      rw [hU] at this
      have e : S * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) = S * sc := by
        rw [hsc, scaleFac, mul_assoc]
      rw [e] at this
      rcases le_or_gt 0 sc with h0 | h0
      · exact this.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCS h0))
      · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hS.le h0.le)] at this
        exact this.trans bot_le
    · rw [setDist_eq_iInf']
      refine le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_
      obtain ⟨u', hu', rfl⟩ := mem_sphere_scale hr (show u ∈ Metric.sphere z (r * 1) by
        rwa [mul_one])
      obtain ⟨v', hv', rfl⟩ := mem_sphere_scale hr (show v ∈ Metric.sphere z (r * 2) by
        rwa [mul_comm])
      have hAu := hA u' hu' v' hv'
      have e : s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) = s * sc := by
        rw [hsc, scaleFac, mul_assoc]
      rw [e] at hAu
      rcases le_or_gt 0 sc with h0 | h0
      · exact ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_right hCs h0).trans hAu.le)
      · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
          (inv_nonneg.2 (by linarith)) h0.le)]
        exact bot_le
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  calc P Abad + P Bbad < ε / 2 + ε / 2 :=
        ENNReal.add_lt_add (HA P h hh r hr z) (HC P h hh r hr z)
    _ = ε := ENNReal.add_halves ε

end LQGMetric.DFGPS
