/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_20Transl at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20Bilip
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_13

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.20: translation invariance of the law of the rescaled limit (`Lem2_20Transl`)

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.20,
T:1323–1324: "the translation invariance of the law of `h`, modulo additive constant". We prove
that the law of `e^{−ξ h_r(z)} D_h(r· + z, r· + z)` does not depend on `z`, following the pattern
of the proof of Lemma 2.13 (`L213.tendsto_law_scaled`, T:1104–1116):

1. at the LFPP level, a.s. `e^{−ξ g_r(0)} 𝔞⁻¹D^ε_g(r·, r·) = e^{−ξ h_r(z)} 𝔞⁻¹D^ε_h(r· + z, r· + z)`
   for `g = h(· + z) − h_1(z)` (heat-kernel translation `ae_heatMollify_translate`, path change of
   variables `lfppDOn_affine`, Weyl scaling by a constant `lem2_6_ae_const`), and `g =ᵈ h`
   (`GM.Tight.map_normalize_eq`); so the LFPP laws at centres `z` and `0` coincide;
2. the LFPP laws at centre `z` converge to the law of `e^{−ξ h_r(z)} D_h(r· + z, r· + z)`
   (`L213.tendstoInDistribution_adjoin` with the continuous approximants `⟨h, σ_{z,r} * ψ_m⟩` of
   `h_r(z)`); limits in law are unique.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint GM.Tight

namespace L220

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- the LFPP analogue of `resc`: `e^{−ξ g_r(z)} 𝔞_ε⁻¹ D^ε_g(r· + z, r· + z)` -/
def lfppResc (ξ ε r : ℝ) (z : ℂ) (g : DistC) : C(ℂ × ℂ, ℝ) :=
  Real.exp (-ξ * circleAvg g r z) • (lfppC ξ ε g).comp (affArgs r z)

/-- **Step 2**: the LFPP laws at centre `z` converge to the law of the rescaled limit. -/
theorem tendsto_law_lfppResc {γ : ℝ} (εn : ℕ → ℝ) (hε : ∀ n, 0 < εn n)
    (Dh : Ω → ContMetric) (hh : IsNormalizedWPGFF h P) (hDh : Measurable Dh)
    (hconv : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P)))
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Tendsto (fun n => L213.lawPM P (fun ω => lfppResc (xiGamma γ) (εn n) r z (h ω))) atTop
      (𝓝 (L213.lawPM P (fun ω => resc (xiGamma γ) (fun _ => 1) r z (h ω, Dh ω)))) := by
  set ξ := xiGamma γ
  have hgff := isGFFPlusBddCont_of_normalizedWP hh
  have hA : AEMeasurable (fun ω => circleAvg (h ω) r z) P :=
    ((measurable_circleAvg_left r z).comp hh.1.measurable).aemeasurable
  obtain ⟨gA, hgAc, hgAm, hgA⟩ := CoordApprox.exists_coord_circ hh.1 hr z
  have hT := L213.tendstoInDistribution_adjoin (P := P) (fun ω => pairJ ⊤ (h ω))
    ((measurable_pairJ ⊤).comp hh.1.measurable)
    (fun n ω => lfppC ξ (εn n) (h ω)) (fun ω => (Dh ω).1)
    (fun n => aemeasurable_lfppC hgff (hε _).ne')
    (measurable_subtype_coe.comp hDh).aemeasurable hconv
    gA hgAc hgAm _ hA hgA (fun _ => (1 : ℝ)) 1 tendsto_const_nhds
  set G : (ℝ × ℝ) × C(ℂ × ℂ, ℝ) → C(ℂ × ℂ, ℝ) := fun x =>
    (x.1.2 * Real.exp (-ξ * x.1.1)) • x.2.comp (affArgs r z)
  have hG : Continuous G :=
    ((continuous_snd.comp continuous_fst).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.comp continuous_fst)))).smul
      ((ContinuousMap.continuous_precomp (affArgs r z)).comp continuous_snd)
  have hT2 := (hT.continuous_comp hG).tendsto
  have e2 : (G ∘ fun ω => ((circleAvg (h ω) r z, (1 : ℝ)), (Dh ω).1)) =
      fun ω => resc ξ (fun _ => 1) r z (h ω, Dh ω) := by
    funext ω; ext p; simp [G, resc]
  have e1 : ∀ n, (G ∘ fun ω => ((circleAvg (h ω) r z, (1 : ℝ)), lfppC ξ (εn n) (h ω))) =
      fun ω => lfppResc ξ (εn n) r z (h ω) := fun n => by
    funext ω; ext p; simp [G, lfppResc]
  have hT3 : Tendsto (fun n => L213.lawPM P (fun ω => lfppResc ξ (εn n) r z (h ω))) atTop
      (𝓝 (L213.lawPM P (G ∘ fun ω => ((circleAvg (h ω) r z, (1 : ℝ)), (Dh ω).1)))) := by
    refine hT2.congr fun n => ?_
    apply Subtype.ext
    show P.map (G ∘ _) = P.map _
    rw [e1 n]
  rwa [e2] at hT3

end L220

end LQGMetric.DFGPS
