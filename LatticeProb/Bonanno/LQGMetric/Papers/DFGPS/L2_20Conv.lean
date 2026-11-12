/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_20Conv at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L1_3
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofTightA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Proof
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.20, last sentence: determinism ⇒ convergence in probability

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 2.20 (`lem-lfpp-msrble`,
T:1297–1302), proof T:1335 "The last statement follows from Lemma 1.3": once the subsequential
limit `D_h` is a.s. determined by `h`, `𝔞_{εn}⁻¹ D^{εn}_h → D_h` in probability.

As in the footnote at T:383, Lemma 1.3 is applied with `Ω₂` a complete separable metric space of
continuous functions: here, for each `R`, the restrictions to the compact square
`B̄_R(0) × B̄_R(0)` (`C(K, ℝ)` with the sup metric, Polish), which is exactly what
`TendstoInProbLU` measures. The field coordinate is `pairJ ⊤ ∘ h` (Polish, D80) instead of `h`
itself (mathlib's topology on `DistC` is not Polish). `L220.tendstoInProbLU_of_det`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

namespace L220

open Blueprint TopologicalSpace

/-- the compact square `B̄_R(0) × B̄_R(0)` of `TendstoInProbLU` -/
abbrev sqR (R : ℝ) : Set (ℂ × ℂ) := Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R

instance compactSpace_sqR (R : ℝ) : CompactSpace (sqR R) :=
  isCompact_iff_compactSpace.1 ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

/-- **DFGPS Lemma 2.20, last sentence** (T:1301, T:1335, via Lemma 1.3): if the subsequential
limit `D_h` is a.s. determined by `h`, then `𝔞_{εn}⁻¹ D^{εn}_h → D_h` in probability. -/
theorem tendstoInProbLU_of_det {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (Dh : Ω → ContMetric) (εn : ℕ → ℝ)
    (hh : IsNormalizedWPGFF h P) (hDm : Measurable Dh) (hεp : ∀ n, 0 < εn n)
    (hconv : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P)))
    (hdet : AEDeterminedBy Dh h P) :
    TendstoInProbLU P (fun n ω => (aEpsDF (xiGamma γ) (εn n))⁻¹ •
      lfppDist (xiGamma γ) (εn n) (h ω)) atTop (fun ω => (Dh ω).1) := by
  intro R _ δ hδ
  have hgff := isGFFPlusBddCont_of_normalizedWP hh
  set ξ := xiGamma γ
  let ρ : C(ℂ × ℂ, ℝ) → C(sqR R, ℝ) := fun u => u.restrict (sqR R)
  have hρ : Continuous ρ := ContinuousMap.continuous_restrict _
  have hmeas := fun n => aemeasurable_lfppC hgff (ξ := ξ) (hεp n).ne'
  let L : ℕ → Ω → C(ℂ × ℂ, ℝ) := fun n => (hmeas n).mk _
  have hL : ∀ n, Measurable (L n) := fun n => (hmeas n).measurable_mk
  have hLe : ∀ n, (fun ω => lfppC ξ (εn n) (h ω)) =ᵐ[P] L n := fun n => (hmeas n).ae_eq_mk
  obtain ⟨F, hF, hDF⟩ := hdet
  let X : Ω → (CoordJ → ℝ) := fun ω => pairJ ⊤ (h ω)
  have hX : Measurable X := (measurable_pairJ ⊤).comp hgff.1
  have hD1 : Measurable fun ω => (Dh ω).1 := measurable_subtype_coe.comp hDm
  have key := lem1_3 (α := CoordJ → ℝ) (β := C(sqR R, ℝ)) P X (fun ω => ρ (Dh ω).1)
    (fun n ω => ρ (L n ω)) hX (hρ.measurable.comp hD1) (fun n => hρ.measurable.comp (hL n))
    (by
      intro φ hφ hb
      obtain ⟨C, hC⟩ := hb
      have hc := hconv (fun x => φ (x.1, ρ x.2))
        (hφ.comp (continuous_fst.prodMk (hρ.comp continuous_snd)))
        ⟨C, fun x => hC _⟩
      refine (tendsto_congr fun n => integral_congr_ae ?_).1 hc
      filter_upwards [hLe n] with ω hω
      simp only [lfppC] at hω
      simp only [X, hω])
    ⟨fun x => ρ (F (pairJInv ⊤ x)).1,
      hρ.measurable.comp (measurable_subtype_coe.comp (hF.comp (measurable_pairJInv ⊤))),
      hDF.mono fun ω hω => by simp only [Function.comp_apply, X, pairJInv_pairJ, hω]⟩
  have hk := key (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hk (fun _ => zero_le)
    fun n => measure_mono_ae ?_
  filter_upwards [hLe n, hgff.ae_tendstoLocallyUniformly_heatMollify (εn n) (hεp n).ne']
    with ω hω hc hmem
  change ENNReal.ofReal δ ≤ _ at hmem ⊢
  refine hmem.trans (iSup₂_le fun p hp => ?_)
  have h1 : ((aEpsDF ξ (εn n))⁻¹ • lfppDist ξ (εn n) (h ω)) p = ρ (L n ω) ⟨p, hp⟩ := by
    show _ = L n ω p
    rw [← hω, lfppC_apply_of_continuous hc.2 p]
    simp [lfppDist, smul_eq_mul]
  have h2 : (Dh ω).1 p = ρ (Dh ω).1 ⟨p, hp⟩ := rfl
  rw [h1, h2, edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal (ContinuousMap.dist_apply_le_dist _)

end L220

end LQGMetric.DFGPS
