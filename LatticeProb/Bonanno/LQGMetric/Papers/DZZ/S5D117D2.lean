/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117D2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117D1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W12
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B9

/-!
# D117, packet P-DIH, part 2: pathwise covariance of `M_{γ,η}` under a symmetry of `𝕍`

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-translation-invariant) l. 2271, "by symmetry"
l. 2555; DEC-117 §1 (`DZZDihedralLaw`: "the η-field of the noise `W ∘ g` is the η-field of `W`
composed with `g`, pathwise"). For an involutive symmetry `σ` of `𝕍` (`IsDihGen`, S5D117D1) and
the transformed noise `W' = W ∘ dihL2 σ`:

* `ae_coarseVer_dih`: a.s. the continuous versions satisfy `ζ_n[W'](z) = ζ_n[W](σ z)` for all `n`,
  `z` (equal at the rational points by `tildeHInf_dihNoise`, then by continuity);
* `lintegral_ball_dih`: the change of variables `z ↦ σ z` on `B(c, q) ∩ 𝕍`;
* **`ae_ballMassQ_dihNoise`**: a.s. `ballMassQ (M[W']) = ballMassQ (σ_* M[W])` for `M = dzzMuIn γ`,
  through the chaos-limit characterisation `ae_isChaosLimit_wickQArea` (S3P32W12) of both
  measures and the invariance `tildeVar_dih` of the variance.

Own elementary argument (DZZ state the invariance without proof); DV-D117-3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat GMCIdent4

variable {σ : ℂ → ℂ}

/-- `σ` as a measurable equivalence -/
def IsDihGen.mEquiv (hσ : IsDihGen σ) : ℂ ≃ᵐ ℂ where
  toFun := σ
  invFun := σ
  left_inv := hσ.invol
  right_inv := hσ.invol
  measurable_toFun := hσ.continuous.measurable
  measurable_invFun := hσ.continuous.measurable

lemma IsDihGen.dist_eq (hσ : IsDihGen σ) (z w : ℂ) : dist (σ z) (σ w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm, hσ.norm_sub]

lemma IsDihGen.preimage_ball (hσ : IsDihGen σ) (x : ℂ) (r : ℝ) :
    σ ⁻¹' Metric.ball x r = Metric.ball (σ x) r := by
  ext y
  simp only [mem_preimage, Metric.mem_ball]
  rw [← hσ.dist_eq, hσ.invol]

lemma IsDihGen.preimage_dzzV (hσ : IsDihGen σ) : σ ⁻¹' dzzV = dzzV := by
  ext y; exact hσ.mem_dzzV y

/-- change of variables on `B(x, q) ∩ 𝕍` -/
lemma lintegral_ball_dih (hσ : IsDihGen σ) (F : ℂ → ℝ≥0∞) (x : ℂ) (q : ℝ) :
    ∫⁻ z in Metric.ball x q ∩ dzzV, F (σ z) = ∫⁻ y in Metric.ball (σ x) q ∩ dzzV, F y := by
  have hS : MeasurableSet (Metric.ball x q ∩ dzzV) :=
    Metric.isOpen_ball.measurableSet.inter measurableSet_dzzV
  have hS' : MeasurableSet (Metric.ball (σ x) q ∩ dzzV) :=
    Metric.isOpen_ball.measurableSet.inter measurableSet_dzzV
  rw [← lintegral_indicator hS, ← lintegral_indicator hS']
  have e : (Metric.ball x q ∩ dzzV).indicator (fun z => F (σ z)) =
      fun z => (Metric.ball (σ x) q ∩ dzzV).indicator F (σ z) := by
    funext z
    have hm : σ z ∈ Metric.ball (σ x) q ∩ dzzV ↔ z ∈ Metric.ball x q ∩ dzzV := by
      have h1 : σ z ∈ Metric.ball (σ x) q ↔ z ∈ Metric.ball x q := by
        simp only [Metric.mem_ball]; rw [hσ.dist_eq]
      exact and_congr h1 (hσ.mem_dzzV z)
    by_cases hz : z ∈ Metric.ball x q ∩ dzzV
    · rw [indicator_of_mem hz, indicator_of_mem (hm.2 hz)]
    · rw [indicator_of_notMem hz, indicator_of_notMem (fun h => hz (hm.1 h))]
  rw [e]
  exact hσ.mp.lintegral_comp_emb hσ.mEquiv.measurableEmbedding _

lemma denseRange_ratPt : DenseRange ratPt :=
  Metric.denseRange_iff.2 fun x r hr => by
    obtain ⟨c, hc⟩ := exists_ratPt_dist_lt x hr
    exact ⟨c, by rw [dist_comm]; exact hc⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- a.s. the continuous versions of `h̃_{2^{-n}}` of `W ∘ dihL2` are those of `W` composed with
`σ` -/
theorem ae_coarseVer_dih (hW : IsWhiteNoise P W) (hσ : IsDihGen σ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ z : ℂ,
      coarseVer (isWhiteNoise_dihNoise hW hσ) n z ω = coarseVer hW n (σ z) ω := by
  have hW' := isWhiteNoise_dihNoise hW hσ
  have h : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ c : ℚ × ℚ,
      coarseVer hW' n (ratPt c) ω = coarseVer hW n (σ (ratPt c)) ω := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro c
    filter_upwards [(coarseVer_spec hW' n).2.2 (ratPt c),
      (coarseVer_spec hW n).2.2 (σ (ratPt c))] with ω h1 h2
    rw [h1, h2, tildeHInf_dihNoise]
  filter_upwards [h] with ω hω n
  have := (denseRange_ratPt).equalizer ((coarseVer_spec hW' n).1 ω)
    (((coarseVer_spec hW n).1 ω).comp hσ.continuous) (funext fun c => hω n c)
  exact fun z => congrFun this z

/-- **pathwise covariance of the DZZ measure** under an involutive symmetry `σ` of `𝕍`: a.s. the
rational ball masses of `M[W ∘ dihL2 σ]` are those of `σ_* M[W]` -/
theorem ae_ballMassQ_dihNoise (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hσ : IsDihGen σ) :
    ∀ᵐ ω ∂P, ballMassQ (dzzMuIn γ (dihNoise hσ W) ω) = ballMassQ ((dzzMuIn γ W ω).map σ) := by
  have hW' := isWhiteNoise_dihNoise hW hσ
  filter_upwards [ae_coarseVer_dih hW hσ, ae_isChaosLimit_wickQArea hW hγ hγ2,
    ae_isChaosLimit_wickQArea hW' hγ hγ2] with ω hco hL hL'
  funext c q
  obtain ⟨c', hc'⟩ := hσ.rat c
  have hB : MeasurableSet (Metric.ball (ratPt c) (q : ℝ)) := Metric.isOpen_ball.measurableSet
  -- the `wickQArea` parts
  have hwick : wickQArea γ (dihNoise hσ W) ω (Metric.ball (ratPt c) q) =
      wickQArea γ W ω (Metric.ball (ratPt c') q) := by
    by_cases hq : (0 : ℚ) < q
    · refine tendsto_nhds_unique (hL' c q hq) ?_
      have e : ∀ n : ℕ, ∫⁻ z in Metric.ball (ratPt c) q ∩ dzzV,
          ENNReal.ofReal (Real.exp (γ * wickZeta hW' ((1 / 2 : ℝ) ^ n) z ω -
            γ ^ 2 / 2 * tildeVar ((1 / 2 : ℝ) ^ n) z)) =
          ∫⁻ z in Metric.ball (ratPt c') q ∩ dzzV,
          ENNReal.ofReal (Real.exp (γ * wickZeta hW ((1 / 2 : ℝ) ^ n) z ω -
            γ ^ 2 / 2 * tildeVar ((1 / 2 : ℝ) ^ n) z)) := by
        intro n
        rw [hc', ← lintegral_ball_dih hσ]
        refine setLIntegral_congr_fun
          (Metric.isOpen_ball.measurableSet.inter measurableSet_dzzV) fun z _ => ?_
        rw [wickZeta_pow, wickZeta_pow, hco n z, tildeVar_dih hσ]
      simp_rw [e]
      exact hL c' q hq
    · have h1 : Metric.ball (ratPt c) (q : ℝ) = ∅ :=
        Metric.ball_eq_empty.2 (by exact_mod_cast not_lt.1 hq)
      have h2 : Metric.ball (ratPt c') (q : ℝ) = ∅ :=
        Metric.ball_eq_empty.2 (by exact_mod_cast not_lt.1 hq)
      rw [h1, h2, measure_empty, measure_empty]
  have hpre : σ ⁻¹' Metric.ball (ratPt c) q = Metric.ball (ratPt c') q := by
    rw [hσ.preimage_ball, hc']
  have hvol : volume (Metric.ball (ratPt c') (q : ℝ) ∩ dzzVᶜ) =
      volume (Metric.ball (ratPt c) (q : ℝ) ∩ dzzVᶜ) := by
    have e : σ ⁻¹' Metric.ball (ratPt c) (q : ℝ) ∩ dzzVᶜ =
        σ ⁻¹' (Metric.ball (ratPt c) (q : ℝ) ∩ dzzVᶜ) := by
      rw [preimage_inter, preimage_compl, hσ.preimage_dzzV]
    rw [← hpre, e]
    exact hσ.mp.measure_preimage
      (hB.inter measurableSet_dzzV.compl).nullMeasurableSet
  simp only [ballMassQ, dzzMuIn]
  rw [Measure.map_apply hσ.continuous.measurable hB, hpre, dzzWall_apply_ball,
    dzzWall_apply_ball, hwick, hvol]

end DZZ
end LQGMetric
