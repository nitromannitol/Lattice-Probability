/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W2

/-!
# D117, packet P-BIG: big balls have mass `> 2δ²` with high probability

Ding–Zeitouni–Zhang, arXiv:1807.00422, `literature/src/1807.00422/LBM_LGDarXiv.tex`, l. 2342
and l. 2562 ("with high probability, the balls intersecting both `∂𝕍_{u,λ}` and `∂𝕍_{u,2λ}` have
LQG measure larger than `2δ²`"). DZZ give no further argument; the reason (DEC-117 §1) is that a
ball of radius `≥ r` inside `𝕍` contains one of finitely many fixed rational balls inside
`(0,1)²`, each of which has a.s. positive mass (DZZ Lemma 2.10, negative moments:
`ae_qArea_wn_ball_pos`, S3P32W2). Here:

* `exists_netBall`: the deterministic geometry (finite rational `r/4`-net of `𝕍`, `exists_finite_ratNet`);
* `tendsto_prob_qArea_ball_le`: `P(M_γ(B) ≤ K · 2δ²) → 0` for a fixed rational ball `B ⊆ (0,1)²`
  (continuity from above, `tendsto_measure_biInter_gt`);
* **`dzzBigBalls_dzzMuIn`**: `DZZBigBalls P (dzzMuIn γ W) r` for every `r > 0`.

Own elementary argument for DZZ's one-line claim (cost rule), recorded as such in the report.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

/-- a ball of radius `≥ r` inside `𝕍` contains a ball `B(c, q)`, `c` in a finite rational net,
with `B(c, q) ⊆ (0,1)²` -/
lemma exists_netBall {r : ℝ} (hr : 0 < r) {q : ℚ} (hq1 : r / 4 < q) (hq2 : (q : ℝ) < r / 2) :
    ∃ G : Finset (ℚ × ℚ), ∀ (x : ℂ) (ρ : ℝ), r ≤ ρ → ball x ρ ⊆ dzzV →
      ∃ c ∈ G, ball (ratPt c) q ⊆ openSquare ∧ ball (ratPt c) q ⊆ ball x ρ := by
  have hV : IsCompact dzzV := by
    have hb : Bornology.IsBounded dzzV := by
      refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => ?_
      obtain ⟨h1, h2, h3, h4⟩ := hz
      rw [mem_closedBall, dist_zero_right]
      refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
      rw [abs_of_nonneg h1, abs_of_nonneg h3]; linarith
    exact Metric.isCompact_of_isClosed_isBounded isClosed_dzzV hb
  obtain ⟨G, hG⟩ := exists_finite_ratNet hV (show 0 < r / 4 by positivity)
  refine ⟨G, fun x ρ hρ hB => ?_⟩
  have hx : x ∈ dzzV := hB (mem_ball_self (by linarith))
  obtain ⟨c, hc, hxc⟩ := hG x hx
  have hsub : ball (ratPt c) q ⊆ ball x (3 * r / 4) := by
    intro y hy
    rw [mem_ball] at hy ⊢
    calc dist y x ≤ dist y (ratPt c) + dist (ratPt c) x := dist_triangle _ _ _
      _ < q + r / 4 := add_lt_add hy (by rw [dist_comm]; exact hxc)
      _ < 3 * r / 4 := by linarith
  refine ⟨c, hc, fun y hy => ?_, hsub.trans (ball_subset_ball (by linarith))⟩
  have hy' : dist y x < 3 * r / 4 := hsub hy
  have hin : ∀ w : ℂ, ‖w‖ = r / 4 → y + w ∈ dzzV := fun w hw => hB (by
    rw [mem_ball]
    calc dist (y + w) x ≤ dist (y + w) y + dist y x := dist_triangle _ _ _
      _ = r / 4 + dist y x := by rw [dist_eq_norm, add_sub_cancel_left, hw]
      _ < ρ := by linarith)
  have hr4 : (0 : ℝ) ≤ r / 4 := by positivity
  have n1 : ‖((r / 4 : ℝ) : ℂ)‖ = r / 4 := by rw [Complex.norm_real, Real.norm_of_nonneg hr4]
  have n2 : ‖(-(r / 4 : ℝ) : ℂ)‖ = r / 4 := by rw [norm_neg, n1]
  have n3 : ‖((r / 4 : ℝ) : ℂ) * Complex.I‖ = r / 4 := by rw [norm_mul, Complex.norm_I, mul_one, n1]
  have n4 : ‖-(((r / 4 : ℝ) : ℂ) * Complex.I)‖ = r / 4 := by rw [norm_neg, n3]
  have a1 := (hin _ n1).2.1
  have a2 := (hin _ n2).1
  have a3 := (hin _ n3).2.2.2
  have a4 := (hin _ n4).2.2.1
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im] at a1 a2 a3 a4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- for a fixed rational ball `B ⊆ (0,1)²` and a constant `K < ∞`, `P(M_γ(B) ≤ K · 2δ²) → 0` -/
theorem tendsto_prob_qArea_ball_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (c : ℚ × ℚ) (q : ℚ) (hq : 0 < q) (hB : ball (ratPt c) q ⊆ openSquare) {K : ℝ≥0∞}
    (hK : K ≠ ⊤) :
    Tendsto (fun δ : ℝ => P {ω | qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare
      (ball (ratPt c) q) ≤ K * ENNReal.ofReal (2 * δ ^ 2)}) (𝓝[>] 0) (𝓝 0) := by
  have := hW.isProbabilityMeasure
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  set f : Ω → ℝ≥0∞ := fun ω =>
    qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare (ball (ratPt c) q) with hf
  have hfm : AEMeasurable f P := by
    have hF := GMCIdent4.aemeasurable_qAreaMeasureOn_ball_circ hX hγ hγ2 (ratPt c) (q : ℝ)
    rw [GMCIdent3.circLaw, GMCIdent3.map_circVec_eq hX hW] at hF
    exact hF.comp_aemeasurable (GMCIdent3.measurable_wnCircVec hW).aemeasurable
  set s : ℝ → Set Ω := fun δ => {ω | f ω ≤ K * ENNReal.ofReal (2 * δ ^ 2)} with hs
  have hns : ∀ δ > (0 : ℝ), NullMeasurableSet (s δ) P := fun δ _ =>
    hfm.nullMeasurable measurableSet_Iic
  have hmono : ∀ i j : ℝ, 0 < i → i ≤ j → s i ⊆ s j := fun i j hi hij ω hω =>
    le_trans (b := K * ENNReal.ofReal (2 * i ^ 2)) hω
      (mul_le_mul_right (ENNReal.ofReal_le_ofReal (by nlinarith)) _)
  have hT := tendsto_measure_biInter_gt hns hmono ⟨1, one_pos, measure_ne_top _ _⟩
  have hpos := ae_qArea_wn_ball_pos hW hγ hγ2
  have h0 : P (⋂ r > (0 : ℝ), s r) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hpos)
    intro hall
    have hlt := hall c q hq hB
    simp only [mem_iInter] at hω
    have hc : Tendsto (fun δ : ℝ => K * ENNReal.ofReal (2 * δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous fun δ : ℝ => K * ENNReal.ofReal (2 * δ ^ 2) :=
        (ENNReal.continuous_const_mul hK).comp
          (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 2)))
      have h1 := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [show K * ENNReal.ofReal (2 * (0 : ℝ) ^ 2) = 0 by simp] at h1
    have hle : f ω ≤ 0 := ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun δ hδ =>
      hω δ hδ)
    exact (lt_irrefl _ (hlt.trans_le hle))
  rw [h0] at hT
  exact hT

/-- **DZZ l. 2342, 2562 (big balls)**: for the DZZ measure `dzzMuIn γ W` and every `r > 0`, every
ball of radius `≥ r` inside `𝕍` has mass `> 2δ²` with probability `→ 1` as `δ → 0`. -/
theorem dzzBigBalls_dzzMuIn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {r : ℝ} (hr : 0 < r) : DZZBigBalls P (dzzMuIn γ W) r := by
  classical
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r / 4 < r / 2 by linarith)
  have hq0 : (0 : ℚ) < q := by
    have : (0 : ℝ) < q := lt_trans (by positivity) hq1
    exact_mod_cast this
  obtain ⟨G, hG⟩ := exists_netBall hr hq1 hq2
  set F := G.filter fun c => ball (ratPt c) q ⊆ openSquare with hF
  set K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 / 2 * Real.log 3)) with hK
  set A : (ℚ × ℚ) → ℝ → Set Ω := fun c δ => {ω | qAreaMeasureOn γ (GMCIdent3.wnField W ω)
    openSquare (ball (ratPt c) q) ≤ K * ENNReal.ofReal (2 * δ ^ 2)} with hA
  have hsub : ∀ δ : ℝ, {ω | ¬ ∀ (x : ℂ) (ρ : ℝ), r ≤ ρ → ball x ρ ⊆ dzzV →
      ENNReal.ofReal (2 * δ ^ 2) < dzzMuIn γ W ω (ball x ρ)} ⊆ ⋃ c ∈ F, A c δ := by
    intro δ ω hω
    simp only [mem_ofPred_eq, not_forall, not_lt] at hω
    obtain ⟨x, ρ, hρ, hB, hm⟩ := hω
    obtain ⟨c, hc, hcS, hcB⟩ := hG x ρ hρ hB
    refine mem_iUnion₂.2 ⟨c, Finset.mem_filter.2 ⟨hc, hcS⟩, ?_⟩
    change qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare (ball (ratPt c) q) ≤
      K * ENNReal.ofReal (2 * δ ^ 2)
    calc qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare (ball (ratPt c) q)
        ≤ K * wickQArea γ W ω (ball (ratPt c) q) := le_wickQArea γ W ω isOpen_ball.measurableSet
      _ ≤ K * dzzMuIn γ W ω (ball (ratPt c) q) :=
          mul_le_mul_right (le_dzzWall dzzV (wickQArea γ W ω) _) _
      _ ≤ K * dzzMuIn γ W ω (ball x ρ) := by gcongr
      _ ≤ K * ENNReal.ofReal (2 * δ ^ 2) := by gcongr
  have hsum : Tendsto (fun δ : ℝ => ∑ c ∈ F, P (A c δ)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum F fun c hc =>
      tendsto_prob_qArea_ball_le hW hγ hγ2 c q hq0 (Finset.mem_filter.1 hc).2
        (K := K) ENNReal.ofReal_ne_top
    rw [Finset.sum_const_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
    fun δ => (measure_mono (hsub δ)).trans (measure_biUnion_finset_le F _)

end DZZ
end LQGMetric
