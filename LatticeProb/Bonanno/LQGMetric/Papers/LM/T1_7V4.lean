/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V3
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P1A

/-!
# LM Theorem 1.7, packet P-VAR (c): the per-metric product bound (D107 §3(ii)–(iv))

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7, Step 2 (l. 1038–1055) with the repaired Step 3
of decision D107 (`decisions/DEC-107.md` §2, §3(ii)–(iv)): for a fixed length metric `d`, two
near-geodesics `P₁ ⊂ B_n` (for `d(z,w;B_n)`) and `P₂ ⊂ B_{n+1}` (for `F := d(z,w;B_{n+1})`),
chosen depending only on `d` (LM l. 1038; D107 §1.3: no measurable selection), and for a.e. grid
shift `θ` (LM Lemma 5.2, `t17_grid_null`):

* `A(S) := (F(D^S) − F(d))_+ ≤ b₁(S) := len(P₁) − F + (C² − 1) len(P₁ ∩ S)` and
  `A(S) ≤ b₂(S) := len(P₂) − F + (C² − 1) len(P₂ ∩ S)` (`t17v_A_bound`, (5.16));
* `sup_S b₁(S) ≤ C²(η + ε³ + κ)` once `2ε < r(d, κ)` (`t17_near_bound`, first/last hits of the
  closed square, D107 §2), `η := d(z,w;B_n) − F`;
* `∑_S b₂(S) ≤ C²(F + ε³) + ε³ #𝒮` ((5.2) for `P₂`);
* hence `∑_S A(S)² ≤ ∑_S b₁ b₂ ≤ C²(η + ε³ + κ)(C²(F + ε³) + ε³ #𝒮)` (`t17_sum_sq_le` pattern).

`t17v_perD` states this as: there are bounds `b_S` for `(F(D^S) − F(d))_+²` over every `D^S`
compatible with `d` at `S` (`T17Compat`), with the displayed sum bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric.LM

open MetricGeometry

/-- a near-minimal path for the internal metric, as a continuous curve `ℝ → ℂ` on `[0, 1]` -/
theorem t17v_near_path (d : ContMetric) {V : Set ℂ} {z w : ℂ} (hfin : d.internal V z w ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) : ∃ P : ℝ → ℂ, Continuous P ∧ P 0 = z ∧ P 1 = w ∧
      MapsTo P (Icc 0 1) V ∧ d.len P 0 1 ≤ d.internal V z w + ENNReal.ofReal δ := by
  have hlt : d.internal V z w < d.internal V z w + ENNReal.ofReal δ :=
    ENNReal.lt_add_right hfin (by simpa using hδ)
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1
    (show internalEDist (d.pt '' V) (d.pt z) (d.pt w) < d.internal V z w + ENNReal.ofReal δ
      from hlt)
  refine ⟨d.unpt ∘ γ.1.extend, d.continuous_unpt.comp γ.1.continuous_extend, ?_, ?_, ?_, hγ.le⟩
  · show d.unpt (γ.1.extend 0) = z
    rw [Path.extend_zero]; rfl
  · show d.unpt (γ.1.extend 1) = w
    rw [Path.extend_one]; rfl
  · intro t ht
    have h2 : d.pt (d.unpt (γ.1.extend t)) ∈ d.pt '' V := by
      rw [Path.extend_apply _ ht]; exact γ.2 ⟨t, ht⟩
    exact d.mem_image_pt.1 h2

/-- the closed square `cl S_k` -/
def t17CSq (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : Set ℂ :=
  {x | ε * (k.1 + θ.1) ≤ x.re ∧ x.re ≤ ε * (k.1 + 1 + θ.1) ∧
    ε * (k.2 + θ.2) ≤ x.im ∧ x.im ≤ ε * (k.2 + 1 + θ.2)}

lemma t17v_isClosed_csq (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : IsClosed (t17CSq ε θ k) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)))

lemma t17v_square_sub_csq (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : t17Square ε θ k ⊆ t17CSq ε θ k :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1.le, h2.le, h3.le, h4.le⟩

lemma t17v_csq_norm {ε : ℝ} {θ : ℝ × ℝ} {k : ℤ × ℤ} {x y : ℂ} (hx : x ∈ t17CSq ε θ k)
    (hy : y ∈ t17CSq ε θ k) : ‖x - y‖ ≤ 2 * ε := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : |(x - y).re| ≤ ε := by
    rw [Complex.sub_re, abs_sub_le_iff]; constructor <;> nlinarith
  have him : |(x - y).im| ≤ ε := by
    rw [Complex.sub_im, abs_sub_le_iff]; constructor <;> nlinarith
  linarith

lemma t17v_sfinite (d : ContMetric) (P : ℝ → ℂ) (a b : ℝ) : SFinite (t17LenMeas (d.pt ∘ P) a b) := by
  unfold t17LenMeas
  split_ifs <;> infer_instance

/-- **D107 §2** (LM l. 1079–1081 repaired): a near-geodesic `P ⊂ B_n` of `d(z,w;B_n)` has
`len(P ∩ S; d) ≤ d(z,w;B_n) + ε' + κ − d(z,w;B_{n+1})` for every square of side `ε < r/2`. -/
theorem t17v_piece_le {d : ContMetric} {n : ℕ} {r κ : ℝ}
    (hr : ∀ (a b : ℝ) (P : ℝ → ℂ), ContinuousOn P (Icc a b) →
      MapsTo P (Icc a b) (Metric.closedBall 0 (n : ℝ)) →
      ∀ ε' : ℝ≥0∞, d.len P a b ≤ d.internal (Metric.ball 0 (n : ℝ)) (P a) (P b) + ε' →
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ b → ‖P s - P u‖ < r →
        d.len P s u + d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) (P a) (P b) ≤
          d.internal (Metric.ball 0 (n : ℝ)) (P a) (P b) + ε' + ENNReal.ofReal κ)
    {P : ℝ → ℂ} (hP : Continuous P) (hfin : d.len P 0 1 ≠ ⊤)
    (hPn : MapsTo P (Icc 0 1) (Metric.closedBall 0 (n : ℝ))) {e : ℝ} (he : 0 ≤ e)
    (hnear : d.len P 0 1 ≤ d.internal (Metric.ball 0 (n : ℝ)) (P 0) (P 1) + ENNReal.ofReal e)
    (hF0 : d.internal (Metric.ball 0 (n : ℝ)) (P 0) (P 1) ≠ ⊤) (hκ : 0 ≤ κ)
    {ε : ℝ} (hεr : 2 * ε < r) (θ : ℝ × ℝ) (k : ℤ × ℤ) :
    t17Piece d P 0 1 ε θ k ≤
      (d.internal (Metric.ball 0 (n : ℝ)) (P 0) (P 1)).toReal + e + κ -
        (d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) (P 0) (P 1)).toReal := by
  set I₀ := d.internal (Metric.ball 0 (n : ℝ)) (P 0) (P 1)
  set I₁ := d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) (P 0) (P 1)
  have hI : I₁ ≤ I₀ := internalEDist_anti (image_mono (Metric.ball_subset_ball (by
    push_cast; linarith))) _ _
  have hI₁ : I₁ ≠ ⊤ := ne_top_of_le_ne_top hF0 hI
  have hrhs : 0 ≤ I₀.toReal + e + κ - I₁.toReal := by
    have := ENNReal.toReal_mono hF0 hI; linarith
  have hcurve : T17Curve (d.pt ∘ P) 0 1 := ⟨zero_le_one, d.continuous_pt.comp_continuousOn
    hP.continuousOn, hfin⟩
  by_cases hex : ∃ t ∈ Icc (0 : ℝ) 1, P t ∈ t17CSq ε θ k
  · obtain ⟨t₀, ht₀, hPt₀⟩ := hex
    obtain ⟨s, u, hs, hsu, hu, hPs, hPu, hall⟩ :=
      t17_first_last_hit hP.continuousOn (t17v_isClosed_csq ε θ k) ht₀ hPt₀
    have hsub : Icc (0 : ℝ) 1 ∩ P ⁻¹' t17Square ε θ k ⊆ Icc s u := fun t ⟨ht, hPt⟩ =>
      hall t ht (t17v_square_sub_csq ε θ k hPt)
    have h1 := t17LenMeas_le_of_subset hcurve hs hsu hu hsub
    have hnorm : ‖P s - P u‖ < r := (t17v_csq_norm hPs hPu).trans_lt hεr
    have h2 := hr 0 1 P hP.continuousOn hPn (ENNReal.ofReal e) hnear s u hs hsu hu hnorm
    have hlsu : d.len P s u ≠ ⊤ := ne_top_of_le_ne_top hfin
      (eVariationOn.mono _ (Icc_subset_Icc hs hu))
    have h3 := ENNReal.toReal_mono (by finiteness) h2
    rw [ENNReal.toReal_add hlsu hI₁, ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hF0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal he,
      ENNReal.toReal_ofReal hκ] at h3
    have h4 : t17Piece d P 0 1 ε θ k ≤ (d.len P s u).toReal :=
      ENNReal.toReal_mono hlsu h1
    linarith
  · push_neg at hex
    have : Icc (0 : ℝ) 1 ∩ P ⁻¹' t17Square ε θ k = ∅ :=
      eq_empty_of_forall_notMem fun t ⟨ht, hPt⟩ => hex t ht (t17v_square_sub_csq ε θ k hPt)
    rw [t17Piece, this, measure_empty, ENNReal.toReal_zero]
    exact hrhs

end LQGMetric.LM
