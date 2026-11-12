/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Defs
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDScale

/-!
# DZZ Lemma 3.8: comparison of the LGDs of two coupled fields (P2-DZZ3C, WP-113 part 3)

Ding–Zeitouni–Zhang, *Heat kernel for Liouville Brownian motion and Liouville graph distance*
(arXiv:1807.00422, `LBM_LGDarXiv.tex`), (eq-def-M-eta) l. 1205–1210 and Lemma 3.8
(`lem-LGD-compare`, l. 1218–1233), proof l. 1229–1232.

* `IsChaosLimit γ ζ V s μ`: the measure `μ` is DZZ's `M^ζ_γ` (eq-def-M-eta), i.e.
  `μ(A) = lim_n ∫_{A ∩ 𝕍} e^{γ ζ_{s_n}(z) − γ²/2 V_{s_n}(z)} dz` (`V_ε(z)` the normalisation,
  `Var ζ_ε(z)` in DZZ), along the scales `s_n`, for every ball `A` with rational centre and
  rational radius (a countable family, so that the a.s. limits of DZZ hold simultaneously).
  `M^ζ` lives on `𝕍` (`ℒ₂` restricted to `𝕍`, DZZ l. 421).
* `lgdDZZ_le_of_ball_le`: if `μ(B) ≤ e^c ν(B)` on balls then `D_δ(μ) ≤ D_{δ e^{−c/2}}(ν)`: a ball of
  `ν`-mass `≤ (δe^{−c/2})²` has `μ`-mass `≤ δ²` (DZZ l. 1231).
* `ratBall_le_of_ratBall_le`: the comparison extends from rational to real radii (continuity
  from below).
* **`dzz_lemma38`**: DZZ Lemma 3.8 on a given instance.

DZZ's (eq-coupling-two-fields) compares `ζ¹_{2^{-n}}` with `ζ²_{a2^{-n}}`, and the proof
(l. 1230) compares `M^{ζ¹}` with `M^{ζ²}` through these approximations, i.e. it reads `M^{ζ²}` as the
limit along the scales `a 2^{-n}`; this is the hypothesis `IsChaosLimit γ ζ₂ V₂ (a 2^{-n}) μ₂`
(for `a = 1`, the only case used in §3, it is (eq-def-M-eta) itself). The normalisations `V₁, V₂`
are arbitrary functions (in DZZ the variances); the lemma is deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- `min_{x ∈ A, y ∈ B} D_{γ,δ}(x, y)` for the Liouville graph distance of a measure `μ`. -/
def lgdMinSet (μ : Measure ℂ) (δ : ℝ) (A B : Set ℂ) : ℕ∞ :=
  ⨅ x ∈ A, ⨅ y ∈ B, lgdDZZ μ δ x y

/-- DZZ (eq-def-M-eta): `μ = M^ζ_γ` along the scales `s`, tested on balls with rational centre
and rational radius. -/
def IsChaosLimit (γ : ℝ) (ζ V : ℝ → ℂ → ℝ) (s : ℕ → ℝ) (μ : Measure ℂ) : Prop :=
  ∀ (c : ℚ × ℚ) (q : ℚ), 0 < q →
    Tendsto (fun n : ℕ => ∫⁻ z in Metric.ball (ratPt c) q ∩ dzzV,
        ENNReal.ofReal (Real.exp (γ * ζ (s n) z - γ ^ 2 / 2 * V (s n) z)))
      atTop (𝓝 (μ (Metric.ball (ratPt c) q)))

lemma isClosed_dzzV : IsClosed dzzV := by
  show IsClosed ({z : ℂ | 0 ≤ z.re} ∩ ({z : ℂ | z.re ≤ 1} ∩
    ({z : ℂ | 0 ≤ z.im} ∩ {z : ℂ | z.im ≤ 1})))
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

lemma measurableSet_dzzV : MeasurableSet dzzV := isClosed_dzzV.measurableSet

/-- The mass comparison extends from rational radii to all radii. -/
lemma ratBall_le_of_ratBall_le {μ ν : Measure ℂ} {K : ℝ≥0∞}
    (h : ∀ (c : ℚ × ℚ) (q : ℚ), 0 < q →
      μ (Metric.ball (ratPt c) q) ≤ K * ν (Metric.ball (ratPt c) q))
    (c : ℚ × ℚ) (r : ℝ) :
    μ (Metric.ball (ratPt c) r) ≤ K * ν (Metric.ball (ratPt c) r) := by
  have hU : Metric.ball (ratPt c) r =
      ⋃ q : {q : ℚ // 0 < q ∧ (q : ℝ) < r}, Metric.ball (ratPt c) (q : ℝ) := by
    ext z
    simp only [mem_iUnion, Metric.mem_ball]
    constructor
    · intro hz
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hz
      exact ⟨⟨q, by exact_mod_cast (dist_nonneg.trans_lt hq1), hq2⟩, hq1⟩
    · rintro ⟨q, hq⟩
      exact hq.trans q.2.2
  have hd : Directed (· ⊆ ·)
      (fun q : {q : ℚ // 0 < q ∧ (q : ℝ) < r} => Metric.ball (ratPt c) (q : ℝ)) :=
    Monotone.directed_le fun a b hab =>
      Metric.ball_subset_ball (by exact_mod_cast (show (a : ℚ) ≤ b from hab))
  rw [hU, hd.measure_iUnion, hd.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_mono fun q => h c q q.2.1

/-- **Comparison core** (DZZ l. 1231): if `μ(B) ≤ e^c ν(B)` for all balls `B` with rational
centre, then `D_δ(μ)(u,v) ≤ D_{δ e^{−c/2}}(ν)(u,v)`. -/
theorem lgdDZZ_le_of_ball_le {μ ν : Measure ℂ} {c : ℝ}
    (h : ∀ (x : ℚ × ℚ) (r : ℝ),
      μ (Metric.ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp c) * ν (Metric.ball (ratPt x) r))
    (δ : ℝ) (u v : ℂ) :
    lgdDZZ μ δ u v ≤ lgdDZZ ν (δ * Real.exp (-c / 2)) u v := by
  unfold lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨cc, ρ, P, h1, h2⟩ := hN
  refine iInf₂_le N ⟨cc, ρ, P, fun i => ⟨(h1 i).1, ?_⟩, h2⟩
  have he : Real.exp (-c / 2) ^ 2 = Real.exp (-c) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc μ _ ≤ ENNReal.ofReal (Real.exp c) * ν _ := h _ _
    _ ≤ ENNReal.ofReal (Real.exp c) * ENNReal.ofReal ((δ * Real.exp (-c / 2)) ^ 2) := by
        gcongr; exact (h1 i).2
    _ = ENNReal.ofReal (δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos c).le, mul_pow, he, Real.exp_neg]
        congr 1
        field_simp

/-- Mass comparison of two chaos limits from a pointwise comparison of the exponents. -/
theorem chaos_ratBall_le {γ c : ℝ} {ζ₁ ζ₂ V₁ V₂ : ℝ → ℂ → ℝ} {s₁ s₂ : ℕ → ℝ}
    {μ₁ μ₂ : Measure ℂ} (h₁ : IsChaosLimit γ ζ₁ V₁ s₁ μ₁) (h₂ : IsChaosLimit γ ζ₂ V₂ s₂ μ₂)
    (hpt : ∀ n : ℕ, ∀ z ∈ dzzV, γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z ≤
      c + (γ * ζ₂ (s₂ n) z - γ ^ 2 / 2 * V₂ (s₂ n) z))
    (x : ℚ × ℚ) (r : ℝ) :
    μ₁ (Metric.ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp c) * μ₂ (Metric.ball (ratPt x) r) := by
  refine ratBall_le_of_ratBall_le (fun x q hq => ?_) x r
  refine le_of_tendsto_of_tendsto' (h₁ x q hq)
    (ENNReal.Tendsto.const_mul (h₂ x q hq) (Or.inr ENNReal.ofReal_ne_top)) fun n => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (Metric.isOpen_ball.measurableSet.inter measurableSet_dzzV)
    fun z hz => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos c).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpt n z hz.2))

end DZZ
end LQGMetric
