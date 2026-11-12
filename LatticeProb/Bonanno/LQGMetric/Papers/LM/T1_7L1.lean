/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7L1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7D1
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8CondBd
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Lim
import LatticeProb.Bonanno.LQGMetric.Metric.WeylBasic

/-!
# LM Theorem 1.7, packet P-LIM (DEC-107 §3(vi)): helper lemmas

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7, l. 1000–1089, as repaired by decision D107
(`decisions/DEC-107.md` §3(vi)).

* `t17_internal_le_of_le`: `D₂ ≤ C D₁` pointwise implies `D₂(·,·;V) ≤ C D₁(·,·;V)` (lengths of
  paths scale; mathlib `LipschitzOnWith.comp_eVariationOn_le`). This is the deterministic part of
  LM Lemma 5.1 (l. 904–929: "`D̃(z,w;V) ≤ C D(z,w;V)`").
* `t17_chainInf_le`: the same for the measurable countable formula `chainInf` of
  `Meas/Internal.lean`, with only `D₁` a length metric (`chainInf_le_internal` holds for every
  continuous metric). This is what makes LM Lemma 5.1 usable for the copy `D̃`, whose length
  property is not available as an a.s. statement (handoff/P2-LMC18.md, `CopyAeLength`).
* `t17_iInf_chainInf`, `t17_chainInf_succ_le`: `D(z,w;B_m) ↓ D(z,w)` for a length metric
  (exhaustion; `c18_internal_eq_iInf`, `internal_univ_of_isLength`).
* `t17_seq_props`: the resulting real sequence is bounded, antitone and converges.
* `t17_var_limit`: bounded convergence (DEC-107 §3(vi), "`η_m → 0` boundedly"): if
  `Var(F_{m+1}) ≤ c E[(F_m − F_{m+1}) F_{m+1}]` for a bounded antitone sequence `F_m → G`, then
  `G` is a.s. constant.
* `t17_ae_kernel`: an a.s. property of `(h, D)` holds for `law(h)`-a.e. `g` and
  `condDistrib D h P g`-a.e. `d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-! ## Comparison of internal metrics (deterministic part of LM Lemma 5.1) -/

/-- if `D₂ ≤ C D₁` pointwise then `D₂(z,w;V) ≤ C D₁(z,w;V)` -/
theorem t17_internal_le_of_le {d₁ d₂ : ContMetric} {C : ℝ} (hC : 0 < C)
    (hle : ∀ x y : ℂ, d₂.1 (x, y) ≤ C * d₁.1 (x, y)) (V : Set ℂ) (z w : ℂ) :
    d₂.internal V z w ≤ ENNReal.ofReal C * d₁.internal V z w := by
  unfold ContMetric.internal MetricGeometry.internalEDist
  rw [ENNReal.mul_iInf_of_ne (by simpa using hC) ENNReal.ofReal_ne_top]
  refine le_iInf fun γ => ?_
  set φ : d₁.Space → d₂.Space := fun x => d₂.pt (d₁.unpt x) with hφ
  have hφc : Continuous φ := d₂.continuous_pt.comp d₁.continuous_unpt
  have hlip : LipschitzOnWith (Real.toNNReal C) φ univ := by
    intro a _ b _
    calc edist (φ a) (φ b) = ENNReal.ofReal (d₂.1 (d₁.unpt a, d₁.unpt b)) :=
          ContMetric.edist_pt d₂ _ _
      _ ≤ ENNReal.ofReal (C * d₁.1 (d₁.unpt a, d₁.unpt b)) := ENNReal.ofReal_le_ofReal (hle _ _)
      _ = ENNReal.ofReal C * edist a b := by
          rw [ENNReal.ofReal_mul hC.le]; congr 1; exact (ContMetric.edist_pt d₁ _ _).symm
      _ = ↑(Real.toNNReal C) * edist a b := rfl
  have hmem : ∀ t, (γ.1.map hφc) t ∈ d₂.pt '' V := by
    intro t
    obtain ⟨y, hy, hyt⟩ := γ.2 t
    exact ⟨y, hy, by show d₂.pt y = φ (γ.1 t); rw [← hyt]; rfl⟩
  refine (MetricGeometry.internalEDist_le_pathLength (γ.1.map hφc) hmem).trans ?_
  unfold MetricGeometry.pathLength MetricGeometry.curveLength
  have hext : (γ.1.map hφc).extend = φ ∘ γ.1.extend := rfl
  rw [hext]
  exact hlip.comp_eVariationOn_le (mapsTo_univ _ _)

/-- **LM Lemma 5.1, deterministic part, measurable form**: `chainInf_V(D₂) ≤ C chainInf_V(D₁)` if
`D₂ ≤ C D₁` and `D₁` is a length metric (no length hypothesis on `D₂`) -/
theorem t17_chainInf_le {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) {C : ℝ} (hC : 0 < C)
    (hle : ∀ x y : ℂ, d₂.1 (x, y) ≤ C * d₁.1 (x, y)) {V : Set ℂ} (hV : IsOpen V) (z w : ℂ) :
    d₂.chainInf V z w ≤ ENNReal.ofReal C * d₁.chainInf V z w := by
  rw [← d₁.internal_eq_chainInf h₁ hV]
  exact (d₂.chainInf_le_internal hV z w).trans (t17_internal_le_of_le hC hle V z w)

/-- `F_m(d) := d(z, w; B_m(0))`, through the measurable countable formula `chainInf` (equal to the
internal metric on length metrics, `ContMetric.internal_eq_chainInf`) -/
def t17F (m : ℕ) (z w : ℂ) (d : ContMetric) : ℝ≥0∞ := d.chainInf (Metric.ball 0 (m : ℝ)) z w

lemma measurable_t17F (m : ℕ) (z w : ℂ) : Measurable (t17F m z w) :=
  (ContMetric.measurable_chainInf _).comp (measurable_id.prodMk (measurable_const (a := (z, w))))

/-! ## Exhaustion `D(z,w;B_m) ↓ D(z,w)` -/

theorem t17_chainInf_succ_le {d : ContMetric} (hd : d.IsLength) (m : ℕ) (z w : ℂ) :
    t17F (m + 1) z w d ≤ t17F m z w d := by
  unfold t17F
  rw [← d.internal_eq_chainInf hd Metric.isOpen_ball, ← d.internal_eq_chainInf hd Metric.isOpen_ball]
  exact MetricGeometry.internalEDist_anti (image_mono (Metric.ball_subset_ball (by push_cast; linarith)))
    _ _

theorem t17_iInf_chainInf {d : ContMetric} (hd : d.IsLength) (n₀ : ℕ) (z w : ℂ) :
    ⨅ m : ℕ, t17F (n₀ + m) z w d = ENNReal.ofReal (d.1 (z, w)) := by
  rw [← d.internal_univ_of_isLength hd]
  have e : ∀ m : ℕ, t17F (n₀ + m) z w d = d.internal (Metric.ball 0 ((n₀ + m : ℕ) : ℝ)) z w :=
    fun m => (d.internal_eq_chainInf hd Metric.isOpen_ball z w).symm
  simp_rw [e]
  refine le_antisymm ?_ (le_iInf fun m => MetricGeometry.internalEDist_anti (image_mono
    (subset_univ _)) _ _)
  have h := c18_internal_eq_iInf d ⊤ z w
  simp only [TopologicalSpace.Opens.coe_top] at h
  rw [h]
  refine le_iInf fun n => iInf_le_of_le (n + 1) ?_
  refine MetricGeometry.internalEDist_anti (image_mono fun x hx => ?_) _ _
  have hx' := Metric.mem_ball.1 (show x ∈ (univ : Set ℂ) ∩ Metric.ball 0 ((n : ℝ) + 1) from hx).2
  exact Metric.mem_ball.2 (hx'.trans_le (by push_cast; linarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)]))

/-- a bounded antitone `ℝ≥0∞`-sequence decreasing to a finite value, as reals -/
theorem t17_seq_props {a : ℕ → ℝ≥0∞} {X : ℝ≥0∞} {x : ℝ} (hx : 0 ≤ x) (hX : X ≠ ⊤)
    (h1 : ∀ m, a (m + 1) ≤ a m) (h2 : ⨅ m, a m = ENNReal.ofReal x) (h3 : a 0 ≤ X) :
    (∀ m, 0 ≤ (a m).toReal ∧ (a m).toReal ≤ X.toReal) ∧ (∀ m, (a (m + 1)).toReal ≤ (a m).toReal)
      ∧ Tendsto (fun m => (a m).toReal) atTop (𝓝 x) := by
  have anti : Antitone a := antitone_nat_of_succ_le h1
  have ham : ∀ m, a m ≤ X := fun m => (anti (Nat.zero_le m)).trans h3
  have hne : ∀ m, a m ≠ ⊤ := fun m => ne_top_of_le_ne_top hX (ham m)
  refine ⟨fun m => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hX (ham m)⟩,
    fun m => ENNReal.toReal_mono (hne m) (h1 m), ?_⟩
  have h : Tendsto a atTop (𝓝 (⨅ m, a m)) := tendsto_atTop_iInf anti
  rw [h2] at h
  have := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h
  rwa [ENNReal.toReal_ofReal hx] at this

/-! ## Bounded convergence -/

/-- **Bounded convergence step of DEC-107 §3(vi)**: for a bounded antitone sequence `F_m → G`
with `Var(F_{m+1}) ≤ c E[(F_m − F_{m+1}) F_{m+1}]`, `G` is a.s. equal to its mean. -/
theorem t17_var_limit {β : Type*} [MeasurableSpace β] {μ : Measure β} [IsProbabilityMeasure μ]
    {F : ℕ → β → ℝ} {G : β → ℝ} {B c : ℝ} (hF : ∀ m, Measurable (F m))
    (h0 : ∀ᵐ d ∂μ, ∀ m, 0 ≤ F m d ∧ F m d ≤ B) (hmono : ∀ᵐ d ∂μ, ∀ m, F (m + 1) d ≤ F m d)
    (hlim : ∀ᵐ d ∂μ, Tendsto (fun m => F m d) atTop (𝓝 (G d)))
    (hvar : ∀ m, ∫ d, (F (m + 1) d - ∫ d', F (m + 1) d' ∂μ) ^ 2 ∂μ ≤
      c * ∫ d, (F m d - F (m + 1) d) * F (m + 1) d ∂μ) :
    ∀ᵐ d ∂μ, G d = ∫ d', G d' ∂μ := by
  have hFa : ∀ m, AEStronglyMeasurable (F m) μ := fun m => (hF m).aestronglyMeasurable
  have hGm : AEStronglyMeasurable G μ := aestronglyMeasurable_of_tendsto_ae _ hFa hlim
  have hG : ∀ᵐ d ∂μ, 0 ≤ G d ∧ G d ≤ B := by
    filter_upwards [h0, hlim] with d hd hl
    exact ⟨ge_of_tendsto' hl fun m => (hd m).1, le_of_tendsto' hl fun m => (hd m).2⟩
  -- the means converge
  have hA : Tendsto (fun m => ∫ d, F m d ∂μ) atTop (𝓝 (∫ d, G d ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => B) hFa (integrable_const B)
      (fun m => h0.mono fun d hd => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hd m).1]; exact (hd m).2) hlim
  have hA1 : Tendsto (fun m => ∫ d, F (m + 1) d ∂μ) atTop (𝓝 (∫ d, G d ∂μ)) :=
    hA.comp (tendsto_add_atTop_nat 1)
  have hmean : ∀ m, 0 ≤ ∫ d, F m d ∂μ ∧ ∫ d, F m d ∂μ ≤ B := fun m =>
    ⟨integral_nonneg_of_ae (h0.mono fun d hd => (hd m).1),
      (integral_mono_ae ((integrable_const B).mono' (hFa m) (h0.mono fun d hd => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hd m).1]; exact (hd m).2)) (integrable_const B)
        (h0.mono fun d hd => (hd m).2)).trans (by simp)⟩
  -- left side
  have hL : Tendsto (fun m => ∫ d, (F (m + 1) d - ∫ d', F (m + 1) d' ∂μ) ^ 2 ∂μ) atTop
      (𝓝 (∫ d, (G d - ∫ d', G d' ∂μ) ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B ^ 2)
      (fun m => ((hFa (m + 1)).sub aestronglyMeasurable_const).pow 2) (integrable_const _)
      (fun m => h0.mono fun d hd => ?_) ?_
    · have h1 := hd (m + 1)
      have h2 := hmean (m + 1)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith
    · filter_upwards [hlim] with d hd
      exact ((hd.comp (tendsto_add_atTop_nat 1)).sub hA1).pow 2
  -- right side
  have hR : Tendsto (fun m => c * ∫ d, (F m d - F (m + 1) d) * F (m + 1) d ∂μ) atTop (𝓝 (c * 0)) := by
    refine Tendsto.const_mul c ?_
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun m d => (F m d - F (m + 1) d) * F (m + 1) d) (f := fun d => (G d - G d) * G d)
      (fun _ => B ^ 2) (fun m => ((hFa m).sub (hFa (m + 1))).mul (hFa (m + 1)))
      (integrable_const _) (fun m => (h0.and hmono).mono fun d hd => by
        have h1 := hd.1 m
        have h2 := hd.1 (m + 1)
        have h3 := hd.2 m
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.2 h3) h2.1)]
        nlinarith) (by
        filter_upwards [hlim] with d hd
        exact (hd.sub (hd.comp (tendsto_add_atTop_nat 1))).mul (hd.comp (tendsto_add_atTop_nat 1)))
    simpa using h
  have hle := le_of_tendsto_of_tendsto' hL hR hvar
  rw [mul_zero] at hle
  have hint : Integrable (fun d => (G d - ∫ d', G d' ∂μ) ^ 2) μ :=
    Integrable.of_bound ((hGm.sub aestronglyMeasurable_const).pow 2) (B ^ 2) (by
      have hm : 0 ≤ ∫ d, G d ∂μ ∧ ∫ d, G d ∂μ ≤ B :=
        ⟨integral_nonneg_of_ae (hG.mono fun d hd => hd.1),
          (integral_mono_ae ((integrable_const B).mono' hGm (hG.mono fun d hd => by
            rw [Real.norm_eq_abs, abs_of_nonneg hd.1]; exact hd.2)) (integrable_const B)
            (hG.mono fun d hd => hd.2)).trans (by simp)⟩
      filter_upwards [hG] with d hd
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith)
  have h0' := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun d => sq_nonneg _)
    hint).1 (le_antisymm hle (integral_nonneg fun d => sq_nonneg _))
  filter_upwards [h0'] with d hd
  have : (G d - ∫ d', G d' ∂μ) ^ 2 = 0 := hd
  linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this]

/-! ## From `(h, D)` to the conditional law -/

/-- an a.s. property of `(h, D)` holds for `law(h)`-a.e. `g`, `condDistrib D h P g`-a.e. `d` -/
theorem t17_ae_kernel {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} {D : Ω → ContMetric} (hh : Measurable h) (hD : Measurable D)
    {S : Set (DistC × ContMetric)} (hS : MeasurableSet S) (H : ∀ᵐ ω ∂P, (h ω, D ω) ∈ S) :
    ∀ᵐ g ∂P.map h, ∀ᵐ d ∂condDistrib D h P g, (g, d) ∈ S := by
  have h1 : ∀ᵐ p ∂P.map (fun ω => (h ω, D ω)), p ∈ S :=
    (ae_map_iff (hh.prodMk hD).aemeasurable hS).2 H
  rw [← compProd_map_condDistrib hh.aemeasurable hD.aemeasurable] at h1
  exact (Measure.ae_compProd_iff hS).1 h1

end LQGMetric.LM
