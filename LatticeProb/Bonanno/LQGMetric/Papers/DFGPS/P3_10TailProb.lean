/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_10TailProb at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10TailChain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5CentreGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_11
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10Neg
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.10, Step 1 (T:1875–1893):

* `hcr_of_good`, `vcr_of_good`: on the event of Proposition 3.1 (upper bound) for the
  configurations of `P3_10TailGeom`, the crossings `HCr`, `VCr` exist with `D`-length
  `≤ 2A 𝔠_s e^{ξh_s(w)}`;
* `scale_ratio_dyadic`: "applying Theorem 1.5 to bound `𝔠_{2^{-n}𝕣}`" (T:1890): from
  `DFGPSScaling` (small `2^{-n}`) and Axiom V (the finitely many other `n`),
  `𝔠_{2^{-n}𝕣} ≤ K₀ (2^{-n})^{ξQ-ζ} 𝔠_𝕣` for all `n`;
* `exists_q_exponent`: the choice of `q < Q` (T:1878, 1911) with `Q + √(Q²-4) = 4/γ`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology Complex
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

variable {D : ContMetric} {Y : Set ℂ}

lemma HCr.mono {s : ℝ} {w : ℂ} {e : ℝ} {P : ℝ → ℂ} {L L' : ℝ} (h : HCr D Y s w e P L)
    (hL : L ≤ L') : HCr D Y s w e P L' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.trans (ENNReal.ofReal_le_ofReal hL)⟩

lemma VCr.mono {s : ℝ} {w : ℂ} {P : ℝ → ℂ} {L L' : ℝ} (h : VCr D Y s w P L)
    (hL : L ≤ L') : VCr D Y s w P L' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.trans (ENNReal.ofReal_le_ofReal hL)⟩

/-- the horizontal configuration: `K₁, K₂` the segments at `re = 1/16, 15/16`, `U` the strip -/
lemma hcr_of_good {s : ℝ} (hs : 0 < s) {w : ℂ} {e X : ℝ} (hX : 0 < X)
    (hsq : ∀ x : ℂ, w.re < x.re → x.re < w.re + s → w.im < x.im → x.im < w.im + s → x ∈ Y)
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2)
    (hgood : setDistIn D (scaleSet s w (Icc (1 / 16) (1 / 16) ×ℂ Icc (3 / 16 + e) (5 / 16 + e)))
      (scaleSet s w (Icc (15 / 16) (15 / 16) ×ℂ Icc (3 / 16 + e) (5 / 16 + e)))
      (scaleSet s w (Ioo 0 1 ×ℂ Ioo (1 / 8 + e) (3 / 8 + e))) ≤ ENNReal.ofReal X) :
    ∃ P, HCr D Y s w e P (2 * X) := by
  obtain ⟨P, hPc, hP0, hP1, hPm, hPl⟩ := exists_path_of_setDistIn_lt D
    (X := ENNReal.ofReal (2 * X))
    (hgood.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)))
  rw [mem_scaleSet_Icc hs] at hP0 hP1
  refine ⟨P, hPc, by linarith [hP0.1.1, hP0.1.2], by linarith [hP1.1.1, hP1.1.2],
    fun t ht => ?_, fun t ht => ?_, hPl.le⟩
  · have := (mem_scaleSet_Ioo hs _ _ _ _ _ _).1 (hPm ht)
    exact ⟨this.2.1.le, this.2.2.le⟩
  · have := (mem_scaleSet_Ioo hs _ _ _ _ _ _).1 (hPm ht)
    refine hsq _ (by linarith [this.1.1]) (by linarith [this.1.2]) ?_ ?_
    · nlinarith [this.2.1]
    · nlinarith [this.2.2]

/-- the vertical configuration -/
lemma vcr_of_good {s : ℝ} (hs : 0 < s) {w : ℂ} {X : ℝ} (hX : 0 < X)
    (hsq : ∀ x : ℂ, w.re < x.re → x.re < w.re + s → w.im < x.im → x.im < w.im + s → x ∈ Y)
    (hgood : setDistIn D (scaleSet s w (Icc (3 / 16) (5 / 16) ×ℂ Icc (1 / 16) (1 / 16)))
      (scaleSet s w (Icc (3 / 16) (5 / 16) ×ℂ Icc (15 / 16) (15 / 16)))
      (scaleSet s w (Ioo (1 / 8) (3 / 8) ×ℂ Ioo 0 1)) ≤ ENNReal.ofReal X) :
    ∃ P, VCr D Y s w P (2 * X) := by
  obtain ⟨P, hPc, hP0, hP1, hPm, hPl⟩ := exists_path_of_setDistIn_lt D
    (X := ENNReal.ofReal (2 * X))
    (hgood.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)))
  rw [mem_scaleSet_Icc hs] at hP0 hP1
  refine ⟨P, hPc, by linarith [hP0.2.1, hP0.2.2], by linarith [hP1.2.1, hP1.2.2],
    fun t ht => ?_, fun t ht => ?_, hPl.le⟩
  · have := (mem_scaleSet_Ioo hs _ _ _ _ _ _).1 (hPm ht)
    exact ⟨this.1.1.le, this.1.2.le⟩
  · have := (mem_scaleSet_Ioo hs _ _ _ _ _ _).1 (hPm ht)
    refine hsq _ ?_ ?_ (by linarith [this.2.1]) (by linarith [this.2.2])
    · nlinarith [this.1.1]
    · nlinarith [this.1.2]

/-- the open dyadic square lies in `𝕣𝕊` -/
lemma dySq_sub {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) {n j k : ℕ} (hj : j < 2 ^ n) (hk : k < 2 ^ n) (x : ℂ)
    (h1 : (dyCorner 𝕣 n j k).re < x.re) (h2 : x.re < (dyCorner 𝕣 n j k).re + 𝕣 / 2 ^ n)
    (h3 : (dyCorner 𝕣 n j k).im < x.im) (h4 : x.im < (dyCorner 𝕣 n j k).im + 𝕣 / 2 ^ n) :
    x ∈ rS 𝕣 := by
  simp only [dyCorner] at h1 h2 h3 h4
  have hs : 0 < 𝕣 / 2 ^ n := by positivity
  have hj' : (j : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hj
  have hk' : (k : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hk
  have e : (2 : ℝ) ^ n * (𝕣 / 2 ^ n) = 𝕣 := by field_simp
  rw [mem_rS_iff h𝕣]
  refine ⟨by nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j)], by nlinarith, by
    nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)], by nlinarith⟩

/-- **Scaling at all dyadic scales** (T:1890, Theorem 1.5 + Axiom V) -/
lemma scale_ratio_dyadic {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) (hS : DFGPSScaling) {ζ : ℝ} (hζ : 0 < ζ)
    (hζQ : ζ < xiGamma γ * Q γ) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ n : ℕ, ∀ r : ℝ, 0 < r →
      c (r / 2 ^ n) ≤ K₀ * ((1 / 2) ^ n) ^ (xiGamma γ * Q γ - ζ) * c r := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := hS γ hγ0 hγ2 D c hD ζ hζ
  obtain ⟨Λ, hΛ1, hΛ⟩ := hD.tightness.2.1
  set κ := xiGamma γ * Q γ - ζ with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  refine ⟨max 1 (Λ * δ₀ ^ (-Λ) * δ₀ ^ (-κ)), le_max_left _ _, fun n r hr => ?_⟩
  have hcr := hD.tightness.1 r hr
  set δ : ℝ := (1 / 2) ^ n with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hrδ : r / 2 ^ n = δ * r := by rw [hδdef, one_div, inv_pow]; ring
  rw [hrδ, ← div_le_iff₀ hcr]
  rcases eq_or_lt_of_le hδ1 with h1 | h1
  · rw [h1, one_mul, div_self hcr.ne', Real.one_rpow, mul_one]; exact le_max_left _ _
  rcases lt_or_ge δ δ₀ with h2 | h2
  · refine (hδ δ ⟨hδ0, h2⟩ r hr).2.trans ?_
    exact le_mul_of_one_le_left (Real.rpow_nonneg hδ0.le _) (le_max_left _ _)
  · refine (hΛ δ ⟨hδ0, h1⟩ r hr).2.trans ?_
    have hδ₀δ : δ₀ ^ κ ≤ δ ^ κ := Real.rpow_le_rpow hδ₀.le h2 hκ0.le
    have hΛδ : δ ^ (-Λ) ≤ δ₀ ^ (-Λ) :=
      Real.rpow_le_rpow_of_nonpos hδ₀ h2 (by linarith)
    have e : δ₀ ^ (-κ) * δ₀ ^ κ = 1 := by
      rw [← Real.rpow_add hδ₀]; simp
    calc Λ * δ ^ (-Λ) ≤ Λ * δ₀ ^ (-Λ) := by gcongr
      _ = Λ * δ₀ ^ (-Λ) * δ₀ ^ (-κ) * δ₀ ^ κ := by rw [mul_assoc _ (δ₀ ^ (-κ)), e, mul_one]
      _ ≤ max 1 (Λ * δ₀ ^ (-Λ) * δ₀ ^ (-κ)) * δ ^ κ := by
        gcongr
        exact le_max_right _ _

lemma Q_gt_two {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : 2 < Q γ := by
  unfold Q
  have : 0 < (2 - γ) ^ 2 / (2 * γ) := by
    apply div_pos _ (by positivity); nlinarith
  have e : 2 / γ + γ / 2 - 2 = (2 - γ) ^ 2 / (2 * γ) := by field_simp; ring
  linarith

lemma Q_add_sqrt {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    Q γ + Real.sqrt (Q γ ^ 2 - 4) = 4 / γ := by
  have h : Q γ ^ 2 - 4 = (2 / γ - γ / 2) ^ 2 := by unfold Q; field_simp; ring
  have hp : 0 ≤ 2 / γ - γ / 2 := by
    rw [sub_nonneg, div_le_div_iff₀ (by norm_num) hγ0]; nlinarith
  rw [h, Real.sqrt_sq hp]; unfold Q; ring

/-- **Choice of `q`** (T:1878, 1911–1912): the final exponent tends to `4d_γ/γ²` as `q → Q`. -/
lemma exists_q_exponent {γ a : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (ha : a < 4 * dGamma γ / γ ^ 2) :
    ∃ q : ℝ, 2 < q ∧ q < Q γ ∧ a < (q + Real.sqrt (q ^ 2 - 4) - (Q γ - q)) /
      (xiGamma γ + xiGamma γ * (Q γ - q) / 4) := by
  set ξ := xiGamma γ
  have hξ : 0 < ξ := DG.xiGamma_pos hγ0
  set f : ℝ → ℝ := fun q => (q + Real.sqrt (q ^ 2 - 4) - (Q γ - q)) / (ξ + ξ * (Q γ - q) / 4)
  have hf : ContinuousAt f (Q γ) := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simp only [sub_self, mul_zero, zero_div, add_zero]; exact hξ.ne'
  have hfQ : f (Q γ) = 4 * dGamma γ / γ ^ 2 := by
    simp only [f, sub_self, mul_zero, zero_div, add_zero, sub_zero]
    rw [Q_add_sqrt hγ0 hγ2]
    have hd := DG.dGamma_pos γ
    simp only [ξ, xiGamma]
    field_simp
  have h1 : ∀ᶠ q in 𝓝[<] Q γ, a < f q :=
    (hf.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds (hfQ ▸ ha))
  have h2 : ∀ᶠ q in 𝓝[<] Q γ, 2 < q :=
    nhdsWithin_le_nhds (lt_mem_nhds (Q_gt_two hγ0 hγ2))
  have h3 : ∀ᶠ q in 𝓝[<] Q γ, q < Q γ := self_mem_nhdsWithin
  obtain ⟨q, hq1, hq2, hq3⟩ := (h1.and (h2.and h3)).exists
  exact ⟨q, hq2, hq3, hq1⟩

end LQGMetric.DFGPS
