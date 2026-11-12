/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes56Diam at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes55
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Trans

/-!
# GM Lemma 5.6, the estimate (5.17) for the squares of `𝓢_{ε₁r}(B_{2r}(z))` (task P2-M2L3)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.6, l. 2969–2974: "Since `|u − v| ≥ b₁r` …, Axiom V (tightness across scales) together with
Lemma 2.8 (`lem-square-diam`) imply that we can find `ε₁ ∈ (0, b₁/100)` … such that with probability
at least `p₀/9` the event of Lemma 5.5 occurs and also (5.17)
`sup_{S ∈ 𝓢_{ε₁r}(B_{2r}(z))} sup_{w₁,w₂ ∈ S} D̃_h(w₁,w₂;S) ≤ (η/100) D̃_h(u,v)`."

`gm_L56_sqDiam` proves the probabilistic content: for every `θ > 0` (GM: `θ = η/100`), `b > 0`, and
failure probability `q > 0`, there is `ε₁ ∈ (0, ε₀)` such that, for every whole-plane GFF, every
`r > 0` and every `z`, with probability at least `1 − q`, simultaneously for all `u, v ∈ cl B_r(z)`
with `|u − v| ≥ br` and all squares `S ∈ 𝓢_{ε₁r}(B_{2r}(z))`, `internalDiam D_h S S ≤ θ D_h(u,v)`.
(GM need it for the random pair `(u,v)` of Lemma 5.5; the uniform statement implies it.)

Ingredients, as in GM:
* Axiom V in the form `Tight.gm_S2_4a_sep` (lower bound `D_h(u,v) > s 𝔠_r e^{ξ h_r(z')}` for
  separated points);
* GM Lemma 2.8 = DFGPS Lemma 3.20, second display (`Blueprint.DFGPSLem3_20`, grid squares of side
  `ε𝕣` at centre `0`, normalized field), applied to the recentred translate `h(· + z′) − h_1(z′)`
  where `z′ ∈ ε₁rℤ²` is a grid point near `z` (translation by a grid vector preserves the grid);
  Axiom IV′ (translation) and Axiom III (Weyl scaling by a constant) transfer it to `h`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- translating by a grid vector maps grid squares to grid squares -/
lemma image_gridSquare_sub (s : ℝ) (m k : ℤ × ℤ) :
    (fun w => w - gridPt s k) '' gridSquare s m = gridSquare s (m - k) := by
  ext x
  simp only [mem_image, gridSquare, mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  constructor
  · rintro ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [Complex.sub_re, Complex.sub_im, gridPt_re, gridPt_im]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨x + gridPt s k, ?_, by ring⟩
    simp only [Complex.add_re, Complex.add_im, gridPt_re, gridPt_im]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- a grid point within `2s` of `z` -/
lemma exists_gridPt_near {s : ℝ} (hs : 0 < s) (z : ℂ) : ∃ k : ℤ × ℤ, ‖z - gridPt s k‖ < 2 * s := by
  refine ⟨(⌊z.re / s⌋, ⌊z.im / s⌋), ?_⟩
  have e1 : (z - gridPt s (⌊z.re / s⌋, ⌊z.im / s⌋)).re = z.re - ⌊z.re / s⌋ * s := by
    rw [Complex.sub_re, gridPt_re, mul_comm]
  have e2 : (z - gridPt s (⌊z.re / s⌋, ⌊z.im / s⌋)).im = z.im - ⌊z.im / s⌋ * s := by
    rw [Complex.sub_im, gridPt_im, mul_comm]
  have b1 : ∀ t : ℝ, 0 ≤ t - ⌊t / s⌋ * s ∧ t - ⌊t / s⌋ * s < s := fun t => by
    have f1 := Int.floor_le (t / s)
    have f2 := Int.lt_floor_add_one (t / s)
    have g1 : (⌊t / s⌋ : ℝ) * s ≤ t := by rwa [le_div_iff₀ hs] at f1
    have g2 : t < ((⌊t / s⌋ : ℝ) + 1) * s := by rwa [div_lt_iff₀ hs] at f2
    constructor <;> nlinarith
  calc ‖z - gridPt s _‖ ≤ |(z - gridPt s (⌊z.re / s⌋, ⌊z.im / s⌋)).re| +
        |(z - gridPt s (⌊z.re / s⌋, ⌊z.im / s⌋)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < s + s := by
        rw [e1, e2, abs_of_nonneg (b1 _).1, abs_of_nonneg (b1 _).1]
        exact add_lt_add (b1 _).2 (b1 _).2
    _ = 2 * s := by ring

lemma xiQ_pos {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : 0 < xiGamma γ * (Q γ - 2) := by
  refine mul_pos (xiGamma_pos hγ0) ?_
  have : Q γ - 2 = (2 - γ) ^ 2 / (2 * γ) := by unfold Q; field_simp; ring
  rw [this]; exact div_pos (by nlinarith) (by positivity)

/-- the grid vector of `sℤ²` as a grid vector of the dyadic subgrid `2^{-j}sℤ²` -/
lemma gridPt_refine (s : ℝ) (j : ℕ) (k : ℤ × ℤ) :
    gridPt s k = gridPt ((2 : ℝ)⁻¹ ^ j * s) ((2 : ℤ) ^ j * k.1, (2 : ℤ) ^ j * k.2) := by
  have h2 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ two_ne_zero
  apply Complex.ext
  · rw [gridPt_re, gridPt_re]; push_cast; rw [inv_pow]; field_simp
  · rw [gridPt_im, gridPt_im]; push_cast; rw [inv_pow]; field_simp

/-- the uniform statement of GM (5.17), at every dyadic level `j` (DFGPS Lemma 3.20 has all levels):
the event that for all `u, v ∈ cl B_r(z)` with `|u − v| ≥ br` and every square `S` of side
`2^{-j}ε₁r` (corners in `2^{-j}ε₁rℤ²`) meeting `B_{3r}(z)`,
`internalDiam D_h S S ≤ 2^{-jχ} θ D_h(u,v)` -/
def sqDiamEvent (D : DistC → ContMetric) (χ b θ ε₁ r : ℝ) (z : ℂ) : Set DistC :=
  {g | ∀ u ∈ closedBall z r, ∀ v ∈ closedBall z r, b * r ≤ ‖u - v‖ →
    ∀ (j : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m ∩ ball z (3 * r)).Nonempty →
      internalDiam (D g) (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m)
        (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m) ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * (θ * (D g).1 (u, v)))}

/-- **GM (5.17)** (l. 2969–2974, Axiom V and GM Lemma 2.8 = DFGPS Lemma 3.20), uniformly over
separated pairs and at every dyadic level: see the module docstring -/
theorem gm_L56_sqDiam (h320 : DFGPSLem3_20) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {χ : ℝ} (hχ0 : 0 < χ)
    (hχQ : χ < xiGamma γ * (Q γ - 2)) {b θ q ε₀ : ℝ}
    (hb : 0 < b) (hθ : 0 < θ) (hq : 0 < q) (hε₀ : 0 < ε₀) :
    ∃ ε₁ ∈ Ioo (0 : ℝ) ε₀, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
      ∀ z : ℂ, P (h ⁻¹' sqDiamEvent D χ b θ ε₁ r z)ᶜ ≤ ENNReal.ofReal q := by
  set ξ := xiGamma γ with hξ
  set K₁ : Set ℂ := closedBall 0 2
  set K₂ : Set ℂ := closedBall 0 5
  have hq2 : (0 : ℝ≥0∞) < ENNReal.ofReal (q / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨s, hs, H1⟩ := Tight.gm_S2_4a_sep hD (isCompact_closedBall (0 : ℂ) 2) hb hq2
  obtain ⟨-, p, hp, C, ε₂, hε₂, H2⟩ := h320 γ hγ0 hγ2 D c hD K₂ (isCompact_closedBall _ _) χ hχ0
    hχQ
  obtain ⟨a₀, ha₀, ha₀ε, hB⟩ := gm_exists_small_rpow (C := C) hp hε₂ (by linarith : 0 < q / 2)
  set ε₁ : ℝ := min (min a₀ ((θ * s) ^ χ⁻¹)) (min (ε₀ / 2) (1 / 8)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (lt_min ha₀ (Real.rpow_pos_of_pos (by positivity) _))
    (lt_min (by linarith) (by norm_num))
  have hε₁a : ε₁ ≤ a₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₁8 : ε₁ ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hε₁χ : ε₁ ^ χ ≤ θ * s := by
    have h1 : ε₁ ≤ (θ * s) ^ χ⁻¹ := (min_le_left _ _).trans (min_le_right _ _)
    have := Real.rpow_le_rpow hε₁0.le h1 hχ0.le
    rwa [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hχ0.ne', Real.rpow_one] at this
  refine ⟨ε₁, ⟨hε₁0, lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)⟩,
    ?_⟩
  intro Ω _ P _ h hh r hr z
  set sr := ε₁ * r with hsr
  have hsr0 : 0 < sr := mul_pos hε₁0 hr
  obtain ⟨k, hk⟩ := exists_gridPt_near hsr0 z
  set z' := gridPt sr k with hz'
  -- the recentred translate `h(· + z′) − h_1(z′)`
  have hw : IsWholePlaneGFF (fun ω => affineComp 1 z' (h ω)) P := hh.affineComp one_pos z'
  have hm : Measurable fun ω => -circleAvg (h ω) 1 z' :=
    ((measurable_circleAvg_left 1 z').comp hh.measurable).neg
  set h' : Ω → DistC := fun ω => addConst (affineComp 1 z' (h ω)) (-circleAvg (h ω) 1 z')
  have hh' : IsNormalizedWPGFF h' P := by
    refine ⟨hw.addConst hm, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst hw 0 one_pos] with ω hω
    simp only [h', hω, Tight.circleAvg_affineComp_one, add_neg_cancel]
  have hT : ∀ᵐ ω ∂P, (∀ x y, (D (h' ω)).1 (x, y) =
      Real.exp (-(ξ * circleAvg (h ω) 1 z')) * (D (h ω)).1 (x + z', y + z')) ∧
      circleAvg (h' ω) r 0 = circleAvg (h ω) r z' - circleAvg (h ω) 1 z' := by
    filter_upwards [hD.translation P h (Tight.isGFFPlusCont_of_wp hh) z',
      hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hw),
      CircleAvg.ae_circleAvg_addConst hw 0 hr] with ω h1 h2 h3
    refine ⟨fun x y => ?_, ?_⟩
    · simp only [h']; rw [h2, mul_neg]; exact congrArg _ (h1 x y)
    · simp only [h']; rw [h3, Tight.circleAvg_affineComp_one, sub_eq_add_neg]
  set E1 : Set Ω := {ω | ∀ u ∈ K₁, ∀ v ∈ K₁, b ≤ ‖u - v‖ →
    s * c r * Real.exp (ξ * circleAvg (h ω) r z') < (D (h ω)).1 ((r : ℂ) * u + z', (r : ℂ) * v + z')}
  set E2 : Set Ω := h' ⁻¹' {g : DistC | ∀ (j : ℕ) (m : ℤ × ℤ),
    (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m ∩ scaleSet r 0 K₂).Nonempty →
    ENNReal.ofReal ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg g r 0)) *
      internalDiam (D g) (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m)
        (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j * ε₁) ^ χ)}
  have hP1 : P E1ᶜ ≤ ENNReal.ofReal (q / 2) := (H1 P h hh r hr z').le
  have hP2 : P E2ᶜ ≤ ENNReal.ofReal (q / 2) :=
    (H2 P h' hh' ε₁ ⟨hε₁0, lt_of_le_of_lt hε₁a ha₀ε⟩ r hr).trans
      (ENNReal.ofReal_le_ofReal (hB ε₁ ⟨hε₁0, hε₁a⟩))
  have hcr : 0 < c r := hD.tightness.1 r hr
  have hsub : (h ⁻¹' sqDiamEvent D χ b θ ε₁ r z)ᶜ ≤ᵐ[P] (E1ᶜ ∪ E2ᶜ : Set Ω) := by
    filter_upwards [hT] with ω ⟨hd1, hd2⟩
    intro hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨g1, g2⟩ := hcon
    apply hω
    intro u hu v hv huv j m hm
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hzz : ‖z - z'‖ < 2 * sr := hk
    -- lower bound for `D_h(u,v)`
    have hlow : s * c r * Real.exp (ξ * circleAvg (h ω) r z') < (D (h ω)).1 (u, v) := by
      have hK : ∀ x ∈ closedBall z r, (x - z') / r ∈ K₁ := fun x hx => by
        rw [mem_closedBall, dist_zero_right, norm_scale_back hr, div_le_iff₀ hr]
        have := mem_closedBall.1 hx
        rw [dist_eq_norm] at this
        calc ‖x - z'‖ ≤ ‖x - z‖ + ‖z - z'‖ := by
              rw [← sub_add_sub_cancel x z z']; exact norm_add_le _ _
          _ ≤ 2 * r := by nlinarith
      have := g1 _ (hK u hu) _ (hK v hv) (by
        rw [← sub_div, show (u - z') - (v - z') = u - v by ring, norm_div, Complex.norm_real,
          Real.norm_of_nonneg hr.le, le_div_iff₀ hr]; exact huv)
      rwa [scale_back hr, scale_back hr] at this
    -- the square, translated to the grid at centre `0`
    set kj : ℤ × ℤ := ((2 : ℤ) ^ j * k.1, (2 : ℤ) ^ j * k.2)
    have hzj : z' = gridPt ((2 : ℝ)⁻¹ ^ j * ε₁ * r) kj := by
      rw [hz', gridPt_refine sr j k, hsr, mul_assoc]
    obtain ⟨x, hxS, hxB⟩ := hm
    have hne : (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) (m - kj) ∩ scaleSet r 0 K₂).Nonempty := by
      refine ⟨x - z', ?_, (x - z') / r, ?_, ?_⟩
      · rw [← image_gridSquare_sub, ← hzj]; exact ⟨x, hxS, rfl⟩
      · rw [mem_closedBall, dist_zero_right, norm_scale_back hr, div_le_iff₀ hr]
        have := mem_ball.1 hxB
        rw [dist_eq_norm] at this
        calc ‖x - z'‖ ≤ ‖x - z‖ + ‖z - z'‖ := by
              rw [← sub_add_sub_cancel x z z']; exact norm_add_le _ _
          _ ≤ 5 * r := by nlinarith
      · simp only; field_simp; ring
    have h2 := g2 j (m - kj) hne
    rw [← image_gridSquare_sub, ← hzj,
      DFGPS.internalDiam_transl_smul (Real.exp_pos _) z' hd1, hd2, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)] at h2
    have hkey : (c r)⁻¹ * Real.exp (-xiGamma γ * (circleAvg (h ω) r z' - circleAvg (h ω) 1 z')) *
        Real.exp (-(ξ * circleAvg (h ω) 1 z')) =
        (c r * Real.exp (ξ * circleAvg (h ω) r z'))⁻¹ := by
      rw [mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
      congr 2; rw [hξ]; ring
    rw [hkey] at h2
    set F := c r * Real.exp (ξ * circleAvg (h ω) r z') with hF
    have hF0 : 0 < F := mul_pos hcr (Real.exp_pos _)
    set Sq := gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m
    have h3 : internalDiam (D (h ω)) Sq Sq ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j * ε₁) ^ χ * F) := by
      have e : internalDiam (D (h ω)) Sq Sq =
          ENNReal.ofReal F * (ENNReal.ofReal F⁻¹ * internalDiam (D (h ω)) Sq Sq) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hF0.le, mul_inv_cancel₀ hF0.ne',
          ENNReal.ofReal_one, one_mul]
      rw [e, mul_comm _ F, ENNReal.ofReal_mul hF0.le]
      exact mul_le_mul_right h2 _
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2j : 0 ≤ ((2 : ℝ)⁻¹ ^ j) ^ χ := Real.rpow_nonneg (by positivity) _
    rw [Real.mul_rpow (by positivity) hε₁0.le]
    calc ((2 : ℝ)⁻¹ ^ j) ^ χ * ε₁ ^ χ * F ≤ ((2 : ℝ)⁻¹ ^ j) ^ χ * (θ * s) * F :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε₁χ h2j) hF0.le
      _ = ((2 : ℝ)⁻¹ ^ j) ^ χ * (θ * (s * c r * Real.exp (ξ * circleAvg (h ω) r z'))) := by
          rw [hF]; ring
      _ ≤ ((2 : ℝ)⁻¹ ^ j) ^ χ * (θ * (D (h ω)).1 (u, v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow.le hθ.le) h2j
  calc _ ≤ P (E1ᶜ ∪ E2ᶜ) := measure_mono_ae hsub
    _ ≤ P E1ᶜ + P E2ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) := add_le_add hP1 hP2
    _ = ENNReal.ofReal q := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

end LQGMetric.GM
