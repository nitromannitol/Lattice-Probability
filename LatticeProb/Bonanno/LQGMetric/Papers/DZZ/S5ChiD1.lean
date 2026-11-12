/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5ChiD1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiA3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiC2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiB1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiB2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim6E
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W12
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Ind

/-!
# The exponent identification `DZZChiIdent` (D129, packet P-129D: assembly)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`: Theorem 1.1 (l. 126–141, the a.s.
statement and the "amalgamation" along dyadic `δ`), Prop 5.1 (l. 2254–2258; proof l. 2306–2350)
and L2.12 (`lem-obvious-bounds`, l. 740–759). Decision D129 (`decisions/DEC-129.md` §1, §4 P-129D).

For `u ≠ v ∈ 𝕍°` and `ι > 0`:
* upper bound: D97's sandwich `D_δ(u,v) ≤ D^𝕍_{δ e^{−a/2}}(u,v)` (`ae_lgd_sandwich_wick_K`, P-129B)
  and the rate bound `hasRate_dzzMuIn_upper_interior` (P-129A) at the scales `e^{−a/2} 2^{−k}`;
* lower bound: the `K`-walled lower half of the sandwich at `U = 𝕍°_{u,λ}`, `K = 𝕍_{u,2λ}`, and
  the rate bound `hasRate_dzzMuIn_lower_box` (P-129B) at the scales `e^{b/2} 2^{−k}`;
* Borel–Cantelli (`HasRate.ae_eventually`, P-129A) for `ι = 1/(n+1)`, all `n` (`ae_all_iff`);
* the constant factors `e^{−a/2}`, `e^{b/2}` cost `O(1/k)` in the ratio; dyadic reduction
  `lgdEvent_iff_dyadic` (GMCIdent4LGD; DZZ l. 135–141); transfer to the statement layer's
  zero-boundary GFF by `isLGDExponent_iff_wn'` (GMCIdent5Ind).
* `χ > 0`: DZZ L2.12 (P-129C, `chi_pos_of_lem53`, S5ChiC2).

P-129B's results enter directly: `ae_lgd_sandwich_wick_K` (S5ChiB1), `hasRate_dzzMuIn_lower_box`
(S5ChiB2); the walls hypothesis is discharged by `dzzProp317WallsAll_holds` (S5WallSim6E).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

/-! ### Elementary conversions -/

lemma log_toNat_le_of_le_ofReal {N : ℕ∞} (h1 : 1 ≤ N) {t : ℝ}
    (h : (N : ℝ≥0∞) ≤ ENNReal.ofReal t) : Real.log N.toNat ≤ Real.log t := by
  have hN : N ≠ ⊤ := fun hT => by
    rw [hT, ENat.toENNReal_top] at h; exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hN
  have hn : 1 ≤ n := by exact_mod_cast h1
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast] at h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : (n : ℝ) ≤ t := by
    rcases ENNReal.ofReal_le_ofReal_iff'.1 h with h' | h'
    · exact h'
    · linarith
  rw [ENat.toNat_natCast]
  exact Real.log_le_log (by exact_mod_cast hn) ht

lemma log_le_log_toNat_of_ofReal_le {N : ℕ∞} (hN : N ≠ ⊤) {t : ℝ} (ht : 0 < t)
    (h : ENNReal.ofReal t ≤ (N : ℝ≥0∞)) : Real.log t ≤ Real.log N.toNat := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hN
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast] at h
  rw [ENat.toNat_natCast]
  exact Real.log_le_log ht ((ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg n)).1 h)

/-- `log (s 2^{-k})^{-p} = p (k log 2 − log s)` -/
lemma log_rpow_neg_scale {s : ℝ} (hs : 0 < s) (p : ℝ) (k : ℕ) :
    Real.log ((s * (2 : ℝ)⁻¹ ^ k) ^ (-p)) = p * (k * Real.log 2 - Real.log s) := by
  rw [Real.log_rpow (by positivity), Real.log_mul hs.ne' (by positivity), Real.log_pow,
    Real.log_inv]
  ring

/-- the deterministic squeeze: two-sided bounds `(χ ∓ ι_n)(k log 2 − log s)` for every `n`
give `f k / (k log 2) → χ`. -/
lemma tendsto_div_of_bounds {f : ℕ → ℝ} {χ s₁ s₂ : ℝ}
    (hup : ∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
      f k ≤ (χ + 1 / ((n : ℝ) + 1)) * (k * Real.log 2 - Real.log s₁))
    (hlo : ∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
      (χ - 1 / ((n : ℝ) + 1)) * (k * Real.log 2 - Real.log s₂) ≤ f k) :
    Tendsto (fun k : ℕ => f k / (k * Real.log 2)) atTop (𝓝 χ) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the comparison functions
  have hg : ∀ (c s : ℝ), Tendsto (fun k : ℕ => c - (c * Real.log s / Real.log 2) / k) atTop
      (𝓝 c) := fun c s => by
    simpa using (tendsto_const_nhds (x := c)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (c * Real.log s / Real.log 2))
  have hkey : ∀ (c s : ℝ) (k : ℕ), 1 ≤ k →
      c * (k * Real.log 2 - Real.log s) / (k * Real.log 2) =
        c - (c * Real.log s / Real.log 2) / k := fun c s k hk => by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    field_simp
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < (k : ℝ) * Real.log 2 ∧ 1 ≤ k :=
    (eventually_ge_atTop 1).mono fun k hk =>
      ⟨mul_pos (by exact_mod_cast hk) hL, hk⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 ha)
    have h1 := (hg (χ - 1 / ((n : ℝ) + 1)) s₂).eventually (lt_mem_nhds (show a < χ - 1 / ((n : ℝ) + 1) by linarith))
    filter_upwards [h1, hlo n, hpos] with k hk1 hk2 ⟨hk3, hk4⟩
    rw [← hkey _ _ k hk4] at hk1
    exact hk1.trans_le (div_le_div_of_nonneg_right hk2 hk3.le)
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 ha)
    have h1 := (hg (χ + 1 / ((n : ℝ) + 1)) s₁).eventually (gt_mem_nhds (show χ + 1 / ((n : ℝ) + 1) < a by linarith))
    filter_upwards [h1, hup n, hpos] with k hk1 hk2 ⟨hk3, hk4⟩
    rw [← hkey _ _ k hk4] at hk1
    exact (div_le_div_of_nonneg_right hk2 hk3.le).trans_lt hk1

/-! ### The geometry of the boxes `𝕍°_{u,λ} ⊆ 𝕍_{u,2λ}` -/

/-- own elementary geometry: a box `𝕍°_{u,λ}` around `u ∈ 𝕍°` avoiding `v`, with all the
hypotheses of the `K`-walled sandwich for `K = 𝕍_{u,2λ}`, `r = λ/8`. -/
lemma chiD_box_geom {u v : ℂ} (hu : u ∈ openSquare) (huv : u ≠ v) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 / 20 ∧ sqBox u (2 * lam) ⊆ openSquare ∧
      u ∈ openBoxC u lam ∧ v ∉ openBoxC u lam ∧
      (∀ p ∈ closure (openBoxC u lam), ∀ z ∉ sqBox u (2 * lam), 4 * (lam / 8) ≤ dist p z) ∧
      thickening (4 * (lam / 8)) (closure (openBoxC u lam)) ⊆ openSquare := by
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  set m := min (min u.re (1 - u.re)) (min u.im (1 - u.im)) with hm
  have a1 : m ≤ u.re := (min_le_left _ _).trans (min_le_left _ _)
  have a2 : m ≤ 1 - u.re := (min_le_left _ _).trans (min_le_right _ _)
  have a3 : m ≤ u.im := (min_le_right _ _).trans (min_le_left _ _)
  have a4 : m ≤ 1 - u.im := (min_le_right _ _).trans (min_le_right _ _)
  have hm0 : 0 < m := lt_min (lt_min hu1 (by linarith)) (lt_min hu3 (by linarith))
  have hd : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 huv.symm)
  set lam := min (1 / 20) (min (‖v - u‖ / 2) (m / 2)) with hlam
  have hl0 : 0 < lam := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hl1 : lam ≤ 1 / 20 := min_le_left _ _
  have hl2 : lam ≤ ‖v - u‖ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hl3 : lam ≤ m / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hbox : sqBox u (2 * lam) ⊆ openSquare := fun z hz => by
    obtain ⟨h1, h2⟩ := hz
    rw [show 2 * lam / 2 = lam by ring] at h1 h2
    obtain ⟨h1a, h1b⟩ := abs_le.1 h1
    obtain ⟨h2a, h2b⟩ := abs_le.1 h2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  -- points of `closure 𝕍°_{u,λ}` are `λ/2`-close to `u` in each coordinate
  have hcl : ∀ p ∈ closure (openBoxC u lam), |p.re - u.re| ≤ lam / 2 ∧ |p.im - u.im| ≤ lam / 2 :=
    fun p hp => closure_openBoxC_subset u lam hp
  have hre : ∀ x y : ℂ, |x.re - y.re| ≤ dist x y := fun x y => by
    rw [dist_eq_norm, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have him : ∀ x y : ℂ, |x.im - y.im| ≤ dist x y := fun x y => by
    rw [dist_eq_norm, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
  refine ⟨lam, hl0, hl1, hbox, ?_, ?_, ?_, ?_⟩
  · exact Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · intro hv
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Complex.mem_reProdIm.1 hv
    have hn := Complex.norm_le_abs_re_add_abs_im (v - u)
    rw [Complex.sub_re, Complex.sub_im] at hn
    have e1 : |v.re - u.re| < lam / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    have e2 : |v.im - u.im| < lam / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  · intro p hp z hz
    obtain ⟨hp1, hp2⟩ := hcl p hp
    have hz' : ¬ (|z.re - u.re| ≤ lam ∧ |z.im - u.im| ≤ lam) := fun h =>
      hz ⟨by rw [show 2 * lam / 2 = lam by ring]; exact h.1,
        by rw [show 2 * lam / 2 = lam by ring]; exact h.2⟩
    rw [show 4 * (lam / 8) = lam / 2 by ring]
    rcases not_and_or.1 hz' with h | h
    · have t := abs_sub_le z.re p.re u.re
      rw [abs_sub_comm z.re p.re] at t
      linarith [hre p z]
    · have t := abs_sub_le z.im p.im u.im
      rw [abs_sub_comm z.im p.im] at t
      linarith [him p z]
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_thickening_iff.1 hz
    obtain ⟨hp1, hp2⟩ := hcl p hp
    rw [show 4 * (lam / 8) = lam / 2 by ring] at hzp
    refine hbox ⟨?_, ?_⟩ <;> rw [show 2 * lam / 2 = lam by ring]
    · linarith [abs_sub_le z.re p.re u.re, hre z p]
    · linarith [abs_sub_le z.im p.im u.im, him z p]

/-! ### The a.s. upgrade -/

/-- **The L5.3 exponent at `μIn` is the a.s. exponent of DZZ Theorem 1.1** (DZZ Thm 1.1,
l. 126–141, with Prop 5.1, l. 2254–2350; D129 §4 P-129D). -/
theorem isLGDExponent_of_lem53 {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {χ : ℝ} (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (hwalls : ∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) :
    IsLGDExponent γ χ := by
  rw [GMCIdent5.isLGDExponent_iff_wn' hW hγ hγ2 χ]
  intro u hu v hv huv
  obtain ⟨lam, hl0, hl1, hbox, huU, hvU, hCK, hCV⟩ := chiD_box_geom hu huv
  have hCU : IsCompact (closure (openBoxC u lam)) :=
    (isCompact_sqBox u hl0.le).of_isClosed_subset isClosed_closure (closure_openBoxC_subset u lam)
  obtain ⟨a, b, hsand⟩ := ae_lgd_sandwich_wick_K hW hγ hγ2 (isOpen_openBoxC u lam) hCU
    (isCompact_sqBox u (by positivity)) hbox (r := lam / 8) (by positivity) hCK hCV
  have hfr : frontier (openBoxC u lam) = frontier (sqBox u lam) := frontier_openBox_eq u hl0
  have hι : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hup := ae_all_iff.2 fun n : ℕ =>
    (hasRate_dzzMuIn_upper_interior hW hγ hγ2 hL hwalls hu hv huv (hι n)).ae_eventually
      (Real.exp_pos (-a / 2))
  have hlo := ae_all_iff.2 fun n : ℕ =>
    (hasRate_dzzMuIn_lower_box hW hγ hγ2 hL hwalls hu hl0 hl1 hbox (hι n)).ae_eventually
      (Real.exp_pos (b / 2))
  filter_upwards [hsand, hup, hlo] with ω ⟨δ₀, hδ₀, hsw⟩ hupω hloω
  rw [GMCIdent4.lgdEvent_iff_dyadic]
  simp_rw [GMCIdent4.log_inv_two_inv_pow]
  have hsmall : ∀ᶠ k : ℕ in atTop, (2 : ℝ)⁻¹ ^ k < δ₀ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (gt_mem_nhds hδ₀)
  have hupper : ∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
      ((lgdDZZ (qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare) ((2 : ℝ)⁻¹ ^ k) u v : ℕ∞) :
        ℝ≥0∞) ≤ ENNReal.ofReal ((Real.exp (-a / 2) * (2 : ℝ)⁻¹ ^ k) ^ (-(χ + 1 / ((n : ℝ) + 1)))) := by
    intro n
    filter_upwards [hupω n, hsmall] with k hk hk2
    have h1 := (hsw _ (by positivity) hk2 u huU v hvU).2
    rw [mul_comm ((2 : ℝ)⁻¹ ^ k)] at h1
    exact (ENat.toENNReal_le.2 h1).trans hk
  refine tendsto_div_of_bounds (s₁ := Real.exp (-a / 2)) (s₂ := Real.exp (b / 2))
    (fun n => ?_) (fun n => ?_)
  · filter_upwards [hupper n] with k hk
    rw [← log_rpow_neg_scale (Real.exp_pos _)]
    exact log_toNat_le_of_le_ofReal (one_le_lgdDZZ _ _ _ _) hk
  · filter_upwards [hupper 0, hloω n, hsmall] with k hk0 hk hk2
    have hfin : lgdDZZ (qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare) ((2 : ℝ)⁻¹ ^ k) u v
        ≠ ⊤ := fun hT => by
      rw [hT, ENat.toENNReal_top] at hk0; exact ENNReal.ofReal_ne_top (top_le_iff.1 hk0)
    have h1 := (hsw _ (by positivity) hk2 u huU v hvU).1
    rw [mul_comm ((2 : ℝ)⁻¹ ^ k), hfr] at h1
    rw [← log_rpow_neg_scale (Real.exp_pos _)]
    exact log_le_log_toNat_of_ofReal_le hfin (by positivity) (hk.trans (ENat.toENNReal_le.2 h1))

/-- **`DZZChiIdentW`** (D129 §1, exact statement). -/
theorem dzzChiIdentW :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ χ : ℝ, DZZLem53Exp P (dzzMuIn γ W) χ →
        (∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) →
        0 < χ ∧ IsLGDExponent γ χ := by
  intro Ω _ P W hW γ hγ hγ2 χ hL hw
  exact ⟨chi_pos_of_lem53 hW hγ hγ2 hL, isLGDExponent_of_lem53 hW hγ hγ2 hL hw⟩

/-- **`DZZInW.DZZChiIdent` holds**: `dzzChiIdentW` with the walled P3.17
`dzzProp317WallsAll_holds` (S5WallSim6E) (D129 §1 adapter `dzzChiIdent_of`). -/
theorem dzzChiIdent_holds : DZZInW.DZZChiIdent := by
  intro Ω _ P W hW γ hγ hγ2 χ hL
  exact dzzChiIdentW P W hW γ hγ hγ2 χ hL (dzzProp317WallsAll_holds P W hW γ hγ hγ2)

end DZZ
end LQGMetric
