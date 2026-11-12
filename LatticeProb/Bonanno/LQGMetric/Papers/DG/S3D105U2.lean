/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105U2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105U1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Lemma 3.8, upper half, for `μ_{h^𝕍}`: the sharp upper tail of `μ(B(w,s))` (D105, P2)

Ding–Gwynne, arXiv:1807.01072, Lemma 3.8 (DG:1112–1150), upper half (DG:1124–1137): DG bound
`E μ_h(B_δ(z))^p ≤ δ^{f(p)+o(1)}`, `f(p) = (2 + γ²/2)p − γ²p²/2`, `p ∈ (1, 4/γ²)`, and apply
Markov and a union bound. Here (S3D105U1 for the ingredients), at a dyadic scale `δ = 2^{-m}` with
`s ≤ δ ≤ 2s`, on the event `𝓑ᶜ = {osc_{|u−v| ≤ δ} h̃_δ < T}` (DZZ Lemma 2.6, tail form
`sup_tail_of_wn`; `T = O(√(log δ⁻¹)) + κ₀ log δ⁻¹`, `P(𝓑) ≤ δ`):

`μ(B(w,s)) ≤ e^{γ²/2 (H + D) − γ²/2 Var h̃_δ(w) + γT} · e^{γ h̃_δ(w)} M̃_{γ,δ}(B(w,s))`,

and Markov with the product formula `lintegral_coarse_mul_tildeM` and the fine moment
`E M̃(B(w,s))^p ≤ C (2s)^{2p}` give `P[μ(B(w,s)) > t, 𝓑ᶜ] ≤ C t^{−p} s^{f(p) − η}` for every
`η > 0` (**`muHU_ball_upper_tail`**). DG's `o(1)` is the `η`; it comes from the `√(log δ⁻¹)`
oscillation and variance fluctuation of the coarse field over `B(w,s)` (own bookkeeping; DG take
the `L^p` bound as known, DG:1127).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace DG

open WhiteNoise DZZ GMCIdent GMCIdent4 GMCIdent5 SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **the sharp upper tail of `μ_{h^𝕍}(B(w,s))`** off a bad event `𝓑` (independent of `w`)
with `P(𝓑) ≤ C s`: `P[μ(B(w,s)) > t, 𝓑ᶜ] ≤ C t^{−p} s^{f(p) − η}`, `f(p) = (2+γ²/2)p − γ²p²/2`,
for `1 < p < 4/γ²`, `η > 0`, `w ∈ B̄(u, 3R/2)`, `B̄(u, 2R) ⊆ 𝕍` -/
theorem muHU_ball_upper_tail (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {p : ℝ} (hp1 : 1 < p) (hp : p < 4 / γ ^ 2) {u : ℂ} {R : ℝ} (hR : 0 < R)
    (hKU : closedBall u (2 * R) ⊆ openSquare) {η : ℝ} (hη : 0 < η) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ s : ℝ, 0 < s → s ≤ r₀ → ∃ Bad : Set Ω,
      P Bad ≤ ENNReal.ofReal (C * s) ∧ ∀ w ∈ closedBall u (3 * R / 2), ∀ t : ℝ, 0 < t →
      P ({ω | ENNReal.ofReal t < muHU W γ ω (ball w s)} \ Bad) ≤
        ENNReal.ofReal (C * t ^ (-p) * s ^ ((2 + γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 - η)) := by
  have hP := hW.isProbabilityMeasure
  have hp0 : 0 < p := by linarith
  obtain ⟨CM, hCMt, hCM⟩ := GMCIdent6.lintegral_tildeM_rpow_le_of_one_lt hW hγ hγ2 hp1 hp
  obtain ⟨c₀, hc₀, hV⟩ := exists_tildeVar_le
  obtain ⟨H, hH⟩ := (isCompact_closedBall u (2 * R)).exists_bound_of_continuousOn
    (continuousOn_hS_diag.mono hKU)
  set ε₁ : ℝ := 2 * η / (3 * p * γ ^ 2) with hε₁
  set ε₂ : ℝ := η / (6 * p * γ) with hε₂
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₂0 : 0 < ε₂ := by positivity
  set cF : ℝ := ferniqueCF * Real.sqrt (3 * 1076)
  set b₁ : ℝ := 2 * Real.sqrt 28
  set b₂ : ℝ := Real.sqrt (2 * (6 * 1076) * 5) with hb₂
  set K₀ : ℝ := (p ^ 2 - p) * γ ^ 2 / 2 * c₀ + p * γ ^ 2 / 2 * (H + ε₁ * c₀ + b₁ ^ 2 / (4 * ε₁)) +
    p * γ * 2 * (b₂ ^ 2 / (4 * ε₂) + cF) + 2 * p * Real.log 2
  set C : ℝ := max 2 (CM.toReal * Real.exp K₀)
  set r₀ : ℝ := min (R / 2) (min (1 / 4) (Real.exp (-(2 * (6 * 1076) / ε₂ ^ 2)) / 2))
  have hr₀ : 0 < r₀ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  refine ⟨C, r₀, hr₀, fun s hs hsr => ?_⟩
  have hsR : s ≤ R / 2 := hsr.trans (min_le_left _ _)
  have hs4 : s ≤ 1 / 4 := hsr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsE : 2 * s ≤ Real.exp (-(2 * (6 * 1076) / ε₂ ^ 2)) := by
    have := hsr.trans ((min_le_right _ _).trans (min_le_right _ _)); linarith
  obtain ⟨m, hm1, hm2⟩ := exists_dyadic_between hs (by linarith)
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by linarith
  set L : ℝ := Real.log δ⁻¹ with hL
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hδ0).2 (by linarith))
  have hLℓ : L ≤ Real.log s⁻¹ := Real.log_le_log (by positivity) (inv_anti₀ hs hm1)
  have hLbig : 2 * (6 * 1076) / ε₂ ^ 2 ≤ L := by
    have h1 : Real.log δ ≤ -(2 * (6 * 1076) / ε₂ ^ 2) := by
      rw [Real.log_le_iff_le_exp hδ0]; linarith
    rw [hL, Real.log_inv]; linarith
  set Y := coarseVer hW m
  set T : ℝ := 2 * (Real.sqrt (2 * (6 * 1076) * Real.log (2 * (⌈1 / δ⌉₊ : ℝ) ^ 2)) + cF + ε₂ * L)
    with hTdef
  set Bad : Set Ω := {ω | ∃ u' ∈ ferniqueBox 0 1, ∃ v ∈ ferniqueBox 0 1, ‖u' - v‖ ≤ δ ∧
    T ≤ |Y u' ω - Y v ω|}
  refine ⟨Bad, ?_, fun w hw t ht => ?_⟩
  · have htail := sup_tail_of_wn hW (wndKernelL2 openSquare (Ioi (δ ^ 2))) hδ0
      (fun u v => (pi_sq_norm_tildeHKernel_sub_le hW hδ0 u v).trans (by gcongr; norm_num)) Y
      (coarseVer_spec hW m).1 (fun x => (coarseVer_spec hW m).2.2 x) (x := ε₂ * L)
      (by positivity)
    rw [← ofReal_measureReal (measure_ne_top P Bad)]
    refine (ENNReal.ofReal_le_ofReal htail).trans (ENNReal.ofReal_le_ofReal ?_)
    have hexp : Real.exp (-(ε₂ * L) ^ 2 / (2 * (6 * 1076))) ≤ δ := by
      have e : δ = Real.exp (-L) := by rw [hL, Real.log_inv, neg_neg, Real.exp_log hδ0]
      rw [e, Real.exp_le_exp]
      have h' := (div_le_iff₀ (by positivity)).1 hLbig
      have : L * (2 * (6 * 1076)) ≤ (ε₂ * L) ^ 2 := by nlinarith
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]; linarith
    have hC2 : 2 ≤ C := le_max_left _ _
    nlinarith
  -- the coarse bound on `B(w,s)` off `Bad`
  have hw2 : w ∈ closedBall u (2 * R) := closedBall_subset_closedBall (by linarith) hw
  have hwball : ball w s ⊆ closedBall u (2 * R) := fun z hz => by
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    rw [mem_ball, dist_eq_norm] at hz
    calc ‖z - u‖ ≤ ‖z - w‖ + ‖w - u‖ := norm_sub_le_norm_sub_add_norm_sub z w u
      _ ≤ 2 * R := by linarith
  have hBV : ball w s ⊆ openSquare := hwball.trans hKU
  set V := tildeVar δ w
  set D : ℝ := b₁ * Real.sqrt (L + c₀)
  set E : ℝ := γ ^ 2 / 2 * (H + D) - γ ^ 2 / 2 * V + γ * T
  have hκ0 : 0 < Real.exp E := Real.exp_pos E
  set X : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (γ * Y w ω)) * tildeM hW γ m ω (ball w s)
  have hsub : {ω | ENNReal.ofReal t < muHU W γ ω (ball w s)} \ Bad ⊆
      {ω | ENNReal.ofReal (t / Real.exp E) ≤ X ω} := by
    rintro ω ⟨h1, h2⟩
    have hle := muHU_ball_le hW γ m ω (w := w) (s := s) hκ0.le (fun z hz => by
      have hzw : ‖z - w‖ ≤ δ := by
        rw [mem_ball, dist_eq_norm] at hz; linarith
      refine cDens_le_of hW m ω ((Real.le_norm_self _).trans (hH z (hwball hz))) ?_ ?_ hγ.le
      · refine (tildeVar_sub_le hW hδ0 (B := L + c₀) (fun v => hV m v) w z).trans ?_
        have h28 : Real.sqrt (28 * ‖w - z‖ / δ) ≤ Real.sqrt 28 := by
          refine Real.sqrt_le_sqrt ?_
          rw [div_le_iff₀ hδ0, norm_sub_rev]; nlinarith [norm_nonneg (z - w)]
        have := Real.sqrt_nonneg (L + c₀)
        simp only [D, b₁]; nlinarith
      · by_contra hcon
        push Not at hcon
        exact h2 ⟨z, openSquare_subset_ferniqueBox (hBV hz), w,
          openSquare_subset_ferniqueBox (hKU hw2), hzw, hcon.le.trans (le_abs_self _)⟩)
    show ENNReal.ofReal (t / Real.exp E) ≤ X ω
    refine le_of_not_gt fun hlt => ?_
    have : ENNReal.ofReal (Real.exp E) * X ω ≤ ENNReal.ofReal t := by
      calc ENNReal.ofReal (Real.exp E) * X ω
          ≤ ENNReal.ofReal (Real.exp E) * ENNReal.ofReal (t / Real.exp E) := by gcongr
        _ = ENNReal.ofReal t := by
          rw [← ENNReal.ofReal_mul hκ0.le]; congr 1; field_simp
    exact absurd (lt_of_lt_of_le h1 hle) (not_lt.2 this)
  have hXm : AEMeasurable X P :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((coarseVer_spec hW m).2.1 w).const_mul γ))).aemeasurable.mul
      (aemeasurable_tildeM_open hW hγ hγ2 m isOpen_ball hBV)
  have hmark := meas_ofReal_le_rpow hXm (div_pos ht hκ0) hp0
  rw [lintegral_coarse_mul_tildeM hW hγ hγ2 m isOpen_ball hBV w hp0.le] at hmark
  -- the fine moment `E M̃(B(w,s))^p ≤ (2s)^{2p} C_M`
  have hfine : ∫⁻ ω, tildeM hW γ m ω (ball w s) ^ p ∂P ≤
      ENNReal.ofReal ((2 * s) ^ (2 * p)) * ENNReal.ofReal CM.toReal := by
    have h := hCM m w (2 * s) (ball w s) isOpen_ball hBV
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hm2
    set κ' : ℝ≥0∞ := ENNReal.ofReal (2 * s) ^ 2
    have hκ'0 : κ' ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hκ't : κ' ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have e : ∀ ω, tildeM hW γ m ω (ball w s) ^ p =
        κ' ^ p * (κ'⁻¹ * tildeM hW γ m ω (ball w s)) ^ p := fun ω => by
      rw [← GMCIdent6.mul_rpow_of_pos_ne_top hκ'0 hκ't, ← mul_assoc,
        ENNReal.mul_inv_cancel hκ'0 hκ't, one_mul]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le hκ't),
      ENNReal.ofReal_toReal hCMt]
    have e2 : κ' ^ p = ENNReal.ofReal ((2 * s) ^ (2 * p)) := by
      simp only [κ']
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_pos (by positivity)]
      norm_num
    rw [e2]; gcongr
  refine (measure_mono hsub).trans (hmark.trans ?_)
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfine zero_le)
    zero_le).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real inequality: exponents
  set e := (2 + γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 - η
  have hls : Real.log s = -Real.log s⁻¹ := by rw [Real.log_inv, neg_neg]
  set ℓ := Real.log s⁻¹
  have hl2s : Real.log (2 * s) = Real.log 2 - ℓ := by
    rw [Real.log_mul (by norm_num) hs.ne', hls]; ring
  have r1 : (t / Real.exp E) ^ (-p) = t ^ (-p) * Real.exp (p * E) := by
    rw [Real.div_rpow ht.le hκ0.le, ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg]
    congr 2; ring
  have r2 : (2 * s) ^ (2 * p) = Real.exp (Real.log (2 * s) * (2 * p)) :=
    Real.rpow_def_of_pos (by positivity) _
  have r3 : s ^ e = Real.exp (Real.log s * e) := Real.rpow_def_of_pos hs _
  rw [r1, r2, r3]
  -- the exponent inequality
  have hDt : D ≤ ε₁ * (L + c₀) + b₁ ^ 2 / (4 * ε₁) := mul_sqrt_le_lin hε₁0 (by linarith)
  have hsq : Real.sqrt (2 * (6 * 1076) * Real.log (2 * (⌈1 / δ⌉₊ : ℝ) ^ 2)) ≤
      b₂ * Real.sqrt L := by
    have hlog : Real.log (2 * (⌈1 / δ⌉₊ : ℝ) ^ 2) ≤ 5 * L := DZZ.log_two_ceil_sq_le hδ0 hδ2
    have h' : Real.sqrt (2 * (6 * 1076) * Real.log (2 * (⌈1 / δ⌉₊ : ℝ) ^ 2)) ≤
        Real.sqrt (2 * (6 * 1076) * 5 * L) := Real.sqrt_le_sqrt (by linarith)
    rw [hb₂, ← Real.sqrt_mul (by norm_num)]; exact h'
  have hTt : T ≤ 2 * (ε₂ * L + b₂ ^ 2 / (4 * ε₂) + cF + ε₂ * L) := by
    have := mul_sqrt_le_lin (b := b₂) hε₂0 hL0; rw [hTdef]; linarith
  have i1 : p * γ ^ 2 / 2 * ε₁ = η / 3 := by
    rw [hε₁]; field_simp
  have i2 : p * γ * 2 * ε₂ = η / 3 := by
    rw [hε₂]; field_simp; ring
  have hexpo : p * E + (p ^ 2 * γ ^ 2 / 2 * V) + Real.log (2 * s) * (2 * p) ≤
      K₀ + Real.log s * e := by
    rw [hl2s, hls]
    exact upper_expo_aux hp1 hγ hη hLℓ (hV m w) hDt hTt i1 i2
  have hC : CM.toReal * Real.exp K₀ ≤ C := le_max_right _ _
  have hCM0 : 0 ≤ CM.toReal := ENNReal.toReal_nonneg
  have ht0 : 0 < t ^ (-p) := Real.rpow_pos_of_pos ht _
  calc t ^ (-p) * Real.exp (p * E) * (Real.exp (p ^ 2 * γ ^ 2 / 2 * V) *
        (Real.exp (Real.log (2 * s) * (2 * p)) * CM.toReal))
      = CM.toReal * t ^ (-p) * Real.exp (p * E + (p ^ 2 * γ ^ 2 / 2 * V) +
          Real.log (2 * s) * (2 * p)) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ CM.toReal * t ^ (-p) * Real.exp (K₀ + Real.log s * e) := by gcongr
    _ = CM.toReal * Real.exp K₀ * t ^ (-p) * Real.exp (Real.log s * e) := by
        rw [Real.exp_add]; ring
    _ ≤ C * t ^ (-p) * Real.exp (Real.log s * e) := by gcongr

/-- **DG Lemma 3.8, upper half, from the upper tail off a bad event** (grid union bound,
DG:1131–1137): if for `s ≤ r₀` there is `𝓑` with `P(𝓑) ≤ C s` and
`P[μ(B(w,s)) > t, 𝓑ᶜ] ≤ C t^{−q} s^e` for `w ∈ B̄(u, 3R/2)`, and `β(e − 2) − q > 0`, then with
polynomially high probability every `B(z, ε^β)`, `z ∈ B̄(u,R)`, has `μ`-mass `≤ ε`. -/
theorem dgL38Upper_of_tail {μ : Ω → Measure ℂ} {u : ℂ} {R r₀ C q e β : ℝ} (hR : 0 < R)
    (hr₀ : 0 < r₀) (hβ : 0 < β) (hexp : 0 < β * (e - 2) - q)
    (htail : ∀ s : ℝ, 0 < s → s ≤ r₀ → ∃ Bad : Set Ω, P Bad ≤ ENNReal.ofReal (C * s) ∧
      ∀ w ∈ closedBall u (3 * R / 2), ∀ t : ℝ, 0 < t →
        P ({ω | ENNReal.ofReal t < μ ω (ball w s)} \ Bad) ≤
          ENNReal.ofReal (C * t ^ (-q) * s ^ e)) :
    DGL38Upper P μ (closedBall u R) β := by
  set m₀ : ℝ := min 1 (min (r₀ / 2) (R / 6)) with hm₀
  have hm0 : 0 < m₀ := lt_min one_pos (lt_min (by positivity) (by positivity))
  set c₀ : ℝ := 2 * (‖u‖ + R) + 9
  have hc₀ : 0 < c₀ := by positivity
  set p' : ℝ := min β (β * (e - 2) - q)
  refine ⟨p', 2 * |C| + c₀ ^ 2 * |C| * 2 ^ e, m₀ ^ β⁻¹, lt_min hβ hexp,
    Real.rpow_pos_of_pos hm0 _, fun ε hε hεm => ?_⟩
  have hεβm : ε ^ β < m₀ := by
    have := Real.rpow_lt_rpow hε.le hεm hβ
    rwa [Real.rpow_inv_rpow hm0.le hβ.ne'] at this
  have hm1 : m₀ ≤ 1 := min_le_left _ _
  have hε1 : ε < 1 := by
    by_contra h; push Not at h
    have := Real.one_le_rpow h hβ.le; linarith
  set g : ℝ := ε ^ β with hg_def
  have hg : 0 < g := Real.rpow_pos_of_pos hε β
  have hg1 : g ≤ 1 := by linarith
  have hgr : 2 * g ≤ r₀ := by
    have : g < r₀ / 2 := hεβm.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hgR : R + 3 * g ≤ 3 * R / 2 := by
    have : g < R / 6 := hεβm.trans_le ((min_le_right _ _).trans (min_le_right _ _)); linarith
  obtain ⟨Bad, hBad, hT⟩ := htail (2 * g) (by positivity) hgr
  set E : ℂ → Set Ω := fun w => {ω | ENNReal.ofReal ε < μ ω (ball w (2 * g))} \ Bad
  have hsub : {ω | ¬ ∀ z ∈ closedBall u R, μ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε} ⊆
      Bad ∪ {ω | ∃ i j : ℤ, ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ R + 3 * g ∧
        ω ∈ E ⟨i * g, j * g⟩} := by
    intro ω hω
    by_cases hB : ω ∈ Bad
    · exact Or.inl hB
    right
    push Not at hω
    obtain ⟨z, hz, hzm⟩ := hω
    obtain ⟨i, j, hij⟩ := exists_grid_near z hg
    refine ⟨i, j, ?_, ?_, hB⟩
    · rw [mem_closedBall, dist_eq_norm] at hz
      calc ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ ‖(⟨i * g, j * g⟩ : ℂ) - z‖ + ‖z - u‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ R + 3 * g := by linarith
    · refine lt_of_lt_of_le hzm (measure_mono fun y hy => ?_)
      rw [mem_ball, dist_eq_norm] at hy ⊢
      calc ‖y - ⟨i * g, j * g⟩‖ ≤ ‖y - z‖ + ‖z - ⟨i * g, j * g⟩‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < 2 * g := by rw [norm_sub_rev z]; linarith
  have hgrid := prob_grid_event_le (P := P) (E := E) (u := u) (R := R) (g := g)
    (A := C * ε ^ (-q) * (2 * g) ^ e) hR.le hg
    (fun w hw => hT w (closedBall_subset_closedBall hgR hw) ε hε)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  -- the count, as in `dgL38Lower_of_tail`
  set x : ℝ := (‖u‖ + (R + 3 * g)) / g with hx
  have hx0 : 0 < x := by positivity
  have hceil : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hceil0 : (0 : ℝ) ≤ 2 * (⌈x⌉ : ℝ) + 1 := by
    have : (0 : ℝ) < (⌈x⌉ : ℝ) := by exact_mod_cast (Int.ceil_pos.2 hx0)
    linarith
  have hN : 2 * (⌈x⌉ : ℝ) + 1 ≤ c₀ / g := by
    have e : c₀ / g = 2 * x + 3 + (2 * (‖u‖ + R) + 9 - (2 * (‖u‖ + R) + 9 * g)) / g := by
      rw [hx]; field_simp; ring
    have hnn : 0 ≤ (2 * (‖u‖ + R) + 9 - (2 * (‖u‖ + R) + 9 * g)) / g :=
      div_nonneg (by linarith) hg.le
    rw [e]; linarith
  have hN2 : (2 * (⌈x⌉ : ℝ) + 1) ^ 2 ≤ c₀ ^ 2 / g ^ 2 := by
    rw [← div_pow]; exact pow_le_pow_left₀ hceil0 hN 2
  have hT0 : 0 ≤ |C| * ε ^ (-q) * (2 * g) ^ e := by positivity
  have hpe1 : ε ^ (β * (e - 2) - q) ≤ ε ^ p' :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1.le (min_le_right _ _)
  have hpe2 : ε ^ β ≤ ε ^ p' := Real.rpow_le_rpow_of_exponent_ge hε hε1.le (min_le_left _ _)
  have hcount : (2 * (⌈x⌉ : ℝ) + 1) ^ 2 * (C * ε ^ (-q) * (2 * g) ^ e) ≤
      c₀ ^ 2 * |C| * 2 ^ e * ε ^ p' := by
    calc (2 * (⌈x⌉ : ℝ) + 1) ^ 2 * (C * ε ^ (-q) * (2 * g) ^ e)
        ≤ (2 * (⌈x⌉ : ℝ) + 1) ^ 2 * (|C| * ε ^ (-q) * (2 * g) ^ e) :=
          mul_le_mul_of_nonneg_left (by gcongr; exact le_abs_self C) (sq_nonneg _)
      _ ≤ c₀ ^ 2 / g ^ 2 * (|C| * ε ^ (-q) * (2 * g) ^ e) :=
          mul_le_mul_of_nonneg_right hN2 hT0
      _ = c₀ ^ 2 * |C| * 2 ^ e * ε ^ (β * (e - 2) - q) := upper_rpow_alg hε
      _ ≤ c₀ ^ 2 * |C| * 2 ^ e * ε ^ p' := by gcongr
  have hbad : C * (2 * g) ≤ 2 * |C| * ε ^ p' := by
    have : C * (2 * g) ≤ |C| * (2 * g) := by gcongr; exact le_abs_self C
    rw [hg_def] at this
    nlinarith [abs_nonneg C]
  refine (add_le_add (hBad.trans (ENNReal.ofReal_le_ofReal hbad))
    (hgrid.trans (ENNReal.ofReal_le_ofReal hcount))).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- DG's optimal moment (3.13): for `β > 2/(2−γ)²`, `p = (2 + γ²/2 − β⁻¹)/γ²` lies in `(1, 4/γ²)`
and `β (f(p) − 2) − p = β (a² − 4γ²)/(2γ²) > 0`, `a = 2 + γ²/2 − β⁻¹ > 2γ` -/
lemma dgL38Upper_exponent {γ β : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : 2 / (2 - γ) ^ 2 < β) :
    ∃ p : ℝ, 1 < p ∧ p < 4 / γ ^ 2 ∧
      0 < β * ((2 + γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 - 2) - p := by
  have h2γ : 0 < (2 - γ) ^ 2 := by nlinarith
  have hβ0 : 0 < β := lt_trans (by positivity) hβ
  have h2 : 2 < β * (2 - γ) ^ 2 := (div_lt_iff₀ h2γ).1 hβ
  set ib := β⁻¹ with hib
  have hib0 : 0 < ib := inv_pos.2 hβ0
  have hib1 : β * ib = 1 := mul_inv_cancel₀ hβ0.ne'
  have hibl : ib < (2 - γ) ^ 2 / 2 := by nlinarith
  set a := 2 + γ ^ 2 / 2 - ib with ha
  have hγ2' : 0 < γ ^ 2 := by positivity
  refine ⟨a / γ ^ 2, ?_, ?_, ?_⟩
  · rw [one_lt_div hγ2']; nlinarith
  · exact div_lt_div_of_pos_right (by nlinarith) hγ2'
  · have key : β * ((2 + γ ^ 2 / 2) * (a / γ ^ 2) - γ ^ 2 * (a / γ ^ 2) ^ 2 / 2 - 2) -
        a / γ ^ 2 = β * ((a ^ 2 - 4 * γ ^ 2) / (2 * γ ^ 2)) := by
      field_simp
      rw [ha]
      linear_combination (γ ^ 2 + 4 - 2 * ib) * hib1
    rw [key]
    have ha2 : 2 * γ < a := by rw [ha]; nlinarith
    have : 0 < a ^ 2 - 4 * γ ^ 2 := by nlinarith
    positivity

/-- **DG Lemma 3.8, upper half** (DG:1112–1150, second estimate of (3.11)) for the LQG measure
`μ_{h^𝕍}` of the white-noise zero-boundary GFF on `𝕍`, on a closed ball `B̄(u,R)` with
`B̄(u,2R) ⊆ 𝕍`, for every `β > 2/(2−γ)²`: with polynomially high probability as `ε → 0`,
`sup_{z ∈ B̄(u,R)} μ(B_{ε^β}(z)) ≤ ε`. -/
theorem dgL38Upper_muHU (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {u : ℂ}
    {R : ℝ} (hR : 0 < R) (hKU : closedBall u (2 * R) ⊆ openSquare) {β : ℝ}
    (hβ : 2 / (2 - γ) ^ 2 < β) :
    DGL38Upper P (fun ω => muHU W γ ω) (closedBall u R) β := by
  have hβ0 : 0 < β := lt_trans (by have : 0 < (2 - γ) ^ 2 := by nlinarith
                                   positivity) hβ
  obtain ⟨p, hp1, hp, hgap⟩ := dgL38Upper_exponent hγ hγ2 hβ
  set gap := β * ((2 + γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 - 2) - p
  obtain ⟨C, r₀, hr₀, htail⟩ := muHU_ball_upper_tail hW hγ hγ2 hp1 hp hR hKU
    (η := gap / (2 * β)) (by positivity)
  refine dgL38Upper_of_tail hR hr₀ hβ0 ?_ htail
  have e : β * ((2 + γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 - gap / (2 * β) - 2) - p = gap / 2 := by
    simp only [gap]; field_simp; ring
  rw [e]; positivity

end DG
end LQGMetric
