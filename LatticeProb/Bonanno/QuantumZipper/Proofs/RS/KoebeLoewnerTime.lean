/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.KoebeLoewnerTime at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.KoebeLoewner
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.SmallStep
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TraceRadial

/-!
# EXT-RS node KD(b): the Loewner time step (Kemppainen Lemma 6.7)

A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs Math. Phys. 24 (2017), Lemma 6.7,
p. 110 (proof pp. 110–111): there is a constant `C` such that for the inverse Loewner maps
`f_t = g_t⁻¹`, every `x + iy ∈ ℍ`, `t ≥ 0` and `s ∈ [0, y²]`,

* `C⁻¹|f_t'(x+iy)| ≤ |f_{t+s}'(x+iy)| ≤ C|f_t'(x+iy)|`   (6.14),
* `|f_{t+s}(x+iy) − f_t(x+iy)| ≤ C y |f_t'(x+iy)|`       (6.15).

## Project form

The project's `fwdMapInv W t` is the *centred* inverse map `f̂_t(w) = f_t(w + W_t)`
(Kemppainen's `f̃_t`). Kemppainen's uncentred map is `fwdMapInvUnc W t z = f̂_t(z − W_t)`.
`kd_time_step` states (6.14)–(6.15) for `f̂` at the pair of points `w` (time `t`) and
`w − (W_{t+s} − W_t)` (time `t+s`), which both correspond to the same uncentred point
`z = w + W_t`; `kd_time_step_unc` restates it literally for `fwdMapInvUnc`.

## Proof (own route; recorded in DEVIATIONS L-RS-P)

Kemppainen differentiates the Loewner PDE `∂_t f_t = −f_t' · 2/(z − W_t)` in time and uses
`|f''| ≤ C|f'|/y`. The project has no PDE for the inverse maps, so we use the flow property
P3(a) instead: `f̂_{t+s} = f̂_t ∘ φ` with `φ = fwdMapInv (shiftDrive W t) s`, which is a reverse
flow of duration `s ≤ y²` (`fwdMapInv_eq_revMap_timeRev`). Its integral equation gives
`|φ(w − (W_{t+s} − W_t)) − w| ≤ 2s/y ≤ 2y`, `Im φ(·) ≥ y`, and `|log|φ'|| ≤ 2s/y² ≤ 2`
(`deriv_revMap`). A chain of four Whitney steps (Koebe distortion, K4/K5b:
`Koebe.deriv_ratio_le`, `Koebe.norm_sub_le_growth_global`) along the segment from `w` to
`φ(w')` finishes the proof. The constants are non-sharp: `C = K⁵e²`, `K = 2^C₂`.
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology Real

namespace QuantumZipper.RS

open QuantumZipper.CA QuantumZipper.CA.Koebe UnzipInvariance

/-! ## A Whitney chain along a segment -/

/-- Koebe growth on a Whitney disk with the step length: if `dist w c ≤ Im c / 2` then
`‖f w − f c‖ ≤ dist w c · K ‖f'(c)‖`. -/
theorem norm_sub_le_dist_mul_step {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {c w : ℂ} (hc : 0 < c.im) (hw : dist w c ≤ c.im / 2) :
    ‖f w - f c‖ ≤ dist w c * (koebeStepConst * ‖deriv f c‖) := by
  have hsub := ball_im_subset_upperHalfPlane (z := c)
  have hwB : w ∈ ball c c.im := mem_ball.2 (by linarith)
  have h := norm_sub_le_growth_global (hd.mono hsub) (hinj.mono hsub) hwB
  refine h.trans ?_
  have hs : 1 / 2 ≤ 1 - dist w c / c.im := by
    have : dist w c / c.im ≤ 1 / 2 := by rw [div_le_iff₀ hc]; linarith
    linarith
  have hC := koebeDistExp_pos
  have hq : (1 - dist w c / c.im) ^ (-koebeDistExp) ≤ koebeStepConst := by
    calc (1 - dist w c / c.im) ^ (-koebeDistExp) ≤ (1 / 2 : ℝ) ^ (-koebeDistExp) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hs (by linarith)
      _ = koebeStepConst := by
          rw [koebeStepConst, Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num),
            inv_inv]
  refine mul_le_mul_of_nonneg_left ?_ dist_nonneg
  exact (mul_le_mul_of_nonneg_left hq (norm_nonneg (deriv f c))).trans_eq (mul_comm _ _)

/-- **Four Whitney steps along a segment.** If `Im a, Im b ≥ y > 0` and `‖b − a‖ ≤ 2y`, then
`‖f'(b)‖ ≤ K⁴‖f'(a)‖`, `‖f'(a)‖ ≤ K⁴‖f'(b)‖` and `‖f b − f a‖ ≤ 2y K⁵ ‖f'(a)‖`. -/
theorem koebe_segment_chain {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {a b : ℂ} {y : ℝ} (hy : 0 < y) (ha : y ≤ a.im)
    (hb : y ≤ b.im) (hab : ‖b - a‖ ≤ 2 * y) :
    ‖deriv f b‖ ≤ koebeStepConst ^ 4 * ‖deriv f a‖ ∧
    ‖deriv f a‖ ≤ koebeStepConst ^ 4 * ‖deriv f b‖ ∧
    ‖f b - f a‖ ≤ 2 * y * koebeStepConst ^ 5 * ‖deriv f a‖ := by
  set K := koebeStepConst with hK
  have hK1 : 1 ≤ K := one_le_koebeStepConst
  set p : ℕ → ℂ := fun j => a + ((j : ℂ) / 4) * (b - a) with hp
  have him : ∀ j : ℕ, j ≤ 4 → y ≤ (p j).im := by
    intro j hj
    have hj' : (j : ℝ) ≤ 4 := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have e : (p j).im = (1 - (j : ℝ) / 4) * a.im + ((j : ℝ) / 4) * b.im := by
      simp only [hp, add_im, mul_im, sub_re, sub_im, div_re, div_im, natCast_re, natCast_im]
      norm_num
      ring
    rw [e]
    nlinarith
  have hstep : ∀ j : ℕ, dist (p (j + 1)) (p j) ≤ y / 2 := by
    intro j
    rw [dist_eq_norm]
    have e : p (j + 1) - p j = (b - a) / 4 := by
      simp only [hp]; push_cast; ring
    rw [e, norm_div]
    have : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [this]
    linarith
  have hDa := norm_nonneg (deriv f a)
  have key : ∀ j : ℕ, j ≤ 4 → ‖deriv f (p j)‖ ≤ K ^ j * ‖deriv f a‖ ∧
      ‖deriv f a‖ ≤ K ^ j * ‖deriv f (p j)‖ ∧
      ‖f (p j) - f a‖ ≤ j * (y / 2) * K ^ (j + 1) * ‖deriv f a‖ := by
    intro j
    induction j with
    | zero =>
      intro _
      have : p 0 = a := by simp [hp]
      simp [this]
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have hcy := him j (by omega)
      have hc : 0 < (p j).im := lt_of_lt_of_le hy hcy
      have hd' : dist (p (j + 1)) (p j) ≤ (p j).im / 2 := (hstep j).trans (by linarith)
      obtain ⟨r1, r2⟩ := deriv_ratio_le hd hinj hc hd'
      rw [← koebeStepConst, ← hK] at r1 r2
      have hg := norm_sub_le_dist_mul_step hd hinj hc hd'
      rw [← hK] at hg
      have hK0 : 0 ≤ K := by linarith
      have hKj : 0 ≤ K ^ j := pow_nonneg hK0 j
      refine ⟨?_, ?_, ?_⟩
      · calc ‖deriv f (p (j + 1))‖ ≤ K * ‖deriv f (p j)‖ := r1
          _ ≤ K * (K ^ j * ‖deriv f a‖) := mul_le_mul_of_nonneg_left h1 hK0
          _ = K ^ (j + 1) * ‖deriv f a‖ := by ring
      · calc ‖deriv f a‖ ≤ K ^ j * ‖deriv f (p j)‖ := h2
          _ ≤ K ^ j * (K * ‖deriv f (p (j + 1))‖) := mul_le_mul_of_nonneg_left r2 hKj
          _ = K ^ (j + 1) * ‖deriv f (p (j + 1))‖ := by ring
      · have hA : ‖f (p (j + 1)) - f (p j)‖ ≤ (y / 2) * K ^ (j + 1) * ‖deriv f a‖ := by
          calc ‖f (p (j + 1)) - f (p j)‖ ≤ dist (p (j + 1)) (p j) * (K * ‖deriv f (p j)‖) := hg
            _ ≤ (y / 2) * (K * (K ^ j * ‖deriv f a‖)) := by
                gcongr
                exact hstep j
            _ = (y / 2) * K ^ (j + 1) * ‖deriv f a‖ := by ring
        have hmono : K ^ (j + 1) ≤ K ^ (j + 1 + 1) := pow_le_pow_right₀ hK1 (by omega)
        have hy2 : 0 ≤ y / 2 := by linarith
        calc ‖f (p (j + 1)) - f a‖
            ≤ ‖f (p (j + 1)) - f (p j)‖ + ‖f (p j) - f a‖ := by
              have := norm_add_le (f (p (j + 1)) - f (p j)) (f (p j) - f a)
              rwa [sub_add_sub_cancel] at this
          _ ≤ (y / 2) * K ^ (j + 1) * ‖deriv f a‖ + j * (y / 2) * K ^ (j + 1) * ‖deriv f a‖ :=
              add_le_add hA h3
          _ = ((j : ℝ) + 1) * (y / 2) * K ^ (j + 1) * ‖deriv f a‖ := by ring
          _ ≤ ((j : ℝ) + 1) * (y / 2) * K ^ (j + 1 + 1) * ‖deriv f a‖ := by gcongr
          _ = ((j + 1 : ℕ) : ℝ) * (y / 2) * K ^ (j + 1 + 1) * ‖deriv f a‖ := by push_cast; ring
  have hp4 : p 4 = b := by simp only [hp]; push_cast; ring
  obtain ⟨k1, k2, k3⟩ := key 4 le_rfl
  rw [hp4] at k1 k2 k3
  refine ⟨k1, k2, ?_⟩
  calc ‖f b - f a‖ ≤ ((4 : ℕ) : ℝ) * (y / 2) * K ^ (4 + 1) * ‖deriv f a‖ := k3
    _ = 2 * y * K ^ 5 * ‖deriv f a‖ := by push_cast; ring

/-! ## The reverse flow over a short time -/

/-- The exact small-step displacement: `‖revMap V δ w − w + V δ‖ ≤ 2δ/Im w`. -/
theorem norm_revMap_sub_self_add_le {V : ℝ → ℝ} (hV : Continuous V) {δ : ℝ} (hδ : 0 ≤ δ)
    {w : ℂ} (hw : w ∈ H) : ‖revMap V δ w - w + V δ‖ ≤ 2 * δ / w.im := by
  have hw0 : 0 < w.im := hw
  obtain ⟨u, hu⟩ := exists_isReverseSol V hV w hw0 δ hδ
  rw [revMap_eq V hV w hδ le_rfl hu, (hu.2 δ ⟨hδ, le_rfl⟩).2]
  have hI : ‖∫ s in (0 : ℝ)..δ, 2 / u s‖ ≤ 2 / w.im * |δ - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    rw [uIoc_of_le hδ] at hr
    have hr' : r ∈ Icc (0 : ℝ) δ := ⟨hr.1.le, hr.2⟩
    have hge : w.im ≤ (u r).im := ReverseFlow.isReverseSol_im_ge hu hr'
    have hnorm : w.im ≤ ‖u r‖ := hge.trans (Complex.im_le_norm _)
    rw [norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_left (by norm_num) hw0 hnorm
  rw [sub_zero, abs_of_nonneg hδ] at hI
  have e : (w - ↑(V δ) - ∫ s in (0 : ℝ)..δ, 2 / u s) - w + ↑(V δ) =
      -∫ s in (0 : ℝ)..δ, 2 / u s := by ring
  rw [e, norm_neg]
  calc _ ≤ 2 / w.im * δ := hI
    _ = 2 * δ / w.im := by ring

/-- The derivative of a short reverse flow: `‖(revMap V δ)'(w)‖ = e^{ρ}` with
`|ρ| ≤ 2δ/Im w²`. -/
theorem norm_deriv_revMap_bounds {V : ℝ → ℝ} (hV : Continuous V) {δ : ℝ} (hδ : 0 ≤ δ)
    {w : ℂ} (hw : w ∈ H) :
    Real.exp (-(2 * δ / w.im ^ 2)) ≤ ‖deriv (revMap V δ) w‖ ∧
    ‖deriv (revMap V δ) w‖ ≤ Real.exp (2 * δ / w.im ^ 2) := by
  have hw0 : 0 < w.im := hw
  rw [deriv_revMap V hV hδ hw, Complex.norm_exp]
  have hI : ‖∫ s in (0 : ℝ)..δ, 2 / (revMap V s w) ^ 2‖ ≤ 2 / w.im ^ 2 * |δ - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    rw [uIoc_of_le hδ] at hr
    have hge : w.im ≤ (revMap V r w).im := im_le_im_revMap V hV w hw0 hr.1.le
    have hnorm : w.im ≤ ‖revMap V r w‖ := hge.trans (Complex.im_le_norm _)
    rw [norm_div, Complex.norm_two, norm_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hw0.le hnorm 2)
  rw [sub_zero, abs_of_nonneg hδ] at hI
  have hre := Complex.abs_re_le_norm (∫ s in (0 : ℝ)..δ, 2 / (revMap V s w) ^ 2)
  have hb : |(∫ s in (0 : ℝ)..δ, 2 / (revMap V s w) ^ 2).re| ≤ 2 * δ / w.im ^ 2 := by
    have : 2 / w.im ^ 2 * δ = 2 * δ / w.im ^ 2 := by ring
    linarith
  exact ⟨Real.exp_le_exp.2 (neg_le_of_abs_le hb), Real.exp_le_exp.2 (le_of_abs_le hb)⟩

/-! ## KD(b) -/

variable {W : ℝ → ℝ}

theorem differentiableOn_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableOn ℂ (fwdMapInv W t) {z : ℂ | 0 < z.im} := fun _ hz =>
  (differentiableAt_fwdMapInv hW hW0 ht hz).differentiableWithinAt

theorem injOn_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    InjOn (fwdMapInv W t) {z : ℂ | 0 < z.im} := by
  intro z₁ h₁ z₂ h₂ h
  rw [← fwdMap_fwdMapInv hW hW0 ht (w := z₁) h₁, ← fwdMap_fwdMapInv hW hW0 ht (w := z₂) h₂, h]

/-- **KD(b) (Kemppainen Lemma 6.7, (6.14)–(6.15)), centred form.** There is `C ≥ 1` such that
for every continuous driver `W` with `W 0 = 0`, `t ≥ 0`, `w ∈ ℍ` and `s ∈ [0, (Im w)²]`, with
`w' = w − (W_{t+s} − W_t)` (the same uncentred point `w + W_t` seen from time `t+s`):
`‖f̂_{t+s}'(w')‖ ≤ C‖f̂_t'(w)‖`, `‖f̂_t'(w)‖ ≤ C‖f̂_{t+s}'(w')‖` and
`‖f̂_{t+s}(w') − f̂_t(w)‖ ≤ C · Im w · ‖f̂_t'(w)‖`. -/
theorem kd_time_step : ∃ C : ℝ, 1 ≤ C ∧ ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
    ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ∀ w : ℂ, 0 < w.im → s ≤ w.im ^ 2 →
      ‖deriv (fwdMapInv W (t + s)) (w - ((W (t + s) - W t : ℝ) : ℂ))‖ ≤
          C * ‖deriv (fwdMapInv W t) w‖ ∧
      ‖deriv (fwdMapInv W t) w‖ ≤
          C * ‖deriv (fwdMapInv W (t + s)) (w - ((W (t + s) - W t : ℝ) : ℂ))‖ ∧
      ‖fwdMapInv W (t + s) (w - ((W (t + s) - W t : ℝ) : ℂ)) - fwdMapInv W t w‖ ≤
          C * w.im * ‖deriv (fwdMapInv W t) w‖ := by
  set K := koebeStepConst with hK
  have hK1 : 1 ≤ K := one_le_koebeStepConst
  have hE1 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hE2 : 2 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hK5 : 1 ≤ K ^ 5 := one_le_pow₀ hK1
  refine ⟨K ^ 5 * Real.exp 2, by nlinarith, fun W hW hW0 t s ht hs w hw hsw => ?_⟩
  set y := w.im with hy
  set w' : ℂ := w - ((W (t + s) - W t : ℝ) : ℂ) with hw'
  have hw'H : w' ∈ H := by
    show 0 < w'.im
    simpa [hw'] using hw
  have hw'im : w'.im = y := by simp [hw', hy]
  set Ws := shiftDrive W t with hWs
  have hWsc : Continuous Ws := continuous_shiftDrive hW t
  have hWs0 : Ws 0 = 0 := shiftDrive_zero W t
  set V : ℝ → ℝ := fun r => Ws (s - r) - Ws s with hV
  have hVc : Continuous V := by rw [hV]; fun_prop
  set φ := fwdMapInv Ws s with hφ
  -- `φ` is the short reverse flow near `w'`
  have hφeq : φ =ᶠ[𝓝 w'] revMap V s :=
    eventually_of_mem (isOpen_H.mem_nhds hw'H) fun z hz =>
      fwdMapInv_eq_revMap_timeRev Ws hWsc hWs0 hs hz
  have hφw' : φ w' = revMap V s w' := hφeq.eq_of_nhds
  have hVs : V s = -(W (t + s) - W t) := by simp [hV, hWs, shiftDrive]
  have hdisp : ‖φ w' - w‖ ≤ 2 * s / y := by
    have h := norm_revMap_sub_self_add_le hVc hs hw'H
    rw [hVs, hw'im, ← hφw'] at h
    have e : φ w' - w' + ((-(W (t + s) - W t) : ℝ) : ℂ) = φ w' - w := by
      rw [hw']; push_cast; ring
    rwa [e] at h
  have hφim : y ≤ (φ w').im := by
    rw [hφw', ← hw'im]; exact im_le_im_revMap V hVc w' hw'H hs
  have hdφ : deriv φ w' = deriv (revMap V s) w' := hφeq.deriv_eq
  obtain ⟨hφlo, hφhi⟩ := norm_deriv_revMap_bounds hVc hs hw'H
  rw [← hdφ, hw'im] at hφlo hφhi
  have hq : 2 * s / y ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hφlo' : Real.exp (-2) ≤ ‖deriv φ w'‖ :=
    (Real.exp_le_exp.2 (by linarith)).trans hφlo
  have hφhi' : ‖deriv φ w'‖ ≤ Real.exp 2 := hφhi.trans (Real.exp_le_exp.2 hq)
  -- the flow property and the chain rule
  have hflow : fwdMapInv W (t + s) =ᶠ[𝓝 w'] fun z => fwdMapInv W t (φ z) :=
    eventually_of_mem (isOpen_H.mem_nhds hw'H) fun z hz =>
      fwdMapInv_add_shift hW hW0 ht hs hz
  have hφH : φ w' ∈ H := fwdMapInv_mem_H hWsc hWs0 hs hw'H
  have hderiv : deriv (fwdMapInv W (t + s)) w' = deriv (fwdMapInv W t) (φ w') * deriv φ w' := by
    rw [hflow.deriv_eq]
    exact deriv_comp (h₂ := fwdMapInv W t) (h := φ) w'
      (differentiableAt_fwdMapInv hW hW0 ht hφH) (differentiableAt_fwdMapInv hWsc hWs0 hs hw'H)
  have hval : fwdMapInv W (t + s) w' = fwdMapInv W t (φ w') := hflow.eq_of_nhds
  -- Koebe along the segment from `w` to `φ w'`
  have hy0 : 0 < y := hw
  have hseg : ‖φ w' - w‖ ≤ 2 * y := by
    refine hdisp.trans ?_
    rw [div_le_iff₀ hy0]; nlinarith
  obtain ⟨c1, c2, c3⟩ := koebe_segment_chain (differentiableOn_fwdMapInv hW hW0 ht)
    (injOn_fwdMapInv hW hW0 ht) hy0 le_rfl hφim hseg
  rw [← hK] at c1 c2 c3
  set A := ‖deriv (fwdMapInv W t) w‖ with hA
  set Bb := ‖deriv (fwdMapInv W t) (φ w')‖ with hBb
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ Bb := norm_nonneg _
  have hK0 : 0 ≤ K := by linarith
  have hK4 : K ^ 4 ≤ K ^ 5 := pow_le_pow_right₀ hK1 (by norm_num)
  have hEm : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hderiv, norm_mul]
    calc Bb * ‖deriv φ w'‖ ≤ (K ^ 4 * A) * Real.exp 2 :=
          mul_le_mul c1 hφhi' (norm_nonneg _) (by positivity)
      _ ≤ (K ^ 5 * A) * Real.exp 2 := by gcongr
      _ = K ^ 5 * Real.exp 2 * A := by ring
  · rw [hderiv, norm_mul]
    have hBle : Bb ≤ Real.exp 2 * (Bb * ‖deriv φ w'‖) := by
      calc Bb = Real.exp 2 * (Bb * Real.exp (-2)) := by
            rw [mul_comm Bb, ← mul_assoc, mul_comm (Real.exp 2), hEm, one_mul]
        _ ≤ Real.exp 2 * (Bb * ‖deriv φ w'‖) := by gcongr
    calc A ≤ K ^ 4 * Bb := c2
      _ ≤ K ^ 5 * (Real.exp 2 * (Bb * ‖deriv φ w'‖)) :=
          mul_le_mul hK4 hBle hB0 (by positivity)
      _ = K ^ 5 * Real.exp 2 * (Bb * ‖deriv φ w'‖) := by ring
  · rw [hval]
    calc ‖fwdMapInv W t (φ w') - fwdMapInv W t w‖ ≤ 2 * y * K ^ 5 * A := c3
      _ ≤ Real.exp 2 * y * K ^ 5 * A := by gcongr
      _ = K ^ 5 * Real.exp 2 * y * A := by ring

/-- Kemppainen's uncentred inverse Loewner map `f_t(z) = f̂_t(z − W_t)` (`= g_t⁻¹(z)`). -/
def fwdMapInvUnc (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ := fwdMapInv W t (z - W t)

end QuantumZipper.RS
