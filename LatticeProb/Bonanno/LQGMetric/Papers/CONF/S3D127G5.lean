/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127G5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127G2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 (L2), part 5: power-law decay of the survival probability near `Uᶜ`
(packet P-127G, task P2-HEATG)

`killedSurv_le_rpow_of_step`: suppose that from every point within `ρ ≤ L` of `Uᶜ` Brownian
motion is killed before time `ρ²` with probability `≥ γ > 0` (the corkscrew step, P2-HEATC's
`killedSurv_le_of_ball`). Then for `H ≥ 2L²` there are `C ≥ 0`, `β ∈ (0, 1]` with
```
P^y(τ_U > H) ≤ C ρ^β      whenever B(y, ρ) ⊄ U.
```
This is the classical Hölder decay of the survival probability at a boundary satisfying an
exterior cone/corkscrew condition (e.g. Bass, *Probabilistic techniques in analysis*, Ch. II;
Port–Stone, *Brownian motion and classical potential theory*, Ch. 2). The textbook proof
iterates the strong Markov property at the exit times of the balls `B(p, Λʲρ)`; we only have the
Markov property at fixed times (`killedSurv_add`), so we use a self-improving multi-scale bound
instead (own argument, DV-P127G-2): with `h = ρ²`,
```
P^y(τ > s) ≤ ∫ p_U(h; y, w) P^w(τ > s − h) dw
          ≤ (1 − γ) C((Λ+1)ρ)^β + ∫_{|w−y| > Λρ} p_h(y, w) C(2|w − y|)^β dw
          ≤ C ρ^β ((1 − γ)(Λ + 1)^β + 16/Λ) ≤ C ρ^β
```
for `Λ = 64/γ` and `β` small, by downward induction over the scales `ρ ∈ (L(Λ+1)^{-(n+1)}, L]`
(the far part uses the Gaussian tail `p_h ≤ 2e^{-|w−y|²/(4h)} p_{2h}`; the times `s ≥ H − ρ²`
absorb the time spent).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat

lemma exp_neg_le_inv_G5 {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ y⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hy (by linarith [Real.add_one_le_exp y])

/-- The far-field pointwise bound `p_h(y,w) (2d)^β ≤ (16 ρ^β/Λ) p_{2h}(y,w)` for
`d = |w − y| > Λρ`, `h = ρ²`, `Λ ≥ 1`, `β ∈ (0, 1]`. -/
lemma heat_far_le {ρ Λ β : ℝ} (hρ : 0 < ρ) (hΛ : 1 ≤ Λ) (hβ : 0 < β) (hβ1 : β ≤ 1) {y w : ℂ}
    (hd : Λ * ρ < dist w y) :
    heatKernel (ρ ^ 2) y w * (2 * dist w y) ^ β ≤
      16 * ρ ^ β / Λ * heatKernel (2 * ρ ^ 2) y w := by
  set d := dist w y with hdd
  have hd0 : 0 < d := lt_of_le_of_lt (by positivity) hd
  have hdr : 1 ≤ d / ρ := by rw [le_div_iff₀ hρ]; nlinarith
  have hyw : d ≤ ‖y - w‖ := by rw [hdd, dist_comm, dist_eq_norm]
  have htail := heatKernel_le_tail_G (by positivity : (0 : ℝ) < ρ ^ 2) hd0.le hyw
  have hexp := exp_neg_le_inv_G5 (y := d ^ 2 / (4 * ρ ^ 2)) (by positivity)
  rw [neg_div] at htail
  have hp2 : 0 ≤ heatKernel (2 * ρ ^ 2) y w := heatKernel_nonneg _ (by positivity) _ _
  have hpow : (2 * d) ^ β ≤ 2 * ρ ^ β * (d / ρ) := by
    have e : 2 * d = 2 * (ρ * (d / ρ)) := by field_simp
    rw [e, Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hρ.le (by positivity)]
    have h2 : (2 : ℝ) ^ β ≤ 2 := by
      calc (2 : ℝ) ^ β ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
        _ = 2 := Real.rpow_one 2
    have h3 : (d / ρ) ^ β ≤ d / ρ := by
      calc (d / ρ) ^ β ≤ (d / ρ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hdr hβ1
        _ = d / ρ := Real.rpow_one _
    have h4 : 0 ≤ ρ ^ β := by positivity
    calc 2 ^ β * (ρ ^ β * (d / ρ) ^ β) ≤ 2 * (ρ ^ β * (d / ρ)) := by gcongr
      _ = 2 * ρ ^ β * (d / ρ) := by ring
  have hpow0 : 0 ≤ (2 * d) ^ β := by positivity
  calc heatKernel (ρ ^ 2) y w * (2 * d) ^ β
      ≤ (2 * Real.exp (-(d ^ 2 / (4 * ρ ^ 2))) * heatKernel (2 * ρ ^ 2) y w) * (2 * d) ^ β :=
        mul_le_mul_of_nonneg_right htail hpow0
    _ ≤ (2 * (d ^ 2 / (4 * ρ ^ 2))⁻¹ * heatKernel (2 * ρ ^ 2) y w) * (2 * ρ ^ β * (d / ρ)) := by
        gcongr
    _ = 16 * ρ ^ β * (ρ / d) * heatKernel (2 * ρ ^ 2) y w := by
        field_simp
        ring
    _ ≤ 16 * ρ ^ β / Λ * heatKernel (2 * ρ ^ 2) y w := by
        gcongr
        have hrd : ρ / d ≤ 1 / Λ := by rw [div_le_div_iff₀ hd0 (by linarith)]; nlinarith
        calc 16 * ρ ^ β * (ρ / d) ≤ 16 * ρ ^ β * (1 / Λ) := by gcongr
          _ = 16 * ρ ^ β / Λ := by ring

/-- **One multi-scale step.** -/
theorem killedSurv_step {U : Set ℂ} (hU : IsOpen U) {γ ρ Λ β A B : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ : 0 < ρ) (hΛ : 1 ≤ Λ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) {y : ℂ}
    (hcork : killedSurv U (ρ.toNNReal ^ 2) y ≤ 1 - ENNReal.ofReal γ) {s : ℝ≥0}
    (hs : ρ ^ 2 < s)
    (hnear : ∀ w, dist w y ≤ Λ * ρ → killedSurv U (s - ρ.toNNReal ^ 2) w ≤ ENNReal.ofReal A)
    (hfar : ∀ w, Λ * ρ < dist w y →
      killedSurv U (s - ρ.toNNReal ^ 2) w ≤ ENNReal.ofReal (B * (2 * dist w y) ^ β)) :
    killedSurv U s y ≤ ENNReal.ofReal (A * (1 - γ) + 16 * B * ρ ^ β / Λ) := by
  set h : ℝ≥0 := ρ.toNNReal ^ 2 with hh
  have hhc : (h : ℝ) = ρ ^ 2 := by rw [hh]; push_cast; rw [Real.coe_toNNReal _ hρ.le]
  have hh0 : h ≠ 0 := by
    intro h0; have := hhc; rw [h0] at this; simp at this; linarith [pow_pos hρ 2]
  have hhs : h ≤ s := by rw [← NNReal.coe_le_coe, hhc]; exact hs.le
  have hs' : s - h ≠ 0 := by
    intro h0
    have : (s : ℝ) ≤ h := by exact_mod_cast tsub_eq_zero_iff_le.mp h0
    rw [hhc] at this; linarith
  have hsplit : s = h + (s - h) := (add_tsub_cancel_of_le hhs).symm
  rw [hsplit, killedSurv_add hU hh0 hs' y]
  set c : ℝ := 16 * B * ρ ^ β / Λ with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ w, ENNReal.ofReal (killedHeat U h y w) * killedSurv U (s - h) w ≤
      ENNReal.ofReal (killedHeat U h y w) * ENNReal.ofReal A +
        ENNReal.ofReal c * ENNReal.ofReal (heatKernel (2 * ρ ^ 2) y w) := by
    intro w
    by_cases hw : dist w y ≤ Λ * ρ
    · exact le_add_right (mul_le_mul' le_rfl (hnear w hw))
    · push_neg at hw
      refine le_add_left ?_
      calc ENNReal.ofReal (killedHeat U h y w) * killedSurv U (s - h) w
          ≤ ENNReal.ofReal (heatKernel (ρ ^ 2) y w) * ENNReal.ofReal (B * (2 * dist w y) ^ β) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (by
              rw [← hhc]; exact killedHeat_le_heatKernel _ _ _ _)) (hfar w hw)
        _ = ENNReal.ofReal (B * (heatKernel (ρ ^ 2) y w * (2 * dist w y) ^ β)) := by
            rw [← ENNReal.ofReal_mul (heatKernel_nonneg _ (by positivity) _ _)]; ring_nf
        _ ≤ ENNReal.ofReal (B * (16 * ρ ^ β / Λ * heatKernel (2 * ρ ^ 2) y w)) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
              (heat_far_le hρ hΛ hβ hβ1 hw) hB)
        _ = ENNReal.ofReal c * ENNReal.ofReal (heatKernel (2 * ρ ^ 2) y w) := by
            rw [← ENNReal.ofReal_mul hc0, hc]; ring_nf
  have hm1 : Measurable fun w => ENNReal.ofReal (killedHeat U h y w) * ENNReal.ofReal A :=
    (measurable_killedHeat_right hU hh0 y).ennreal_ofReal.mul_const _
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left hm1, lintegral_mul_const _ (measurable_killedHeat_right hU hh0 y).ennreal_ofReal,
    lintegral_const_mul _ (measurable_heatKernel_right _ y).ennreal_ofReal,
    lintegral_ofReal_heatKernel_eq_one (by positivity) y, mul_one]
  have h1 : (∫⁻ w, ENNReal.ofReal (killedHeat U h y w)) * ENNReal.ofReal A ≤
      ENNReal.ofReal (A * (1 - γ)) := by
    calc (∫⁻ w, ENNReal.ofReal (killedHeat U h y w)) * ENNReal.ofReal A
        ≤ (1 - ENNReal.ofReal γ) * ENNReal.ofReal A := mul_le_mul' hcork le_rfl
      _ = ENNReal.ofReal (A * (1 - γ)) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hγ0,
            ← ENNReal.ofReal_mul (by linarith), mul_comm]
  calc (∫⁻ w, ENNReal.ofReal (killedHeat U h y w)) * ENNReal.ofReal A + ENNReal.ofReal c
      ≤ ENNReal.ofReal (A * (1 - γ)) + ENNReal.ofReal c := add_le_add h1 le_rfl
    _ = ENNReal.ofReal (A * (1 - γ) + c) := by
        rw [ENNReal.ofReal_add (mul_nonneg hA (by linarith)) hc0]

/-- **Power-law decay of the survival probability** from the corkscrew step (multi-scale
induction, see the module docstring). -/
theorem killedSurv_le_rpow_of_step {U : Set ℂ} (hU : IsOpen U) {L γ : ℝ} (hL : 0 < L)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hstep : ∀ ρ : ℝ, 0 < ρ → ρ ≤ L → ∀ y, ¬ ball y ρ ⊆ U →
      killedSurv U (ρ.toNNReal ^ 2) y ≤ 1 - ENNReal.ofReal γ)
    {H : ℝ≥0} (hH : 2 * L ^ 2 ≤ H) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ β ≤ 1 ∧ ∀ y : ℂ, ∀ ρ : ℝ, 0 < ρ → ¬ ball y ρ ⊆ U →
      killedSurv U H y ≤ ENNReal.ofReal (C * ρ ^ β) := by
  set Λ : ℝ := 64 / γ with hΛdef
  have hΛ : 1 ≤ Λ := by rw [hΛdef, le_div_iff₀ hγ0]; linarith
  have hΛ0 : 0 < Λ := by linarith
  set ratio : ℝ := (1 - γ / 4) / (1 - γ) with hratio
  have hratio1 : 1 < ratio := by rw [hratio, lt_div_iff₀ (by linarith)]; linarith
  have hl : 0 < Real.log (Λ + 1) := Real.log_pos (by linarith)
  set β : ℝ := min 1 (Real.log ratio / Real.log (Λ + 1)) with hβdef
  have hβ0 : 0 < β := lt_min one_pos (div_pos (Real.log_pos hratio1) hl)
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hkey : (1 - γ) * (Λ + 1) ^ β + 16 / Λ ≤ 1 := by
    have h1 : (Λ + 1) ^ β ≤ ratio := by
      calc (Λ + 1) ^ β ≤ (Λ + 1) ^ (Real.log ratio / Real.log (Λ + 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (min_le_right _ _)
        _ = ratio := by
            rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hl.ne',
              Real.exp_log (by linarith)]
    have h2 : 16 / Λ = γ / 4 := by rw [hΛdef]; field_simp; ring
    have hne : (1 : ℝ) - γ ≠ 0 := (by linarith : (0 : ℝ) < 1 - γ).ne'
    have h3 : (1 - γ) * ratio = 1 - γ / 4 := by rw [hratio]; field_simp
    nlinarith
  set C : ℝ := ((Λ + 1) / L) ^ β with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hC1 : ∀ r : ℝ, L / (Λ + 1) < r → 1 ≤ C * r ^ β := by
    intro r hr
    have hr0 : 0 < r := lt_trans (by positivity) hr
    rw [hCdef, ← Real.mul_rpow (by positivity) hr0.le]
    refine Real.one_le_rpow ?_ hβ0.le
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    rw [div_lt_iff₀ (by linarith)] at hr
    linarith
  have htriv : ∀ r : ℝ, L / (Λ + 1) < r → ∀ (s : ℝ≥0), s ≠ 0 → ∀ w,
      killedSurv U s w ≤ ENNReal.ofReal (C * r ^ β) := fun r hr s hs w =>
    (killedSurv_le_one U hs w).trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hC1 r hr))
  set q : ℝ := (Λ + 1)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hLq : ∀ n : ℕ, L * q ^ (n + 1) ≤ L / (Λ + 1) := fun n => by
    rw [div_eq_mul_inv, ← hq]
    exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hq0.le hq1.le (by omega)) hL.le
  have hmemball : ∀ {y w : ℂ} {ρ r : ℝ}, ¬ ball y ρ ⊆ U → dist w y + ρ ≤ r → ¬ ball w r ⊆ U := by
    intro y w ρ r hy hr hsub
    obtain ⟨p, hp, hpU⟩ := not_subset.mp hy
    apply hpU
    apply hsub
    rw [mem_ball] at hp ⊢
    calc dist p w ≤ dist p y + dist y w := dist_triangle _ _ _
      _ < ρ + dist w y := by rw [dist_comm y w]; linarith
      _ ≤ r := by linarith
  have hspos : ∀ (s : ℝ≥0) (r : ℝ), 0 < r → r ≤ L → (H : ℝ) - r ^ 2 ≤ s → s ≠ 0 := by
    intro s r hr0 hr hs h0
    rw [h0, NNReal.coe_zero] at hs
    have : r ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hr0.le hr 2
    have := pow_pos hL 2
    linarith
  -- the multi-scale induction
  have hP : ∀ n : ℕ, ∀ r : ℝ, L * q ^ (n + 1) < r → r ≤ L → ∀ y, ¬ ball y r ⊆ U →
      ∀ s : ℝ≥0, (H : ℝ) - r ^ 2 ≤ s → killedSurv U s y ≤ ENNReal.ofReal (C * r ^ β) := by
    intro n
    induction n with
    | zero =>
      intro r hr hrL y _ s hs
      have e : L * q ^ (0 + 1) = L / (Λ + 1) := by rw [hq]; ring
      exact htriv r (lt_of_le_of_lt e.ge hr) s
        (hspos s r (lt_of_le_of_lt (by positivity) hr) hrL hs) y
    | succ n ih =>
      intro ρ hr hrL y hy s hs
      by_cases hbig : L * q ^ (n + 1) < ρ
      · exact ih ρ hbig hrL y hy s hs
      push_neg at hbig
      have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hr
      have hρq : ρ ≤ L * q := hbig.trans (by
        exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hq0.le hq1.le (by omega)) hL.le)
      have hρL2 : 2 * ρ ≤ L := by
        have : q ≤ 1 / 2 := by
          rw [hq]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
        nlinarith
      have hss : ρ ^ 2 < s := by nlinarith
      set s' : ℝ≥0 := s - ρ.toNNReal ^ 2 with hs'
      have hs'c : (s' : ℝ) = s - ρ ^ 2 := by
        have hle : ρ.toNNReal ^ 2 ≤ s := by
          rw [← NNReal.coe_le_coe]; push_cast; rw [Real.coe_toNNReal _ hρ0.le]; exact hss.le
        rw [hs', NNReal.coe_sub hle]; push_cast; rw [Real.coe_toNNReal _ hρ0.le]
      have hs'pos : s' ≠ 0 := by
        intro h0; have := hs'c; rw [h0, NNReal.coe_zero] at this; nlinarith
      have hsub : ∀ r' : ℝ, 2 * ρ ≤ r' → L * q ^ (n + 1) < r' → ∀ w, ¬ ball w r' ⊆ U →
          killedSurv U s' w ≤ ENNReal.ofReal (C * r' ^ β) := by
        intro r' h2 hr' w hw
        by_cases hr'L : r' ≤ L
        · refine ih r' hr' hr'L w hw s' ?_
          rw [hs'c]; nlinarith
        · push_neg at hr'L
          exact htriv r' (lt_of_le_of_lt (by
            rw [div_eq_mul_inv]; exact mul_le_of_le_one_right hL.le (inv_le_one_of_one_le₀ (by linarith))) hr'L) s' hs'pos w
      have hr1 : L * q ^ (n + 1) < (Λ + 1) * ρ := by
        have : L * q ^ (n + 1 + 1) = q * (L * q ^ (n + 1)) := by ring
        rw [this] at hr
        have hq' : (Λ + 1) * q = 1 := by rw [hq]; field_simp
        nlinarith
      have hstep' := killedSurv_step hU hγ0.le hγ1.le hρ0 hΛ hβ0 hβ1
        (by positivity : 0 ≤ C * ((Λ + 1) * ρ) ^ β) hC0 (hstep ρ hρ0 (by linarith) y hy) hss
        (fun w hw => hsub ((Λ + 1) * ρ) (by nlinarith) hr1 w (hmemball hy (by linarith)))
        (fun w hw => by
          have hdw : ρ < dist w y := lt_of_le_of_lt (by nlinarith) hw
          refine (hsub (dist w y + ρ) (by nlinarith) (lt_of_lt_of_le hr1 (by nlinarith)) w
            (hmemball hy le_rfl)).trans (ENNReal.ofReal_le_ofReal ?_)
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith)
            hβ0.le) hC0)
      refine hstep'.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [Real.mul_rpow (by linarith) hρ0.le]
      have hρβ : 0 ≤ ρ ^ β := by positivity
      have : C * ((Λ + 1) ^ β * ρ ^ β) * (1 - γ) + 16 * C * ρ ^ β / Λ =
          C * ρ ^ β * ((1 - γ) * (Λ + 1) ^ β + 16 / Λ) := by ring
      rw [this]
      exact mul_le_of_le_one_right (by positivity) hkey
  refine ⟨C, β, hC0, hβ0, hβ1, fun y ρ hρ hy => ?_⟩
  have hH0 : H ≠ 0 := by
    intro h0; rw [h0, NNReal.coe_zero] at hH; have := pow_pos hL 2; linarith
  by_cases hρL : L < ρ
  · exact htriv ρ (lt_of_le_of_lt (by
      rw [div_eq_mul_inv]; exact mul_le_of_le_one_right hL.le (inv_le_one_of_one_le₀ (by linarith))) hρL) H hH0 y
  push_neg at hρL
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hρ hL) hq1
  have hn' : L * q ^ (n + 1) < ρ := by
    have : q ^ (n + 1) ≤ q ^ n := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    rw [lt_div_iff₀ hL] at hn
    nlinarith
  refine hP n ρ hn' hρL y hy H ?_
  have := sq_nonneg ρ
  linarith

end ZBM
end CONF
end LQGMetric
