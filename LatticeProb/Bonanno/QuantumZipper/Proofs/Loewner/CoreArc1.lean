/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CoreArc1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ArcDeterminesDriver

/-!
# CORE_ARC, part 1: a Loewner ODE toolkit

Deterministic estimates for the centred forward flow `u_t = z - A_t + ∫₀ᵗ 2/u_s ds` and the
reverse flow, used for the arc structure of Loewner chains (`blueprint/CORE_ARC_PLAN.md`):

* `exists_isForwardSol_of_im_ge` (T1): uniform local existence from `Im w ≥ c`;
* `exists_isForwardSol_beyond` (T2): a solution staying away from the driving point extends;
* `exists_small_of_mem_fwdHull`: a swallowed point comes arbitrarily close to the driver;
* `apriori`, `fwd_far`, `rev_far` (T4, T5): scale-correct far-field bounds; `fwd_far` also
  shows that hulls are small, `K_h ⊆ ball(0, 4(M + √h))`;
* `norm_revMap_sub_le` (UB): `‖revMap W h z - z‖ ≤ 12M + 8√h` on all of `ℍ`;
* `exists_im_lower_of_isCompact` (T3): a uniform lower bound for `Im f_s` on compact sets;
* `norm_fwdMap_le_of_mem_diff` (T6): local growth.
-/

noncomputable section

open Set Filter Topology

namespace QuantumZipper

namespace CoreArc

/-! ### T1: uniform local existence -/

theorem exists_isForwardSol_of_im_ge {B : ℝ → ℝ} (hB : Continuous B) {w : ℂ} {c : ℝ}
    (hc : 0 < c) (hw : c ≤ w.im) : ∃ u, IsForwardSol B w (c ^ 2 / 8) u := by
  obtain ⟨v, hv0, hvd⟩ := FwdHolo.exists_tf_sol hB (c := c / 2) (by positivity)
    (T := c ^ 2 / 8) (by positivity) w
  refine ⟨_, FwdHolo.isForwardSol_of_tf hB (by positivity) hv0 hvd fun t ht => ?_⟩
  have hbd := norm_image_sub_le_of_norm_deriv_le_segment' (f := v) (C := 2 / (c / 2)) hvd
    (fun s _ => FwdHolo.tf_norm_le (by positivity) B s (v s)) t ht
  rw [hv0] at hbd
  have him := (Complex.abs_im_le_norm (v t - w)).trans hbd
  rw [Complex.sub_im] at him
  have e : 2 / (c / 2) * (t - 0) = 4 * t / c := by field_simp; ring
  rw [e] at him
  have h4 : 4 * t / c ≤ c / 2 := by
    rw [div_le_iff₀ hc]
    nlinarith [ht.2]
  have := (abs_le.1 him).1
  linarith

/-! ### T2: extension away from the driving point -/

theorem im_two_div (u : ℂ) : (2 / u).im = -(2 * u.im / ‖u‖ ^ 2) := by
  rw [div_eq_mul_inv, Complex.sq_norm]
  simp [Complex.mul_im, Complex.inv_im]
  ring

theorem im_lower_of_norm_lower {A : ℝ → ℝ} (hA : Continuous A) {z : ℂ} (hz : 0 < z.im)
    {s m : ℝ} (hs : 0 ≤ s) (hm : 0 < m) {u : ℝ → ℂ} (hu : IsForwardSol A z s u)
    (hbd : ∀ r ∈ Icc (0 : ℝ) s, m ≤ ‖u r‖) :
    z.im * Real.exp (-(2 / m ^ 2) * s) ≤ (u s).im := by
  set k : ℝ := 2 / m ^ 2 with hk
  have hkpos : 0 ≤ k := by positivity
  have hpos := (im_isForwardSol_le hA hz hu).2
  have hderiv : ∀ r ∈ Icc (0 : ℝ) s,
      HasDerivWithinAt (fun r => (u r).im) ((2 / u r).im) (Icc 0 s) r := by
    intro r hr
    have h1 := FwdHolo.hasDerivWithinAt_shift hu hr
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt r h1
    have e : (fun r => (u r).im) = (Complex.imCLM ∘ fun r => u r + (A r : ℂ)) := by
      funext r; simp
    rw [e]
    exact h2
  set φ : ℝ → ℝ := fun r => (u r).im * Real.exp (k * r) with hφ
  have hφd : ∀ r ∈ Icc (0 : ℝ) s, HasDerivWithinAt φ
      ((2 / u r).im * Real.exp (k * r) + (u r).im * (Real.exp (k * r) * k)) (Icc 0 s) r := by
    intro r hr
    have he : HasDerivAt (fun r => Real.exp (k * r)) (Real.exp (k * r) * k) r := by
      simpa using ((hasDerivAt_id r).const_mul k).exp
    exact (hderiv r hr).mul he.hasDerivWithinAt
  have hφc : ContinuousOn φ (Icc 0 s) :=
    (Complex.continuous_im.comp_continuousOn hu.1).mul (by fun_prop)
  have hmono : MonotoneOn φ (Icc 0 s) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s) hφc
      (fun r hr => (hφd r (interior_subset hr)).mono interior_subset) fun r hr => ?_
    have hr' := interior_subset hr
    have hy := hpos r hr'
    have hn := hbd r hr'
    have hne : u r ≠ 0 := (hu.2 r hr').1
    have hnpos : 0 < ‖u r‖ := norm_pos_iff.2 hne
    have him : (2 / u r).im = -(2 * (u r).im / ‖u r‖ ^ 2) := im_two_div (u r)
    rw [him]
    have hle : (u r).im / ‖u r‖ ^ 2 ≤ (u r).im / m ^ 2 :=
      div_le_div_of_nonneg_left hy.le (by positivity) (pow_le_pow_left₀ hm.le hn 2)
    have hE := Real.exp_pos (k * r)
    have : 0 ≤ (u r).im * k - 2 * (u r).im / ‖u r‖ ^ 2 := by
      rw [hk]
      have : 2 * (u r).im / ‖u r‖ ^ 2 = 2 * ((u r).im / ‖u r‖ ^ 2) := by ring
      rw [this]
      have : (u r).im * (2 / m ^ 2) = 2 * ((u r).im / m ^ 2) := by ring
      rw [this]
      linarith
    nlinarith
  have h0 : φ 0 = z.im := by
    simp only [hφ, mul_zero, Real.exp_zero, mul_one]
    rw [FwdHolo.sol_zero hu hs]
    simp
  have hs' := hmono ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  rw [h0] at hs'
  simp only [hφ] at hs'
  have hE : Real.exp (-(k * s)) * Real.exp (k * s) = 1 := by
    rw [← Real.exp_add]; simp
  calc z.im * Real.exp (-k * s) = z.im * Real.exp (-(k * s)) := by ring_nf
    _ ≤ (u s).im * Real.exp (k * s) * Real.exp (-(k * s)) :=
        mul_le_mul_of_nonneg_right hs' (Real.exp_pos _).le
    _ = (u s).im := by rw [mul_assoc, mul_comm (Real.exp _), hE, mul_one]

theorem exists_isForwardSol_beyond {A : ℝ → ℝ} (hA : Continuous A) {z : ℂ} (hz : 0 < z.im)
    {S m : ℝ} (hS : 0 < S) (hm : 0 < m)
    (hex : ∀ s ∈ Ico (0 : ℝ) S, ∃ u, IsForwardSol A z s u)
    (hbd : ∀ s ∈ Ico (0 : ℝ) S, m ≤ ‖fwdMap A s z‖) :
    ∃ S' > S, ∃ u, IsForwardSol A z S' u := by
  set c₀ := z.im * Real.exp (-(2 / m ^ 2) * S) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hlow : ∀ s ∈ Ico (0 : ℝ) S, c₀ ≤ (fwdMap A s z).im := by
    intro s hs
    obtain ⟨u, hu⟩ := hex s hs
    have hbd' : ∀ r ∈ Icc (0 : ℝ) s, m ≤ ‖u r‖ := fun r hr => by
      rw [← fwdMap_eq hA hz hu hr]
      exact hbd r ⟨hr.1, hr.2.trans_lt hs.2⟩
    rw [fwdMap_eq hA hz hu ⟨hs.1, le_rfl⟩]
    refine le_trans ?_ (im_lower_of_norm_lower hA hz hs.1 hm hu hbd')
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hz.le
    have : 0 ≤ 2 / m ^ 2 := by positivity
    nlinarith [hs.2]
  set s₁ := max 0 (S - c₀ ^ 2 / 16) with hs₁
  have hs₁mem : s₁ ∈ Ico (0 : ℝ) S :=
    ⟨le_max_left _ _, max_lt hS (by nlinarith [sq_nonneg c₀, pow_pos hc₀pos 2])⟩
  obtain ⟨u, hu⟩ := hex s₁ hs₁mem
  have hus : c₀ ≤ (u s₁).im := by
    rw [← fwdMap_eq hA hz hu ⟨hs₁mem.1, le_rfl⟩]
    exact hlow s₁ hs₁mem
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_im_ge (B := fun r => A (s₁ + r) - A s₁)
    (by fun_prop) hc₀pos hus
  refine ⟨s₁ + c₀ ^ 2 / 8, ?_, _, isForwardSol_glue hs₁mem.1 (by positivity) hu hv⟩
  have := le_max_right 0 (S - c₀ ^ 2 / 16)
  nlinarith [pow_pos hc₀pos 2]

/-- A point swallowed by time `r` comes arbitrarily close to the driving point before it is
swallowed, and after any given earlier time. -/
theorem exists_small_of_mem_fwdHull {A : ℝ → ℝ} (hA : Continuous A) {z : ℂ} (hz : z ∈ H)
    {r : ℝ} (hr : 0 ≤ r) (hzK : z ∈ fwdHull A r) {m : ℝ} (hm : 0 < m) :
    ∃ s ∈ Ico (0 : ℝ) r, z ∉ fwdHull A s ∧ ‖fwdMap A s z‖ < m := by
  have hz' : 0 < z.im := hz
  have hle : swallowTime A z ≤ ENNReal.ofReal r := hzK.2
  have hfin : swallowTime A z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  set σ := (swallowTime A z).toReal with hσ
  have hσe : swallowTime A z = ENNReal.ofReal σ := (ENNReal.ofReal_toReal hfin).symm
  have hσpos : 0 < σ := ENNReal.toReal_pos (swallowTime_pos hA hz').ne' hfin
  have hσr : σ ≤ r := by
    rw [hσe] at hle
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 hle
  have hnot : ∀ s ∈ Ico (0 : ℝ) σ, z ∉ fwdHull A s := by
    intro s hs hK
    have h1 : swallowTime A z ≤ ENNReal.ofReal s := hK.2
    rw [hσe] at h1
    exact absurd ((ENNReal.ofReal_le_ofReal_iff hs.1).1 h1) (not_le.2 hs.2)
  by_contra hcon
  push Not at hcon
  obtain ⟨S', hS', u, hu⟩ := exists_isForwardSol_beyond hA hz' hσpos hm
    (fun s hs => exists_isForwardSol_of_not_mem_fwdHull hs.1 hz (hnot s hs))
    (fun s hs => hcon s ⟨hs.1, hs.2.trans_le hσr⟩ (hnot s hs))
  have h2 := ofReal_le_swallowTime (hσpos.trans hS').le ⟨u, hu⟩
  rw [hσe] at h2
  exact absurd ((ENNReal.ofReal_le_ofReal_iff hσpos.le).1 h2) (not_le.2 hS')

/-! ### T4, T5: scale-correct far-field bounds -/

theorem four_mul_div_le_sqrt {h N M : ℝ} (hh : 0 ≤ h) (hM : 0 ≤ M)
    (hR : 4 * (M + Real.sqrt h) < N) : 4 * h / N ≤ Real.sqrt h := by
  have hs := Real.sqrt_nonneg h
  have hsq := Real.sq_sqrt hh
  have hN : 0 < N := by nlinarith
  rw [div_le_iff₀ hN]
  nlinarith

/-- A priori bound for any solution `u` of `u = z - W ± ∫ 2/u`. -/
theorem apriori {W : ℝ → ℝ} {z : ℂ} {s h M : ℝ} {u : ℝ → ℂ} (hc : ContinuousOn u (Icc 0 s))
    (heq : ∀ r ∈ Icc (0 : ℝ) s, ‖u r - (z - W r)‖ = ‖∫ x in (0 : ℝ)..r, 2 / u x‖)
    (hsh : s ≤ h) (hM : ∀ r ∈ Icc (0 : ℝ) h, |W r| ≤ M) (hR : 4 * (M + Real.sqrt h) < ‖z‖) :
    ∀ r ∈ Icc (0 : ℝ) s, ‖z‖ / 2 < ‖u r‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s₁, hs₁, hs₁'⟩ := hcon
  have hs : 0 ≤ s := hs₁.1.trans hs₁.2
  have hh : 0 ≤ h := hs.trans hsh
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hh⟩)
  have hzpos : 0 < ‖z‖ := by nlinarith [Real.sqrt_nonneg h]
  set S : Set ℝ := Icc (0 : ℝ) s ∩ u ⁻¹' {w | ‖w‖ ≤ ‖z‖ / 2} with hSdef
  have hSc : IsClosed S :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_le continuous_norm continuous_const)
  have hSne : S.Nonempty := ⟨s₁, hs₁, hs₁'⟩
  have hSbdd : BddBelow S := ⟨0, fun r hr => hr.1.1⟩
  have hs₀ : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  set s₀ := sInf S
  have hlt : ∀ r ∈ Icc (0 : ℝ) s, r < s₀ → ‖z‖ / 2 < ‖u r‖ := fun r hr hrs => by
    by_contra h'
    push Not at h'
    exact absurd (csInf_le hSbdd ⟨hr, h'⟩) (not_le.2 hrs)
  have hint : ‖∫ r in (0 : ℝ)..s₀, 2 / u r‖ ≤ 4 / ‖z‖ * |s₀ - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [(Set.countable_singleton s₀).ae_notMem MeasureTheory.volume] with r hr hrI
    rw [Set.uIoc_of_le hs₀.1.1] at hrI
    have hrs : r < s₀ := lt_of_le_of_ne hrI.2 (Set.mem_singleton_iff.not.1 hr)
    have h1 := hlt r ⟨hrI.1.le, hrI.2.trans hs₀.1.2⟩ hrs
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    calc 2 / ‖u r‖ ≤ 2 / (‖z‖ / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) h1.le
      _ = 4 / ‖z‖ := by field_simp; ring
  have hW : ‖((W s₀ : ℝ) : ℂ)‖ ≤ M := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s₀ ⟨hs₀.1.1, hs₀.1.2.trans hsh⟩
  have hlow : ‖z‖ - M - 4 / ‖z‖ * |s₀ - 0| ≤ ‖u s₀‖ := by
    have h1 := heq s₀ hs₀.1
    have h2 := norm_sub_norm_le z (u s₀)
    have h3 : z - u s₀ = (W s₀ : ℂ) - (u s₀ - (z - (W s₀ : ℂ))) := by ring
    rw [h3] at h2
    have h4 := norm_sub_le ((W s₀ : ℂ)) (u s₀ - (z - (W s₀ : ℂ)))
    linarith
  have hkey : 4 / ‖z‖ * |s₀ - 0| ≤ Real.sqrt h := by
    rw [sub_zero, abs_of_nonneg hs₀.1.1]
    calc 4 / ‖z‖ * s₀ ≤ 4 / ‖z‖ * h := by
          gcongr; exact hs₀.1.2.trans hsh
      _ = 4 * h / ‖z‖ := by ring
      _ ≤ Real.sqrt h := four_mul_div_le_sqrt hh hM0 hR
  have h5 : ‖u s₀‖ ≤ ‖z‖ / 2 := hs₀.2
  linarith

theorem apriori_bound {W : ℝ → ℝ} {z : ℂ} {s h M : ℝ} {u : ℝ → ℂ}
    (hc : ContinuousOn u (Icc 0 s))
    (heq : ∀ r ∈ Icc (0 : ℝ) s, ‖u r - (z - W r)‖ = ‖∫ x in (0 : ℝ)..r, 2 / u x‖)
    (hsh : s ≤ h) (hM : ∀ r ∈ Icc (0 : ℝ) h, |W r| ≤ M) (hR : 4 * (M + Real.sqrt h) < ‖z‖) :
    ∀ r ∈ Icc (0 : ℝ) s, ‖u r - (z - W r)‖ ≤ 4 * r / ‖z‖ := by
  have hb := apriori hc heq hsh hM hR
  intro r hr
  have hh : 0 ≤ h := hr.1.trans (hr.2.trans hsh)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hh⟩)
  have hzpos : 0 < ‖z‖ := by nlinarith [Real.sqrt_nonneg h]
  rw [heq r hr]
  calc ‖∫ x in (0 : ℝ)..r, 2 / u x‖ ≤ 4 / ‖z‖ * |r - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [Set.uIoc_of_le hr.1] at hx
        have h1 := hb x ⟨hx.1.le, hx.2.trans hr.2⟩
        rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
        calc 2 / ‖u x‖ ≤ 2 / (‖z‖ / 2) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) h1.le
          _ = 4 / ‖z‖ := by field_simp; ring
    _ = 4 * r / ‖z‖ := by rw [sub_zero, abs_of_nonneg hr.1]; ring

/-- **T4.** Far points are not swallowed by time `h`, and the forward map moves them little. -/
theorem fwd_far {A : ℝ → ℝ} (hA : Continuous A) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ r ∈ Icc (0 : ℝ) h, |A r| ≤ M) {w : ℂ} (hw : w ∈ H)
    (hR : 4 * (M + Real.sqrt h) < ‖w‖) :
    w ∉ fwdHull A h ∧ ∀ s ∈ Icc (0 : ℝ) h, ‖fwdMap A s w - (w - A s)‖ ≤ 4 * s / ‖w‖ := by
  have hw' : 0 < w.im := hw
  have heq : ∀ {s : ℝ} {u : ℝ → ℂ}, IsForwardSol A w s u →
      ∀ r ∈ Icc (0 : ℝ) s, ‖u r - (w - A r)‖ = ‖∫ x in (0 : ℝ)..r, 2 / u x‖ := by
    intro s u hu r hr
    rw [(hu.2 r hr).2]
    congr 1
    ring
  have hnot : w ∉ fwdHull A h := by
    intro hK
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hh⟩)
    have hpos : 0 < ‖w‖ / 2 := by nlinarith [Real.sqrt_nonneg h]
    obtain ⟨s, hs, hsK, hsm⟩ := exists_small_of_mem_fwdHull hA hw hh hK hpos
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hs.1 hw hsK
    have := apriori hu.1 (heq hu) hs.2.le hM hR s ⟨hs.1, le_rfl⟩
    rw [← fwdMap_eq hA hw' hu ⟨hs.1, le_rfl⟩] at this
    linarith
  refine ⟨hnot, fun s hs => ?_⟩
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hh hw hnot
  rw [fwdMap_eq hA hw' hu hs]
  exact apriori_bound hu.1 (heq hu) le_rfl hM hR s hs

/-- **T5.** Scale-correct far-field bound for the reverse map. -/
theorem rev_far {W : ℝ → ℝ} (hW : Continuous W) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ r ∈ Icc (0 : ℝ) h, |W r| ≤ M) {z : ℂ} (hz : z ∈ H)
    (hR : 4 * (M + Real.sqrt h) < ‖z‖) :
    ‖revMap W h z - (z - W h)‖ ≤ 4 * h / ‖z‖ := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz h hh
  have heq : ∀ r ∈ Icc (0 : ℝ) h, ‖u r - (z - W r)‖ = ‖∫ x in (0 : ℝ)..r, 2 / u x‖ := by
    intro r hr
    rw [(hu.2 r hr).2]
    rw [show z - (W r : ℂ) - (∫ x in (0 : ℝ)..r, 2 / u x) - (z - (W r : ℂ)) =
      -∫ x in (0 : ℝ)..r, 2 / u x by ring, norm_neg]
  rw [revMap_eq W hW z hh le_rfl hu]
  exact apriori_bound hu.1 heq le_rfl hM hR h ⟨hh, le_rfl⟩

/-! ### UB: the uniform bound for the reverse map -/

theorem norm_revMap_sub_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {h M : ℝ}
    (hh : 0 < h) (hM : ∀ r ∈ Icc (0 : ℝ) h, |W r| ≤ M) {z : ℂ} (hz : z ∈ H) :
    ‖revMap W h z - z‖ ≤ 12 * M + 8 * Real.sqrt h := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hh.le⟩)
  have hsq := Real.sqrt_nonneg h
  set w := revMap W h z with hw
  have hWh : ‖((W h : ℝ) : ℂ)‖ ≤ M := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hM h ⟨hh.le, le_rfl⟩
  by_cases h1 : 4 * (M + Real.sqrt h) < ‖z‖
  · have hf := rev_far hW hh.le hM hz h1
    have h4 := four_mul_div_le_sqrt hh.le hM0 h1
    have e : w - z = (w - (z - W h)) - (W h : ℂ) := by ring
    rw [e]
    calc ‖(w - (z - W h)) - (W h : ℂ)‖ ≤ ‖w - (z - W h)‖ + ‖((W h : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ 12 * M + 8 * Real.sqrt h := by linarith
  push Not at h1
  have hwH : w ∈ H := lt_of_lt_of_le hz (im_le_im_revMap W hW z hz hh.le)
  by_cases h2 : 4 * (2 * M + Real.sqrt h) < ‖w‖
  · set V : ℝ → ℝ := fun s => W (h - s) - W h with hV
    have hVc : Continuous V := by fun_prop
    have hVM : ∀ r ∈ Icc (0 : ℝ) h, |V r| ≤ 2 * M := by
      intro r hr
      have ha := hM (h - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hb := hM h ⟨hh.le, le_rfl⟩
      calc |V r| ≤ |W (h - r)| + |W h| := abs_sub _ _
        _ ≤ 2 * M := by linarith
    obtain ⟨-, hbd⟩ := fwd_far hVc hh.le hVM hwH h2
    have hb := hbd h ⟨hh.le, le_rfl⟩
    have hfz : fwdMap V h w = z := (LoewnerAlgebra.fwdMap_revMap_timeRev W hW hW0 hh hz).2
    rw [hfz] at hb
    have h4 := four_mul_div_le_sqrt hh.le (by positivity : (0 : ℝ) ≤ 2 * M) h2
    have hVh : V h = -W h := by simp [hV, hW0]
    rw [hVh] at hb
    have e : w - z = -(z - (w - ((-W h : ℝ) : ℂ))) - (W h : ℂ) := by push_cast; ring
    rw [e]
    calc ‖-(z - (w - ((-W h : ℝ) : ℂ))) - (W h : ℂ)‖
        ≤ ‖-(z - (w - ((-W h : ℝ) : ℂ)))‖ + ‖((W h : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 12 * M + 8 * Real.sqrt h := by rw [norm_neg]; linarith
  push Not at h2
  calc ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ 12 * M + 8 * Real.sqrt h := by linarith

/-! ### T3: uniform lower bound on compact sets -/

theorem exists_im_lower_of_isCompact {A : ℝ → ℝ} (hA : Continuous A) {r : ℝ} (hr : 0 ≤ r)
    {C : Set ℂ} (hC : IsCompact C) (hCK : C ⊆ H \ fwdHull A r) :
    ∃ m > 0, ∀ z ∈ C, ∀ s ∈ Icc (0 : ℝ) r, m ≤ (fwdMap A s z).im := by
  have hloc := fun z (hz : z ∈ C) => FwdHolo.fwdMap_local hA hr (hCK hz)
  choose mz hmz Cz hCz εz hεz hl using hloc
  obtain ⟨t, ht⟩ := hC.elim_nhds_subcover' (fun z hz => Metric.ball z (εz z hz))
    (fun z hz => Metric.ball_mem_nhds z (hεz z hz))
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · exact ⟨1, one_pos, by simp [hCe]⟩
  have htne : t.Nonempty := by
    obtain ⟨z, hz⟩ := hCne
    obtain ⟨x, hx, -⟩ := mem_iUnion₂.1 (ht hz)
    exact ⟨x, hx⟩
  refine ⟨t.inf' htne (fun x => mz x x.2 / 2), ?_, fun z hz s hs => ?_⟩
  · show 0 < _
    rw [Finset.lt_inf'_iff]
    intro x _
    have := hmz x x.2
    positivity
  · obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (ht hz)
    have hzx' : ‖z - x‖ < εz x x.2 := by rwa [Metric.mem_ball, dist_eq_norm] at hzx
    have h := ((hl x x.2 z hzx').2 s hs).2.1
    exact (Finset.inf'_le _ hx).trans h

/-! ### T6: local growth -/

theorem norm_fwdMap_le_of_mem_diff {A : ℝ → ℝ} (hA : Continuous A) {r h M : ℝ} (hr : 0 ≤ r)
    (hh : 0 ≤ h) (hM : ∀ s ∈ Icc (0 : ℝ) h, |A (r + s) - A r| ≤ M) {z : ℂ}
    (hz : z ∈ fwdHull A (r + h)) (hzr : z ∉ fwdHull A r) :
    ‖fwdMap A r z‖ ≤ 4 * (M + Real.sqrt h) := by
  have hzH : z ∈ H := hz.1
  have hz' : 0 < z.im := hzH
  by_contra hlt
  push Not at hlt
  obtain ⟨-, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff hr).1 ⟨hzH, hzr⟩
  have hur : IsForwardSol A z r u := isForwardSol_restrict hu hr hT'.le
  have hζ : fwdMap A r z = u r := fwdMap_eq hA hz' hu ⟨hr, hT'.le⟩
  have hζH : u r ∈ H := (im_isForwardSol_le hA hz' hur).2 r ⟨hr, le_rfl⟩
  rw [hζ] at hlt
  have hB : Continuous fun s => A (r + s) - A r := by fun_prop
  obtain ⟨hnot, -⟩ := fwd_far hB hh hM hζH hlt
  obtain ⟨-, h', hh', v, hv⟩ := (FwdHolo.mem_compl_fwdHull_iff hh).1 ⟨hζH, hnot⟩
  have hglue := isForwardSol_glue hr (hh.trans hh'.le) hur hv
  exact hz.2.not_gt (lt_of_lt_of_le
    ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
    (ofReal_le_swallowTime (by linarith) ⟨_, hglue⟩))

end CoreArc

end QuantumZipper
