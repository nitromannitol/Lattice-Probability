/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.PsiContinuity at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle

/-!
# Continuity and properness of the Route M strip map

This module proves the analytic part of Proposition M1 from the Peanosphere bundle.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace MatedCRTHarmonic.RouteM

variable {ω : MatedCRT.Path2} {η : ℝ → ℂ} {w : ℂ}

theorem stripRegion_mid_iff (w : ℂ) : stripRegion w = 0 ↔ 0 ≤ w.im ∧ w.im ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    by_cases hb : w.im < 0 <;> simp [stripRegion, hn, hb] at h
  · intro h
    simp [stripRegion, h]

theorem stripRegion_lower_iff (w : ℂ) : stripRegion w = 1 ↔ w.im < 0 := by
  constructor
  · intro h
    by_contra hn
    have him : 0 ≤ w.im := le_of_not_gt hn
    by_cases hle : w.im ≤ 1
    · simp [stripRegion, him, hle] at h
    · simp [stripRegion, him, hle] at h
  · intro h
    have hn : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
      intro hm
      exact (not_lt_of_ge hm.1 h)
    simp [stripRegion, hn, h]

theorem stripRegion_upper_iff (w : ℂ) : stripRegion w = 2 ↔ 1 < w.im := by
  constructor
  · intro h
    have hnot : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
      intro hm
      simp [stripRegion, hm] at h
    have hnotneg : ¬ w.im < 0 := by
      intro hn
      simp [stripRegion, hnot, hn] at h
    have him0 : 0 ≤ w.im := le_of_not_gt hnotneg
    exact lt_of_not_ge (fun hle => hnot ⟨him0, hle⟩)
  · intro h
    have hn : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
      intro hm
      linarith
    have hneg : ¬ w.im < 0 := by linarith
    simp [stripRegion, hn, hneg]

private theorem tendsto_nat_add_one_inv :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hnat

/-- Representatives stay in a common compact interval near every convergent input sequence.
The lower endpoint is chosen using the two liminf hypotheses, while the upper endpoint is the
real coordinate of the limiting point plus a fixed margin. -/
theorem stripRepresentative_eventually_bounded (P : Peanosphere ω η) {u : ℕ → ℂ}
    (hu : Tendsto u atTop (𝓝 w)) :
    ∃ lo hi, ∀ᶠ n in atTop, stripRepresentative P (u n) ∈ Icc lo hi := by
  let t := w.re
  let levL := lCoord ω t + w.im
  let levR := rCoord ω t - (w.im - 1)
  let T := |t| + 3
  have htlo : -T < t - 1 := by
    dsimp [T]
    linarith [neg_abs_le t]
  have hthi : t + 1 < T := by
    dsimp [T]
    linarith [le_abs_self t]
  obtain ⟨sL, hsLT, hsLL⟩ := (P.liminf_L (levL - 1) T).2
  obtain ⟨sR, hsRT, hsRR⟩ := (P.liminf_R (levR - 1) T).2
  let lo := min sL sR
  have hRe : Tendsto (fun n => (u n).re) atTop (𝓝 t) :=
    (Complex.continuous_re.continuousAt.tendsto).comp hu
  have hIm : Tendsto (fun n => (u n).im) atTop (𝓝 w.im) :=
    (Complex.continuous_im.continuousAt.tendsto).comp hu
  have hLlevel : Tendsto (fun n => lCoord ω (u n).re + (u n).im) atTop (𝓝 levL) := by
    have hL : Tendsto (fun n => lCoord ω (u n).re) atTop (𝓝 (lCoord ω t)) :=
      (continuous_lCoord.continuousAt.tendsto).comp hRe
    simpa [levL] using hL.add hIm
  have hRlevel : Tendsto (fun n => rCoord ω (u n).re - ((u n).im - 1)) atTop (𝓝 levR) := by
    have hR : Tendsto (fun n => rCoord ω (u n).re) atTop (𝓝 (rCoord ω t)) :=
      (continuous_rCoord.continuousAt.tendsto).comp hRe
    have him1 : Tendsto (fun n => (u n).im - 1) atTop (𝓝 (w.im - 1)) :=
      hIm.sub tendsto_const_nhds
    simpa [levR] using hR.sub him1
  have hReLo : ∀ᶠ n in atTop, t - 1 < (u n).re :=
    hRe.eventually (Ioi_mem_nhds (by linarith))
  have hReHi : ∀ᶠ n in atTop, (u n).re < t + 1 :=
    hRe.eventually (Iio_mem_nhds (by linarith))
  have hLnear : ∀ᶠ n in atTop, levL - 1 < lCoord ω (u n).re + (u n).im :=
    hLlevel.eventually (Ioi_mem_nhds (by linarith))
  have hRnear : ∀ᶠ n in atTop, levR - 1 < rCoord ω (u n).re - ((u n).im - 1) :=
    hRlevel.eventually (Ioi_mem_nhds (by linarith))
  have hbounded : ∀ᶠ n in atTop, stripRepresentative P (u n) ∈ Icc lo T := by
    filter_upwards [hReLo, hReHi, hLnear, hRnear] with n hnlo hnhi hnL hnR
    have htimeLo : lo ≤ (u n).re := by
      dsimp [lo]
      exact le_trans (min_le_left _ _)
        (le_trans hsLT (le_trans (le_of_lt htlo) hnlo.le))
    have htimeHi : (u n).re ≤ T := le_trans hnhi.le (le_of_lt hthi)
    by_cases hmid : 0 ≤ (u n).im ∧ (u n).im ≤ 1
    · simp [stripRepresentative, hmid]
      exact ⟨htimeLo, htimeHi⟩
    · by_cases hbelow : (u n).im < 0
      · have hcontact : sL ∈ {s | s ≤ (u n).re ∧
            lCoord ω s ≤ lCoord ω (u n).re + (u n).im} := by
          refine ⟨le_trans hsLT (le_of_lt (lt_trans htlo hnlo)), ?_⟩
          have hlev : lCoord ω sL ≤ levL - 1 := by
            change lCoord ω sL < levL - 1 at hsLL
            exact hsLL.le
          dsimp [levL] at hlev ⊢
          linarith
        have hrepLo : sL ≤ ellMinus ω (u n).re
            (lCoord ω (u n).re + (u n).im) := by
          exact le_csSup ⟨(u n).re, fun x hx => hx.1⟩ hcontact
        have hrepHi : ellMinus ω (u n).re
            (lCoord ω (u n).re + (u n).im) ≤ (u n).re :=
          (ellMinus_mem P _ _).1
        have hlo : lo ≤ ellMinus ω (u n).re
            (lCoord ω (u n).re + (u n).im) :=
          le_trans (min_le_left _ _) hrepLo
        have hhi : ellMinus ω (u n).re
            (lCoord ω (u n).re + (u n).im) ≤ T := le_trans hrepHi htimeHi
        simpa [stripRepresentative, hmid, hbelow] using And.intro hlo hhi
      · have him0 : 0 ≤ (u n).im := le_of_not_gt hbelow
        have hcontact : sR ∈ {s | s ≤ (u n).re ∧
            rCoord ω s ≤ rCoord ω (u n).re - ((u n).im - 1)} := by
          refine ⟨le_trans hsRT (le_of_lt (lt_trans htlo hnlo)), ?_⟩
          have hlev : rCoord ω sR ≤ levR - 1 := by
            change rCoord ω sR < levR - 1 at hsRR
            exact hsRR.le
          dsimp [levR] at hlev ⊢
          linarith
        have hrepLo : sR ≤ rhoMinus ω (u n).re
            (rCoord ω (u n).re - ((u n).im - 1)) := by
          exact le_csSup ⟨(u n).re, fun x hx => hx.1⟩ hcontact
        have hrepHi : rhoMinus ω (u n).re
            (rCoord ω (u n).re - ((u n).im - 1)) ≤ (u n).re :=
          (rhoMinus_mem P _ _).1
        have hlo : lo ≤ rhoMinus ω (u n).re
            (rCoord ω (u n).re - ((u n).im - 1)) :=
          le_trans (min_le_right _ _) hrepLo
        have hhi : rhoMinus ω (u n).re
            (rCoord ω (u n).re - ((u n).im - 1)) ≤ T := le_trans hrepHi htimeHi
        simpa [stripRepresentative, hmid, hbelow] using And.intro hlo hhi
  exact ⟨lo, T, hbounded⟩

/-- A convergent sequence of lower-strip representatives has the correct image limit. -/
theorem eta_limit_of_lower_region (P : Peanosphere ω η) {u : ℕ → ℂ} {s : ℝ}
    (hrep : Tendsto (fun n => stripRepresentative P (u n)) atTop (𝓝 s))
    (hRe : Tendsto (fun n => (u n).re) atTop (𝓝 w.re))
    (hIm : Tendsto (fun n => (u n).im) atTop (𝓝 w.im))
    (hlow : ∀ᶠ n in atTop, stripRegion (u n) = 1) :
    η s = shearedStripMap P w := by
  let lev : ℝ := lCoord ω w.re + w.im
  have hlevSeq : Tendsto (fun n => lCoord ω (u n).re + (u n).im) atTop (𝓝 lev) := by
    have hL : Tendsto (fun n => lCoord ω (u n).re) atTop (𝓝 (lCoord ω w.re)) :=
      (continuous_lCoord.continuousAt.tendsto).comp hRe
    simpa [lev] using hL.add hIm
  have hformula : ∀ᶠ n in atTop,
      stripRepresentative P (u n) = ellMinus ω (u n).re
        (lCoord ω (u n).re + (u n).im) := by
    filter_upwards [hlow] with n hn
    have hbelow := (stripRegion_lower_iff (u n)).1 hn
    have hmid : ¬ (0 ≤ (u n).im ∧ (u n).im ≤ 1) := by
      intro hm
      exact (not_lt_of_ge hm.1 hbelow)
    simp [stripRepresentative, hmid, hbelow]
  have hlevelEq : ∀ᶠ n in atTop,
      lCoord ω (stripRepresentative P (u n)) =
        lCoord ω (u n).re + (u n).im := by
    filter_upwards [hlow, hformula] with n hn hf
    rw [hf]
    apply ellMinus_level P
    have hbelow := (stripRegion_lower_iff (u n)).1 hn
    linarith
  have hLrep : Tendsto (fun n => lCoord ω (stripRepresentative P (u n)))
      atTop (𝓝 (lCoord ω s)) :=
    (continuous_lCoord.continuousAt.tendsto).comp hrep
  have hlevelEqFun :
      (fun n => lCoord ω (stripRepresentative P (u n))) =ᶠ[atTop]
        (fun n => lCoord ω (u n).re + (u n).im) := hlevelEq
  have hlevL : Tendsto (fun n => lCoord ω (u n).re + (u n).im)
      atTop (𝓝 (lCoord ω s)) :=
    hLrep.congr' hlevelEqFun
  have hsLevel : lCoord ω s = lev := tendsto_nhds_unique hlevL hlevSeq
  have hrepLe : ∀ᶠ n in atTop, stripRepresentative P (u n) ≤ (u n).re := by
    filter_upwards [hformula] with n hf
    rw [hf]
    exact (ellMinus_mem P _ _).1
  have hdiff : Tendsto (fun n => stripRepresentative P (u n) - (u n).re)
      atTop (𝓝 (s - w.re)) := hrep.sub hRe
  have hsLe : s ≤ w.re := by
    have hclosed := isClosed_Iic.mem_of_tendsto hdiff
      (hrepLe.mono fun _ hn => sub_nonpos.mpr hn)
    exact sub_nonpos.mp hclosed
  have habove : ∀ v ∈ Ioo s w.re, lev ≤ lCoord ω v := by
    intro v hv
    have hreRep : ∀ᶠ n in atTop, stripRepresentative P (u n) < v :=
      hrep.eventually (Iio_mem_nhds hv.1)
    have htime : ∀ᶠ n in atTop, v < (u n).re :=
      hRe.eventually (Ioi_mem_nhds hv.2)
    have hstrict : ∀ᶠ n in atTop, lCoord ω (u n).re + (u n).im < lCoord ω v := by
      filter_upwards [hlow, hformula, hreRep, htime] with n hn hf hsn htn
      have hbelow := (stripRegion_lower_iff (u n)).1 hn
      have hnot : ¬ lCoord ω v ≤ lCoord ω (u n).re + (u n).im := by
        intro hle
        have hmem : v ∈ {x | x ≤ (u n).re ∧ lCoord ω x ≤
            lCoord ω (u n).re + (u n).im} := ⟨htn.le, hle⟩
        have hsup := le_csSup (show BddAbove {x : ℝ | x ≤ (u n).re ∧
            lCoord ω x ≤ lCoord ω (u n).re + (u n).im} from
            ⟨(u n).re, fun x hx => hx.1⟩) hmem
        change v ≤ ellMinus ω (u n).re (lCoord ω (u n).re + (u n).im) at hsup
        rw [← hf] at hsup
        exact (not_lt_of_ge hsup) hsn
      exact lt_of_not_ge hnot
    have hclosed := isClosed_Iic.mem_of_tendsto hlevSeq
      (hstrict.mono fun _ hn => hn.le)
    exact hclosed
  have himNonpos : w.im ≤ 0 := by
    apply isClosed_Iic.mem_of_tendsto hIm
    filter_upwards [hlow] with n hn
    exact (stripRegion_lower_iff (u n)).1 hn |>.le
  let s₀ := stripRepresentative P w
  have hs₀Level : lCoord ω s₀ = lev := by
    by_cases hy : w.im = 0
    · simp [s₀, lev, stripRepresentative, hy]
    · have hy' : w.im < 0 := by
        rcases lt_or_eq_of_le himNonpos with hlt | heq
        · exact hlt
        · exact (hy heq).elim
      have hmid : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
        intro hm
        exact (not_lt_of_ge hm.1 hy')
      have hlevel : lev < lCoord ω w.re := by
        dsimp [lev]
        linarith
      have hcontact := ellMinus_level P hlevel
      have hrepEq : s₀ = ellMinus ω w.re lev := by
        simp [s₀, stripRepresentative, hmid, hy', lev]
      rw [hrepEq]
      exact hcontact
  have hs₀Le : s₀ ≤ w.re := by
    by_cases hy : w.im = 0
    · simp [s₀, stripRepresentative, hy]
    · have hy' : w.im < 0 := by
        rcases lt_or_eq_of_le himNonpos with hlt | heq
        · exact hlt
        · exact (hy heq).elim
      have hmid : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
        intro hm
        exact (not_lt_of_ge hm.1 hy')
      have hrepEq : s₀ = ellMinus ω w.re lev := by
        simp [s₀, stripRepresentative, hmid, hy', lev]
      rw [hrepEq]
      exact (ellMinus_mem P _ _).1
  have hsLe₀ : s ≤ s₀ := by
    by_cases hy : w.im = 0
    ·
      have hs₀Eq : s₀ = w.re := by
        simp [s₀, stripRepresentative, hy]
      calc
        s ≤ w.re := hsLe
        _ = s₀ := hs₀Eq.symm
    · have hy' : w.im < 0 := by
        rcases lt_or_eq_of_le himNonpos with hlt | heq
        · exact hlt
        · exact (hy heq).elim
      have hmid : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
        intro hm
        exact (not_lt_of_ge hm.1 hy')
      have hmem : s ∈ {x | x ≤ w.re ∧ lCoord ω x ≤ lev} := ⟨hsLe, hsLevel.le⟩
      have hsup := le_csSup
        (show BddAbove {x : ℝ | x ≤ w.re ∧ lCoord ω x ≤ lev} from
          ⟨w.re, fun x hx => hx.1⟩) hmem
      change s ≤ ellMinus ω w.re lev at hsup
      have hrepEq : s₀ = ellMinus ω w.re lev := by
        simp [s₀, stripRepresentative, hmid, hy', lev]
      simpa [hrepEq] using hsup
  have haboveTarget : ∀ v ∈ Ioo s s₀, lev ≤ lCoord ω v := by
    intro v hv
    apply habove v
    exact ⟨hv.1, lt_of_lt_of_le hv.2 hs₀Le⟩
  have heta : η s = η s₀ := eta_eq_of_L_level_interval P hsLe₀ hsLevel hs₀Level haboveTarget
  rw [heta]
  rw [shearedStripMap_eq_eta_representative]

/-- The upper-strip counterpart of `eta_limit_of_lower_region`. -/
theorem eta_limit_of_upper_region (P : Peanosphere ω η) {u : ℕ → ℂ} {s : ℝ}
    (hrep : Tendsto (fun n => stripRepresentative P (u n)) atTop (𝓝 s))
    (hRe : Tendsto (fun n => (u n).re) atTop (𝓝 w.re))
    (hIm : Tendsto (fun n => (u n).im) atTop (𝓝 w.im))
    (hupper : ∀ᶠ n in atTop, stripRegion (u n) = 2) :
    η s = shearedStripMap P w := by
  let lev : ℝ := rCoord ω w.re - (w.im - 1)
  have hlevSeq : Tendsto (fun n => rCoord ω (u n).re - ((u n).im - 1))
      atTop (𝓝 lev) := by
    have hR : Tendsto (fun n => rCoord ω (u n).re) atTop (𝓝 (rCoord ω w.re)) :=
      (continuous_rCoord.continuousAt.tendsto).comp hRe
    have him1 : Tendsto (fun n => (u n).im - 1) atTop (𝓝 (w.im - 1)) :=
      hIm.sub tendsto_const_nhds
    simpa [lev] using hR.sub him1
  have hformula : ∀ᶠ n in atTop,
      stripRepresentative P (u n) = rhoMinus ω (u n).re
        (rCoord ω (u n).re - ((u n).im - 1)) := by
    filter_upwards [hupper] with n hn
    have habove := (stripRegion_upper_iff (u n)).1 hn
    have hmid : ¬ (0 ≤ (u n).im ∧ (u n).im ≤ 1) := by
      intro hm
      linarith
    have hnotbelow : ¬ (u n).im < 0 := by linarith
    simp [stripRepresentative, hmid, hnotbelow]
  have hlevelEq : ∀ᶠ n in atTop,
      rCoord ω (stripRepresentative P (u n)) =
        rCoord ω (u n).re - ((u n).im - 1) := by
    filter_upwards [hupper, hformula] with n hn hf
    rw [hf]
    apply rhoMinus_level P
    have habove := (stripRegion_upper_iff (u n)).1 hn
    linarith
  have hRrep : Tendsto (fun n => rCoord ω (stripRepresentative P (u n)))
      atTop (𝓝 (rCoord ω s)) :=
    (continuous_rCoord.continuousAt.tendsto).comp hrep
  have hlevelEqFun :
      (fun n => rCoord ω (stripRepresentative P (u n))) =ᶠ[atTop]
        (fun n => rCoord ω (u n).re - ((u n).im - 1)) := hlevelEq
  have hlevR : Tendsto (fun n => rCoord ω (u n).re - ((u n).im - 1))
      atTop (𝓝 (rCoord ω s)) := hRrep.congr' hlevelEqFun
  have hsLevel : rCoord ω s = lev := tendsto_nhds_unique hlevR hlevSeq
  have hrepLe : ∀ᶠ n in atTop, stripRepresentative P (u n) ≤ (u n).re := by
    filter_upwards [hformula] with n hf
    rw [hf]
    exact (rhoMinus_mem P _ _).1
  have hdiff : Tendsto (fun n => stripRepresentative P (u n) - (u n).re)
      atTop (𝓝 (s - w.re)) := hrep.sub hRe
  have hsLe : s ≤ w.re := by
    have hclosed := isClosed_Iic.mem_of_tendsto hdiff
      (hrepLe.mono fun _ hn => sub_nonpos.mpr hn)
    exact sub_nonpos.mp hclosed
  have habove : ∀ v ∈ Ioo s w.re, lev ≤ rCoord ω v := by
    intro v hv
    have hreRep : ∀ᶠ n in atTop, stripRepresentative P (u n) < v :=
      hrep.eventually (Iio_mem_nhds hv.1)
    have htime : ∀ᶠ n in atTop, v < (u n).re :=
      hRe.eventually (Ioi_mem_nhds hv.2)
    have hstrict : ∀ᶠ n in atTop,
        rCoord ω (u n).re - ((u n).im - 1) < rCoord ω v := by
      filter_upwards [hupper, hformula, hreRep, htime] with n hn hf hsn htn
      have hnot : ¬ rCoord ω v ≤ rCoord ω (u n).re - ((u n).im - 1) := by
        intro hle
        have hmem : v ∈ {x | x ≤ (u n).re ∧ rCoord ω x ≤
            rCoord ω (u n).re - ((u n).im - 1)} := ⟨htn.le, hle⟩
        have hsup := le_csSup (show BddAbove {x : ℝ | x ≤ (u n).re ∧
            rCoord ω x ≤ rCoord ω (u n).re - ((u n).im - 1)} from
            ⟨(u n).re, fun x hx => hx.1⟩) hmem
        change v ≤ rhoMinus ω (u n).re (rCoord ω (u n).re - ((u n).im - 1)) at hsup
        rw [← hf] at hsup
        exact (not_lt_of_ge hsup) hsn
      exact lt_of_not_ge hnot
    have hclosed := isClosed_Iic.mem_of_tendsto hlevSeq
      (hstrict.mono fun _ hn => hn.le)
    exact hclosed
  have himGeOne : 1 ≤ w.im := by
    apply isClosed_Ici.mem_of_tendsto hIm
    filter_upwards [hupper] with n hn
    exact (stripRegion_upper_iff (u n)).1 hn |>.le
  let s₀ := stripRepresentative P w
  have hs₀Level : rCoord ω s₀ = lev := by
    by_cases hy : w.im = 1
    · simp [s₀, lev, stripRepresentative, hy]
    · have hy' : 1 < w.im := by
        rcases eq_or_lt_of_le himGeOne with heq | hlt
        · exact (hy heq.symm).elim
        · exact hlt
      have hmid : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
        intro hm
        linarith
      have hnotbelow : ¬ w.im < 0 := by linarith
      have hlevel : lev < rCoord ω w.re := by
        dsimp [lev]
        linarith
      have hcontact := rhoMinus_level P hlevel
      have hrepEq : s₀ = rhoMinus ω w.re lev := by
        simp [s₀, stripRepresentative, hmid, hnotbelow, lev]
      rw [hrepEq]
      exact hcontact
  have hs₀Le : s₀ ≤ w.re := by
    by_cases hy : w.im = 1
    · simp [s₀, stripRepresentative, hy]
    · have hy' : 1 < w.im := by
        rcases eq_or_lt_of_le himGeOne with heq | hlt
        · exact (hy heq.symm).elim
        · exact hlt
      have hmid : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
        intro hm
        linarith
      have hnotbelow : ¬ w.im < 0 := by linarith
      have hrepEq : s₀ = rhoMinus ω w.re lev := by
        simp [s₀, stripRepresentative, hmid, hnotbelow, lev]
      rw [hrepEq]
      exact (rhoMinus_mem P _ _).1
  have hsLe₀ : s ≤ s₀ := by
    by_cases hy : w.im = 1
    · have hs₀Eq : s₀ = w.re := by simp [s₀, stripRepresentative, hy]
      rw [hs₀Eq]
      exact hsLe
    · have hy' : 1 < w.im := by
        rcases eq_or_lt_of_le himGeOne with heq | hlt
        · exact (hy heq.symm).elim
        · exact hlt
      have hmid : ¬ (0 ≤ w.im ∧ w.im ≤ 1) := by
        intro hm
        linarith
      have hnotbelow : ¬ w.im < 0 := by linarith
      have hmem : s ∈ {x | x ≤ w.re ∧ rCoord ω x ≤ lev} := ⟨hsLe, hsLevel.le⟩
      have hsup := le_csSup
        (show BddAbove {x : ℝ | x ≤ w.re ∧ rCoord ω x ≤ lev} from
          ⟨w.re, fun x hx => hx.1⟩) hmem
      change s ≤ rhoMinus ω w.re lev at hsup
      have hrepEq : s₀ = rhoMinus ω w.re lev := by
        simp [s₀, stripRepresentative, hmid, hnotbelow, lev]
      simpa [hrepEq] using hsup
  have haboveTarget : ∀ v ∈ Ioo s s₀, lev ≤ rCoord ω v := by
    intro v hv
    apply habove v
    exact ⟨hv.1, lt_of_lt_of_le hv.2 hs₀Le⟩
  have heta : η s = η s₀ := eta_eq_of_R_level_interval P hsLe₀ hsLevel hs₀Level haboveTarget
  rw [heta]
  rw [shearedStripMap_eq_eta_representative]

/-- Proposition M1's continuity assertion for the sheared strip map. -/
theorem shearedStripMap_continuousAt (P : Peanosphere ω η) (w : ℂ) :
    ContinuousAt (shearedStripMap P) w := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  by_contra hδ
  have hbad : ∀ δ > 0, ∃ z : ℂ,
      dist z w < δ ∧ ε ≤ dist (shearedStripMap P z) (shearedStripMap P w) := by
    intro δ hδpos
    by_contra h
    push Not at h
    apply hδ
    refine ⟨δ, hδpos, ?_⟩
    intro z hz
    exact h z hz
  let x : ℕ → ℂ := fun n => Classical.choose (hbad (((n : ℝ) + 1)⁻¹) (by positivity))
  have hxspec (n : ℕ) :
      dist (x n) w < ((n : ℝ) + 1)⁻¹ ∧
        ε ≤ dist (shearedStripMap P (x n)) (shearedStripMap P w) :=
    Classical.choose_spec (hbad (((n : ℝ) + 1)⁻¹) (by positivity))
  have hx : Tendsto x atTop (𝓝 w) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply Metric.tendsto_nhds.2
    intro δ hδpos
    filter_upwards [tendsto_nat_add_one_inv.eventually (Iio_mem_nhds hδpos)] with n hn
    simpa [Real.dist_eq] using lt_trans (hxspec n).1 hn
  obtain ⟨lo, hi, hbound⟩ := stripRepresentative_eventually_bounded (w := w) P hx
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hbound
  let seq : ℕ → ℝ × Fin 3 := fun n =>
    (stripRepresentative P (x (n + N)), stripRegion (x (n + N)))
  have hseqMem (n : ℕ) : seq n ∈ Icc lo hi ×ˢ (Set.univ : Set (Fin 3)) := by
    refine ⟨hN (n + N) (by omega), Set.mem_univ _⟩
  have hcompact : IsCompact (Icc lo hi ×ˢ (Set.univ : Set (Fin 3))) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨a, ha, φ, hφ, hpair⟩ := hcompact.tendsto_subseq hseqMem
  have hφTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφN : Tendsto (fun n => φ n + N) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro m
    filter_upwards [hφTop.eventually (eventually_ge_atTop m)] with n hn
    exact le_trans hn (Nat.le_add_right _ _)
  let z : ℕ → ℂ := fun n => x (φ n + N)
  have hzin : Tendsto z atTop (𝓝 w) := by
    exact hx.comp hφN
  have hfst : Tendsto (fun n => stripRepresentative P (z n)) atTop (𝓝 a.1) := by
    have h := (continuous_fst.continuousAt.tendsto).comp hpair
    simpa [Function.comp_def, seq, z] using h
  have hsnd : Tendsto (fun n => stripRegion (z n)) atTop (𝓝 a.2) := by
    have h := (continuous_snd.continuousAt.tendsto).comp hpair
    simpa [Function.comp_def, seq, z] using h
  have hregEq : ∀ᶠ n in atTop, stripRegion (z n) = a.2 := by
    have hopen : IsOpen ({a.2} : Set (Fin 3)) := isOpen_discrete _
    have hmem : ({a.2} : Set (Fin 3)) ∈ 𝓝 a.2 := hopen.mem_nhds (Set.mem_singleton a.2)
    filter_upwards [hsnd.eventually hmem] with n hn
    exact Set.mem_singleton_iff.mp hn
  have hRe : Tendsto (fun n => (z n).re) atTop (𝓝 w.re) :=
    (Complex.continuous_re.continuousAt.tendsto).comp hzin
  have hIm : Tendsto (fun n => (z n).im) atTop (𝓝 w.im) :=
    (Complex.continuous_im.continuousAt.tendsto).comp hzin
  have hηlim : Tendsto (fun n => η (stripRepresentative P (z n)))
      atTop (𝓝 (η a.1)) := (P.cont.continuousAt.tendsto).comp hfst
  have hbadOut : ∀ n, ε ≤ dist (shearedStripMap P (z n)) (shearedStripMap P w) := by
    intro n
    exact (hxspec (φ n + N)).2
  have hmaplim_of_eq (hηeq : η a.1 = shearedStripMap P w) :
      Tendsto (fun n => shearedStripMap P (z n)) atTop (𝓝 (shearedStripMap P w)) := by
    have hmap : (fun n => η (stripRepresentative P (z n))) =ᶠ[atTop]
        (fun n => shearedStripMap P (z n)) := by
      filter_upwards [] with n
      exact (shearedStripMap_eq_eta_representative P (z n)).symm
    have h := hηlim.congr' hmap
    simpa [hηeq] using h
  have hcontradiction (hlimit : Tendsto (fun n => shearedStripMap P (z n))
      atTop (𝓝 (shearedStripMap P w))) : False := by
    have hclose := hlimit.eventually (Metric.ball_mem_nhds _ hε)
    obtain ⟨n, hn⟩ := hclose.exists
    exact (not_lt_of_ge (hbadOut n)) hn
  by_cases hmid : a.2 = 0
  · have hreg : ∀ᶠ n in atTop, stripRegion (z n) = 0 := by
      filter_upwards [hregEq] with n hn
      rw [hmid] at hn
      exact hn
    have hrepEq : ∀ᶠ n in atTop,
        stripRepresentative P (z n) = (z n).re := by
      filter_upwards [hreg] with n hn
      have hm := (stripRegion_mid_iff (z n)).1 hn
      simp [stripRepresentative, hm]
    have hReLimit : Tendsto (fun n => (z n).re) atTop (𝓝 a.1) := hfst.congr' hrepEq
    have htime : a.1 = w.re := tendsto_nhds_unique hReLimit hRe
    have hmidCoords : ∀ᶠ n in atTop, (z n).im ∈ Icc (0 : ℝ) 1 := by
      filter_upwards [hreg] with n hn
      exact (stripRegion_mid_iff (z n)).1 hn
    have hwmid : w.im ∈ Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hIm hmidCoords
    have hηeq : η a.1 = shearedStripMap P w := by
      calc
        η a.1 = η w.re := congrArg η htime
        _ = shearedStripMap P w := by
          rw [shearedStripMap_eq_eta_representative]
          rcases hwmid with ⟨hy₀, hy₁⟩
          simp [stripRepresentative, hy₀, hy₁]
    exact hcontradiction (hmaplim_of_eq hηeq)
  · by_cases hlower : a.2 = 1
    · have hreg : ∀ᶠ n in atTop, stripRegion (z n) = 1 := by
        filter_upwards [hregEq] with n hn
        rw [hlower] at hn
        exact hn
      exact hcontradiction (hmaplim_of_eq
        (eta_limit_of_lower_region P hfst hRe hIm hreg))
    · have hupperIdx : a.2 = 2 := by
        omega
      have hreg : ∀ᶠ n in atTop, stripRegion (z n) = 2 := by
        filter_upwards [hregEq] with n hn
        rw [hupperIdx] at hn
        exact hn
      exact hcontradiction (hmaplim_of_eq
        (eta_limit_of_upper_region P hfst hRe hIm hreg))

theorem shearedStripMap_continuous (P : Peanosphere ω η) :
    Continuous (shearedStripMap P) :=
  continuous_iff_continuousAt.mpr fun w => shearedStripMap_continuousAt P w

/-- The two endpoints of an excursion chord have the same Peanosphere image. -/
theorem eta_eq_of_L_last_first (P : Peanosphere ω η) {t level : ℝ}
    (hlevel : level < lCoord ω t) :
    η (ellMinus ω t level) = η (ellPlus ω t level) := by
  let s := ellMinus ω t level
  let p := ellPlus ω t level
  have hslev : lCoord ω s = level := by
    simpa [s] using ellMinus_level P hlevel
  have hplev : lCoord ω p = level := by
    simpa [p] using ellPlus_level P hlevel
  have hst : s ≤ t := by simpa [s] using (ellMinus_mem P t level).1
  have htp : t ≤ p := by simpa [p] using (ellPlus_mem P t level).1
  have hsp : s ≤ p := hst.trans htp
  have habove : ∀ u ∈ Ioo s p, level ≤ lCoord ω u := by
    intro u hu
    rcases le_total u t with hut | htu
    · by_contra hn
      have hle : lCoord ω u ≤ level := le_of_not_ge hn
      have hmem : u ∈ {x | x ≤ t ∧ lCoord ω x ≤ level} := ⟨hut, hle⟩
      have hsup := le_csSup (show BddAbove {x : ℝ | x ≤ t ∧ lCoord ω x ≤ level} from
        ⟨t, fun x hx => hx.1⟩) hmem
      change u ≤ ellMinus ω t level at hsup
      exact (not_le_of_gt hu.1) hsup
    · by_contra hn
      have hle : lCoord ω u ≤ level := le_of_not_ge hn
      have hmem : u ∈ {x | t ≤ x ∧ lCoord ω x ≤ level} := ⟨htu, hle⟩
      have hinf := csInf_le
        (show BddBelow {x : ℝ | t ≤ x ∧ lCoord ω x ≤ level} from
          ⟨t, fun x hx => hx.1⟩) hmem
      change ellPlus ω t level ≤ u at hinf
      exact (not_le_of_gt hu.2) hinf
  exact eta_eq_of_L_level_interval P hsp hslev hplev habove

/-- The R-coordinate counterpart of `eta_eq_of_L_last_first`. -/
theorem eta_eq_of_R_last_first (P : Peanosphere ω η) {t level : ℝ}
    (hlevel : level < rCoord ω t) :
    η (rhoMinus ω t level) = η (rhoPlus ω t level) := by
  let s := rhoMinus ω t level
  let p := rhoPlus ω t level
  have hslev : rCoord ω s = level := by
    simpa [s] using rhoMinus_level P hlevel
  have hplev : rCoord ω p = level := by
    simpa [p] using rhoPlus_level P hlevel
  have hst : s ≤ t := by simpa [s] using (rhoMinus_mem P t level).1
  have htp : t ≤ p := by simpa [p] using (rhoPlus_mem P t level).1
  have hsp : s ≤ p := hst.trans htp
  have habove : ∀ u ∈ Ioo s p, level ≤ rCoord ω u := by
    intro u hu
    rcases le_total u t with hut | htu
    · by_contra hn
      have hle : rCoord ω u ≤ level := le_of_not_ge hn
      have hmem : u ∈ {x | x ≤ t ∧ rCoord ω x ≤ level} := ⟨hut, hle⟩
      have hsup := le_csSup (show BddAbove {x : ℝ | x ≤ t ∧ rCoord ω x ≤ level} from
        ⟨t, fun x hx => hx.1⟩) hmem
      change u ≤ rhoMinus ω t level at hsup
      exact (not_le_of_gt hu.1) hsup
    · by_contra hn
      have hle : rCoord ω u ≤ level := le_of_not_ge hn
      have hmem : u ∈ {x | t ≤ x ∧ rCoord ω x ≤ level} := ⟨htu, hle⟩
      have hinf := csInf_le
        (show BddBelow {x : ℝ | t ≤ x ∧ rCoord ω x ≤ level} from
          ⟨t, fun x hx => hx.1⟩) hmem
      change rhoPlus ω t level ≤ u at hinf
      exact (not_le_of_gt hu.2) hinf
  exact eta_eq_of_R_level_interval P hsp hslev hplev habove

/-- A compact target set has compact preimage under the Route M map. -/
theorem shearedStripMap_isProperMap (P : Peanosphere ω η) :
    IsProperMap (shearedStripMap P) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨shearedStripMap_continuous P, ?_⟩
  intro K hK
  by_cases hKempty : K = ∅
  · simp [hKempty]
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
  have htrans : η ⁻¹' Kᶜ ∈ Filter.cocompact ℝ :=
    P.transient (hK.compl_mem_cocompact)
  obtain ⟨C, hC, hCsub⟩ := Filter.mem_cocompact.mp htrans
  have htimeC : ∀ {t}, η t ∈ K → t ∈ C := by
    intro t htK
    by_contra htC
    have htOut : η t ∈ Kᶜ := hCsub htC
    change η t ∉ K at htOut
    exact htOut htK
  obtain ⟨q, hq⟩ := hKne
  obtain ⟨t₀, ht₀⟩ := P.surj q
  have ht₀C : t₀ ∈ C := htimeC (by simpa [ht₀] using hq)
  obtain ⟨B, hCB⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hC.isBounded
  have hBnonneg : 0 ≤ B := by
    have hball := hCB ht₀C
    have habs : |t₀| ≤ B := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hball
    exact le_trans (abs_nonneg t₀) habs
  have htimeBounds : ∀ t ∈ C, -B ≤ t ∧ t ≤ B := by
    intro t ht
    have hball := hCB ht
    have habs : |t| ≤ B := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hball
    exact abs_le.mp habs
  have hzeroI : (0 : ℝ) ∈ Icc (-B) B := by
    exact ⟨by linarith, hBnonneg⟩
  have hLcompact : IsCompact (lCoord ω '' Icc (-B) B) :=
    isCompact_Icc.image continuous_lCoord
  have hRcompact : IsCompact (rCoord ω '' Icc (-B) B) :=
    isCompact_Icc.image continuous_rCoord
  obtain ⟨ML, hLball⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hLcompact.isBounded
  obtain ⟨MR, hRball⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hRcompact.isBounded
  have hMLnonneg : 0 ≤ ML := by
    have hball := hLball ⟨0, hzeroI, rfl⟩
    have habs : |lCoord ω 0| ≤ ML := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hball
    exact le_trans (abs_nonneg _) habs
  have hMRnonneg : 0 ≤ MR := by
    have hball := hRball ⟨0, hzeroI, rfl⟩
    have habs : |rCoord ω 0| ≤ MR := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hball
    exact le_trans (abs_nonneg _) habs
  have hLbound {t : ℝ} (ht : t ∈ Icc (-B) B) : |lCoord ω t| ≤ ML := by
    have hball := hLball ⟨t, ht, rfl⟩
    simpa [Metric.mem_closedBall, Real.dist_eq] using hball
  have hRbound {t : ℝ} (ht : t ∈ Icc (-B) B) : |rCoord ω t| ≤ MR := by
    have hball := hRball ⟨t, ht, rfl⟩
    simpa [Metric.mem_closedBall, Real.dist_eq] using hball
  let Y := max 1 (max (2 * ML) (1 + 2 * MR))
  have hYone : 1 ≤ Y := le_max_left _ _
  have hYL : 2 * ML ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hYR : 1 + 2 * MR ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hYnonneg : 0 ≤ Y := le_trans (by norm_num : (0 : ℝ) ≤ 1) hYone
  let stripPointPair : ℝ × ℝ → ℂ := fun p => stripPoint p.1 p.2
  have hpreSub : (shearedStripMap P ⁻¹' K) ⊆
      stripPointPair '' (Icc (-B) B ×ˢ Icc (-Y) Y) := by
    intro z hz
    have hqK : shearedStripMap P z ∈ K := hz
    have hmake (hyRe : -B ≤ z.re ∧ z.re ≤ B) (hyIm : -Y ≤ z.im ∧ z.im ≤ Y) :
        z ∈ stripPointPair '' (Icc (-B) B ×ˢ Icc (-Y) Y) := by
      refine ⟨(z.re, z.im), ⟨hyRe, hyIm⟩, ?_⟩
      apply Complex.ext <;> simp [stripPointPair, stripPoint]
    by_cases hmid : 0 ≤ z.im ∧ z.im ≤ 1
    · have hmap : shearedStripMap P z = η z.re := by
        rw [shearedStripMap_eq_eta_representative]
        simp [stripRepresentative, hmid]
      have hreC : z.re ∈ C := htimeC (hmap ▸ hqK)
      have hre := htimeBounds z.re hreC
      have him : -Y ≤ z.im ∧ z.im ≤ Y := by
        constructor <;> linarith [hmid.1, hmid.2, hYone]
      exact hmake ⟨hre.1, hre.2⟩ him
    · by_cases hbelow : z.im < 0
      · have hmid' : ¬ (0 ≤ z.im ∧ z.im ≤ 1) := by
          intro hm
          exact (not_lt_of_ge hm.1 hbelow)
        let lev := lCoord ω z.re + z.im
        let s := ellMinus ω z.re lev
        have hlev : lev < lCoord ω z.re := by dsimp [lev]; linarith
        have hsLevel : lCoord ω s = lev := by simpa [s] using ellMinus_level P hlev
        have hmap : shearedStripMap P z = η s := by
          rw [shearedStripMap_eq_eta_representative]
          simp [stripRepresentative, hmid', hbelow, s, lev]
        have hsC : s ∈ C := htimeC (hmap ▸ hqK)
        let p := ellPlus ω z.re lev
        have hEtaEnds : η s = η p := by
          simpa [s, p] using eta_eq_of_L_last_first P hlev
        have hpC : p ∈ C := htimeC (hEtaEnds ▸ hmap ▸ hqK)
        have hst : s ≤ z.re := by simpa [s] using (ellMinus_mem P _ _).1
        have htp : z.re ≤ p := by simpa [p] using (ellPlus_mem P _ _).1
        have hsB := htimeBounds s hsC
        have hpB := htimeBounds p hpC
        have hreB : -B ≤ z.re ∧ z.re ≤ B :=
          ⟨le_trans hsB.1 hst, le_trans htp hpB.2⟩
        have hLsb : |lCoord ω s| ≤ ML := hLbound ⟨hsB.1, hsB.2⟩
        have hLtb : |lCoord ω z.re| ≤ ML := hLbound hreB
        have himEq : z.im = lCoord ω s - lCoord ω z.re := by
          dsimp [lev] at hsLevel
          linarith
        have himAbs : |z.im| ≤ 2 * ML := by
          rw [himEq]
          calc
            |lCoord ω s - lCoord ω z.re| ≤ |lCoord ω s| + |lCoord ω z.re| := abs_sub _ _
            _ ≤ ML + ML := add_le_add hLsb hLtb
            _ = 2 * ML := by ring
        have himB : -Y ≤ z.im ∧ z.im ≤ Y := abs_le.mp (le_trans himAbs hYL)
        exact hmake hreB himB
      · have him0 : 0 ≤ z.im := le_of_not_gt hbelow
        have hmid' : ¬ (0 ≤ z.im ∧ z.im ≤ 1) := hmid
        have habove : 1 < z.im := by
          by_contra h
          have hle : z.im ≤ 1 := le_of_not_gt h
          exact hmid ⟨him0, hle⟩
        let lev := rCoord ω z.re - (z.im - 1)
        let s := rhoMinus ω z.re lev
        have hlev : lev < rCoord ω z.re := by dsimp [lev]; linarith
        have hsLevel : rCoord ω s = lev := by simpa [s] using rhoMinus_level P hlev
        have hmap : shearedStripMap P z = η s := by
          rw [shearedStripMap_eq_eta_representative]
          simp [stripRepresentative, hmid', hbelow, s, lev]
        have hsC : s ∈ C := htimeC (hmap ▸ hqK)
        let p := rhoPlus ω z.re lev
        have hEtaEnds : η s = η p := by
          simpa [s, p] using eta_eq_of_R_last_first P hlev
        have hpC : p ∈ C := htimeC (hEtaEnds ▸ hmap ▸ hqK)
        have hst : s ≤ z.re := by simpa [s] using (rhoMinus_mem P _ _).1
        have htp : z.re ≤ p := by simpa [p] using (rhoPlus_mem P _ _).1
        have hsB := htimeBounds s hsC
        have hpB := htimeBounds p hpC
        have hreB : -B ≤ z.re ∧ z.re ≤ B :=
          ⟨le_trans hsB.1 hst, le_trans htp hpB.2⟩
        have hRsb : |rCoord ω s| ≤ MR := hRbound ⟨hsB.1, hsB.2⟩
        have hRtb : |rCoord ω z.re| ≤ MR := hRbound hreB
        have himEq : z.im = 1 + rCoord ω z.re - rCoord ω s := by
          dsimp [lev] at hsLevel
          linarith
        have hraw : |1 + rCoord ω z.re - rCoord ω s| ≤
            1 + |rCoord ω z.re| + |rCoord ω s| := by
          calc
            |1 + rCoord ω z.re - rCoord ω s|
                ≤ |1 + rCoord ω z.re| + |rCoord ω s| := abs_sub _ _
            _ ≤ (|1| + |rCoord ω z.re|) + |rCoord ω s| :=
              add_le_add (abs_add_le 1 (rCoord ω z.re)) le_rfl
            _ = 1 + |rCoord ω z.re| + |rCoord ω s| := by simp [abs_one]
        have himAbs : |z.im| ≤ 1 + 2 * MR := by
          rw [himEq]
          calc
            |1 + rCoord ω z.re - rCoord ω s| ≤
                1 + |rCoord ω z.re| + |rCoord ω s| := hraw
            _ ≤ 1 + MR + MR := by nlinarith [hRtb, hRsb]
            _ = 1 + 2 * MR := by ring
        have himB : -Y ≤ z.im ∧ z.im ≤ Y := abs_le.mp (le_trans himAbs hYR)
        exact hmake hreB himB
  let rect := stripPointPair '' (Icc (-B) B ×ˢ Icc (-Y) Y)
  have hrect : IsCompact rect :=
    (isCompact_Icc.prod isCompact_Icc).image continuous_stripPoint_pair
  have hpreclosed : IsClosed (shearedStripMap P ⁻¹' K) :=
    hK.isClosed.preimage (shearedStripMap_continuous P)
  have hpre : IsCompact (shearedStripMap P ⁻¹' K) :=
    hrect.of_isClosed_subset hpreclosed (by simpa [rect] using hpreSub)
  exact hpre

/-- Properness of the sheared strip map gives its required cocompact tendsto statement. -/
theorem shearedStripMap_tendsto_cocompact (P : Peanosphere ω η) :
    Tendsto (shearedStripMap P) (Filter.cocompact ℂ) (Filter.cocompact ℂ) :=
  (isProperMap_iff_tendsto_cocompact.mp (shearedStripMap_isProperMap P)).2

/-- The fibres satisfy the preconnectedness field required by `MonotoneDrawing`. -/
theorem shearedStripMap_fiber_isPreconnected (P : Peanosphere ω η) (q : ℂ) :
    IsPreconnected (shearedStripMap P ⁻¹' {q}) :=
  (shearedStripMap_fiber_isPathConnected P q).isConnected.isPreconnected

end MatedCRTHarmonic.RouteM
