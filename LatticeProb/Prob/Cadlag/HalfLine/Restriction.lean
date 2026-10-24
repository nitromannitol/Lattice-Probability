import LatticeProb.Prob.Cadlag.HalfLine.Metric
import LatticeProb.Prob.Cadlag.HalfLine.Convergence
import LatticeProb.Prob.Cadlag.HalfLine.Separable
import LatticeProb.Prob.Cadlag.Basic
import LatticeProb.Prob.Cadlag.Metric
import LatticeProb.Prob.Cadlag.Measurable

/-!
# Restriction of half-line càdlàg paths

Restricting a half-line path to a closed finite interval preserves right continuity
and genuine left limits, including the left limit at the terminal time. The restriction
is continuous at paths continuous at the terminal time, by modifying time changes
on a short terminal interval and controlling stopped discrepancies with Fatou’s lemma.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- The inclusion of a finite time interval in the nonnegative half-line. -/
def intervalTime {T : ℝ} (t : Icc (0 : ℝ) T) : Time := ⟨t.1, t.2.1⟩

/-- The time inclusion is continuous for the usual subtype topologies. -/
theorem continuous_intervalTime (T : ℝ) :
    Continuous (intervalTime : Icc (0 : ℝ) T → Time) :=
  continuous_subtype_val.subtype_mk _

/-- A half-line time change can be made to fix the finite terminal time, while
agreeing with the original change up to any earlier time whose image lies below it. -/
theorem exists_terminal_timeChange {T : ℝ} (l : LambdaPrime) (a : Time)
    (ha : (a : ℝ) < T) (hla : (l a : ℝ) < T) :
    ∃ m : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T,
      ∀ t : Icc (0 : ℝ) T, (t : ℝ) ≤ a → (m t : ℝ) = l (intervalTime t) := by
  let c : ℝ := (T - l a) / (T - a)
  have hc : 0 < c := div_pos (sub_pos.mpr hla) (sub_pos.mpr ha)
  let f : Time → ℝ := fun t => (l (min t a) : ℝ) + c * max ((t : ℝ) - a) 0
  have hfleft (t : Time) (ht : t ≤ a) : f t = l t := by
    have htReal : (t : ℝ) ≤ a := ht
    simp only [f, min_eq_left ht, max_eq_right (sub_nonpos.mpr htReal),
      mul_zero, add_zero]
  have hfright (t : Time) (ht : a ≤ t) : f t = l a + c * ((t : ℝ) - a) := by
    have htReal : (a : ℝ) ≤ t := ht
    simp only [f, min_eq_right ht, max_eq_left (sub_nonneg.mpr htReal)]
  have hfmono : StrictMono f := by
    intro s t hst
    have hstReal : (s : ℝ) < t := hst
    by_cases ht : t ≤ a
    · rw [hfleft s (hst.le.trans ht), hfleft t ht]
      exact l.strictMono hst
    · by_cases hs : s ≤ a
      · rw [hfleft s hs, hfright t (le_of_not_ge ht)]
        have hls : (l s : ℝ) ≤ l a := l.monotone hs
        have hpos := mul_pos hc (sub_pos.mpr (lt_of_not_ge ht))
        exact lt_of_le_of_lt hls (lt_add_of_pos_right _ hpos)
      · rw [hfright s (le_of_not_ge hs), hfright t (le_of_not_ge ht)]
        exact add_lt_add_right (mul_lt_mul_of_pos_left (sub_lt_sub_right hstReal _) hc) _
  have hfzero : f 0 = 0 := by
    rw [hfleft 0 ((zero_le : (0 : Time) ≤ a)), l.map_zero, NNReal.coe_zero]
  let terminal : Time := ⟨T, a.2.trans ha.le⟩
  have hfT : f terminal = T := by
    rw [hfright terminal ha.le]
    change (l a : ℝ) + (T - l a) / (T - a) * (T - a) = T
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt ha))]
    ring
  have hfcont : Continuous f := by
    exact ((continuous_subtype_val.comp
      (l.continuous.comp (continuous_id.min continuous_const))).add
      (continuous_const.mul ((continuous_subtype_val.sub continuous_const).max
        continuous_const)))
  let F : Icc (0 : ℝ) T → Icc (0 : ℝ) T := fun t =>
    ⟨f (intervalTime t), by
      constructor
      · calc
          0 = f 0 := hfzero.symm
          _ ≤ f (intervalTime t) := hfmono.monotone (zero_le : (0 : Time) ≤ _)
      · calc
          f (intervalTime t) ≤ f terminal := hfmono.monotone t.2.2
          _ = T := hfT⟩
  have hFmono : StrictMono F := fun s t hst => hfmono hst
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc
      (show (0 : Time) ≤ terminal from zero_le) hfcont.continuousOn
      (show (y : ℝ) ∈ Icc (f 0) (f terminal) by
        rw [hfzero, hfT]
        exact y.2)
    refine ⟨⟨t, ⟨t.2, ht.2⟩⟩, Subtype.ext ?_⟩
    exact hty
  exact ⟨hFmono.orderIsoOfSurjective F hFsurj, fun t ht => hfleft _ ht⟩

/-- Restricting the time domain preserves the càdlàg conditions at both endpoints. -/
theorem IsCadlag.restrict {T : ℝ} {x : Time → E} (hx : IsCadlag x) :
    Cadlag.IsCadlag T (fun t => x (intervalTime t)) := by
  constructor
  · intro t _
    exact (hx.1 (intervalTime t)).comp
      (continuous_intervalTime T).continuousAt.continuousWithinAt
      (fun _ hs => hs)
  · intro t ht
    obtain ⟨l, hl⟩ := hx.2 (intervalTime t) ht
    refine ⟨l, hl.comp ?_⟩
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨(continuous_intervalTime T).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, self_mem_nhdsWithin⟩

/-- Restriction evaluates the actual half-line path on the closed interval `[0,T]`. -/
def restrict (T : ℝ) (x : D E) : Cadlag.D T E :=
  ⟨fun t => x.1 (intervalTime t), x.2.restrict⟩

/-- Restriction preserves every evaluation, including the terminal value. -/
@[simp] theorem restrict_apply (T : ℝ) (x : D E) (t : Icc (0 : ℝ) T) :
    (restrict T x).1 t = x.1 (intervalTime t) := rfl

/-- Restricting an actual constant path gives the corresponding finite constant path. -/
@[simp] theorem restrict_const (T : ℝ) (a : E) :
    restrict T (const a) = Cadlag.const T a := rfl

/-- Each evaluation of the restricted path is Borel measurable. -/
theorem measurable_eval_restrict [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (t : Icc (0 : ℝ) T) :
    Measurable (fun x : D E => (restrict T x).1 t) :=
  measurable_eval (intervalTime t)

/-- A small stopped discrepancy gives a small finite J1 distance when the limiting
path has small oscillation near the terminal time. -/
theorem skorokhodDist_restrict_lt_of_control {T ε δ : ℝ} (x y : D E)
    (l : LambdaPrime) (U : Time) (hδ : 0 < δ) (hT : 3 * δ < T)
    (hδε : 3 * δ < ε) (hε : ε < 4) (hU : T + δ < U)
    (hshift : ∀ t : Icc (0 : ℝ) T,
      |(l (intervalTime t) : ℝ) - t| < δ)
    (hosc : ∀ s : Time, dist s ⟨T, by linarith⟩ < 3 * δ →
      dist (x.1 s) (x.1 ⟨T, by linarith⟩) < ε / 4)
    (hdisc : discrepancy y x l U < ENNReal.ofReal (ε / 4)) :
    Cadlag.skorokhodDist (restrict T x) (restrict T y) < ε := by
  have hεpos : 0 < ε := lt_trans (by linarith) hδε
  let a : Time := ⟨T - 2 * δ, by linarith⟩
  have haeq : (a : ℝ) = T - 2 * δ := rfl
  let atime : Icc (0 : ℝ) T := ⟨a, ⟨a.2, by rw [haeq]; linarith⟩⟩
  have ha : (a : ℝ) < T := by rw [haeq]; linarith
  have hla : (l a : ℝ) < T := by
    have hs := (abs_lt.mp (hshift atime)).2
    change (l a : ℝ) - a < δ at hs
    linarith only [hs, haeq, hδ]
  obtain ⟨m, hm⟩ := exists_terminal_timeChange l a ha hla
  have hma : (m atime : ℝ) = l a := hm atime le_rfl
  have hlalo : T - 3 * δ < (l a : ℝ) := by
    have hs := (abs_lt.mp (hshift atime)).1
    change -δ < (l a : ℝ) - a at hs
    linarith only [hs, haeq, hδ]
  have htime (t : Icc (0 : ℝ) T) : |(m t : ℝ) - t| < 3 * δ := by
    by_cases ht : (t : ℝ) ≤ a
    · rw [hm t ht]
      exact (hshift t).trans (by linarith)
    · have hmt : (l a : ℝ) ≤ m t := by
        rw [← hma]
        exact m.monotone (le_of_lt (lt_of_not_ge ht))
      apply abs_lt.mpr
      have htlo : T - 2 * δ < (t : ℝ) := lt_of_not_ge ht
      constructor <;> linarith [t.2.2, (m t).2.2]
  have hspace (t : Icc (0 : ℝ) T) :
      ‖(restrict T x).1 (m t) - (restrict T y).1 t‖ < 3 * ε / 4 := by
    have hltU : l (intervalTime t) < U := by
      have hs := (abs_lt.mp (hshift t)).2
      change (l (intervalTime t) : ℝ) < U
      linarith [t.2.2]
    have htU : intervalTime t < U := by
      change (t : ℝ) < U
      linarith [t.2.2]
    have hq : q (y.1 (intervalTime t)) (x.1 (l (intervalTime t))) <
        ENNReal.ofReal (ε / 4) := by
      have hb : q (y.1 (intervalTime t)) (x.1 (l (intervalTime t))) ≤
          discrepancy y x l U := by
        simpa only [discrepancy, min_eq_left htU.le, min_eq_left hltU.le] using
          (le_iSup (fun s : Time => q (y.1 (min s U))
            (x.1 (min (l s) U))) (intervalTime t))
      exact hb.trans_lt hdisc
    have hd : dist (y.1 (intervalTime t)) (x.1 (l (intervalTime t))) < ε / 4 := by
      change min _ 1 < _ at hq
      rcases min_lt_iff.mp hq with hd | hd
      · simpa only [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < ε / 4)]
          using hd
      · have hb : ENNReal.ofReal (ε / 4) < 1 := by
          rw [← ENNReal.ofReal_one]
          exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith)
        exact False.elim ((not_lt_of_ge hb.le) hd)
    by_cases ht : (t : ℝ) ≤ a
    · have he : intervalTime (m t) = l (intervalTime t) := NNReal.eq (hm t ht)
      rw [restrict_apply, restrict_apply, he, ← dist_eq_norm, dist_comm]
      linarith
    · have hmt : (l a : ℝ) ≤ m t := by
        rw [← hma]
        exact m.monotone (le_of_lt (lt_of_not_ge ht))
      have hls : (l a : ℝ) ≤ l (intervalTime t) :=
        l.monotone (le_of_lt (lt_of_not_ge ht))
      have hms : dist (intervalTime (m t)) ⟨T, by linarith⟩ < 3 * δ := by
        change |(m t : ℝ) - T| < 3 * δ
        exact abs_lt.mpr ⟨by linarith, by linarith [(m t).2.2]⟩
      have hls' : dist (l (intervalTime t)) ⟨T, by linarith⟩ < 3 * δ := by
        have hs := (abs_lt.mp (hshift t)).2
        change |(l (intervalTime t) : ℝ) - T| < 3 * δ
        exact abs_lt.mpr ⟨by linarith, by linarith [t.2.2]⟩
      have hmclose := hosc _ hms
      have hlclose := hosc _ hls'
      have htri := dist_triangle (x.1 (intervalTime (m t)))
        (x.1 ⟨T, by linarith⟩) (x.1 (l (intervalTime t)))
      have htri' := dist_triangle (x.1 (intervalTime (m t)))
        (x.1 (l (intervalTime t))) (y.1 (intervalTime t))
      rw [dist_comm (x.1 ⟨T, by linarith⟩)] at htri
      rw [dist_comm (x.1 (l (intervalTime t)))] at htri'
      change ‖x.1 (intervalTime (m t)) - y.1 (intervalTime t)‖ < _
      rw [← dist_eq_norm]
      linarith
  have hbound : max (3 * δ) (3 * ε / 4) ∈
      Cadlag.admissibleBounds (restrict T x) (restrict T y) :=
    ⟨by positivity, m,
      fun t => (htime t).le.trans (le_max_left _ _),
      fun t => (hspace t).le.trans (le_max_right _ _)⟩
  exact (Cadlag.skorokhodDist_le_of_mem hbound).trans_lt
    (max_lt hδε (by linarith))

/-- Restriction to a positive finite horizon is continuous at every path continuous
at its terminal time. -/
theorem continuousAt_restrict {T : ℝ} (hT : 0 < T) {x : D E}
    (hx : ContinuousAt x.1 ⟨T, hT.le⟩) : ContinuousAt (restrict T) x := by
  classical
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro y hy
  have he : Tendsto (fun n => skorohodDistanceExtended (y n) x) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal_zero_iff (fun n =>
      ne_of_lt ((skorohodDistanceExtended_le_one (y n) x).trans_lt
        ENNReal.one_lt_top))).mp (tendsto_iff_dist_tendsto_zero.mp hy)
  have hp (n : ℕ) : ∃ l : Lambda,
      max (gamma l.1) (integratedDiscrepancy (y n) x l.1) <
        skorohodDistanceExtended (y n) x + ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    apply iInf_lt_iff.mp
    exact ENNReal.lt_add_right
      (ne_of_lt ((skorohodDistanceExtended_le_one _ _).trans_lt ENNReal.one_lt_top))
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  choose l hl using hp
  have hr : Tendsto (fun n : ℕ => skorohodDistanceExtended (y n) x +
      ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, add_zero] using
      he.add (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
  have hg : Tendsto (fun n => gamma (l n).1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
      (fun _ => bot_le) (fun n => (le_max_left _ _).trans (hl n).le)
  have hi : Tendsto (fun n => integratedDiscrepancy (y n) x (l n).1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
      (fun _ => bot_le) (fun n => (le_max_right _ _).trans (hl n).le)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (restrict T (y n)) (restrict T x) := by
    simpa only [Function.comp_def, not_eventually, not_lt] using hbad
  obtain ⟨k, hk, hdist⟩ := extraction_of_frequently_atTop hfreq
  let e : ℝ := min ε 1
  have hepos : 0 < e := lt_min hε zero_lt_one
  have heε : e ≤ ε := min_le_left _ _
  have hefour : e < 4 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨ρ, hρ, hosc⟩ := Metric.continuousAt_iff.mp hx (e / 4) (by positivity)
  let δ : ℝ := min T (min ρ e) / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδT : 3 * δ < T := by
    have := min_le_left T (min ρ e)
    dsimp [δ]
    linarith
  have hδρ : 3 * δ < ρ := by
    have := (min_le_right T (min ρ e)).trans (min_le_left ρ e)
    dsimp [δ]
    linarith
  have hδe : 3 * δ < e := by
    have := (min_le_right T (min ρ e)).trans (min_le_right ρ e)
    dsimp [δ]
    linarith
  have hgReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hg
  have hb : Tendsto (fun n => T * (Real.exp (gamma (l n).1).toReal - 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero, Real.exp_zero,
      sub_self, mul_zero] using
      (((Real.continuous_exp.continuousAt.tendsto.comp hgReal).sub_const 1).const_mul T)
  have hshift : ∀ᶠ n in atTop, ∀ t : Icc (0 : ℝ) T,
      |((l n).1 (intervalTime t) : ℝ) - t| < δ := by
    filter_upwards [hb.eventually (gt_mem_nhds hδ)] with n hn t
    have hnonneg : 0 ≤ Real.exp (gamma (l n).1).toReal - 1 := by
      have := Real.add_one_le_exp (gamma (l n).1).toReal
      linarith [ENNReal.toReal_nonneg (a := gamma (l n).1)]
    exact (abs_sub_le_of_gamma (l n).1 (ne_of_lt (l n).2.2)
      (intervalTime t)).trans_lt
      ((mul_le_mul_of_nonneg_right t.2.2 hnonneg).trans_lt hn)
  let f : ℕ → ℝ → ℝ≥0∞ := fun n u => ENNReal.ofReal (Real.exp (-u)) *
    discrepancy (y (k n)) x (l (k n)).1 u.toNNReal
  have hm (n : ℕ) : Measurable (f n) :=
    measurable_integratedDiscrepancy_integrand _ _ _
  have hz : (∫⁻ u : ℝ in Ioi 0, liminf (fun n => f n u) atTop) = 0 := by
    apply le_antisymm _ bot_le
    exact (lintegral_liminf_le hm).trans_eq (hi.comp hk.tendsto_atTop).liminf_eq
  have hae := (lintegral_eq_zero_iff (Measurable.liminf hm)).mp hz
  have htail : volume.restrict (Ioi (0 : ℝ)) (Ioi (T + δ)) ≠ 0 := by
    have hs : Ioi (T + δ) ⊆ Ioi (0 : ℝ) := fun u hu => by
      have : T + δ < u := hu
      change 0 < u
      linarith
    rw [Measure.restrict_apply measurableSet_Ioi, inter_eq_left.mpr hs,
      Real.volume_Ioi]
    exact ENNReal.top_ne_zero
  obtain ⟨u, htu, hu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae htail
    (hae.filter_mono (ae_mono (Measure.restrict_le_self)))
  have htuReal : T + δ < u := htu
  have hU : T + δ < (u.toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ (by linarith : 0 ≤ u)]
    exact htuReal
  have hlower : ENNReal.ofReal (Real.exp (-u)) * ENNReal.ofReal (e / 4) ≤
      liminf (fun n => f n u) atTop := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hk.tendsto_atTop.eventually hshift] with n hn
    apply mul_le_mul_right
    apply le_of_not_gt
    intro hsmall
    have hd := skorokhodDist_restrict_lt_of_control x (y (k n)) (l (k n)).1
      u.toNNReal hδ hδT hδe hefour hU hn
      (fun s hs => hosc (hs.trans hδρ)) hsmall
    have hdist' : ε ≤ Cadlag.skorokhodDist (restrict T x) (restrict T (y (k n))) := by
      simpa only [Cadlag.dist_eq_skorokhodDist, Cadlag.skorokhodDist_comm] using hdist n
    exact (not_lt_of_ge (heε.trans hdist')) hd
  change liminf (fun n => f n u) atTop = 0 at hu
  rw [hu] at hlower
  have hzero := (mul_eq_zero.mp (le_antisymm hlower bot_le)).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity : 0 < e / 4))) hzero

end

end LatticeProb.Cadlag.HalfLine
