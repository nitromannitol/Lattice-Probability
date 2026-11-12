/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eL413 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eFin2

/-!
# GM Lemma 4.13′, metric step (l. 2077–2080)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.13
(`lem-geo-disconnect`), l. 2077–2080: `X₀ ⊆ ℂ ∖ 𝓑^•_s` connected of Euclidean diameter
`≤ (ε+δ)𝕣` with `cl X₀ ∩ ∂𝓑^•_s ≠ ∅`, `t` a time after `s` with `P(t) ∈ X₀`.

* `p412e_time_le` ("since `P` is a `D_h`-geodesic, `P(t) ∈ X₀` and `Cl'(X₀)` contains a point
  of `∂𝓑^•_s`, `t − s ≤ D_h`-diameter of `X₀`").
* `p412e_dist_le_of_regC3` (upper bound of condition 3: the `D_h`-diameter of `X₀` is at most
  `(ε+δ)^χ 𝔠_𝕣e^{ξh_𝕣(0)}`).
* `p412e_geod_eucl` (lower bound of condition 3: the Euclidean diameter of `P([s,t])` is at most
  `((t−s)/𝔠_𝕣e^{ξh_𝕣(0)})^{1/χ'}𝕣`). Condition 3 only compares points with `|z − w| ≤ a𝕣`;
  GM use it on `P([s,t])` without comment. We add the smallness `(t−s)/𝔠_𝕣e^{ξh_𝕣(0)} < a^{χ'}`
  and a first-exit (intermediate value) argument (own elementary step, DV-L413-exit proposed).
* `p412e_L413_metric`: the combination, `|P(u) − P(s)| ≤ (d/𝕣)^{χ/χ'}𝕣` on `[s, t]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open LQGMetric.MetricGeometry LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

/-- GM l. 2078: `t − s ≤ sup_{X₀} D(q, ·)` for a geodesic `P` from `𝕫`, `D(𝕫, q) ≤ s`,
`q ∈ cl X₀`, `P(t) ∈ X₀` -/
theorem p412e_time_le {D : ContMetric} {P : ℝ → ℂ} {L : ℝ} {𝕫 y : ℂ} (hP : IsGeodesicL D P L 𝕫 y)
    {s t : ℝ} (ht : t ∈ Icc 0 L) {q : ℂ} (hq : D.1 (𝕫, q) ≤ s) {X₀ : Set ℂ} (hqX : q ∈ closure X₀)
    (htX : P t ∈ X₀) {M : ℝ} (hM : ∀ w ∈ X₀, ∀ w' ∈ X₀, D.1 (w, w') ≤ M) : t - s ≤ M := by
  obtain ⟨-, hP0, -, hPd⟩ := hP
  have h1 : D.1 (𝕫, P t) = t := by
    have := hPd 0 ⟨le_rfl, ht.1.trans ht.2⟩ t ht
    rw [hP0, sub_zero, abs_of_nonneg ht.1] at this; exact this
  have hc : Continuous fun w => D.1 (w, P t) :=
    D.1.continuous.comp (continuous_id.prodMk continuous_const)
  have h2 : D.1 (q, P t) ≤ M := by
    have : closure X₀ ⊆ (fun w => D.1 (w, P t)) ⁻¹' Iic M :=
      closure_minimal (fun w hw => hM w hw _ htX) (isClosed_Iic.preimage hc)
    exact this hqX
  have h3 := D.2.triangle 𝕫 q (P t)
  linarith

/-- GM l. 2077: the upper bound of condition 3 gives `D(w, w') ≤ 𝔠_𝕣e^{ξh_𝕣(0)} (d/𝕣)^χ` for
`w, w' ∈ B_{4ℓ𝕣}(𝕣V)` with `|w − w'| ≤ d ≤ a𝕣` -/
theorem p412e_dist_le_of_regC3 {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (hχ : 0 < R.χ) {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a)
    (hs : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {w w' : ℂ} (hw : w ∈ regRegion R 𝕣)
    (hw' : w' ∈ regRegion R 𝕣) {d : ℝ} (hd : ‖w - w'‖ ≤ d) (hda : d ≤ a * 𝕣) :
    (D (h ω)).1 (w, w') ≤ scaleFac R.ξ R.c (h ω) 𝕣 0 * (d / 𝕣) ^ R.χ := by
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  by_cases hne : w = w'
  · subst hne; rw [(D (h ω)).2.self_eq_zero]; positivity
  have h3 := (hω w hw w' hw' (hd.trans hda)).2 hne
  have hle : (D (h ω)).1 (w, w') ≤ S * ‖(w - w') / (𝕣 : ℂ)‖ ^ R.χ := by
    have h4 : ENNReal.ofReal ((D (h ω)).1 (w, w')) ≤ (D (h ω)).internal (ball w (2 * ‖w - w'‖)) w w' := by
      have := edist_le_internalEDist ((D (h ω)).pt '' ball w (2 * ‖w - w'‖)) ((D (h ω)).pt w)
        ((D (h ω)).pt w')
      rw [edist_dist] at this; exact this
    have hone : ENNReal.ofReal S * ENNReal.ofReal S⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one]
    have h5 : ENNReal.ofReal ((D (h ω)).1 (w, w')) ≤
        ENNReal.ofReal (S * ‖(w - w') / (𝕣 : ℂ)‖ ^ R.χ) := by
      calc ENNReal.ofReal ((D (h ω)).1 (w, w'))
          ≤ ENNReal.ofReal S * (ENNReal.ofReal S⁻¹ *
              (D (h ω)).internal (ball w (2 * ‖w - w'‖)) w w') := by
            rw [← mul_assoc, hone, one_mul]; exact h4
        _ ≤ ENNReal.ofReal S * ENNReal.ofReal (‖(w - w') / (𝕣 : ℂ)‖ ^ R.χ) := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul hs.le]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h5
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ hs.le)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣]
  exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hd h𝕣.le) hχ.le

/-- GM l. 2079 (lower bound of condition 3, with a first-exit argument): a unit-speed
`D_h`-geodesic stays within `((t−s)/𝔠_𝕣e^{ξh_𝕣(0)})^{1/χ'}𝕣` of `P(s)` on `[s, t]`, if
`P([s,t]) ⊆ B_{4ℓ𝕣}(𝕣V)` and `(t−s)/𝔠_𝕣e^{ξh_𝕣(0)} < a^{χ'}` -/
theorem p412e_geod_eucl {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (ha : 0 < a) (hχ' : 0 < R.χ') {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a)
    (hs : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {P : ℝ → ℂ} {L : ℝ} {𝕫 y : ℂ}
    (hP : IsGeodesicL (D (h ω)) P L 𝕫 y) (hPc : ContinuousOn P (Icc 0 L)) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htL : t ≤ L) (hreg : ∀ u ∈ Icc s t, P u ∈ regRegion R 𝕣)
    (hsmall : (t - s) / scaleFac R.ξ R.c (h ω) 𝕣 0 < a ^ R.χ') :
    ∀ u ∈ Icc s t, ‖P u - P s‖ ≤ ((t - s) / scaleFac R.ξ R.c (h ω) 𝕣 0) ^ (1 / R.χ') * 𝕣 := by
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0
  obtain ⟨-, -, -, hPd⟩ := hP
  have hIcc : ∀ u ∈ Icc s t, u ∈ Icc 0 L := fun u hu => ⟨hs0.trans hu.1, hu.2.trans htL⟩
  have hsI : s ∈ Icc s t := ⟨le_rfl, hst⟩
  -- the lower Hölder bound along `P`
  have hlow : ∀ u ∈ Icc s t, ‖P u - P s‖ ≤ a * 𝕣 → (‖P u - P s‖ / 𝕣) ^ R.χ' ≤ (t - s) / S := by
    intro u hu hle
    have h3 := (hω (P u) (hreg u hu) (P s) (hreg s hsI) hle).1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣,
      hPd u (hIcc u hu) s (hIcc s hsI), abs_of_nonpos (by linarith [hu.1])] at h3
    calc (‖P u - P s‖ / 𝕣) ^ R.χ' ≤ S⁻¹ * -(s - u) := h3
      _ = (u - s) / S := by rw [div_eq_inv_mul]; ring
      _ ≤ (t - s) / S := div_le_div_of_nonneg_right (by linarith [hu.2]) hs.le
  -- first exit: `P` never reaches Euclidean distance `a𝕣` from `P(s)`
  have hin : ∀ u ∈ Icc s t, ‖P u - P s‖ < a * 𝕣 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨u, hu, hu'⟩ := hcon
    have hf : ContinuousOn (fun v => ‖P v - P s‖) (Icc s u) :=
      ((hPc.mono fun v hv => hIcc v ⟨hv.1, hv.2.trans hu.2⟩).sub continuousOn_const).norm
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hu.1 hf
      ⟨by simp only [sub_self, norm_zero]; positivity, hu'⟩
    have hvI : v ∈ Icc s t := ⟨hv.1, hv.2.trans hu.2⟩
    have hfv' : ‖P v - P s‖ = a * 𝕣 := hfv
    have := hlow v hvI (le_of_eq hfv')
    rw [hfv', mul_div_cancel_right₀ _ h𝕣.ne'] at this
    linarith
  intro u hu
  have h1 := hlow u hu (hin u hu).le
  have h0 : 0 ≤ ‖P u - P s‖ / 𝕣 := by positivity
  have hq : 0 ≤ (t - s) / S := div_nonneg (by linarith) hs.le
  have h2 : ‖P u - P s‖ / 𝕣 ≤ ((t - s) / S) ^ (1 / R.χ') := by
    have := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 1 / R.χ')
    rwa [← Real.rpow_mul h0, mul_one_div_cancel hχ'.ne', Real.rpow_one] at this
  rwa [div_le_iff₀ h𝕣] at h2

end LQGMetric.GM
