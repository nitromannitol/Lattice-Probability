import LatticeProb.LQG.WeylCompositionOuter
import LatticeProb.LQG.LQGMetricMeasurable

/-!
# Annulus crossings and the Weyl scaling of a metric by a weight modified near the origin

Let `D` be a metric on `ℂ` and `0 < r < r'`. A curve that starts outside the disk of radius `r'` and enters the disk of
radius `r` crosses the closed annulus `r ≤ |z| ≤ r'`. If it is parametrized by `D`-length, the crossing takes time at
least the `D`-distance `c` between the two circles, and the weighted time it spends there is at least `e^m c` when
`ξ f ≥ m` on the annulus. Hence two weights `f`, `g` which agree outside the disk of radius `r` give Weyl scalings
(Gwynne-Miller, arXiv:1905.00383, (1.8)) that agree up to the crossing cost:

* `LatticeProb.LQG.exists_norm_crossing_interval`: a curve continuous on `[0, T]` with `|p(0)| ≥ r'` and `|p(t₀)| < r`
  has a parameter interval `[s₀, s₁]` with `|p(s₀)| = r'`, `|p(s₁)| = r` and `r < |p(t)| < r'` for `s₀ < t < s₁`.
* `LatticeProb.LQG.IsEuclideanLengthMetric.continuous_uncurry`: a Euclidean length metric is jointly continuous.
* `LatticeProb.LQG.IsEuclideanLengthMetric.exists_pos_le_of_norm_eq`: the `D`-distance between the circles of radii
  `r < r'` is bounded below by a positive constant.
* `LatticeProb.LQG.min_le_weylScaling_of_eq_of_le_norm`: if `f = g` on `{|z| ≥ r}`, `ξ f ≥ m` on the open annulus and
  `D ≥ c` between the two circles, then `min(e^m c, (e^{ξ g} · D)(x, y)) ≤ (e^{ξ f} · D)(x, y)` for `|x| ≥ r'`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LatticeProb.LQG

/-- A curve continuous on `[0, T]` that starts outside the open disk of radius `r'` and visits the open disk of radius
`r < r'` at a time `t₀ ∈ [0, T]` crosses the annulus: there are `0 ≤ s₀ ≤ s₁ ≤ T` with `|p(s₀)| = r'`, `|p(s₁)| = r`
and `r < |p(t)| < r'` for `s₀ < t < s₁` (`s₁` is the first hitting time of the closed disk of radius `r`, and `s₀` the
last time before `s₁` outside the open disk of radius `r'`). -/
theorem exists_norm_crossing_interval {p : ℝ → ℂ} {T r r' t₀ : ℝ} (hp : ContinuousOn p (Icc 0 T)) (hrr' : r < r')
    (h0 : r' ≤ ‖p 0‖) (ht₀ : t₀ ∈ Icc 0 T) (hlt : ‖p t₀‖ < r) :
    ∃ s₀ s₁, 0 ≤ s₀ ∧ s₀ ≤ s₁ ∧ s₁ ≤ T ∧ ‖p s₀‖ = r' ∧ ‖p s₁‖ = r ∧
      ∀ t ∈ Ioo s₀ s₁, r < ‖p t‖ ∧ ‖p t‖ < r' := by
  set g : ℝ → ℝ := fun t => ‖p t‖ with hg
  have hgc : ContinuousOn g (Icc 0 T) := continuous_norm.comp_continuousOn hp
  have hsub : Icc 0 t₀ ⊆ Icc 0 T := Icc_subset_Icc_right ht₀.2
  -- the first hitting time `s₁` of `{g ≤ r}` in `[0, t₀]`
  set S₁ := Icc 0 t₀ ∩ g ⁻¹' Iic r with hS₁
  have hS₁c : IsClosed S₁ := (hgc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hS₁ne : S₁.Nonempty := ⟨t₀, ⟨ht₀.1, le_rfl⟩, show g t₀ ≤ r from hlt.le⟩
  have hS₁b : BddBelow S₁ := ⟨0, fun t ht => ht.1.1⟩
  set s₁ := sInf S₁ with hs₁def
  have hs₁ : s₁ ∈ S₁ := hS₁c.csInf_mem hS₁ne hS₁b
  have hbefore : ∀ t ∈ Icc 0 t₀, t < s₁ → r < g t := by
    intro t ht hts
    by_contra hle
    push Not at hle
    exact absurd (csInf_le hS₁b ⟨ht, show g t ≤ r from hle⟩) (not_le.2 hts)
  have hs₁T : s₁ ≤ T := hs₁.1.2.trans ht₀.2
  have hgs₁ : g s₁ = r := by
    obtain ⟨c, hc, hgc'⟩ := intermediate_value_Icc' hs₁.1.1 (hgc.mono (Icc_subset_Icc_right hs₁T))
      ⟨show g s₁ ≤ r from hs₁.2, show r ≤ g 0 from (hrr'.trans_le h0).le⟩
    have hcS : c ∈ S₁ := ⟨⟨hc.1, hc.2.trans hs₁.1.2⟩, show g c ≤ r from hgc'.le⟩
    have hcs : c = s₁ := le_antisymm hc.2 (csInf_le hS₁b hcS)
    rw [← hcs]
    exact hgc'
  -- the last time `s₀ ≤ s₁` with `g ≥ r'`
  set S₀ := Icc 0 s₁ ∩ g ⁻¹' Ici r' with hS₀
  have hS₀c : IsClosed S₀ :=
    (hgc.mono (Icc_subset_Icc_right hs₁T)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS₀ne : S₀.Nonempty := ⟨0, ⟨le_rfl, hs₁.1.1⟩, show r' ≤ g 0 from h0⟩
  have hS₀b : BddAbove S₀ := ⟨s₁, fun t ht => ht.1.2⟩
  set s₀ := sSup S₀ with hs₀def
  have hs₀ : s₀ ∈ S₀ := hS₀c.csSup_mem hS₀ne hS₀b
  have hafter : ∀ t ∈ Icc 0 s₁, s₀ < t → g t < r' := by
    intro t ht hts
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hS₀b ⟨ht, show r' ≤ g t from hle⟩) (not_le.2 hts)
  have hgs₀ : g s₀ = r' := by
    obtain ⟨c, hc, hgc'⟩ := intermediate_value_Icc' hs₀.1.2 (hgc.mono (Icc_subset_Icc hs₀.1.1 hs₁T))
      ⟨show g s₁ ≤ r' by rw [hgs₁]; exact hrr'.le, show r' ≤ g s₀ from hs₀.2⟩
    have hcS : c ∈ S₀ := ⟨⟨hs₀.1.1.trans hc.1, hc.2⟩, show r' ≤ g c from hgc'.ge⟩
    have hcs : c = s₀ := le_antisymm (le_csSup hS₀b hcS) hc.1
    rw [← hcs]
    exact hgc'
  refine ⟨s₀, s₁, hs₀.1.1, hs₀.1.2, hs₁T, hgs₀, hgs₁, fun t ht => ⟨?_, ?_⟩⟩
  · exact hbefore t ⟨hs₀.1.1.trans ht.1.le, ht.2.le.trans hs₁.1.2⟩ ht.2
  · exact hafter t ⟨hs₀.1.1.trans ht.1.le, ht.2.le⟩ ht.1

/-- A Euclidean length metric is jointly continuous: `|D(a, b) - D(a₀, b₀)| ≤ D(a, a₀) + D(b, b₀)`. -/
theorem IsEuclideanLengthMetric.continuous_uncurry {D : ℂ → ℂ → ℝ} (h : IsEuclideanLengthMetric D) :
    Continuous fun q : ℂ × ℂ => D q.1 q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a₀, b₀⟩
  have h1 : Tendsto (fun q : ℂ × ℂ => D q.1 a₀) (𝓝 (a₀, b₀)) (𝓝 0) := by
    have := ((h.continuous_left a₀).tendsto a₀).comp (continuous_fst.tendsto (a₀, b₀))
    simpa [Function.comp_def, h.self_eq_zero] using this
  have h2 : Tendsto (fun q : ℂ × ℂ => D q.2 b₀) (𝓝 (a₀, b₀)) (𝓝 0) := by
    have := ((h.continuous_left b₀).tendsto b₀).comp (continuous_snd.tendsto (a₀, b₀))
    simpa [Function.comp_def, h.self_eq_zero] using this
  have hb : ∀ q : ℂ × ℂ, |D q.1 q.2 - D a₀ b₀| ≤ D q.1 a₀ + D q.2 b₀ := by
    intro q
    have t1 := h.triangle q.1 a₀ q.2
    have t2 := h.triangle a₀ b₀ q.2
    have t3 := h.triangle a₀ q.1 b₀
    have t4 := h.triangle q.1 q.2 b₀
    have s1 := h.symm b₀ q.2
    have s2 := h.symm a₀ q.1
    rw [abs_le]
    constructor <;> linarith
  have h12 : Tendsto (fun q : ℂ × ℂ => D q.1 a₀ + D q.2 b₀) (𝓝 (a₀, b₀)) (𝓝 0) := by
    simpa using h1.add h2
  show Tendsto (fun q : ℂ × ℂ => D q.1 q.2) (𝓝 (a₀, b₀)) (𝓝 (D a₀ b₀))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun q => norm_nonneg _) (fun q => by rw [Real.norm_eq_abs]; exact hb q) h12

/-- The `D`-distance between the circles of radii `0 ≤ r < r'` about the origin is bounded below by a positive
constant, for a Euclidean length metric `D` (a positive continuous function on a compact set has a positive minimum). -/
theorem IsEuclideanLengthMetric.exists_pos_le_of_norm_eq {D : ℂ → ℂ → ℝ} (h : IsEuclideanLengthMetric D) {r r' : ℝ}
    (hr : 0 ≤ r) (hrr' : r < r') : ∃ c > 0, ∀ a b : ℂ, ‖a‖ = r → ‖b‖ = r' → c ≤ D a b := by
  have hK : IsCompact (Metric.sphere (0 : ℂ) r ×ˢ Metric.sphere (0 : ℂ) r') :=
    (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hne : (Metric.sphere (0 : ℂ) r ×ˢ Metric.sphere (0 : ℂ) r').Nonempty :=
    ⟨((r : ℂ), (r' : ℂ)), by
      simp only [mem_prod, mem_sphere_zero_iff_norm, Complex.norm_of_nonneg hr,
        Complex.norm_of_nonneg (hr.trans hrr'.le), and_self]⟩
  obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn hne h.continuous_uncurry.continuousOn
  have hq1 : ‖q.1‖ = r := mem_sphere_zero_iff_norm.1 hq.1
  have hq2 : ‖q.2‖ = r' := mem_sphere_zero_iff_norm.1 hq.2
  refine ⟨D q.1 q.2, ?_, fun a b ha hb => isMinOn_iff.1 hmin (a, b)
    ⟨mem_sphere_zero_iff_norm.2 ha, mem_sphere_zero_iff_norm.2 hb⟩⟩
  have hne' : q.1 ≠ q.2 := by
    intro heq
    rw [heq] at hq1
    linarith
  exact lt_of_le_of_ne (h.nonneg' _ _) fun h0 => hne' (h.eq_of_eq_zero _ _ h0.symm)

/-- **Weyl scalings by weights that agree outside a disk.** Let `0 < r < r'` (only `r < r'` is used), let `f = g` on
`{|z| ≥ r}`, let `ξ f ≥ m` on the open annulus `r < |z| < r'`, and let `D(a, b) ≥ c` for `|a| = r`, `|b| = r'`. Then for
`|x| ≥ r'` and every `y`, `min(e^m c, (e^{ξ g} · D)(x, y)) ≤ (e^{ξ f} · D)(x, y)`: a competitor curve from `x` either
stays in `{|z| ≥ r}`, where the two weights agree, or crosses the annulus, which costs at least `e^m c`. -/
theorem min_le_weylScaling_of_eq_of_le_norm {D : ℂ → ℂ → ℝ} {ξ : ℝ} {f g : ℂ → ℝ} {r r' m c : ℝ} (hrr' : r < r')
    (hfg : ∀ z : ℂ, r ≤ ‖z‖ → f z = g z) (hm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < r' → m ≤ ξ * f z)
    (hc : ∀ a b : ℂ, ‖a‖ = r → ‖b‖ = r' → c ≤ D a b) {x : ℂ} (hx : r' ≤ ‖x‖) (y : ℂ) :
    min (ENNReal.ofReal (Real.exp m * c)) (weylScaling D ξ g x y) ≤ weylScaling D ξ f x y := by
  unfold weylScaling
  refine le_iInf₂ fun T p => le_iInf₂ fun hp h0 => le_iInf fun hT => ?_
  by_cases hout : ∀ t ∈ Icc 0 T, r ≤ ‖p t‖
  · refine min_le_of_right_le ?_
    have heq : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) =
        ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
      setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hfg _ (hout t ht)]
    rw [heq]
    exact (iInf₂_le T p).trans ((iInf₂_le hp h0).trans (iInf_le _ hT))
  · push Not at hout
    obtain ⟨t₀, ht₀, hlt⟩ := hout
    refine min_le_of_left_le ?_
    have h0' : r' ≤ ‖p 0‖ := by rw [h0]; exact hx
    obtain ⟨s₀, s₁, hs₀, hs₀₁, hs₁, hn₀, hn₁, hmid⟩ := exists_norm_crossing_interval hp.2.1 hrr' h0' ht₀ hlt
    have hlen : curveLength D p s₀ s₁ = ENNReal.ofReal (s₁ - s₀) := hp.2.2 s₀ s₁ hs₀ hs₀₁ hs₁
    have hcD : ENNReal.ofReal c ≤ ENNReal.ofReal (s₁ - s₀) :=
      (ENNReal.ofReal_le_ofReal (hc _ _ hn₁ hn₀)).trans ((two_point_le_curveLength (D := D) p hs₀₁).trans hlen.le)
    calc ENNReal.ofReal (Real.exp m * c) = ENNReal.ofReal (Real.exp m) * ENNReal.ofReal c :=
          ENNReal.ofReal_mul (Real.exp_pos m).le
      _ ≤ ENNReal.ofReal (Real.exp m) * ENNReal.ofReal (s₁ - s₀) := by gcongr
      _ = ∫⁻ _ in Ioo s₀ s₁, ENNReal.ofReal (Real.exp m) := by
          rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
      _ ≤ ∫⁻ t in Ioo s₀ s₁, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
          setLIntegral_mono' measurableSet_Ioo fun t ht =>
            ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hm _ (hmid t ht).1 (hmid t ht).2))
      _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
          lintegral_mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc hs₀ hs₁))

end LatticeProb.LQG
