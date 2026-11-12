import LatticeProb.LQG.LengthParamNullFiber

/-!
# Truncation of a logarithmic singularity in the Weyl scaling

Let `D` be a Euclidean length metric on `ℂ`, `F : ℂ → ℝ`, and `ξ, α₀ ∈ ℝ`. The weight `F - α₀ log |·|` has a
logarithmic singularity at `0`; truncating it at radius `r > 0` gives the continuous weight
`F - α₀ log max(|·|, r)`, which agrees with the singular one off the closed disc of radius `r`. This file proves that the
Weyl scalings by the truncated weights converge to the Weyl scaling by the singular weight as `r ↓ 0`, at every pair of
points, including pairs with `0` as an endpoint:

* `ξ α₀ ≤ 0`: the truncated weights decrease to the singular one away from `0`, and
  `inf_k e^{ξ(F - α₀ log max(|·|, r_k))} · D = e^{ξ(F - α₀ log |·|)} · D` for continuous `F`, by monotone convergence
  along each length-parametrized curve (`IsEuclideanLengthMetric.iInf_weylScaling_logCutoff_of_nonpos`);
* `ξ α₀ ≥ 0`: the truncated weights increase to the singular one away from `0`, and the supremum is the singular Weyl
  scaling whenever the latter is continuous at `0` in its first variable
  (`IsEuclideanLengthMetric.iSup_weylScaling_logCutoff_of_nonneg`). The proof cuts a near-optimal curve for the
  truncated weight at its first entrance and last exit of the closed disc of radius `r_k`
  (`IsEuclideanLengthMetric.weylScaling_le_add_of_eq_off_closedBall`).

Both cases give `IsEuclideanLengthMetric.tendsto_weylScaling_logCutoff`. The value of the weights at the single point
`0` is irrelevant because a length-parametrized curve spends zero time at a point
(`IsEuclideanLengthMetric.weylScaling_mono_of_forall_ne`).
-/

namespace LatticeProb.LQG

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- Monotonicity of the Weyl scaling in the weight, when the weights are compared away from a single point. -/
theorem IsEuclideanLengthMetric.weylScaling_mono_of_forall_ne {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {f f' : ℂ → ℝ} (z₀ : ℂ) (h : ∀ z, z ≠ z₀ → ξ * f z ≤ ξ * f' z) (u v : ℂ) :
    weylScaling D ξ f u v ≤ weylScaling D ξ f' u v := by
  unfold weylScaling
  refine iInf_mono fun T => iInf_mono fun p => iInf_mono fun hp => iInf_mono fun _ => iInf_mono fun _ => ?_
  refine lintegral_mono_ae ?_
  filter_upwards [hD.ae_ne_of_lengthParametrized hp z₀] with t ht
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (h _ ht))

/-- The Weyl distance between two points of a length-parametrized curve is at most the weighted time the curve spends
between them. -/
theorem IsEuclideanLengthMetric.weylScaling_le_lintegral_subarc {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (ξ : ℝ) (f : ℂ → ℝ) {p : ℝ → ℂ} {T a b : ℝ}
    (hp : IsLengthParametrized D p T) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    weylScaling D ξ f (p a) (p b) ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  have hsub := hD.isLengthParametrized_subcurve hp ha hab hb
  have h0 : (fun t => p (a + t)) 0 = p a := by simp
  have hT : (fun t => p (a + t)) (b - a) = p b := by simp
  refine (iInf₂_le (b - a) (fun t => p (a + t))).trans ((iInf₂_le hsub h0).trans
    ((iInf_le _ hT).trans (le_of_eq ?_)))
  have htr := lintegral_Icc_translate (fun t => ENNReal.ofReal (Real.exp (ξ * f (p (a + t))))) a (b - a)
  rw [show a + (b - a) = b by ring] at htr
  simp only [show ∀ t : ℝ, a + (t - a) = t from fun t => by ring] at htr
  exact htr.symm

/-- Cutting at a small closed disc. Let the weights `f` and `f'` agree outside the closed disc of radius `ρ` about `0`,
and let `e^{ξ f'} · D (u, v)` be finite. Then for every `δ > 0` there are points `x, y` of that disc with
`e^{ξ f} · D (u, v) ≤ e^{ξ f'} · D (u, v) + δ + (e^{ξ f} · D (x, 0) + e^{ξ f} · D (0, y))`. A `δ`-optimal curve for `f'`
either avoids the disc, so that its costs for `f` and `f'` agree, or it is cut at its first entrance `x` and its last
exit `y` of the disc, and the two outer pieces see equal weights. -/
theorem IsEuclideanLengthMetric.weylScaling_le_add_of_eq_off_closedBall {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f f' : ℂ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hff' : ∀ z : ℂ, ρ < ‖z‖ → f' z = f z) {u v : ℂ} {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hfin : weylScaling D ξ f' u v ≠ ⊤) :
    ∃ x y : ℂ, ‖x‖ ≤ ρ ∧ ‖y‖ ≤ ρ ∧
      weylScaling D ξ f u v ≤
        weylScaling D ξ f' u v + δ + (weylScaling D ξ f x 0 + weylScaling D ξ f 0 y) := by
  obtain ⟨T, p, hp, h0, hT, hcost⟩ : ∃ T : ℝ, ∃ p : ℝ → ℂ, IsLengthParametrized D p T ∧ p 0 = u ∧ p T = v ∧
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f' (p t))) < weylScaling D ξ f' u v + δ := by
    have h := ENNReal.lt_add_right hfin hδ
    generalize weylScaling D ξ f' u v + δ = c at h
    unfold weylScaling at h
    simpa only [iInf_lt_iff, exists_prop] using h
  have hW : ∀ t : ℝ, ρ < ‖p t‖ →
      ENNReal.ofReal (Real.exp (ξ * f' (p t))) = ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
    intro t ht
    rw [hff' _ ht]
  set S : Set ℝ := Icc 0 T ∩ p ⁻¹' {z | ‖z‖ ≤ ρ} with hS
  have hSc : IsClosed S :=
    hp.2.1.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_le continuous_norm continuous_const)
  have hSk : IsCompact S := isCompact_Icc.of_isClosed_subset hSc inter_subset_left
  by_cases hne : S.Nonempty
  · obtain ⟨s, hs⟩ := hSk.exists_isLeast hne
    obtain ⟨s', hs'⟩ := hSk.exists_isGreatest hne
    have hss' : s ≤ s' := hs.2 hs'.1
    have hs0 : 0 ≤ s := hs.1.1.1
    have hs'T : s' ≤ T := hs'.1.1.2
    have hsT : s ≤ T := hss'.trans hs'T
    have hs'0 : 0 ≤ s' := hs0.trans hss'
    refine ⟨p s, p s', hs.1.2, hs'.1.2, ?_⟩
    have hleft : EqOn (fun t => ENNReal.ofReal (Real.exp (ξ * f' (p t))))
        (fun t => ENNReal.ofReal (Real.exp (ξ * f (p t)))) (Ico 0 s) := by
      intro t ht
      refine hW t (lt_of_not_ge fun hle => ?_)
      exact absurd (hs.2 ⟨⟨ht.1, ht.2.le.trans hsT⟩, hle⟩) (not_le.mpr ht.2)
    have hright : EqOn (fun t => ENNReal.ofReal (Real.exp (ξ * f' (p t))))
        (fun t => ENNReal.ofReal (Real.exp (ξ * f (p t)))) (Ioc s' T) := by
      intro t ht
      refine hW t (lt_of_not_ge fun hle => ?_)
      exact absurd (hs'.2 ⟨⟨hs'0.trans ht.1.le, ht.2⟩, hle⟩) (not_le.mpr ht.1)
    have hdisj : Disjoint (Ico 0 s) (Ioc s' T) := by
      rw [disjoint_left]
      intro t ht ht'
      linarith [ht.2, ht'.1]
    have hsub : Ico 0 s ∪ Ioc s' T ⊆ Icc 0 T := by
      rintro t (ht | ht)
      · exact ⟨ht.1, ht.2.le.trans hsT⟩
      · exact ⟨hs'0.trans ht.1.le, ht.2⟩
    have hsplit : weylScaling D ξ f u (p s) + weylScaling D ξ f (p s') v ≤
        ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f' (p t))) := by
      have h1 : weylScaling D ξ f u (p s) ≤ ∫⁻ t in Icc 0 s, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
        rw [← h0]; exact hD.weylScaling_le_lintegral_subarc ξ f hp le_rfl hs0 hsT
      have h2 : weylScaling D ξ f (p s') v ≤ ∫⁻ t in Icc s' T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
        rw [← hT]; exact hD.weylScaling_le_lintegral_subarc ξ f hp hs'0 hs'T le_rfl
      calc weylScaling D ξ f u (p s) + weylScaling D ξ f (p s') v
          ≤ (∫⁻ t in Icc 0 s, ENNReal.ofReal (Real.exp (ξ * f (p t)))) +
              ∫⁻ t in Icc s' T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := add_le_add h1 h2
        _ = (∫⁻ t in Ico 0 s, ENNReal.ofReal (Real.exp (ξ * f' (p t)))) +
              ∫⁻ t in Ioc s' T, ENNReal.ofReal (Real.exp (ξ * f' (p t))) := by
            rw [setLIntegral_congr_fun measurableSet_Ico hleft,
              setLIntegral_congr_fun measurableSet_Ioc hright, setLIntegral_congr Ico_ae_eq_Icc,
              setLIntegral_congr Ioc_ae_eq_Icc]
        _ = ∫⁻ t in Ico 0 s ∪ Ioc s' T, ENNReal.ofReal (Real.exp (ξ * f' (p t))) :=
            (lintegral_union measurableSet_Ioc hdisj).symm
        _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f' (p t))) := lintegral_mono_set hsub
    calc weylScaling D ξ f u v
        ≤ weylScaling D ξ f u (p s) + weylScaling D ξ f (p s) v := hD.weylScaling_triangle ξ f u (p s) v
      _ ≤ weylScaling D ξ f u (p s) + ((weylScaling D ξ f (p s) 0 + weylScaling D ξ f 0 (p s')) +
            weylScaling D ξ f (p s') v) := by
          refine add_le_add le_rfl ((hD.weylScaling_triangle ξ f _ (p s') v).trans (add_le_add ?_ le_rfl))
          exact hD.weylScaling_triangle ξ f _ 0 _
      _ = (weylScaling D ξ f u (p s) + weylScaling D ξ f (p s') v) +
            (weylScaling D ξ f (p s) 0 + weylScaling D ξ f 0 (p s')) := by ring
      _ ≤ weylScaling D ξ f' u v + δ + (weylScaling D ξ f (p s) 0 + weylScaling D ξ f 0 (p s')) :=
          add_le_add (hsplit.trans hcost.le) le_rfl
  · refine ⟨0, 0, by simpa using hρ, by simpa using hρ, ?_⟩
    have hall : EqOn (fun t => ENNReal.ofReal (Real.exp (ξ * f' (p t))))
        (fun t => ENNReal.ofReal (Real.exp (ξ * f (p t)))) (Icc 0 T) := by
      intro t ht
      exact hW t (lt_of_not_ge fun hle => hne ⟨t, ht, hle⟩)
    have h1 := hD.weylScaling_le_lintegral_subarc ξ f hp le_rfl hp.1 le_rfl
    rw [h0, hT, ← setLIntegral_congr_fun measurableSet_Icc hall] at h1
    exact (h1.trans hcost.le).trans le_self_add

/-- The truncated logarithm `z ↦ log max(|z|, r)` is continuous for `r > 0`. -/
theorem continuous_log_max_norm {r : ℝ} (hr : 0 < r) : Continuous fun z : ℂ => Real.log (max ‖z‖ r) :=
  (continuous_norm.max continuous_const).log fun _ => (lt_of_lt_of_le hr (le_max_right _ _)).ne'

/-- Case `ξ α₀ ≤ 0`: for continuous `F` and radii `r_k > 0` decreasing to `0`, the Weyl scalings by the truncated weights
`F - α₀ log max(|·|, r_k)` decrease to the Weyl scaling by the singular weight `F - α₀ log |·|`, at every pair of
points: the infimum over `k` is the singular Weyl scaling. -/
theorem IsEuclideanLengthMetric.iInf_weylScaling_logCutoff_of_nonpos {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ α₀ : ℝ} (ha : ξ * α₀ ≤ 0) {F : ℂ → ℝ} (hF : Continuous F)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hr : Antitone r) (hlim : Tendsto r atTop (𝓝 0)) (u v : ℂ) :
    ⨅ k, weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r k))) u v =
      weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) u v := by
  have hexp_le : ∀ k (z : ℂ), z ≠ 0 →
      ξ * (F z + -α₀ * Real.log ‖z‖) ≤ ξ * (F z + -α₀ * Real.log (max ‖z‖ (r k))) := by
    intro k z hz
    have hL : Real.log ‖z‖ ≤ Real.log (max ‖z‖ (r k)) :=
      Real.log_le_log (norm_pos_iff.mpr hz) (le_max_left _ _)
    nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sub_nonneg.mpr hL)]
  have hexp_anti : ∀ (z : ℂ) (k k' : ℕ), k ≤ k' →
      ξ * (F z + -α₀ * Real.log (max ‖z‖ (r k'))) ≤ ξ * (F z + -α₀ * Real.log (max ‖z‖ (r k))) := by
    intro z k k' hkk'
    have hL : Real.log (max ‖z‖ (r k')) ≤ Real.log (max ‖z‖ (r k)) :=
      Real.log_le_log (lt_of_lt_of_le (hr0 k') (le_max_right _ _)) (max_le_max le_rfl (hr hkk'))
    nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sub_nonneg.mpr hL)]
  have hpt : ∀ z : ℂ, z ≠ 0 →
      ⨅ k, ENNReal.ofReal (Real.exp (ξ * (F z + -α₀ * Real.log (max ‖z‖ (r k))))) =
        ENNReal.ofReal (Real.exp (ξ * (F z + -α₀ * Real.log ‖z‖))) := by
    intro z hz
    obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds (norm_pos_iff.mpr hz))).exists
    refine le_antisymm (iInf_le_of_le K (by rw [max_eq_left hK.le])) (le_iInf fun k => ?_)
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hexp_le k z hz))
  refine le_antisymm ?_ (le_iInf fun k => hD.weylScaling_mono_of_forall_ne 0 (fun z hz => hexp_le k z hz) u v)
  simp only [weylScaling]
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
  refine (iInf_mono fun k => (iInf₂_le T p).trans ((iInf₂_le hp h0).trans (iInf_le _ hT))).trans ?_
  have hc : ∀ k, Continuous fun z : ℂ => Real.exp (ξ * (F z + -α₀ * Real.log (max ‖z‖ (r k)))) := fun k =>
    Real.continuous_exp.comp (continuous_const.mul (hF.add (continuous_const.mul (continuous_log_max_norm (hr0 k)))))
  have hmeas : ∀ k, AEMeasurable
      (fun t => ENNReal.ofReal (Real.exp (ξ * (F (p t) + -α₀ * Real.log (max ‖p t‖ (r k))))))
      (volume.restrict (Icc 0 T)) := fun k =>
    ((ENNReal.continuous_ofReal.comp (hc k)).comp_continuousOn hp.2.1).aemeasurable measurableSet_Icc
  have hanti : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), Antitone fun k =>
      ENNReal.ofReal (Real.exp (ξ * (F (p t) + -α₀ * Real.log (max ‖p t‖ (r k))))) :=
    Eventually.of_forall fun t k k' hkk' =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hexp_anti (p t) k k' hkk'))
  have hfin : ∫⁻ t in Icc 0 T,
      ENNReal.ofReal (Real.exp (ξ * (F (p t) + -α₀ * Real.log (max ‖p t‖ (r 0))))) ≠ ⊤ :=
    (Integrable.lintegral_lt_top (((hc 0).comp_continuousOn hp.2.1).integrableOn_compact isCompact_Icc)).ne
  rw [← lintegral_iInf' hmeas hanti hfin]
  refine (lintegral_congr_ae ?_).le
  filter_upwards [hD.ae_ne_of_lengthParametrized hp 0] with t ht
  exact hpt (p t) ht

/-- Case `ξ α₀ ≥ 0`: for radii `r_k > 0` tending to `0`, the Weyl scalings by the truncated weights
`F - α₀ log max(|·|, r_k)` are bounded by the Weyl scaling by the singular weight `F - α₀ log |·|`, and their supremum is
the singular Weyl scaling at every pair of points, provided the singular Weyl scaling `x ↦ e^{ξ(F - α₀ log |·|)} · D (x, 0)`
tends to `0` as `x → 0`. No regularity of `F` is needed. -/
theorem IsEuclideanLengthMetric.iSup_weylScaling_logCutoff_of_nonneg {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ α₀ : ℝ} (ha : 0 ≤ ξ * α₀) (F : ℂ → ℝ)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hlim : Tendsto r atTop (𝓝 0))
    (hcont : Tendsto (fun x => weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) x 0) (𝓝 0) (𝓝 0))
    (u v : ℂ) :
    ⨆ k, weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r k))) u v =
      weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) u v := by
  refine le_antisymm (iSup_le fun k => hD.weylScaling_mono_of_forall_ne 0 (fun z hz => ?_) u v) ?_
  · have hL : Real.log ‖z‖ ≤ Real.log (max ‖z‖ (r k)) :=
      Real.log_le_log (norm_pos_iff.mpr hz) (le_max_left _ _)
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hL)]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
  have hδ : 0 < (ε : ℝ≥0∞) / 3 := ENNReal.div_pos (ENNReal.coe_ne_zero.mpr hε.ne') (by norm_num)
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ x : ℂ, ‖x‖ < ρ →
      weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) x 0 < (ε : ℝ≥0∞) / 3 := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (hcont (Iio_mem_nhds hδ))
    exact ⟨ρ, hρ, fun x hx => hsub (mem_ball_zero_iff.mpr hx)⟩
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hρ)).exists
  have hfin : weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r k))) u v ≠ ⊤ :=
    ne_top_of_le_ne_top hlt.ne
      (le_iSup (fun j => weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r j))) u v) k)
  obtain ⟨x, y, hx, hy, hle⟩ := hD.weylScaling_le_add_of_eq_off_closedBall (hr0 k).le
    (f := fun z => F z + -α₀ * Real.log ‖z‖) (f' := fun z => F z + -α₀ * Real.log (max ‖z‖ (r k)))
    (fun z hz => by simp only [max_eq_left hz.le]) hδ.ne' hfin
  have hx' := hball x (hx.trans_lt hk)
  have hy' : weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) 0 y < (ε : ℝ≥0∞) / 3 := by
    rw [hD.weylScaling_symm]; exact hball y (hy.trans_lt hk)
  calc weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) u v
      ≤ _ := hle
    _ ≤ (⨆ j, weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r j))) u v) + (ε : ℝ≥0∞) / 3 +
          ((ε : ℝ≥0∞) / 3 + (ε : ℝ≥0∞) / 3) :=
        add_le_add (add_le_add (le_iSup
          (fun j => weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r j))) u v) k) le_rfl)
          (add_le_add hx'.le hy'.le)
    _ = (⨆ j, weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r j))) u v) + ε := by
        rw [add_assoc, ← add_assoc ((ε : ℝ≥0∞) / 3), ENNReal.add_thirds]

/-- Truncation limit of the singular Weyl scaling. For continuous `F` and radii `r_k > 0` decreasing to `0`, the Weyl
scalings by the truncated weights `F - α₀ log max(|·|, r_k)` converge to the Weyl scaling by the singular weight
`F - α₀ log |·|` at every pair of points, provided the singular Weyl scaling `x ↦ e^{ξ(F - α₀ log |·|)} · D (x, 0)` tends
to `0` as `x → 0`. The convergence is monotone: decreasing if `ξ α₀ ≤ 0`, increasing if `ξ α₀ ≥ 0`. -/
theorem IsEuclideanLengthMetric.tendsto_weylScaling_logCutoff {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (ξ α₀ : ℝ) {F : ℂ → ℝ} (hF : Continuous F)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hr : Antitone r) (hlim : Tendsto r atTop (𝓝 0))
    (hcont : Tendsto (fun x => weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) x 0) (𝓝 0) (𝓝 0))
    (u v : ℂ) :
    Tendsto (fun k => weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r k))) u v) atTop
      (𝓝 (weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) u v)) := by
  have hL : ∀ (z : ℂ) (k k' : ℕ), k ≤ k' → Real.log (max ‖z‖ (r k')) ≤ Real.log (max ‖z‖ (r k)) :=
    fun z k k' hkk' =>
      Real.log_le_log (lt_of_lt_of_le (hr0 k') (le_max_right _ _)) (max_le_max le_rfl (hr hkk'))
  rcases le_total (ξ * α₀) 0 with ha | ha
  · rw [← hD.iInf_weylScaling_logCutoff_of_nonpos ha hF hr0 hr hlim u v]
    refine tendsto_atTop_iInf fun k k' hkk' => hD.weylScaling_mono_of_forall_ne 0 (fun z _ => ?_) u v
    nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sub_nonneg.mpr (hL z k k' hkk'))]
  · rw [← hD.iSup_weylScaling_logCutoff_of_nonneg ha F hr0 hlim hcont u v]
    refine tendsto_atTop_iSup fun k k' hkk' => hD.weylScaling_mono_of_forall_ne 0 (fun z _ => ?_) u v
    nlinarith [mul_nonneg ha (sub_nonneg.mpr (hL z k k' hkk'))]

end LatticeProb.LQG
