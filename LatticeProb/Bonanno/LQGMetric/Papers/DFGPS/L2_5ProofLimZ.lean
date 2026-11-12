/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofLimZ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofLimDet
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofLimPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 A: the local midpoint condition for `𝔞_ε⁻¹ D_h^ε` and its closedness

For a continuous field `h*_ε`, `𝔞_ε⁻¹ D_h^ε` (as `lfppC`) is a continuous symmetric pseudo-metric
with `ε`-midpoints (DFGPS T:1005–1012 use that `D_h^ε` is a length metric), and by the first-hit
cut at `∂S_s(0)` (as `iInf_frontier_lfppDOn_le`, `L2_10ProofCut.lean`, for endpoints outside the
square) it satisfies the local midpoint condition `zSetC s`. The set `zSetC s` is closed in
`C(ℂ × ℂ, ℝ)` (it only depends on the restriction to `S_s(0)²`, a compact metric setting).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- **first-hit cut, endpoint outside**: for `u ∈ int K` and `v ∉ int K` (`K` closed),
`inf_{w ∈ ∂K} D(u, w; K) ≤ D(u, v)` (the proof of `iInf_frontier_lfppDOn_le`, with the hitting
time of `∂K` from the connectedness of the path) -/
theorem iInf_frontier_lfppDOn_le' {ξ ε : ℝ} {x : DistC} {K : Set ℂ} (hK : IsClosed K) {u v : ℂ}
    (hu : u ∈ interior K) (hv : v ∉ interior K) :
    ⨅ w ∈ frontier K, lfppDOn ξ (heatMollify ε x) K u w ≤ lfppDistE ξ ε x u v := by
  by_cases hvf : v ∈ frontier K
  · exact iInf_frontier_lfppDOn_le hK hu hvf
  have hvK : v ∉ K := fun h => hvf ⟨subset_closure h, hv⟩
  refine le_iInf fun Q => ?_
  obtain ⟨P, hP⟩ := Q
  simp only
  set T : Set ℝ := Icc 0 1 ∩ P ⁻¹' frontier K
  have hTc : IsClosed T := hP.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
    isClosed_frontier
  obtain ⟨_, ⟨t1, ht1, rfl⟩, ht1f⟩ := cut_inter_frontier_nonempty hK
    (isPreconnected_Icc.image P hP.continuousOn) ⟨1, ⟨zero_le_one, le_rfl⟩, hP.target⟩ hvK
    ⟨0, ⟨le_rfl, zero_le_one⟩, hP.source⟩ (interior_subset hu)
  have h1T : t1 ∈ T := ⟨ht1, ht1f⟩
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set t0 := sInf T
  have ht0T : t0 ∈ T := hTc.csInf_mem ⟨t1, h1T⟩ hTb
  have hu' : u ∉ frontier K := fun h => h.2 hu
  have ht0pos : 0 < t0 := by
    rcases ht0T.1.1.eq_or_lt with h | h
    · exfalso; have := ht0T.2; rw [← h] at this; exact hu' (by simpa [hP.source] using this)
    · exact h
  have hin : ∀ t ∈ Icc (0 : ℝ) t0, P t ∈ K := by
    intro t ht
    by_contra hPt
    have htt0 : t < t0 := by
      rcases ht.2.lt_or_eq with h | h
      · exact h
      · exfalso; rw [h] at hPt
        exact hPt (hK.closure_subset ht0T.2.1)
    have hcon : IsPreconnected (P '' Icc 0 t) :=
      isPreconnected_Icc.image P (hP.continuousOn.mono (Icc_subset_Icc le_rfl
        (htt0.le.trans ht0T.1.2)))
    obtain ⟨y, ⟨t', ht', rfl⟩, hy⟩ := cut_inter_frontier_nonempty hK hcon
      ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩ hPt ⟨0, ⟨le_rfl, ht.1⟩, rfl⟩
      (by rw [hP.source]; exact interior_subset hu)
    have : t0 ≤ t' := csInf_le hTb ⟨⟨ht'.1, ht'.2.trans (htt0.le.trans ht0T.1.2)⟩, hy⟩
    linarith [ht'.2]
  have hsub := isPiecewiseC1Path_subPath hP le_rfl ht0pos ht0T.1.2
  rw [hP.source] at hsub
  refine iInf₂_le_of_le (P t0) ht0T.2 ?_
  refine (lfppDOn_le hsub fun τ hτ => hin _ ⟨by nlinarith [hτ.1, hτ.2],
    by nlinarith [hτ.1, hτ.2]⟩).trans ?_
  rw [lfppLen_subPath P ht0pos, lfppLen_eq]
  exact lintegral_mono_set (Icc_subset_Icc le_rfl ht0T.1.2)

section lfppC

variable {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
include hc

theorem lfppDistE_ne_top' (u v : ℂ) : lfppDistE ξ ε g u v ≠ ⊤ := by
  rw [lfppDistE_eq_lfppDOn]; exact lfppD_ne_top hc u v

theorem lfppC_nonneg (p : ℂ × ℂ) : 0 ≤ lfppC ξ ε g p := by
  rw [lfppC_apply_of_continuous hc]
  exact mul_nonneg (inv_nonneg.2 (aEpsDF_nonneg_sq _ _)) ENNReal.toReal_nonneg

theorem lfppC_mem_pmetSet : lfppC ξ ε g ∈ pmetSet ℂ := by
  refine ⟨fun x => ?_, fun x y z => ?_⟩
  · rw [lfppC_apply_of_continuous hc, lfppDistE_self]; simp
  · simp only [lfppC_apply_of_continuous hc]
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (aEpsDF_nonneg_sq _ _))
    have := (lfppDistCM ξ ε g hc).2.triangle x y z
    simpa only [lfppDistCM_coe, lfppDist] using this

theorem lfppC_mem_symmSet : lfppC ξ ε g ∈ symmSet ℂ := by
  intro x y
  simp only [lfppC_apply_of_continuous hc]
  have := (lfppDistCM ξ ε g hc).2.symm x y
  simp only [lfppDistCM_coe, lfppDist] at this
  rw [this]

/-- `ε`-midpoints of `𝔞_ε⁻¹ D_h^ε` -/
theorem lfppC_approxMid (x y : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z, lfppC ξ ε g (x, z) ≤ lfppC ξ ε g (x, y) / 2 + δ ∧
      lfppC ξ ε g (z, y) ≤ lfppC ξ ε g (x, y) / 2 + δ := by
  simp only [lfppC_apply_of_continuous hc]
  set c := (aEpsDF ξ ε)⁻¹
  have hc0 : 0 ≤ c := inv_nonneg.2 (aEpsDF_nonneg_sq _ _)
  rcases hc0.eq_or_lt with h0 | h0
  · exact ⟨x, by rw [← h0]; simp; linarith, by rw [← h0]; simp; linarith⟩
  have hself : ∀ z ∈ (univ : Set ℂ), lfppDOn ξ (heatMollify ε g) univ z z = 0 := fun z _ => by
    rw [← lfppDistE_eq_lfppDOn]; exact lfppDistE_self _ _ _ _
  obtain ⟨z, -, h1, h2⟩ := lfppDOn_approxMid_of_fin hc hself (mem_univ x) (mem_univ y)
    (lfppD_ne_top hc x y) (div_pos hδ h0)
  rw [← lfppDistE_eq_lfppDOn, ← lfppDistE_eq_lfppDOn] at h1 h2
  have key : c * ((lfppDistE ξ ε g x y).toReal / 2 + δ / c) =
      c * (lfppDistE ξ ε g x y).toReal / 2 + δ := by field_simp
  exact ⟨z, (mul_le_mul_of_nonneg_left h1 hc0).trans key.le,
    (mul_le_mul_of_nonneg_left h2 hc0).trans key.le⟩

/-- first-hit cut for `𝔞_ε⁻¹ D_h^ε`: a lower bound on `∂K` is a lower bound outside `int K` -/
theorem lfppC_cut {K : Set ℂ} (hK : IsClosed K) {x z : ℂ} (hx : x ∈ interior K)
    (hz : z ∉ interior K) {m : ℝ} (hm : ∀ w ∈ frontier K, m ≤ lfppC ξ ε g (x, w)) :
    m ≤ lfppC ξ ε g (x, z) := by
  rcases le_or_gt m 0 with hm0 | hm0
  · exact hm0.trans (lfppC_nonneg hc _)
  have hfr : ∃ w, w ∈ frontier K := by
    by_cases hzf : z ∈ frontier K
    · exact ⟨z, hzf⟩
    · have hzK : z ∉ K := fun h => hzf ⟨subset_closure h, hz⟩
      obtain ⟨w, -, hw⟩ := cut_inter_frontier_nonempty hK isPreconnected_univ (mem_univ z) hzK
        (mem_univ x) (interior_subset hx)
      exact ⟨w, hw⟩
  obtain ⟨w1, hw1⟩ := hfr
  simp only [lfppC_apply_of_continuous hc] at hm ⊢
  set c := (aEpsDF ξ ε)⁻¹
  have hc0 : 0 ≤ c := inv_nonneg.2 (aEpsDF_nonneg_sq _ _)
  rcases hc0.eq_or_lt with h0 | h0
  · have := hm w1 hw1; rw [← h0, zero_mul] at this; linarith
  have hle : ENNReal.ofReal (m / c) ≤ ⨅ w ∈ frontier K, lfppDOn ξ (heatMollify ε g) K x w := by
    refine le_iInf₂ fun w hw => ?_
    refine le_trans ?_ (lfppDistE_le_lfppDOn ξ ε g K x w)
    rw [ENNReal.ofReal_le_iff_le_toReal (lfppDistE_ne_top' hc x w), div_le_iff₀ h0, mul_comm]
    exact hm w hw
  have := (hle.trans (iInf_frontier_lfppDOn_le' hK hx hz))
  rw [ENNReal.ofReal_le_iff_le_toReal (lfppDistE_ne_top' hc x z), div_le_iff₀ h0, mul_comm] at this
  exact this

/-- `𝔞_ε⁻¹ D_h^ε` satisfies the local midpoint condition on `S_s(0)` -/
theorem lfppC_mem_zSetC {s : ℝ} (hs : 0 ≤ s) : lfppC ξ ε g ∈ zSetC s := by
  intro x hx y hy hxy
  set f := lfppC ξ ε g
  set T := sqC s 0
  have hTc : IsCompact T := isCompact_sqC hs
  have hf0 : ∀ p, 0 ≤ f p := lfppC_nonneg hc
  have hfxx : ∀ u, f (u, u) = 0 := (lfppC_mem_pmetSet hc).1
  have hxi : x ∈ interior T := by
    rw [← self_sdiff_frontier]
    refine ⟨hx, fun hxf => ?_⟩
    have := hxy x hxf
    rw [hfxx] at this; linarith [hf0 (x, y)]
  have hcx : Continuous fun w => f (x, w) := f.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M, hM1, hM2⟩ : ∃ M, f (x, y) / 2 < M ∧ ∀ w ∈ frontier T, M ≤ f (x, w) := by
    rcases (frontier T).eq_empty_or_nonempty with he | hne
    · exact ⟨f (x, y) / 2 + 1, by linarith, fun w hw => by rw [he] at hw; exact absurd hw id⟩
    · obtain ⟨w0, hw0, hmin⟩ := (hTc.of_isClosed_subset isClosed_frontier
        hTc.isClosed.frontier_subset).exists_isMinOn hne hcx.continuousOn
      exact ⟨f (x, w0), by linarith [hxy w0 hw0, hf0 (x, y)], fun w hw => hmin hw⟩
  set δ : ℕ → ℝ := fun n => (M - f (x, y) / 2) / ((n : ℝ) + 2)
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos (by linarith) (by positivity)
  have hδlt : ∀ n, δ n < M - f (x, y) / 2 := fun n =>
    (div_lt_self (by linarith) (by have := n.cast_nonneg (α := ℝ); linarith))
  have hz : ∀ n, ∃ z ∈ T, f (x, z) ≤ f (x, y) / 2 + δ n ∧ f (z, y) ≤ f (x, y) / 2 + δ n := by
    intro n
    obtain ⟨z, h1, h2⟩ := lfppC_approxMid hc x y (hδpos n)
    refine ⟨z, ?_, h1, h2⟩
    by_contra hzT
    have := lfppC_cut hc hTc.isClosed hxi (fun h => hzT (interior_subset h)) hM2
    linarith [hδlt n]
  choose z hzT hz1 hz2 using hz
  obtain ⟨z0, hz0, φ, hφ, hlim⟩ := hTc.tendsto_subseq hzT
  have hδ0 : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun n => f (x, y) / 2 + δ (φ n)) atTop (𝓝 (f (x, y) / 2 + 0)) :=
    tendsto_const_nhds.add (hδ0.comp hφ.tendsto_atTop)
  rw [add_zero] at h2
  refine ⟨z0, hz0, ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto' ((f.continuous.tendsto (x, z0)).comp
      (tendsto_const_nhds.prodMk_nhds hlim)) h2 fun n => hz1 (φ n)
  · exact le_of_tendsto_of_tendsto' ((f.continuous.tendsto (z0, y)).comp
      (hlim.prodMk_nhds tendsto_const_nhds)) h2 fun n => hz2 (φ n)

end lfppC

/-- the local midpoint condition for functions on `T × T` -/
def zSetSq (T : Set ℂ) : Set C(T × T, ℝ) :=
  {d | ∀ x y : T, (∀ w : T, w.1 ∈ frontier T → d (x, y) < d (x, w)) →
    ∃ z : T, d (x, z) ≤ d (x, y) / 2 ∧ d (z, y) ≤ d (x, y) / 2}

theorem zSetC_eq {s : ℝ} (hs : 0 ≤ s) :
    zSetC s = restrSq (sqC s 0) ⁻¹' zSetSq (sqC s 0) := by
  have hfT : ∀ w ∈ frontier (sqC s 0), w ∈ sqC s 0 := fun w hw =>
    (isCompact_sqC hs).isClosed.frontier_subset hw
  ext d
  simp only [zSetC, zSetSq, mem_preimage, restrSq_apply, mem_ofPred_eq]
  constructor
  · intro h x y hw
    obtain ⟨z, hz, h1, h2⟩ := h x.1 x.2 y.1 y.2 fun w hwf => hw ⟨w, hfT w hwf⟩ hwf
    exact ⟨⟨z, hz⟩, h1, h2⟩
  · intro h x hx y hy hw
    obtain ⟨z, h1, h2⟩ := h ⟨x, hx⟩ ⟨y, hy⟩ fun w hwf => hw w.1 hwf
    exact ⟨z.1, z.2, h1, h2⟩

theorem isClosed_zSetSq {T : Set ℂ} [CompactSpace T] : IsClosed (zSetSq T) := by
  refine isClosed_of_closure_subset fun d hd => ?_
  obtain ⟨dn, hdn, hlim⟩ := mem_closure_iff_seq_limit.1 hd
  intro x y hw
  set W : Set T := {w | w.1 ∈ frontier T}
  have hev : ∀ᶠ n in atTop, ∀ w : T, w.1 ∈ frontier T → dn n (x, y) < dn n (x, w) := by
    have hWc : IsCompact W := (isClosed_frontier.preimage continuous_subtype_val).isCompact
    rcases W.eq_empty_or_nonempty with he | hne
    · exact Eventually.of_forall fun n w hwf =>
        absurd (show w ∈ W from hwf) (by rw [he]; exact id)
    · obtain ⟨w0, hw0, hmin⟩ := hWc.exists_isMinOn hne (f := fun w => d (x, w))
        (d.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      have hm : 0 < d (x, w0) - d (x, y) := sub_pos.2 (hw w0 hw0)
      filter_upwards [Metric.tendsto_nhds.1 hlim _ (half_pos hm)] with n hn w hwf
      have e1 := (ContinuousMap.dist_apply_le_dist (f := dn n) (g := d) (x, y)).trans_lt hn
      have e2 := (ContinuousMap.dist_apply_le_dist (f := dn n) (g := d) (x, w)).trans_lt hn
      rw [Real.dist_eq, abs_lt] at e1 e2
      have := hmin (show w ∈ W from hwf)
      simp only [mem_ofPred_eq] at this
      linarith [e1.1, e1.2, e2.1, e2.2]
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hz : ∀ n, ∃ z : T, N ≤ n →
      dn n (x, z) ≤ dn n (x, y) / 2 ∧ dn n (z, y) ≤ dn n (x, y) / 2 := fun n => by
    by_cases h : N ≤ n
    · obtain ⟨z, hz⟩ := hdn n x y (hN n h)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose z hz using hz
  obtain ⟨z0, -, φ, hφ, hzlim⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (z n))
  have hdφ := hlim.comp hφ.tendsto_atTop
  have hev2 : ∀ᶠ n in atTop, N ≤ φ n := hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
  have hR : Tendsto (fun n => dn (φ n) (x, y) / 2) atTop (𝓝 (d (x, y) / 2)) :=
    (((continuous_eval_const (x, y)).tendsto d).comp hdφ).div_const 2
  refine ⟨z0, ?_, ?_⟩
  · have hL : Tendsto (fun n => dn (φ n) (x, z (φ n))) atTop (𝓝 (d (x, z0))) :=
      (continuous_eval.tendsto (d, (x, z0))).comp
        (hdφ.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hzlim))
    exact le_of_tendsto_of_tendsto hL hR (hev2.mono fun n hn => (hz (φ n) hn).1)
  · have hL : Tendsto (fun n => dn (φ n) (z (φ n), y)) atTop (𝓝 (d (z0, y))) :=
      (continuous_eval.tendsto (d, (z0, y))).comp
        (hdφ.prodMk_nhds (hzlim.prodMk_nhds tendsto_const_nhds))
    exact le_of_tendsto_of_tendsto hL hR (hev2.mono fun n hn => (hz (φ n) hn).2)

theorem isClosed_zSetC {s : ℝ} (hs : 0 ≤ s) : IsClosed (zSetC s) := by
  have : CompactSpace (sqC s 0) := isCompact_iff_compactSpace.1 (isCompact_sqC hs)
  rw [zSetC_eq hs]
  exact isClosed_zSetSq.preimage (restrSq _).continuous

end LQGMetric.DFGPS
