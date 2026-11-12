/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_10ProofCut at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Sq
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.10, step (ii): internal metric on `S_1(0)` → whole-plane metric

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`), proof of Lemma 2.10, T:953–957:
the event (2.11) for `S_{1/R}(0)` and `∂S_1(0)` follows from the corresponding statement for
the internal metric `D_h^ε(·,·;S_1(0))` given by Lemma 2.8. The two facts used implicitly by the
paper: `D_h^ε(u,v) ≤ D_h^ε(u,v;S_1(0))` (fewer paths), and a path from `u ∈ int S_1(0)` to
`v ∈ ∂S_1(0)` contains a sub-path in `S_1(0)` from `u` to `∂S_1(0)` (cut at the first hit of
`∂S_1(0)`), so `D_h^ε(u, v) ≥ inf_{w∈∂S_1(0)} D_h^ε(u,w;S_1(0))`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- a preconnected set meeting a closed set `K` and its complement meets `∂K` (as
`GM.jb_inter_frontier_nonempty`) -/
theorem cut_inter_frontier_nonempty {K C : Set ℂ} (hK : IsClosed K) (hC : IsPreconnected C)
    {a b : ℂ} (ha : a ∈ C) (haK : a ∉ K) (hb : b ∈ C) (hbK : b ∈ K) :
    (C ∩ frontier K).Nonempty := by
  by_contra hne
  have hsub : C ⊆ interior K ∪ Kᶜ := fun x hx => by
    by_cases hxK : x ∈ K
    · left
      by_contra hi
      exact hne ⟨x, hx, subset_closure hxK, hi⟩
    · exact Or.inr hxK
  rcases hC.subset_or_subset isOpen_interior hK.isOpen_compl
      ((disjoint_compl_right (a := K)).mono_left interior_subset) hsub with h | h
  · exact haK (interior_subset (h ha))
  · exact h hb hbK

theorem lfppDistE_le_lfppDOn (ξ ε : ℝ) (x : DistC) (S : Set ℂ) (u v : ℂ) :
    lfppDistE ξ ε x u v ≤ lfppDOn ξ (heatMollify ε x) S u v :=
  le_iInf fun P => iInf_le_of_le ⟨P.1, P.2.1⟩ le_rfl

/-- **first-hit cut**: for `u ∈ int K` and `v ∈ ∂K` (`K` closed),
`inf_{w ∈ ∂K} D(u, w; K) ≤ D(u, v)`. -/
theorem iInf_frontier_lfppDOn_le {ξ ε : ℝ} {x : DistC} {K : Set ℂ} (hK : IsClosed K) {u v : ℂ}
    (hu : u ∈ interior K) (hv : v ∈ frontier K) :
    ⨅ w ∈ frontier K, lfppDOn ξ (heatMollify ε x) K u w ≤ lfppDistE ξ ε x u v := by
  refine le_iInf fun Q => ?_
  obtain ⟨P, hP⟩ := Q
  simp only
  set T : Set ℝ := Icc 0 1 ∩ P ⁻¹' frontier K
  have hTc : IsClosed T := hP.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
    isClosed_frontier
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by simp [hP.target, hv]⟩
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set t0 := sInf T
  have ht0T : t0 ∈ T := hTc.csInf_mem ⟨1, h1T⟩ hTb
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

theorem mem_interior_sq1_of_mem_sqC_half {u : ℂ} (hu : u ∈ sqC (1 / 2) 0) : u ∈ interior sq1 := by
  rw [← self_sdiff_frontier]
  exact ⟨sqC_mono (by norm_num) hu, not_mem_frontier_of_mem_sqC_half hu⟩

theorem zero_mem_sqC {s : ℝ} (hs : 0 ≤ s) : (0 : ℂ) ∈ sqC s 0 := by
  rw [mem_sqC_iff]; simp only [Complex.zero_re, Complex.zero_im]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem frontier_sq1_nonempty : (frontier sq1).Nonempty := by
  refine nonempty_frontier_iff.2 ⟨⟨0, zero_mem_sqC zero_le_one⟩, fun h => ?_⟩
  have : (2 : ℂ) ∈ sq1 := h ▸ mem_univ _
  rw [mem_sqC_iff] at this
  norm_num at this

/-- **DFGPS T:953–957, step (ii)**: if `𝔞_ε⁻¹ D_h^ε(·,·;S_1(0)) ∈ sqG C R`, then the event of
(2.10) holds for the whole-plane metric with `r = 1/(R+2)` and `R + 2` in place of `R`. -/
theorem sqBdyEvent_of_mem_sqG {ξ ε C : ℝ} (hC : 0 < C) {x : DistC}
    (hc : Continuous (heatMollify ε x)) {R₀ : ℕ} (hd : lfppSqC ξ ε x sq1 ∈ sqG C R₀) :
    sqBdyEvent ξ ε C (innSide R₀) (1 / innSide R₀) x := by
  have := compactSpace_sq1
  obtain ⟨a, h1, h2⟩ := hd
  set s := innSide R₀
  set 𝔞 := aEpsDF ξ ε
  set φ := heatMollify ε x
  set d := lfppSqC ξ ε x sq1
  have hdeq : ∀ p : sq1 × sq1, d p = 𝔞⁻¹ * (lfppDOn ξ φ sq1 p.1 p.2).toReal := fun p =>
    lfppSqC_apply_of_continuous (a := 0 - ((1 / 2 : ℝ) : ℂ) * (1 + Complex.I)) hc one_pos p
  obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hc
    (convex_closedSq (0 - ((1 / 2 : ℝ) : ℂ) * (1 + Complex.I)) 1)
    (closedSq_subset_closedBall _ zero_le_one)
  have hfin : ∀ u ∈ sq1, ∀ v ∈ sq1, lfppDOn ξ φ sq1 u v ≠ ⊤ := fun u hu v hv =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB u hu v hv)
  have hs0 : 0 < s := innSide_pos R₀
  have h0s : (0 : ℂ) ∈ sqC s 0 := zero_mem_sqC hs0.le
  have h01 : (0 : ℂ) ∈ sq1 := zero_mem_sqC zero_le_one
  have hsq : ∀ {u}, u ∈ sqC s 0 → u ∈ sq1 := fun hu => sqC_mono (innSide_le_half R₀ |>.trans
    (by norm_num)) hu
  have ha : 0 < a := by
    have := h1 (x := (⟨0, h01⟩, ⟨0, h01⟩)) ⟨h0s, h0s⟩
    rw [hdeq] at this
    simp only at this
    rwa [show lfppDOn ξ φ sq1 0 0 = 0 from lfppDOn_self (convex_closedSq _ 1) h01,
      ENNReal.toReal_zero, mul_zero] at this
  have h𝔞 : 0 < 𝔞 := by
    rcases (aEpsDF_nonneg_sq ξ ε).eq_or_lt with h | h
    · exfalso
      obtain ⟨w, hw⟩ := frontier_sq1_nonempty
      have hw1 : w ∈ sq1 := (isCompact_sqC zero_le_one).isClosed.closure_subset hw.1
      have := h2 (x := (⟨0, h01⟩, ⟨w, hw1⟩)) ⟨h0s, hw⟩
      simp only [mem_Ioi, hdeq] at this
      rw [show 𝔞 = 0 from h.symm, inv_zero, zero_mul] at this
      nlinarith
    · exact h
  -- the maximum of `d` on `innerPairs`
  obtain ⟨p0, hp0, hmax⟩ := (isClosed_innerPairs R₀).isCompact.exists_isMaxOn
    ⟨(⟨0, h01⟩, ⟨0, h01⟩), h0s, h0s⟩ d.continuous.continuousOn
  have hm : d p0 < a := h1 hp0
  have hsup : (⨆ u ∈ sqC s 0, ⨆ v ∈ sqC s 0, lfppDistE ξ ε x u v) ≤
      ENNReal.ofReal (𝔞 * d p0) := by
    refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
    refine (lfppDistE_le_lfppDOn ξ ε x sq1 u v).trans ?_
    rw [← ENNReal.ofReal_toReal (hfin u (hsq hu) v (hsq hv))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hmax (a := (⟨u, hsq hu⟩, ⟨v, hsq hv⟩)) ⟨hu, hv⟩
    simp only [hdeq] at this
    rw [hdeq p0, ← mul_assoc, mul_inv_cancel₀ h𝔞.ne', one_mul]
    exact le_of_mul_le_mul_left this (inv_pos.2 h𝔞)
  have hinf : ENNReal.ofReal (𝔞 * (C * a)) ≤
      ⨅ u ∈ sqC s 0, ⨅ v ∈ frontier (sqC (1 / s * s) 0), lfppDistE ξ ε x u v := by
    rw [one_div_mul_cancel hs0.ne']
    refine le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_
    refine le_trans ?_ (iInf_frontier_lfppDOn_le (isCompact_sqC zero_le_one).isClosed
      (mem_interior_sq1_of_mem_sqC_half (sqC_mono (innSide_le_half R₀) hu)) hv)
    refine le_iInf₂ fun w hw => ?_
    have hw1 : w ∈ sq1 := (isCompact_sqC zero_le_one).isClosed.closure_subset hw.1
    rw [← ENNReal.ofReal_toReal (hfin u (hsq hu) w hw1)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := h2 (x := (⟨u, hsq hu⟩, ⟨w, hw1⟩)) ⟨hu, hw⟩
    simp only [mem_Ioi, hdeq] at this
    rw [inv_mul_eq_div, lt_div_iff₀ h𝔞] at this
    nlinarith
  refine lt_of_le_of_lt hsup (lt_of_lt_of_le ?_ (by gcongr :
    ENNReal.ofReal C⁻¹ * ENNReal.ofReal (𝔞 * (C * a)) ≤ _))
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hC.le),
    show C⁻¹ * (𝔞 * (C * a)) = 𝔞 * a by field_simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)

end LQGMetric.DFGPS
