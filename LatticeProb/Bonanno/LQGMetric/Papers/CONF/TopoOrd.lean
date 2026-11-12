/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.TopoOrd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrdCore
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrdRay
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.Lift

/-!
# TOPO-ORD (D-D2, DV-CONF-AN2) and the unconditional CONF L2.5′

`topoOrd : TopoOrd`: two paths in `K₂ ∖ int K₁` whose lifted starts are ordered `u₁ < u₂` on
the lifted inner boundary and whose lifted ends are ordered `v₂ ≤ v₁` on the lifted outer
boundary meet with equal lifted angles. This is the step "paths with reversed boundary order must
intersect" of CONF (Gwynne–Miller, *Confluence of geodesic paths and separating loops in
continuum LQG*, arXiv:1905.00381, l. 598–600, in the universal cover of the annulus), in the
log-cover model of decision D-D2.

Proof (handoff P2-CONFTOPO, steps 2–3, with the inner set straightened instead of using inward
rays): the chart `L₁` of `ℂ ∖ int K₁` (`exists_chart`, from Carathéodory's theorem for the
inverted exterior of `K₁`) turns the lifted inner boundary into the line `Re ζ = 0`, so the
inward rays are horizontal half-lines; the outward rays are the `L₁`-preimages of the radial rays
of the chart `L₂` of `ℂ ∖ int K₂` (`chart_ray`); the order of starts and ends transfers through
`IsChart.bdy_mono`; `core_meet` (rectangle crossings, `RectMeet.rect_crossings_meet`) gives the
meeting. Own formalization of the strip-model argument (DV-CONF-TO1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric.CONF.DD

theorem chart_re_zero {K : Set ℂ} {z : ℂ} {L : ℂ → ℂ} (hL : IsChart K z L) {ζ : ℂ}
    (h0 : 0 ≤ ζ.re) (hK : z + Complex.exp (L ζ) ∈ K) : ζ.re = 0 := by
  by_contra h
  exact hL.out ζ (lt_of_le_of_ne h0 (Ne.symm h)) hK

/-- **TOPO-ORD** (D-D2) -/
theorem topoOrd : TopoOrd := by
  intro K₁ K₂ z hK₁ hK₂ hz h12 hc₁ hc₂ φ₁ θ₁ φ₂ θ₂ h₁ h₂ P Q a b α β hab hPc hQc hPm hQm hα hβ
    u₁ u₂ v₁ v₂ hPa1 hPa2 hQa1 hQa2 hPb1 hPb2 hQb1 hQb2 hu hv
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  rcases eq_or_lt_of_le hv with hveq | hvlt
  · refine ⟨b, hb, b, hb, ?_, ?_⟩
    · rw [← hPb1, ← hQb1, hveq]
    · rw [← hPb2, ← hQb2, hveq]
  have hz₂ : z ∈ interior K₂ := h12 (interior_subset hz)
  obtain ⟨L₁, hL₁⟩ := exists_chart hK₁ hz hc₁ h₁
  obtain ⟨L₂, hL₂⟩ := exists_chart hK₂ hz₂ hc₂ h₂
  have hzF₁ : z ∉ frontier K₁ := fun h => h.2 hz
  have hzF₂ : z ∉ frontier K₂ := fun h => h.2 hz₂
  obtain ⟨hPe, ZP, hZPc, hZP⟩ := chart_path hL₁ hPc (fun t ht => (hPm ht).2) hz hα
  obtain ⟨hQe, ZQ, hZQc, hZQ⟩ := chart_path hL₁ hQc (fun t ht => (hQm ht).2) hz hβ
  have hφ₁F : ∀ u, φ₁ u ∈ frontier K₁ := fun u => h₁.2.2.2.1 ▸ mem_range_self u
  have hφ₂F : ∀ u, φ₂ u ∈ frontier K₂ := fun u => h₂.2.2.2.1 ▸ mem_range_self u
  -- starts on the line `Re ζ = 0`, in order
  have hPaj : plift z P α a = jlog z φ₁ θ₁ u₁ := by unfold plift jlog; rw [hPa1, hPa2]
  have hQaj : plift z Q β a = jlog z φ₁ θ₁ u₂ := by unfold plift jlog; rw [hQa1, hQa2]
  have hZPa0 : (ZP a).re = 0 := chart_re_zero hL₁ (hZP a ha).1
    (by rw [(hZP a ha).2, hPe a ha, ← hPa1]; exact hK₁.isClosed.frontier_subset (hφ₁F u₁))
  have hZQa0 : (ZQ a).re = 0 := chart_re_zero hL₁ (hZQ a ha).1
    (by rw [(hZQ a ha).2, hQe a ha, ← hQa1]; exact hK₁.isClosed.frontier_subset (hφ₁F u₂))
  have hord : (ZP a).im < (ZQ a).im := hL₁.bdy_mono hK₁.isClosed h₁ hzF₁ hZPa0 hZQa0
    ((hZP a ha).2.trans hPaj) ((hZQ a ha).2.trans hQaj) hu
  -- ends in the outer chart, in order
  have hPbj : plift z P α b = jlog z φ₂ θ₂ v₁ := by unfold plift jlog; rw [hPb1, hPb2]
  have hQbj : plift z Q β b = jlog z φ₂ θ₂ v₂ := by unfold plift jlog; rw [hQb1, hQb2]
  obtain ⟨ξP, hξP0, hξPL⟩ := chart_bdy_pre hL₂ hK₂.isClosed (w := plift z P α b)
    (by rw [hPe b hb, ← hPb1]; exact hφ₂F v₁)
  obtain ⟨ξQ, hξQ0, hξQL⟩ := chart_bdy_pre hL₂ hK₂.isClosed (w := plift z Q β b)
    (by rw [hQe b hb, ← hQb1]; exact hφ₂F v₂)
  have hξ : ξQ.im < ξP.im := hL₂.bdy_mono hK₂.isClosed h₂ hzF₂ hξQ0 hξP0
    (hξQL.trans hQbj) (hξPL.trans hPbj) hvlt
  -- the outward rays
  obtain ⟨C₁, hC₁⟩ := hL₁.bdd
  obtain ⟨C₂, hC₂⟩ := hL₂.bdd
  obtain ⟨c₁, hc₁'⟩ := hL₁.asym
  obtain ⟨c₂, hc₂'⟩ := hL₂.asym
  obtain ⟨RP, hRPc, hRP, hgP, hsP⟩ := chart_ray hL₁ hL₂ h12 hC₁ hC₂ hc₁' hc₂' hξP0
  obtain ⟨RQ, hRQc, hRQ, hgQ, hsQ⟩ := chart_ray hL₁ hL₂ h12 hC₁ hC₂ hc₁' hc₂' hξQ0
  have hΔ : 0 < (ξP.im - ξQ.im) / 2 := by linarith
  obtain ⟨TP, hTP⟩ := hsP _ hΔ
  obtain ⟨TQ, hTQ⟩ := hsQ _ hΔ
  have hR0 : ∀ {R : ℝ → ℂ} {ξ : ℂ} {Z : ℝ → ℂ} {t : ℝ}, (∀ r, 0 ≤ r → 0 ≤ (R r).re ∧
      L₁ (R r) = L₂ (ξ + r)) → 0 ≤ (Z t).re → L₁ (Z t) = L₂ ξ → R 0 = Z t := by
    intro R ξ Z t hR hZ0 hZL
    refine hL₁.inj (show (0:ℝ) ≤ _ from (hR 0 le_rfl).1) (show (0:ℝ) ≤ _ from hZ0) ?_
    rw [(hR 0 le_rfl).2, hZL, Complex.ofReal_zero, add_zero]
  have hdisj : ∀ {R : ℝ → ℂ} {ξ : ℂ} (S : ℝ → ℂ), ξ.re = 0 → (∀ r, 0 ≤ r → 0 ≤ (R r).re ∧
      L₁ (R r) = L₂ (ξ + r)) → (∀ t ∈ Icc a b, z + Complex.exp (L₁ (ZP t)) ∈ K₂ ∧
      z + Complex.exp (L₁ (ZQ t)) ∈ K₂) → ∀ t ∈ Icc a b, ∀ r, 0 < r → R r ≠ ZP t ∧ R r ≠ ZQ t := by
    intro R ξ _ hξ0 hR hK t ht r hr
    have hout := hL₂.out (ξ + r) (by simp [hξ0]; exact hr)
    rw [← (hR r hr.le).2] at hout
    exact ⟨fun h => hout (h ▸ (hK t ht).1), fun h => hout (h ▸ (hK t ht).2)⟩
  have hK2 : ∀ t ∈ Icc a b, z + Complex.exp (L₁ (ZP t)) ∈ K₂ ∧
      z + Complex.exp (L₁ (ZQ t)) ∈ K₂ := fun t ht =>
    ⟨by rw [(hZP t ht).2, hPe t ht]; exact (hPm ht).1,
      by rw [(hZQ t ht).2, hQe t ht]; exact (hQm ht).1⟩
  obtain ⟨t, ht, t', ht', hZ⟩ := core_meet hab hZPc hZQc hRPc hRQc (fun t ht => (hZP t ht).1)
    (fun t ht => (hZQ t ht).1) (fun r hr => (hRP r hr).1) (fun r hr => (hRQ r hr).1)
    hZPa0 hZQa0 hord (hR0 hRP (hZP b hb).1 ((hZP b hb).2.trans hξPL.symm))
    (hR0 hRQ (hZQ b hb).1 ((hZQ b hb).2.trans hξQL.symm))
    (fun t ht r hr => (hdisj ZP hξQ0 hRQ hK2 t ht r hr).1)
    (fun t ht r hr => (hdisj ZP hξP0 hRP hK2 t ht r hr).2)
    (fun r hr r' hr' h => by
      have e := congrArg L₁ h
      rw [(hRP r hr).2, (hRQ r' hr').2] at e
      have e2 := hL₂.inj (show (0:ℝ) ≤ (ξP + r).re by simp [hξP0]; exact hr)
        (show (0:ℝ) ≤ (ξQ + r').re by simp [hξQ0]; exact hr') e
      have e3 := congrArg Complex.im e2
      simp at e3
      linarith)
    (C₁ + C₂) (max TP TQ) ((ξP.im + ξQ.im) / 2 + (c₂ - c₁).im) hgP hgQ
    (fun r hr hT => by
      have := abs_lt.1 (hTP r hr ((le_max_left _ _).trans hT)); linarith [this.1])
    (fun r hr hT => by
      have := abs_lt.1 (hTQ r hr ((le_max_right _ _).trans hT)); linarith [this.2])
  have hL : plift z P α t = plift z Q β t' := by
    rw [← (hZP t ht).2, ← (hZQ t' ht').2, hZ]
  refine ⟨t, ht, t', ht', ?_, ?_⟩
  · rw [← hPe t ht, ← hQe t' ht', hL]
  · have := congrArg Complex.im hL
    simpa [plift] using this

end LQGMetric.CONF.DD
