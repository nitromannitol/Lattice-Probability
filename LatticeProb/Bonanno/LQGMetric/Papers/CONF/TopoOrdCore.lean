/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.TopoOrdCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrdPath

/-!
# TOPO-ORD, step 3b: the crossing argument in the chart plane

Planar core of TOPO-ORD (handoff P2-CONFTOPO, step 3): in the chart plane of the inner set
(`Re ζ ≥ 0` is the closed exterior of `K₁`, `Re ζ = 0` its boundary), paths `ZP`, `ZQ` start on
the line `Re ζ = 0` in the order `Im ZP(a) < Im ZQ(a)`, and continue at their ends by rays `RP`,
`RQ` that go to `Re ζ = +∞` and end up separated by a horizontal level `y₀` (`RP` above, `RQ`
below), with `RP`, `RQ` disjoint from each other and (except their starts) from the paths.
Then `ZP`, `ZQ` meet. Proof: in the rectangle `[−M, M] × [−N, N]`, the horizontal segment to
`ZP(a)` followed by `ZP` and `RP` up to its first hit of `Re = M` is a left–right crossing; the
segment from the top-left corner to `ZQ(a)`, then `ZQ`, `RQ` up to `Re = M` and the vertical
segment down to the bottom side is a top–bottom crossing; they meet by
`RectMeet.rect_crossings_meet`, and every meeting not between `ZP` and `ZQ` is excluded.
This is the strip-model proof of "paths with reversed boundary order cross" (CONF
arXiv:1905.00381 l. 598–600), own formalization (DV-CONF-TO1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric.CONF.DD

theorem core_meet {a b : ℝ} (hab : a ≤ b) {ZP ZQ RP RQ : ℝ → ℂ}
    (hZPc : ContinuousOn ZP (Icc a b)) (hZQc : ContinuousOn ZQ (Icc a b))
    (hRPc : ContinuousOn RP (Ici 0)) (hRQc : ContinuousOn RQ (Ici 0))
    (hZPre : ∀ t ∈ Icc a b, 0 ≤ (ZP t).re) (hZQre : ∀ t ∈ Icc a b, 0 ≤ (ZQ t).re)
    (hRPre : ∀ r, 0 ≤ r → 0 ≤ (RP r).re) (hRQre : ∀ r, 0 ≤ r → 0 ≤ (RQ r).re)
    (hP0 : (ZP a).re = 0) (hQ0 : (ZQ a).re = 0) (hord : (ZP a).im < (ZQ a).im)
    (hRP0 : RP 0 = ZP b) (hRQ0 : RQ 0 = ZQ b)
    (hdPQ : ∀ t ∈ Icc a b, ∀ r, 0 < r → RQ r ≠ ZP t)
    (hdQP : ∀ t ∈ Icc a b, ∀ r, 0 < r → RP r ≠ ZQ t)
    (hRR : ∀ r, 0 ≤ r → ∀ r', 0 ≤ r' → RP r ≠ RQ r')
    (C T y₀ : ℝ) (hgP : ∀ r, 0 ≤ r → r - C ≤ (RP r).re) (hgQ : ∀ r, 0 ≤ r → r - C ≤ (RQ r).re)
    (hsP : ∀ r, 0 ≤ r → T ≤ (RP r).re → y₀ < (RP r).im)
    (hsQ : ∀ r, 0 ≤ r → T ≤ (RQ r).re → (RQ r).im < y₀) :
    ∃ t ∈ Icc a b, ∃ t' ∈ Icc a b, ZP t = ZQ t' := by
  by_contra hno
  have hne : ∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, ZP t ≠ ZQ t' := fun t ht t' ht' h =>
    hno ⟨t, ht, t', ht', h⟩
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  obtain ⟨BP, hBP⟩ := isCompact_Icc.exists_bound_of_continuousOn hZPc
  obtain ⟨BQ, hBQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hZQc
  set B₁ := |BP| + |BQ| with hB₁
  have hZPb : ∀ t ∈ Icc a b, ‖ZP t‖ ≤ B₁ := fun t ht =>
    (hBP t ht).trans (by linarith [le_abs_self BP, abs_nonneg BQ])
  have hZQb : ∀ t ∈ Icc a b, ‖ZQ t‖ ≤ B₁ := fun t ht =>
    (hBQ t ht).trans (by linarith [le_abs_self BQ, abs_nonneg BP])
  set M := max (max T (B₁ + 1)) 1 with hM
  have hMT : T ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMB : B₁ + 1 ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM1 : 1 ≤ M := le_max_right _ _
  have hZPM : ∀ t ∈ Icc a b, (ZP t).re < M := fun t ht => by
    linarith [Complex.re_le_norm (ZP t), hZPb t ht]
  have hZQM : ∀ t ∈ Icc a b, (ZQ t).re < M := fun t ht => by
    linarith [Complex.re_le_norm (ZQ t), hZQb t ht]
  -- first hits of `Re = M`
  set R := M + |C| with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨rP, hrP, hPM, hPle⟩ := first_hit (f := fun r => (RP r).re) hR0
    (Complex.continuous_re.comp_continuousOn (hRPc.mono Icc_subset_Ici_self))
    (by simp only [hRP0]; exact hZPM b hb) (by linarith [hgP R hR0, le_abs_self C])
  obtain ⟨rQ, hrQ, hQM, hQle⟩ := first_hit (f := fun r => (RQ r).re) hR0
    (Complex.continuous_re.comp_continuousOn (hRQc.mono Icc_subset_Ici_self))
    (by simp only [hRQ0]; exact hZQM b hb) (by linarith [hgQ R hR0, le_abs_self C])
  have hRPc' : ContinuousOn RP (Icc 0 rP) := hRPc.mono Icc_subset_Ici_self
  have hRQc' : ContinuousOn RQ (Icc 0 rQ) := hRQc.mono Icc_subset_Ici_self
  obtain ⟨B₂, hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hRPc'
  obtain ⟨B₃, hB₃⟩ := isCompact_Icc.exists_bound_of_continuousOn hRQc'
  set N := B₁ + |B₂| + |B₃| + 1 with hN
  have hB1 : 0 ≤ B₁ := by positivity
  have imb : ∀ x : ℂ, ∀ B : ℝ, ‖x‖ ≤ B → |B| ≤ N - 1 - B₁ ∨ B = B₁ → x.im ∈ Icc (-N) N := by
    intro x B hx hB
    have h1 := Complex.abs_im_le_norm x
    have h2 : B ≤ N - 1 := by
      rcases hB with hB | hB
      · linarith [le_abs_self B]
      · rw [hB]; linarith [abs_nonneg B₂, abs_nonneg B₃]
    rw [abs_le] at h1
    exact ⟨by linarith, by linarith⟩
  have hZPi : ∀ t ∈ Icc a b, (ZP t).im ∈ Icc (-N) N := fun t ht =>
    imb _ _ (hZPb t ht) (Or.inr rfl)
  have hZQi : ∀ t ∈ Icc a b, (ZQ t).im ∈ Icc (-N) N := fun t ht =>
    imb _ _ (hZQb t ht) (Or.inr rfl)
  have hRPi : ∀ r ∈ Icc 0 rP, (RP r).im ∈ Icc (-N) N := fun r hr =>
    imb _ _ (hB₂ r hr) (Or.inl (by linarith [abs_nonneg B₃]))
  have hRQi : ∀ r ∈ Icc 0 rQ, (RQ r).im ∈ Icc (-N) N := fun r hr =>
    imb _ _ (hB₃ r hr) (Or.inl (by linarith [abs_nonneg B₂]))
  set yP := (ZP a).im
  set yQ := (ZQ a).im
  have hyP := hZPi a ha
  have hyQ := hZQi a ha
  set cQ := (RQ rQ).im
  have hcQ := hRQi rQ ⟨hrQ.1, le_rfl⟩
  have hcQy : cQ < y₀ := hsQ rQ hrQ.1 (hQM ▸ hMT)
  -- the crossings
  let γ : Path (⟨-M, yP⟩ : ℂ) (RP rP) := (segPath ⟨-M, yP⟩ (ZP a)).trans
    ((pathOn ZP hab hZPc).trans ((pathOn RP hrP.1 hRPc').cast hRP0.symm rfl))
  let δ : Path (⟨-M, N⟩ : ℂ) ⟨M, -N⟩ := (segPath ⟨-M, N⟩ (ZQ a)).trans
    ((pathOn ZQ hab hZQc).trans (((pathOn RQ hrQ.1 hRQc').cast hRQ0.symm rfl).trans
      (segPath (RQ rQ) ⟨M, -N⟩)))
  have hγr : ∀ x ∈ range γ, x ∈ range (segPath ⟨-M, yP⟩ (ZP a)) ∨ x ∈ ZP '' Icc a b ∨
      x ∈ RP '' Icc 0 rP := by
    intro x hx
    simp only [γ, path_trans_range, mem_union] at hx
    rcases hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (pathOn_range _ _ _ h))
    · refine Or.inr (Or.inr (pathOn_range RP hrP.1 hRPc' ?_))
      simpa [Path.cast_coe] using h
  have hδr : ∀ x ∈ range δ, x ∈ range (segPath ⟨-M, N⟩ (ZQ a)) ∨ x ∈ ZQ '' Icc a b ∨
      x ∈ RQ '' Icc 0 rQ ∨ x ∈ range (segPath (RQ rQ) ⟨M, -N⟩) := by
    intro x hx
    simp only [δ, path_trans_range, mem_union] at hx
    rcases hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (pathOn_range _ _ _ h))
    · refine Or.inr (Or.inr (Or.inl (pathOn_range RQ hrQ.1 hRQc' ?_)))
      simpa [Path.cast_coe] using h
    · exact Or.inr (Or.inr (Or.inr h))
  -- the segments
  have hSP : ∀ x ∈ range (segPath ⟨-M, yP⟩ (ZP a)), x.re ≤ 0 ∧ -M ≤ x.re ∧ x.im = yP := by
    intro x hx
    obtain ⟨s, hs, h1, h2⟩ := segPath_range _ _ hx
    simp only [hP0] at h1 h2
    refine ⟨by nlinarith [hs.2], by nlinarith [hs.1], by rw [h2]; ring⟩
  have hST : ∀ x ∈ range (segPath ⟨-M, N⟩ (ZQ a)), x.re ≤ 0 ∧ -M ≤ x.re ∧ yQ ≤ x.im ∧
      x.im ≤ N ∧ (x.re = 0 → x.im = yQ) := by
    intro x hx
    obtain ⟨s, hs, h1, h2⟩ := segPath_range _ _ hx
    simp only [hQ0] at h1 h2
    refine ⟨by nlinarith [hs.2], by nlinarith [hs.1], by nlinarith [hs.1, hs.2, hyQ.2],
      by nlinarith [hs.1, hs.2, hyQ.2], fun h0 => ?_⟩
    have hs1 : s = 1 := by nlinarith
    rw [h2, hs1]; ring
  have hSR : ∀ x ∈ range (segPath (RQ rQ) ⟨M, -N⟩), x.re = M ∧ -N ≤ x.im ∧ x.im ≤ cQ := by
    intro x hx
    obtain ⟨s, hs, h1, h2⟩ := segPath_range _ _ hx
    simp only [hQM] at h1
    refine ⟨by rw [h1]; ring, by nlinarith [hs.1, hs.2, hcQ.1], by nlinarith [hs.1, hs.2, hcQ.1]⟩
  -- containment in the rectangle
  have hγR : ∀ x ∈ range γ, x ∈ RectCross.rect (-M) M (-N) N := by
    intro x hx
    rcases hγr x hx with h | ⟨t, ht, rfl⟩ | ⟨r, hr, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := hSP x h
      exact ⟨⟨h2, by linarith⟩, h3 ▸ hyP⟩
    · exact ⟨⟨by linarith [hZPre t ht], (hZPM t ht).le⟩, hZPi t ht⟩
    · exact ⟨⟨by linarith [hRPre r hr.1], hPle r hr⟩, hRPi r hr⟩
  have hδR : ∀ x ∈ range δ, x ∈ RectCross.rect (-M) M (-N) N := by
    intro x hx
    rcases hδr x hx with h | ⟨t, ht, rfl⟩ | ⟨r, hr, rfl⟩ | h
    · obtain ⟨h1, h2, h3, h4, -⟩ := hST x h
      exact ⟨⟨h2, by linarith⟩, ⟨by linarith [hyQ.1], h4⟩⟩
    · exact ⟨⟨by linarith [hZQre t ht], (hZQM t ht).le⟩, hZQi t ht⟩
    · exact ⟨⟨by linarith [hRQre r hr.1], hQle r hr⟩, hRQi r hr⟩
    · obtain ⟨h1, h2, h3⟩ := hSR x h
      exact ⟨⟨by linarith, h1.le⟩, ⟨h2, by linarith [hcQ.2]⟩⟩
  have hext : ∀ {p q : ℂ} (c : Path p q) (s : ℝ), c.extend s ∈ range c := fun c s => by
    rw [← Path.extend_range]; exact mem_range_self s
  obtain ⟨s, -, t, -, hst⟩ := RectMeet.rect_crossings_meet (-M) M (-N) N γ.extend δ.extend
    γ.continuous_extend.continuousOn δ.continuous_extend.continuousOn
    (fun s _ => hγR _ (hext γ s)) (fun s _ => hδR _ (hext δ s))
    (by rw [Path.extend_zero]) (by rw [Path.extend_one, hPM]) (by rw [Path.extend_zero])
    (by rw [Path.extend_one])
  -- excluding every meeting
  have hx1 := hext γ s
  have hx2 := hext δ t
  rw [hst] at hx1
  set x := δ.extend t
  have hZPa : ∀ y : ℂ, y.re = 0 → y.im = yP → y = ZP a := fun y h1 h2 =>
    Complex.ext (h1.trans hP0.symm) h2
  have hZQa : ∀ y : ℂ, y.re = 0 → y.im = yQ → y = ZQ a := fun y h1 h2 =>
    Complex.ext (h1.trans hQ0.symm) h2
  rcases hγr x hx1 with hS | ⟨u, hu, hux⟩ | ⟨r, hr, hrx⟩ <;>
    rcases hδr x hx2 with hT | ⟨u', hu', hux'⟩ | ⟨r', hr', hrx'⟩ | hV
  · linarith [(hSP x hS).2.2, (hST x hT).2.2.1]
  · have h0 : x.re = 0 := le_antisymm (hSP x hS).1 (hux' ▸ hZQre u' hu')
    exact hne a ha u' hu' ((hZPa x h0 (hSP x hS).2.2).symm.trans hux'.symm)
  · have h0 : x.re = 0 := le_antisymm (hSP x hS).1 (hrx' ▸ hRQre r' hr'.1)
    have hxa := hZPa x h0 (hSP x hS).2.2
    rcases eq_or_lt_of_le hr'.1 with h | h
    · rw [← h, hRQ0] at hrx'
      exact hne a ha b hb (hxa.symm.trans hrx'.symm)
    · exact hdPQ a ha r' h (hrx'.trans hxa)
  · linarith [(hSP x hS).1, (hSR x hV).1]
  · have h0 : x.re = 0 := le_antisymm (hST x hT).1 (hux ▸ hZPre u hu)
    exact hne u hu a ha (hux.trans (hZQa x h0 ((hST x hT).2.2.2.2 h0)))
  · exact hne u hu u' hu' (hux.trans hux'.symm)
  · rcases eq_or_lt_of_le hr'.1 with h | h
    · rw [← h, hRQ0] at hrx'
      exact hne u hu b hb (hux.trans hrx'.symm)
    · exact hdPQ u hu r' h (hrx'.trans hux.symm)
  · have := (hSR x hV).1
    rw [← hux] at this
    linarith [hZPM u hu]
  · have h0 : x.re = 0 := le_antisymm (hST x hT).1 (hrx ▸ hRPre r hr.1)
    have hxa := hZQa x h0 ((hST x hT).2.2.2.2 h0)
    rcases eq_or_lt_of_le hr.1 with h | h
    · rw [← h, hRP0] at hrx
      exact hne b hb a ha (hrx.trans hxa)
    · exact hdQP a ha r h (hrx.trans hxa)
  · rcases eq_or_lt_of_le hr.1 with h | h
    · rw [← h, hRP0] at hrx
      exact hne b hb u' hu' (hrx.trans hux'.symm)
    · exact hdQP u' hu' r h (hrx.trans hux'.symm)
  · exact hRR r hr.1 r' hr'.1 (hrx.trans hrx'.symm)
  · have hre : (RP r).re = M := by rw [hrx]; exact (hSR x hV).1
    have h1 := hsP r hr.1 (hre ▸ hMT)
    rw [hrx] at h1
    linarith [(hSR x hV).2.2]

end LQGMetric.CONF.DD
