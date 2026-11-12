/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodL416b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL416

/-!
# GM Lemma 4.16, deterministic form

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.16 (`lem-geodesic-diam`,
l. 2216–2222), proof l. 2572–2579.

`gm_L4_16_det`: in the setting of `gm_L4_22_det` (`K = 𝓑^•_t`, `t = t_k`, `e = ε𝕣`, `λ = λ₄`,
`ρ = 2λe`, `c = (e/(4𝕣))^χ S`, `N = ⌈16πλ⌉`), let `0 < r ≤ e` and let `Q : [0,T] → ℂ` be a
`D(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to a point of `∂B_r(z)` (`IsAvoidGeod`) of finite
length. Assume the Hölder lower bound `(|u−v|/𝕣)^{χ'} S ≤ D(u,v)` for `u, v ∈ 𝓑_{s'}`,
`|u − v| ≤ A` (condition 3 of `ℰ_𝕣`, `A = a𝕣`) and `Nc < (A/𝕣)^{χ'} S`. Then any two points
`Q(s₁), Q(s₂)` reached after `D`-length `t` (GM: `P'([t_k, |P'|])` for the unit-speed
parametrization) satisfy `|Q(s₁) − Q(s₂)| ≤ 2𝕣(Nc/S)^{1/χ'} + 4ρ`; with `S = 𝔠_𝕣e^{ξh_𝕣(0)}`,
`Nc/S = N(ε/4)^χ`, this is GM's `diam P'([t_k,|P'|]) ≼ ε^{χ/χ'}𝕣`.

GM's proof: `t'` = last time `P'` hits `∂B_{2λ₄ε𝕣}(z)` (`gm_exists_last_hit`); (4.39) and the
geodesic property bound `len(P'|_{[0,t']})` (`gm_avoid_len_le_internal`, `gm_L4_22_det`); the
Hölder lower bound turns the `D`-length bound of `P'([t_k, t'])` into a Euclidean one (GM leave
implicit that the lower bound needs `|u − v| ≤ a𝕣`: we use an intermediate-value argument); and
`P'([t', |P'|]) ⊆ cl B_{2λ₄ε𝕣}(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the last time a curve from outside `cl B_ρ(z)` to a point inside `B_ρ(z)` hits `∂B_ρ(z)` -/
theorem gm_exists_last_hit {Q : ℝ → ℂ} {T ρ : ℝ} {z : ℂ} (hT : 0 ≤ T)
    (hQc : ContinuousOn Q (Icc 0 T)) (h0 : ρ < ‖Q 0 - z‖) (hT' : ‖Q T - z‖ < ρ) :
    ∃ τ ∈ Icc 0 T, Q τ ∈ sphere z ρ ∧ ∀ s ∈ Ioc τ T, Q s ∈ ball z ρ := by
  set A := {s ∈ Icc 0 T | ρ ≤ ‖Q s - z‖}
  have hAc : IsClosed A := hQc.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hAne : A.Nonempty := ⟨0, ⟨le_rfl, hT⟩, h0.le⟩
  have hAbd : BddAbove A := ⟨T, fun s hs => hs.1.2⟩
  set τ := sSup A
  have hτA : τ ∈ A := hAc.csSup_mem hAne hAbd
  have hafter : ∀ s ∈ Ioc τ T, Q s ∈ ball z ρ := by
    intro s hs
    rw [mem_ball, dist_eq_norm]
    by_contra hle
    exact absurd (le_csSup hAbd ⟨⟨hτA.1.1.trans hs.1.le, hs.2⟩, not_lt.1 hle⟩) (not_le.2 hs.1)
  have hτT : τ < T := lt_of_le_of_ne hτA.1.2 (fun h => by
    have := hτA.2; rw [h] at this; linarith)
  refine ⟨τ, hτA.1, ?_, hafter⟩
  rw [mem_sphere, dist_eq_norm]
  refine le_antisymm ?_ hτA.2
  -- right limit of points in `B_ρ(z)`
  have hcw : ContinuousWithinAt (fun s => ‖Q s - z‖) (Ioc τ T) τ :=
    ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt.comp_continuousWithinAt
      ((hQc τ hτA.1).mono fun s hs => ⟨hτA.1.1.trans hs.1.le, hs.2⟩))
  have hmem : τ ∈ closure (Ioc τ T) := by rw [closure_Ioc hτT.ne]; exact ⟨le_rfl, hτT.le⟩
  have := hcw.mem_closure_image hmem
  refine closure_minimal (s := (fun s => ‖Q s - z‖) '' Ioc τ T) (t := Iic ρ) ?_ isClosed_Iic this
  rintro _ ⟨s, hs, rfl⟩
  have := hafter s hs
  rw [mem_ball, dist_eq_norm] at this
  exact this.le

theorem gm_D_le_len (D : ContMetric) (Q : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (D.1 (Q a, Q b)) ≤ D.len Q a b := by
  rw [← gm_D_edist_eq]
  exact MetricGeometry.edist_le_curveLength (D.pt ∘ Q) hab

/-- **GM Lemma 4.16 from (4.39)** (proof l. 2572–2579): if the circle bound (4.39) of Lemma 4.22
holds, `D(𝕫, u; Y ∖ cl B_e(z)) ≤ t + B` on `∂B_ρ(z)`, then the points of a
`D(·,·;ℂ∖cl B_r(z))`-geodesic `Q` (`r ≤ e < ρ`) reached after `D`-length `t` are within
`2𝕣(B/S)^{1/χ'} + 4ρ` of each other. -/
theorem gm_L4_16_of_439 (D : ContMetric) {𝕫 z x : ℂ} {ρ e 𝕣 χ' S t s' r A T B : ℝ}
    {Q : ℝ → ℂ} {Y : Set ℂ} (he : 0 < e) (hρe : e < ρ) (h𝕣 : 0 < 𝕣) (hS : 0 < S) (ht : 0 ≤ t)
    (hB0 : 0 ≤ B) (hts' : t + B < s') (hfar : ρ < ‖𝕫 - z‖)
    (hcirc : ∀ u ∈ sphere z ρ, D.internal (Y \ closedBall z e) 𝕫 u ≤ ENNReal.ofReal (t + B))
    (hr : 0 < r) (hre : r ≤ e) (hQ : IsAvoidGeod D 𝕫 z r x Q T) (hfin : D.len Q 0 T ≠ ⊤)
    (hχ' : 0 < χ') (hA : 0 < A)
    (hHolLow : ∀ u ∈ ballM D 𝕫 s', ∀ v ∈ ballM D 𝕫 s', ‖u - v‖ ≤ A →
      (‖u - v‖ / 𝕣) ^ χ' * S ≤ D.1 (u, v))
    (hsmall : B < (A / 𝕣) ^ χ' * S) :
    ∀ s₁ ∈ Icc 0 T, ∀ s₂ ∈ Icc 0 T, ENNReal.ofReal t ≤ D.len Q 0 s₁ →
      ENNReal.ofReal t ≤ D.len Q 0 s₂ →
      ‖Q s₁ - Q s₂‖ ≤ 2 * (𝕣 * (B / S) ^ (1 / χ')) + 4 * ρ := by
  set δ := 𝕣 * (B / S) ^ (1 / χ') with hδdef
  have hρ0 : 0 < ρ := by linarith
  have hδ0 : 0 ≤ δ := by positivity
  obtain ⟨hT0, hQc, hQ0, hQT, hxs, hQout, hmin⟩ := id hQ
  have h0far : ρ < ‖Q 0 - z‖ := by rw [hQ0]; exact hfar
  have hTin : ‖Q T - z‖ < ρ := by
    rw [hQT, ← dist_eq_norm, mem_sphere.1 hxs]; linarith
  obtain ⟨τ, hτ, hτs, hafter⟩ := gm_exists_last_hit hT0 hQc h0far hTin
  have hV : Y \ closedBall z e ⊆ (ball z r)ᶜ := fun y hy hyb =>
    hy.2 (ball_subset_closedBall.trans (closedBall_subset_closedBall hre) hyb)
  have hlen : D.len Q 0 τ ≤ ENNReal.ofReal (t + B) :=
    (gm_avoid_len_le_internal hQ hfin hτ hV).trans (hcirc _ hτs)
  -- points before `τ` lie in `𝓑_{s'}`
  have hinB : ∀ s ∈ Icc 0 τ, Q s ∈ ballM D 𝕫 s' := by
    intro s hs
    show D.1 (𝕫, Q s) < s'
    have h1 := (gm_D_le_len D Q hs.1).trans ((MetricGeometry.curveLength_mono _ le_rfl hs.2).trans
      hlen)
    rw [hQ0, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
    linarith
  -- Claim A
  have hA' : ∀ s ∈ Icc 0 τ, ENNReal.ofReal t ≤ D.len Q 0 s → ‖Q s - Q τ‖ ≤ δ := by
    intro s hs hts
    have hsτ : D.len Q s τ ≤ ENNReal.ofReal B := by
      have hsplit := (MetricGeometry.curveLength_add (D.pt ∘ Q) hs.1 hs.2)
      have h2 : ENNReal.ofReal t + D.len Q s τ ≤ ENNReal.ofReal t + ENNReal.ofReal B := by
        calc ENNReal.ofReal t + D.len Q s τ ≤ D.len Q 0 s + D.len Q s τ := add_le_add hts le_rfl
          _ = D.len Q 0 τ := hsplit
          _ ≤ _ := by rw [← ENNReal.ofReal_add ht hB0]; exact hlen
      exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 h2
    have hD3 : ∀ s₃ ∈ Icc s τ, D.1 (Q s, Q s₃) ≤ B := by
      intro s₃ hs₃
      have h1 := (gm_D_le_len D Q hs₃.1).trans
        ((MetricGeometry.curveLength_mono _ le_rfl hs₃.2).trans hsτ)
      exact (ENNReal.ofReal_le_ofReal_iff hB0).1 h1
    have hmem : ∀ s₃ ∈ Icc s τ, Q s₃ ∈ ballM D 𝕫 s' := fun s₃ hs₃ =>
      hinB s₃ ⟨hs.1.trans hs₃.1, hs₃.2⟩
    have hnear : ‖Q s - Q τ‖ ≤ A := by
      by_contra hfar'
      push_neg at hfar'
      have hgc : ContinuousOn (fun u => ‖Q u - Q s‖) (Icc s τ) :=
        (continuous_norm.comp (continuous_id.sub continuous_const)).comp_continuousOn
          (hQc.mono fun u hu => ⟨hs.1.trans hu.1, hu.2.trans hτ.2⟩)
      have hiv := intermediate_value_Icc hs.2 hgc
      have hAin : A ∈ Icc ‖Q s - Q s‖ ‖Q τ - Q s‖ :=
        ⟨by rw [sub_self, norm_zero]; exact hA.le, by rw [norm_sub_rev]; exact hfar'.le⟩
      obtain ⟨s₃, hs₃, hs₃A⟩ := hiv hAin
      simp only at hs₃A
      have hlow := hHolLow (Q s) (hmem s ⟨le_rfl, hs.2⟩) (Q s₃) (hmem s₃ hs₃)
        (by rw [norm_sub_rev]; exact hs₃A.le)
      rw [norm_sub_rev, hs₃A] at hlow
      have := hD3 s₃ hs₃
      linarith
    have hlow := hHolLow (Q s) (hmem s ⟨le_rfl, hs.2⟩) (Q τ) (hmem τ ⟨hs.2, le_rfl⟩) hnear
    have hB : (‖Q s - Q τ‖ / 𝕣) ^ χ' ≤ B / S := by
      rw [le_div_iff₀ hS]; linarith [hD3 τ ⟨hs.2, le_rfl⟩]
    have hx0 : 0 ≤ ‖Q s - Q τ‖ / 𝕣 := by positivity
    have := Real.rpow_le_rpow (Real.rpow_nonneg hx0 _) hB (by positivity : 0 ≤ 1 / χ')
    rw [one_div, Real.rpow_rpow_inv hx0 hχ'.ne', ← one_div] at this
    rw [hδdef, ← div_le_iff₀' h𝕣]
    exact this
  -- every relevant point is within `δ + 2ρ` of `Q τ`
  have hall : ∀ s ∈ Icc 0 T, ENNReal.ofReal t ≤ D.len Q 0 s → ‖Q s - Q τ‖ ≤ δ + 2 * ρ := by
    intro s hs hts
    by_cases hsτ : s ≤ τ
    · linarith [hA' s ⟨hs.1, hsτ⟩ hts]
    · have h1 := hafter s ⟨not_le.1 hsτ, hs.2⟩
      rw [mem_ball, dist_eq_norm] at h1
      have h2 : ‖Q τ - z‖ = ρ := by rw [← dist_eq_norm]; exact mem_sphere.1 hτs
      have := norm_sub_le_norm_sub_add_norm_sub (Q s) z (Q τ)
      rw [norm_sub_rev z] at this
      linarith
  intro s₁ hs₁ s₂ hs₂ ht₁ ht₂
  have h1 := hall s₁ hs₁ ht₁
  have h2 := hall s₂ hs₂ ht₂
  have := norm_sub_le_norm_sub_add_norm_sub (Q s₁) (Q τ) (Q s₂)
  rw [norm_sub_rev (Q τ)] at this
  linarith

end LQGMetric.GM
