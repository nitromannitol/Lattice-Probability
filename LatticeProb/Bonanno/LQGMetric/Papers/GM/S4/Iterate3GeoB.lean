/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3GeoB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3GeoA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD3

/-!
# GM Lemma 4.20, the `Stab`-piece: deterministic locality of avoid-geodesics on `gmGeoSet` (D81, G2)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.19 (l. 2595–2601:
"a `D_h(·,·;ℂ∖cl B_r(z))`-geodesic is the same as a `D_h(·,·;𝓑^•_{s_{k+1}}∖cl B_r(z))`-geodesic")
and Lemma 4.20 (l. 2352–2354). Decision `decisions/DEC-81.md`, packet G2.

* `gm_avoid_len_le_internal_add`: an avoid-geodesic is not longer than any competitor made of a
  path in `V ⊆ ℂ ∖ B_r(z)` followed by a curve `Q'|_{[a,b]}` (concatenation, as
  `gm_avoid_len_le_internal`, GM l. 2575);
* `gm_avoidGeod_transfer_geo`: on `gmGeoSet` (GM (4.39)), with equal internal metrics on an open
  `U ⊇ 𝓑^•_{τc'}`, `D(·,·;ℂ∖cl B_r(z))`-geodesics from `𝕫` are the same for both metrics (GM
  l. 2595–2601; the exit argument of DEC-81 G2: a competitor leaving `U` has `d₂`-length `≥ s`
  before its last visit to `∂B_ρ(z)`, while (4.39) bounds the part before that visit by `θ < s`);
* `gm_stab_of_internal_eq_geo`: saturation of `gmStabSetN ∩ gmGeoSet` (the a.s. form of
  `Stab_{k,r}(z) ∩ F_k`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- **competitors through `V`** (GM l. 2575–2576): for an avoid-geodesic `Q` and a curve `Q'` on
`[a,b]` in `ℂ ∖ B_r(z)` ending at `x`, `len Q ≤ D(𝕫, Q'(a); V) + len Q'|_{[a,b]}` -/
theorem gm_avoid_len_le_internal_add {D : ContMetric} {𝕫 z x : ℂ} {r : ℝ} {Q : ℝ → ℂ} {T : ℝ}
    (hQ : IsAvoidGeod D 𝕫 z r x Q T) {Q' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hQ'c : ContinuousOn Q' (Icc a b)) (hQ'b : Q' b = x) (hQ'U : MapsTo Q' (Icc a b) (ball z r)ᶜ)
    {V : Set ℂ} (hV : V ⊆ (ball z r)ᶜ) :
    D.len Q 0 T ≤ D.internal V 𝕫 (Q' a) + D.len Q' a b := by
  obtain ⟨hT0, hQc, hQ0, hQT, hxs, hQout, hmin⟩ := hQ
  unfold ContMetric.internal MetricGeometry.internalEDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun γ => ?_
  set φ : ℝ → ℝ := fun s => s - a + 1 with hφ
  set Q'' : ℝ → ℂ := fun s => if s ≤ a then D.unpt (γ.1.extend (φ s)) else Q' s with hQ''
  have ha : a - 1 ≤ a := by linarith
  have hφ1 : φ a = 1 := by simp [hφ]
  have hφ0 : φ (a - 1) = 0 := by simp [hφ]
  have hmatch : D.unpt (γ.1.extend (φ a)) = Q' a := by rw [hφ1, Path.extend_one]; rfl
  have hcont : ContinuousOn Q'' (Icc (a - 1) b) :=
    MetricGeometry.continuousOn_concat (X := ℂ) ha hab hmatch
      ((D.continuous_unpt.comp (γ.1.continuous_extend.comp
        (continuous_id.sub continuous_const |>.add continuous_const))).continuousOn) hQ'c
  have hstart : Q'' (a - 1) = 𝕫 := by
    simp only [hQ'', if_pos ha, hφ0, Path.extend_zero]; rfl
  have hend : Q'' b = x := by
    by_cases hba : b ≤ a
    · have e : b = a := le_antisymm hba hab
      simp only [hQ'', if_pos hba]
      rw [e, hmatch, ← e, hQ'b]
    · simp only [hQ'', if_neg hba]; exact hQ'b
  have hmaps : MapsTo Q'' (Icc (a - 1) b) (ball z r)ᶜ := by
    intro s hs
    by_cases hst : s ≤ a
    · simp only [hQ'', if_pos hst]
      apply hV
      obtain ⟨u, hu⟩ : γ.1.extend (φ s) ∈ range γ.1 := by
        rw [← Path.extend_range]; exact mem_range_self _
      have h2 := γ.2 u
      rw [hu] at h2
      exact (D.mem_image_pt (z := D.unpt (γ.1.extend (φ s)))).1 h2
    · simp only [hQ'', if_neg hst]
      exact hQ'U ⟨(not_le.1 hst).le, hs.2⟩
  have hle := hmin Q'' (a - 1) b (by linarith) hcont hstart hend hmaps
  have hlenQ'' : D.len Q'' (a - 1) b = MetricGeometry.pathLength γ.1 + D.len Q' a b := by
    have heq : D.pt ∘ Q'' = fun s => if s ≤ a then γ.1.extend (φ s) else D.pt (Q' s) := by
      funext s; simp only [Function.comp_apply, hQ'']; split_ifs <;> rfl
    unfold ContMetric.len
    rw [heq, MetricGeometry.curveLength_concat ha hab (by rw [hφ1, Path.extend_one])]
    congr 1
    have := MetricGeometry.curveLength_comp_of_continuousOn_monotoneOn γ.1.extend
      (φ := φ) ha (by fun_prop) (fun u _ v _ huv => by simp only [hφ]; linarith)
    rw [show (fun s => γ.1.extend (φ s)) = γ.1.extend ∘ φ from rfl, this, hφ0, hφ1]
    rfl
  rw [hlenQ''] at hle
  exact hle

/-- **GM l. 2595–2601 on `gmGeoSet`**: avoid-geodesics of `d₁` are avoid-geodesics of `d₂` when
the internal metrics agree on an open `U ⊇ 𝓑^•_{τc'}(𝕫; d₁)` and `d₁` satisfies (4.39) in the
form `gmGeoSet` (`0 < r ≤ e < ρ < |𝕫 - z|`, `c ≤ c'`) -/
theorem gm_avoidGeod_transfer_geo {d₁ d₂ : ContMetric} (h₁ : d₁ ∈ lenSet) (h₂ : d₂ ∈ lenSet)
    {U : Set ℂ} (hU : IsOpen U) (heq : d₁.internal U = d₂.internal U) {𝕫 : ℂ} {R c c' : ℝ}
    {z : ℂ} {ρ e r : ℝ} (hc : 0 < c) (hcc' : c ≤ c') (hc' : 1 < c') (hR : 0 < R)
    (he : 0 < e) (hρe : e < ρ) (hr : 0 < r) (hre : r ≤ e)
    (hKU : filledBall d₁ 𝕫 (tauD d₁ 𝕫 R * c') ⊆ U) (hG : d₁ ∈ gmGeoSet 𝕫 R c z ρ e)
    {x : ℂ} {Q : ℝ → ℂ} {T : ℝ} (hQ : IsAvoidGeod d₁ 𝕫 z r x Q T) :
    IsAvoidGeod d₂ 𝕫 z r x Q T := by
  have l1 := isLength_of_mem_lenSet h₁
  have l2 := isLength_of_mem_lenSet h₂
  have hτpos := gm_tauD_pos d₁ 𝕫 hR
  obtain ⟨-, hball⟩ := gm_tk_congr l1 l2 hc' hU heq hτpos hKU
  have heqU : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y := fun x _ y _ => by
    rw [heq]
  set s := tauD d₁ 𝕫 R * c with hs_def
  have hs : 0 < s := mul_pos hτpos hc
  have hsc' : s ≤ tauD d₁ 𝕫 R * c' := mul_le_mul_of_nonneg_left hcc' hτpos.le
  have hfbU : filledBall d₁ 𝕫 s ⊆ U := (gm_filledBall_mono d₁ 𝕫 hsc').trans hKU
  have hbU : ballM d₁ 𝕫 s ⊆ U := subset_closure.trans (subset_union_left.trans hfbU)
  obtain ⟨θ, hθ, hsph⟩ := gm_geoSet_sphere h₁ he hρe hG
  obtain ⟨hρball, hgeo⟩ := gm_geoSet_avoidGeod h₁ he hρe hR hc hG
  have hV : (closedBall z e)ᶜ ⊆ (ball z r)ᶜ :=
    compl_subset_compl.2 (ball_subset_closedBall.trans (closedBall_subset_closedBall hre))
  have hsphB : sphere z ρ ⊆ ballM d₁ 𝕫 s := gm_geoSet_sphere_ballM h₁ he hρe hR hc hG
  obtain ⟨hT0, hQc, hQ0, hQT, hxs, hQout, hmin⟩ := id hQ
  have key : ∀ (Q' : ℝ → ℂ) (a b : ℝ), a ≤ b → ContinuousOn Q' (Icc a b) → Q' a = 𝕫 →
      Q' b = x → MapsTo Q' (Icc a b) (ball z r)ᶜ → d₁.len Q 0 T ≤ d₂.len Q' a b := by
    intro Q' a b hab hQ'c hQ'a hQ'b hQ'U
    by_cases hin : MapsTo Q' (Icc a b) U
    · rw [gm_len_eq_of_internal_eq heqU hQ'c hin]
      exact hmin Q' a b hab hQ'c hQ'a hQ'b hQ'U
    obtain ⟨t₀, ht₀, hout⟩ : ∃ t₀ ∈ Icc a b, Q' t₀ ∉ U := by
      simp only [MapsTo, not_forall] at hin
      obtain ⟨t₀, ht₀, h⟩ := hin
      exact ⟨t₀, ht₀, h⟩
    have hb_in : ‖Q' (a + (b - a)) - z‖ < ρ := by
      rw [add_sub_cancel, hQ'b, ← dist_eq_norm, mem_sphere.1 hxs]; linarith
    have ht₀far : ρ ≤ ‖Q' (a + (t₀ - a)) - z‖ := by
      rw [add_sub_cancel, ← dist_eq_norm]
      by_contra hlt
      exact hout (hfbU (hρball (not_le.1 hlt)))
    obtain ⟨τ₀, hτ₀, ht₀τ₀, hτs, hafter⟩ := gm_exists_last_hit' (Q := fun t => Q' (a + t))
      (T := b - a) (t₁ := t₀ - a) ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
      (hQ'c.comp (continuous_const.add continuous_id).continuousOn
        fun t ht => ⟨show a ≤ a + t by linarith [ht.1], show a + t ≤ b by linarith [ht.2]⟩)
      ht₀far hb_in
    set τ' := a + τ₀ with hτ'_def
    have hτ' : τ' ∈ Icc a b := ⟨by linarith [hτ₀.1], by linarith [hτ₀.2]⟩
    have hQτ' : Q' τ' ∈ sphere z ρ := hτs
    have htail : ∀ t ∈ Ioc τ' b, Q' t ∈ ball z ρ := fun t ht => by
      have := hafter (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simpa only [add_sub_cancel] using this
    have htailU : MapsTo Q' (Icc τ' b) U := fun t ht => by
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]; exact hbU (hsphB hQτ')
      · exact hfbU (hρball (htail t ⟨h, ht.2⟩))
    have hlen_tail : d₂.len Q' τ' b = d₁.len Q' τ' b :=
      gm_len_eq_of_internal_eq heqU (hQ'c.mono (Icc_subset_Icc hτ'.1 le_rfl)) htailU
    have hcomp : d₁.len Q 0 T ≤ d₁.internal (closedBall z e)ᶜ 𝕫 (Q' τ') + d₁.len Q' τ' b :=
      gm_avoid_len_le_internal_add hQ hτ'.2 (hQ'c.mono (Icc_subset_Icc hτ'.1 le_rfl)) hQ'b
        (hQ'U.mono_left (Icc_subset_Icc hτ'.1 le_rfl)) hV
    have ht₀τ : t₀ ≤ τ' := by linarith
    have hd₂ : s ≤ d₂.1 (𝕫, Q' t₀) := by
      by_contra hlt
      have hm : Q' t₀ ∈ ballM d₂ 𝕫 s := not_le.1 hlt
      rw [hball s hsc'] at hm
      exact hout (hbU hm)
    have hhead : ENNReal.ofReal s ≤ d₂.len Q' a τ' := by
      have := gm_D_le_len d₂ Q' ht₀.1
      rw [hQ'a] at this
      exact (ENNReal.ofReal_le_ofReal hd₂).trans
        (this.trans (MetricGeometry.curveLength_mono _ le_rfl ht₀τ))
    calc d₁.len Q 0 T ≤ d₁.internal (closedBall z e)ᶜ 𝕫 (Q' τ') + d₁.len Q' τ' b := hcomp
      _ ≤ ENNReal.ofReal s + d₁.len Q' τ' b := by
          gcongr
          exact (hsph _ hQτ').trans (ENNReal.ofReal_le_ofReal hθ.le)
      _ ≤ d₂.len Q' a τ' + d₂.len Q' τ' b := by rw [hlen_tail]; gcongr
      _ = d₂.len Q' a b := MetricGeometry.curveLength_add (d₂.pt ∘ Q') hτ'.1 hτ'.2
  refine ⟨hT0, hQc, hQ0, hQT, hxs, hQout, fun Q' a b hab hQ'c hQ'a hQ'b hQ'U => ?_⟩
  by_cases hfin : d₁.len Q 0 T = ⊤
  · have := key Q' a b hab hQ'c hQ'a hQ'b hQ'U
    rw [hfin, top_le_iff] at this
    rw [this]; exact le_top
  · have hQU : MapsTo Q (Icc 0 T) U := fun t ht => hfbU (hgeo r x Q T hr hre hQ hfin t ht)
    rw [gm_len_eq_of_internal_eq heqU hQc hQU]
    exact key Q' a b hab hQ'c hQ'a hQ'b hQ'U

/-- **G2, deterministic** (GM l. 2595–2601 with Lemma 4.6 (b)): `gmStabSetN ∩ gmGeoSet` (the
metric form of `Stab_{k,r}(z) ∩ F_k`) is saturated for agreement of internal metrics on an open
`U ⊇ 𝓑^•_{τc'}(𝕫; d₁)` -/
theorem gm_stab_of_internal_eq_geo {d₁ d₂ : ContMetric} (h₁ : d₁ ∈ lenSet) (h₂ : d₂ ∈ lenSet)
    {U : Set ℂ} (hU : IsOpen U) (heq : d₁.internal U = d₂.internal U) {𝕫 : ℂ}
    {R c₁ c cg c' lam1 lam4 ε ν 𝕣 : ℝ} {Rads : Set ℝ} {z : ℂ} {r ρ e : ℝ}
    (hc₁ : c₁ ≤ c) (hcc' : c ≤ c') (hcg : 0 < cg) (hcgc' : cg ≤ c') (hc' : 1 < c') (hR : 0 < R)
    (he : 0 < e) (hρe : e < ρ) (hr : 0 < r) (hre : r ≤ e)
    (hKU : filledBall d₁ 𝕫 (tauD d₁ 𝕫 R * c') ⊆ U)
    (H : d₁ ∈ gmStabSetN 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r ∩ gmGeoSet 𝕫 R cg z ρ e) :
    d₂ ∈ gmStabSetN 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r ∩ gmGeoSet 𝕫 R cg z ρ e := by
  obtain ⟨⟨hcand, hns⟩, hG⟩ := H
  have l1 := isLength_of_mem_lenSet h₁
  have l2 := isLength_of_mem_lenSet h₂
  have hτpos := gm_tauD_pos d₁ 𝕫 hR
  obtain ⟨hτ, hball⟩ := gm_tk_congr l1 l2 hc' hU heq hτpos hKU
  have heqU : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y := fun x _ y _ => by
    rw [heq]
  have hA : GMAgree d₁ d₂ U 𝕫 (tauD d₁ 𝕫 R * c') :=
    ⟨heqU, fun u hu => (hball u hu).symm, hKU, mul_pos hτpos (by linarith)⟩
  have hG₂ := gm_geoSet_of_internal_eq h₁ h₂ hU heq hcg hcgc' hc' hR hKU hG
  have hKU₂ : filledBall d₂ 𝕫 (tauD d₂ 𝕫 R * c') ⊆ U := by rw [hτ, hA.fb le_rfl]; exact hKU
  have hct : tauD d₁ 𝕫 R * c ≤ tauD d₁ 𝕫 R * c' := mul_le_mul_of_nonneg_left hcc' hτpos.le
  have hc₁t : tauD d₁ 𝕫 R * c₁ ≤ tauD d₁ 𝕫 R * c' :=
    mul_le_mul_of_nonneg_left (hc₁.trans hcc') hτpos.le
  refine ⟨⟨?_, ?_⟩, hG₂⟩
  · show (z, r) ∈ candSet (filledBall d₂ 𝕫 (tauD d₂ 𝕫 R * c)) lam1 lam4 ε ν 𝕣 Rads
    rw [hτ, hA.fb hct]; exact hcand
  · rw [hτ]
    rintro ⟨x₁, hx₁, x₂, hx₂, hne, ⟨y₁, hy₁, hv₁⟩, ⟨y₂, hy₂, hv₂⟩⟩
    have hB := hA.symm
    have tr : ∀ {y : ℂ}, gmOnAvoid d₂ 𝕫 z r y → gmOnAvoid d₁ 𝕫 z r y := by
      rintro y ⟨x, Q, T, hQ, hy⟩
      exact ⟨x, Q, T, gm_avoidGeod_transfer_geo h₂ h₁ hU heq.symm hcg hcgc' hc' hR he hρe
        hr hre hKU₂ hG₂ hQ, hy⟩
    exact hns ⟨x₁, gm_hitSet_transfer hB hc₁t hct hx₁, x₂, gm_hitSet_transfer hB hc₁t hct hx₂,
      hne, ⟨y₁, gm_arcOf_transfer hB hct hy₁, tr hv₁⟩, ⟨y₂, gm_arcOf_transfer hB hct hy₂, tr hv₂⟩⟩

end LQGMetric.GM
