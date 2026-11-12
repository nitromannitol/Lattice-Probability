/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodL422b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422
import LatticeProb.Bonanno.LQGMetric.Metric.Internal

/-!
# GM Lemma 4.22, deterministic form

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.22 (`lem-holder-balls0`,
l. 2527–2535), proof l. 2541–2565.

`gm_L4_22_det`: let `K = 𝓑^•_t(𝕫; D)` (`t = t_k`), `e = ε𝕣`, `λ = λ₄ > 1`, and let `z` satisfy
`λe ≤ dist(z, K) ≤ 2λe`, attained (GM: `z ∈ B_{2λ₄ε𝕣}(𝓑^•_{t_k}) ∖ B_{λ₄ε𝕣}(𝓑^•_{t_k})`;
`dist(z, K) = 2λe` is allowed since `𝒵_k`, GM (4.10), uses the closed range). Assume the
Hölder upper bound `D(u,v; B_{2|u−v|}(u)) ≤ (|u−v|/𝕣)^χ S` for `u ∈ ∂B_{2λe}(z)`,
`|u − v| ≤ e/2` (condition 3 of `ℰ_𝕣`, `S = 𝔠_𝕣e^{ξh_𝕣(0)}`), that `D`-geodesics exist (GM
S1.1) and the gap `t + N(e/(4𝕣))^χ S + (e/(2𝕣))^χ S < s'` (`s' = s_{k+1}`; GM (4.40) with
`β < χ`). Then, GM (4.39):
`sup_{u ∈ ∂B_{2λe}(z)} D(𝕫, u; 𝓑^•_{s'} ∖ cl B_e(z)) ≤ t + N (e/(4𝕣))^χ S`, `N = ⌈16πλ⌉`.

GM's steps: the circle `∂B_{2λe}(z)` meets `∂𝓑^•_t` (here: meets `cl 𝓑_t`, via a point of
`∂𝓑^•_t` within `2λe` of `z` and connectedness of `cl 𝓑_t`); a geodesic from `𝕫` to that point
stays in `𝓑^•_t`, which avoids `cl B_e(z)`; summing the Hölder bounds over the circle
(`gm_L4_22_circle`) first in `ℂ` (to see that the balls `B_{e/2}(u)` lie in `𝓑^•_{s'}`) and then
in `𝓑^•_{s'} ∖ cl B_e(z)`. Reading: `λ₄ > 1` (GM l. 2553: "since `λ₄ ≥ 1`"; strictness keeps
`𝓑^•_t` off the closed ball `cl B_e(z)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

theorem gm_D_edist_eq (D : ContMetric) (x y : ℂ) :
    edist (D.pt x) (D.pt y) = ENNReal.ofReal (D.1 (x, y)) := by
  rw [edist_dist]; rfl

theorem gm_D_le_internal (D : ContMetric) (V : Set ℂ) (x y : ℂ) :
    ENNReal.ofReal (D.1 (x, y)) ≤ D.internal V x y := by
  rw [← gm_D_edist_eq]; exact MetricGeometry.edist_le_internalEDist _ _ _

/-- a geodesic of length `L` inside `V` bounds the internal distance in `V` by `L` -/
theorem gm_internal_le_of_geod (D : ContMetric) {P : ℝ → ℂ} {L : ℝ} {x y : ℂ}
    (hP : IsGeodesicL D P L x y) {V : Set ℂ} (hV : MapsTo P (Icc 0 L) V) :
    D.internal V x y ≤ ENNReal.ofReal L := by
  have hc : ContinuousOn (D.pt ∘ P) (Icc 0 L) := by
    intro s hs
    rw [Metric.continuousWithinAt_iff]
    intro δ hδ
    refine ⟨δ, hδ, fun {u} hu hus => ?_⟩
    show D.1 (P u, P s) < δ
    rw [hP.2.2.2 u hu s hs, abs_sub_comm]
    exact hus
  have h := MetricGeometry.internalEDist_le_curveLength (Y := D.pt '' V) hP.1 hc
    (fun u hu => mem_image_of_mem _ (hV hu))
  simp only [Function.comp_apply] at h
  rw [hP.2.1, hP.2.2.1] at h
  exact h.trans_eq (gm_len_geodL hP ⟨hP.1, le_rfl⟩)

/-- **GM Lemma 4.22, deterministic form** (l. 2527–2565). -/
theorem gm_L4_22_det (D : ContMetric) {𝕫 z : ℂ} {lam e 𝕣 χ S t s' : ℝ}
    (hlam : 1 < lam) (he : 0 < e) (h𝕣 : 0 < 𝕣) (hχ : 0 < χ) (hS : 0 ≤ S) (ht : 0 < t)
    (hL : D.IsLength) (hbd : Bornology.IsBounded (ballM D 𝕫 t))
    (hgeod : ∀ y : ℂ, ∃ P : ℝ → ℂ, IsGeodesicL D P (D.1 (𝕫, y)) 𝕫 y)
    (hz1 : lam * e ≤ infDist z (filledBall D 𝕫 t))
    (hz2 : ∃ q ∈ filledBall D 𝕫 t, dist z q ≤ 2 * lam * e) (hfar : 2 * lam * e < ‖𝕫 - z‖)
    (hHol : ∀ u ∈ sphere z (2 * lam * e), ∀ v : ℂ, u ≠ v → ‖u - v‖ ≤ e / 2 →
      D.internal (ball u (2 * ‖u - v‖)) u v ≤ ENNReal.ofReal ((‖u - v‖ / 𝕣) ^ χ * S))
    (hgap : t + ⌈8 * Real.pi * (2 * lam * e) / e⌉₊ * ((e / 4 / 𝕣) ^ χ * S) +
      (e / 2 / 𝕣) ^ χ * S < s') :
    ∀ u ∈ sphere z (2 * lam * e), D.internal (filledBall D 𝕫 s' \ closedBall z e) 𝕫 u ≤
      ENNReal.ofReal (t + ⌈8 * Real.pi * (2 * lam * e) / e⌉₊ * ((e / 4 / 𝕣) ^ χ * S)) := by
  set ρ := 2 * lam * e with hρdef
  set K := filledBall D 𝕫 t with hKdef
  set N := ⌈8 * Real.pi * ρ / e⌉₊
  have hρ : 2 * e ≤ ρ := by rw [hρdef]; nlinarith
  have hρ0 : 0 < ρ := by linarith
  have hKc : IsClosed K := gm_filledBall_isClosed D 𝕫 t
  have h𝕫B : 𝕫 ∈ ballM D 𝕫 t := jb_mem_ballM D 𝕫 t ht
  have hBK : closure (ballM D 𝕫 t) ⊆ K := fun x hx => Or.inl hx
  have hKne : K.Nonempty := ⟨𝕫, hBK (subset_closure h𝕫B)⟩
  -- `K` avoids `cl B_e(z)`
  have hKfar : ∀ x ∈ K, lam * e ≤ ‖x - z‖ := fun x hx => by
    have := infDist_le_dist_of_mem (x := z) hx
    rw [dist_comm, dist_eq_norm] at this; linarith
  have hKV : ∀ x ∈ K, x ∉ closedBall z e := fun x hx hxb => by
    rw [mem_closedBall, dist_eq_norm] at hxb
    have := hKfar x hx
    nlinarith
  -- a point `p ∈ ∂K` with `|p − z| < ρ`
  obtain ⟨q, hqK, hqz⟩ := hz2
  have hzK : z ∉ K := fun hz => by
    rw [infDist_zero_of_mem hz] at hz1; nlinarith
  have hseg : segment ℝ z q ⊆ closedBall z (dist z q) :=
    (convex_closedBall z _).segment_subset (mem_closedBall_self dist_nonneg)
      (by rw [mem_closedBall, dist_comm])
  obtain ⟨p, hpseg, hpfr⟩ := jb_inter_frontier_nonempty hKc (convex_segment z q).isPreconnected
    (left_mem_segment ℝ z q) hzK (right_mem_segment ℝ z q) hqK
  have hpB : p ∈ closure (ballM D 𝕫 t) := jb_frontier_subset_closure hbd hpfr
  have hpz : p ∈ closedBall z ρ := by
    have := hseg hpseg
    rw [mem_closedBall] at this ⊢; linarith
  -- a point `u₀ ∈ cl 𝓑_t` on the circle
  have h𝕫out : 𝕫 ∉ closedBall z ρ := by
    rw [mem_closedBall, dist_eq_norm]; linarith
  obtain ⟨u₀, hu₀B, hu₀fr⟩ := jb_inter_frontier_nonempty (isClosed_closedBall (x := z) (ε := ρ))
    (jb_isPreconnected_ballM D 𝕫 t hL).closure (subset_closure h𝕫B) h𝕫out hpB hpz
  rw [frontier_closedBall z hρ0.ne'] at hu₀fr
  -- the geodesic from `𝕫` to `u₀` stays in `K`
  obtain ⟨P, hP⟩ := hgeod u₀
  set L := D.1 (𝕫, u₀)
  have hLt : L ≤ t := gm_closure_ballM_subset D 𝕫 t hu₀B
  have hPK : MapsTo P (Icc 0 L) K := by
    intro v hv
    rcases lt_or_eq_of_le hv.2 with hvL | hvL
    · refine hBK (subset_closure ?_)
      show D.1 (𝕫, P v) < t
      rw [gm_geodL_dist hP hv]; linarith
    · rw [hvL, hP.2.2.1]; exact hBK hu₀B
  have h0 : ∀ Y : Set ℂ, K ⊆ Y → D.internal (Y \ closedBall z e) 𝕫 u₀ ≤ ENNReal.ofReal t :=
    fun Y hY => (gm_internal_le_of_geod D hP (V := Y \ closedBall z e) fun v hv => ⟨hY (hPK hv), hKV _ (hPK hv)⟩).trans
      (ENNReal.ofReal_le_ofReal hLt)
  have hHol4 : ∀ u ∈ sphere z ρ, ∀ v ∈ sphere z ρ, u ≠ v → ‖u - v‖ ≤ e / 4 →
      D.internal (ball u (2 * ‖u - v‖)) u v ≤ ENNReal.ofReal ((‖u - v‖ / 𝕣) ^ χ * S) :=
    fun u hu v _ huv hd => hHol u hu v huv (by linarith)
  have hc0 : 0 ≤ (e / 4 / 𝕣) ^ χ * S := by positivity
  have hc1 : 0 ≤ (e / 2 / 𝕣) ^ χ * S := by positivity
  -- Step 1: in `ℂ`
  have hstep1 := gm_L4_22_circle D he hρ h𝕣 hχ hS ht.le hHol4 (Y := univ)
    (fun _ _ => subset_univ _) hu₀fr (h0 univ (subset_univ _))
  have hD1 : ∀ u ∈ sphere z ρ, D.1 (𝕫, u) ≤ t + N * ((e / 4 / 𝕣) ^ χ * S) := fun u hu =>
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 ((gm_D_le_internal D _ _ _).trans
      (hstep1 u hu))
  -- Step 2: the balls `B_{e/2}(u)` lie in `𝓑_{s'}`
  have hY : ∀ u ∈ sphere z ρ, ball u (e / 2) ⊆ filledBall D 𝕫 s' := by
    intro u hu x hx
    refine Or.inl (subset_closure ?_)
    show D.1 (𝕫, x) < s'
    have hux : D.1 (u, x) ≤ (e / 2 / 𝕣) ^ χ * S := by
      by_cases hxu : u = x
      · rw [← hxu, D.2.self_eq_zero]; exact hc1
      · have hd : ‖u - x‖ < e / 2 := by rw [← dist_eq_norm, dist_comm]; exact hx
        have h1 := (gm_D_le_internal D _ _ _).trans (hHol u hu x hxu hd.le)
        rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ hS)
        exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hd.le h𝕣.le) hχ.le
    have := D.2.triangle 𝕫 u x
    have := hD1 u hu
    linarith
  -- Step 3: in `𝓑^•_{s'} ∖ cl B_e(z)`
  have hKs' : K ⊆ filledBall D 𝕫 s' := gm_filledBall_mono D 𝕫 (by
    have : 0 ≤ N * ((e / 4 / 𝕣) ^ χ * S) := by positivity
    linarith)
  exact gm_L4_22_circle D he hρ h𝕣 hχ hS ht.le hHol4 hY hu₀fr (h0 _ hKs')

end LQGMetric.GM
