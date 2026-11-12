/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eExt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eL413c
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eStep3

/-!
# GM (4.41) on `ℰ_𝕣` from Step 3 and the events `G_y` (proof of Prop. 4.12, l. 2236–2244)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, l. 2236–2244 (contrapositive of
Lemma 4.13 with `(ε^κ/2)^{χ'/χ}` in place of `ε`) and L4.15 Step 3 (∗), item A (l. 2160–2170).

`p412e_ext_of_noHit` (deterministic): let `K = 𝓑^•_t` (`t = t_k`), `P` a geodesic from `𝕫` with
`P(t) ∈ I`, `ε₂ = 2ε'^{χ/χ'}𝕣`, `F ⊇ cl B_{16ε₂}(K)` (`F = 𝓑^•_{s_{k+1}}`, GM l. 2240) with
`P(b) ∉ F`, `E ⊇` the endpoints of `I`, and `z_e` with the Step 3 property (∗) (`p412eGoodZ`). If
`P((t, b])` avoids every `B_{17ε₂}(z_e)` (GM's event `G_y`, item A, with `17` instead of `16`:
the hit of `cl B_{2r}(z_e)`, `2r ≤ 16ε₂`, may occur at time `t`, and continuity of `P` moves it
into `(t, b]`), then (4.41): `d^{ℂ∖K}(P(u₀), v) ≥ ε'𝕣` for all `P(u₀) ∉ K`, `v ∈ ∂K ∖ I`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM (4.41)** (l. 2236–2244) from (∗) and `G_y`, deterministic on condition 3 of `ℰ_𝕣` -/
theorem p412e_ext_of_noHit {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (ha : 0 < a) (hχ : 0 < R.χ) (hχχ : R.χ ≤ R.χ') (hc : 0 < R.c 𝕣)
    {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a) (hL : (D (h ω)).IsLength) {P : ℝ → ℂ} {L : ℝ} {𝕫 y : ℂ}
    (hP : IsGeodesicL (D (h ω)) P L 𝕫 y) {t : ℝ} (ht : 0 < t) (htL : t < L)
    (hbd : Bornology.IsBounded (ballM (D (h ω)) 𝕫 t)) (hy : y ∉ filledBall (D (h ω)) 𝕫 t)
    {I : Set ℂ} (hPI : P t ∈ I) {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1) (hεa : ε' ≤ a)
    (hsmall : ε' ^ R.χ < a ^ R.χ')
    (hKreg : cthickening (ε' * 𝕣) (filledBall (D (h ω)) 𝕫 t) ⊆ regRegion R 𝕣)
    (hreg : ∀ u ∈ Icc t L, u ≤ t + scaleFac R.ξ R.c (h ω) 𝕣 0 * ε' ^ R.χ →
      P u ∈ regRegion R 𝕣)
    {F : Set ℂ} (hF : IsClosed F) (hFb : Bornology.IsBounded F) (hFc : IsConnected Fᶜ)
    (hKF : cthickening (16 * (2 * ε' ^ (R.χ / R.χ') * 𝕣)) (filledBall (D (h ω)) 𝕫 t) ⊆ F)
    {b : ℝ} (htb : t < b) (hbL : b ≤ L) (hPb : P b ∉ F) {E : Set ℂ}
    (hE : closure I ∩ closure (frontier (filledBall (D (h ω)) 𝕫 t) \ I) ⊆ E) {zf : ℂ → ℂ}
    (hz : ∀ e ∈ E, p412eGoodZ (filledBall (D (h ω)) 𝕫 t) e (zf e) (2 * ε' ^ (R.χ / R.χ') * 𝕣))
    (hnohit : ∀ e ∈ E, ∀ u ∈ Ioc t b, P u ∉ ball (zf e) (17 * (2 * ε' ^ (R.χ / R.χ') * 𝕣))) :
    ∀ u₀ ∈ Icc 0 L, P u₀ ∉ filledBall (D (h ω)) 𝕫 t →
      ∀ v ∈ frontier (filledBall (D (h ω)) 𝕫 t) \ I,
        ENNReal.ofReal (ε' * 𝕣) ≤ dU (filledBall (D (h ω)) 𝕫 t)ᶜ (P u₀) v := by
  intro u₀ hu₀ hu₀K v hv
  by_contra hlt
  push_neg at hlt
  obtain ⟨X, hXK, hXc, hXd, v₀, hv₀, hb, hPV, e, he1, he2, heV⟩ := p412e_GML4_13 h𝕣 ha hχ hχχ hc
    hω hL hP ht htL hbd hy hPI hu₀ hu₀K hv.1 hv.2 hε0 hε1 hεa hsmall hlt hKreg hreg
  set ε₂ := 2 * ε' ^ (R.χ / R.χ') * 𝕣 with hε₂def
  have hε₂ : 0 < ε₂ := by positivity
  have heE : e ∈ E := hE ⟨he1, he2⟩
  obtain ⟨r, hr, hr8, H⟩ := hz e heE
  have hPc := gm_geodL_continuousOn hP
  have hPc' : ContinuousOn P (Icc t b) := hPc.mono fun u hu => ⟨ht.le.trans hu.1, hu.2.trans hbL⟩
  obtain ⟨s, hs, hsB⟩ := H F hF hFb hFc hKF X v₀ P t b hXK hXc hXd hv₀ hb heV hPV
    (gm_geod_mem_frontier hP ht htL hy) htb hPc'
    (fun s hs => p412e_geod_after hP ht htL hy s ⟨hs.1, hs.2.trans hbL⟩) hPb
  rw [mem_closedBall] at hsB
  rcases eq_or_lt_of_le hs.1 with hst | hst
  · -- the hit is at time `t`: move it into `(t, b]` by continuity
    rw [← hst] at hsB
    obtain ⟨δ, hδ, hδP⟩ := Metric.continuousWithinAt_iff.1 (hPc' t ⟨le_rfl, htb.le⟩) ε₂ hε₂
    set u := min (t + δ / 2) b
    have hu : u ∈ Ioc t b := ⟨lt_min (by linarith) htb, min_le_right _ _⟩
    have hdu : dist u t < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hu.1])]
      linarith [min_le_left (t + δ / 2) b]
    have h1 := hδP ⟨hu.1.le, hu.2⟩ hdu
    refine hnohit e heE u hu (mem_ball.2 ?_)
    linarith [dist_triangle (P u) (P t) (zf e)]
  · exact hnohit e heE s ⟨hst, hs.2⟩ (mem_ball.2 (by linarith))

end LQGMetric.GM
