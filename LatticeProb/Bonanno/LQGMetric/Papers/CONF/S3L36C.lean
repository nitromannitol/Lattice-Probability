/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36In

/-!
# CONF Lemma 3.6, Step 2: property A for one good radius (deterministic)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6, Step 2 (C:1388–1410), with
D108 (b) (`decisions/DEC-108.md`).

`conf36_propA_core`: let `r ≥ ε𝕣 =: e` be a radius at which, for the grid point `z` within `e`
of `x ∈ 𝓑 := 𝓑^•_τ` and the set `T` of squares of `𝒮^z_{δr}(𝔸_{3r,4r}(z))` meeting `𝓑`
(C:1344, `Ũ^r = confU r δ z T`), conditions 1, 2 of `E^{Ũ^r}_r(z)` and the event (3.9′) hold.
Assume `𝓑` meets `𝔸_{3r,4r}(z)` or lies in `cl B_{3r}(z)` (true when `𝓑` is connected, which
holds a.s.; CONF C:1393 uses it in "`𝔸_{3ρ̃,4ρ̃}(z)` intersects `𝓑^•_τ`"). If
`6r + e ≤ R ≤ diam 𝓑` and `y ∉ B_R(𝓑)`, no `D`-geodesic from the centre to `y` enters
`B_e(x) ∖ 𝓑` (C:1390–1410).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- a filled ball of non-positive radius is empty -/
theorem conf36_pos_of_mem_filledBall {d : ContMetric} {z₀ x : ℂ} {τ : ℝ}
    (hx : x ∈ filledBall d z₀ τ) : 0 < τ := by
  by_contra hτ
  have hb : ballM d z₀ τ = ∅ := by
    ext w
    simp only [ballM, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact (not_lt.1 hτ).trans (dist_nonneg (x := d.pt z₀) (y := d.pt w))
  rcases hx with h | ⟨-, h⟩
  · rw [hb, closure_empty] at h; exact h
  · rw [hb, closure_empty, compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ] at h
    exact GM.jb_not_isBounded_lt_norm 0 (h.subset (subset_univ _))

/-- every point lies in a grid square -/
theorem conf36_mem_confSq {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    w ∈ confSq ε z (⌊(w.re - z.re) / ε⌋, ⌊(w.im - z.im) / ε⌋) := by
  have a1 := Int.floor_le ((w.re - z.re) / ε)
  have a2 := Int.lt_floor_add_one ((w.re - z.re) / ε)
  have b1 := Int.floor_le ((w.im - z.im) / ε)
  have b2 := Int.lt_floor_add_one ((w.im - z.im) / ε)
  rw [le_div_iff₀ hε] at a1 b1
  rw [div_lt_iff₀ hε] at a2 b2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [] <;> linarith

/-- the `e`-diameter of a subset of `cl B_ρ(z)` is at most `2ρ` -/
theorem conf36_ediam_le {A : Set ℂ} {z : ℂ} {ρ : ℝ} (hA : A ⊆ closedBall z ρ) :
    Metric.ediam A ≤ ENNReal.ofReal (2 * ρ) := by
  refine Metric.ediam_le fun a ha b hb => ?_
  have h1 := hA ha
  have h2 := hA hb
  rw [mem_closedBall] at h1 h2
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  linarith [dist_triangle a z b, dist_comm z b]

/-- the hypothesis `hnear` of `conf36_geod_kill` from `L36Step2Input` (CONF (3.21), C:1396) -/
theorem conf36_hnear_gen {p : CONFParams}
    {Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop} (hIn : L36Step2Input p Fat)
    {d : ContMetric} {z₀ z : ℂ} {τ r s : ℝ} (hr : 0 < r) (hs : 0 < s) {T : Finset (ℤ × ℤ)}
    (hT : ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)))
    (hTB : ∀ k ∈ T, (confSq (p.δ * r) z k ∩ filledBall d z₀ τ).Nonempty)
    (hcov : ∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
      (confSq (p.δ * r) z k ∩ filledBall d z₀ τ).Nonempty → k ∈ T) (hTne : T.Nonempty)
    (h2 : ∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
      internalDiam d (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
        ENNReal.ofReal (p.c / 100 * s))
    (hfat : Fat d s r z T) :
    ∀ w ∈ (annulus z (3 * r) (4 * r) : Set ℂ), w ∉ filledBall d z₀ τ →
      ∃ b, d.1 (z₀, b) ≤ τ ∧ d.1 (w, b) < p.c * s := by
  intro w hw hwB
  obtain ⟨b, hb, hint⟩ := hIn d s r z T _ hs hr hT hTB hcov hTne h2 hfat w hw
  obtain ⟨b', hb'f, hb'⟩ := conf36_exists_frontier_lt (GM.gm_filledBall_isClosed d z₀ τ) hwB hb
    hint
  exact ⟨b', conf36_dist_le_of_frontier hb'f, (ENNReal.ofReal_lt_ofReal_iff'.1 hb').1⟩

/-- **CONF Lemma 3.6, Step 2** (C:1388–1410) for one good radius `r` (see module docstring) -/
theorem conf36_propA_core {p : CONFParams}
    {Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop} (hIn : L36Step2Input p Fat)
    {d : ContMetric} {z₀ z x y : ℂ} {τ r e s L u : ℝ} {Q : ℝ → ℂ} (hδ : 0 < p.δ)
    (he : 0 < e) (her : e ≤ r) (hs : 0 < s)
    (hx : x ∈ filledBall d z₀ τ) (hxz : ‖x - z‖ ≤ e) {T : Finset (ℤ × ℤ)}
    (hT : ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)))
    (hTB : ∀ k ∈ T, (confSq (p.δ * r) z k ∩ filledBall d z₀ τ).Nonempty)
    (hcov : ∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
      (confSq (p.δ * r) z k ∩ filledBall d z₀ τ).Nonempty → k ∈ T)
    (h1 : ENNReal.ofReal (p.c * s) ≤ setDist d (sphere z (2 * r)) (sphere z (3 * r)))
    (h2 : ∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
      internalDiam d (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
        ENNReal.ofReal (p.c / 100 * s))
    (hfat : Fat d s r z T)
    (hconn : (filledBall d z₀ τ ∩ (annulus z (3 * r) (4 * r) : Set ℂ)).Nonempty ∨
      filledBall d z₀ τ ⊆ closedBall z (3 * r))
    {R : ℝ≥0∞} (hR6 : ENNReal.ofReal (6 * r + e) ≤ R)
    (hRd : R ≤ Metric.ediam (filledBall d z₀ τ)) (hy : y ∉ enbhd R (filledBall d z₀ τ))
    (hQ : IsGeodesicL d Q L z₀ y) (hu : u ∈ Icc 0 L)
    (hQu : Q u ∈ ball x e \ filledBall d z₀ τ) : False := by
  have hτ : 0 < τ := conf36_pos_of_mem_filledBall hx
  have hr : 0 < r := he.trans_le her
  rcases hconn with ⟨w, hwB, hwA⟩ | hsub
  swap
  · have := (hR6.trans hRd).trans (conf36_ediam_le hsub)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    linarith
  have hδr : 0 < p.δ * r := by positivity
  have hTne : T.Nonempty := by
    have hk := conf36_mem_confSq hδr z w
    exact ⟨_, hcov _ ⟨w, hk, hwA⟩ ⟨w, hk, hwB⟩⟩
  have hnear := conf36_hnear_gen hIn hr hs hT hTB hcov hTne h2 hfat
  have hyx : 6 * r + e ≤ ‖y - x‖ := by
    have h' : R ≤ Metric.infEDist y (filledBall d z₀ τ) := not_lt.1 hy
    have h'' := (hR6.trans h').trans (Metric.infEDist_le_edist_of_mem hx)
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg, dist_eq_norm] at h''
    exact h''
  have hyz : 4 * r ≤ ‖y - z‖ := by
    have e1 : ‖x - z‖ = ‖z - x‖ := norm_sub_rev _ _
    linarith [norm_sub_le_norm_sub_add_norm_sub y z x]
  have hQuz : ‖Q u - z‖ < 2 * r := by
    have h0 : ‖Q u - x‖ < e := by rw [← dist_eq_norm]; exact hQu.1
    linarith [norm_sub_le_norm_sub_add_norm_sub (Q u) x z]
  exact conf36_geod_kill hτ hr hQ (fun hyB => hy (by
      show Metric.infEDist y (filledBall d z₀ τ) < R
      rw [Metric.infEDist_zero_of_mem hyB]
      exact lt_of_lt_of_le (by positivity) hR6)) hyz h1 hnear hu hQuz hQu.2

end LQGMetric.CONF
