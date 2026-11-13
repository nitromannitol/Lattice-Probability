/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13EdgeGrad at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13Energy

/-!
# The gradient-weighted edge estimate of [18] Lemma 3.3 along bounded-convexity paths

Source: the proof of [18] Lemma 3.3 : for adjacent `x, y` and points
`z ∈ H_x ∩ D`, `w ∈ H_y ∩ D`, a path in `D` of length `≤ C(diam H_x + diam H_y)` joins them and, `∇f` being
Lipschitz, `|f^ε(x) − f^ε(y)| ≲ |∇f(·)| diam + C Λ diam²`; summing over the edges at each vertex gives (3.14). Here
`f` is only differentiable on `D` and the reference points of the boundary vertices lie on `∂D` (the maximizers of
(1.6)), so the estimate is proved on `D̄` by continuity, with the gradient evaluated at a point of `H_x ∩ D`.

* `t13_le_on_closure` — a bound `|f a − f b| ≤ Φ(a, b)` with `Φ` continuous extends from `D` to `D̄`;
* `t13_abs_sub_le_grad` — for `C`-bounded convex `D`, `z ∈ D`, `a, b ∈ D̄`:
  `|f a − f b| ≤ C|a − b| (|∇f(z)| + Λ(|a − z| + C|a − b|))`;
* `t13_sq_le_of_two_bounds` — the elementary squared form of the symmetric edge bound;
* **`t13_energy_le_grad`** — `Energy(f_ε; G(D)) ≤ ∑_{x ∈ V(D)} deg(x) (3C² diam(H_x)² |∇f(z_x)|² + 24 C²Λ²(1+C)²
  diam(H_x)⁴)` for any choice of `z_x ∈ H_x ∩ D`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal Classical

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3 LFMultigraph Harmonic

/-- **A continuous bound extends from `D` to `D̄`** for `f` continuous on `D̄`. -/
theorem t13_le_on_closure {D : Set ℂ} {f : ℂ → ℝ} (hfc : ContinuousOn f (closure D)) {Φ : ℂ → ℂ → ℝ}
    (hΦ : Continuous fun q : ℂ × ℂ => Φ q.1 q.2) (h : ∀ a ∈ D, ∀ b ∈ D, |f a - f b| ≤ Φ a b) :
    ∀ a ∈ closure D, ∀ b ∈ closure D, |f a - f b| ≤ Φ a b := by
  intro a ha b hb
  obtain ⟨zs, hzD, hzlim⟩ := mem_closure_iff_seq_limit.1 ha
  obtain ⟨ws, hwD, hwlim⟩ := mem_closure_iff_seq_limit.1 hb
  have hfz : Tendsto (fun n => f (zs n)) atTop (𝓝 (f a)) :=
    (hfc a ha).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hzlim, Eventually.of_forall fun n => subset_closure (hzD n)⟩)
  have hfw : Tendsto (fun n => f (ws n)) atTop (𝓝 (f b)) :=
    (hfc b hb).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hwlim, Eventually.of_forall fun n => subset_closure (hwD n)⟩)
  have hΦlim : Tendsto (fun n => Φ (zs n) (ws n)) atTop (𝓝 (Φ a b)) :=
    (hΦ.tendsto (a, b)).comp (hzlim.prodMk_nhds hwlim)
  exact le_of_tendsto_of_tendsto' (hfz.sub hfw).abs hΦlim fun n => h _ (hzD n) _ (hwD n)

/-- **The gradient estimate along a bounded-convexity path**, on `D̄`: for `z ∈ D` and `a, b ∈ D̄`,
`|f a − f b| ≤ C|a − b| (|∇f(z)| + Λ(|a − z| + C|a − b|))`. -/
theorem t13_abs_sub_le_grad {D : Set ℂ} (hDo : IsOpen D) {C : ℝ} (hC0 : 0 ≤ C)
    (hbc : BoundedConvexityWith C D) {f : ℂ → ℝ} (hf : DifferentiableOn ℝ f D) {Λ : ℝ≥0}
    (hΛ : LipschitzOnWith Λ (fderiv ℝ f) D) (hfc : ContinuousOn f (closure D)) (z : ℂ) (hz : z ∈ D) :
    ∀ a ∈ closure D, ∀ b ∈ closure D,
      |f a - f b| ≤ C * dist a b * (‖fderiv ℝ f z‖ + Λ * (dist a z + C * dist a b)) := by
  refine t13_le_on_closure hfc (by fun_prop) fun a ha b hb => ?_
  obtain ⟨p, hpc, hp0, hp1, hpD, hlen⟩ := hbc a ha b hb
  set ℓ := C * dist a b with hℓdef
  have hℓ : 0 ≤ ℓ := mul_nonneg hC0 dist_nonneg
  have hpa : ∀ t ∈ Icc (0 : ℝ) 1, dist (p t) a ≤ ℓ := by
    intro t ht
    have h1 := eVariationOn.edist_le p (left_mem_Icc.2 zero_le_one) ht
    rw [hp0] at h1
    have h2 := h1.trans hlen
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hℓ, dist_comm] at h2
    exact h2
  -- the bound with an extra margin `η`
  have key : ∀ η : ℝ, 0 < η →
      |f a - f b| ≤ (‖fderiv ℝ f z‖ + Λ * (dist a z + ℓ + η)) * ℓ := by
    intro η hη
    set R := dist a z + ℓ + η with hR
    have hU : IsOpen (D ∩ ball z R) := hDo.inter isOpen_ball
    set G : ℝ := ‖fderiv ℝ f z‖ + Λ * R with hG
    have hG0 : 0 ≤ G := by positivity
    have hGb : ∀ u ∈ D ∩ ball z R, ‖fderiv ℝ f u‖₊ ≤ G.toNNReal := by
      intro u hu
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hG0]
      have hd := hΛ.dist_le_mul u hu.1 z hz
      have hur : dist u z < R := mem_ball.1 hu.2
      calc ‖fderiv ℝ f u‖ ≤ ‖fderiv ℝ f z‖ + dist (fderiv ℝ f u) (fderiv ℝ f z) := by
            rw [dist_eq_norm]
            have := norm_add_le (fderiv ℝ f z) (fderiv ℝ f u - fderiv ℝ f z)
            rwa [add_sub_cancel] at this
        _ ≤ ‖fderiv ℝ f z‖ + Λ * dist u z := by gcongr
        _ ≤ G := by rw [hG]; gcongr
    have hmaps : MapsTo p (Icc 0 1) (D ∩ ball z R) := by
      intro t ht
      refine ⟨hpD ht, mem_ball.2 ?_⟩
      calc dist (p t) z ≤ dist (p t) a + dist a z := dist_triangle _ _ _
        _ ≤ ℓ + dist a z := by gcongr; exact hpa t ht
        _ < R := by rw [hR]; linarith
    have h := t13_abs_sub_le_of_path hU (hf.mono inter_subset_left) hGb zero_le_one hpc hmaps hℓ hlen
    rw [hp0, hp1, abs_sub_comm, Real.coe_toNNReal _ hG0] at h
    exact h
  -- let the margin tend to zero
  have hlim : Tendsto (fun η : ℝ => (‖fderiv ℝ f z‖ + Λ * (dist a z + ℓ + η)) * ℓ) (𝓝[>] 0)
      (𝓝 ((‖fderiv ℝ f z‖ + Λ * (dist a z + ℓ + 0)) * ℓ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by fun_prop : Continuous fun η : ℝ =>
      (‖fderiv ℝ f z‖ + Λ * (dist a z + ℓ + η)) * ℓ).continuousAt.tendsto
  have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => key η hη)
  calc |f a - f b| ≤ (‖fderiv ℝ f z‖ + Λ * (dist a z + ℓ + 0)) * ℓ := this
    _ = C * dist a b * (‖fderiv ℝ f z‖ + Λ * (dist a z + C * dist a b)) := by rw [hℓdef]; ring

/-- The elementary squared form of the symmetric edge bound: if `|Δ| ≤ C s (g_x + K s)` and `|Δ| ≤ C s (g_y + K s)`
with `s = d_x + d_y`, then `Δ² ≤ 3C²d_x²g_x² + 3C²d_y²g_y² + 24C²K²(d_x⁴ + d_y⁴)`. -/
theorem t13_sq_le_of_two_bounds {Δ C K dx dy gx gy : ℝ} (hC : 0 ≤ C) (hdx : 0 ≤ dx) (hdy : 0 ≤ dy)
    (hx : |Δ| ≤ C * (dx + dy) * (gx + K * (dx + dy)))
    (hy : |Δ| ≤ C * (dx + dy) * (gy + K * (dx + dy))) :
    Δ ^ 2 ≤ 3 * C ^ 2 * dx ^ 2 * gx ^ 2 + 3 * C ^ 2 * dy ^ 2 * gy ^ 2 +
      24 * C ^ 2 * K ^ 2 * (dx ^ 4 + dy ^ 4) := by
  set s := dx + dy with hs
  have hs0 : 0 ≤ s := by positivity
  have hmin : |Δ| ≤ C * (dx * gx + dy * gy) + C * K * s ^ 2 := by
    rcases le_total gx gy with h | h
    · calc |Δ| ≤ C * s * (gx + K * s) := hx
        _ = C * (s * gx) + C * K * s ^ 2 := by ring
        _ ≤ C * (dx * gx + dy * gy) + C * K * s ^ 2 := by
            gcongr
            rw [hs]; nlinarith
    · calc |Δ| ≤ C * s * (gy + K * s) := hy
        _ = C * (s * gy) + C * K * s ^ 2 := by ring
        _ ≤ C * (dx * gx + dy * gy) + C * K * s ^ 2 := by
            gcongr
            rw [hs]; nlinarith
  have hsq : Δ ^ 2 ≤ (C * (dx * gx + dy * gy) + C * K * s ^ 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hmin 2
  have hs4 : s ^ 4 ≤ 8 * (dx ^ 4 + dy ^ 4) := by
    rw [hs]
    nlinarith [sq_nonneg (dx - dy), sq_nonneg (dx + dy), sq_nonneg (dx ^ 2 - dy ^ 2),
      mul_nonneg hdx hdy, sq_nonneg (dx * dy)]
  set u := C * dx * gx
  set v := C * dy * gy
  set w := C * K * s ^ 2
  have h3 : (u + v + w) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
    nlinarith [sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w)]
  have heq : C * (dx * gx + dy * gy) + C * K * s ^ 2 = u + v + w := by ring
  rw [heq] at hsq
  calc Δ ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := hsq.trans h3
    _ = 3 * C ^ 2 * dx ^ 2 * gx ^ 2 + 3 * C ^ 2 * dy ^ 2 * gy ^ 2 + 3 * C ^ 2 * K ^ 2 * s ^ 4 := by ring
    _ ≤ 3 * C ^ 2 * dx ^ 2 * gx ^ 2 + 3 * C ^ 2 * dy ^ 2 * gy ^ 2 +
          3 * C ^ 2 * K ^ 2 * (8 * (dx ^ 4 + dy ^ 4)) := by gcongr
    _ = _ := by ring

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- **(3.14) for `f_ε`**: for `C`-bounded convex open bounded `D`, `f` differentiable on `D` with `Λ`-Lipschitz
gradient and continuous on `D̄`, and reference points `z_x ∈ H_x ∩ D` (`x ∈ V(D)`),
`Energy(f_ε; G(D)) ≤ ∑_{x ∈ V(D)} deg(x) (3C² diam(H_x)² |∇f(z_x)|² + 24C²(Λ(1+C))² diam(H_x)⁴)`. -/
theorem t13_energy_le_grad {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D) {C : ℝ} (hC0 : 0 ≤ C)
    (hbc : BoundedConvexityWith C D) {f : ℂ → ℝ} (hf : DifferentiableOn ℝ f D) {Λ : ℝ≥0}
    (hΛ : LipschitzOnWith Λ (fderiv ℝ f) D) (hfc : ContinuousOn f (closure D))
    (zr : V → ℂ) (hzr : ∀ x ∈ vFin H D, zr x ∈ H.cell x ∩ D)
    {fε : V → ℝ} (hsol : IsGMSDirichletSolution H D f fε) :
    energy G (vFin H D) fε ≤ ∑ x ∈ vFin H D, (G.deg x : ℝ) *
      (3 * C ^ 2 * cellDiam H x ^ 2 * ‖fderiv ℝ f (zr x)‖ ^ 2 +
        24 * C ^ 2 * ((Λ : ℝ) * (1 + C)) ^ 2 * cellDiam H x ^ 4) := by
  -- reference points in `D̄` carrying the boundary values (1.6)
  let p : V → ℂ := fun x =>
    if hx : (H.cell x ∩ closure D).Nonempty then (t13_exists_refPoint H hfc x hx).choose
    else (cell_nonempty H x).choose
  have hxcl : ∀ x ∈ vFin H D, (H.cell x ∩ closure D).Nonempty := by
    intro x hx
    obtain ⟨z, hz⟩ := (mem_vFin H hDb).1 hx
    exact ⟨z, hz.1, subset_closure hz.2⟩
  have hp : ∀ x ∈ vFin H D, p x ∈ H.cell x ∩ closure D := by
    intro x hx
    simp only [p, dite_eq_left (hxcl x hx)]
    exact (t13_exists_refPoint H hfc x (hxcl x hx)).choose_spec.1
  have hpbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      f (p x) = sSup (f '' (H.cell x ∩ frontier D)) := by
    intro x hx hb
    simp only [p, dite_eq_left (hxcl x hx)]
    exact (t13_exists_refPoint H hfc x (hxcl x hx)).choose_spec.2 hb
  -- Dirichlet's principle
  have hDir : energy G (vFin H D) fε ≤ energy G (vFin H D) (f ∘ p) :=
    energy_le_of_lap_eq_zero H hDo hDb (f ∘ p) fε hsol.2
      fun x hx hb => (hsol.1 x hx hb).trans (hpbd x hx hb).symm
  set K : ℝ := (Λ : ℝ) * (1 + C) with hK
  have hK0 : 0 ≤ K := by positivity
  set φ : V → ℝ := fun x => 3 * C ^ 2 * cellDiam H x ^ 2 * ‖fderiv ℝ f (zr x)‖ ^ 2 +
    24 * C ^ 2 * K ^ 2 * cellDiam H x ^ 4 with hφ
  have hφ0 : ∀ x ∈ vFin H D, 0 ≤ φ x := fun x _ => by positivity
  -- the edge estimate
  have hgrad := t13_abs_sub_le_grad hDo hC0 hbc hf hΛ hfc
  have hone : ∀ x ∈ vFin H D, ∀ y ∈ vFin H D, G.adj.Adj x y →
      |f (p x) - f (p y)| ≤ C * (cellDiam H x + cellDiam H y) *
        (‖fderiv ℝ f (zr x)‖ + K * (cellDiam H x + cellDiam H y)) := by
    intro x hx y hy hadj
    have hd : dist (p x) (p y) ≤ cellDiam H x + cellDiam H y :=
      dist_le_cellDiam_add_of_adj H hadj (hp x hx).1 (hp y hy).1
    have hdz : dist (p x) (zr x) ≤ cellDiam H x := dist_le_cellDiam H (hp x hx).1 (hzr x hx).1
    have hdy := cellDiam_nonneg H y
    refine (hgrad (zr x) (hzr x hx).2 (p x) (hp x hx).2 (p y) (hp y hy).2).trans ?_
    calc C * dist (p x) (p y) * (‖fderiv ℝ f (zr x)‖ + Λ * (dist (p x) (zr x) + C * dist (p x) (p y)))
        ≤ C * (cellDiam H x + cellDiam H y) *
          (‖fderiv ℝ f (zr x)‖ + Λ * ((cellDiam H x + cellDiam H y) +
            C * (cellDiam H x + cellDiam H y))) := by
          have hdx := cellDiam_nonneg H x
          have h1 : C * dist (p x) (p y) ≤ C * (cellDiam H x + cellDiam H y) :=
            mul_le_mul_of_nonneg_left hd hC0
          have h2 : dist (p x) (zr x) + C * dist (p x) (p y) ≤
              (cellDiam H x + cellDiam H y) + C * (cellDiam H x + cellDiam H y) :=
            add_le_add (hdz.trans (by linarith)) (mul_le_mul_of_nonneg_left hd hC0)
          have h3 : ‖fderiv ℝ f (zr x)‖ + Λ * (dist (p x) (zr x) + C * dist (p x) (p y)) ≤
              ‖fderiv ℝ f (zr x)‖ + Λ * ((cellDiam H x + cellDiam H y) +
                C * (cellDiam H x + cellDiam H y)) := by
            have := mul_le_mul_of_nonneg_left h2 Λ.coe_nonneg
            linarith
          exact mul_le_mul h1 h3 (by positivity) (mul_nonneg hC0 (by linarith))
      _ = C * (cellDiam H x + cellDiam H y) *
          (‖fderiv ℝ f (zr x)‖ + K * (cellDiam H x + cellDiam H y)) := by rw [hK]; ring
  have hedge : energy G (vFin H D) (f ∘ p) ≤
      ∑ e ∈ edgesIn G (vFin H D), (φ (G.src e) + φ (G.tgt e)) := by
    unfold energy
    refine Finset.sum_le_sum fun e he => ?_
    rw [mem_edgesIn] at he
    simp only [Function.comp]
    by_cases hloop : G.src e = G.tgt e
    · rw [hloop, sub_self, sq, mul_zero]
      exact add_nonneg (hφ0 _ (hloop ▸ he.1)) (hφ0 _ he.2)
    · have hadj := adj_of_edge G hloop
      have hx := hone _ he.1 _ he.2 hadj
      have hy := hone _ he.2 _ he.1 hadj.symm
      rw [abs_sub_comm, add_comm (cellDiam H (G.tgt e))] at hy
      have h := t13_sq_le_of_two_bounds hC0 (cellDiam_nonneg H _) (cellDiam_nonneg H _) hx hy
      simp only [hφ]
      nlinarith [h]
  calc energy G (vFin H D) fε ≤ energy G (vFin H D) (f ∘ p) := hDir
    _ ≤ ∑ e ∈ edgesIn G (vFin H D), (φ (G.src e) + φ (G.tgt e)) := hedge
    _ ≤ ∑ x ∈ vFin H D, (G.deg x : ℝ) * φ x := sum_edgesIn_add_le G _ hφ0

end MatedCRTHarmonic.GMSMain
