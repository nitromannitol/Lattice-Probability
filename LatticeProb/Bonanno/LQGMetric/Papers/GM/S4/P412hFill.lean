/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412hFill at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hBor3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hL414
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasB1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop

/-!
# `gd` for filled metric balls (D98 §2: P-L414B and P-L414Borel, filled-ball form)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.14 (l. 2097–2102) and
L4.15 Step 3 (∗) (l. 2159–2165); decision D98 §2.

* `p412h_goodZ_cover` — (∗) at `x` for `y` whenever `x ∈ B̄_{8ε}(gd(K, y))` or `∂K` misses that
  ball (the second case only occurs when `𝒞^ε_y = ∅`, where (∗) is vacuous);
* `p412h_goodZ_filled` — the same for `K = 𝓑^•_t` (`t > 0`, `D` length, `𝓑_t` bounded);
* `p412h_filledBall_reg`, `p412h_rc_filled` — filled balls form a regular random closed set;
* **`p412h_gdBorel`** — P-L414Borel: `{(d, y) | gd(𝓑^•_{τ_R c}(d), y) = q}` agrees on
  `lenSet × ℂ` with a Borel set;
* `gmAn_iInter` — countable intersections of analytic sets (own routine argument).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Topology Bornology
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- **(∗) for the guard points of `gd(K, y)`** -/
theorem p412h_goodZ_cover {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) (hLC : ∀ q ∈ frontier K, LocConnAt K q) {y : ℂ}
    (hy : y ∈ frontier K) {ε : ℝ} (hε : 0 < ε) (x : ℂ)
    (hx : (frontier K ∩ closedBall (p412hGd K y ε) (8 * ε)).Nonempty →
      x ∈ closedBall (p412hGd K y ε) (8 * ε)) : p412eGoodZ K y x ε := by
  rcases p412h_L414B hK hKc hKo hLC hy hε with hC | ⟨r, hr, hr8, hKB, y₀, hy₀, hy₀K, -⟩
  · refine ⟨8 * ε, by positivity, le_rfl, fun F _ _ _ _ X v P a b hX hXc hXd hv hb hyV _ _ _ _ _ _ =>
      ?_⟩
    exfalso
    have := p412c_cc_subset_dcSetC hX hXc hXd hv hb hyV (mem_connectedComponentIn hv)
    rw [hC] at this; exact this
  · obtain ⟨z, hz, hzB⟩ := p412b_frontier_mem_closedBall hK.isClosed hKB
      (sphere_subset_closedBall hy₀) hy₀K
    exact p412h_goodZ hK hKc hKo hLC hy hε
      (hx ⟨z, hz, closedBall_subset_closedBall hr8 hzB⟩)

/-- the hypotheses of L4.14 for a filled metric ball -/
theorem p412h_filled_geo {D : ContMetric} {𝕫 : ℂ} {t : ℝ} (ht : 0 < t) (hL : D.IsLength)
    (hbd : IsBounded (ballM D 𝕫 t)) :
    p412hGeo (filledBall D 𝕫 t) ∧ ∀ q ∈ frontier (filledBall D 𝕫 t), LocConnAt (filledBall D 𝕫 t) q :=
  ⟨⟨jb_isCompact_filledBall hbd, ⟨⟨𝕫, jo_mem_filledBall_self ht⟩, jp_isPreconnected_filledBall ht hL⟩,
    jb_isPreconnected_compl hbd⟩, fun _ hq => p412c_filledBall_locConnAt ht hL hbd hq⟩

/-- **(∗) for `𝓑^•_t`** at the guard points of `gd` -/
theorem p412h_goodZ_filled {D : ContMetric} {𝕫 : ℂ} {t : ℝ} (ht : 0 < t) (hL : D.IsLength)
    (hbd : IsBounded (ballM D 𝕫 t)) {y : ℂ} (hy : y ∈ frontier (filledBall D 𝕫 t)) {ε : ℝ}
    (hε : 0 < ε) (x : ℂ)
    (hx : (frontier (filledBall D 𝕫 t) ∩ closedBall (p412hGd (filledBall D 𝕫 t) y ε) (8 * ε)).Nonempty →
      x ∈ closedBall (p412hGd (filledBall D 𝕫 t) y ε) (8 * ε)) :
    p412eGoodZ (filledBall D 𝕫 t) y x ε := by
  obtain ⟨⟨hK, hKc, hKo⟩, hLC⟩ := p412h_filled_geo ht hL hbd
  exact p412h_goodZ_cover hK hKc hKo hLC hy hε x hx

/-- a filled ball is the closure of its interior -/
theorem p412h_filledBall_reg (d : ContMetric) (𝕫 : ℂ) (s : ℝ) :
    filledBall d 𝕫 s ⊆ closure (interior (filledBall d 𝕫 s)) := by
  have hB : ballM d 𝕫 s ⊆ interior (filledBall d 𝕫 s) :=
    interior_maximal (fun w hw => Or.inl (subset_closure hw)) (gmE_isOpen_ballM d 𝕫 s)
  rintro w (hw | ⟨hwX, hwb⟩)
  · exact closure_mono hB hw
  · have hCo : IsOpen (connectedComponentIn (closure (ballM d 𝕫 s))ᶜ w) :=
      isClosed_closure.isOpen_compl.connectedComponentIn
    have hCsub : connectedComponentIn (closure (ballM d 𝕫 s))ᶜ w ⊆ filledBall d 𝕫 s :=
      fun v hv => Or.inr ⟨connectedComponentIn_subset _ _ hv, by
        rw [← connectedComponentIn_eq hv]; exact hwb⟩
    exact subset_closure (interior_maximal hCsub hCo (mem_connectedComponentIn hwX))

/-- filled balls form a regular random closed set over `(d, s, x)` -/
theorem p412h_rc_filled (𝕫 : ℂ) : P412hRC (fun p : ContMetric × ℝ × ℂ => filledBall p.1 𝕫 p.2.1) :=
  ⟨fun w => (gmE_measurableSet_filledBall 𝕫).preimage
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const)),
    fun p => gm_filledBall_isClosed _ _ _, fun p => p412h_filledBall_reg _ _ _⟩

/-- countable intersections of analytic sets -/
theorem gmAn_iInter {α : Type} [MeasurableSpace α] {L : Set α} {A : ℕ → Set α}
    (h : ∀ m, GMAnalyticOn L (A m)) : GMAnalyticOn L (⋂ m, A m) := by
  choose β mβ sb S hS hA using h
  let _ : ∀ m, MeasurableSpace (β m) := mβ
  have _ : ∀ m, StandardBorelSpace (β m) := sb
  refine ⟨∀ m, β m, inferInstance, inferInstance, {q | ∀ m, (q.1, q.2 m) ∈ S m}, ?_, fun a ha => ?_⟩
  · have : {q : α × (∀ m, β m) | ∀ m, (q.1, q.2 m) ∈ S m} =
        ⋂ m, (fun q : α × (∀ m, β m) => (q.1, q.2 m)) ⁻¹' S m := by
      ext q; simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
    rw [this]
    exact MeasurableSet.iInter fun m => (hS m).preimage
      (measurable_fst.prodMk ((measurable_pi_apply m).comp measurable_snd))
  · simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro H
      choose b hb using fun m => (hA m a ha).1 (H m)
      exact ⟨b, hb⟩
    · rintro ⟨b, hb⟩ m
      exact (hA m a ha).2 ⟨b m, hb m⟩

end LQGMetric.GM
