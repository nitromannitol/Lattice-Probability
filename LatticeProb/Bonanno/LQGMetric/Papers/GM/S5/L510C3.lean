/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510C3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CLay
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event2Fin

/-!
# GM Lemma 5.10, condition (9): internal diameter of `W_r^x` (task P2-M2M6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, l. 3329:
"By Axiom V and Lemma 2.9, we can find `M > 1` such that condition 9 holds with probability at
least `1 − (1−𝕡)/100`" — the same chaining argument as for condition (5) (l. 3313–3320), for the
tubes `W_r^x(θ)` (GM (5.28)), which consist of the squares of side `θr` meeting the segment
`[x, (3/2 − θ)x]`. Here `gm_L510Line` deduces it from `l510_tubes_diam`; the facts used about
`W_r^x` are that it is preconnected (`l510_sqUnion_isPreconnected`: the squares meeting a
preconnected set `X` have a preconnected open union-interior, which contains `X`; own elementary
argument, GM use it implicitly) and that its squares meet `cl B_{(2 + 2|3/2 − θ|) r}(0)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the interior of the union of the squares meeting a preconnected set is preconnected -/
lemma l510_sqUnion_isPreconnected {s : ℝ} (hs : 0 < s) {X : Set ℂ} (hX : IsPreconnected X) :
    IsPreconnected (interior (⋃ m ∈ squareSet s X, gridSquare s m)) := by
  set V := interior (⋃ m ∈ squareSet s X, gridSquare s m) with hVdef
  have hXV : X ⊆ V := subset_interior_squares_m2m hs X
  rcases X.eq_empty_or_nonempty with hXe | ⟨x0, hx0⟩
  · have : V = ∅ := by simp [hVdef, hXe, squareSet]
    rw [this]; exact isPreconnected_empty
  refine isPreconnected_of_forall x0 fun y hy => ?_
  obtain ⟨m, hm, hym⟩ : ∃ m ∈ squareSet s X, y ∈ gridSquare s m := by
    have := interior_subset hy; simpa only [mem_iUnion, exists_prop] using this
  obtain ⟨c, hcS, hcX⟩ := hm
  have hintV : interior (gridSquare s m) ⊆ V :=
    interior_mono (subset_biUnion_of_mem (u := fun m => gridSquare s m) ⟨c, hcS, hcX⟩)
  obtain ⟨ηc, hηc, hbc⟩ := Metric.isOpen_iff.1 isOpen_interior c (hXV hcX)
  obtain ⟨ηy, hηy, hby⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  have hmeet : ∀ w ∈ gridSquare s m, ∀ η : ℝ, 0 < η →
      (ball w η ∩ interior (gridSquare s m)).Nonempty := fun w hw η hη => by
    obtain ⟨v, hv, hvd⟩ := Metric.mem_closure_iff.1 (gridSquare_subset_closure_interior hs m hw) η hη
    exact ⟨v, mem_ball.2 (by rw [dist_comm]; exact hvd), hv⟩
  have hI : IsPreconnected (interior (gridSquare s m)) :=
    ((convex_gridSquare56 s m).interior).isPreconnected
  have h1 : IsPreconnected (X ∪ ball c ηc) :=
    IsPreconnected.union c hcX (mem_ball_self hηc) hX (convex_ball c ηc).isPreconnected
  have h2 : IsPreconnected (X ∪ ball c ηc ∪ interior (gridSquare s m)) := by
    obtain ⟨v, hv1, hv2⟩ := hmeet c hcS ηc hηc
    exact IsPreconnected.union v (Or.inr hv1) hv2 h1 hI
  have h3 : IsPreconnected (X ∪ ball c ηc ∪ interior (gridSquare s m) ∪ ball y ηy) := by
    obtain ⟨v, hv1, hv2⟩ := hmeet y hym ηy hηy
    exact IsPreconnected.union v (Or.inr hv2) hv1 h2 (convex_ball y ηy).isPreconnected
  refine ⟨_, ?_, Or.inl (Or.inl (Or.inl hx0)), Or.inr (mem_ball_self hηy), h3⟩
  rintro z (((hz | hz) | hz) | hz)
  · exact hXV hz
  · exact hbc hz
  · exact hintV hz
  · exact hby hz

/-- the segment `[x, (3/2 − θ)x]` lies in `cl B_{(2 + 2|3/2 − θ|) r}(0)` -/
lemma l510_segment_subset {θ r : ℝ} (hr : 0 < r) {x : ℂ} (hx : ‖x‖ = 2 * r) :
    segment ℝ x (((3 / 2 - θ : ℝ) : ℂ) * x) ⊆ closedBall 0 ((2 + 2 * |3 / 2 - θ|) * r) := by
  refine (convex_closedBall _ _).segment_subset ?_ ?_
  · rw [mem_closedBall, dist_zero_right, hx]
    nlinarith [abs_nonneg (3 / 2 - θ)]
  · rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, hx]
    nlinarith [abs_nonneg (3 / 2 - θ)]

/-- `L510Line` (condition (9), `L510B.lean`) with the range `0 < γ < 2` -/
def L510LineG : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c →
  ∀ {θ q : ℝ}, 0 < θ → 0 < q → ∃ M : ℝ, 1 < M ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
    P {ω | ¬ ∀ x ∈ Metric.sphere (0 : ℂ) (2 * r),
      internalDiam (D (h ω)) (lineTube θ r x) (lineTube θ r x) ≤
        ENNReal.ofReal (M * scaleFac (xiGamma γ) c (h ω) r 0)} ≤ ENNReal.ofReal q

/-- **GM Lemma 5.10, condition (9)** (l. 3329) -/
theorem gm_L510Line (h320 : DFGPSLem3_20) : L510LineG := by
  intro γ D c hγ0 hγ2 hD θ q hθ hq
  obtain ⟨M, hM, H⟩ := l510_tubes_diam h320 hγ0 hγ2 hD hθ
    (by positivity : (0 : ℝ) ≤ 2 + 2 * |3 / 2 - θ|) hq
  refine ⟨M, hM, fun P _ h hh r hr => le_trans (measure_mono ?_) (H P h hh r hr)⟩
  intro ω hω hgood
  apply hω
  intro x hx
  rw [mem_sphere, dist_zero_right] at hx
  have hs : 0 < θ * r := mul_pos hθ hr
  have hseg := l510_segment_subset (θ := θ) hr hx
  have hfin : (squareSet (θ * r) (segment ℝ x (((3 / 2 - θ : ℝ) : ℂ) * x))).Finite :=
    squareSet_finite_m2m2 hs (hseg.trans (closedBall_subset_ball (lt_add_one _)))
  have heq : lineTube θ r x = tubeOf (θ * r) hfin.toFinset := by
    unfold lineTube tubeOf
    congr 1
    ext z
    simp only [mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
  rw [heq]
  refine hgood _ (fun m hm => ?_) ?_
  · obtain ⟨z, hz1, hz2⟩ := (Set.Finite.mem_toFinset hfin).1 hm
    exact ⟨z, hz1, hseg hz2⟩
  · rw [← heq]
    exact l510_sqUnion_isPreconnected hs (convex_segment _ _).isPreconnected

end LQGMetric.GM
