import LatticeProb.Topology.RerootedExitWindow
import LatticeProb.Topology.StoppedNestedExitTrial

/-!
# Measurability and laws of exit windows of re-rooted plane curves

For a continuous plane curve `w : C(ℝ, ℂ)`, the *exit window* at radius `R` is the pair
formed by the first exit time of `w` from `ball 0 R` after time `0` and the curve `w`
observed on `[0, T]` (frozen outside). We prove:

* the first exit time after a measurable start time from a ball, of a measurable random
  curve in `ℂ`, is measurable (`measurable_exitTimeAfter`), and so is the event that a ball
  of fixed radius lies in the trace of the curve between two such exits;
* the exit window is a measurable function of the curve (`measurable_originExitWindow`);
* an integrated lower bound for the ball event on the preimages of the exit window depends
  only on the law of the curve (`originExitWindow_ball_bound_of_map_eq`);
* after re-rooting a curve at its first hit of `z` and rescaling by `s`, the exit window
  at radius `1` is the image, under the space-time scaling `(d, w) ↦ (s ^ 2 d, s w(· / s ^ 2))`,
  of the forward window of `c` from its first hit of `z` until its exit from `ball z s`
  (`rerootedExitWindow_eq_spaceTimeScale`);
* a ball event for the re-rooted curve gives a nested exit trial of the original curve
  (`mem_nestedExitTrialEvent_of_affineReroot`).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology

namespace LatticeProb

open MatedCRTHarmonic.MatedCRT

/-- The first exit time from a ball, after a measurable start time, of a measurable random
continuous curve in `ℂ` is measurable. -/
theorem measurable_exitTimeAfter {Ω : Type*} [MeasurableSpace Ω] {g : Ω → C(ℝ, ℂ)}
    {t₀ : Ω → ℝ} (hg : Measurable g) (ht₀ : Measurable t₀) (z : ℂ) (r : ℝ) :
    Measurable fun ω => exitTimeAfter (g ω) (t₀ ω) z r := by
  let e := Complex.orthonormalBasisOneI.repr
  let G : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2)) := fun w =>
    ⟨fun t => e (w t), e.continuous.comp w.continuous⟩
  have hG : Continuous G :=
    ContinuousMap.continuous_of_continuous_uncurry _ (e.continuous.comp continuous_eval)
  have h := measurable_sInf_outside (hG.measurable.comp hg) ht₀
    (isOpen_ball : IsOpen (ball (e z) r))
  convert h using 2 with ω
  unfold exitTimeAfter
  congr 1
  ext t
  simp only [mem_ofPred_eq, Function.comp_apply, G, ContinuousMap.coe_mk, mem_ball,
    LinearIsometryEquiv.dist_map]

/-- The event that a ball of fixed positive radius lies in the trace of a measurable random
curve in `ℂ` between two of its exits, after a measurable start time, is measurable. -/
theorem measurableSet_exists_ball_subset_exitWindow {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → C(ℝ, ℂ)} {t₀ : Ω → ℝ} (hg : Measurable g) (ht₀ : Measurable t₀) (z : ℂ)
    (r₁ r₂ : ℝ) {a : ℝ} (ha : 0 < a) :
    MeasurableSet {ω | ∃ x, ball x a ⊆ g ω ''
      Icc (exitTimeAfter (g ω) (t₀ ω) z r₁) (exitTimeAfter (g ω) (t₀ ω) z r₂)} := by
  have h := measurableSet_exists_closedBall_subset_segment hg
    (measurable_exitTimeAfter hg ht₀ z r₁) (measurable_exitTimeAfter hg ht₀ z r₂)
    (measurable_const : Measurable fun _ : Ω => a)
  convert h using 1
  ext ω
  exact exists_ball_subset_image_Icc_iff (g ω) ha _ _

/-- Nested exit trials of a measurable random curve in `ℂ` after a measurable start time are
measurable. -/
theorem measurableSet_nestedExitTrialEvent_complex {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → C(ℝ, ℂ)} {t₀ : Ω → ℝ} (hg : Measurable g) (ht₀ : Measurable t₀) (z : ℂ)
    (r : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (i : ℕ) :
    MeasurableSet (nestedExitTrialEvent (fun ω => ⇑(g ω)) t₀ z r a i) :=
  measurableSet_exists_ball_subset_exitWindow hg ht₀ z (r i) (r (i + 1)) ha

/-- The window `w` observed on `[t₀, T]` depends continuously on `(T, w)`. -/
theorem continuous_realWindowCurve {E : Type*} [TopologicalSpace E] (t₀ : ℝ) :
    Continuous fun p : ℝ × C(ℝ, E) => realWindowCurve t₀ p.1 p.2 := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
    ((continuous_snd.max continuous_const).min (continuous_fst.comp continuous_fst)))

/-- The exit window at radius `R`: the first exit time `T` from `ball 0 R` after time `0`,
and the curve observed on `[0, T]`. -/
noncomputable def originExitWindow (R : ℝ) (w : C(ℝ, ℂ)) : ℝ × C(ℝ, ℂ) :=
  (exitTimeAfter w 0 0 R, realWindowCurve 0 (exitTimeAfter w 0 0 R) w)

theorem measurable_originExitWindow (R : ℝ) : Measurable (originExitWindow R) := by
  have he : Measurable fun w : C(ℝ, ℂ) => exitTimeAfter w 0 0 R :=
    measurable_exitTimeAfter measurable_id measurable_const 0 R
  exact he.prodMk ((continuous_realWindowCurve 0).measurable.comp (he.prodMk measurable_id))

/-- An integrated lower bound for a ball event on a preimage of the exit window depends only
on the law of the curve. -/
theorem originExitWindow_ball_bound_of_map_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {c c' : Ω → C(ℝ, ℂ)} (hc : AEMeasurable c P) (hc' : AEMeasurable c' P)
    (hmap : P.map c' = P.map c) {p a R : ℝ} (ha : 0 < a) {S : Set (ℝ × C(ℝ, ℂ))}
    (hS : MeasurableSet S)
    (h : ENNReal.ofReal p * P {ω | originExitWindow 1 (c ω) ∈ S} ≤
      P ({ω | originExitWindow 1 (c ω) ∈ S} ∩
        {ω | ∃ x, ball x a ⊆ c ω '' Icc (exitTimeAfter (c ω) 0 0 1) (exitTimeAfter (c ω) 0 0 R)})) :
    ENNReal.ofReal p * P {ω | originExitWindow 1 (c' ω) ∈ S} ≤
      P ({ω | originExitWindow 1 (c' ω) ∈ S} ∩
        {ω | ∃ x, ball x a ⊆ c' ω '' Icc (exitTimeAfter (c' ω) 0 0 1)
          (exitTimeAfter (c' ω) 0 0 R)}) := by
  have hpre : MeasurableSet (originExitWindow 1 ⁻¹' S) := measurable_originExitWindow 1 hS
  have hEv : MeasurableSet {w : C(ℝ, ℂ) | ∃ x, ball x a ⊆ w ''
      Icc (exitTimeAfter w 0 0 1) (exitTimeAfter w 0 0 R)} :=
    measurableSet_exists_ball_subset_exitWindow measurable_id measurable_const 0 1 R ha
  have key : ∀ g : Ω → C(ℝ, ℂ), AEMeasurable g P →
      P {ω | originExitWindow 1 (g ω) ∈ S} = P.map g (originExitWindow 1 ⁻¹' S) ∧
      P ({ω | originExitWindow 1 (g ω) ∈ S} ∩
        {ω | ∃ x, ball x a ⊆ g ω '' Icc (exitTimeAfter (g ω) 0 0 1)
          (exitTimeAfter (g ω) 0 0 R)}) =
      P.map g (originExitWindow 1 ⁻¹' S ∩ {w : C(ℝ, ℂ) | ∃ x, ball x a ⊆ w ''
        Icc (exitTimeAfter w 0 0 1) (exitTimeAfter w 0 0 R)}) := fun g hg =>
    ⟨(Measure.map_apply_of_aemeasurable hg hpre).symm,
      (Measure.map_apply_of_aemeasurable hg (hpre.inter hEv)).symm⟩
  rw [(key c hc).1, (key c hc).2] at h
  rw [(key c' hc').1, (key c' hc').2, hmap]
  exact h

/-- The space-time scaling `(d, w) ↦ (s ^ 2 d, s w(· / s ^ 2))` of a window. -/
noncomputable def spaceTimeScale (s : ℝ) (p : ℝ × C(ℝ, ℂ)) : ℝ × C(ℝ, ℂ) :=
  (s ^ 2 * p.1, ⟨fun t => (s : ℂ) * p.2 (t / s ^ 2),
    continuous_const.mul (p.2.continuous.comp (continuous_id.div_const _))⟩)

theorem measurable_spaceTimeScale (s : ℝ) : Measurable (spaceTimeScale s) := by
  have hcont : Continuous fun w : C(ℝ, ℂ) => (⟨fun t => (s : ℂ) * w (t / s ^ 2),
      continuous_const.mul (w.continuous.comp (continuous_id.div_const _))⟩ : C(ℝ, ℂ)) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      (continuous_const.mul (continuous_eval.comp
        (continuous_fst.prodMk (continuous_snd.div_const _))))
  exact (measurable_fst.const_mul _).prodMk (hcont.measurable.comp measurable_snd)

/-- The forward window of `c` from its first hit of `z` until its exit from `ball z s`,
re-rooted at `z` (time shifted by the first hit, space by `z`), is the space-time scaling by
`s` of the exit window at radius `1` of the curve re-rooted at `z` and rescaled by `s`. -/
theorem rerootedExitWindow_eq_spaceTimeScale (c : C(ℝ, ℂ)) (z : ℂ) {s : ℝ} (hs : 0 < s)
    (hex : ∃ t, firstHit c z ≤ t ∧ c t ∉ ball z s) :
    (exitTimeAfter c (firstHit c z) z s - firstHit c z,
      realWindowCurve 0 (exitTimeAfter c (firstHit c z) z s - firstHit c z)
        (affineReroot z 1 0 c)) =
      spaceTimeScale s (originExitWindow 1 (affineReroot z s 0 c)) := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs.ne'
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have h1 := exitTimeAfter_affineReroot c z hs 1 (by simpa only [mul_one] using hex)
  rw [mul_one] at h1
  simp only [spaceTimeScale, originExitWindow, h1]
  refine Prod.ext (mul_div_cancel₀ _ hs2).symm ?_
  ext t
  simp only [ContinuousMap.coe_mk]
  rw [realWindowCurve_affineReroot_apply c z hs, mul_div_cancel₀ t hs2, ← mul_assoc,
    mul_inv_cancel₀ hs0, one_mul]

/-- A ball of radius `a` in the trace of the curve re-rooted at `z` and rescaled by `r k`,
between its exits from `ball 0 1` and `ball 0 R`, gives the `k`-th nested exit trial of the
original curve after its first hit of `z`, with ball radius `r k * a`, when
`r k * R ≤ r (k + 1)`. -/
theorem mem_nestedExitTrialEvent_of_affineReroot {Ω : Type*} {η : Ω → C(ℝ, ℂ)} (z : ℂ)
    (r : ℕ → ℝ) (k : ℕ) {ω : Ω} {R a : ℝ} (hs : 0 < r k) (hR : r k * R ≤ r (k + 1))
    (hex : ∀ r' : ℝ, ∃ t, firstHit (η ω) z ≤ t ∧ η ω t ∉ ball z r')
    (h : ∃ x, ball x a ⊆ affineReroot z (r k) 0 (η ω) ''
      Icc (exitTimeAfter (affineReroot z (r k) 0 (η ω)) 0 0 1)
        (exitTimeAfter (affineReroot z (r k) 0 (η ω)) 0 0 R)) :
    ω ∈ nestedExitTrialEvent (fun ω => ⇑(η ω)) (fun ω => firstHit (η ω) z) z r
      (r k * a) k :=
  exists_ball_subset_exitWindow_of_affineReroot (η ω) z hs hR hex h

end LatticeProb
