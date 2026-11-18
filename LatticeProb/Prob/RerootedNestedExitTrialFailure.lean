import LatticeProb.Prob.RerootedNestedExitTrial
import LatticeProb.Topology.StoppedNestedExitTrial

/-!
# Failure of nested exit trials after a first hit, from re-rooting invariance

Let `c` be a random continuous plane curve, proper almost surely, and `τ` its first hit of
`z`. The `i`-th nested exit trial after `τ` asks that some ball of radius `a` lie in the trace
of `c` between its first exits, after `τ`, from `ball z (r i)` and from `ball z (r (i + 1))`.
Almost surely this event is read off the forward window of `c` from `τ` until its exit from
`ball z ρ`, re-rooted at `z` (`rerootedExitWindow`), as soon as `r i, r (i + 1) ≤ ρ`. Hence,
for nondecreasing radii, the trials before step `k` are measurable for the completed
σ-algebra of the window at radius `r k`.

Combined with the conditional lower bound `le_condExp_nestedExitTrial_rerootedExitWindow`,
which follows from the invariance of the law of `c` under re-rooting at `z` and rescaling,
this gives the inverse-scale exponential bound for the event that no ball of radius `a` lies
in the trace of `c` between `τ` and its first exit from `ball z R`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

open MatedCRTHarmonic.MatedCRT

/-- Windows `(d, w)` whose curve `w` contains a ball of radius `a` in its trace between its
first exits, after time `0`, from `ball 0 ρ₁` and from `ball 0 ρ₂`. -/
def windowTraceBallSet (ρ₁ ρ₂ a : ℝ) : Set (ℝ × C(ℝ, ℂ)) :=
  {p | ∃ x, ball x a ⊆ p.2 '' Icc (exitTimeAfter p.2 0 0 ρ₁) (exitTimeAfter p.2 0 0 ρ₂)}

theorem measurableSet_windowTraceBallSet (ρ₁ ρ₂ : ℝ) {a : ℝ} (ha : 0 < a) :
    MeasurableSet (windowTraceBallSet ρ₁ ρ₂ a) :=
  measurableSet_exists_ball_subset_exitWindow (g := Prod.snd) (t₀ := fun _ => (0 : ℝ))
    measurable_snd measurable_const 0 ρ₁ ρ₂ ha

/-- Exit times after `t₀` only depend on the curve from time `t₀` on. -/
theorem exitTimeAfter_congr_of_eqOn_Ici {E : Type*} [PseudoMetricSpace E] {w₁ w₂ : ℝ → E}
    {t₀ : ℝ} (h : ∀ t, t₀ ≤ t → w₁ t = w₂ t) (z : E) (ρ : ℝ) :
    exitTimeAfter w₁ t₀ z ρ = exitTimeAfter w₂ t₀ z ρ := by
  unfold exitTimeAfter
  congr 1
  ext t
  exact and_congr_right fun ht => by rw [h t ht]

/-- Observing a curve on the window `[0, T]`, with `T` its first exit after `0` from
`ball z R`, changes neither its first exits after `0` from concentric balls of radii at most
`R` nor its trace between two of them. -/
theorem exists_ball_subset_realWindowCurve_trace_iff {E : Type*} [PseudoMetricSpace E]
    (g : C(ℝ, E)) (z : E) {R ρ₁ ρ₂ a : ℝ} (h₁ : ρ₁ ≤ R) (h₂ : ρ₂ ≤ R)
    (hne : ∃ t, 0 ≤ t ∧ g t ∉ ball z R) :
    (∃ x, ball x a ⊆ realWindowCurve 0 (exitTimeAfter g 0 z R) g '' Icc
        (exitTimeAfter (realWindowCurve 0 (exitTimeAfter g 0 z R) g) 0 z ρ₁)
        (exitTimeAfter (realWindowCurve 0 (exitTimeAfter g 0 z R) g) 0 z ρ₂)) ↔
      ∃ x, ball x a ⊆ g '' Icc (exitTimeAfter g 0 z ρ₁) (exitTimeAfter g 0 z ρ₂) := by
  have hagree : ∀ t, 0 ≤ t → realWindowCurve 0 (exitTimeAfter g 0 z R) g t =
      realStoppedCurve (exitTimeAfter g 0 z R) g t := fun t ht => by
    rw [realWindowCurve_apply, realStoppedCurve_apply, max_eq_left ht]
  obtain ⟨e₁, -⟩ := sInf_outside_realStoppedCurve_ball g 0 z h₁ hne
  obtain ⟨e₂, hle⟩ := sInf_outside_realStoppedCurve_ball g 0 z h₂ hne
  have hW₁ : exitTimeAfter (realWindowCurve 0 (exitTimeAfter g 0 z R) g) 0 z ρ₁ =
      exitTimeAfter g 0 z ρ₁ := (exitTimeAfter_congr_of_eqOn_Ici hagree z ρ₁).trans e₁
  have hW₂ : exitTimeAfter (realWindowCurve 0 (exitTimeAfter g 0 z R) g) 0 z ρ₂ =
      exitTimeAfter g 0 z ρ₂ := (exitTimeAfter_congr_of_eqOn_Ici hagree z ρ₂).trans e₂
  have h0 : 0 ≤ exitTimeAfter g 0 z ρ₁ := Real.sInf_nonneg fun x hx => hx.1
  have himage : realWindowCurve 0 (exitTimeAfter g 0 z R) g ''
      Icc (exitTimeAfter g 0 z ρ₁) (exitTimeAfter g 0 z ρ₂) =
      g '' Icc (exitTimeAfter g 0 z ρ₁) (exitTimeAfter g 0 z ρ₂) := by
    refine Set.EqOn.image_eq fun t ht => ?_
    have htR : t ≤ exitTimeAfter g 0 z R := ht.2.trans hle
    rw [realWindowCurve_apply, max_eq_left (h0.trans ht.1), min_eq_left htR]
  rw [hW₁, hW₂, himage]

theorem affineReroot_one_apply (z : ℂ) (c : C(ℝ, ℂ)) (t : ℝ) :
    affineReroot z 1 0 c t = c (firstHit c z + t) - z := by
  rw [affineReroot_zero_apply_eq]
  simp only [Complex.ofReal_one, inv_one, one_mul, one_pow]

/-- On a curve that leaves every ball after its first hit of `z`, a nested trace event after
that hit with radii at most `R` is read off the re-rooted forward window at radius `R`. -/
theorem rerootedExitWindow_mem_windowTraceBallSet_iff (c : C(ℝ, ℂ)) (z : ℂ) {R ρ₁ ρ₂ a : ℝ}
    (h₁ : ρ₁ ≤ R) (h₂ : ρ₂ ≤ R)
    (hex : ∀ r' : ℝ, ∃ t, firstHit c z ≤ t ∧ c t ∉ ball z r') :
    rerootedExitWindow c z R ∈ windowTraceBallSet ρ₁ ρ₂ a ↔
      ∃ x, ball x a ⊆ c '' Icc (exitTimeAfter c (firstHit c z) z ρ₁)
        (exitTimeAfter c (firstHit c z) z ρ₂) := by
  have hgexit : ∀ ρ, exitTimeAfter (affineReroot z 1 0 c) 0 0 ρ =
      exitTimeAfter c (firstHit c z) z ρ - firstHit c z := fun ρ => by
    have h := exitTimeAfter_affineReroot c z one_pos ρ (by simpa only [one_mul] using hex ρ)
    rwa [one_mul, one_pow, div_one] at h
  have hgex : ∃ t, 0 ≤ t ∧ affineReroot z 1 0 c t ∉ ball (0 : ℂ) R := by
    obtain ⟨t, ht, hct⟩ := hex R
    refine ⟨t - firstHit c z, sub_nonneg.2 ht, ?_⟩
    rw [affineReroot_one_apply, add_sub_cancel, mem_ball, dist_zero_right, ← dist_eq_norm]
    exact hct
  have hW : rerootedExitWindow c z R = (exitTimeAfter (affineReroot z 1 0 c) 0 0 R,
      realWindowCurve 0 (exitTimeAfter (affineReroot z 1 0 c) 0 0 R) (affineReroot z 1 0 c)) := by
    rw [hgexit R]
    rfl
  rw [hW]
  refine (exists_ball_subset_realWindowCurve_trace_iff (affineReroot z 1 0 c) 0 h₁ h₂
    hgex).trans ?_
  rw [hgexit ρ₁, hgexit ρ₂]
  constructor
  · rintro ⟨x, hx⟩
    have hb := ball_subset_image_of_affineReroot c z one_pos hx
    simp only [Complex.ofReal_one, one_mul, one_pow, add_sub_cancel] at hb
    exact ⟨_, hb⟩
  · rintro ⟨x, hx⟩
    refine ⟨x - z, fun y hy => ?_⟩
    have hy' : y + z ∈ ball x a := by
      rw [mem_ball, dist_eq_norm] at hy ⊢
      rwa [show y + z - x = y - (x - z) by ring]
    obtain ⟨t, ht, hct⟩ := hx hy'
    refine ⟨t - firstHit c z, ⟨sub_le_sub_right ht.1 _, sub_le_sub_right ht.2 _⟩, ?_⟩
    rw [affineReroot_one_apply, add_sub_cancel, hct, add_sub_cancel_right]

/-- If the curve is proper almost surely, every nested exit trial after the first hit of `z`
with radii at most `ρ` lies in the completion of the σ-algebra generated by the re-rooted
forward window at radius `ρ`. -/
theorem nestedExitTrialEvent_mem_completed_rerootedExitWindow {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : Ω → C(ℝ, ℂ))
    (hprop : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ)) (z : ℂ) {ρ : ℝ}
    (r : ℕ → ℝ) {a : ℝ} (ha : 0 < a) {i : ℕ} (hi : r i ≤ ρ) (hi1 : r (i + 1) ≤ ρ) :
    MeasurableSet[eventuallyMeasurableSpace (MeasurableSpace.comap
        (fun ω => rerootedExitWindow (c ω) z ρ) inferInstance) (ae P)]
      (nestedExitTrialEvent (fun ω => ⇑(c ω)) (fun ω => firstHit (c ω) z) z r a i) := by
  refine ⟨_, ⟨windowTraceBallSet (r i) (r (i + 1)) a, measurableSet_windowTraceBallSet _ _ ha,
    rfl⟩, Filter.eventuallyEqSet_iff.2 ?_⟩
  filter_upwards [hprop] with ω hω
  exact (rerootedExitWindow_mem_windowTraceBallSet_iff (c ω) z hi hi1
    (fun r' => exists_exit_of_tendsto_cocompact hω _ z r')).symm

/-- Nested exit trials after the first hit of `z` by a measurable, almost surely proper random
plane curve whose law is invariant under re-rooting at `z` and rescaling by each radius `r k`:
if, at every step `k`, the integrated lower bound `p` holds for a ball of radius `a / r k` in
the trace of `c` between its exits from `ball 0 1` and `ball 0 (Rk k)`, with
`r k * Rk k ≤ r (k + 1)`, then the event that no ball of radius `a` lies in the trace of `c`
between the first hit of `z` and its first exit from `ball z R` has probability at most
`exp (p ^ 2) exp (-(p ^ 2 / 2) (C ε)⁻¹)`. -/
theorem measureReal_firstExitTrace_failure_le_floor_inv_of_rerootedExitWindow
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {c : Ω → C(ℝ, ℂ)} (hc : Measurable c)
    (hprop : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ)) (z : ℂ)
    {r : ℕ → ℝ} (hr : Monotone r) (Rk : ℕ → ℝ) {R a C ε p : ℝ} (ha : 0 < a)
    (hrR : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, r (k + 1) ≤ R)
    (hpos : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, 0 < r k)
    (hRk : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, r k * Rk k ≤ r (k + 1))
    (hmap : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1,
      P.map (fun ω => affineReroot z (r k) 0 (c ω)) = P.map c)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbound : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ S : Set (ℝ × C(ℝ, ℂ)), MeasurableSet S →
      ENNReal.ofReal p * P {ω | originExitWindow 1 (c ω) ∈ S} ≤
        P ({ω | originExitWindow 1 (c ω) ∈ S} ∩
          {ω | ∃ x, ball x (a / r k) ⊆ c ω '' Icc (exitTimeAfter (c ω) 0 0 1)
            (exitTimeAfter (c ω) 0 0 (Rk k))})) :
    P.real {ω | ¬ ∃ w, ball w a ⊆ c ω '' Icc (firstHit (c ω) z)
      (sInf {t : ℝ | firstHit (c ω) z ≤ t ∧ c ω t ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  refine measureReal_firstExitTrace_failure_le_floor_inv_of_perStepHistory
    (fun k => eventuallyMeasurableSpace (MeasurableSpace.comap
      (fun ω => rerootedExitWindow (c ω) z (r k)) inferInstance) (ae P) ⊓ m)
    (fun ω => ⇑(c ω)) (fun ω => firstHit (c ω) z) z r R a C ε
    (fun k hk => ⟨(hr (Nat.le_succ k)).trans (hrR k hk), hrR k hk⟩) ?_
    (fun _ _ => inf_le_right)
    (fun k _ => measurableSet_nestedExitTrialEvent_complex hc (measurable_firstHit_const hc z)
      z r ha k) ?_ hp0 hp1 ?_
  · filter_upwards [hprop] with ω hω
    obtain ⟨t, ht0, htR⟩ := exists_exit_of_tendsto_cocompact hω (firstHit (c ω) z) z R
    refine ⟨(c ω).continuous, ?_⟩
    have hsum : firstHit (c ω) z + (((t - firstHit (c ω) z).toNNReal : ℝ≥0) : ℝ) = t := by
      rw [Real.coe_toNNReal _ (sub_nonneg.2 ht0)]
      ring
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top
      (openExitTime_le_of_not_mem (B := fun s (_ : Unit) => c ω (firstHit (c ω) z + (s : ℝ)))
        (U := ball z R) (ω := ())
        (by show c ω (firstHit (c ω) z + _) ∉ ball z R; rw [hsum]; exact htR))
  · intro k _ i hi
    exact MeasurableSpace.measurableSet_inf.2
      ⟨nestedExitTrialEvent_mem_completed_rerootedExitWindow P c hprop z r ha
        (hr hi.le) (hr (Nat.succ_le_of_lt hi)),
       measurableSet_nestedExitTrialEvent_complex hc (measurable_firstHit_const hc z) z r ha i⟩
  · intro k hk
    have h := le_condExp_nestedExitTrial_rerootedExitWindow hc hprop z r k (hpos k hk)
      (hmap k hk) (div_pos ha (hpos k hk)) (hRk k hk) (hbound k hk)
    rw [mul_div_cancel₀ a (hpos k hk).ne'] at h
    exact h

end LatticeProb
