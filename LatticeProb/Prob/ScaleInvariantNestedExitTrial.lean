import LatticeProb.Prob.RerootedNestedExitTrialFailure

/-!
# Nested exit trials of a scale-invariant random curve after a first hit

Let `c` be a measurable random continuous plane curve, proper almost surely, whose law is
invariant under re-rooting at `z` and rescaling by every `s > 0`
(`t ↦ s⁻¹ (c (τ_z + s ^ 2 t) - z)`, with `τ_z` the first hit of `z`). Suppose that, for some
`δ > 0` and `p`, uniformly in `ε ∈ (0, 1)` and in the measurable set `S` of exit windows, the
event that a ball of radius `δ ε` lies in the trace of `c` between its exits from `ball 0 1`
and from `ball 0 (1 + ε)` has probability at least `p` on the event that the exit window of
`c` at radius `1` lies in `S`, in integrated form.

With `C = 2 / δ` and the radii `r k = (k + 1) C ε ρ`, each nested exit trial after `τ_z`
(a ball of radius `ε ρ` in the trace between the exits from `ball z (r k)` and
`ball z (r (k + 1))`) then has conditional probability at least `p` given the re-rooted
forward window at radius `r k`, and the event that no ball of radius `ε ρ` lies in the trace
of `c` between `τ_z` and its exit from `ball z ρ` has probability at most
`exp (p ^ 2) exp (-(p ^ 2 / 2) (C ε)⁻¹)`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology

namespace LatticeProb

open MatedCRTHarmonic.MatedCRT

/-- The ratio `1 / (2 (k + 1))` of the trial `k` lies in `(0, 1)`. -/
theorem one_div_two_mul_succ_mem_Ioo (k : ℕ) : 1 / (2 * ((k : ℝ) + 1)) ∈ Ioo (0 : ℝ) 1 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- The ball radius `δ / (2 (k + 1))` at scale `(k + 1) (2 / δ) ε ρ` is `ε ρ`. -/
theorem nestedTrialRadius_mul_eq {δ : ℝ} (hδ : δ ≠ 0) (ε ρ : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * (2 / δ) * ε * ρ * (δ * (1 / (2 * ((k : ℝ) + 1)))) = ε * ρ := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The outer radius `1 + 1 / (2 (k + 1))` at scale `r k = (k + 1) (2 / δ) ε ρ` stays below
`r (k + 1)`. -/
theorem nestedTrialRadius_mul_le {δ ε ρ : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (k : ℕ) :
    ((k : ℝ) + 1) * (2 / δ) * ε * ρ * (1 + 1 / (2 * ((k : ℝ) + 1))) ≤
      (((k + 1 : ℕ) : ℝ) + 1) * (2 / δ) * ε * ρ := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hdiff : (((k + 1 : ℕ) : ℝ) + 1) * (2 / δ) * ε * ρ -
      ((k : ℝ) + 1) * (2 / δ) * ε * ρ * (1 + 1 / (2 * ((k : ℝ) + 1))) = ε * ρ / δ := by
    push_cast
    field_simp
    ring
  have hpos : 0 ≤ ε * ρ / δ := by positivity
  linarith

/-- Per-step form: the `k`-th nested exit trial after the first hit of `z`, with radii
`r k = (k + 1) (2 / δ) ε ρ` and ball radius `ε ρ`, has conditional probability at least `p`
given the completed σ-algebra of the re-rooted forward window at radius `r k`. -/
theorem le_condExp_nestedExitTrial_rerootedExitWindow_of_scaleInvariant
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {c : Ω → C(ℝ, ℂ)} (hc : Measurable c)
    (hprop : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ)) (z : ℂ)
    (hmap : ∀ s : ℝ, 0 < s → P.map (fun ω => affineReroot z s 0 (c ω)) = P.map c)
    {δ p : ℝ} (hδ : 0 < δ)
    (hD3 : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ S : Set (ℝ × C(ℝ, ℂ)), MeasurableSet S →
      ENNReal.ofReal p * P {ω | originExitWindow 1 (c ω) ∈ S} ≤
        P ({ω | originExitWindow 1 (c ω) ∈ S} ∩
          {ω | ∃ x, ball x (δ * ε) ⊆ c ω '' Icc (exitTimeAfter (c ω) 0 0 1)
            (exitTimeAfter (c ω) 0 0 (1 + ε))}))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k : ℕ) :
    ∀ᵐ ω ∂P, p ≤ P[(nestedExitTrialEvent (fun ω => ⇑(c ω)) (fun ω => firstHit (c ω) z) z
        (fun k : ℕ => ((k : ℝ) + 1) * (2 / δ) * ε * ρ) (ε * ρ) k).indicator
          (fun _ => (1 : ℝ)) |
      eventuallyMeasurableSpace (MeasurableSpace.comap
        (fun ω => rerootedExitWindow (c ω) z (((k : ℝ) + 1) * (2 / δ) * ε * ρ)) inferInstance)
          (ae P) ⊓ m] ω := by
  have hrk : 0 < ((k : ℝ) + 1) * (2 / δ) * ε * ρ := by positivity
  have hε' := one_div_two_mul_succ_mem_Ioo k
  have h := le_condExp_nestedExitTrial_rerootedExitWindow hc hprop z
    (fun k : ℕ => ((k : ℝ) + 1) * (2 / δ) * ε * ρ) k hrk (hmap _ hrk)
    (mul_pos hδ hε'.1) (nestedTrialRadius_mul_le hδ hε.le hρ.le k) (hD3 _ hε')
  rw [nestedTrialRadius_mul_eq hδ.ne' ε ρ k] at h
  exact h

/-- Failure bound: the event that no ball of radius `ε ρ` lies in the trace of `c` between
the first hit of `z` and its first exit from `ball z ρ` has probability at most
`exp (p ^ 2) exp (-(p ^ 2 / 2) ((2 / δ) ε)⁻¹)`. -/
theorem measureReal_firstExitTrace_failure_le_of_scaleInvariant
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {c : Ω → C(ℝ, ℂ)} (hc : Measurable c)
    (hprop : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ)) (z : ℂ)
    (hmap : ∀ s : ℝ, 0 < s → P.map (fun ω => affineReroot z s 0 (c ω)) = P.map c)
    {δ p : ℝ} (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hD3 : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ S : Set (ℝ × C(ℝ, ℂ)), MeasurableSet S →
      ENNReal.ofReal p * P {ω | originExitWindow 1 (c ω) ∈ S} ≤
        P ({ω | originExitWindow 1 (c ω) ∈ S} ∩
          {ω | ∃ x, ball x (δ * ε) ⊆ c ω '' Icc (exitTimeAfter (c ω) 0 0 1)
            (exitTimeAfter (c ω) 0 0 (1 + ε))}))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    P.real {ω | ¬ ∃ w, ball w (ε * ρ) ⊆ c ω '' Icc (firstHit (c ω) z)
      (sInf {t : ℝ | firstHit (c ω) z ≤ t ∧ c ω t ∉ ball z ρ})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (2 / δ * ε)⁻¹) := by
  have hrpos : ∀ k : ℕ, 0 < ((k : ℝ) + 1) * (2 / δ) * ε * ρ := fun k => by positivity
  have hCε : 0 < 2 / δ * ε := by positivity
  refine measureReal_firstExitTrace_failure_le_floor_inv_of_rerootedExitWindow hc hprop z
    (r := fun k : ℕ => ((k : ℝ) + 1) * (2 / δ) * ε * ρ) ?_
    (fun k : ℕ => 1 + 1 / (2 * ((k : ℝ) + 1))) (mul_pos hε hρ) ?_ (fun k _ => hrpos k)
    (fun k _ => nestedTrialRadius_mul_le hδ hε.le hρ.le k) (fun k _ => hmap _ (hrpos k))
    hp0 hp1 ?_
  · intro i j hij
    have hij' : (i : ℝ) ≤ j := Nat.cast_le.2 hij
    dsimp only
    gcongr
  · intro k hk
    have h1 : ((k + 2 : ℕ) : ℝ) ≤ ⌊(2 / δ * ε)⁻¹⌋₊ := by
      exact_mod_cast (show k + 2 ≤ ⌊(2 / δ * ε)⁻¹⌋₊ by omega)
    have h2 : ((⌊(2 / δ * ε)⁻¹⌋₊ : ℕ) : ℝ) ≤ (2 / δ * ε)⁻¹ := Nat.floor_le (by positivity)
    have h4 : ((k : ℝ) + 2) * (2 / δ * ε) ≤ 1 := by
      push_cast at h1
      calc ((k : ℝ) + 2) * (2 / δ * ε) ≤ (2 / δ * ε)⁻¹ * (2 / δ * ε) :=
            mul_le_mul_of_nonneg_right (h1.trans h2) hCε.le
        _ = 1 := inv_mul_cancel₀ hCε.ne'
    show (((k + 1 : ℕ) : ℝ) + 1) * (2 / δ) * ε * ρ ≤ ρ
    calc (((k + 1 : ℕ) : ℝ) + 1) * (2 / δ) * ε * ρ = ((k : ℝ) + 2) * (2 / δ * ε) * ρ := by
          push_cast
          ring
      _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right h4 hρ.le
      _ = ρ := one_mul ρ
  · intro k _ S hS
    have hdiv : ε * ρ / (((k : ℝ) + 1) * (2 / δ) * ε * ρ) = δ * (1 / (2 * ((k : ℝ) + 1))) := by
      rw [div_eq_iff (hrpos k).ne']
      linear_combination -(nestedTrialRadius_mul_eq hδ.ne' ε ρ k)
    have h := hD3 _ (one_div_two_mul_succ_mem_Ioo k) S hS
    rw [hdiv]
    exact h

end LatticeProb
