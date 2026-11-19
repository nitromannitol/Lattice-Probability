import LatticeProb.Topology.StoppedNestedExitTrial
import LatticeProb.Prob.FirstHitRandomRoot

/-!
# Ball absorption by first-exit traces, transported along isometries

Exit times from balls, ball absorption by traces and the nested exit trials are invariant
under an isometric equivalence of the target space. Consequently the inverse-scale
exponential bound for the failure of a first-exit trace to absorb a ball, proved for
continuous curves in Euclidean space, holds for curves in any isometric copy of it, in
particular in `ℂ`.

The last theorem is a variant of the ball-absorption estimate of Gwynne–Holden–Miller
(*An almost sure KPZ relation for SLE and Brownian motion*, Lemma 3.6) with their trials: the
curve starts at its first hitting time of `z`, the trials are the traces between the first
exits from `B_{(k+1) C ε ρ}(z)` and `B_{(k+2) C ε ρ}(z)`, and a success is a ball of radius
`ε ρ`. If each trial succeeds with conditional probability at least `p` given a history
containing the completed σ-algebra of the hitting time, the inner exit time and the curve
stopped at the inner exit, then the trace up to the first exit from `B_ρ(z)` misses every ball
of radius `ε ρ` with probability at most `exp (p ^ 2) * exp (-(p ^ 2 / 2) * (C ε)⁻¹)`.

The curve is indexed by `ℝ` and stopped on all of `ℝ`, so this history contains the whole
past of the curve before the inner exit (including negative times) and the absolute times.
It is larger than the history in their (3.6), which is the curve on `[0, τ_z(ρ_ε(k))]`
only; the conditional success hypothesis here is therefore stronger than (3.6) and is not
implied by it.

## Main statements

* `nestedExitTrialEvent_isometryEquiv`: nested exit trials are invariant under isometric
  equivalences.
* `measureReal_firstExitTrace_failure_le_floor_inv_of_isometryEquiv`: the completed-history
  failure bound for curves in an isometric copy of Euclidean space.
* `measureReal_firstHit_ballAbsorption_failure_le`: a first-hit form in `ℂ`.
-/

set_option autoImplicit false

open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

section Isometry

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- The times after `t₀` spent outside a ball are invariant under an isometric equivalence. -/
theorem setOf_exit_isometryEquiv (φ : E ≃ᵢ F) (w : ℝ → E) (t₀ : ℝ) (z : E) (ρ : ℝ) :
    {t : ℝ | t₀ ≤ t ∧ φ (w t) ∉ ball (φ z) ρ} = {t : ℝ | t₀ ≤ t ∧ w t ∉ ball z ρ} := by
  ext t
  simp only [mem_ofPred_eq, mem_ball, φ.dist_eq]

/-- A trace contains a ball of radius `a` if and only if its image under an isometric
equivalence does. -/
theorem exists_ball_subset_image_isometryEquiv (φ : E ≃ᵢ F) (w : ℝ → E) (I : Set ℝ)
    (a : ℝ) :
    (∃ v, ball v a ⊆ (fun t => φ (w t)) '' I) ↔ ∃ v, ball v a ⊆ w '' I := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨φ.symm v, fun x hx => ?_⟩
    have hd := φ.dist_eq x (φ.symm v)
    rw [φ.apply_symm_apply] at hd
    have hx' : φ x ∈ ball v a := by
      rw [mem_ball] at hx ⊢
      rwa [hd]
    obtain ⟨t, ht, hte⟩ := hv hx'
    exact ⟨t, ht, φ.injective hte⟩
  · rintro ⟨v, hv⟩
    refine ⟨φ v, fun y hy => ?_⟩
    have hd := φ.symm.dist_eq y (φ v)
    rw [φ.symm_apply_apply] at hd
    have hy' : φ.symm y ∈ ball v a := by
      rw [mem_ball] at hy ⊢
      rwa [hd]
    obtain ⟨t, ht, hte⟩ := hv hy'
    refine ⟨t, ht, ?_⟩
    show φ (w t) = y
    rw [hte, φ.apply_symm_apply]

/-- Nested exit trials are invariant under an isometric equivalence of the target. -/
theorem nestedExitTrialEvent_isometryEquiv {Ω : Type*} (φ : E ≃ᵢ F) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    nestedExitTrialEvent (fun ω t => φ (η ω t)) t₀ (φ z) r a k =
      nestedExitTrialEvent η t₀ z r a k := by
  ext ω
  show (∃ v, ball v a ⊆ (fun t => φ (η ω t)) '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ φ (η ω t) ∉ ball (φ z) (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ φ (η ω t) ∉ ball (φ z) (r (k + 1))})) ↔ _
  rw [setOf_exit_isometryEquiv, setOf_exit_isometryEquiv]
  exact exists_ball_subset_image_isometryEquiv φ (η ω) _ a

/-- The failure of a first-exit trace to absorb a ball is invariant under an isometric
equivalence of the target. -/
theorem setOf_not_exists_ball_subset_firstExitTrace_isometryEquiv {Ω : Type*} (φ : E ≃ᵢ F)
    (η : Ω → ℝ → E) (t₀ : Ω → ℝ) (z : E) (R a : ℝ) :
    {ω | ¬ ∃ v, ball v a ⊆ (fun t => φ (η ω t)) '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ φ (η ω t) ∉ ball (φ z) R})} =
    {ω | ¬ ∃ v, ball v a ⊆ η ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z R})} := by
  ext ω
  show (¬ ∃ v, ball v a ⊆ (fun t => φ (η ω t)) '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ φ (η ω t) ∉ ball (φ z) R})) ↔ _
  rw [setOf_exit_isometryEquiv]
  exact not_congr (exists_ball_subset_image_isometryEquiv φ (η ω) _ a)

end Isometry

/-- Enlarging the underlying σ-algebra enlarges its completion along a filter. -/
theorem eventuallyMeasurableSpace_le_of_le {α : Type*} {m₁ m₂ : MeasurableSpace α}
    (h : m₁ ≤ m₂) (l : Filter α) [CountableInterFilter l] :
    eventuallyMeasurableSpace m₁ l ≤ eventuallyMeasurableSpace m₂ l := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hs
  exact ⟨t, h t ht, hst⟩

/-- **Nested-exit failure bound in an isometric copy of Euclidean space.** For a measurable
random continuous curve `c` in a space `E` isometric to `ℝ^d`, started at a measurable time
`t₀`, if the `k`-th nested exit trial succeeds with conditional probability at least `p`
given a sub-σ-algebra `G k` containing the completion of `σ(t₀, T_k, c(· ∧ T_k))`
(`T_k` the first exit after `t₀` from `B_{r k}(z)`), then the trace up to the first exit
from `B_R(z)` misses every ball of radius `a` with probability at most
`exp (p ^ 2) * exp (-(p ^ 2 / 2) * (C ε)⁻¹)`. -/
theorem measureReal_firstExitTrace_failure_le_floor_inv_of_isometryEquiv
    {Ω E : Type*} [PseudoMetricSpace E] {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (φ : E ≃ᵢ EuclideanSpace ℝ (Fin d))
    (G : ℕ → MeasurableSpace Ω) {c : Ω → C(ℝ, E)} {t₀ : Ω → ℝ}
    (hc : Measurable c) (ht₀ : Measurable t₀) (z : E)
    {r : ℕ → ℝ} (hr : Monotone r) {R a C ε : ℝ} (ha : 0 < a)
    (hrR : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, r (k + 1) ≤ R)
    (hexit : ∀ᵐ ω ∂μ, ∃ t, t₀ ω ≤ t ∧ c ω t ∉ ball z R)
    (hG : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, G k ≤ m)
    (hGO : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1,
      eventuallyMeasurableSpace (MeasurableSpace.comap (fun ω => (t₀ ω,
        sInf {t : ℝ | t₀ ω ≤ t ∧ c ω t ∉ ball z (r k)},
        realStoppedCurve (sInf {t : ℝ | t₀ ω ≤ t ∧ c ω t ∉ ball z (r k)}) (c ω)))
          inferInstance) (ae μ) ≤ G k)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ ω ∂μ,
      p ≤ μ[(nestedExitTrialEvent (fun ω => ⇑(c ω)) t₀ z r a k).indicator
        (fun _ => (1 : ℝ)) | G k] ω) :
    μ.real {ω | ¬ ∃ w, ball w a ⊆ c ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ c ω t ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  let eC : C(E, EuclideanSpace ℝ (Fin d)) := ⟨φ, φ.continuous⟩
  let g : Ω → C(ℝ, EuclideanSpace ℝ (Fin d)) := fun ω => eC.comp (c ω)
  have hpost : Measurable fun w : C(ℝ, E) => eC.comp w :=
    (ContinuousMap.continuous_postcomp eC).measurable
  have hg : Measurable g := hpost.comp hc
  have hset : ∀ ω ρ, {t : ℝ | t₀ ω ≤ t ∧ g ω t ∉ ball (φ z) ρ} =
      {t : ℝ | t₀ ω ≤ t ∧ c ω t ∉ ball z ρ} := fun ω ρ =>
    setOf_exit_isometryEquiv φ (c ω) (t₀ ω) z ρ
  have hexit' : ∀ᵐ ω ∂μ, ∃ t, t₀ ω ≤ t ∧ g ω t ∉ ball (φ z) R := by
    filter_upwards [hexit] with ω hω
    obtain ⟨t, ht, htR⟩ := hω
    refine ⟨t, ht, ?_⟩
    show φ (c ω t) ∉ ball (φ z) R
    rwa [mem_ball, φ.dist_eq]
  let Ψ : ℝ × ℝ × C(ℝ, E) → ℝ × ℝ × C(ℝ, EuclideanSpace ℝ (Fin d)) :=
    fun x => (x.1, x.2.1, eC.comp x.2.2)
  have hΨ : Measurable Ψ :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (hpost.comp (measurable_snd.comp measurable_snd)))
  have hGO' : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1,
      eventuallyMeasurableSpace (MeasurableSpace.comap (fun ω => (t₀ ω,
        sInf {t : ℝ | t₀ ω ≤ t ∧ g ω t ∉ ball (φ z) (r k)},
        realStoppedCurve (sInf {t : ℝ | t₀ ω ≤ t ∧ g ω t ∉ ball (φ z) (r k)}) (g ω)))
          inferInstance) (ae μ) ≤ G k := by
    intro k hk
    have hfun : (fun ω => (t₀ ω,
        sInf {t : ℝ | t₀ ω ≤ t ∧ g ω t ∉ ball (φ z) (r k)},
        realStoppedCurve (sInf {t : ℝ | t₀ ω ≤ t ∧ g ω t ∉ ball (φ z) (r k)}) (g ω))) =
        Ψ ∘ (fun ω => (t₀ ω, sInf {t : ℝ | t₀ ω ≤ t ∧ c ω t ∉ ball z (r k)},
          realStoppedCurve (sInf {t : ℝ | t₀ ω ≤ t ∧ c ω t ∉ ball z (r k)}) (c ω))) := by
      funext ω
      rw [Function.comp_apply, hset]
      rfl
    refine le_trans (eventuallyMeasurableSpace_le_of_le ?_ (ae μ)) (hGO k hk)
    rw [hfun, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hΨ.comap_le
  have hp' : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ ω ∂μ,
      p ≤ μ[(nestedExitTrialEvent (fun ω => ⇑(g ω)) t₀ (φ z) r a k).indicator
        (fun _ => (1 : ℝ)) | G k] ω := by
    intro k hk
    have hev : nestedExitTrialEvent (fun ω => ⇑(g ω)) t₀ (φ z) r a k =
        nestedExitTrialEvent (fun ω => ⇑(c ω)) t₀ z r a k :=
      nestedExitTrialEvent_isometryEquiv φ (fun ω => ⇑(c ω)) t₀ z r a k
    rw [hev]
    exact hp k hk
  have key := measureReal_firstExitTrace_failure_le_floor_inv_of_completed_stopped_history
    G hg ht₀ (φ z) hr ha hrR hexit' hG hGO' hp0 hp1 hp'
  have hfail : {ω | ¬ ∃ w, ball w a ⊆ g ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ g ω t ∉ ball (φ z) R})} =
      {ω | ¬ ∃ w, ball w a ⊆ c ω '' Icc (t₀ ω)
        (sInf {t : ℝ | t₀ ω ≤ t ∧ c ω t ∉ ball z R})} :=
    setOf_not_exists_ball_subset_firstExitTrace_isometryEquiv φ (fun ω => ⇑(c ω)) t₀ z R a
  rw [← hfail]
  exact key

/-- **Ball absorption after the first hit** (a variant of Gwynne–Holden–Miller, Lemma 3.6, from
a conditional success bound that is stronger than their (3.6), see the module docstring).
Let `c` be a measurable random continuous curve in `ℂ`, `τ_z` its first hitting time
of `z`, and `ρ, C, ε > 0`. Suppose the curve almost surely leaves `B_ρ(z)` after `τ_z`, and,
for every `k < ⌊(C ε)⁻¹⌋₊ - 1`, the trace of `c` between its first exits after `τ_z` from
`B_{(k+1) C ε ρ}(z)` and `B_{(k+2) C ε ρ}(z)` contains a ball of radius `ε ρ` with
conditional probability at least `p` given a sub-σ-algebra `G k` containing the completed
σ-algebra of `τ_z`, the inner exit time and the curve stopped there. Then the trace
`c([τ_z, τ_z(ρ)])` misses every ball of radius `ε ρ` with probability at most
`exp (p ^ 2) * exp (-(p ^ 2 / 2) * (C ε)⁻¹)`.

For an index `k` in range, `hG k` and `hGO k` together force `m` to contain every `μ`-null
set (the completion enters through `eventuallyMeasurableSpace`), so with a nonempty range of
trials the hypotheses can hold only when `m` is complete for `μ`. -/
theorem measureReal_firstHit_ballAbsorption_failure_le
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : ℕ → MeasurableSpace Ω) {c : Ω → C(ℝ, ℂ)} (hc : Measurable c) (z : ℂ)
    {ρ C ε : ℝ} (hρ : 0 < ρ) (hC : 0 < C) (hε : 0 < ε)
    (hexit : ∀ᵐ ω ∂μ, ∃ t, MatedCRTHarmonic.GMS4b.hitTime (c ω) z ≤ t ∧ c ω t ∉ ball z ρ)
    (hG : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, G k ≤ m)
    (hGO : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1,
      eventuallyMeasurableSpace (MeasurableSpace.comap (fun ω =>
        (MatedCRTHarmonic.GMS4b.hitTime (c ω) z,
          sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (c ω) z ≤ t ∧
            c ω t ∉ ball z (((k : ℝ) + 1) * C * ε * ρ)},
          realStoppedCurve (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (c ω) z ≤ t ∧
            c ω t ∉ ball z (((k : ℝ) + 1) * C * ε * ρ)}) (c ω))) inferInstance) (ae μ) ≤ G k)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ ω ∂μ,
      p ≤ μ[(nestedExitTrialEvent (fun ω => ⇑(c ω))
        (fun ω => MatedCRTHarmonic.GMS4b.hitTime (c ω) z) z
        (fun k : ℕ => ((k : ℝ) + 1) * C * ε * ρ) (ε * ρ) k).indicator
        (fun _ => (1 : ℝ)) | G k] ω) :
    μ.real {ω | ¬ ∃ w, ball w (ε * ρ) ⊆ c ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (c ω) z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (c ω) z ≤ t ∧ c ω t ∉ ball z ρ})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  have hCε : 0 < C * ε := mul_pos hC hε
  have h0 : 0 ≤ C * ε * ρ := (mul_pos hCε hρ).le
  refine measureReal_firstExitTrace_failure_le_floor_inv_of_isometryEquiv
    Complex.orthonormalBasisOneI.repr.toIsometryEquiv G hc
    (measurable_firstHitTime hc measurable_const) z
    (r := fun k : ℕ => ((k : ℝ) + 1) * C * ε * ρ) ?_ (mul_pos hε hρ) ?_ hexit hG hGO
    hp0 hp1 hp
  · intro i j hij
    have hij' : (i : ℝ) ≤ j := Nat.cast_le.2 hij
    show ((i : ℝ) + 1) * C * ε * ρ ≤ ((j : ℝ) + 1) * C * ε * ρ
    calc ((i : ℝ) + 1) * C * ε * ρ = ((i : ℝ) + 1) * (C * ε * ρ) := by ring
      _ ≤ ((j : ℝ) + 1) * (C * ε * ρ) := mul_le_mul_of_nonneg_right (by linarith) h0
      _ = ((j : ℝ) + 1) * C * ε * ρ := by ring
  · intro k hk
    have hk2 : k + 2 ≤ ⌊(C * ε)⁻¹⌋₊ := by omega
    have hfl : ((k + 2 : ℕ) : ℝ) ≤ (C * ε)⁻¹ :=
      (Nat.cast_le.2 hk2).trans (Nat.floor_le (inv_nonneg.2 hCε.le))
    have h1 : ((k : ℝ) + 2) * (C * ε) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hfl hCε.le
      rwa [inv_mul_cancel₀ hCε.ne', Nat.cast_add, Nat.cast_ofNat] at h
    show (((k + 1 : ℕ) : ℝ) + 1) * C * ε * ρ ≤ ρ
    calc (((k + 1 : ℕ) : ℝ) + 1) * C * ε * ρ = ((k : ℝ) + 2) * (C * ε) * ρ := by
          push_cast; ring
      _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right h1 hρ.le
      _ = ρ := one_mul ρ

end LatticeProb
