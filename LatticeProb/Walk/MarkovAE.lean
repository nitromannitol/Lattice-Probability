/-
The strong Markov property of simple random walk on the lattice at an almost
surely finite stopping time.

`LatticeProb.markov_stopping` asks for a stopping time bounded by a horizon `N`.
The times the papers stop at are hitting times, which are finite almost surely
but not bounded, and which take the value `⊤` on the null set where the target
is never reached.  Such a time is a function into `ℕ∞`, and `ENat.toNat` sends
`⊤` to `0`, so the composite is not a stopping time in the bounded sense: the
value `0` on a trajectory that never hits is not settled by the position at time
`0`.  What is a bounded stopping time is the truncation `stopTrunc τ N`, equal to
`τ` where `τ ≤ N` and to `N` elsewhere.

The identity at `τ` is obtained from the identities at the truncations by
dominated convergence.  The conditioning datum is multiplied by the indicator of
`{τ ≤ N}`, which is settled by the positions up to the truncation, and the
events `{τ ≤ N}` increase to `{τ < ⊤}`, a set of full measure.  Both integrands
are bounded by the product of the two bounds, so a constant dominates and no
integrability hypothesis beyond boundedness is needed.
-/
import LatticeProb.Walk.Markov

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-! ### Measurability at a bounded stopping time -/

/-- The expectation of a bounded function of the path is bounded by the same
constant. -/
theorem norm_pathExpect_le [NeZero d] {F : (ℕ → Site d) → ℝ} {CF : ℝ} (hFb : ∀ X, ‖F X‖ ≤ CF)
    (y : Site d) : ‖pathExpect d F y‖ ≤ CF := by
  have := norm_integral_le_of_norm_le_const (μ := siteWalkLaw d y) (C := CF)
    (Filter.Eventually.of_forall hFb)
  simpa [pathExpect, measureReal_def] using this

/-- A bounded stopping time takes finitely many values, so the path shifted by it
is a finite sum of indicators and the composite is measurable. -/
theorem measurable_comp_shiftPath_stopping {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ)
    {N : ℕ} (hτN : ∀ X, τ X ≤ N) {f : (ℕ → Site d) → ℝ} (hf : Measurable f) :
    Measurable fun X => f (shiftPath (τ X) X) := by
  classical
  have hτm : Measurable τ := measurable_isWalkStopping hτ hτN
  have hrepr : (fun X => f (shiftPath (τ X) X))
      = fun X => ∑ k ∈ Finset.range (N + 1),
          Set.indicator {Y : ℕ → Site d | τ Y = k} (fun Y => f (shiftPath k Y)) X := by
    funext X
    rw [Finset.sum_eq_single_of_mem (τ X)
      (Finset.mem_range.mpr (by have := hτN X; omega))]
    · exact (Set.indicator_of_mem (show X ∈ {Y : ℕ → Site d | τ Y = τ X} from rfl)
        (fun Y => f (shiftPath (τ X) Y))).symm
    · intro b _ hb
      exact Set.indicator_of_notMem (fun hc => hb hc.symm) _
  rw [hrepr]
  exact Finset.measurable_sum _ fun k _ =>
    (hf.comp (measurable_shiftPath k)).indicator (hτm (MeasurableSet.singleton k))

/-- The position at a bounded stopping time is measurable. -/
theorem measurable_comp_apply_stopping {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ)
    {N : ℕ} (hτN : ∀ X, τ X ≤ N) {g : Site d → ℝ} (hg : Measurable g) :
    Measurable fun X : ℕ → Site d => g (X (τ X)) := by
  classical
  have hτm : Measurable τ := measurable_isWalkStopping hτ hτN
  have hrepr : (fun X : ℕ → Site d => g (X (τ X)))
      = fun X => ∑ k ∈ Finset.range (N + 1),
          Set.indicator {Y : ℕ → Site d | τ Y = k} (fun Y => g (Y k)) X := by
    funext X
    rw [Finset.sum_eq_single_of_mem (τ X)
      (Finset.mem_range.mpr (by have := hτN X; omega))]
    · exact (Set.indicator_of_mem (show X ∈ {Y : ℕ → Site d | τ Y = τ X} from rfl)
        (fun Y => g (Y (τ X)))).symm
    · intro b _ hb
      exact Set.indicator_of_notMem (fun hc => hb hc.symm) _
  rw [hrepr]
  exact Finset.measurable_sum _ fun k _ =>
    (hg.comp (measurable_pi_apply k)).indicator (hτm (MeasurableSet.singleton k))

/-! ### Stopping times with values in `ℕ∞` -/

/-- `τ`, with values in `ℕ∞`, is a stopping time of the walk: that it takes the
finite value `k` is settled by the positions up to time `k`.  Unlike
`IsWalkStopping` this allows the value `⊤`, on the trajectories where the time is
never attained. -/
def IsWalkStoppingE (τ : (ℕ → Site d) → ℕ∞) : Prop :=
  ∀ (k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) → τ X = (k : ℕ∞) → τ Y = (k : ℕ∞)

/-- The truncation of a stopping time at the horizon `N`. -/
def stopTrunc (τ : (ℕ → Site d) → ℕ∞) (N : ℕ) (X : ℕ → Site d) : ℕ :=
  if τ X ≤ (N : ℕ∞) then (τ X).toNat else N

theorem stopTrunc_le (τ : (ℕ → Site d) → ℕ∞) (N : ℕ) (X : ℕ → Site d) :
    stopTrunc τ N X ≤ N := by
  rw [stopTrunc]
  split
  · rename_i h
    obtain ⟨n₀, hn₀, hle⟩ := ENat.le_coe_iff.mp h
    rw [hn₀, ENat.toNat_coe]; exact hle
  · exact le_rfl

theorem stopTrunc_of_le {τ : (ℕ → Site d) → ℕ∞} {N : ℕ} {X : ℕ → Site d}
    (h : τ X ≤ (N : ℕ∞)) : stopTrunc τ N X = (τ X).toNat := if_pos h

/-- The truncation of a stopping time is a bounded stopping time. -/
theorem isWalkStopping_stopTrunc {τ : (ℕ → Site d) → ℕ∞} (hτ : IsWalkStoppingE τ) (N : ℕ) :
    IsWalkStopping (stopTrunc τ N) := by
  intro k X Y hXY hk
  by_cases hX : τ X ≤ (N : ℕ∞)
  · obtain ⟨n₀, hn₀, hle⟩ := ENat.le_coe_iff.mp hX
    have hk' : n₀ = k := by
      rw [stopTrunc, if_pos hX, hn₀, ENat.toNat_coe] at hk; exact hk
    have hY : τ Y = (n₀ : ℕ∞) := hτ n₀ X Y (fun j hj => hXY j (hk' ▸ hj)) hn₀
    have hYle : τ Y ≤ (N : ℕ∞) := by rw [hY]; exact_mod_cast hle
    rw [stopTrunc, if_pos hYle, hY, ENat.toNat_coe]
    exact hk'
  · have hkN : N = k := by rw [stopTrunc, if_neg hX] at hk; exact hk
    have hYnot : ¬ (τ Y ≤ (N : ℕ∞)) := by
      intro hY
      obtain ⟨m, hm, hmN⟩ := ENat.le_coe_iff.mp hY
      refine hX ?_
      rw [hτ m Y X (fun j hj => (hXY j (hkN ▸ (hj.trans hmN))).symm) hm]
      exact_mod_cast hmN
    rw [stopTrunc, if_neg hYnot]
    exact hkN

/-! ### The strong Markov property at an almost surely finite stopping time -/

/-- **The strong Markov property at an almost surely finite stopping time.**  For
a bounded measurable `F` on paths, an `ℕ∞`-valued stopping time `τ` which is
finite almost surely, and a bounded `H` which on the event `τ = k` is settled by
the positions up to time `k`,
`E_x[F(θ_τ X) H(X)] = E_x[E_{X_τ}[F] H(X)]`.

`τ` is not assumed bounded, so `LatticeProb.markov_stopping` does not apply to it.
The identity is obtained from the truncations `stopTrunc τ N`, which are bounded
stopping times, by dominated convergence along `N`. -/
theorem markov_stopping_ae (d : ℕ) [NeZero d] (x : Site d)
    (τ : (ℕ → Site d) → ℕ∞) (hτ : IsWalkStoppingE τ)
    (hfin : ∀ᵐ X ∂(siteWalkLaw d x), τ X ≠ ⊤)
    (F : (ℕ → Site d) → ℝ) (hFm : Measurable F) (CF : ℝ) (hFb : ∀ X, ‖F X‖ ≤ CF)
    (H : (ℕ → Site d) → ℝ) (CH : ℝ) (hHb : ∀ X, ‖H X‖ ≤ CH)
    (hHdep : ∀ (k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) →
      τ X = (k : ℕ∞) → H X = H Y) :
    ∫ X, F (shiftPath (τ X).toNat X) * H X ∂(siteWalkLaw d x)
      = ∫ X, pathExpect d F (X (τ X).toNat) * H X ∂(siteWalkLaw d x) := by
  classical
  have hCF : 0 ≤ CF := le_trans (norm_nonneg _) (hFb fun _ => 0)
  have hCH : 0 ≤ CH := le_trans (norm_nonneg _) (hHb fun _ => 0)
  set HN : ℕ → (ℕ → Site d) → ℝ :=
    fun N X => H X * (if τ X ≤ (N : ℕ∞) then 1 else 0) with hHNdef
  have hHNb : ∀ (N : ℕ) (X : ℕ → Site d), ‖HN N X‖ ≤ CH := by
    intro N X
    rw [hHNdef]
    by_cases h : τ X ≤ (N : ℕ∞)
    · simpa [h] using hHb X
    · simpa [h] using hCH
  have hHNdep : ∀ (N k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) →
      stopTrunc τ N X = k → HN N X = HN N Y := by
    intro N k X Y hXY hk
    by_cases hX : τ X ≤ (N : ℕ∞)
    · obtain ⟨n₀, hn₀, hle⟩ := ENat.le_coe_iff.mp hX
      have hk' : n₀ = k := by
        rw [stopTrunc, if_pos hX, hn₀, ENat.toNat_coe] at hk; exact hk
      have hY : τ Y = (n₀ : ℕ∞) := hτ n₀ X Y (fun j hj => hXY j (hk' ▸ hj)) hn₀
      have hYle : τ Y ≤ (N : ℕ∞) := by rw [hY]; exact_mod_cast hle
      have hHXY : H X = H Y := hHdep k X Y hXY (hk' ▸ hn₀)
      simp [hHNdef, hX, hYle, hHXY]
    · have hkN : N = k := by rw [stopTrunc, if_neg hX] at hk; exact hk
      have hYnot : ¬ (τ Y ≤ (N : ℕ∞)) := by
        intro hY
        obtain ⟨m, hm, hmN⟩ := ENat.le_coe_iff.mp hY
        refine hX ?_
        rw [hτ m Y X (fun j hj => (hXY j (hkN ▸ (hj.trans hmN))).symm) hm]
        exact_mod_cast hmN
      simp [hHNdef, hX, hYnot]
  have hHNdepUpTo : ∀ N : ℕ, DependsUpTo N (HN N) := by
    intro N X Y hXY
    exact hHNdep N (stopTrunc τ N X) X Y
      (fun j hj => hXY j (le_trans hj (stopTrunc_le τ N X))) rfl
  have hstop : ∀ N : ℕ,
      ∫ X, F (shiftPath (stopTrunc τ N X) X) * HN N X ∂(siteWalkLaw d x)
        = ∫ X, pathExpect d F (X (stopTrunc τ N X)) * HN N X ∂(siteWalkLaw d x) :=
    fun N => markov_stopping d N x (stopTrunc τ N) (isWalkStopping_stopTrunc hτ N)
      (stopTrunc_le τ N) F hFm hFb (HN N) (hHNb N) (hHNdep N)
  set A : ℕ → (ℕ → Site d) → ℝ :=
    fun N X => F (shiftPath (stopTrunc τ N X) X) * HN N X with hAdef
  set B : ℕ → (ℕ → Site d) → ℝ :=
    fun N X => pathExpect d F (X (stopTrunc τ N X)) * HN N X with hBdef
  have hAm : ∀ N, Measurable (A N) := fun N =>
    (measurable_comp_shiftPath_stopping (isWalkStopping_stopTrunc hτ N)
        (stopTrunc_le τ N) hFm).mul (measurable_of_dependsUpTo (hHNdepUpTo N))
  have hBm : ∀ N, Measurable (B N) := fun N =>
    (measurable_comp_apply_stopping (isWalkStopping_stopTrunc hτ N)
        (stopTrunc_le τ N) (measurable_pathExpect d F)).mul
      (measurable_of_dependsUpTo (hHNdepUpTo N))
  have hAb : ∀ (N : ℕ) (X : ℕ → Site d), ‖A N X‖ ≤ CF * CH := by
    intro N X
    rw [hAdef]
    simp only [norm_mul]
    exact mul_le_mul (hFb _) (hHNb N X) (norm_nonneg _) hCF
  have hBb : ∀ (N : ℕ) (X : ℕ → Site d), ‖B N X‖ ≤ CF * CH := by
    intro N X
    rw [hBdef]
    simp only [norm_mul]
    exact mul_le_mul (norm_pathExpect_le hFb _) (hHNb N X) (norm_nonneg _) hCF
  have hev : ∀ X : ℕ → Site d, τ X ≠ ⊤ →
      ∀ᶠ N : ℕ in Filter.atTop, τ X ≤ (N : ℕ∞) := by
    intro X hX
    filter_upwards [Filter.eventually_ge_atTop ((τ X).toNat)] with N hN
    rw [← ENat.coe_toNat_eq_self.mpr hX]
    exact_mod_cast hN
  have hlimA : ∀ᵐ X ∂(siteWalkLaw d x),
      Filter.Tendsto (fun N => A N X) Filter.atTop
        (nhds (F (shiftPath (τ X).toNat X) * H X)) := by
    filter_upwards [hfin] with X hX
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev X hX] with N hN
    show F (shiftPath (τ X).toNat X) * H X = A N X
    rw [hAdef, hHNdef]
    simp only [stopTrunc_of_le hN, hN, if_true, mul_one]
  have hlimB : ∀ᵐ X ∂(siteWalkLaw d x),
      Filter.Tendsto (fun N => B N X) Filter.atTop
        (nhds (pathExpect d F (X (τ X).toNat) * H X)) := by
    filter_upwards [hfin] with X hX
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev X hX] with N hN
    show pathExpect d F (X (τ X).toNat) * H X = B N X
    rw [hBdef, hHNdef]
    simp only [stopTrunc_of_le hN, hN, if_true, mul_one]
  have hAint := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := siteWalkLaw d x) (F := A)
    (f := fun X => F (shiftPath (τ X).toNat X) * H X)
    (fun _ => CF * CH) (fun N => (hAm N).aestronglyMeasurable)
    (integrable_const _) (fun N => Filter.Eventually.of_forall (hAb N)) hlimA
  have hBint := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := siteWalkLaw d x) (F := B)
    (f := fun X => pathExpect d F (X (τ X).toNat) * H X)
    (fun _ => CF * CH) (fun N => (hBm N).aestronglyMeasurable)
    (integrable_const _) (fun N => Filter.Eventually.of_forall (hBb N)) hlimB
  exact tendsto_nhds_unique (hAint.congr fun N => hstop N) hBint

end LatticeProb
