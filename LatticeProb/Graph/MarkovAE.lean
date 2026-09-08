/-
The strong Markov property of the walk on a locally finite graph at an almost
surely finite stopping time.

`LatticeProb.Graph.markov_stopping` asks for a stopping time bounded by a horizon
`N`, and `LatticeProb.Graph.markov_exitTime` removes that restriction for the
exit time of a finite set.  The times a paper stops at are more general: hitting
times of co-finite sets, finite almost surely but not bounded, taking the value
`⊤` on the null set where the target is never reached.  Such a time is a function
into `ℕ∞`, and `ENat.toNat` sends `⊤` to `0`, so the composite is not a stopping
time in the bounded sense: the value `0` on a trajectory that never hits is not
settled by the position at time `0`.  What is a bounded stopping time is the
truncation `stopTrunc τ N`, equal to `τ` where `τ ≤ N` and to `N` elsewhere.

The identity at `τ` is obtained from the identities at the truncations by
dominated convergence, the same three moves as `markov_exitTime`: truncate at
`τ ∧ N`, kill the trajectories with `τ > N` in the conditioning datum, and pass
to the limit.  The events `{τ ≤ N}` increase to `{τ < ⊤}`, a set of full
measure.  Both integrands are bounded by the product of the two bounds, so a
constant dominates and no integrability hypothesis beyond boundedness is needed.
-/
import LatticeProb.Graph.ExitTime

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
variable [DecidableEq V]

/-! ### Stopping times with values in `ℕ∞` -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- `τ`, with values in `ℕ∞`, is a stopping time of the walk: that it takes the
finite value `k` is settled by the positions up to time `k`.  Unlike
`LatticeProb.Graph.IsStopping` this allows the value `⊤`, on the trajectories
where the time is never attained. -/
def IsWalkStoppingE (τ : (ℕ → V) → ℕ∞) : Prop :=
  ∀ (k : ℕ) (X Y : ℕ → V), (∀ j ≤ k, X j = Y j) → τ X = (k : ℕ∞) → τ Y = (k : ℕ∞)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The truncation of a stopping time at the horizon `N`. -/
def stopTrunc (τ : (ℕ → V) → ℕ∞) (N : ℕ) (X : ℕ → V) : ℕ :=
  if τ X ≤ (N : ℕ∞) then (τ X).toNat else N

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem stopTrunc_le (τ : (ℕ → V) → ℕ∞) (N : ℕ) (X : ℕ → V) :
    stopTrunc τ N X ≤ N := by
  rw [stopTrunc]
  split
  · rename_i h
    obtain ⟨n₀, hn₀, hle⟩ := ENat.le_coe_iff.mp h
    rw [hn₀, ENat.toNat_coe]; exact hle
  · exact le_rfl

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem stopTrunc_of_le {τ : (ℕ → V) → ℕ∞} {N : ℕ} {X : ℕ → V}
    (h : τ X ≤ (N : ℕ∞)) : stopTrunc τ N X = (τ X).toNat := if_pos h

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The truncation of a stopping time is a bounded stopping time. -/
theorem isStopping_stopTrunc {τ : (ℕ → V) → ℕ∞} (hτ : IsWalkStoppingE τ) (N : ℕ) :
    IsStopping (stopTrunc τ N) := by
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

/-- **The strong Markov property at an almost surely finite stopping time**, on
an arbitrary locally finite graph.  For a bounded measurable `F` on paths, an
`ℕ∞`-valued stopping time `τ` which is finite almost surely, and a bounded `H`
which on the event `τ = k` is settled by the positions up to time `k`,
`E_x[F(θ_τ X) H(X)] = E_x[E_{X_τ}[F] H(X)]`.

`τ` is not assumed bounded, so `LatticeProb.Graph.markov_stopping` does not apply
to it.  The identity is obtained from the truncations `stopTrunc τ N`, which are
bounded stopping times, by dominated convergence along `N`. -/
theorem markov_stopping_ae (hdeg : ∀ v : V, 0 < G.degree v) (x : V)
    (τ : (ℕ → V) → ℕ∞) (hτ : IsWalkStoppingE τ)
    (hfin : ∀ᵐ X ∂(walkLaw G x), τ X ≠ ⊤)
    (F : (ℕ → V) → ℝ) (hFm : Measurable F) (CF : ℝ) (hFb : ∀ X, ‖F X‖ ≤ CF)
    (H : (ℕ → V) → ℝ) (CH : ℝ) (hHb : ∀ X, ‖H X‖ ≤ CH)
    (hHdep : ∀ (k : ℕ) (X Y : ℕ → V), (∀ j ≤ k, X j = Y j) →
      τ X = (k : ℕ∞) → H X = H Y) :
    ∫ X, F (shiftPath (τ X).toNat X) * H X ∂(walkLaw G x)
      = ∫ X, pathExp G F (X (τ X).toNat) * H X ∂(walkLaw G x) := by
  classical
  have hCF : 0 ≤ CF := le_trans (norm_nonneg _) (hFb fun _ => x)
  have hCH : 0 ≤ CH := le_trans (norm_nonneg _) (hHb fun _ => x)
  set HN : ℕ → (ℕ → V) → ℝ :=
    fun N X => H X * (if τ X ≤ (N : ℕ∞) then 1 else 0) with hHNdef
  have hHNb : ∀ (N : ℕ) (X : ℕ → V), ‖HN N X‖ ≤ CH := by
    intro N X
    rw [hHNdef]
    by_cases h : τ X ≤ (N : ℕ∞)
    · simpa [h] using hHb X
    · simpa [h] using hCH
  have hHNdep : ∀ (N k : ℕ) (X Y : ℕ → V), (∀ j ≤ k, X j = Y j) →
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
      ∫ X, F (shiftPath (stopTrunc τ N X) X) * HN N X ∂(walkLaw G x)
        = ∫ X, pathExp G F (X (stopTrunc τ N X)) * HN N X ∂(walkLaw G x) :=
    fun N => markov_stopping hdeg N x (stopTrunc τ N) (isStopping_stopTrunc hτ N)
      (stopTrunc_le τ N) F hFm CF hFb (HN N) CH (hHNb N) (hHNdep N)
  set A : ℕ → (ℕ → V) → ℝ :=
    fun N X => F (shiftPath (stopTrunc τ N X) X) * HN N X with hAdef
  set B : ℕ → (ℕ → V) → ℝ :=
    fun N X => pathExp G F (X (stopTrunc τ N X)) * HN N X with hBdef
  have hAm : ∀ N, Measurable (A N) := fun N =>
    (measurable_comp_shiftPath_stopping (isStopping_stopTrunc hτ N)
        (stopTrunc_le τ N) hFm).mul (measurable_of_dependsUpTo (hHNdepUpTo N))
  have hBm : ∀ N, Measurable (B N) := fun N =>
    (measurable_comp_apply_stopping (isStopping_stopTrunc hτ N)
        (stopTrunc_le τ N) (measurable_pathExp F)).mul
      (measurable_of_dependsUpTo (hHNdepUpTo N))
  have hAb : ∀ (N : ℕ) (X : ℕ → V), ‖A N X‖ ≤ CF * CH := by
    intro N X
    rw [hAdef]
    simp only [norm_mul]
    exact mul_le_mul (hFb _) (hHNb N X) (norm_nonneg _) hCF
  have hBb : ∀ (N : ℕ) (X : ℕ → V), ‖B N X‖ ≤ CF * CH := by
    intro N X
    rw [hBdef]
    simp only [norm_mul]
    exact mul_le_mul (norm_pathExp_le hFb _) (hHNb N X) (norm_nonneg _) hCF
  have hev : ∀ X : ℕ → V, τ X ≠ ⊤ →
      ∀ᶠ N : ℕ in Filter.atTop, τ X ≤ (N : ℕ∞) := by
    intro X hX
    filter_upwards [Filter.eventually_ge_atTop ((τ X).toNat)] with N hN
    rw [← ENat.coe_toNat_eq_self.mpr hX]
    exact_mod_cast hN
  have hlimA : ∀ᵐ X ∂(walkLaw G x),
      Filter.Tendsto (fun N => A N X) Filter.atTop
        (nhds (F (shiftPath (τ X).toNat X) * H X)) := by
    filter_upwards [hfin] with X hX
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev X hX] with N hN
    show F (shiftPath (τ X).toNat X) * H X = A N X
    rw [hAdef, hHNdef]
    simp only [stopTrunc_of_le hN, hN, if_true, mul_one]
  have hlimB : ∀ᵐ X ∂(walkLaw G x),
      Filter.Tendsto (fun N => B N X) Filter.atTop
        (nhds (pathExp G F (X (τ X).toNat) * H X)) := by
    filter_upwards [hfin] with X hX
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev X hX] with N hN
    show pathExp G F (X (τ X).toNat) * H X = B N X
    rw [hBdef, hHNdef]
    simp only [stopTrunc_of_le hN, hN, if_true, mul_one]
  have hAint := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := walkLaw G x) (F := A)
    (f := fun X => F (shiftPath (τ X).toNat X) * H X)
    (fun _ => CF * CH) (fun N => (hAm N).aestronglyMeasurable)
    (integrable_const _) (fun N => Filter.Eventually.of_forall (hAb N)) hlimA
  have hBint := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := walkLaw G x) (F := B)
    (f := fun X => pathExp G F (X (τ X).toNat) * H X)
    (fun _ => CF * CH) (fun N => (hBm N).aestronglyMeasurable)
    (integrable_const _) (fun N => Filter.Eventually.of_forall (hBb N)) hlimB
  exact tendsto_nhds_unique (hAint.congr fun N => hstop N) hBint

/-! ### Leaving a finite set after the stopping time -/

/-- **After an almost surely finite stopping time the walk still leaves every
finite set almost surely.**  This is `LatticeProb.Graph.ae_exitTime_ne_top`
transported through `LatticeProb.Graph.markov_stopping_ae`: take for `F` the
indicator of `{X | exitTime D X ≠ ⊤}`, which is bounded by one and measurable
because `{exitTime D = ⊤}` is the intersection of the events `stayIn D k`, and
for `H` the constant one.  The strong Markov identity then reads

    ∫ F(θ_τ X) = ∫ (E_{X_τ}[F]) = 1,

the last equality because `E_y[F] = 1` at every start `y`.  An indicator whose
integral is one is one almost everywhere. -/
theorem ae_exitTime_shift_ne_top (hdeg : ∀ v : V, 0 < G.degree v) (x : V)
    (τ : (ℕ → V) → ℕ∞) (hτ : IsWalkStoppingE τ)
    (hfin : ∀ᵐ X ∂(walkLaw G x), τ X ≠ ⊤)
    (D : Finset V) (hescD : ∀ z : V, ∃ (q : V) (_ : G.Walk z q), q ∉ (D : Set V)) :
    ∀ᵐ X ∂(walkLaw G x),
      exitTime (D : Set V) (shiftPath (τ X).toNat X) ≠ ⊤ := by
  classical
  set F : (ℕ → V) → ℝ := fun Y => if exitTime (D : Set V) Y = ⊤ then 0 else 1 with hFdef
  have hset : MeasurableSet {Y : ℕ → V | exitTime (D : Set V) Y = ⊤} := by
    have he : {Y : ℕ → V | exitTime (D : Set V) Y = ⊤} = ⋂ k : ℕ, stayIn (D : Set V) k := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact exitTime_eq_top_iff (D : Set V) Y
    rw [he]
    exact MeasurableSet.iInter fun k => measurableSet_stayIn _ _
  have hFm : Measurable F := by
    rw [hFdef]
    exact Measurable.ite hset measurable_const measurable_const
  have hFb : ∀ Y, ‖F Y‖ ≤ 1 := by
    intro Y
    rw [hFdef]
    by_cases h : exitTime (D : Set V) Y = ⊤ <;> simp [h]
  have hpe : ∀ y : V, pathExp G F y = 1 := by
    intro y
    have hae : ∀ᵐ Y ∂(walkLaw G y), F Y = (1 : ℝ) := by
      filter_upwards [ae_exitTime_ne_top hdeg D hescD y] with Y hY
      simp [hFdef, hY]
    rw [pathExp, integral_congr_ae hae]
    simp
  have hmk := markov_stopping_ae hdeg x τ hτ hfin F hFm 1 hFb
    (fun _ => (1 : ℝ)) 1 (by simp) (fun _ _ _ _ _ => rfl)
  simp only [mul_one, hpe] at hmk
  have hone : ∫ X, F (shiftPath (τ X).toNat X) ∂(walkLaw G x) = 1 := by
    rw [hmk]; simp
  have hgint : Integrable (fun X => F (shiftPath (τ X).toNat X)) (walkLaw G x) := by
    by_contra hc
    rw [integral_undef hc] at hone
    norm_num at hone
  have hnn : (0 : (ℕ → V) → ℝ) ≤ fun X => 1 - F (shiftPath (τ X).toNat X) := by
    intro X
    show (0 : ℝ) ≤ 1 - F (shiftPath (τ X).toNat X)
    rw [hFdef]
    dsimp only
    split <;> norm_num
  have hzero : ∫ X, (1 - F (shiftPath (τ X).toNat X)) ∂(walkLaw G x) = 0 := by
    rw [integral_sub (integrable_const 1) hgint, hone]
    simp
  have hae0 := (integral_eq_zero_iff_of_nonneg hnn
    ((integrable_const (1 : ℝ)).sub hgint)).mp hzero
  filter_upwards [hae0] with X hX
  intro hc
  have hX1 : F (shiftPath (τ X).toNat X) = 1 := by
    have : (1 : ℝ) - F (shiftPath (τ X).toNat X) = 0 := hX
    linarith
  rw [hFdef] at hX1
  simp [hc] at hX1

end LatticeProb.Graph
