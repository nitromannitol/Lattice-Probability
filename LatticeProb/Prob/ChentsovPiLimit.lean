/-
Limits and quantitative modulus bounds for summable dyadic increments in finite products.
-/
import LatticeProb.Prob.ChentsovPi

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

/-- Chaining across levels: the `f`-values of the level-`m` and level-`j`
truncations of a point of the box of radius `m` differ by at most the sum of
the level increments. -/
theorem LatticeProb.dtruncPi_dist_le {k : ℕ} {f : (Fin k → ℝ) → ℝ} {a : ℕ → ℝ} {n₀ : ℕ}
    (hb : DyadicIncBoundPi f a n₀) (ha : ∀ n, 0 ≤ a n)
    {m : ℕ} (hm : n₀ ≤ m) {z : Fin k → ℝ} (hz : ∀ i, |z i| ≤ (m : ℝ))
    (j : ℕ) (hj : m < j) :
    |f (dtruncPi m z) - f (dtruncPi j z)| ≤ (k : ℝ) * ∑ n ∈ Finset.Ico (m + 1) (j + 1), a n := by
  rw [abs_sub_comm]
  have hjle := hj.le
  clear hj
  induction j, hjle using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    have hjle : m ≤ j := by omega
    have hzj : ∀ i, |z i| ≤ (j : ℝ) := fun i => (hz i).trans (by exact_mod_cast hjle)
    have hstep := dtruncPi_step hb ha (hm.trans (Nat.le_succ_of_le hjle)) hzj
    calc
      |f (dtruncPi (j + 1) z) - f (dtruncPi m z)|
        ≤ |f (dtruncPi (j + 1) z) - f (dtruncPi j z)| +
          |f (dtruncPi j z) - f (dtruncPi m z)| := abs_sub_le _ _ _
      _ ≤ (k : ℝ) * a (j + 1) + (k : ℝ) * ∑ n ∈ Finset.Ico (m + 1) (j + 1), a n :=
        add_le_add hstep ih
      _ = (k : ℝ) * ∑ n ∈ Finset.Ico (m + 1) (j + 1 + 1), a n := by
        rw [Finset.sum_Ico_succ_top (show m + 1 ≤ j + 1 by omega), mul_add]
        ring



/-- The chained limit. -/
def LatticeProb.dlimPi {k : ℕ} (f : (Fin k → ℝ) → ℝ) (z : Fin k → ℝ) : ℝ :=
  limsup (fun n => f (dtruncPi n z)) atTop

theorem LatticeProb.tendsto_dtruncPi {k : ℕ} {f : (Fin k → ℝ) → ℝ} {a : ℕ → ℝ} {n₀ : ℕ}
    (hb : DyadicIncBoundPi f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    {m : ℕ} (hm : n₀ ≤ m) {z : Fin k → ℝ} (hz : ∀ i, |z i| ≤ (m : ℝ)) :
    Tendsto (fun n => f (dtruncPi n z)) atTop (𝓝 (dlimPi f z)) := by
  have hcauchy : CauchySeq fun n => f (dtruncPi n z) := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
    obtain ⟨M, hM⟩ := (tendsto_dtail a).eventually (gt_mem_nhds
      (show (0 : ℝ) < ε / ((k : ℝ) + 1) from by positivity)) |>.exists_forall_of_atTop
    refine ⟨max m M, fun j hj => ?_⟩
    set m' := max m M with hmdef
    have hmn₀ : n₀ ≤ m' := hm.trans (le_max_left _ _)
    have hzm : ∀ i, |z i| ≤ (m' : ℝ) :=
      fun i => (hz i).trans (by exact_mod_cast Nat.cast_le.mpr (le_max_left _ _))
    have hMm : M ≤ m' := le_max_right _ _
    calc dist (f (dtruncPi j z)) (f (dtruncPi m' z))
        = |f (dtruncPi j z) - f (dtruncPi m' z)| := Real.dist_eq _ _
      _ ≤ (k : ℝ) * ∑ n ∈ Finset.Ico (m' + 1) (j + 1), a n := by
          by_cases hlt : m' < j
          · rw [abs_sub_comm]
            exact dtruncPi_dist_le hb ha hmn₀ hzm j hlt
          · have hjm : j = m' := Nat.le_antisymm (Nat.le_of_not_gt hlt) hj
            subst hjm
            rw [sub_self, abs_zero]
            exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => ha n)
      _ ≤ (k : ℝ) * dtail a m' :=
          mul_le_mul_of_nonneg_left (sum_Ico_le_dtail hsum ha m' j) (by positivity)
      _ < ε := by
          have := hM m' hMm
          rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)] at this
          have h0 : (0 : ℝ) ≤ dtail a m' := dtail_nonneg ha m'
          have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
          nlinarith [this, h0, hk]
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  rwa [dlimPi, hc.limsup_eq]

theorem LatticeProb.dlimPi_sub_dtruncPi_le {k : ℕ} {f : (Fin k → ℝ) → ℝ} {a : ℕ → ℝ} {n₀ : ℕ}
    (hb : DyadicIncBoundPi f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    {m : ℕ} (hm : n₀ ≤ m) {z : Fin k → ℝ} (hz : ∀ i, |z i| ≤ (m : ℝ)) :
    |dlimPi f z - f (dtruncPi m z)| ≤ (k : ℝ) * dtail a m := by
  refine le_of_tendsto ((tendsto_dtruncPi hb ha hsum hm hz).sub_const _).abs ?_
  filter_upwards [eventually_ge_atTop m] with j hj
  by_cases h : m < j
  · rw [abs_sub_comm]
    exact (dtruncPi_dist_le hb ha hm hz j h).trans
      (mul_le_mul_of_nonneg_left (sum_Ico_le_dtail hsum ha m j) (by positivity))
  · have hjm : j = m := Nat.le_antisymm (Nat.le_of_not_gt h) hj
    subst hjm
    rw [sub_self, abs_zero]
    exact mul_nonneg (by positivity) (dtail_nonneg ha _)

/-- Modulus of continuity of the chained limit on the box of radius `m`. -/
theorem LatticeProb.dlimPi_dist_le {k : ℕ} {f : (Fin k → ℝ) → ℝ} {a : ℕ → ℝ} {n₀ : ℕ}
    (hb : DyadicIncBoundPi f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    {m : ℕ} (hm : n₀ ≤ m) {s t : Fin k → ℝ}
    (hs : ∀ i, |s i| ≤ (m : ℝ)) (ht : ∀ i, |t i| ≤ (m : ℝ))
    (hst : ∀ i, |t i - s i| ≤ 1 / 2 ^ m) :
    |dlimPi f t - dlimPi f s| ≤ 2 * ((k : ℝ) * dtail a m) + (k : ℝ) * a m := by
  have ht' := dlimPi_sub_dtruncPi_le hb ha hsum hm ht
  have hs' := dlimPi_sub_dtruncPi_le hb ha hsum hm hs
  have hclose := dtruncPi_close hb ha hm hs ht hst
  have htri := abs_sub_le (dlimPi f t) (f (dtruncPi m t)) (dlimPi f s)
  have htri' := abs_sub_le (f (dtruncPi m t)) (f (dtruncPi m s)) (dlimPi f s)
  rw [abs_sub_comm (f (dtruncPi m s)) (dlimPi f s)] at htri'
  linarith


end
