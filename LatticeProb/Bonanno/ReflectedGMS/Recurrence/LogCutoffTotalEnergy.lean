/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.LogCutoffTotalEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.LogCutoffEnergy

/-!
# Total energy of the logarithmic cutoff

This file sums the countable annular estimate over the finitely many dyadic
shells on which the clipped logarithmic cutoff can vary.  The argument is made
first for `energyENN`, so no summability of the edge energy is assumed in
advance.
-/

set_option autoImplicit false

open Set Classical
open scoped ENNReal

namespace ReflectedGMS.LogCutoff

variable {V : Type*}

/-- The ordered edges whose smaller clipped radius lies in the `j`-th dyadic
shell. -/
def dyadicShell (r₀ : ℝ) (z : V → Plane) (j : ℕ) : Set (V × V) :=
  {p | (2 : ℝ) ^ j * r₀ ≤ min (radius r₀ z p.1) (radius r₀ z p.2) ∧
    min (radius r₀ z p.1) (radius r₀ z p.2) < 2 * ((2 : ℝ) ^ j * r₀)}

/-- Every number between `r₀` and `2^n r₀` belongs to one of the first `n`
dyadic shells. -/
theorem exists_dyadicShell {r₀ s : ℝ} (hr₀ : 0 < r₀) {n : ℕ}
    (hlower : r₀ ≤ s) (hupper : s < (2 : ℝ) ^ n * r₀) :
    ∃ j < n, (2 : ℝ) ^ j * r₀ ≤ s ∧ s < 2 * ((2 : ℝ) ^ j * r₀) := by
  induction n with
  | zero =>
      simp only [pow_zero, one_mul] at hupper
      exact (not_lt_of_ge hlower hupper).elim
  | succ n ih =>
      by_cases h : s < (2 : ℝ) ^ n * r₀
      · obtain ⟨j, hjn, hjlower, hjupper⟩ := ih h
        exact ⟨j, hjn.trans (Nat.lt_succ_self n), hjlower, hjupper⟩
      · refine ⟨n, Nat.lt_succ_self n, le_of_not_gt h, ?_⟩
        convert hupper using 1 <;> ring

/-- The full extended energy is bounded by the sum of the first `n` shell
energies.  This is the countable-edge partition step and requires no prior
finite-energy hypothesis. -/
theorem energyENN_le_sum_dyadicShells [Countable V]
    (F : IndexedCells V) (z : V → Plane) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {n : ℕ} (hn : 1 ≤ n) :
    energyENN F.graph (cutoff r₀ n z) ≤
      ∑ j ∈ Finset.range n,
        maskedEnergyENN F (cutoff r₀ n z) (dyadicShell r₀ z j) := by
  unfold energyENN maskedEnergyENN
  have hpoint : ∀ p : V × V,
      ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) ≤
        ∑ j ∈ Finset.range n,
          if p ∈ dyadicShell r₀ z j then
            ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) else 0 := by
    intro p
    by_cases hdiff : cutoff r₀ n z p.2 = cutoff r₀ n z p.1
    · simp [ReflectedWalk.ConductanceGraph.gradSq, hdiff]
    · let s := min (radius r₀ z p.1) (radius r₀ z p.2)
      have hlower : r₀ ≤ s := by
        exact le_min (le_max_left _ _) (le_max_left _ _)
      have hupper : s < (2 : ℝ) ^ n * r₀ := by
        by_contra h
        have hs : (2 : ℝ) ^ n * r₀ ≤ s := le_of_not_gt h
        have h₁ : cutoff r₀ n z p.1 = 1 := by
          unfold cutoff
          exact clippedLog_eq_one hr₀ hn (hs.trans (min_le_left _ _))
        have h₂ : cutoff r₀ n z p.2 = 1 := by
          unfold cutoff
          exact clippedLog_eq_one hr₀ hn (hs.trans (min_le_right _ _))
        exact hdiff (h₂.trans h₁.symm)
      obtain ⟨j, hjn, hjlower, hjupper⟩ :=
        exists_dyadicShell hr₀ hlower hupper
      have hp : p ∈ dyadicShell r₀ z j := by
        exact ⟨hjlower, hjupper⟩
      calc
        ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) =
            (if p ∈ dyadicShell r₀ z j then
              ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) else 0) := by
                simp [hp]
        _ ≤ ∑ i ∈ Finset.range n,
              if p ∈ dyadicShell r₀ z i then
                ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) else 0 :=
          Finset.single_le_sum
            (f := fun i => if p ∈ dyadicShell r₀ z i then
              ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) else 0)
            (fun _ _ => zero_le) (Finset.mem_range.mpr hjn)
  calc
    (∑' p : V × V, ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p)) / 2 ≤
        (∑' p : V × V, ∑ j ∈ Finset.range n,
          if p ∈ dyadicShell r₀ z j then
            ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) else 0) / 2 :=
      ENNReal.div_le_div_right (ENNReal.tsum_le_tsum hpoint) 2
    _ = (∑ j ∈ Finset.range n, ∑' p : V × V,
          if p ∈ dyadicShell r₀ z j then
            ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) else 0) / 2 := by
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = ∑ j ∈ Finset.range n,
          (∑' p : V × V, if p ∈ dyadicShell r₀ z j then
            ENNReal.ofReal (F.graph.gradSq (cutoff r₀ n z) p) else 0) / 2 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Under the quadratic local-mass bound, every dyadic shell has the same
extended-energy bound. -/
theorem dyadicShell_energy_le [Countable V]
    (F : IndexedCells V) (hF : Geometry F)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (hD : ∀ R, r₀ ≤ R → ∀ v, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R, r₀ ≤ R →
      localMassENN F {v | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2))
    (j : ℕ) :
    maskedEnergyENN F (cutoff r₀ n z) (dyadicShell r₀ z j) ≤
      ENNReal.ofReal (32 * C / (((n : ℝ) * Real.log 2) ^ 2)) := by
  let L : ℝ := (2 : ℝ) ^ j * r₀
  have hL : 0 < L := mul_pos (pow_pos (by norm_num) j) hr₀
  have hr₀4L : r₀ ≤ 4 * L := by
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    dsimp only [L]
    nlinarith [mul_le_mul_of_nonneg_right hpow hr₀.le]
  calc
    maskedEnergyENN F (cutoff r₀ n z) (dyadicShell r₀ z j) ≤
        ENNReal.ofReal (2 * (1 / (((n : ℝ) * Real.log 2) * L)) ^ 2) *
          localMassENN F {v | Hits F (Metric.closedBall (0 : Plane) (4 * L)) v} := by
      simpa only [dyadicShell, L] using annularEnergy_le F hF z hz hr₀ hn hD hL
    _ ≤ ENNReal.ofReal (2 * (1 / (((n : ℝ) * Real.log 2) * L)) ^ 2) *
          ENNReal.ofReal (C * (4 * L) ^ 2) :=
      mul_le_mul' le_rfl (hW (4 * L) hr₀4L)
    _ = ENNReal.ofReal (32 * C / (((n : ℝ) * Real.log 2) ^ 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity :
        0 ≤ 2 * (1 / (((n : ℝ) * Real.log 2) * L)) ^ 2)]
      congr 1
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hlog0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      have hL0 : L ≠ 0 := ne_of_gt hL
      field_simp
      ring

/-- The full extended energy form of the manuscript's logarithmic cutoff
estimate. -/
theorem cutoff_energyENN_le [Countable V]
    (F : IndexedCells V) (hF : Geometry F)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (hD : ∀ R, r₀ ≤ R → ∀ v, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R, r₀ ≤ R →
      localMassENN F {v | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2)) :
    energyENN F.graph (cutoff r₀ n z) ≤
      ENNReal.ofReal (32 * C / ((n : ℝ) * (Real.log 2) ^ 2)) := by
  calc
    energyENN F.graph (cutoff r₀ n z) ≤
        ∑ j ∈ Finset.range n,
          maskedEnergyENN F (cutoff r₀ n z) (dyadicShell r₀ z j) :=
      energyENN_le_sum_dyadicShells F z hr₀ hn
    _ ≤ ∑ j ∈ Finset.range n,
          ENNReal.ofReal (32 * C / (((n : ℝ) * Real.log 2) ^ 2)) := by
      exact Finset.sum_le_sum fun j _ => dyadicShell_energy_le F hF z hz hr₀ hC hn hD hW j
    _ = ENNReal.ofReal (32 * C / ((n : ℝ) * (Real.log 2) ^ 2)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        have hlog0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
        field_simp
      · intro j hj
        positivity

/-- The logarithmic cutoff has finite ordinary edge energy. -/
theorem cutoff_hasFiniteEnergy [Countable V]
    (F : IndexedCells V) (hF : Geometry F)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (hD : ∀ R, r₀ ≤ R → ∀ v, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R, r₀ ≤ R →
      localMassENN F {v | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2)) :
    F.graph.HasFiniteEnergy (cutoff r₀ n z) := by
  apply (energyENN_ne_top_iff F.graph _).1
  exact ne_of_lt ((cutoff_energyENN_le F hF z hz hr₀ hC hn hD hW).trans_lt
    ENNReal.ofReal_lt_top)

/-- The ordinary real-energy estimate in Proposition `r:prop:log`. -/
theorem cutoff_energy_le [Countable V]
    (F : IndexedCells V) (hF : Geometry F)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (hD : ∀ R, r₀ ≤ R → ∀ v, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R, r₀ ≤ R →
      localMassENN F {v | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2)) :
    F.graph.Energy (cutoff r₀ n z) ≤
      32 * C / ((n : ℝ) * (Real.log 2) ^ 2) := by
  have hfinite := cutoff_hasFiniteEnergy F hF z hz hr₀ hC hn hD hW
  have hbound := cutoff_energyENN_le F hF z hz hr₀ hC hn hD hW
  calc
    F.graph.Energy (cutoff r₀ n z) =
        (energyENN F.graph (cutoff r₀ n z)).toReal :=
      (energyENN_toReal_eq_Energy F.graph hfinite).symm
    _ ≤ (ENNReal.ofReal (32 * C / ((n : ℝ) * (Real.log 2) ^ 2))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = 32 * C / ((n : ℝ) * (Real.log 2) ^ 2) := by
      rw [ENNReal.toReal_ofReal]
      positivity

end ReflectedGMS.LogCutoff
