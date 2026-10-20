/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/SkorokhodSpace.lean.
-/
import LatticeProb.Prob.SkorokhodPartition
import LatticeProb.Prob.SkorokhodMix

/-!
# Skorokhod representation, step 3: the data of Billingsley's construction

Given `P_n ⇒ P` on a separable pseudo-metric space, choose for `ε_m = 2^{-(m+1)}` the
partitions `B^m` of `exists_skorokhodPartition` and an increasing sequence `n_m` (`φ m`) such
that `P_n (B^m_i) ≥ (1 - ε_m) P (B^m_i)` for all `n ≥ n_m` and all `i` (Billingsley (6.9),
by the portmanteau theorem since the `B^m_i` are `P`-continuity sets).

Source: Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), proof of
Theorem 6.7, p. 70–71, (6.8)–(6.9). We only require `n ≥ n_m` (not `n_m ≤ n < n_{m+1}`), and
the regime of `n` is the largest `m ≤ n` with `n_m ≤ n` (`SkData.reg`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped ENNReal

namespace LatticeProb.Skorokhod

/-- Billingsley's `ε_m = 2^{-m}`, shifted so that the level of index `m` is `2^{-(m+1)}`. -/
noncomputable def skEps (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ (m + 1)

/-- The levels `skEps m` are positive. -/
lemma skEps_pos (m : ℕ) : 0 < skEps m := by unfold skEps; positivity

/-- The levels `skEps m` are at most `1 / 2`. -/
lemma skEps_le_half (m : ℕ) : skEps m ≤ 1 / 2 := by
  unfold skEps
  calc (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 2 := pow_one _

/-- The levels `skEps m` tend to `0`. -/
lemma tendsto_skEps : Tendsto skEps atTop (𝓝 0) := by
  unfold skEps
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
    (tendsto_add_atTop_nat 1)

variable {S : Type*} [MeasurableSpace S] [PseudoMetricSpace S]

/-- The data of Billingsley's construction for a sequence of measures `Ps n` approximating
`P`: an increasing index sequence `φ`, and for each level `m` a partition `B m` of `S` into the
cells `B m 0, …, B m (k m)` such that the cell `B m 0` has `P`-mass at most `skEps m`, every other
cell has diameter `< skEps m`, and `Ps n (B m i) ≥ (1 - skEps m) P (B m i)` for all `n ≥ φ m`
and all `i`. -/
structure SkData (P : Measure S) (Ps : ℕ → Measure S) where
  φ : ℕ → ℕ
  φ_mono : StrictMono φ
  k : ℕ → ℕ
  B : ℕ → ℕ → Set S
  part : ∀ m, IsSkPartition (B m) (k m)
  small : ∀ m, P (B m 0) ≤ ENNReal.ofReal (skEps m)
  diam : ∀ m i, i ≠ 0 → ∀ x ∈ B m i, ∀ y ∈ B m i, dist x y < skEps m
  lower : ∀ m n, φ m ≤ n → ∀ i, ENNReal.ofReal (1 - skEps m) * P (B m i) ≤ Ps n (B m i)

/-- **Billingsley (6.8)–(6.9).** The data exist when `μs n → μ` weakly. -/
theorem exists_skData [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    {μ : ProbabilityMeasure S} {μs : ℕ → ProbabilityMeasure S} (h : Tendsto μs atTop (𝓝 μ)) :
    Nonempty (SkData (μ : Measure S) fun n => (μs n : Measure S)) := by
  have hpart := fun m => exists_skorokhodPartition (μ : Measure S) (skEps_pos m)
  choose k B hmeas hdisj hcov hemp hfr hsmall hdiam using hpart
  have hev : ∀ m, ∀ᶠ n in atTop, ∀ i,
      ENNReal.ofReal (1 - skEps m) * (μ : Measure S) (B m i) ≤ (μs n : Measure S) (B m i) := by
    intro m
    have hfin : ∀ i ∈ Finset.range (k m + 1), ∀ᶠ n in atTop,
        ENNReal.ofReal (1 - skEps m) * (μ : Measure S) (B m i) ≤ (μs n : Measure S) (B m i) := by
      intro i _
      by_cases h0 : (μ : Measure S) (B m i) = 0
      · exact Eventually.of_forall fun n => by simp [h0]
      · have hc : ENNReal.ofReal (1 - skEps m) < 1 := by
          rw [ENNReal.ofReal_lt_one]; linarith [skEps_pos m]
        have hlt : ENNReal.ofReal (1 - skEps m) * (μ : Measure S) (B m i) <
            (μ : Measure S) (B m i) := by
          simpa using (ENNReal.mul_lt_mul_iff_left h0 (measure_ne_top _ _)).2 hc
        exact ((ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h
          (hfr m i)).eventually (lt_mem_nhds hlt)).mono fun n hn => hn.le
    filter_upwards [(Filter.eventually_all_finset (Finset.range (k m + 1))).2 hfin] with n hn i
    by_cases hi : i ≤ k m
    · exact hn i (Finset.mem_range.2 (by omega))
    · rw [hemp m i (by omega)]; simp
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_eventually'
    (P := fun m n₀ => ∀ n ≥ n₀, ∀ i,
      ENNReal.ofReal (1 - skEps m) * (μ : Measure S) (B m i) ≤ (μs n : Measure S) (B m i))
    fun m => by
      obtain ⟨a, ha⟩ := eventually_atTop.1 (hev m)
      exact ⟨a, fun n₀ hn₀ n hn => ha n (hn₀.trans hn)⟩
  exact ⟨{ φ := φ, φ_mono := hφ, k := k, B := B
           part := fun m => ⟨hmeas m, hdisj m, hcov m, hemp m⟩
           small := fun m => (hsmall m).le
           diam := hdiam
           lower := fun m n hn => hφP m n hn }⟩

variable {P : Measure S} {Ps : ℕ → Measure S} (D : SkData P Ps)

namespace SkData

/-- The regime of `n`: the largest `m ≤ n` with `φ m ≤ n`. -/
def reg (n : ℕ) : ℕ := Nat.findGreatest (fun m => D.φ m ≤ n) n

/-- If `φ 0 ≤ n`, the regime `reg n` satisfies `φ (reg n) ≤ n`. -/
lemma reg_spec {n : ℕ} (hn : D.φ 0 ≤ n) : D.φ (D.reg n) ≤ n :=
  Nat.findGreatest_spec (P := fun m => D.φ m ≤ n) (Nat.zero_le n) hn

/-- If `φ M ≤ n`, then `M ≤ reg n`. -/
lemma le_reg {M n : ℕ} (h : D.φ M ≤ n) : M ≤ D.reg n :=
  Nat.le_findGreatest ((D.φ_mono.id_le M).trans h) h

/-- The regime tends to infinity. -/
lemma tendsto_reg : Tendsto D.reg atTop atTop :=
  tendsto_atTop.2 fun M => eventually_atTop.2 ⟨D.φ M, fun _ hn => D.le_reg hn⟩

/-- The index of the cell of `B m` containing `x`: the least such index. -/
noncomputable def idx (m : ℕ) (x : S) : ℕ := by
  classical exact Nat.find ((D.part m).exists_mem x)

/-- A point lies in the cell of `B m` with index `idx m x`. -/
lemma mem_idx (m : ℕ) (x : S) : x ∈ D.B m (D.idx m x) := by
  classical
  have := Nat.find_spec ((D.part m).exists_mem x)
  unfold idx; convert this.2

/-- If `x` lies in the cell `B m i`, then `i` is the index of `x`. -/
lemma idx_eq {m i : ℕ} {x : S} (hx : x ∈ D.B m i) : D.idx m x = i := by
  by_contra hne
  exact Set.disjoint_left.1 ((D.part m).disj hne) (D.mem_idx m x) hx

end SkData

namespace SkorokhodSpaceExample

example (μ : ProbabilityMeasure ℝ) :
    Nonempty (SkData (μ : Measure ℝ) fun _ => (μ : Measure ℝ)) :=
  exists_skData tendsto_const_nhds

end SkorokhodSpaceExample

end LatticeProb.Skorokhod
