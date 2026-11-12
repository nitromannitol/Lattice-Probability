import Mathlib
import LatticeProb.LQG.LengthMetricDerived

/-!
# The length of a curve up to its endpoint

Let `D` be a Euclidean length metric on `ℂ` and `p` a curve, continuous on `[0, 1]` for the Euclidean topology.
If `aₙ ∈ [0, 1]` tends to `1`, then the `D`-length of `p` on `[0, 1]` is the supremum of the `D`-lengths on `[0, aₙ]`.
The partition points below `1` lie in some `[0, aₙ]`, and the last step to `p 1` costs at most `D (p aₙ, p 1)`, which
tends to `0` because the `D`-balls are Euclidean open.

## Main statements

* `LatticeProb.LQG.IsEuclideanLengthMetric.curveLength_le_iSup_of_tendsto_of_mem_Icc`
-/

open Set Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.LQG

/-- Sending the value `1` of a monotone sequence `u ≤ 1` to `b` changes the partition sum of a curve by at most
the closing step `D (p b, p 1)`, paid once: this is a comparison of the sums over `range N`, with
`v i = b` where `u i = 1` and `v i = u i` elsewhere, for `i ≤ N`. -/
lemma sum_range_le_sum_replace_one {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (p : ℝ → ℂ)
    {u v : ℕ → ℝ} (hu : Monotone u) (hu1 : ∀ i, u i ≤ 1) (b : ℝ) (N : ℕ)
    (hv : ∀ i ≤ N, v i = if u i = 1 then b else u i) :
    ∑ i ∈ Finset.range N, ENNReal.ofReal (D (p (u (i + 1))) (p (u i))) ≤
      ∑ i ∈ Finset.range N, ENNReal.ofReal (D (p (v (i + 1))) (p (v i))) +
        if u N = 1 then ENNReal.ofReal (D (p b) (p 1)) else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih fun i hi => hv i (hi.trans N.le_succ)
    have hvN := hv N N.le_succ
    have hvN1 := hv (N + 1) le_rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    by_cases h1 : u (N + 1) = 1
    · by_cases h0 : u N = 1
      · simp only [h0, ↓reduceIte] at ih'
        simp [hvN, hvN1, h0, h1, hD.self_eq_zero, ih']
      · simp only [h0, ↓reduceIte, add_zero] at ih'
        have hvN' : v N = u N := by simp [hvN, h0]
        have hvN1' : v (N + 1) = b := by simp [hvN1, h1]
        rw [hvN', hvN1']
        simp only [h1, ↓reduceIte]
        have htri : ENNReal.ofReal (D (p 1) (p (u N))) ≤
            ENNReal.ofReal (D (p b) (p (u N))) + ENNReal.ofReal (D (p b) (p 1)) := by
          refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
          have := hD.triangle (p 1) (p b) (p (u N))
          rw [hD.symm (p 1) (p b)] at this
          linarith
        calc _ ≤ (∑ i ∈ Finset.range N, ENNReal.ofReal (D (p (v (i + 1))) (p (v i)))) +
              (ENNReal.ofReal (D (p b) (p (u N))) + ENNReal.ofReal (D (p b) (p 1))) :=
              add_le_add ih' htri
          _ = _ := by rw [add_assoc]
    · have h0 : u N ≠ 1 := fun h0 =>
        h1 (le_antisymm (hu1 _) (h0 ▸ hu N.le_succ))
      have hvN' : v N = u N := by simp [hvN, h0]
      have hvN1' : v (N + 1) = u (N + 1) := by simp [hvN1, h1]
      simp only [h0, h1, ↓reduceIte, add_zero] at ih' ⊢
      rw [hvN', hvN1']
      exact add_le_add ih' le_rfl

/-- **The length of a curve up to its endpoint.** Let `D` be a Euclidean length metric, `p` continuous on `[0, 1]`,
and `aₙ ∈ [0, 1]` with `aₙ → 1`. Then `len(p; D)` on `[0, 1]` is at most `sup_n len(p|[0, aₙ]; D)`. -/
theorem IsEuclideanLengthMetric.curveLength_le_iSup_of_tendsto_of_mem_Icc {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) {a : ℕ → ℝ}
    (ha : ∀ n, a n ∈ Icc (0 : ℝ) 1) (hlim : Tendsto a atTop (𝓝 1)) :
    curveLength D p 0 1 ≤ ⨆ n, curveLength D p 0 (a n) := by
  have hpa : Tendsto (fun n => p (a n)) atTop (𝓝 (p 1)) :=
    (hp 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall ha⟩)
  have hball : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, D (p 1) (p (a n)) < ε := by
    intro ε hε
    have hopen : IsOpen {w : ℂ | D (p 1) w < ε} := by
      rw [hD.isOpen_iff]
      intro z hz
      have hz' : D (p 1) z < ε := hz
      refine ⟨ε - D (p 1) z, by linarith, fun w hw => ?_⟩
      have := hD.triangle (p 1) z w
      show D (p 1) w < ε
      linarith
    exact hpa.eventually (hopen.mem_nhds (by
      show D (p 1) (p 1) < ε
      rw [hD.self_eq_zero]
      exact hε))
  refine curveLength_le_of_partition_bound fun N u hu hI => ?_
  have hu1 : ∀ i, u i ≤ 1 := fun i => (hI i).2
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (N + 1), u i < 1 → u i ≤ a n := by
    rw [Filter.eventually_all_finset]
    intro i _
    by_cases hi : u i < 1
    · filter_upwards [hlim.eventually (Ioi_mem_nhds hi)] with n hn _ using le_of_lt hn
    · exact Eventually.of_forall fun n h => absurd h hi
  obtain ⟨n, hn1, hn2⟩ := (hev.and (hball η (NNReal.coe_pos.2 hη))).exists
  set v : ℕ → ℝ := fun i => if i ≤ N ∧ u i < 1 then u i else a n with hvdef
  have hle : ∀ i, u i < 1 → i ≤ N → u i ≤ a n := fun i hi hiN =>
    hn1 i (Finset.mem_range.2 (Nat.lt_succ_of_le hiN)) hi
  have hvle : ∀ i, v i ≤ a n := fun i => by
    by_cases h : i ≤ N ∧ u i < 1
    · simp only [hvdef, h, and_self, ↓reduceIte]
      exact hle i h.2 h.1
    · simp [hvdef, h]
  have hvnn : ∀ i, 0 ≤ v i := fun i => by
    by_cases h : i ≤ N ∧ u i < 1
    · simp only [hvdef, h, and_self, ↓reduceIte]
      exact (hI i).1
    · simp only [hvdef, h, ↓reduceIte]
      exact (ha n).1
  have hvmono : Monotone v := by
    intro i j hij
    by_cases hj : j ≤ N ∧ u j < 1
    · have hi : i ≤ N ∧ u i < 1 := ⟨hij.trans hj.1, lt_of_le_of_lt (hu hij) hj.2⟩
      simp only [hvdef, hi, hj, and_self, ↓reduceIte]
      exact hu hij
    · have : v j = a n := by simp [hvdef, hj]
      rw [this]
      exact hvle i
  have hv : ∀ i ≤ N, v i = if u i = 1 then a n else u i := fun i hiN => by
    by_cases h : u i = 1
    · simp [hvdef, h]
    · have : i ≤ N ∧ u i < 1 := ⟨hiN, lt_of_le_of_ne (hu1 i) h⟩
      simp [hvdef, this, h]
  have hsum := sum_range_le_sum_replace_one hD p hu hu1 (a n) N hv
  have hv_le : ∑ i ∈ Finset.range N, ENNReal.ofReal (D (p (v (i + 1))) (p (v i))) ≤
      curveLength D p 0 (a n) := by
    unfold curveLength
    exact le_iSup (fun q : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 (a n) } =>
      ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p (q.2.1 (i + 1))) (p (q.2.1 i))))
      (N, ⟨v, hvmono, fun i => ⟨hvnn i, hvle i⟩⟩)
  have hlast : (if u N = 1 then ENNReal.ofReal (D (p (a n)) (p 1)) else 0) ≤ (η : ℝ≥0∞) := by
    split_ifs
    · rw [hD.symm (p (a n)) (p 1), ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hn2.le
    · exact zero_le
  calc _ ≤ _ := hsum
    _ ≤ curveLength D p 0 (a n) + (η : ℝ≥0∞) := add_le_add hv_le hlast
    _ ≤ (⨆ n, curveLength D p 0 (a n)) + (η : ℝ≥0∞) :=
        add_le_add (le_iSup (fun n => curveLength D p 0 (a n)) n) le_rfl

end LatticeProb.LQG
