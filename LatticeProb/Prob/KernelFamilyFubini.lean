import LatticeProb.Prob.UniformLimitAfterPositiveTimes

/-!
# Fubini for a kernel family, and countable reductions of path events

Three general tools for passing from statements about a process started at a fixed point to
statements holding almost surely for almost every starting point.

* `LatticeProb.ae_ae_ae_of_ae_prod_kernel`: if, for `ν`-almost every `y`, a measurable set `S` has
  full measure for the product `μ ⊗ κ y`, then for `μ`-almost every `x`, for `ν`-almost every `y`
  and `κ y`-almost every `z`, the pair `(x, z)` lies in `S`.
* `LatticeProb.measurableSet_uniformCauchySeqOn_of_continuous`: for functions of time that are
  continuous in time and measurable in the sample at every time, the event that the sequence is
  uniformly Cauchy on a set of times is measurable.
* `LatticeProb.strictMono_of_monotone_of_rat`: a nondecreasing function on `ℝ≥0` that is strictly
  increasing along rational times is strictly increasing.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace LatticeProb

/-- **Fubini for a kernel family.** If, for `ν`-almost every `y`, the measurable set `S` has full
measure for the product `μ ⊗ κ y`, then for `μ`-almost every `x`, for `ν`-almost every `y` and
`κ y`-almost every `z`, the pair `(x, z)` lies in `S`. -/
theorem ae_ae_ae_of_ae_prod_kernel {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] {S : Set (X × Z)} (hS : MeasurableSet S)
    (h : ∀ᵐ y ∂ν, ∀ᵐ p ∂(μ.prod (κ y)), p ∈ S) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ∀ᵐ z ∂(κ y), (x, z) ∈ S := by
  have h1 : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, ∀ᵐ z ∂(κ y), (x, z) ∈ S :=
    h.mono fun y hy => Measure.ae_ae_of_ae_prod hy
  have hT : MeasurableSet {q : (Y × X) × Z | (q.1.2, q.2) ∉ S} :=
    (hS.preimage ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).compl
  let κ' : Kernel (Y × X) Z := κ.comap (Prod.fst : Y × X → Y) measurable_fst
  have hf : Measurable fun q : Y × X => κ' q
      (Prod.mk q ⁻¹' {q : (Y × X) × Z | (q.1.2, q.2) ∉ S}) :=
    Kernel.measurable_kernel_prodMk_left hT
  have hmeas : MeasurableSet {q : Y × X | ∀ᵐ z ∂(κ q.1), (q.2, z) ∈ S} := by
    have hEq : {q : Y × X | ∀ᵐ z ∂(κ q.1), (q.2, z) ∈ S} =
        (fun q : Y × X => κ' q
          (Prod.mk q ⁻¹' {q : (Y × X) × Z | (q.1.2, q.2) ∉ S})) ⁻¹' {0} := by
      ext q
      show (∀ᵐ z ∂(κ q.1), (q.2, z) ∈ S) ↔ κ' q {z | (q.2, z) ∉ S} = 0
      rw [Kernel.comap_apply, ae_iff]
    rw [hEq]
    exact hf (measurableSet_singleton 0)
  exact (Measure.ae_ae_comm hmeas).1 h1

/-- **Measurability of a uniform-Cauchy event.** For a family of functions `g ω k : ℝ≥0 → ℝ` that
are continuous in time and measurable in `ω` at every time, the event that `(g ω k)_k` is uniformly
Cauchy on a set of times `s` is measurable (continuity reduces it to countably many times). -/
theorem measurableSet_uniformCauchySeqOn_of_continuous {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → ℕ → ℝ≥0 → ℝ) (hg : ∀ ω k, Continuous (g ω k))
    (hm : ∀ k t, Measurable fun ω => g ω k t) (s : Set ℝ≥0) :
    MeasurableSet {ω | UniformCauchySeqOn (g ω) atTop s} := by
  have hEq : {ω | UniformCauchySeqOn (g ω) atTop s} =
      ⋂ j : ℕ, ⋃ N : ℕ, ⋂ m ≥ N, ⋂ n ≥ N,
        {ω | ∃ t ∈ s, ((j : ℝ) + 1)⁻¹ < |g ω m t - g ω n t|}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, Metric.uniformCauchySeqOn_iff, mem_iInter, mem_iUnion,
      mem_compl_iff, not_exists, not_and, not_lt, Real.dist_eq]
    constructor
    · intro h j
      obtain ⟨N, hN⟩ := h _ (by positivity : (0 : ℝ) < ((j : ℝ) + 1)⁻¹)
      exact ⟨N, fun m hm n hn t ht => (hN m hm n hn t ht).le⟩
    · intro h ε hε
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h j
      refine ⟨N, fun m hm n hn t ht => ?_⟩
      have h1 := hN m hm n hn t ht
      rw [one_div] at hj
      exact h1.trans_lt hj
  rw [hEq]
  refine MeasurableSet.iInter fun j => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        (measurableSet_exists_mem_lt_of_continuous
          (fun ω t => |g ω m t - g ω n t|) (fun ω => ((hg ω m).sub (hg ω n)).abs)
          (fun t => ((hm m t).sub (hm n t)).abs) s _).compl

/-- **Strict monotonicity from rational times.** A nondecreasing function on `ℝ≥0` that is strictly
increasing along all pairs of times of the form `q.toNNReal` with `q` rational is strictly
increasing. -/
theorem strictMono_of_monotone_of_rat {L : ℝ≥0 → ℝ} (hL : Monotone L)
    (hq : ∀ q₁ q₂ : ℚ, Real.toNNReal q₁ < Real.toNNReal q₂ →
      L (Real.toNNReal q₁) < L (Real.toNNReal q₂)) : StrictMono L := by
  intro s t hst
  have hst' : (s : ℝ) < t := hst
  obtain ⟨q₁, hsq₁, hq₁t⟩ := exists_rat_btwn hst'
  obtain ⟨q₂, hq₁q₂, hq₂t⟩ := exists_rat_btwn hq₁t
  have hq₁0 : (0 : ℝ) < q₁ := lt_of_le_of_lt s.2 hsq₁
  have h1 : s ≤ Real.toNNReal q₁ := (Real.lt_toNNReal_iff_coe_lt.2 hsq₁).le
  have h2 : Real.toNNReal q₂ ≤ t := Real.toNNReal_le_iff_le_coe.2 hq₂t.le
  have h12 : Real.toNNReal q₁ < Real.toNNReal q₂ :=
    (Real.toNNReal_lt_toNNReal_iff (hq₁0.trans hq₁q₂)).2 hq₁q₂
  exact (hL h1).trans_lt ((hq q₁ q₂ h12).trans_le (hL h2))

end LatticeProb
