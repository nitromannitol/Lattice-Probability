import Mathlib
import LatticeProb.Prob.LevelPassageMarkov

/-!
# First-hit decomposition of small values along an arithmetic grid of levels

Let `Y : ℝ → Ω → ℝ` be a process indexed by levels and let `a_k = α + k h` (`α, h ≥ 0`) be an
arithmetic grid of levels. Suppose that, at fixed levels `0 ≤ aᵢ ≤ b ≤ c`, the increment
`Y c - Y b` is independent of the values `Y (aᵢ)` and has the law of `Y (c - b)` (in the form of a
product formula for the measures of events). Decomposing the event that `|Y|` is at most `r` at
some grid level `a_k`, `k ≤ K`, according to the first such level (the first-hit events `E_k`,
which are pairwise disjoint), one obtains

  `ν {∃ k ≤ K, |Y a_k| ≤ r} * ∑_{i=1}^{M} ν {|Y (i h)| ≤ r} ≤ ∑_{j=0}^{K+M} ν {|Y a_j| ≤ 2 r}`.

* `measure_exists_abs_le_mul_sum_le`: the abstract first-hit inequality.
* `measure_exists_abs_cauchyLevel_le_mul_sum_le`: the first-hit inequality for the level process
  `cauchyLevel` of two independent pairs of independent Brownian paths, using the independent and
  stationary increments `lintegral_cauchyLevel_mul_sub`.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

section FirstHit

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {Y : ℝ → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The first-hit events at distinct grid indices are disjoint. -/
theorem disjoint_firstHit {α h r : ℝ} {k k' : ℕ} (hne : k ≠ k') :
    Disjoint ({q | |Y (α + k * h) q| ≤ r} ∩ ⋂ l : Fin k, {q | r < |Y (α + ((l : ℕ) : ℝ) * h) q|})
      ({q | |Y (α + k' * h) q| ≤ r} ∩ ⋂ l : Fin k', {q | r < |Y (α + ((l : ℕ) : ℝ) * h) q|}) := by
  rcases lt_trichotomy k k' with hlt | heq | hlt
  · refine Set.disjoint_left.2 fun q hq hq' => ?_
    have h1 : |Y (α + k * h) q| ≤ r := hq.1
    have h2 : r < |Y (α + k * h) q| := Set.mem_iInter.1 hq'.2 ⟨k, hlt⟩
    exact absurd h1 (not_le.2 h2)
  · exact absurd heq hne
  · refine Set.disjoint_left.2 fun q hq hq' => ?_
    have h1 : |Y (α + k' * h) q| ≤ r := hq'.1
    have h2 : r < |Y (α + k' * h) q| := Set.mem_iInter.1 hq.2 ⟨k', hlt⟩
    exact absurd h1 (not_le.2 h2)

/-- The first-hit events are measurable. -/
theorem measurableSet_firstHit (hY : ∀ t, Measurable (Y t)) (α h r : ℝ) (k : ℕ) :
    MeasurableSet
      ({q | |Y (α + k * h) q| ≤ r} ∩ ⋂ l : Fin k, {q | r < |Y (α + ((l : ℕ) : ℝ) * h) q|}) :=
  (measurableSet_le (continuous_abs.measurable.comp (hY _)) measurable_const).inter
    (MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hY _)))

omit [MeasurableSpace Ω] in
/-- The event that `|Y|` is at most `r` at some grid level `a_k`, `k ≤ K`, is covered by the
first-hit events `E_k`, `k ≤ K`. -/
theorem subset_biUnion_firstHit (α h r : ℝ) (K : ℕ) :
    {q | ∃ k ≤ K, |Y (α + k * h) q| ≤ r} ⊆
      ⋃ k ∈ Finset.range (K + 1),
        ({q | |Y (α + k * h) q| ≤ r} ∩ ⋂ l : Fin k, {q | r < |Y (α + ((l : ℕ) : ℝ) * h) q|}) := by
  classical
  rintro q ⟨k, hk, hq⟩
  have hex : ∃ k : ℕ, |Y (α + k * h) q| ≤ r := ⟨k, hq⟩
  refine Set.mem_iUnion₂.2 ⟨Nat.find hex, Finset.mem_range.2 ?_, Nat.find_spec hex,
    Set.mem_iInter.2 fun l => not_le.1 (Nat.find_min hex l.isLt)⟩
  exact Nat.lt_add_one_iff.2 ((Nat.find_min' hex hq).trans hk)

/-- **One first-hit term.** If the increments of `Y` after a level are independent of the values
of `Y` at the earlier levels and stationary, then `ν (E_k) ν {|Y (i h)| ≤ r}` is at most the
measure of `E_k ∩ {|Y a_{k+i}| ≤ 2 r}`. -/
theorem measure_firstHit_mul_le
    (hind : ∀ (n : ℕ) (a : Fin n → ℝ) (b c : ℝ), (∀ i, 0 ≤ a i) → (∀ i, a i ≤ b) → 0 ≤ b →
      b ≤ c → ∀ S : Set (Fin n → ℝ), MeasurableSet S → ∀ T : Set ℝ, MeasurableSet T →
        ν {q | (fun i => Y (a i) q) ∈ S ∧ Y c q - Y b q ∈ T} =
          ν {q | (fun i => Y (a i) q) ∈ S} * ν {q | Y (c - b) q ∈ T})
    {α h : ℝ} (hα : 0 ≤ α) (hh : 0 ≤ h) (r : ℝ) (k i : ℕ) :
    ν ({q | |Y (α + k * h) q| ≤ r} ∩ ⋂ l : Fin k, {q | r < |Y (α + ((l : ℕ) : ℝ) * h) q|}) *
        ν {q | |Y (i * h) q| ≤ r} ≤
      ν (({q | |Y (α + k * h) q| ≤ r} ∩ ⋂ l : Fin k, {q | r < |Y (α + ((l : ℕ) : ℝ) * h) q|}) ∩
        {q | |Y (α + ((k + i : ℕ) : ℝ) * h) q| ≤ 2 * r}) := by
  have hS : MeasurableSet ({x : Fin (k + 1) → ℝ | |x (Fin.last k)| ≤ r} ∩
      ⋂ l : Fin k, {x | r < |x (Fin.castSucc l)|}) :=
    (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply _))
      measurable_const).inter
      (MeasurableSet.iInter fun _ =>
        measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_pi_apply _)))
  have hT : MeasurableSet {u : ℝ | |u| ≤ r} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have h1 : ∀ l : Fin (k + 1), 0 ≤ α + ((l : ℕ) : ℝ) * h := fun l =>
    add_nonneg hα (mul_nonneg (Nat.cast_nonneg _) hh)
  have h2 : ∀ l : Fin (k + 1), α + ((l : ℕ) : ℝ) * h ≤ α + (k : ℝ) * h := fun l => by
    have hl : ((l : ℕ) : ℝ) ≤ k := Nat.cast_le.2 (Nat.lt_add_one_iff.1 l.isLt)
    linarith [mul_le_mul_of_nonneg_right hl hh]
  have h3 : 0 ≤ α + (k : ℝ) * h := add_nonneg hα (mul_nonneg (Nat.cast_nonneg _) hh)
  have h4 : α + (k : ℝ) * h ≤ α + ((k + i : ℕ) : ℝ) * h := by
    have hk : (k : ℝ) ≤ ((k + i : ℕ) : ℝ) := Nat.cast_le.2 (Nat.le_add_right k i)
    linarith [mul_le_mul_of_nonneg_right hk hh]
  have key : ν {q | (fun l : Fin (k + 1) => Y (α + ((l : ℕ) : ℝ) * h) q) ∈
        ({x : Fin (k + 1) → ℝ | |x (Fin.last k)| ≤ r} ∩
          ⋂ l : Fin k, {x | r < |x (Fin.castSucc l)|}) ∧
        Y (α + ((k + i : ℕ) : ℝ) * h) q - Y (α + (k : ℝ) * h) q ∈ {u : ℝ | |u| ≤ r}} =
      ν {q | (fun l : Fin (k + 1) => Y (α + ((l : ℕ) : ℝ) * h) q) ∈
        ({x : Fin (k + 1) → ℝ | |x (Fin.last k)| ≤ r} ∩
          ⋂ l : Fin k, {x | r < |x (Fin.castSucc l)|})} *
      ν {q | Y ((α + ((k + i : ℕ) : ℝ) * h) - (α + (k : ℝ) * h)) q ∈ {u : ℝ | |u| ≤ r}} :=
    hind (k + 1) (fun l => α + ((l : ℕ) : ℝ) * h) (α + (k : ℝ) * h)
      (α + ((k + i : ℕ) : ℝ) * h) h1 h2 h3 h4 _ hS _ hT
  have hcb : (α + ((k + i : ℕ) : ℝ) * h) - (α + (k : ℝ) * h) = (i : ℝ) * h := by
    push_cast; ring
  have hE : {q | (fun l : Fin (k + 1) => Y (α + ((l : ℕ) : ℝ) * h) q) ∈
        ({x : Fin (k + 1) → ℝ | |x (Fin.last k)| ≤ r} ∩
          ⋂ l : Fin k, {x | r < |x (Fin.castSucc l)|})} =
      {q | |Y (α + k * h) q| ≤ r} ∩ ⋂ l : Fin k, {q | r < |Y (α + ((l : ℕ) : ℝ) * h) q|} :=
    Set.ext fun q => ⟨fun hq => ⟨hq.1, Set.mem_iInter.2 fun l => Set.mem_iInter.1 hq.2 l⟩,
      fun hq => ⟨hq.1, Set.mem_iInter.2 fun l => Set.mem_iInter.1 hq.2 l⟩⟩
  rw [hcb, hE] at key
  refine key.symm.trans_le (measure_mono fun q hq => ⟨(Set.ext_iff.1 hE q).1 hq.1, ?_⟩)
  have hqk : |Y (α + (k : ℝ) * h) q| ≤ r := ((Set.ext_iff.1 hE q).1 hq.1).1
  have hqi : |Y (α + ((k + i : ℕ) : ℝ) * h) q - Y (α + (k : ℝ) * h) q| ≤ r := hq.2
  obtain ⟨hk1, hk2⟩ := abs_le.1 hqk
  obtain ⟨hi1, hi2⟩ := abs_le.1 hqi
  show |Y (α + ((k + i : ℕ) : ℝ) * h) q| ≤ 2 * r
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Summation over first hits.** For pairwise disjoint measurable events `E k` and measurable
events `A j`, if `ν (E k) * B i ≤ ν (E k ∩ A (k + i))`, then
`(∑_{k ≤ K} ν (E k)) * ∑_{i=1}^{M} B i ≤ ∑_{j ≤ K + M} ν (A j)`. -/
theorem sum_measure_mul_sum_le_of_disjoint {E A : ℕ → Set Ω} {B : ℕ → ℝ≥0∞}
    (hE : ∀ k, MeasurableSet (E k)) (hd : ∀ k k', k ≠ k' → Disjoint (E k) (E k'))
    (hA : ∀ j, MeasurableSet (A j)) (hstep : ∀ k i, ν (E k) * B i ≤ ν (E k ∩ A (k + i)))
    (K M : ℕ) :
    (∑ k ∈ Finset.range (K + 1), ν (E k)) * ∑ i ∈ Finset.Icc 1 M, B i ≤
      ∑ j ∈ Finset.range (K + M + 1), ν (A j) := by
  calc (∑ k ∈ Finset.range (K + 1), ν (E k)) * ∑ i ∈ Finset.Icc 1 M, B i
      = ∑ k ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 M, ν (E k) * B i := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 M, ν (E k ∩ A (k + i)) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => hstep k i
    _ ≤ ∑ k ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (K + M + 1), ν (E k ∩ A j) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkK : k < K + 1 := Finset.mem_range.1 hk
        calc ∑ i ∈ Finset.Icc 1 M, ν (E k ∩ A (k + i))
            = ∑ j ∈ (Finset.Icc 1 M).map (addLeftEmbedding k), ν (E k ∩ A j) :=
              (Finset.sum_map (Finset.Icc 1 M) (addLeftEmbedding k) fun j => ν (E k ∩ A j)).symm
          _ ≤ ∑ j ∈ Finset.range (K + M + 1), ν (E k ∩ A j) := by
              refine Finset.sum_le_sum_of_subset fun j hj => ?_
              obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
              have hiM : i ≤ M := (Finset.mem_Icc.1 hi).2
              exact Finset.mem_range.2 (show k + i < K + M + 1 by omega)
    _ = ∑ j ∈ Finset.range (K + M + 1), ∑ k ∈ Finset.range (K + 1), ν (E k ∩ A j) :=
        Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (K + M + 1), ν (A j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc ∑ k ∈ Finset.range (K + 1), ν (E k ∩ A j)
            = ν (⋃ k ∈ Finset.range (K + 1), E k ∩ A j) :=
              (measure_biUnion_finset (fun k _ k' _ hne => Set.disjoint_left.2 fun q hq hq' =>
                Set.disjoint_left.1 (hd k k' hne) hq.1 hq'.1) fun k _ => (hE k).inter (hA j)).symm
          _ ≤ ν (A j) := measure_mono (Set.iUnion₂_subset fun k _ => Set.inter_subset_right)

/-- **First-hit decomposition on an arithmetic grid of levels.** Let `Y` be a process indexed by
levels with measurable values, such that for levels `0 ≤ aᵢ ≤ b ≤ c` the increment `Y c - Y b` is
independent of `(Y (aᵢ))ᵢ` and has the law of `Y (c - b)`, in the product form
`ν {(Y (aᵢ))ᵢ ∈ S, Y c - Y b ∈ T} = ν {(Y (aᵢ))ᵢ ∈ S} ν {Y (c - b) ∈ T}`. Then along the grid
`a_k = α + k h` (`α, h ≥ 0`),
`ν {∃ k ≤ K, |Y a_k| ≤ r} * ∑_{i=1}^{M} ν {|Y (i h)| ≤ r} ≤ ∑_{j=0}^{K+M} ν {|Y a_j| ≤ 2 r}`. -/
theorem measure_exists_abs_le_mul_sum_le (hY : ∀ t, Measurable (Y t))
    (hind : ∀ (n : ℕ) (a : Fin n → ℝ) (b c : ℝ), (∀ i, 0 ≤ a i) → (∀ i, a i ≤ b) → 0 ≤ b →
      b ≤ c → ∀ S : Set (Fin n → ℝ), MeasurableSet S → ∀ T : Set ℝ, MeasurableSet T →
        ν {q | (fun i => Y (a i) q) ∈ S ∧ Y c q - Y b q ∈ T} =
          ν {q | (fun i => Y (a i) q) ∈ S} * ν {q | Y (c - b) q ∈ T})
    {α h : ℝ} (hα : 0 ≤ α) (hh : 0 ≤ h) (r : ℝ) (K M : ℕ) :
    ν {q | ∃ k ≤ K, |Y (α + k * h) q| ≤ r} * ∑ i ∈ Finset.Icc 1 M, ν {q | |Y (i * h) q| ≤ r} ≤
      ∑ j ∈ Finset.range (K + M + 1), ν {q | |Y (α + j * h) q| ≤ 2 * r} := by
  calc ν {q | ∃ k ≤ K, |Y (α + k * h) q| ≤ r} * ∑ i ∈ Finset.Icc 1 M, ν {q | |Y (i * h) q| ≤ r}
      ≤ (∑ k ∈ Finset.range (K + 1), ν ({q | |Y (α + k * h) q| ≤ r} ∩
          ⋂ l : Fin k, {q | r < |Y (α + ((l : ℕ) : ℝ) * h) q|})) *
          ∑ i ∈ Finset.Icc 1 M, ν {q | |Y (i * h) q| ≤ r} := by
        gcongr ?_ * _
        exact (measure_mono (subset_biUnion_firstHit α h r K)).trans
          (measure_biUnion_finset_le _ _)
    _ ≤ ∑ j ∈ Finset.range (K + M + 1), ν {q | |Y (α + j * h) q| ≤ 2 * r} :=
        sum_measure_mul_sum_le_of_disjoint (fun k => measurableSet_firstHit hY α h r k)
          (fun _ _ hne => disjoint_firstHit hne)
          (fun _ => measurableSet_le (continuous_abs.measurable.comp (hY _)) measurable_const)
          (fun k i => measure_firstHit_mul_le hind hα hh r k i) K M

end FirstHit

section PathLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- **First-hit decomposition for the level-passage process.** Under
`ν = (W ⊗ W) ⊗ (W ⊗ W)`, `W` the Brownian path law, the level process `Y = cauchyLevel` satisfies,
along the grid `a_k = α + k h` (`α, h ≥ 0`),
`ν {∃ k ≤ K, |Y a_k| ≤ r} * ∑_{i=1}^{M} ν {|Y (i h)| ≤ r} ≤ ∑_{j=0}^{K+M} ν {|Y a_j| ≤ 2 r}`. -/
theorem measure_exists_abs_cauchyLevel_le_mul_sum_le (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {α h : ℝ} (hα : 0 ≤ α) (hh : 0 ≤ h) (r : ℝ) (K M : ℕ) :
    (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
        {q | ∃ k ≤ K, |cauchyLevel (α + k * h) q| ≤ r} *
      ∑ i ∈ Finset.Icc 1 M, (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
        {q | |cauchyLevel (i * h) q| ≤ r} ≤
      ∑ j ∈ Finset.range (K + M + 1),
        (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
          ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
          {q | |cauchyLevel (α + j * h) q| ≤ 2 * r} := by
  refine measure_exists_abs_le_mul_sum_le measurable_cauchyLevel ?_ hα hh r K M
  intro n a b c ha hab hb hbc S hS T hT
  have hf : Measurable fun q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) =>
      fun i => cauchyLevel (a i) q :=
    measurable_pi_iff.2 fun i => measurable_cauchyLevel (a i)
  have hg : Measurable fun q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) =>
      cauchyLevel c q - cauchyLevel b q :=
    (measurable_cauchyLevel c).sub (measurable_cauchyLevel b)
  have hfS : MeasurableSet {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) |
      (fun i => cauchyLevel (a i) q) ∈ S} := hf hS
  have hgT : MeasurableSet {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) |
      cauchyLevel c q - cauchyLevel b q ∈ T} := hg hT
  have hfgST : MeasurableSet {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) |
      (fun i => cauchyLevel (a i) q) ∈ S ∧ cauchyLevel c q - cauchyLevel b q ∈ T} :=
    hfS.inter hgT
  have hcT : MeasurableSet {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) |
      cauchyLevel (c - b) q ∈ T} := measurable_cauchyLevel (c - b) hT
  have hprod : ∀ q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)),
      Set.indicator {q | (fun i => cauchyLevel (a i) q) ∈ S ∧
        cauchyLevel c q - cauchyLevel b q ∈ T}
        (1 : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) → ℝ≥0∞) q =
        S.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) (fun i => cauchyLevel (a i) q) *
          T.indicator (1 : ℝ → ℝ≥0∞) (cauchyLevel c q - cauchyLevel b q) := fun q => by
    rw [show {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) |
        (fun i => cauchyLevel (a i) q) ∈ S ∧ cauchyLevel c q - cauchyLevel b q ∈ T} =
        {q | (fun i => cauchyLevel (a i) q) ∈ S} ∩ {q | cauchyLevel c q - cauchyLevel b q ∈ T}
        from rfl, inter_indicator_one]
    rfl
  have key := lintegral_cauchyLevel_mul_sub hB hm hcont ha hab hb hbc
    (measurable_one.indicator hS) (measurable_one.indicator hT)
  rw [← lintegral_indicator_one hcT, ← lintegral_indicator_one hfS,
    ← lintegral_indicator_one hfgST]
  exact (lintegral_congr hprod).trans key

end PathLaw

end LatticeProb
