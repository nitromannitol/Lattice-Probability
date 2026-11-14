import Mathlib
import LatticeProb.Prob.CauchyLevelSmallBall
import LatticeProb.Prob.CorrelatedBMIndependentHalves
import LatticeProb.Prob.CorrelatedBMNoCommonContour
import LatticeProb.Analysis.FirstBelowRestart
import LatticeProb.Topology.ContinuousMapBorel
import LatticeProb.Prob.CauchyLevelPolarityEstimate

/-!
# Points are polar for the level-passage process of a Brownian pair

Let `(L, R)` be two independent two-sided standard Brownian motions. For a level `l < 0` let
`T = firstBelow L 0 l` and `S = lastBelow L 0 l` be the ends of the straddling pair of `L` at time
`0`. This file proves that almost surely `R S ≠ R T` for every `l < 0` simultaneously
(`CauchyPointPolarInput`), from the polarity estimate for the level-passage process on dyadic grids
of levels (`exists_measure_dyadicLevel_abs_cauchyLevel_le_div_log`).

* `map_pathMap_eq_of_isBrownianReal`: two Brownian motions with continuous paths have the same law
  on `C(ℝ≥0, ℝ)`.
* `tendsto_cauchyLevel_nhdsLE`: on paths started at `0` with finite passage times, the level
  process `a ↦ cauchyLevel a q` is left-continuous at every `a > 0`.
* `exists_forall_ge_dyadicLevel_abs_cauchyLevel_le`: a zero at a level `a ∈ (α, β]` forces small
  values at levels of every fine dyadic grid of `[α, β]`.
* `measure_exists_Ioc_cauchyLevel_eq_zero`, `ae_forall_pos_cauchyLevel_ne_zero`: the polarity
  estimate `C / log (1 / r)` gives that almost surely the level process has no zero at a positive
  level.
* `CorrelatedBM.map_halfPathQuad_eq`: the four half paths of `(L, R)` have the law
  `(W ⊗ W) ⊗ (W ⊗ W)`, `W` the Brownian path law.
* `CorrelatedBM.cauchyPointPolarInput_of_polarityEstimate`: the polarity of points, from any
  polarity estimate of this form; `CorrelatedBM.cauchyPointPolarInput`: the polarity of points.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

noncomputable section

section PathLawUniqueness

/-- The coordinate map of continuous paths to all functions `ℝ≥0 → ℝ` is measurable. -/
theorem measurable_coeFn_continuousMap :
    Measurable (fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t) :=
  measurable_pi_iff.mpr fun t => (continuous_eval_const t).measurable

/-- The Borel σ-algebra of `C(ℝ≥0, ℝ)` is the one induced by the map to `ℝ≥0 → ℝ`. -/
theorem measurableSpace_continuousMap_eq_comap_coeFn :
    (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) =
      MeasurableSpace.comap (fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t) inferInstance := by
  let raw := fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t
  refine le_antisymm ?_ measurable_coeFn_continuousMap.comap_le
  change (continuousMapMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ)) ≤
    MeasurableSpace.comap raw inferInstance
  rw [ContinuousMapBorel.ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  refine iSup_le fun t => ?_
  have heval : Measurable[MeasurableSpace.comap raw inferInstance]
      (fun w : C(ℝ≥0, ℝ) => w t) := by
    let : MeasurableSpace C(ℝ≥0, ℝ) := MeasurableSpace.comap raw inferInstance
    exact (measurable_pi_apply t).comp (comap_measurable raw)
  exact heval.comap_le

/-- Two measures on a space whose σ-algebra is the pull-back along a measurable map `f` are equal
when their push-forwards along `f` agree. -/
theorem measure_eq_of_map_eq_of_eq_comap {X Y : Type*}
    [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {f : X → Y}
    (hgen : mX = mY.comap f) (hf : Measurable f) {μ ν : Measure X}
    (heq : μ.map f = ν.map f) : μ = ν := by
  ext s hs
  have hs' : MeasurableSet[mY.comap f] s := hgen ▸ hs
  obtain ⟨t, ht, rfl⟩ := hs'
  simpa only [Measure.map_apply hf ht] using congrArg (fun ρ : Measure Y ↦ ρ t) heq

/-- **Uniqueness of the Brownian path law.** Two real Brownian motions with continuous paths,
possibly on different probability spaces, have the same law on `C(ℝ≥0, ℝ)`. -/
theorem map_pathMap_eq_of_isBrownianReal {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {B : ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hB' : IsBrownianReal B' P') (hm' : ∀ t, Measurable (B' t))
    (hcont' : ∀ ω, Continuous fun t => B' t ω) :
    P.map (pathMap B hcont) = P'.map (pathMap B' hcont') := by
  refine measure_eq_of_map_eq_of_eq_comap measurableSpace_continuousMap_eq_comap_coeFn
    measurable_coeFn_continuousMap ?_
  have hX := measurable_coeFn_continuousMap.comp (measurable_pathMap B hm hcont)
  have hX' := measurable_coeFn_continuousMap.comp (measurable_pathMap B' hm' hcont')
  rw [Measure.map_map measurable_coeFn_continuousMap (measurable_pathMap B hm hcont),
    Measure.map_map measurable_coeFn_continuousMap (measurable_pathMap B' hm' hcont')]
  have hP : IsProjectiveLimit
      (P.map ((fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t) ∘ pathMap B hcont))
      BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict hX]
    exact (hB.hasLaw I).map_eq
  have hP' : IsProjectiveLimit
      (P'.map ((fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t) ∘ pathMap B' hcont'))
      BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict hX']
    exact (hB'.hasLaw I).map_eq
  exact hP.unique hP'

end PathLawUniqueness

section LeftContinuity

/-- The first passage below a level after time `0` only depends on the function on `[0, ∞)`. -/
theorem firstBelow_zero_congr {f g : ℝ → ℝ} (h : ∀ t, 0 ≤ t → f t = g t) (l : ℝ) :
    firstBelow f 0 l = firstBelow g 0 l := by
  unfold firstBelow
  congr 1
  ext t
  exact and_congr_right fun ht => by rw [h t ht]

/-- **Left continuity of the passage value.** For a pair `p` whose first path starts at `0` and has
a finite first passage at every level `-a ≤ 0`, the value of the second path at the first passage
of the first path at `-b` converges to its value at `-a` as `b ↑ a`, for every `a > 0`. -/
theorem tendsto_passageValue_nhdsLE {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)} (hp0 : p.1 0 = 0)
    (hp : ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (p.1 : ℝ≥0 → ℝ) ≠ ⊤) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun b => passageValue b p) (𝓝[≤] a) (𝓝 (passageValue a p)) := by
  have hval : ∀ b : ℝ, 0 ≤ b →
      passageValue b p = p.2 (firstBelow (fun t : ℝ => p.1 t.toNNReal) 0 (-b)).toNNReal := by
    intro b hb
    have h := hitFrom_neg_toNNReal_eq_firstBelow hp0 hb (hp b hb)
    show p.2 (hitFrom (-b) 0 (p.1 : ℝ≥0 → ℝ)).toNNReal = _
    rw [← h, Real.toNNReal_coe]
  obtain ⟨s, -, -, hs, -⟩ := exists_hitFrom_eq p.1.continuous (hp a ha.le)
  have hex : ∃ b, (0 : ℝ) ≤ b ∧ (fun t : ℝ => p.1 t.toNNReal) b ≤ -a := by
    refine ⟨s, s.coe_nonneg, ?_⟩
    show p.1 (s : ℝ).toNNReal ≤ -a
    rw [Real.toNNReal_coe, hs]
  have hcont : Continuous fun t : ℝ => p.2 t.toNNReal :=
    p.2.continuous.comp continuous_real_toNNReal
  have hlim := (hcont.tendsto _).comp
    (tendsto_firstBelow_neg_nhdsLE (p.1.continuous.comp continuous_real_toNNReal) hex)
  rw [hval a ha.le]
  refine Tendsto.congr' ?_ hlim
  filter_upwards [Ioc_mem_nhdsLE ha] with b hb
  exact (hval b hb.1.le).symm

/-- **Left continuity of the level process.** If the first paths `q.1.1`, `q.2.1` of both pairs
start at `0` and have finite first passages at every level `-a ≤ 0`, then
`cauchyLevel b q → cauchyLevel a q` as `b ↑ a`, for every `a > 0`. -/
theorem tendsto_cauchyLevel_nhdsLE {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))}
    (h₁0 : q.1.1 0 = 0) (h₁ : ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.1.1 : ℝ≥0 → ℝ) ≠ ⊤)
    (h₂0 : q.2.1 0 = 0) (h₂ : ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.2.1 : ℝ≥0 → ℝ) ≠ ⊤)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun b => cauchyLevel b q) (𝓝[≤] a) (𝓝 (cauchyLevel a q)) :=
  (tendsto_passageValue_nhdsLE h₂0 h₂ ha).sub (tendsto_passageValue_nhdsLE h₁0 h₁ ha)

/-- `2^{-n} = (1/2)^n`. -/
theorem two_zpow_neg_natCast_eq_half_pow (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2) ^ n := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- **Event inclusion.** Under the hypotheses of `tendsto_cauchyLevel_nhdsLE`, if the level process
vanishes at a level `a ∈ (α, β]` with `α ≥ 0`, then for every `r > 0` and every sufficiently fine
dyadic grid `α + i 2^{-n}`, some grid level in `[α, β]` carries a value of modulus at most `r`. -/
theorem exists_forall_ge_dyadicLevel_abs_cauchyLevel_le
    {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))}
    (h₁0 : q.1.1 0 = 0) (h₁ : ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.1.1 : ℝ≥0 → ℝ) ≠ ⊤)
    (h₂0 : q.2.1 0 = 0) (h₂ : ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.2.1 : ℝ≥0 → ℝ) ≠ ⊤)
    {α β a : ℝ} (hα : 0 ≤ α) (hαa : α < a) (haβ : a ≤ β) (hY : cauchyLevel a q = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ i : ℕ, α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
      |cauchyLevel (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r := by
  have ha : 0 < a := hα.trans_lt hαa
  have hlim := tendsto_cauchyLevel_nhdsLE h₁0 h₁ h₂0 h₂ ha
  rw [hY] at hlim
  have hmem : {b | |cauchyLevel b q| ≤ r} ∈ 𝓝[≤] a := by
    have h := hlim.abs
    rw [abs_zero] at h
    exact h (Iic_mem_nhds hr)
  obtain ⟨c, hc, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.1 hmem
  have hgap : 0 < a - max c α := sub_pos.2 (max_lt hc hαa)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn => ?_⟩
  set h : ℝ := (2 : ℝ) ^ (-(n : ℤ)) with hh_def
  have hh : 0 < h := zpow_pos two_pos _
  have hhN : h < a - max c α := by
    rw [hh_def, two_zpow_neg_natCast_eq_half_pow]
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans_lt hN
  set i : ℕ := ⌊(a - α) / h⌋₊ with hi_def
  have hi1 : (i : ℝ) * h ≤ a - α :=
    (le_div_iff₀ hh).1 (Nat.floor_le (div_nonneg (sub_nonneg.2 hαa.le) hh.le))
  have hi2 : a - α < ((i : ℝ) + 1) * h := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one _)
  rw [add_mul, one_mul] at hi2
  have hi0 : (0 : ℝ) ≤ i * h := mul_nonneg i.cast_nonneg hh.le
  have hcm : c ≤ max c α := le_max_left _ _
  have hαm : α ≤ max c α := le_max_right _ _
  have hb : α + (i : ℝ) * h ∈ Ioc c a := ⟨by linarith, by linarith⟩
  exact ⟨i, ⟨by linarith, by linarith⟩, hsub hb⟩

end LeftContinuity

section Polarity

/-- **Polarity on an interval of levels.** Let `ν` be a measure on two pairs of paths under which
almost surely both first paths start at `0` and have finite first passages at every level `-a ≤ 0`.
If, for `0 ≤ α`, the probability that the level process is at most `r` in modulus at some level of
the dyadic grid `α + i 2^{-n}` in `[α, β]` is at most `C / log (1 / r)` whenever
`2^{-n} ≤ r ≤ r₀`, then the level process has no zero at a level of `(α, β]`, `ν`-almost surely. -/
theorem measure_exists_Ioc_cauchyLevel_eq_zero
    {ν : Measure ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)))}
    (hgood : ∀ᵐ q ∂ν, (q.1.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.1.1 : ℝ≥0 → ℝ) ≠ ⊤) ∧
      (q.2.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.2.1 : ℝ≥0 → ℝ) ≠ ⊤))
    {α β : ℝ} (hα : 0 ≤ α) {C r₀ : ℝ} (hC : 0 < C) (hr₀ : 0 < r₀)
    (hbound : ∀ n : ℕ, ∀ r : ℝ, (2 : ℝ) ^ (-(n : ℤ)) ≤ r → r ≤ r₀ →
      ν {q | ∃ i : ℕ, α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
        |cauchyLevel (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r} ≤
        ENNReal.ofReal (C / Real.log (1 / r))) :
    ν {q | ∃ a ∈ Ioc α β, cauchyLevel a q = 0} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  set r : ℝ := min (min r₀ (1 / 2)) (Real.exp (-(C / ε))) with hr_def
  have hr : 0 < r := lt_min (lt_min hr₀ (by norm_num)) (Real.exp_pos _)
  have hrr₀ : r ≤ r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hrexp : r ≤ Real.exp (-(C / ε)) := min_le_right _ _
  have hlog : C / ε ≤ Real.log (1 / r) := by
    have h1 := Real.log_le_log hr hrexp
    rw [Real.log_exp] at h1
    rw [one_div, Real.log_inv]
    linarith
  have hlogpos : 0 < Real.log (1 / r) := (div_pos hC hεpos).trans_le hlog
  have hCle : C / Real.log (1 / r) ≤ ε := by
    rw [div_le_iff₀ hlogpos]
    calc C ≤ Real.log (1 / r) * ε := (div_le_iff₀ hεpos).1 hlog
      _ = ε * Real.log (1 / r) := mul_comm _ _
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  calc ν {q | ∃ a ∈ Ioc α β, cauchyLevel a q = 0}
      ≤ ν (⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), {q | ∃ i : ℕ, α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
          |cauchyLevel (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r}) := by
        refine measure_mono_ae ?_
        filter_upwards [hgood] with q hq hqZ
        obtain ⟨a, ⟨hαa, haβ⟩, hY⟩ := hqZ
        obtain ⟨N, hN⟩ := exists_forall_ge_dyadicLevel_abs_cauchyLevel_le hq.1.1 hq.1.2 hq.2.1
          hq.2.2 hα hαa haβ hY hr
        exact Set.mem_iUnion.2 ⟨N, Set.mem_iInter₂.2 hN⟩
    _ = ⨆ N : ℕ, ν (⋂ n : ℕ, ⋂ (_ : N ≤ n), {q | ∃ i : ℕ,
          α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
          |cauchyLevel (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r}) :=
        Monotone.measure_iUnion fun N N' hNN' q hq =>
          Set.mem_iInter₂.2 fun n hn => Set.mem_iInter₂.1 hq n (hNN'.trans hn)
    _ ≤ ENNReal.ofReal (C / Real.log (1 / r)) := by
        refine iSup_le fun N => (measure_mono (Set.iInter₂_subset (max N m)
          (le_max_left N m))).trans ?_
        refine hbound (max N m) r ?_ hrr₀
        rw [two_zpow_neg_natCast_eq_half_pow]
        exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right N m)).trans hm.le
    _ ≤ ε := (ENNReal.ofReal_le_ofReal hCle).trans_eq ENNReal.ofReal_coe_nnreal

/-- **Polarity of points for the level process.** Under the hypotheses of
`measure_exists_Ioc_cauchyLevel_eq_zero` for every `0 < α < β`, almost surely the level process
has no zero at a positive level. -/
theorem ae_forall_pos_cauchyLevel_ne_zero
    {ν : Measure ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)))}
    (hgood : ∀ᵐ q ∂ν, (q.1.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.1.1 : ℝ≥0 → ℝ) ≠ ⊤) ∧
      (q.2.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.2.1 : ℝ≥0 → ℝ) ≠ ⊤))
    (hbound : ∀ {α β : ℝ}, 0 < α → α < β →
      ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ n : ℕ, ∀ r : ℝ, (2 : ℝ) ^ (-(n : ℤ)) ≤ r → r ≤ r₀ →
        ν {q | ∃ i : ℕ, α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
          |cauchyLevel (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r} ≤
          ENNReal.ofReal (C / Real.log (1 / r))) :
    ∀ᵐ q ∂ν, ∀ a : ℝ, 0 < a → cauchyLevel a q ≠ 0 := by
  have hm : ∀ m : ℕ, ∀ᵐ q ∂ν, ∀ a ∈ Ioc (1 / ((m : ℝ) + 2)) ((m : ℝ) + 2), cauchyLevel a q ≠ 0 := by
    intro m
    have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hα : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    have hαβ : 1 / ((m : ℝ) + 2) < (m : ℝ) + 2 := by
      rw [div_lt_iff₀ hpos]
      nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    obtain ⟨C, r₀, hC, hr₀, hb⟩ := hbound hα hαβ
    rw [ae_iff]
    refine measure_mono_null (fun q hq => ?_)
      (measure_exists_Ioc_cauchyLevel_eq_zero hgood hα.le hC hr₀ hb)
    have hq' : ¬∀ a ∈ Ioc (1 / ((m : ℝ) + 2)) ((m : ℝ) + 2), cauchyLevel a q ≠ 0 := hq
    push Not at hq'
    exact hq'
  filter_upwards [ae_all_iff.2 hm] with q hq a ha
  obtain ⟨m, hm1⟩ : ∃ m : ℕ, 1 / a + a ≤ m := ⟨⌈1 / a + a⌉₊, Nat.le_ceil _⟩
  have ha' : 0 < 1 / a := one_div_pos.2 ha
  refine hq m a ⟨?_, by linarith⟩
  rw [one_div_lt (by positivity) ha]
  linarith

/-- Under the law `(W ⊗ W) ⊗ (W ⊗ W)`, `W` the Brownian path law, almost surely both first paths
start at `0` and have finite first passages at every level `-a ≤ 0`. -/
theorem ae_hitFrom_neg_ne_top_pathLaw_quad {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) :
    ∀ᵐ q ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont)))),
      (q.1.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.1.1 : ℝ≥0 → ℝ) ≠ ⊤) ∧
      (q.2.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.2.1 : ℝ≥0 → ℝ) ≠ ⊤) := by
  have : IsProbabilityMeasure (P.map (pathMap B hcont)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2
      inferInstance
  have hW := ae_hitFrom_neg_ne_top_pathLaw hB hm hcont
  have hW₁ : ∀ᵐ x ∂((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))),
      x.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (x.1 : ℝ≥0 → ℝ) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_fst.ae hW
  have h₁ : ∀ᵐ q ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont)))),
      q.1.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.1.1 : ℝ≥0 → ℝ) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_fst.ae hW₁
  have h₂ : ∀ᵐ q ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont)))),
      q.2.1 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (q.2.1 : ℝ≥0 → ℝ) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_snd.ae hW₁
  exact h₁.and h₂

end Polarity

end

namespace CorrelatedBM

open MatedCRTHarmonic.MatedCRT

noncomputable section

/-- The half path `halfPath k` of a two-sided pair as a continuous path on `ℝ≥0`. -/
def halfPathMap (k : Fin 2 × Bool) : Path2 → C(ℝ≥0, ℝ) :=
  pathMap (halfPath k) (continuous_halfPath k)

theorem measurable_halfPathMap (k : Fin 2 × Bool) : Measurable (halfPathMap k) :=
  measurable_pathMap _ (measurable_halfPath k) _

/-- The four half paths, grouped as the forward pair `(L⁺, R⁺)` and the backward pair
`(L⁻, R⁻)`. -/
def halfPathQuad (ω : Path2) : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) :=
  ((halfPathMap (0, true) ω, halfPathMap (1, true) ω),
    (halfPathMap (0, false) ω, halfPathMap (1, false) ω))

theorem measurable_halfPathQuad : Measurable halfPathQuad :=
  ((measurable_halfPathMap (0, true)).prodMk (measurable_halfPathMap (1, true))).prodMk
    ((measurable_halfPathMap (0, false)).prodMk (measurable_halfPathMap (1, false)))

/-- **Independence of the four continuous half paths at `γ = √2`.** -/
theorem iIndepFun_halfPathMap {μ : Measure Path2} (hμ : IsCorrelatedBM2 (√2) μ) :
    iIndepFun halfPathMap μ := by
  have h := iIndepFun_halfPath hμ
  rw [iIndepFun_iff_iIndep] at h ⊢
  convert h using 1
  funext k
  exact (congrArg (MeasurableSpace.comap (halfPathMap k))
    measurableSpace_continuousMap_eq_comap_coeFn).trans MeasurableSpace.comap_comp

/-- **Law of the four half paths at `γ = √2`.** The forward and backward pairs of half paths of
two independent two-sided Brownian motions have the law `(W ⊗ W) ⊗ (W ⊗ W)`, where `W` is the law
of the forward half path of `L`. -/
theorem map_halfPathQuad_eq {μ : Measure Path2} (hμ : IsCorrelatedBM2 (√2) μ) :
    μ.map halfPathQuad =
      ((μ.map (pathMap (halfPath (0, true)) (continuous_halfPath (0, true)))).prod
          (μ.map (pathMap (halfPath (0, true)) (continuous_halfPath (0, true))))).prod
        ((μ.map (pathMap (halfPath (0, true)) (continuous_halfPath (0, true)))).prod
          (μ.map (pathMap (halfPath (0, true)) (continuous_halfPath (0, true))))) := by
  have := hμ.isProbabilityMeasure
  have hind := iIndepFun_halfPathMap hμ
  have hm := measurable_halfPathMap
  have hlaw : ∀ k, μ.map (halfPathMap k) =
      μ.map (pathMap (halfPath (0, true)) (continuous_halfPath (0, true))) := fun k =>
    map_pathMap_eq_of_isBrownianReal (isBrownianReal_halfPath hμ k) (measurable_halfPath k)
      (continuous_halfPath k) (isBrownianReal_halfPath hμ (0, true)) (measurable_halfPath _)
      (continuous_halfPath _)
  have h₁ : IndepFun (halfPathMap (0, true)) (halfPathMap (1, true)) μ := hind.indepFun (by decide)
  have h₂ : IndepFun (halfPathMap (0, false)) (halfPathMap (1, false)) μ :=
    hind.indepFun (by decide)
  have h₁₂ : IndepFun (fun ω => (halfPathMap (0, true) ω, halfPathMap (1, true) ω))
      (fun ω => (halfPathMap (0, false) ω, halfPathMap (1, false) ω)) μ :=
    hind.indepFun_prodMk_prodMk hm _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  rw [show halfPathQuad = fun ω => ((halfPathMap (0, true) ω, halfPathMap (1, true) ω),
      (halfPathMap (0, false) ω, halfPathMap (1, false) ω)) from rfl,
    (indepFun_iff_map_prod_eq_prod_map_map ((hm _).prodMk (hm _)).aemeasurable
      ((hm _).prodMk (hm _)).aemeasurable).1 h₁₂,
    (indepFun_iff_map_prod_eq_prod_map_map (hm _).aemeasurable (hm _).aemeasurable).1 h₁,
    (indepFun_iff_map_prod_eq_prod_map_map (hm _).aemeasurable (hm _).aemeasurable).1 h₂,
    hlaw (0, true), hlaw (1, true), hlaw (0, false), hlaw (1, false)]

/-- **Identification of the level process.** If the forward and backward half paths of `L` start
at `0` and have finite first passages at every level `-a ≤ 0`, then for `a ≥ 0` the increment of
`R` across the straddling pair of `L` at level `-a` is the level process of the four half paths:
`R (lastBelow L 0 (-a)) - R (firstBelow L 0 (-a)) = cauchyLevel a (halfPathQuad ω)`. -/
theorem lrCoord_lastBelow_sub_lrCoord_firstBelow {ω : Path2}
    (h₁0 : halfPathMap (0, true) ω 0 = 0)
    (h₁ : ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (halfPathMap (0, true) ω : ℝ≥0 → ℝ) ≠ ⊤)
    (h₂0 : halfPathMap (0, false) ω 0 = 0)
    (h₂ : ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (halfPathMap (0, false) ω : ℝ≥0 → ℝ) ≠ ⊤)
    {a : ℝ} (ha : 0 ≤ a) :
    lrCoord 1 (lastBelow (fun u => lrCoord 0 u ω) 0 (-a)) ω -
        lrCoord 1 (firstBelow (fun u => lrCoord 0 u ω) 0 (-a)) ω =
      cauchyLevel a (halfPathQuad ω) := by
  have hfirst : firstBelow (fun u => lrCoord 0 u ω) 0 (-a) =
      ((hitFrom (-a) 0 (halfPathMap (0, true) ω : ℝ≥0 → ℝ)).toNNReal : ℝ) := by
    rw [hitFrom_neg_toNNReal_eq_firstBelow h₁0 ha (h₁ a ha)]
    exact firstBelow_zero_congr (fun t ht => by
      show lrCoord 0 t ω = lrCoord 0 (t.toNNReal : ℝ) ω
      rw [Real.coe_toNNReal t ht]) (-a)
  have hlast : lastBelow (fun u => lrCoord 0 u ω) 0 (-a) =
      -((hitFrom (-a) 0 (halfPathMap (0, false) ω : ℝ≥0 → ℝ)).toNNReal : ℝ) := by
    rw [lastBelow_eq_neg_firstBelow, neg_zero,
      hitFrom_neg_toNNReal_eq_firstBelow h₂0 ha (h₂ a ha)]
    congr 1
    exact firstBelow_zero_congr (fun t ht => by
      show lrCoord 0 (-t) ω = lrCoord 0 (-(t.toNNReal : ℝ)) ω
      rw [Real.coe_toNNReal t ht]) (-a)
  rw [hlast, hfirst]
  rfl

/-- **Points of the level process are polar.** Given the polarity estimate for the level
process on dyadic grids of levels under the law `(W ⊗ W) ⊗ (W ⊗ W)` of any real Brownian motion
(`hpolar`), for two independent two-sided standard Brownian motions `(L, R)` almost surely, for every
level `l < 0`, `R` takes distinct values at the ends `lastBelow L 0 l`, `firstBelow L 0 l` of the
straddling pair of `L` at time `0`. -/
theorem cauchyPointPolarInput_of_polarityEstimate
    (hpolar : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {B : ℝ≥0 → Ω → ℝ}, IsBrownianReal B P → (∀ t, Measurable (B t)) →
      ∀ (hcont : ∀ ω, Continuous fun t => B t ω) {α β : ℝ}, 0 < α → α < β →
      ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ n : ℕ, ∀ r : ℝ, (2 : ℝ) ^ (-(n : ℤ)) ≤ r → r ≤ r₀ →
        (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
            ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
            {q | ∃ i : ℕ, α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
              |cauchyLevel (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r} ≤
          ENNReal.ofReal (C / Real.log (1 / r))) :
    CauchyPointPolarInput := by
  intro μ hμ
  have := hμ.isProbabilityMeasure
  have hB := isBrownianReal_halfPath hμ (0, true)
  have hgood := ae_hitFrom_neg_ne_top_pathLaw_quad hB (measurable_halfPath (0, true))
    (continuous_halfPath (0, true))
  have hY := ae_forall_pos_cauchyLevel_ne_zero hgood fun hα hαβ =>
    hpolar hB (measurable_halfPath (0, true)) (continuous_halfPath (0, true)) hα hαβ
  have hall := hgood.and hY
  rw [← map_halfPathQuad_eq hμ] at hall
  filter_upwards [ae_of_ae_map measurable_halfPathQuad.aemeasurable hall] with ω hω l hl
  have hl' : 0 < -l := neg_pos.2 hl
  have key := lrCoord_lastBelow_sub_lrCoord_firstBelow hω.1.1.1 hω.1.1.2 hω.1.2.1 hω.1.2.2 hl'.le
  rw [neg_neg] at key
  have h := hω.2 (-l) hl'
  rw [← key] at h
  exact sub_ne_zero.1 h

/-- **Points of the level process are polar.** For two independent two-sided standard Brownian
motions `(L, R)` almost surely, for every level `l < 0`, `R` takes distinct values at the ends
`lastBelow L 0 l`, `firstBelow L 0 l` of the straddling pair of `L` at time `0`. -/
theorem cauchyPointPolarInput : CauchyPointPolarInput :=
  cauchyPointPolarInput_of_polarityEstimate fun hB hm hcont =>
    fun hα hαβ => exists_measure_dyadicLevel_abs_cauchyLevel_le_div_log hB hm hcont hα hαβ

end

end CorrelatedBM

end LatticeProb
