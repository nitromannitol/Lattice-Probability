/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.GridAveragedInvariantVersion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.GridAveragedConstantReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketLLNRootChain
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridTranslationInvariance

/-!
# The invariant version of the chain limit, and `GridAveragedConstant` for a root chain system

`Temporal/GridAveragedConstantReduction.lean` proves `GridAveragedConstant` from
`p:lem:regeninvariant` (the named input `RegenerativeInvariance`), environment ergodicity, and an
**invariant version** `L⋆` of the tail limit: a function almost surely equal to it that, for
almost every grid, does not change under the joint time flow and the joint parabolic scaling of
trajectory and grid.  The manuscript supplies that version at the end of the proof of
`p:lem:timeconverge` (tex:1484):

> Finally use the actual block-average formula to define the limit … Under a fixed time
> re-rooting `s`, all sufficiently large origin blocks contain both `0` and `s` and are
> therefore the same intervals before translation.  Their averages coincide.  Scaling leaves
> the averages unchanged.

This module carries that out for the root dyadic chain `rootTimeBlock` of the marked grid, and
assembles the resulting discharge of `GridAveragedConstant`.

## What is proved

* `ae_rootExhausts` — under any uniform grid law the root chain almost surely exhausts the time
  axis.  For a fixed time `a` the level-`n` root block misses `a` only if the relative position
  of the origin lies within `|a|/2^n` of an endpoint of `[0,1)`, an event of probability at most
  `2|a|/2^n` by the level-`n` cylinder law alone; the integers then give every real time.
* `chainLimsup g D` — the upper limit of the root-block averages of `g`, the manuscript's
  "actual block-average formula".  `chainLimsup_eq_of_tendsto_nat`: it is the limit whenever the
  chain converges.  `chainLimsup_translate`: it is invariant under re-rooting the grid at any
  time when the chain exhausts the axis (`timeBlockAt_translate` and the partition identity).
  `chainLimsup_dilate`: it is invariant under every dilation, for every grid (the levels are
  reindexed by `levelShift`, which does not change an upper limit along `ℤ`).
* `measurable_chainLimsup` — joint measurability in (trajectory, grid).
* `gridAveragedConstant_of_rootChainSystem` — **`GridAveragedConstant` for the tail conditional
  expectation of an unmarked functional of a `BracketLLNRootChain.RootChainSystem`**, from
  `RegenerativeInvariance`, environment ergodicity, and the structure of the flow: the time flow
  is the product of a trajectory flow `θΩ` with the grid re-rooting `translate (timeVec t)`, and
  the density scales parabolically under `SΩ`.
* `ae_hasRootBlockData_of_regenerativeInvariance` and
  `ae_tendsto_intervalAverage_of_regenerativeInvariance` — composed with
  `BracketLLNRootChain`: `HasRootBlockData` and `p:prop:timeergodic` (forward half) for the root
  chain system, with **no** `GridAveragedConstant` hypothesis left.

## What is *not* proved here

`RegenerativeInvariance` (`p:lem:regeninvariant`), the construction of the actual
`RootChainSystem` (including its flow invariance `hθP`, which is stronger than the manuscript),
the scaling action of the actual process, and the annealed-to-quenched step.  Nothing here
certifies `p:lem:regeninvariant`, `p:prop:timeergodic`, `p:lem:bracketlimit`, `p:thm:areaclt`
or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal

namespace ReflectedGMS.GridAveragedInvariantVersion

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridDilationInvariance ReflectedGMS.UniformGridTranslationInvariance
open ReflectedGMS.Temporal.ActualDyadicTemporalBlocks
open ReflectedGMS.BracketTimeAverage ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.ConditionalTemporalAveraging ReflectedGMS.TailAverageIdentification
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.BracketLLNRootChain

/-! ### The root chain exhausts the time axis almost surely -/

theorem rootTimeBlock_mono (D : Grid) {k l : ℤ} (hkl : k ≤ l) :
    rootTimeBlock D k ⊆ rootTimeBlock D l :=
  timeBlockAt_subset_of_le D hkl 0

/-- The root dyadic chain of the grid eventually contains every time. -/
def RootExhausts (D : Grid) : Prop := ∀ t : ℝ, ∃ k : ℤ, t ∈ rootTimeBlock D k

theorem eventually_mem_rootTimeBlock {D : Grid} (hD : RootExhausts D) (t : ℝ) :
    ∀ᶠ k : ℤ in atTop, t ∈ rootTimeBlock D k := by
  obtain ⟨N, hN⟩ := hD t
  exact eventually_atTop.2 ⟨N, fun k hk => rootTimeBlock_mono D hk hN⟩

/-- The level-`k`, depth-`0` cylinder event that the first coordinate of the relative origin
lies in `A`, the second being free. -/
def posCyl (A : Set ℝ) : Set (ℝ × ((Fin 2 → ℝ) × (Fin 0 → Fin 2 → Fin 2))) :=
  Set.univ ×ˢ ((Set.univ.pi fun i : Fin 2 => if i = 0 then A else Set.univ) ×ˢ Set.univ)

theorem measurableSet_posCyl {A : Set ℝ} (hA : MeasurableSet A) : MeasurableSet (posCyl A) := by
  refine MeasurableSet.prod MeasurableSet.univ
    (MeasurableSet.prod (MeasurableSet.univ_pi fun i => ?_) MeasurableSet.univ)
  show MeasurableSet (if i = 0 then A else Set.univ)
  by_cases hi : i = 0
  · rw [if_pos hi]
    exact hA
  · rw [if_neg hi]
    exact MeasurableSet.univ

/-- Under a uniform grid law, the relative position of the origin at every level is uniform on
`[0,1)`: the probability that it lies in `A` is the restricted Lebesgue measure of `A`. -/
theorem measure_posCyl {ν : Measure Grid} (hlaw : UniformGridLaw ν) (k : ℤ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ν (gridCylinder k 0 ⁻¹' posCyl A) = (volume.restrict (Set.Ico (0 : ℝ) 1)) A := by
  have hphase : (volume.restrict (Set.Ico (0 : ℝ) 1)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]
  have hpi : (Measure.pi fun _ : Fin 2 => volume.restrict (Set.Ico (0 : ℝ) 1))
      (Set.univ.pi fun i : Fin 2 => if i = 0 then A else Set.univ)
        = (volume.restrict (Set.Ico (0 : ℝ) 1)) A := by
    rw [Measure.pi_pi, Fin.prod_univ_two, if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0)),
      hphase, mul_one]
  rw [← Measure.map_apply (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k 0)
      (measurableSet_posCyl hA), hlaw.2 k 0, posCyl, Measure.prod_prod, Measure.prod_prod, hpi,
    hphase, measure_univ, one_mul, mul_one]

/-- The level-`n` root block has length at least `2^n`. -/
theorem pow_le_side_nat (D : Grid) (n : ℕ) : (2 : ℝ) ^ n ≤ side D (n : ℤ) := by
  have hside : side D (n : ℤ) = (2 : ℝ) ^ (D.phase + ((n : ℤ) : ℝ)) := rfl
  have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n
  have hφ : 0 ≤ D.phase := (Set.mem_Ico.1 D.phase_mem).1
  rw [hside, hcast, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **A fixed time misses the level-`n` root block only near the edges of the relative
position.** -/
theorem rootPosition_mem_of_not_mem_rootTimeBlock {D : Grid} {n : ℕ} {a : ℝ}
    (ha : a ∉ rootTimeBlock D (n : ℤ)) :
    rootPosition D (n : ℤ) ∈ Set.Icc 0 (|a| / 2 ^ n) ∪ Set.Icc (1 - |a| / 2 ^ n) 1 := by
  have hσ : 0 < side D (n : ℤ) := side_pos D _
  have hpow : (2 : ℝ) ^ n ≤ side D (n : ℤ) := pow_le_side_nat D n
  have h2pos : (0 : ℝ) < 2 ^ n := by positivity
  obtain ⟨hlow, hhigh⟩ := D.origin_position (n : ℤ) 0
  have hlow' : -side D (n : ℤ) < D.origin (n : ℤ) 0 := hlow
  have hou := rootPosition_mul_side D (n : ℤ)
  have hu0 : 0 ≤ rootPosition D (n : ℤ) := by
    have h : rootPosition D (n : ℤ) = -D.origin (n : ℤ) 0 / side D (n : ℤ) := rfl
    rw [h]
    exact div_nonneg (by linarith) hσ.le
  have hu1 : rootPosition D (n : ℤ) ≤ 1 := by
    have h : rootPosition D (n : ℤ) = -D.origin (n : ℤ) 0 / side D (n : ℤ) := rfl
    rw [h, div_le_one hσ]
    linarith
  rw [rootTimeBlock_eq, Set.mem_Ico, not_and_or, not_le, not_lt] at ha
  rcases ha with ha | ha
  · -- CONDITIONAL on `a < o_n`: the origin is within `|a|/2^n` of the left edge
    left
    refine Set.mem_Icc.2 ⟨hu0, ?_⟩
    rw [le_div_iff₀ h2pos]
    have ha0 : a < 0 := lt_of_lt_of_le ha hhigh
    have hua : rootPosition D (n : ℤ) * side D (n : ℤ) < |a| := by
      rw [hou, abs_of_neg ha0]
      linarith
    nlinarith
  · -- CONDITIONAL on `o_n + σ_n ≤ a`: the origin is within `|a|/2^n` of the right edge
    right
    refine Set.mem_Icc.2 ⟨?_, hu1⟩
    have ha0 : 0 < a := by linarith
    have hua : (1 - rootPosition D (n : ℤ)) * side D (n : ℤ) ≤ |a| := by
      have e : (1 - rootPosition D (n : ℤ)) * side D (n : ℤ)
          = D.origin (n : ℤ) 0 + side D (n : ℤ) := by
        linear_combination -hou
      rw [abs_of_pos ha0, e]
      exact ha
    have hmain : (1 - rootPosition D (n : ℤ)) * 2 ^ n ≤ |a| := by
      have h1u : 0 ≤ 1 - rootPosition D (n : ℤ) := by linarith
      nlinarith
    have hdiv : 1 - rootPosition D (n : ℤ) ≤ |a| / 2 ^ n := by
      rw [le_div_iff₀ h2pos]
      exact hmain
    linarith

/-- **For a fixed time, the root chain almost surely reaches it.** -/
theorem ae_exists_mem_rootTimeBlock {ν : Measure Grid} (hlaw : UniformGridLaw ν) (a : ℝ) :
    ∀ᵐ D ∂ν, ∃ k : ℤ, a ∈ rootTimeBlock D k := by
  have hbound : ∀ n : ℕ, ν {D : Grid | ∀ k : ℤ, a ∉ rootTimeBlock D k}
      ≤ ENNReal.ofReal (2 * (|a| / 2 ^ n)) := by
    intro n
    have hA : MeasurableSet (Set.Icc (0 : ℝ) (|a| / 2 ^ n) ∪ Set.Icc (1 - |a| / 2 ^ n) 1) :=
      measurableSet_Icc.union measurableSet_Icc
    have hsub : {D : Grid | ∀ k : ℤ, a ∉ rootTimeBlock D k}
        ⊆ gridCylinder (n : ℤ) 0 ⁻¹'
          posCyl (Set.Icc (0 : ℝ) (|a| / 2 ^ n) ∪ Set.Icc (1 - |a| / 2 ^ n) 1) := by
      intro D hD
      have hD' : ∀ k : ℤ, a ∉ rootTimeBlock D k := hD
      have hmem := rootPosition_mem_of_not_mem_rootTimeBlock (hD' (n : ℤ))
      have hpi : ∀ i : Fin 2, (gridCylinder (n : ℤ) 0 D).2.1 i ∈
          (if i = 0 then Set.Icc (0 : ℝ) (|a| / 2 ^ n) ∪ Set.Icc (1 - |a| / 2 ^ n) 1
            else Set.univ) := by
        intro i
        by_cases hi : i = 0
        · subst hi
          rw [if_pos rfl]
          exact hmem
        · rw [if_neg hi]
          exact Set.mem_univ _
      exact ⟨Set.mem_univ _, fun i _ => hpi i, Set.mem_univ _⟩
    calc ν {D : Grid | ∀ k : ℤ, a ∉ rootTimeBlock D k}
        ≤ ν (gridCylinder (n : ℤ) 0 ⁻¹'
            posCyl (Set.Icc (0 : ℝ) (|a| / 2 ^ n) ∪ Set.Icc (1 - |a| / 2 ^ n) 1)) :=
          measure_mono hsub
      _ = (volume.restrict (Set.Ico (0 : ℝ) 1))
            (Set.Icc (0 : ℝ) (|a| / 2 ^ n) ∪ Set.Icc (1 - |a| / 2 ^ n) 1) :=
          measure_posCyl hlaw (n : ℤ) hA
      _ ≤ volume (Set.Icc (0 : ℝ) (|a| / 2 ^ n) ∪ Set.Icc (1 - |a| / 2 ^ n) 1) :=
          Measure.restrict_apply_le _ _
      _ ≤ volume (Set.Icc (0 : ℝ) (|a| / 2 ^ n)) + volume (Set.Icc (1 - |a| / 2 ^ n) 1) :=
          measure_union_le _ _
      _ = ENNReal.ofReal (|a| / 2 ^ n) + ENNReal.ofReal (|a| / 2 ^ n) := by
          rw [Real.volume_Icc, Real.volume_Icc, sub_zero, sub_sub_cancel]
      _ = ENNReal.ofReal (2 * (|a| / 2 ^ n)) := by
          rw [two_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (|a| / 2 ^ n))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h0 : Tendsto (fun n : ℕ => |a| * (1 / 2 : ℝ) ^ n) atTop (𝓝 (|a| * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul |a|
    have hfun : (fun n : ℕ => |a| * (1 / 2 : ℝ) ^ n) = fun n : ℕ => |a| / 2 ^ n := by
      funext n
      rw [div_pow, one_pow, mul_one_div]
    rw [hfun, mul_zero] at h0
    have h2 := h0.const_mul 2
    rwa [mul_zero] at h2
  have hzero : ν {D : Grid | ∀ k : ℤ, a ∉ rootTimeBlock D k} = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) zero_le
  rw [ae_iff]
  refine le_antisymm (le_trans (measure_mono ?_) hzero.le) zero_le
  intro D hD
  have hD' : ¬∃ k : ℤ, a ∈ rootTimeBlock D k := hD
  show ∀ k : ℤ, a ∉ rootTimeBlock D k
  intro k hk
  exact hD' ⟨k, hk⟩

/-- **Under any uniform grid law, the root chain almost surely exhausts the time axis.** -/
theorem ae_rootExhausts {ν : Measure Grid} (hlaw : UniformGridLaw ν) :
    ∀ᵐ D ∂ν, RootExhausts D := by
  have hint : ∀ᵐ D ∂ν, ∀ z : ℤ, ∃ k : ℤ, (z : ℝ) ∈ rootTimeBlock D k :=
    ae_all_iff.2 fun z => ae_exists_mem_rootTimeBlock hlaw (z : ℝ)
  filter_upwards [hint] with D hD
  intro t
  obtain ⟨k₁, hk₁⟩ := hD ⌊t⌋
  obtain ⟨k₂, hk₂⟩ := hD (⌊t⌋ + 1)
  refine ⟨max k₁ k₂, ?_⟩
  have h1 := rootTimeBlock_mono D (le_max_left k₁ k₂) hk₁
  have h2 := rootTimeBlock_mono D (le_max_right k₁ k₂) hk₂
  rw [rootTimeBlock_eq] at h1 h2 ⊢
  have hfl : ((⌊t⌋ : ℤ) : ℝ) ≤ t := Int.floor_le t
  have hcl : t < ((⌊t⌋ + 1 : ℤ) : ℝ) := by
    push_cast
    exact Int.lt_floor_add_one t
  exact Set.mem_Ico.2 ⟨le_trans (Set.mem_Ico.1 h1).1 hfl, lt_trans hcl (Set.mem_Ico.1 h2).2⟩

/-! ### The invariant version -/

/-- **The invariant version of the chain limit**: the upper limit, along all levels, of the root
block averages of `g`. -/
noncomputable def chainLimsup (g : ℝ → ℝ) (D : Grid) : ℝ :=
  limsup (fun k : ℤ => setAvg (rootTimeBlock D k) g) atTop

/-- Where the chain converges along the nonnegative levels, the invariant version is the
limit. -/
theorem chainLimsup_eq_of_tendsto_nat {g : ℝ → ℝ} {D : Grid} {c : ℝ}
    (h : Tendsto (fun n : ℕ => setAvg (rootTimeBlock D (n : ℤ)) g) atTop (𝓝 c)) :
    chainLimsup g D = c := by
  have hz : Tendsto (fun k : ℤ => setAvg (rootTimeBlock D k) g) atTop (𝓝 c) := by
    rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
    exact h
  exact hz.limsup_eq

/-- Re-rooting the grid at the time `u 0`. -/
theorem rootTimeBlock_translate (D : Grid) (u : Plane) (k : ℤ) :
    rootTimeBlock (translate u D) k = (fun x : ℝ => x + u 0) ⁻¹' timeBlockAt D k (u 0) := by
  have h := timeBlockAt_translate D u k (u 0)
  rw [sub_self] at h
  exact h

/-- Block averages are invariant under translating the block and the density together. -/
theorem setAvg_preimage_add (J : Set ℝ) (g : ℝ → ℝ) (t : ℝ) :
    setAvg ((fun x : ℝ => x + t) ⁻¹' J) (fun s : ℝ => g (s + t)) = setAvg J g := by
  have hvol : volume ((fun x : ℝ => x + t) ⁻¹' J) = volume J :=
    measure_preimage_add_right volume t J
  have hint : (∫ s in (fun x : ℝ => x + t) ⁻¹' J, g (s + t)) = ∫ s in J, g s :=
    (measurePreserving_add_right volume t).setIntegral_preimage_emb
      (measurableEmbedding_addRight t) g J
  rw [setAvg, setAvg, hvol, hint]

/-- **Re-rooting invariance of the invariant version**, for every grid whose root chain
exhausts the time axis. -/
theorem chainLimsup_translate {D : Grid} (hD : RootExhausts D) (u : Plane) (g : ℝ → ℝ) :
    chainLimsup (fun s : ℝ => g (s + u 0)) (translate u D) = chainLimsup g D := by
  refine limsup_congr ?_
  filter_upwards [eventually_mem_rootTimeBlock hD (u 0)] with k hk
  have h1 : timeBlockAt D k (u 0) = rootTimeBlock D k := timeBlockAt_eq_of_mem hk
  rw [rootTimeBlock_translate, setAvg_preimage_add, h1]

/-- The root blocks of a dilated grid, at the shifted levels. -/
theorem rootTimeBlock_dilate {a : ℝ} (ha : 0 < a) (D : Grid) (k : ℤ) :
    rootTimeBlock (dilate a ha D) (k + levelShift a D)
      = Set.Ico (a * D.origin k 0) (a * D.origin k 0 + a * side D k) := by
  have hL : k + levelShift a D - levelShift a D = k := by ring
  have horig : (dilate a ha D).origin (k + levelShift a D) 0 = a * D.origin k 0 := by
    show dilatedOrigin a D (k + levelShift a D) 0 = a * D.origin k 0
    rw [dilatedOrigin, hL]
  have hside : side (dilate a ha D) (k + levelShift a D) = a * side D k := by
    rw [side_dilate ha, hL]
  rw [rootTimeBlock_eq, horig, hside]

/-- Block averages are invariant under dilating the block and the density together. -/
theorem setAvg_Ico_mul {a : ℝ} (ha : 0 < a) (x σ : ℝ) (hσ : 0 < σ) (g : ℝ → ℝ) :
    setAvg (Set.Ico (a * x) (a * x + a * σ)) (fun s : ℝ => g (s / a))
      = setAvg (Set.Ico x (x + σ)) g := by
  have haσ : 0 < a * σ := mul_pos ha hσ
  have hvol1 : (volume (Set.Ico (a * x) (a * x + a * σ))).toReal = a * σ := by
    rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hvol2 : (volume (Set.Ico x (x + σ))).toReal = σ := by
    rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hb1 : a * x / a = x := mul_div_cancel_left₀ x ha.ne'
  have hb2 : (a * x + a * σ) / a = x + σ := by
    rw [← mul_add, mul_div_cancel_left₀ _ ha.ne']
  have hint1 : (∫ s in Set.Ico (a * x) (a * x + a * σ), g (s / a))
      = a * ∫ s in Set.Ico x (x + σ), g s := by
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_div g ha.ne', hb1, hb2, smul_eq_mul,
      intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      ← integral_Ico_eq_integral_Ioo]
  rw [setAvg, setAvg, hvol1, hvol2, hint1]
  have hkey : (a * σ)⁻¹ * (a * ∫ s in Set.Ico x (x + σ), g s)
      = (a⁻¹ * a) * (σ⁻¹ * ∫ s in Set.Ico x (x + σ), g s) := by ring
  rw [hkey, inv_mul_cancel₀ ha.ne', one_mul]

/-- **Scaling invariance of the invariant version**, for every grid: dilating the grid by `a`
and the time axis of the density by `a` reindexes the root chain by `levelShift a D`, which does
not change an upper limit along `ℤ`. -/
theorem chainLimsup_dilate {a : ℝ} (ha : 0 < a) (D : Grid) (g : ℝ → ℝ) :
    chainLimsup (fun s : ℝ => g (s / a)) (dilate a ha D) = chainLimsup g D := by
  have hshift : (fun k : ℤ =>
      setAvg (rootTimeBlock (dilate a ha D) (k + levelShift a D)) (fun s : ℝ => g (s / a)))
      = fun k : ℤ => setAvg (rootTimeBlock D k) g := by
    funext k
    rw [rootTimeBlock_dilate ha D k, rootTimeBlock_eq]
    exact setAvg_Ico_mul ha (D.origin k 0) (side D k) (side_pos D k) g
  have hcomp : chainLimsup (fun s : ℝ => g (s / a)) (dilate a ha D)
      = limsup (fun k : ℤ =>
          setAvg (rootTimeBlock (dilate a ha D) (k + levelShift a D))
            (fun s : ℝ => g (s / a))) atTop := by
    have h := limsup_comp
      (fun k : ℤ => setAvg (rootTimeBlock (dilate a ha D) k) (fun s : ℝ => g (s / a)))
      (fun k : ℤ => k + levelShift a D) atTop
    rw [map_add_atTop_eq] at h
    exact h.symm
  rw [hcomp, hshift, chainLimsup]

/-! ### Measurability -/

/-- The root block averages of a jointly measurable density are jointly measurable. -/
theorem measurable_setAvg_rootTimeBlock {Ω : Type*} [MeasurableSpace Ω] {dens : Ω → ℝ → ℝ}
    (hdens : Measurable fun q : Ω × ℝ => dens q.1 q.2) (k : ℤ) :
    Measurable fun p : Ω × Grid => setAvg (rootTimeBlock p.2 k) (dens p.1) := by
  have hside : Measurable fun p : Ω × Grid => side p.2 k :=
    (ReflectedGMS.MeasurableEndpointTransport.measurable_gridSide k).comp measurable_snd
  have horig : Measurable fun p : Ω × Grid => p.2.origin k 0 :=
    (ReflectedGMS.MeasurableEndpointTransport.measurable_gridOrigin k 0).comp measurable_snd
  have hset : MeasurableSet {q : (Ω × Grid) × ℝ | q.2 ∈ rootTimeBlock q.1.2 k} := by
    have heq : {q : (Ω × Grid) × ℝ | q.2 ∈ rootTimeBlock q.1.2 k}
        = {q : (Ω × Grid) × ℝ | q.1.2.origin k 0 ≤ q.2} ∩
          {q : (Ω × Grid) × ℝ | q.2 < q.1.2.origin k 0 + side q.1.2 k} := by
      ext q
      simp only [rootTimeBlock_eq, Set.mem_Ico, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [heq]
    exact (measurableSet_le (horig.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd ((horig.add hside).comp measurable_fst))
  have hind : Measurable fun q : (Ω × Grid) × ℝ =>
      {q : (Ω × Grid) × ℝ | q.2 ∈ rootTimeBlock q.1.2 k}.indicator
        (fun q : (Ω × Grid) × ℝ => dens q.1.1 q.2) q :=
    (hdens.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator hset
  have hint : Measurable fun p : Ω × Grid => ∫ t : ℝ,
      {q : (Ω × Grid) × ℝ | q.2 ∈ rootTimeBlock q.1.2 k}.indicator
        (fun q : (Ω × Grid) × ℝ => dens q.1.1 q.2) (p, t) :=
    (hind.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have heq : (fun p : Ω × Grid => setAvg (rootTimeBlock p.2 k) (dens p.1))
      = fun p : Ω × Grid => (side p.2 k)⁻¹ * ∫ t : ℝ,
          {q : (Ω × Grid) × ℝ | q.2 ∈ rootTimeBlock q.1.2 k}.indicator
            (fun q : (Ω × Grid) × ℝ => dens q.1.1 q.2) (p, t) := by
    funext p
    have hpt : ∀ t : ℝ, (rootTimeBlock p.2 k).indicator (dens p.1) t
        = {q : (Ω × Grid) × ℝ | q.2 ∈ rootTimeBlock q.1.2 k}.indicator
            (fun q : (Ω × Grid) × ℝ => dens q.1.1 q.2) (p, t) := by
      intro t
      by_cases ht : t ∈ rootTimeBlock p.2 k
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem
          (show ((p, t) : (Ω × Grid) × ℝ) ∈ {q : (Ω × Grid) × ℝ | q.2 ∈ rootTimeBlock q.1.2 k}
            from ht)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem
          (show ((p, t) : (Ω × Grid) × ℝ) ∉ {q : (Ω × Grid) × ℝ | q.2 ∈ rootTimeBlock q.1.2 k}
            from ht)]
    rw [setAvg, volume_rootTimeBlock, ENNReal.toReal_ofReal (side_pos p.2 k).le,
      ← integral_indicator (measurableSet_rootTimeBlock p.2 k)]
    simp only [hpt]
  rw [heq]
  exact hside.inv.mul hint

/-- **The invariant version is jointly measurable.** -/
theorem measurable_chainLimsup {Ω : Type*} [MeasurableSpace Ω] {dens : Ω → ℝ → ℝ}
    (hdens : Measurable fun q : Ω × ℝ => dens q.1 q.2) :
    Measurable fun p : Ω × Grid => chainLimsup (dens p.1) p.2 :=
  Measurable.limsup' (fun k : ℤ => measurable_setAvg_rootTimeBlock hdens k)
    atTop_countable_basis fun _ => Set.to_countable _

/-! ### `GridAveragedConstant` for a root chain system -/

/-- The time vector `(t, 0)`: translating the marked grid by it re-roots its time axis at `t`. -/
noncomputable def timeVec (t : ℝ) : Plane :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)

theorem timeVec_zero (t : ℝ) : timeVec t 0 = t := by
  show (if (0 : Fin 2) = 0 then t else 0) = t
  rw [if_pos rfl]

/-- The parabolic scaling of the time grid by the factor `C`: dilation of the time axis by
`C²` (the identity for `C ≤ 0`, where it is never used). -/
noncomputable def gridScale (C : ℝ) (D : Grid) : Grid :=
  if h : 0 < C then dilate (C ^ 2) (pow_pos h 2) D else D

theorem gridScale_of_pos {C : ℝ} (hC : 0 < C) (D : Grid) :
    gridScale C D = dilate (C ^ 2) (pow_pos hC 2) D := by
  rw [gridScale, dif_pos hC]

/-! ### Composition with the bracket lane -/

end ReflectedGMS.GridAveragedInvariantVersion
