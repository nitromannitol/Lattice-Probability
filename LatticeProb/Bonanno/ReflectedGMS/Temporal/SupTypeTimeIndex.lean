/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.SupTypeTimeIndex at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowSpaceBlockSystem

/-!
# The sup-type time-block index of Section 17 (manuscript (17.3))

Section 17 of the singular-set manuscript (`work/singular/manuscript-text.txt:2062-2086`) selects
its time blocks through the index

```
  D(J) = sup{|I| : I ∩ J ≠ ∅},   α(J) = sup_{k ≥ 0} D(J^(k)) / |J^(k)|,   β(J) = α(J)⁻¹,
  κ(J) = Σ_{k ≥ 0} 4^{-k} β(J^(k)),
```

where `I` ranges over the holding intervals of the label path and `J^(k)` is the `k`-th dyadic
ancestor of `J`; the block through `s` at parameter `m` is the largest dyadic interval `J ∋ s` with
`κ(J) ≤ m`.  "This is the one-dimensional version of the diameter index in Section 3, not a count of
holding intervals."  The criterion is an upper bound on a **supremum** of holding lengths, so a
single nonvertex time never destroys the blocks through it; this is what the infimum criterion
`FlowSpaceBlockSystem.Good` of the earlier construction could not do (`SpatialScaleSingular`, §6).

This module is carrier-generic.  The holding structure enters through a function
`hold : Ω → ℝ → ℝ≥0∞` (the length of the holding interval through a time, `0` at a nonvertex time)
and the axioms `HoldingData` on an invariant gate `G` (the manuscript's invariant domain, page 40:
"holding intervals have positive finite length and cover almost every time, the maximal interval
length meeting each bounded window is finite, and (17.2)").

* `blockSup hold ω J` is `D(J)`, read through the rational times of `J` (so that it is measurable);
  on the gate it dominates the holding length of every time of `J` (`le_blockSup_of_mem`).
* `ratio`, `alpha`, `beta`, `kappa` are `D(J)/|J|`, `α`, `β`, `κ` for `J = timeBlockAt D k s`.
* `kappa_eq`, `kappa_mono`: `κ(J) = β(J) + κ(J^(1))/4` and `κ` is nondecreasing along ancestors
  (`4/3 β(J) < κ(J)` is `beta_le_kappa_succ`); `kappa_le_two_mul_beta`: `κ(J) ≤ 2 β(J)`.
* `kappa_congr_of_mem`: the index depends on `s` only through the block `J`.
* `blockSup_shift`, `blockSup_scale`, `kappa_shift`, `kappa_scale`: covariance on the gate.
* `measurable_kappa`, `measurableSet_goodK_on`: joint measurability.
* `exists_goodK`: at a vertex time every parameter admits a good level ("down a chain through a
  holding interval `I_s`, `κ(J) ≤ 2|J|/|I_s| → 0`"); `exists_not_goodK`: on the gate no level
  beyond a certain one is good ("along ancestors `κ → ∞`", from (17.2)).

Nothing here is probabilistic and nothing here mentions the walk.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal NNReal

namespace ReflectedGMS.SupTypeTimeIndex

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridDilationInvariance
open ReflectedGMS.Temporal.ActualDyadicTemporalBlocks
open ReflectedGMS.FlowSpaceBlockSystem ReflectedGMS.GridAveragedInvariantVersion

variable {Ω : Type*}

/-! ## 1. The window supremum and the holding data -/

/-- The supremal holding length over the rational times of the window `[-T, T)`. -/
noncomputable def windowSup (hold : Ω → ℝ → ℝ≥0∞) (ω : Ω) (T : ℝ) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : (q : ℝ) ∈ Set.Ico (-T) T), hold ω q

/-- **The holding data on an invariant gate**: the holding-length function is covariant under
the flow and the parabolic scaling at every point, jointly measurable, and on the gate `G` the
holding intervals are read at rational times, the window supremum is finite and sublinear
((17.2)), and the nonvertex times are Lebesgue-null. -/
structure HoldingData [MeasurableSpace Ω] (G : Set Ω) (θΩ SΩ : ℝ → Ω → Ω)
    (hold : Ω → ℝ → ℝ≥0∞) : Prop where
  measurableSet_gate : MeasurableSet G
  flow_mem : ∀ (r : ℝ) (ω : Ω), θΩ r ω ∈ G ↔ ω ∈ G
  scale_mem : ∀ C : ℝ, 0 < C → ∀ ω : Ω, SΩ C ω ∈ G ↔ ω ∈ G
  shift : ∀ (r : ℝ) (ω : Ω) (s : ℝ), hold (θΩ r ω) s = hold ω (s + r)
  scale : ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s : ℝ),
    hold (SΩ C ω) (C ^ 2 * s) = ENNReal.ofReal (C ^ 2) * hold ω s
  measurable : Measurable fun q : Ω × ℝ => hold q.1 q.2
  rat : ∀ ω ∈ G, ∀ (c d u : ℝ), u ∈ Set.Ico c d → hold ω u ≠ 0 →
    ∃ q : ℚ, (q : ℝ) ∈ Set.Ico c d ∧ hold ω q = hold ω u
  window_lt_top : ∀ ω ∈ G, ∀ T : ℝ, windowSup hold ω T < ∞
  window_sublinear : ∀ ω ∈ G, ∀ ε : ℝ, 0 < ε →
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → windowSup hold ω T ≤ ENNReal.ofReal (ε * T)
  null_zero : ∀ ω ∈ G, volume {s : ℝ | hold ω s = 0} = 0

/-! ## 2. `D(J)` -/

/-- `D(J)`: the supremal holding length over the rational times of `J`. -/
noncomputable def blockSup (hold : Ω → ℝ → ℝ≥0∞) (ω : Ω) (J : Set ℝ) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : (q : ℝ) ∈ J), hold ω q

variable (hold : Ω → ℝ → ℝ≥0∞)

theorem le_blockSup {ω : Ω} {J : Set ℝ} {q : ℚ} (hq : (q : ℝ) ∈ J) :
    hold ω q ≤ blockSup hold ω J :=
  le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ J) => hold ω q) q hq

theorem blockSup_le {ω : Ω} {J : Set ℝ} {c : ℝ≥0∞} (h : ∀ q : ℚ, (q : ℝ) ∈ J → hold ω q ≤ c) :
    blockSup hold ω J ≤ c :=
  iSup₂_le h

theorem blockSup_mono (ω : Ω) {J J' : Set ℝ} (h : J ⊆ J') :
    blockSup hold ω J ≤ blockSup hold ω J' :=
  blockSup_le hold fun _ hq => le_blockSup hold (h hq)

theorem windowSup_eq_blockSup (ω : Ω) (T : ℝ) :
    windowSup hold ω T = blockSup hold ω (Set.Ico (-T) T) := rfl

section Gate

variable [MeasurableSpace Ω] {G : Set Ω} {θΩ SΩ : ℝ → Ω → Ω}

/-- On the gate `D(J)` dominates the holding length of every time of the half-open `J`. -/
theorem le_blockSup_of_mem (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) {c d u : ℝ}
    (hu : u ∈ Set.Ico c d) : hold ω u ≤ blockSup hold ω (Set.Ico c d) := by
  by_cases h0 : hold ω u = 0
  · rw [h0]
    exact zero_le
  · obtain ⟨q, hq, hqu⟩ := hd.rat ω hω c d u hu h0
    rw [← hqu]
    exact le_blockSup hold hq

theorem le_blockSup_timeBlockAt (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G)
    {D : Grid} {k : ℤ} {s u : ℝ} (hu : u ∈ timeBlockAt D k s) :
    hold ω u ≤ blockSup hold ω (timeBlockAt D k s) :=
  le_blockSup_of_mem hold hd hω hu

/-- On the gate every holding length is finite. -/
theorem hold_lt_top (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (s : ℝ) :
    hold ω s < ∞ := by
  obtain ⟨n, hn⟩ := exists_nat_gt |s|
  have hs : s ∈ Set.Ico (-(n : ℝ)) n :=
    ⟨by linarith [neg_abs_le s], lt_of_le_of_lt (le_abs_self s) hn⟩
  exact lt_of_le_of_lt (le_blockSup_of_mem hold hd hω hs) (hd.window_lt_top ω hω n)

/-- **Flow covariance of `D`** on the gate. -/
theorem blockSup_shift (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (r c d : ℝ) :
    blockSup hold (θΩ r ω) (Set.Ico (c - r) (d - r)) = blockSup hold ω (Set.Ico c d) := by
  have hω' : θΩ r ω ∈ G := (hd.flow_mem r ω).2 hω
  refine le_antisymm (blockSup_le hold fun q hq => ?_) (blockSup_le hold fun q hq => ?_)
  · rw [hd.shift]
    exact le_blockSup_of_mem hold hd hω ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · have h := le_blockSup_of_mem hold hd hω' (u := (q : ℝ) - r) (c := c - r) (d := d - r)
      ⟨by linarith [hq.1], by linarith [hq.2]⟩
    rwa [hd.shift, sub_add_cancel] at h

/-- **Parabolic covariance of `D`** on the gate. -/
theorem blockSup_scale (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) {C : ℝ} (hC : 0 < C)
    (c d : ℝ) :
    blockSup hold (SΩ C ω) (Set.Ico (C ^ 2 * c) (C ^ 2 * d))
      = ENNReal.ofReal (C ^ 2) * blockSup hold ω (Set.Ico c d) := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  have hω' : SΩ C ω ∈ G := (hd.scale_mem C hC ω).2 hω
  refine le_antisymm (blockSup_le hold fun q hq => ?_) ?_
  · have hv : (q : ℝ) / C ^ 2 ∈ Set.Ico c d :=
      ⟨by
        rw [le_div_iff₀ hC2]
        linarith [hq.1], by
        rw [div_lt_iff₀ hC2]
        linarith [hq.2]⟩
    have h1 : hold (SΩ C ω) q = ENNReal.ofReal (C ^ 2) * hold ω ((q : ℝ) / C ^ 2) := by
      rw [← hd.scale C hC ω, mul_div_cancel₀ _ hC2.ne']
    rw [h1]
    exact mul_le_mul_of_nonneg_left (le_blockSup_of_mem hold hd hω hv) zero_le
  · unfold blockSup
    rw [ENNReal.mul_iSup]
    refine iSup_le fun q => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hq => ?_
    rw [← hd.scale C hC ω]
    exact le_blockSup_of_mem hold hd hω'
      ⟨mul_le_mul_of_nonneg_left hq.1 hC2.le, mul_lt_mul_of_pos_left hq.2 hC2⟩

end Gate

/-! ## 3. The index `α`, `β`, `κ` -/

/-- `D(J)/|J|` for the level-`k` block through `s`. -/
noncomputable def ratio (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) : ℝ≥0∞ :=
  blockSup hold ω (timeBlockAt D k s) / ENNReal.ofReal (side D k)

/-- `α(J) = sup_{j ≥ 0} D(J^(j))/|J^(j)|`. -/
noncomputable def alpha (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ j : ℕ, ratio hold ω D (k + j) s

/-- `β(J) = α(J)⁻¹`. -/
noncomputable def beta (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) : ℝ≥0∞ :=
  (alpha hold ω D k s)⁻¹

/-- `κ(J) = Σ_{j ≥ 0} 4^{-j} β(J^(j))`. -/
noncomputable def kappa (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, (4⁻¹ : ℝ≥0∞) ^ j * beta hold ω D (k + j) s

/-- **The block criterion**: the level-`k` block through `s` is good at the rational parameter
`q` when `κ(J) ≤ 2^q`. -/
def GoodK (q : ℚ) (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) : Prop :=
  kappa hold ω D k s ≤ ENNReal.ofReal ((2 : ℝ) ^ (q : ℝ))

/-! ### Congruence on blocks -/

theorem ratio_congr_of_mem {ω : Ω} {D : Grid} {k l : ℤ} (hkl : k ≤ l) {s t : ℝ}
    (ht : t ∈ timeBlockAt D k s) : ratio hold ω D l t = ratio hold ω D l s := by
  unfold ratio
  rw [timeBlockAt_eq_of_mem_of_le D hkl ht]

theorem alpha_congr_of_mem {ω : Ω} {D : Grid} {k l : ℤ} (hkl : k ≤ l) {s t : ℝ}
    (ht : t ∈ timeBlockAt D k s) : alpha hold ω D l t = alpha hold ω D l s := by
  unfold alpha
  exact iSup_congr fun j => ratio_congr_of_mem hold (by omega) ht

theorem beta_congr_of_mem {ω : Ω} {D : Grid} {k l : ℤ} (hkl : k ≤ l) {s t : ℝ}
    (ht : t ∈ timeBlockAt D k s) : beta hold ω D l t = beta hold ω D l s := by
  unfold beta
  rw [alpha_congr_of_mem hold hkl ht]

/-- **The index depends on `s` only through the block.** -/
theorem kappa_congr_of_mem {ω : Ω} {D : Grid} {k l : ℤ} (hkl : k ≤ l) {s t : ℝ}
    (ht : t ∈ timeBlockAt D k s) : kappa hold ω D l t = kappa hold ω D l s := by
  unfold kappa
  exact tsum_congr fun j => by rw [beta_congr_of_mem hold (by omega) ht]

theorem goodK_iff_of_mem {q : ℚ} {ω : Ω} {D : Grid} {k l : ℤ} (hkl : k ≤ l) {s t : ℝ}
    (ht : t ∈ timeBlockAt D k s) : GoodK hold q ω D l t ↔ GoodK hold q ω D l s := by
  unfold GoodK
  rw [kappa_congr_of_mem hold hkl ht]

/-! ### Monotonicity along ancestors -/

theorem ratio_le_alpha (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) (j : ℕ) :
    ratio hold ω D (k + j) s ≤ alpha hold ω D k s :=
  le_iSup (fun j : ℕ => ratio hold ω D (k + j) s) j

theorem alpha_succ_le (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    alpha hold ω D (k + 1) s ≤ alpha hold ω D k s := by
  refine iSup_le fun j => ?_
  have h := ratio_le_alpha hold ω D k s (j + 1)
  rwa [show k + ((j + 1 : ℕ) : ℤ) = k + 1 + (j : ℤ) by push_cast; ring] at h

theorem alpha_antitone (ω : Ω) (D : Grid) (s : ℝ) {k l : ℤ} (hkl : k ≤ l) :
    alpha hold ω D l s ≤ alpha hold ω D k s := by
  induction l, hkl using Int.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact (alpha_succ_le hold ω D m s).trans ih

theorem beta_mono (ω : Ω) (D : Grid) (s : ℝ) {k l : ℤ} (hkl : k ≤ l) :
    beta hold ω D k s ≤ beta hold ω D l s :=
  ENNReal.inv_le_inv.2 (alpha_antitone hold ω D s hkl)

/-- `κ(J) = β(J) + κ(J^(1))/4`. -/
theorem kappa_eq (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    kappa hold ω D k s = beta hold ω D k s + 4⁻¹ * kappa hold ω D (k + 1) s := by
  unfold kappa
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, one_mul, Nat.cast_zero, add_zero]
  congr 1
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [pow_succ, show k + ((j + 1 : ℕ) : ℤ) = k + 1 + (j : ℤ) by push_cast; ring]
  ring

/-! ### The geometric constants -/

theorem one_lt_four : (1 : ℝ≥0∞) < 4 := by
  have h : (2 : ℝ≥0∞) + 2 = 4 := by norm_num
  rw [← h]
  exact lt_of_lt_of_le ENNReal.one_lt_two le_self_add

theorem quarter_lt_one : (4⁻¹ : ℝ≥0∞) < 1 := by
  have h := ENNReal.inv_lt_inv.2 one_lt_four
  rwa [inv_one] at h

theorem one_sub_quarter_ne_zero : (1 : ℝ≥0∞) - 4⁻¹ ≠ 0 :=
  (tsub_pos_iff_lt.2 quarter_lt_one).ne'

theorem one_sub_quarter_ne_top : (1 : ℝ≥0∞) - 4⁻¹ ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

/-- `Σ_j 4^{-j}`. -/
noncomputable def geomQuarter : ℝ≥0∞ := ∑' j : ℕ, (4⁻¹ : ℝ≥0∞) ^ j

theorem geomQuarter_eq : geomQuarter = (1 - 4⁻¹)⁻¹ := ENNReal.tsum_geometric _

theorem geomQuarter_ne_top : geomQuarter ≠ ∞ := by
  rw [geomQuarter_eq]
  exact ENNReal.inv_ne_top.2 one_sub_quarter_ne_zero

theorem geomQuarter_ne_zero : geomQuarter ≠ 0 := by
  rw [geomQuarter_eq]
  exact ENNReal.inv_ne_zero.2 one_sub_quarter_ne_top

theorem one_le_geomQuarter : 1 ≤ geomQuarter := by
  have h := ENNReal.le_tsum (f := fun j : ℕ => (4⁻¹ : ℝ≥0∞) ^ j) 0
  unfold geomQuarter
  simpa only [pow_zero] using h

theorem inv_geomQuarter : geomQuarter⁻¹ = 1 - 4⁻¹ := by
  rw [geomQuarter_eq, inv_inv]

theorem quarter_mul_two : (4⁻¹ : ℝ≥0∞) * 2 = 2⁻¹ := by
  have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
  rw [h4, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_assoc,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-! ### `κ` is nondecreasing along ancestors, and `κ ≤ 2β` -/

theorem geomQuarter_mul_beta_le_kappa (ω : Ω) (D : Grid) (s : ℝ) {k l : ℤ} (hkl : k ≤ l) :
    geomQuarter * beta hold ω D k s ≤ kappa hold ω D l s := by
  unfold kappa geomQuarter
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun j => ?_
  exact mul_le_mul_of_nonneg_left (beta_mono hold ω D s (by omega)) zero_le

/-- `β(J) ≤ (3/4) κ(J^(1))`, i.e. `(4/3) β(J) ≤ κ(J^(1))`. -/
theorem beta_le_kappa_succ (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    beta hold ω D k s ≤ (1 - 4⁻¹) * kappa hold ω D (k + 1) s := by
  have h := geomQuarter_mul_beta_le_kappa hold ω D s (show k ≤ k + 1 by omega)
  have h2 : geomQuarter⁻¹ * (geomQuarter * beta hold ω D k s)
      ≤ geomQuarter⁻¹ * kappa hold ω D (k + 1) s :=
    mul_le_mul_of_nonneg_left h zero_le
  rwa [← mul_assoc, ENNReal.inv_mul_cancel geomQuarter_ne_zero geomQuarter_ne_top, one_mul,
    inv_geomQuarter] at h2

theorem kappa_le_succ (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    kappa hold ω D k s ≤ kappa hold ω D (k + 1) s := by
  rw [kappa_eq hold ω D k s]
  calc beta hold ω D k s + 4⁻¹ * kappa hold ω D (k + 1) s
      ≤ (1 - 4⁻¹) * kappa hold ω D (k + 1) s + 4⁻¹ * kappa hold ω D (k + 1) s :=
        add_le_add (beta_le_kappa_succ hold ω D k s) le_rfl
    _ = kappa hold ω D (k + 1) s := by
        rw [← add_mul, tsub_add_cancel_of_le quarter_lt_one.le, one_mul]

/-- **`κ` is nondecreasing along ancestors.** -/
theorem kappa_mono (ω : Ω) (D : Grid) (s : ℝ) {k l : ℤ} (hkl : k ≤ l) :
    kappa hold ω D k s ≤ kappa hold ω D l s := by
  induction l, hkl using Int.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (kappa_le_succ hold ω D m s)

/-- Goodness passes to finer levels. -/
theorem GoodK.mono_level {q : ℚ} {ω : Ω} {D : Grid} {k l : ℤ} {s : ℝ} (hkl : k ≤ l)
    (h : GoodK hold q ω D l s) : GoodK hold q ω D k s :=
  (kappa_mono hold ω D s hkl).trans h

/-- Goodness passes to larger parameters. -/
theorem GoodK.mono_q {q q' : ℚ} (hq : q ≤ q') {ω : Ω} {D : Grid} {k : ℤ} {s : ℝ}
    (h : GoodK hold q ω D k s) : GoodK hold q' ω D k s :=
  h.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hq)))

theorem ratio_le_two_mul_succ (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    ratio hold ω D k s ≤ 2 * ratio hold ω D (k + 1) s := by
  unfold ratio
  have h2 : ENNReal.ofReal (side D (k + 1)) = 2 * ENNReal.ofReal (side D k) := by
    rw [side_succ, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [h2, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ two_ne_zero ENNReal.ofNat_ne_top]
  exact ENNReal.div_le_div_right (blockSup_mono hold ω (timeBlockAt_subset_succ D k s)) _

theorem alpha_le_two_mul_succ (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    alpha hold ω D k s ≤ 2 * alpha hold ω D (k + 1) s := by
  refine iSup_le fun i => ?_
  calc ratio hold ω D (k + i) s ≤ 2 * ratio hold ω D (k + i + 1) s :=
        ratio_le_two_mul_succ hold ω D (k + i) s
    _ ≤ 2 * alpha hold ω D (k + 1) s := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        have h := ratio_le_alpha hold ω D (k + 1) s i
        rwa [show k + 1 + (i : ℤ) = k + i + 1 by ring] at h

theorem beta_succ_le (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    beta hold ω D (k + 1) s ≤ 2 * beta hold ω D k s := by
  unfold beta
  have h := ENNReal.inv_le_inv.2 (alpha_le_two_mul_succ hold ω D k s)
  rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)] at h
  have h2 := mul_le_mul_of_nonneg_left h (zero_le : (0 : ℝ≥0∞) ≤ 2)
  rwa [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul] at h2

theorem beta_add_le (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) (j : ℕ) :
    beta hold ω D (k + j) s ≤ 2 ^ j * beta hold ω D k s := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc beta hold ω D (k + ((j + 1 : ℕ) : ℤ)) s = beta hold ω D (k + j + 1) s := by
          rw [show k + ((j + 1 : ℕ) : ℤ) = k + j + 1 by push_cast; ring]
      _ ≤ 2 * beta hold ω D (k + j) s := beta_succ_le hold ω D (k + j) s
      _ ≤ 2 * (2 ^ j * beta hold ω D k s) := mul_le_mul_of_nonneg_left ih zero_le
      _ = 2 ^ (j + 1) * beta hold ω D k s := by
          rw [pow_succ]
          ring

/-- **`κ(J) ≤ 2 β(J)`.** -/
theorem kappa_le_two_mul_beta (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    kappa hold ω D k s ≤ 2 * beta hold ω D k s := by
  unfold kappa
  calc ∑' j : ℕ, (4⁻¹ : ℝ≥0∞) ^ j * beta hold ω D (k + j) s
      ≤ ∑' j : ℕ, (4⁻¹ : ℝ≥0∞) ^ j * (2 ^ j * beta hold ω D k s) :=
        ENNReal.tsum_le_tsum fun j =>
          mul_le_mul_of_nonneg_left (beta_add_le hold ω D k s j) zero_le
    _ = (∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j) * beta hold ω D k s := by
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun j => ?_
        rw [← mul_assoc, ← mul_pow, quarter_mul_two]
    _ = 2 * beta hold ω D k s := by
        rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

/-! ## 4. Covariance of the index on the gate -/

section Gate

variable [MeasurableSpace Ω] {G : Set Ω} {θΩ SΩ : ℝ → Ω → Ω}

theorem blockSup_timeBlockAt_shift (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (r : ℝ)
    (D : Grid) (k : ℤ) (s : ℝ) :
    blockSup hold (θΩ r ω) (timeBlockAt (translate (timeVec r) D) k s)
      = blockSup hold ω (timeBlockAt D k (s + r)) := by
  have h := blockSup_shift hold hd hω r (timeLowerAt D k (s + r))
    (timeLowerAt D k (s + r) + side D k)
  have hblk : timeBlockAt (translate (timeVec r) D) k s
      = Set.Ico (timeLowerAt D k (s + r) - r) (timeLowerAt D k (s + r) + side D k - r) := by
    rw [timeBlockAt_translate_timeVec]
    ext x
    simp only [timeBlockAt, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  rw [hblk, h]
  rfl

theorem ratio_shift (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (r : ℝ) (D : Grid)
    (k : ℤ) (s : ℝ) :
    ratio hold (θΩ r ω) (translate (timeVec r) D) k s = ratio hold ω D k (s + r) := by
  unfold ratio
  rw [blockSup_timeBlockAt_shift hold hd hω, side_translate]

theorem kappa_shift (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (r : ℝ) (D : Grid)
    (k : ℤ) (s : ℝ) :
    kappa hold (θΩ r ω) (translate (timeVec r) D) k s = kappa hold ω D k (s + r) := by
  unfold kappa beta alpha
  simp only [ratio_shift hold hd hω]

theorem goodK_shift (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (q : ℚ) (r : ℝ)
    (D : Grid) (k : ℤ) (s : ℝ) :
    GoodK hold q (θΩ r ω) (translate (timeVec r) D) k s ↔ GoodK hold q ω D k (s + r) := by
  unfold GoodK
  rw [kappa_shift hold hd hω]

theorem blockSup_timeBlockAt_scale (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) {C : ℝ}
    (hC : 0 < C) (D : Grid) (k : ℤ) (s : ℝ) :
    blockSup hold (SΩ C ω)
        (timeBlockAt (dilate (C ^ 2) (pow_pos hC 2) D) (k + levelShift (C ^ 2) D) (C ^ 2 * s))
      = ENNReal.ofReal (C ^ 2) * blockSup hold ω (timeBlockAt D k s) := by
  rw [timeBlockAt_dilate (pow_pos hC 2)]
  have himg : (fun x : ℝ => C ^ 2 * x) '' timeBlockAt D k s
      = Set.Ico (C ^ 2 * timeLowerAt D k s) (C ^ 2 * (timeLowerAt D k s + side D k)) := by
    unfold timeBlockAt
    exact Set.image_mul_left_Ico (pow_pos hC 2) _ _
  rw [himg, blockSup_scale hold hd hω hC]
  rfl

theorem ratio_scale (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) {C : ℝ} (hC : 0 < C)
    (D : Grid) (k : ℤ) (s : ℝ) :
    ratio hold (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) (k + levelShift (C ^ 2) D)
        (C ^ 2 * s)
      = ratio hold ω D k s := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  have hc0 : ENNReal.ofReal (C ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hC2).ne'
  unfold ratio
  rw [blockSup_timeBlockAt_scale hold hd hω hC, side_dilate hC2, add_sub_cancel_right,
    ENNReal.ofReal_mul hC2.le, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]

theorem kappa_scale (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) {C : ℝ} (hC : 0 < C)
    (D : Grid) (k : ℤ) (s : ℝ) :
    kappa hold (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) (k + levelShift (C ^ 2) D)
        (C ^ 2 * s)
      = kappa hold ω D k s := by
  unfold kappa beta alpha
  refine tsum_congr fun j => ?_
  congr 2
  refine iSup_congr fun i => ?_
  rw [show k + levelShift (C ^ 2) D + (j : ℤ) + (i : ℤ)
      = (k + (j : ℤ) + (i : ℤ)) + levelShift (C ^ 2) D by ring]
  exact ratio_scale hold hd hω hC D (k + (j : ℤ) + (i : ℤ)) s

theorem goodK_scale (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (q : ℚ) {C : ℝ}
    (hC : 0 < C) (D : Grid) (k : ℤ) (s : ℝ) :
    GoodK hold q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) (k + levelShift (C ^ 2) D)
        (C ^ 2 * s)
      ↔ GoodK hold q ω D k s := by
  unfold GoodK
  rw [kappa_scale hold hd hω hC]

/-! ## 5. Measurability -/

theorem measurable_blockSup_timeBlockAt (hd : HoldingData G θΩ SΩ hold) (k : ℤ) :
    Measurable fun y : (Ω × Grid) × ℝ => blockSup hold y.1.1 (timeBlockAt y.1.2 k y.2) := by
  unfold blockSup
  refine Measurable.iSup fun q => ?_
  have hset : MeasurableSet {y : (Ω × Grid) × ℝ | (q : ℝ) ∈ timeBlockAt y.1.2 k y.2} := by
    have hmap : Measurable fun y : (Ω × Grid) × ℝ =>
        (((y.1.2, y.2), (q : ℝ)) : (Grid × ℝ) × ℝ) :=
      ((measurable_fst.snd).prodMk measurable_snd).prodMk measurable_const
    exact hmap (measurableSet_mem_timeBlockAt k)
  have hf : Measurable fun y : (Ω × Grid) × ℝ => hold y.1.1 q :=
    hd.measurable.comp (measurable_fst.fst.prodMk measurable_const)
  have hEq : (fun y : (Ω × Grid) × ℝ => ⨆ (_ : (q : ℝ) ∈ timeBlockAt y.1.2 k y.2), hold y.1.1 q)
      = Set.indicator {y : (Ω × Grid) × ℝ | (q : ℝ) ∈ timeBlockAt y.1.2 k y.2}
        (fun y => hold y.1.1 q) := by
    funext y
    by_cases hy : (q : ℝ) ∈ timeBlockAt y.1.2 k y.2
    · rw [iSup_pos hy, Set.indicator_of_mem
        (show y ∈ {y : (Ω × Grid) × ℝ | (q : ℝ) ∈ timeBlockAt y.1.2 k y.2} from hy)]
    · rw [iSup_neg hy, Set.indicator_of_notMem
        (show y ∉ {y : (Ω × Grid) × ℝ | (q : ℝ) ∈ timeBlockAt y.1.2 k y.2} from hy)]
      rfl
  rw [hEq]
  exact hf.indicator hset

theorem measurable_ratio (hd : HoldingData G θΩ SΩ hold) (k : ℤ) :
    Measurable fun y : (Ω × Grid) × ℝ => ratio hold y.1.1 y.1.2 k y.2 :=
  (measurable_blockSup_timeBlockAt hold hd k).div
    (((measurable_side k).comp measurable_fst.snd).ennreal_ofReal)

theorem measurable_alpha (hd : HoldingData G θΩ SΩ hold) (k : ℤ) :
    Measurable fun y : (Ω × Grid) × ℝ => alpha hold y.1.1 y.1.2 k y.2 :=
  Measurable.iSup fun j => measurable_ratio hold hd (k + j)

theorem measurable_beta (hd : HoldingData G θΩ SΩ hold) (k : ℤ) :
    Measurable fun y : (Ω × Grid) × ℝ => beta hold y.1.1 y.1.2 k y.2 :=
  (measurable_alpha hold hd k).inv

theorem measurable_kappa (hd : HoldingData G θΩ SΩ hold) (k : ℤ) :
    Measurable fun y : (Ω × Grid) × ℝ => kappa hold y.1.1 y.1.2 k y.2 :=
  Measurable.ennreal_tsum fun j => (measurable_beta hold hd (k + j)).const_mul _

theorem measurableSet_goodK (hd : HoldingData G θΩ SΩ hold) (q : ℚ) (k : ℤ) :
    MeasurableSet {y : (Ω × Grid) × ℝ | GoodK hold q y.1.1 y.1.2 k y.2} :=
  measurableSet_le (measurable_kappa hold hd k) measurable_const

/-! ## 6. Good levels exist at vertex times and are bounded on the gate -/

/-- **A good level exists at every vertex time**: down the chain through the holding interval of
`s`, `κ(J) ≤ 2|J|/|I_s| → 0`. -/
theorem exists_goodK (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) {s : ℝ}
    (hs : hold ω s ≠ 0) (q : ℚ) (D : Grid) : ∃ k : ℤ, GoodK hold q ω D k s := by
  have hsT : hold ω s ≠ ∞ := (hold_lt_top hold hd hω s).ne
  have hpos : 0 < (hold ω s).toReal := ENNReal.toReal_pos hs hsT
  have h2q := two_rpow_pos q
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (2 * side D 0 / ((hold ω s).toReal * (2 : ℝ) ^ (q : ℝ))) (by norm_num : (1 : ℝ) < 2)
  refine ⟨0 - n, ?_⟩
  unfold GoodK
  have hβ : beta hold ω D (0 - n) s ≤ ENNReal.ofReal (side D (0 - n)) / hold ω s := by
    unfold beta
    have hα : hold ω s / ENNReal.ofReal (side D (0 - n)) ≤ alpha hold ω D (0 - n) s := by
      refine le_trans ?_ (ratio_le_alpha hold ω D (0 - n) s 0)
      simp only [Nat.cast_zero, add_zero]
      unfold ratio
      exact ENNReal.div_le_div_right (le_blockSup_timeBlockAt hold hd hω
        (mem_timeBlockAt_self D _ s)) _
    calc (alpha hold ω D (0 - n) s)⁻¹
        ≤ (hold ω s / ENNReal.ofReal (side D (0 - n)))⁻¹ := ENNReal.inv_le_inv.2 hα
      _ = ENNReal.ofReal (side D (0 - n)) / hold ω s :=
          ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inr hs)
  calc kappa hold ω D (0 - n) s ≤ 2 * beta hold ω D (0 - n) s :=
        kappa_le_two_mul_beta hold ω D _ s
    _ ≤ 2 * (ENNReal.ofReal (side D (0 - n)) / hold ω s) :=
        mul_le_mul_of_nonneg_left hβ zero_le
    _ = ENNReal.ofReal (2 * side D (0 - n) / (hold ω s).toReal) := by
        rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_toReal hsT,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_div_assoc]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (q : ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [side_sub_nat]
        have hn' : 2 * side D 0 < 2 ^ n * ((hold ω s).toReal * (2 : ℝ) ^ (q : ℝ)) :=
          (div_lt_iff₀ (by positivity)).1 hn
        rw [div_le_iff₀ hpos, mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
        nlinarith [hn']

/-- The ratio of a block whose side dominates `|s|` and the sublinearity threshold is at most
`2ε`. -/
theorem ratio_le_of_window (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) {ε : ℝ}
    (hε : 0 < ε) {T₀ : ℝ}
    (hT₀ : ∀ T : ℝ, T₀ ≤ T → windowSup hold ω T ≤ ENNReal.ofReal (ε * T)) {D : Grid} {k : ℤ}
    {s : ℝ} (hk : |s| ≤ side D k) (hk' : T₀ ≤ side D k) :
    ratio hold ω D k s ≤ ENNReal.ofReal (2 * ε) := by
  have hσ := side_pos D k
  have hsJ := mem_timeBlockAt_self D k s
  have hsub : timeBlockAt D k s ⊆ Set.Ico (-(|s| + side D k)) (|s| + side D k) := by
    intro x hx
    have h1 := hsJ.1
    have h2 := hsJ.2
    have h3 := hx.1
    have h4 := hx.2
    have h5 := neg_abs_le s
    have h6 := le_abs_self s
    exact ⟨by linarith, by linarith⟩
  unfold ratio
  calc blockSup hold ω (timeBlockAt D k s) / ENNReal.ofReal (side D k)
      ≤ windowSup hold ω (|s| + side D k) / ENNReal.ofReal (side D k) :=
        ENNReal.div_le_div_right (blockSup_mono hold ω hsub) _
    _ ≤ ENNReal.ofReal (ε * (|s| + side D k)) / ENNReal.ofReal (side D k) :=
        ENNReal.div_le_div_right (hT₀ _ (by linarith [abs_nonneg s])) _
    _ = ENNReal.ofReal (ε * (|s| + side D k) / side D k) := by
        rw [ENNReal.ofReal_div_of_pos hσ]
    _ ≤ ENNReal.ofReal (2 * ε) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hσ]
        nlinarith [hk, hε]

theorem alpha_le_of_window (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) {ε : ℝ}
    (hε : 0 < ε) {T₀ : ℝ}
    (hT₀ : ∀ T : ℝ, T₀ ≤ T → windowSup hold ω T ≤ ENNReal.ofReal (ε * T)) {D : Grid} {k : ℤ}
    {s : ℝ} (hk : |s| ≤ side D k) (hk' : T₀ ≤ side D k) :
    alpha hold ω D k s ≤ ENNReal.ofReal (2 * ε) := by
  refine iSup_le fun j => ?_
  have hmono : side D k ≤ side D (k + j) := side_mono D (by omega)
  exact ratio_le_of_window hold hd hω hε hT₀ (hk.trans hmono) (hk'.trans hmono)

/-- **On the gate the good levels are bounded above**: along ancestors `κ → ∞`. -/
theorem exists_not_goodK (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (q : ℚ) (D : Grid)
    (s : ℝ) : ∃ k : ℤ, ¬ GoodK hold q ω D k s := by
  have h2q := two_rpow_pos q
  set ε : ℝ := 1 / (4 * (2 : ℝ) ^ (q : ℝ)) with hε_def
  have hεpos : 0 < ε := by positivity
  obtain ⟨T₀, hT₀⟩ := hd.window_sublinear ω hω ε hεpos
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max |s| T₀ / side D 0) (by norm_num : (1 : ℝ) < 2)
  refine ⟨0 + n, fun hg => ?_⟩
  have hside : max |s| T₀ ≤ side D (0 + n) := by
    rw [side_add_nat]
    rw [div_lt_iff₀ (side_pos D 0)] at hn
    linarith
  have hα : alpha hold ω D (0 + n) s ≤ ENNReal.ofReal (2 * ε) :=
    alpha_le_of_window hold hd hω hεpos hT₀ (le_trans (le_max_left _ _) hside)
      (le_trans (le_max_right _ _) hside)
  have hβ : ENNReal.ofReal ((2 : ℝ) ^ (q : ℝ)) < beta hold ω D (0 + n) s := by
    unfold beta
    calc ENNReal.ofReal ((2 : ℝ) ^ (q : ℝ)) < ENNReal.ofReal ((2 * ε)⁻¹) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          rw [hε_def, show (2 * (1 / (4 * (2 : ℝ) ^ (q : ℝ))))⁻¹ = 2 * (2 : ℝ) ^ (q : ℝ) by
            field_simp
            ring]
          linarith
      _ = (ENNReal.ofReal (2 * ε))⁻¹ := ENNReal.ofReal_inv_of_pos (by positivity)
      _ ≤ (alpha hold ω D (0 + n) s)⁻¹ := ENNReal.inv_le_inv.2 hα
  have hκ : beta hold ω D (0 + n) s ≤ kappa hold ω D (0 + n) s := by
    calc beta hold ω D (0 + n) s = 1 * beta hold ω D (0 + n) s := (one_mul _).symm
      _ ≤ geomQuarter * beta hold ω D (0 + n) s :=
          mul_le_mul_of_nonneg_right one_le_geomQuarter zero_le
      _ ≤ kappa hold ω D (0 + n) s := geomQuarter_mul_beta_le_kappa hold ω D s le_rfl
  exact absurd (lt_of_lt_of_le hβ (hκ.trans hg)) (lt_irrefl _)

theorem bddAbove_goodK (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (q : ℚ) (D : Grid)
    (s : ℝ) : BddAbove {k : ℤ | GoodK hold q ω D k s} := by
  obtain ⟨k₀, hk₀⟩ := exists_not_goodK hold hd hω q D s
  refine ⟨k₀, fun k hk => ?_⟩
  by_contra hlt
  exact hk₀ (GoodK.mono_level hold (le_of_lt (not_le.1 hlt)) hk)

/-! ## 7. On the gate: `0 < α, β, κ < ∞`, and `κ` is strictly increasing along ancestors -/

/-- **`α > 0` on the gate**: some time of every block is a vertex time (the nonvertex times are
Lebesgue-null), so `D(J) > 0`. -/
theorem alpha_pos (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) : 0 < alpha hold ω D k s := by
  have hpos : 0 < volume (timeBlockAt D k s) := by
    rw [volume_timeBlockAt]
    exact ENNReal.ofReal_pos.2 (side_pos D k)
  have hne : ∃ u ∈ timeBlockAt D k s, hold ω u ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hsub : timeBlockAt D k s ⊆ {u : ℝ | hold ω u = 0} := fun u hu => hall u hu
    exact hpos.ne' (measure_mono_null hsub (hd.null_zero ω hω))
  obtain ⟨u, hu, hu0⟩ := hne
  have hD : 0 < blockSup hold ω (timeBlockAt D k s) :=
    lt_of_lt_of_le (pos_iff_ne_zero.2 hu0) (le_blockSup_timeBlockAt hold hd hω hu)
  refine lt_of_lt_of_le ?_ (ratio_le_alpha hold ω D k s 0)
  simp only [Nat.cast_zero, add_zero]
  unfold ratio
  exact ENNReal.div_pos hD.ne' ENNReal.ofReal_ne_top

theorem alpha_le_pow_mul (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) (j : ℕ) :
    alpha hold ω D k s ≤ 2 ^ j * alpha hold ω D (k + j) s := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc alpha hold ω D k s ≤ 2 ^ j * alpha hold ω D (k + j) s := ih
      _ ≤ 2 ^ j * (2 * alpha hold ω D (k + j + 1) s) :=
          mul_le_mul_of_nonneg_left (alpha_le_two_mul_succ hold ω D (k + j) s) zero_le
      _ = 2 ^ (j + 1) * alpha hold ω D (k + ((j + 1 : ℕ) : ℤ)) s := by
          rw [show k + ((j + 1 : ℕ) : ℤ) = k + j + 1 by push_cast; ring, pow_succ]
          ring

/-- Along ancestors `α` becomes smaller than any positive threshold. -/
theorem exists_alpha_le (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, alpha hold ω D (k + j) s ≤ ENNReal.ofReal (2 * ε) := by
  obtain ⟨T₀, hT₀⟩ := hd.window_sublinear ω hω ε hε
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max |s| T₀ / side D k) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_⟩
  have hside : max |s| T₀ ≤ side D (k + n) := by
    rw [side_add_nat]
    rw [div_lt_iff₀ (side_pos D k)] at hn
    linarith
  exact alpha_le_of_window hold hd hω hε hT₀ (le_trans (le_max_left _ _) hside)
    (le_trans (le_max_right _ _) hside)

/-- **`α < ∞` on the gate.** -/
theorem alpha_lt_top (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) : alpha hold ω D k s < ∞ := by
  obtain ⟨j, hj⟩ := exists_alpha_le hold hd hω D k s one_pos
  calc alpha hold ω D k s ≤ 2 ^ j * alpha hold ω D (k + j) s := alpha_le_pow_mul hold ω D k s j
    _ ≤ 2 ^ j * ENNReal.ofReal (2 * 1) := mul_le_mul_of_nonneg_left hj zero_le
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) ENNReal.ofReal_lt_top

theorem beta_pos (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) : 0 < beta hold ω D k s :=
  ENNReal.inv_pos.2 (alpha_lt_top hold hd hω D k s).ne

theorem beta_lt_top (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) : beta hold ω D k s < ∞ :=
  ENNReal.inv_lt_top.2 (alpha_pos hold hd hω D k s)

/-- **`κ < ∞` on the gate.** -/
theorem kappa_lt_top (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) : kappa hold ω D k s < ∞ :=
  lt_of_le_of_lt (kappa_le_two_mul_beta hold ω D k s)
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top (beta_lt_top hold hd hω D k s))

/-- **`κ > 0` on the gate.** -/
theorem kappa_pos (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) : 0 < kappa hold ω D k s :=
  lt_of_lt_of_le (beta_pos hold hd hω D k s)
    (calc beta hold ω D k s = 1 * beta hold ω D k s := (one_mul _).symm
      _ ≤ geomQuarter * beta hold ω D k s := mul_le_mul_of_nonneg_right one_le_geomQuarter zero_le
      _ ≤ kappa hold ω D k s := geomQuarter_mul_beta_le_kappa hold ω D s le_rfl)

/-- Along ancestors `β` eventually exceeds any of its values. -/
theorem exists_beta_lt (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) : ∃ j : ℕ, beta hold ω D k s < beta hold ω D (k + j) s := by
  have hα0 := alpha_pos hold hd hω D k s
  have hαT := alpha_lt_top hold hd hω D k s
  have hpos : 0 < (alpha hold ω D k s).toReal / 4 := by
    have := ENNReal.toReal_pos hα0.ne' hαT.ne
    positivity
  obtain ⟨j, hj⟩ := exists_alpha_le hold hd hω D k s hpos
  refine ⟨j, ?_⟩
  unfold beta
  refine ENNReal.inv_lt_inv.2 (lt_of_le_of_lt hj ?_)
  rw [show 2 * ((alpha hold ω D k s).toReal / 4) = (alpha hold ω D k s).toReal / 2 by ring,
    ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hαT.ne]
  have := ENNReal.toReal_pos hα0.ne' hαT.ne
  linarith

/-- Some consecutive pair along the ancestors of a block has strictly increasing `β`. -/
theorem exists_beta_lt_succ (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid)
    (k : ℤ) (s : ℝ) : ∃ j : ℕ, beta hold ω D (k + j) s < beta hold ω D (k + j + 1) s := by
  by_contra hall
  push_neg at hall
  have hconst : ∀ j : ℕ, beta hold ω D (k + j) s = beta hold ω D k s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine le_antisymm ?_ ?_
      · rw [show k + ((j + 1 : ℕ) : ℤ) = k + j + 1 by push_cast; ring]
        exact (hall j).trans ih.le
      · exact beta_mono hold ω D s (by omega)
  obtain ⟨j, hj⟩ := exists_beta_lt hold hd hω D k s
  rw [hconst j] at hj
  exact lt_irrefl _ hj

/-- **`κ` is strictly increasing along ancestors** on the gate. -/
theorem kappa_lt_succ (hd : HoldingData G θΩ SΩ hold) {ω : Ω} (hω : ω ∈ G) (D : Grid) (k : ℤ)
    (s : ℝ) : kappa hold ω D k s < kappa hold ω D (k + 1) s := by
  have hdecomp : kappa hold ω D (k + 1) s = kappa hold ω D k s
      + ∑' j : ℕ, (4⁻¹ : ℝ≥0∞) ^ j * (beta hold ω D (k + 1 + j) s - beta hold ω D (k + j) s) := by
    unfold kappa
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun j => ?_
    rw [← mul_add, add_tsub_cancel_of_le (beta_mono hold ω D s (by omega))]
  obtain ⟨j, hj⟩ := exists_beta_lt_succ hold hd hω D k s
  have hterm : 0 < (4⁻¹ : ℝ≥0∞) ^ j * (beta hold ω D (k + 1 + j) s - beta hold ω D (k + j) s) := by
    refine ENNReal.mul_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)) ?_
    rw [show k + 1 + (j : ℤ) = k + j + 1 by ring]
    exact (tsub_pos_iff_lt.2 hj).ne'
  have hR : (∑' j : ℕ, (4⁻¹ : ℝ≥0∞) ^ j * (beta hold ω D (k + 1 + j) s - beta hold ω D (k + j) s))
      ≠ 0 :=
    (lt_of_lt_of_le hterm (ENNReal.le_tsum (f := fun j : ℕ =>
      (4⁻¹ : ℝ≥0∞) ^ j * (beta hold ω D (k + 1 + j) s - beta hold ω D (k + j) s)) j)).ne'
  rw [hdecomp]
  exact ENNReal.lt_add_right (kappa_lt_top hold hd hω D k s).ne hR

end Gate

end ReflectedGMS.SupTypeTimeIndex
