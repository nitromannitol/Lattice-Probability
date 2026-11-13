/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.BracketLLNUniformProbability at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# From a fixed-time bracket law of large numbers to the uniform (ucp) form

The `ucp` field of `Limit/LocalizedArrayProducer.ThresholdArrayInputs` asks for

```
∀ ε > 0, Tendsto (fun n => P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T, ε < |V n t ω - v * t|}) atTop (𝓝 0)
```

i.e. the brackets converge to the linear bracket `v · t` **uniformly in probability** on
`[0, T]`.  The bracket law of large numbers, however, is naturally proved *at each fixed
rescaled time*: the manuscript's `p:lem:bracketlimit` is a statement about
`ε_n² ⟨M⟩(ε_n⁻² t)` for one `t`.  This module supplies the missing lift, abstractly:

**Pointwise in probability + monotonicity in the time variable + a continuous (here linear,
nonnegative-slope) limit ⟹ uniformly in probability on `[0, T]`.**

The mechanism is Pólya's: a monotone function which is within `ε/2` of `v · t` at the two
endpoints of an interval of length `δ` with `v δ ≤ ε/2` is within `ε` of `v · t` throughout
(`abs_sub_linear_le_of_monotone`).  So the uniform bad event is contained in the union of
finitely many *fixed-time* bad events at half the tolerance, plus the null set where
monotonicity fails, and finite subadditivity finishes it.

## Why this is not the Pólya theorem already in the tree

`Limit/ActualArrayBracketLimit.tendstoUniformlyOn_Icc_zero_of_eventually_monotoneOn` is the
**deterministic** Pólya theorem: pointwise convergence of real functions to a continuous limit,
upgraded to uniform convergence on a compact interval.  It applies pathwise, i.e. it converts an
*almost sure* fixed-time statement into an *almost sure* uniform statement.  It does not apply
here, because convergence in probability is not convergence at a point of the sample space: the
exceptional set moves with `n`.

The lift below is also **strictly cheaper than the almost-sure route**, and this is worth
recording.  Deducing the `ucp` field from an almost-sure locally uniform convergence would need
`{ω | ∃ t ∈ Icc 0 T, ε < |V n t ω - v t|}` to be *measurable* (a.e. convergence implies
convergence in measure only for measurable sets), and that set quantifies over an uncountable
index set, so its measurability is a genuine side condition — separability of the paths, or a
countable-dense-set reduction.  The route taken here never needs it: `measure_mono`,
`measure_union_le` and `measure_biUnion_finset_le` all hold for the outer measure of an
arbitrary set.  So the hypothesis is weaker (in probability, not a.s.) *and* the side
conditions are fewer.

## Contents

* `abs_sub_linear_le_of_monotone` — the deterministic two-point sandwich.
* `exists_gt_grid_of_monotone` — the pathwise inclusion: if a monotone `W` misses `v · t` by
  more than `ε` somewhere on `[0, T]`, it misses it by more than `ε/2` at one of the `N + 1`
  uniform grid points, provided `v · (T/N) ≤ ε/2`.
* `tendsto_measure_exists_gt_of_tendsto_pointwise` — **the lift**, in exactly the shape of the
  `ucp` field.

Nothing here is about the reflected walk, a martingale, or a filtration: the statements are
about an arbitrary family `V : ℕ → ℝ≥0 → Ω → ℝ` over an arbitrary measure.  In particular
nothing here certifies `p:lem:bracketlimit`, `p:eq:bracketLLN`, `p:thm:areaclt` or either main
theorem; the *input* `hpt` is the open bracket law of large numbers.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.BracketLLNUniform

/-! ### 1. The deterministic two-point sandwich -/

/-- **Monotone interpolation against a nonnegative linear function.**

If `W` is nondecreasing, `v ≥ 0`, and `W` is within `ε` of `t ↦ v t` at both endpoints `a ≤ b`
of an interval whose linear increment `v·b - v·a` is at most `ε`, then `W` is within `2ε` of
`t ↦ v t` at every `t ∈ [a, b]`.

This is the whole content of "monotonicity and a finite mesh in `t`". -/
theorem abs_sub_linear_le_of_monotone
    {W : ℝ≥0 → ℝ} {v ε : ℝ} {a b t : ℝ≥0}
    (hW : Monotone W) (hv : 0 ≤ v) (hat : a ≤ t) (htb : t ≤ b)
    (ha : |W a - v * (a : ℝ)| ≤ ε) (hb : |W b - v * (b : ℝ)| ≤ ε)
    (hgap : v * (b : ℝ) - v * (a : ℝ) ≤ ε) :
    |W t - v * (t : ℝ)| ≤ 2 * ε := by
  have h1 : W a ≤ W t := hW hat
  have h2 : W t ≤ W b := hW htb
  have hca : (a : ℝ) ≤ (t : ℝ) := by exact_mod_cast hat
  have hcb : (t : ℝ) ≤ (b : ℝ) := by exact_mod_cast htb
  have hva : v * (a : ℝ) ≤ v * (t : ℝ) := mul_le_mul_of_nonneg_left hca hv
  have hvb : v * (t : ℝ) ≤ v * (b : ℝ) := mul_le_mul_of_nonneg_left hcb hv
  rw [abs_le] at ha hb ⊢
  constructor
  · linarith [ha.1, hb.2]
  · linarith [ha.1, hb.2]

/-! ### 2. The pathwise inclusion -/

/-- **A monotone path that is far from `v · t` somewhere is far from it at a grid point.**

`δ₀` is the mesh, `N · δ₀ = T` the horizon, and `v · δ₀ ≤ ε/2` the mesh condition.  If the
nondecreasing `W` satisfies `ε < |W t - v t|` for some `t ≤ T`, then already
`ε/2 < |W (i δ₀) - v (i δ₀)|` for some `i ≤ N`.

The index is `i = ⌊t/δ₀⌋` and its partner `min (i+1) N`; capping at `N` is what removes the
case `t = T`, exactly as in the deterministic Pólya proof already in the tree. -/
theorem exists_gt_grid_of_monotone
    {W : ℝ≥0 → ℝ} {v ε : ℝ} {T δ₀ : ℝ≥0} {N : ℕ}
    (hW : Monotone W) (hv : 0 ≤ v) (hε : 0 < ε)
    (hTδ : (N : ℝ≥0) * δ₀ = T) (hvδ : v * (δ₀ : ℝ) ≤ ε / 2)
    {t : ℝ≥0} (htT : t ≤ T) (hlt : ε < |W t - v * (t : ℝ)|) :
    ∃ i ∈ Finset.range (N + 1),
      ε / 2 < |W ((i : ℝ≥0) * δ₀) - v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)| := by
  by_contra hcon
  push_neg at hcon
  have hTR : (N : ℝ) * (δ₀ : ℝ) = (T : ℝ) := by
    rw [← hTδ]; push_cast; ring
  have hsR : ∀ i : ℕ, (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ) = (i : ℝ) * (δ₀ : ℝ) := by
    intro i; push_cast; ring
  have hdnn : (0 : ℝ) ≤ (δ₀ : ℝ) := δ₀.coe_nonneg
  have htR : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
  rcases eq_or_lt_of_le hdnn with hd0 | hdpos
  · -- degenerate mesh: the horizon itself is `0`
    have hT0 : (T : ℝ) = 0 := by rw [← hTR, ← hd0]; ring
    have ht0 : t = 0 := by
      have h1 : (t : ℝ) = 0 := le_antisymm (by rw [← hT0]; exact htR) t.coe_nonneg
      exact_mod_cast h1
    have h0 := hcon 0 (Finset.mem_range.mpr (Nat.succ_pos N))
    have hs0 : ((0 : ℕ) : ℝ≥0) * δ₀ = t := by rw [ht0]; simp
    rw [hs0] at h0
    linarith
  · -- the generic mesh
    set i : ℕ := ⌊(t : ℝ) / (δ₀ : ℝ)⌋₊ with hidef
    have htd : (0 : ℝ) ≤ (t : ℝ) / (δ₀ : ℝ) := div_nonneg t.coe_nonneg hdnn
    have hfl : (i : ℝ) ≤ (t : ℝ) / (δ₀ : ℝ) := Nat.floor_le htd
    have hfl2 : (t : ℝ) / (δ₀ : ℝ) < (i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hiN : i ≤ N := by
      have h1 : (t : ℝ) / (δ₀ : ℝ) ≤ (N : ℝ) := by
        rw [div_le_iff₀ hdpos, hTR]; exact htR
      calc i = ⌊(t : ℝ) / (δ₀ : ℝ)⌋₊ := hidef
        _ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_mono h1
        _ = N := Nat.floor_natCast N
    set k : ℕ := min (i + 1) N with hkdef
    have hkN : k ≤ N := min_le_right _ _
    have hik : i ≤ k := le_min (Nat.le_succ i) hiN
    have hlow : (i : ℝ≥0) * δ₀ ≤ t := by
      have h2 : (i : ℝ) * (δ₀ : ℝ) ≤ (t : ℝ) := by
        have h3 := mul_le_mul_of_nonneg_right hfl hdnn
        rwa [div_mul_cancel₀ _ hdpos.ne'] at h3
      have h4 : (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ) ≤ (t : ℝ) := by rw [hsR i]; exact h2
      exact_mod_cast h4
    have hhigh : t ≤ (k : ℝ≥0) * δ₀ := by
      have h2 : (t : ℝ) ≤ (k : ℝ) * (δ₀ : ℝ) := by
        rcases le_or_gt (i + 1) N with hc | hc
        · have hkeq : k = i + 1 := by rw [hkdef, min_eq_left hc]
          have hkR : (k : ℝ) = (i : ℝ) + 1 := by rw [hkeq]; push_cast; ring
          rw [hkR]
          have h5 : ((t : ℝ) / (δ₀ : ℝ)) * (δ₀ : ℝ) < ((i : ℝ) + 1) * (δ₀ : ℝ) :=
            mul_lt_mul_of_pos_right hfl2 hdpos
          rw [div_mul_cancel₀ _ hdpos.ne'] at h5
          linarith
        · have hkeq : k = N := by rw [hkdef, min_eq_right hc.le]
          rw [hkeq, hTR]; exact htR
      have h4 : (t : ℝ) ≤ (((k : ℝ≥0) * δ₀ : ℝ≥0) : ℝ) := by rw [hsR k]; exact h2
      exact_mod_cast h4
    have hgapR : v * (((k : ℝ≥0) * δ₀ : ℝ≥0) : ℝ) - v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ) ≤ ε / 2 := by
      rw [hsR k, hsR i]
      have hikR : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
      have hkiR : (k : ℝ) ≤ (i : ℝ) + 1 := by
        have hle : k ≤ i + 1 := min_le_left _ _
        have h' : (k : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast hle
        push_cast at h'; exact h'
      have h1 : (δ₀ : ℝ) * ((k : ℝ) - (i : ℝ)) ≤ (δ₀ : ℝ) := by nlinarith
      calc v * ((k : ℝ) * (δ₀ : ℝ)) - v * ((i : ℝ) * (δ₀ : ℝ))
          = v * ((δ₀ : ℝ) * ((k : ℝ) - (i : ℝ))) := by ring
        _ ≤ v * (δ₀ : ℝ) := mul_le_mul_of_nonneg_left h1 hv
        _ ≤ ε / 2 := hvδ
    have hA := hcon i (Finset.mem_range.mpr (Nat.lt_succ_of_le hiN))
    have hB := hcon k (Finset.mem_range.mpr (Nat.lt_succ_of_le hkN))
    have hfin : |W t - v * (t : ℝ)| ≤ 2 * (ε / 2) :=
      abs_sub_linear_le_of_monotone hW hv hlow hhigh hA hB hgapR
    linarith

/-! ### 3. The lift -/

/-- **The ucp lift.**  Let `V n` be a family of real processes indexed by `ℝ≥0`, almost surely
nondecreasing in the time variable, and let `v ≥ 0`.  If at **every fixed** time `t ≤ T` the
values `V n t` converge in probability to `v · t`, then the convergence is uniform in
probability on `[0, T]`:

`∀ ε > 0, P {ω | ∃ t ∈ [0,T], ε < |V n t ω - v t|} → 0`.

This is exactly the `ucp` field of `Limit/LocalizedArrayProducer.ThresholdArrayInputs`, and it
is the only step between the manuscript's fixed-time bracket law of large numbers and that
field.

No measurability whatsoever is assumed — neither of `V n t` nor of the uniform bad event.  The
proof uses only monotonicity of the outer measure and finite subadditivity. -/
theorem tendsto_measure_exists_gt_of_tendsto_pointwise
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {V : ℕ → ℝ≥0 → Ω → ℝ} {v : ℝ} {T : ℝ≥0}
    (hv : 0 ≤ v)
    (hmono : ∀ n, ∀ᵐ ω ∂P, Monotone fun t => V n t ω)
    (hpt : ∀ t : ℝ≥0, t ≤ T → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => P {ω | δ < |V n t ω - v * (t : ℝ)|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T, ε < |V n t ω - v * (t : ℝ)|})
      atTop (𝓝 0) := by
  -- the mesh
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * v * (T : ℝ) / ε)
  set N : ℕ := N₀ + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos _
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : ((N : ℝ≥0)) ≠ 0 := by
    have hne : N ≠ 0 := hNpos.ne'
    exact_mod_cast hne
  set δ₀ : ℝ≥0 := T / (N : ℝ≥0) with hδdef
  have hTδ : (N : ℝ≥0) * δ₀ = T := by
    rw [hδdef]; field_simp
  have hTR : (N : ℝ) * (δ₀ : ℝ) = (T : ℝ) := by
    rw [← hTδ]; push_cast; ring
  have hvδ : v * (δ₀ : ℝ) ≤ ε / 2 := by
    have hcoe : (δ₀ : ℝ) = (T : ℝ) / (N : ℝ) := by rw [hδdef]; push_cast; ring
    rw [hcoe]
    have hrw : v * ((T : ℝ) / (N : ℝ)) = (v * (T : ℝ)) / (N : ℝ) := by ring
    rw [hrw, div_le_iff₀ hNR]
    have h2 : 2 * v * (T : ℝ) < (N₀ : ℝ) * ε := (div_lt_iff₀ hε).mp hN₀
    have h3 : ((N₀ : ℕ) : ℝ) ≤ (N : ℝ) := by
      have hle : N₀ ≤ N := by omega
      exact_mod_cast hle
    have h4 : (N₀ : ℝ) * ε ≤ (N : ℝ) * ε := mul_le_mul_of_nonneg_right h3 hε.le
    linarith
  -- the grid points lie in `[0, T]`
  have hsT : ∀ i : ℕ, i ≤ N → (i : ℝ≥0) * δ₀ ≤ T := by
    intro i hi
    have hiR : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    have hdnn : (0 : ℝ) ≤ (δ₀ : ℝ) := δ₀.coe_nonneg
    have hcoe : (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ) = (i : ℝ) * (δ₀ : ℝ) := by push_cast; ring
    have h1 : (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
      rw [hcoe, ← hTR]; nlinarith
    exact_mod_cast h1
  -- the inclusion of events
  have hincl : ∀ n : ℕ,
      {ω | ∃ t ∈ Icc (0 : ℝ≥0) T, ε < |V n t ω - v * (t : ℝ)|} ⊆
        {ω | ¬ Monotone fun t => V n t ω} ∪
          ⋃ i ∈ Finset.range (N + 1),
            {ω | ε / 2 < |V n ((i : ℝ≥0) * δ₀) ω -
              v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)|} := by
    intro n ω hω
    rcases Classical.em (Monotone fun t => V n t ω) with hm | hm
    · refine Or.inr ?_
      obtain ⟨t, htmem, hlt⟩ := hω
      obtain ⟨i, hi, hgi⟩ :=
        exists_gt_grid_of_monotone (W := fun u => V n u ω) hm hv hε hTδ hvδ htmem.2 hlt
      exact Set.mem_biUnion hi hgi
    · exact Or.inl hm
  -- the null set where monotonicity fails
  have hBad : ∀ n : ℕ, P {ω | ¬ Monotone fun t => V n t ω} = 0 := fun n => ae_iff.mp (hmono n)
  -- finite subadditivity
  have hbound : ∀ n : ℕ,
      P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T, ε < |V n t ω - v * (t : ℝ)|} ≤
        ∑ i ∈ Finset.range (N + 1),
          P {ω | ε / 2 < |V n ((i : ℝ≥0) * δ₀) ω - v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)|} := by
    intro n
    calc P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T, ε < |V n t ω - v * (t : ℝ)|}
        ≤ P ({ω | ¬ Monotone fun t => V n t ω} ∪
            ⋃ i ∈ Finset.range (N + 1),
              {ω | ε / 2 < |V n ((i : ℝ≥0) * δ₀) ω -
                v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)|}) := measure_mono (hincl n)
      _ ≤ P {ω | ¬ Monotone fun t => V n t ω} +
            P (⋃ i ∈ Finset.range (N + 1),
              {ω | ε / 2 < |V n ((i : ℝ≥0) * δ₀) ω -
                v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)|}) := measure_union_le _ _
      _ = P (⋃ i ∈ Finset.range (N + 1),
              {ω | ε / 2 < |V n ((i : ℝ≥0) * δ₀) ω -
                v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)|}) := by rw [hBad n, zero_add]
      _ ≤ ∑ i ∈ Finset.range (N + 1),
              P {ω | ε / 2 < |V n ((i : ℝ≥0) * δ₀) ω -
                v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)|} := measure_biUnion_finset_le _ _
  -- each fixed-time term vanishes
  have hsum : Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range (N + 1),
        P {ω | ε / 2 < |V n ((i : ℝ≥0) * δ₀) ω - v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)|})
      atTop (𝓝 0) := by
    have hzero : Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (N + 1),
          P {ω | ε / 2 < |V n ((i : ℝ≥0) * δ₀) ω - v * (((i : ℝ≥0) * δ₀ : ℝ≥0) : ℝ)|})
        atTop (𝓝 (∑ _i ∈ Finset.range (N + 1), (0 : ℝ≥0∞))) := by
      refine tendsto_finsetSum _ ?_
      intro i hi
      exact hpt ((i : ℝ≥0) * δ₀) (hsT i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        (ε / 2) (by linarith)
    simpa using hzero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

end ReflectedGMS.BracketLLNUniform
