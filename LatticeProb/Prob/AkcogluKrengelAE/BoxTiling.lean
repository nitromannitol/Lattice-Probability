/-
# The per-coordinate box tiling: the anchored-box theorem from the anchored-cube iteration

The library's cube theorem `LatticeProb.exists_ae_tendsto_gridAvg_univ_with_integral`
(`BoundedErgodic.lean:561`) is proved by iterating the one-parameter Birkhoff theorem over the
coordinates of `ℤ^d`, using the *same* side length `n` in every coordinate.  The frozen
`VRW.External.PointwiseErgodicCubes` needs the **anchored box** `∏ᵢ [0, ⌈N cᵢ⌉)` with
coordinate-dependent sides.

This file generalises the iteration to per-coordinate lengths: `boxGridSet s m` is the box
`∏_{i∈s}[0, mᵢ)`, and `boxAvg σ h s m` its average.  The combinatorial reindexing and the
Birkhoff identity `boxAvg_insert_eq_bAvg_boxAvg` are the exact analogues of the library's
`sum_gridSet_insert_eq_sum_range_sum_iterate` and `gridAvg_insert_eq_bAvg_gridAvg`.  No maximal
inequality is needed: the box limit is produced by the same moving-target Birkhoff argument, with
the average length running over the coordinate function `m` rather than the index.
-/
import LatticeProb.Prob.AkcogluKrengelAE.BoundedErgodic

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Coordinates in `s` range over `[0, m i)`, the others are `0`. -/
def boxGridSet {d : ℕ} (s : Finset (Fin d)) (m : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => if i ∈ s then Finset.range (m i) else {0}

/-- Average of `h ∘ σ z` over the box `boxGridSet s m`. -/
noncomputable def boxAvg {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) (s : Finset (Fin d))
    (m : Fin d → ℕ) (ω : Ω) : ℝ :=
  (∑ w ∈ boxGridSet s m, h (σ (natToSite w) ω)) / ∏ i ∈ s, (m i : ℝ)

/-- The box `boxGridSet s m` has `∏_{i∈s} mᵢ` points. -/
theorem card_boxGridSet {d : ℕ} (s : Finset (Fin d)) (m : Fin d → ℕ) :
    (boxGridSet s m).card = ∏ i ∈ s, m i := by
  unfold boxGridSet
  rw [Fintype.card_piFinset]
  have hcoe : ∀ i : Fin d, (if i ∈ s then Finset.range (m i) else {0}).card
      = (if i ∈ s then m i else 1) := by
    intro i
    by_cases hi : i ∈ s <;> simp [hi]
  simp only [hcoe]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- A coordinate outside `s` vanishes on every point of `boxGridSet s m`. -/
theorem boxGridSet_apply_eq_zero_of_notMem {d : ℕ} {s : Finset (Fin d)} {m : Fin d → ℕ}
    {w : Fin d → ℕ} {i : Fin d} (hw : w ∈ boxGridSet s m) (hi : i ∉ s) : w i = 0 := by
  simp only [boxGridSet, Fintype.mem_piFinset] at hw
  have h := hw i
  rw [if_neg hi, Finset.mem_singleton] at h
  exact h

/-- Updating coordinate `i` of a box point in `boxGridSet s m` to a value `j` lands in
`boxGridSet (insert i s) m` iff `j < m i`. -/
theorem update_mem_boxGridSet_insert_iff {d : ℕ} {s : Finset (Fin d)} {i : Fin d}
    (_unused_hi : i ∉ s) (m : Fin d → ℕ) (w : Fin d → ℕ) (j : ℕ) (hw : w ∈ boxGridSet s m) :
    Function.update w i j ∈ boxGridSet (insert i s) m ↔ j ∈ Finset.range (m i) := by
  unfold boxGridSet at hw ⊢
  rw [Fintype.mem_piFinset] at hw ⊢
  constructor
  · intro h
    have := h i
    rw [Function.update_self, if_pos (Finset.mem_insert_self i s)] at this
    exact this
  · intro hj a
    by_cases ha : a = i
    · rw [ha, Function.update_self, if_pos (Finset.mem_insert_self i s)]
      exact hj
    · rw [Function.update_apply, if_neg ha]
      have hwa := hw a
      by_cases has : a ∈ s
      · rw [if_pos has] at hwa
        rw [if_pos (Finset.mem_insert_of_mem has)]
        exact hwa
      · rw [if_neg has] at hwa
        rw [if_neg (fun hmem => by
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact ha h'
          · exact has h')]
        exact hwa

/-- A point of `boxGridSet (insert i s) m` restricts, after zeroing coordinate `i`, to a point of
`boxGridSet s m`, with its `i`-th coordinate below `m i`. -/
theorem update_zero_mem_boxGridSet_of_mem_insert {d : ℕ} {s : Finset (Fin d)} {i : Fin d}
    (hi : i ∉ s) (m : Fin d → ℕ) (w : Fin d → ℕ) (hw : w ∈ boxGridSet (insert i s) m) :
    Function.update w i 0 ∈ boxGridSet s m ∧ w i ∈ Finset.range (m i) := by
  unfold boxGridSet at hw ⊢
  rw [Fintype.mem_piFinset] at hw ⊢
  refine ⟨?_, ?_⟩
  · intro a
    by_cases ha : a = i
    · rw [ha, Function.update_self, if_neg hi]
      exact Finset.mem_singleton.mpr rfl
    · rw [Function.update_apply, if_neg ha]
      have hwa := hw a
      by_cases has : a ∈ s
      · rw [if_pos has]
        rw [if_pos (Finset.mem_insert_of_mem has)] at hwa
        exact hwa
      · rw [if_neg has]
        have hni : ¬ a ∈ insert i s := fun hmem => by
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact ha h'
          · exact has h'
        rw [if_neg hni] at hwa
        rw [Finset.mem_singleton] at hwa ⊢
        exact hwa
  · have := hw i
    rw [if_pos (Finset.mem_insert_self i s)] at this
    exact this

/-- A sum over the box `boxGridSet (insert i s) m` splits as a sum over `boxGridSet s m` of sums
over the `m i` values of the new coordinate `i`. -/
theorem sum_boxGridSet_insert {d : ℕ} {M : Type*} [AddCommMonoid M] (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (m : Fin d → ℕ) (g : (Fin d → ℕ) → M) :
    ∑ w ∈ boxGridSet (insert i s) m, g w =
      ∑ w ∈ boxGridSet s m, ∑ j ∈ Finset.range (m i), g (Function.update w i j) := by
  rw [← Finset.sum_product (boxGridSet s m) (Finset.range (m i))
        (fun p : (Fin d → ℕ) × ℕ => g (Function.update p.1 i p.2))]
  refine Finset.sum_nbij' (s := boxGridSet (insert i s) m)
    (t := boxGridSet s m ×ˢ Finset.range (m i)) (f := g)
    (g := fun p : (Fin d → ℕ) × ℕ => g (Function.update p.1 i p.2))
    (i := fun w : Fin d → ℕ => (Function.update w i 0, w i))
    (j := fun p : (Fin d → ℕ) × ℕ => Function.update p.1 i p.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_product]
    exact update_zero_mem_boxGridSet_of_mem_insert hi m w hw
  · intro p hp
    rw [Finset.mem_product] at hp
    exact (update_mem_boxGridSet_insert_iff hi m p.1 p.2 hp.1).mpr hp.2
  · intro w _hw
    rw [Function.update_idem, Function.update_eq_self]
  · intro p hp
    rw [Finset.mem_product] at hp
    have h0 : p.1 i = 0 := boxGridSet_apply_eq_zero_of_notMem hp.1 hi
    apply Prod.ext
    · rw [Function.update_idem, ← h0, Function.update_eq_self]
    · rw [Function.update_self]
  · intro w _hw
    rw [Function.update_idem, Function.update_eq_self]

/-- The numerator of `boxAvg` over `insert i s` splits, via the box reindexing and the additivity
of the action, into a sum over the range of the new coordinate of sums over `boxGridSet s m`. -/
theorem sum_boxGridSet_insert_eq_sum_range_sum_iterate {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (m : Fin d → ℕ) (ω : Ω) :
    ∑ w ∈ boxGridSet (insert i s) m, h (σ (natToSite w) ω) =
      ∑ k ∈ Finset.range (m i), ∑ w ∈ boxGridSet s m,
        h (σ (natToSite w) ((σ (unit i))^[k] ω)) := by
  rw [sum_boxGridSet_insert s i hi m (fun w => h (σ (natToSite w) ω)), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro w hw
  rw [natToSite_update_eq_add_smul_unit w i (boxGridSet_apply_eq_zero_of_notMem hw hi) j,
      action_add_smul_unit_eq_iterate hσadd (natToSite w) i ω j,
      ← action_commute_iterate hσadd (natToSite w) (unit i) j ω]

/-- The box average over `insert i s` equals the Birkhoff average, along the action of `unit i`,
of the box average over `s`, with length `m i`. -/
theorem boxAvg_insert_eq_bAvg_boxAvg {d : ℕ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (m : Fin d → ℕ) (ω : Ω) :
    boxAvg σ h (insert i s) m ω = bAvg (σ (unit i)) (boxAvg σ h s m) (m i) ω := by
  simp only [boxAvg, bAvg, birkhoffSum]
  rw [Finset.prod_insert hi, sum_boxGridSet_insert_eq_sum_range_sum_iterate hσadd h s i hi m ω]
  rw [← Finset.sum_div, div_div, mul_comm]


omit [MeasurableSpace Ω] in
/-- The box average over the empty set is the single value `h (σ (natToSite 0))`. -/
theorem boxAvg_empty {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) (m : Fin d → ℕ) (ω : Ω) :
    boxAvg σ h ∅ m ω = h (σ (natToSite 0) ω) := by
  simp only [boxAvg, boxGridSet, Finset.notMem_empty, if_false, Fintype.piFinset_singleton,
    Finset.sum_singleton, Finset.prod_empty, div_one]
  rfl

/-- `boxAvg σ h s m` is measurable when `h` is measurable and each `σ z` is measurable. -/
theorem measurable_boxAvg {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) {h : Ω → ℝ} (hh : Measurable h)
    (s : Finset (Fin d)) (m : Fin d → ℕ) : Measurable (boxAvg σ h s m) := by
  unfold boxAvg
  exact (Finset.measurable_sum _ (fun w _ => hh.comp (hσ (natToSite w)).measurable)).div_const _

omit [MeasurableSpace Ω] in
/-- The box average `boxAvg σ h s m` is bounded in absolute value by the bound `M` on `h`. -/
theorem abs_boxAvg_le {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hh : ∀ x, |h x| ≤ M) (s : Finset (Fin d)) (m : Fin d → ℕ) (ω : Ω) :
    |boxAvg σ h s m ω| ≤ M := by
  rw [boxAvg]
  have hDn : 0 ≤ ∏ i ∈ s, (m i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  rw [abs_div, abs_of_nonneg hDn]
  by_cases hD : (∏ i ∈ s, (m i : ℝ)) = 0
  · rw [hD, div_zero]; exact hM
  · have hDp : 0 < ∏ i ∈ s, (m i : ℝ) := lt_of_le_of_ne hDn (Ne.symm hD)
    rw [div_le_iff₀ hDp, mul_comm M (∏ i ∈ s, (m i : ℝ))]
    calc |∑ w ∈ boxGridSet s m, h (σ (natToSite w) ω)|
        ≤ ∑ w ∈ boxGridSet s m, |h (σ (natToSite w) ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w ∈ boxGridSet s m, M := Finset.sum_le_sum fun w _ => hh _
      _ = (boxGridSet s m).card • M := Finset.sum_const M
      _ = ((∏ i ∈ s, m i : ℕ) : ℝ) * M := by rw [card_boxGridSet, nsmul_eq_mul]
      _ = (∏ i ∈ s, (m i : ℝ)) * M := by rw [Nat.cast_prod]

/-- Moving-target Birkhoff theorem along an arbitrary length sequence: if `g n → G` a.e. with a
uniform bound and `L n → ∞`, then `bAvg T (g n) (L n) → bLimsup T G` a.e. -/
theorem ae_tendsto_bAvg_movingTarget_seq {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hgm : ∀ n, Measurable (g n)) (hGm : Measurable G)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M)
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (G x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T (g n) (L n) x) atTop (𝓝 (bLimsup T G x)) := by
  have hGint : Integrable G μ :=
    Integrable.of_bound hGm.aestronglyMeasurable M (by
      filter_upwards with x; rw [Real.norm_eq_abs]; exact hG x)
  have hDmeas : ∀ N, Measurable (supDev g G N) :=
    (measurable_supDev_and_tendsto_zero hM hgm hGm hg hG).1
  have hDbound : ∀ N x, |supDev g G N x| ≤ 2 * M := fun N x => by
    have h := supDev_nonneg_le_antitone_bound hM hg hG N x
    rw [abs_of_nonneg h.1]; exact h.2.1
  have hDint : ∀ N, Integrable (supDev g G N) μ := fun N =>
    Integrable.of_bound (hDmeas N).aestronglyMeasurable (2 * M) (by
      filter_upwards with x; rw [Real.norm_eq_abs]; exact hDbound N x)
  have hae0 : ∀ᵐ x ∂μ, Tendsto (fun N => bLimsup T (supDev g G N) x) atTop (𝓝 0) :=
    tendsto_bLimsup_supDev_zero hT hM hgm hGm hg hG hconv
  have haeG : ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T G (L n) x) atTop (𝓝 (bLimsup T G x)) := by
    filter_upwards [ae_tendsto_bLimsup hT hGm hGint] with x hx
    exact hx.comp hL
  have haeD : ∀ᵐ x ∂μ, ∀ N, Tendsto (fun n => bAvg T (supDev g G N) (L n) x) atTop
      (𝓝 (bLimsup T (supDev g G N) x)) := by
    rw [ae_all_iff]
    intro N
    filter_upwards [ae_tendsto_bLimsup hT (hDmeas N) (hDint N)] with x hx
    exact hx.comp hL
  filter_upwards [hae0, haeG, haeD] with x hx0 hxG hxD
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hx0 (ε / 4) hε4
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hxG (ε / 2) hε2
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp (hxD N0) (ε / 4) hε4
  refine ⟨max N0 (max N1 N2), fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hN0lt : bLimsup T (supDev g G N0) x < ε / 4 := by
    have h := hN0 N0 le_rfl
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hBlt : bAvg T (supDev g G N0) (L n) x < ε / 2 := by
    have hB : bAvg T (supDev g G N0) (L n) x ≤ bLimsup T (supDev g G N0) x +
        |bAvg T (supDev g G N0) (L n) x - bLimsup T (supDev g G N0) x| := by
      have hb := le_abs_self (bAvg T (supDev g G N0) (L n) x - bLimsup T (supDev g G N0) x)
      linarith
    have h2 := hN2 n hn2
    rw [Real.dist_eq] at h2
    linarith
  have hX : |bAvg T (g n) (L n) x - bAvg T G (L n) x| < ε / 2 := by
    have h1 := abs_bAvg_sub_le_bAvg_of_abs_sub_le (T := T) (g := g n) (G := G)
      (fun y => (supDev_nonneg_le_antitone_bound hM hg hG N0 y).2.2.2 n hn0) (L n) x
    linarith
  have hY : dist (bAvg T G (L n) x) (bLimsup T G x) < ε / 2 := hN1 n hn1
  calc dist (bAvg T (g n) (L n) x) (bLimsup T G x)
      ≤ dist (bAvg T (g n) (L n) x) (bAvg T G (L n) x) +
          dist (bAvg T G (L n) x) (bLimsup T G x) := dist_triangle _ _ _
    _ < ε := by rw [Real.dist_eq]; linarith


/-- For each coordinate set `s`, the box average `boxAvg σ h s (m N)` converges a.e., as `N → ∞`
along any sequence of boxes all of whose sides over `s` tend to infinity, to a bounded measurable
limit depending only on `s` (not on the sequence). -/
theorem exists_ae_tendsto_boxAvg {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (s : Finset (Fin d)) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧
      ∀ (m : ℕ → Fin d → ℕ), (∀ i ∈ s, Tendsto (fun N => m N i) atTop atTop) →
        ∀ᵐ ω ∂μ, Tendsto (fun N => boxAvg σ h s (m N) ω) atTop (𝓝 (G ω)) := by
  induction s using Finset.induction with
  | empty =>
    refine ⟨fun ω => h (σ (natToSite 0) ω), hh.comp (hσ _).measurable, fun x => hb _, ?_⟩
    intro m _hm
    filter_upwards with ω
    have hconst : (fun N : ℕ => boxAvg σ h ∅ (m N) ω) = fun _ : ℕ => h (σ (natToSite 0) ω) := by
      funext N; exact boxAvg_empty σ h (m N) ω
    rw [hconst]; exact tendsto_const_nhds
  | insert i s hi ih =>
    obtain ⟨G, hGm, hGb, hGconv⟩ := ih
    refine ⟨bLimsup (σ (unit i)) G, measurable_bLimsup (hσ _).measurable hGm,
      fun x => abs_bLimsup_le_of_abs_le hM hGb x, ?_⟩
    intro m hm
    have hmi : Tendsto (fun N => m N i) atTop atTop := hm i (Finset.mem_insert_self i s)
    have hms : ∀ j ∈ s, Tendsto (fun N => m N j) atTop atTop :=
      fun j hj => hm j (Finset.mem_insert_of_mem hj)
    have hconv : ∀ᵐ ω ∂μ, Tendsto (fun N => boxAvg σ h s (m N) ω) atTop (𝓝 (G ω)) :=
      hGconv m hms
    have hmeas : ∀ N, Measurable (boxAvg σ h s (m N)) :=
      fun N => measurable_boxAvg hσ hh s (m N)
    have hbdd : ∀ N x, |boxAvg σ h s (m N) x| ≤ M :=
      fun N x => abs_boxAvg_le σ h hM hb s (m N) x
    have hmt := ae_tendsto_bAvg_movingTarget_seq (hσ (unit i)) hM hmeas hGm hbdd hGb hmi hconv
    filter_upwards [hmt] with ω hω
    have heq : (fun N => boxAvg σ h (insert i s) (m N) ω)
        = fun N => bAvg (σ (unit i)) (boxAvg σ h s (m N)) (m N i) ω := by
      funext N; exact boxAvg_insert_eq_bAvg_boxAvg hσadd h s i hi (m N) ω
    rw [heq]; exact hω


end LatticeProb
