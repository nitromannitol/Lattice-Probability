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
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic

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
    (_unused_hi : i ∉ s) (m : Fin d → ℕ) (w : Fin d → ℕ) (j : ℕ)
    (hw : w ∈ boxGridSet s m) :
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
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (m : Fin d → ℕ) (ω : Ω) :
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
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (m : Fin d → ℕ) (ω : Ω) :
    boxAvg σ h (insert i s) m ω = bAvg (σ (unit i)) (boxAvg σ h s m) (m i) ω := by
  simp only [boxAvg, bAvg, birkhoffSum]
  rw [Finset.prod_insert hi, sum_boxGridSet_insert_eq_sum_range_sum_iterate hσadd h s i hi m ω]
  rw [← Finset.sum_div, div_div, mul_comm]


omit [MeasurableSpace Ω] in
/-- The box average over the empty set is the single value `h (σ (natToSite 0))`. -/
theorem boxAvg_empty {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) (m : Fin d → ℕ)
    (ω : Ω) :
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
theorem abs_boxAvg_le {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hh : ∀ x, |h x| ≤ M) (s : Finset (Fin d)) (m : Fin d → ℕ) (ω : Ω) :
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
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hgm : ∀ n, Measurable (g n)) (hGm : Measurable G)
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


omit [MeasurableSpace Ω] in
/-- Iterates of two commuting maps commute. -/
theorem iterate_comm {T S : Ω → Ω} (hcomm : ∀ ω, T (S ω) = S (T ω)) (k : ℕ) (ω : Ω) :
    (T^[k]) (S ω) = S ((T^[k]) ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hcomm]

omit [MeasurableSpace Ω] in
/-- `bLimsup T f` commutes with a map `S` that commutes with `T`. -/
theorem bLimsup_comp_apply {T S : Ω → Ω} (hcomm : ∀ ω, T (S ω) = S (T ω))
    (f : Ω → ℝ) :
    bLimsup T f ∘ S = bLimsup T (f ∘ S) := by
  funext ω
  have h : (fun n => bAvg T f n (S ω)) = fun n => bAvg T (f ∘ S) n ω := by
    funext n
    unfold bAvg birkhoffSum
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [iterate_comm hcomm k ω]
    rfl
  simp only [bLimsup, Function.comp_apply]
  rw [h]

/-- For each coordinate set `s`, the box average `boxAvg σ h s (m N)` converges a.e., as
`N → ∞` along any sequence of boxes all of whose sides over `s` tend to infinity, to a bounded
measurable limit depending only on `s` (not on the sequence). -/
theorem exists_ae_tendsto_boxAvg {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (s : Finset (Fin d)) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧
      (∀ (m : ℕ → Fin d → ℕ), (∀ i ∈ s, Tendsto (fun N => m N i) atTop atTop) →
        ∀ᵐ ω ∂μ, Tendsto (fun N => boxAvg σ h s (m N) ω) atTop (𝓝 (G ω))) ∧
      (∀ j ∈ s, G ∘ σ (unit j) = G) := by
  induction s using Finset.induction with
  | empty =>
    refine ⟨fun ω => h (σ (natToSite 0) ω), hh.comp (hσ _).measurable, fun x => hb _,
      ?_, ?_⟩
    · intro m _hm
      filter_upwards with ω
      have hconst : (fun N : ℕ => boxAvg σ h ∅ (m N) ω) =
          fun _ : ℕ => h (σ (natToSite 0) ω) := by
        funext N; exact boxAvg_empty σ h (m N) ω
      rw [hconst]; exact tendsto_const_nhds
    · intro j hj; exact absurd hj (Finset.notMem_empty j)
  | insert i s hi ih =>
    obtain ⟨G, hGm, hGb, hGconv, hinv⟩ := ih
    refine ⟨bLimsup (σ (unit i)) G, measurable_bLimsup (hσ _).measurable hGm,
      fun x => abs_bLimsup_le_of_abs_le hM hGb x, ?_, ?_⟩
    · intro m hm
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
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · funext ω
        exact bLimsup_comp hM hGb ω
      · have hcomm : ∀ ω, σ (unit i) (σ (unit j) ω) = σ (unit j) (σ (unit i) ω) := by
          intro ω
          rw [← hσadd, ← hσadd, add_comm]
        funext ω
        rw [congrFun (bLimsup_comp_apply hcomm G) ω, hinv j hjs]


/-- The box `∏_{i∈s} [0, mᵢ) ⊂ ℤ^d` with integer corners; `anchoredBox c N` is this with
`mᵢ = ⌈N cᵢ⌉`. -/
noncomputable def intBox {d : ℕ} (s : Finset (Fin d)) (m : Fin d → ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => if i ∈ s then Finset.Ico (0 : ℤ) (m i : ℤ) else {0}

/-- The `ℕ`-indexed box sum (`boxGridSet`) is the `ℤ`-indexed box sum (`intBox`) under
`natToSite`. -/
theorem sum_boxGridSet_eq_sum_intBox {d : ℕ} (s : Finset (Fin d)) (m : Fin d → ℕ)
    (F : Site d → ℝ) :
    ∑ w ∈ boxGridSet s m, F (natToSite w) = ∑ x ∈ intBox s m, F x := by
  refine Finset.sum_nbij' (fun w => natToSite w) (fun x i => (x i).toNat) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [boxGridSet, Fintype.mem_piFinset] at hw
    rw [intBox, Fintype.mem_piFinset]
    intro i
    have hwi := hw i
    by_cases hi : i ∈ s
    · rw [if_pos hi] at hwi ⊢
      exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by
        simp only [natToSite]
        exact_mod_cast (Finset.mem_range.mp hwi)⟩
    · rw [if_neg hi] at hwi ⊢
      rw [Finset.mem_singleton] at hwi ⊢
      simp [natToSite, hwi]
  · intro x hx
    rw [intBox, Fintype.mem_piFinset] at hx
    rw [boxGridSet, Fintype.mem_piFinset]
    intro i
    have hxi := hx i
    by_cases hi : i ∈ s
    · rw [if_pos hi] at hxi ⊢
      rw [Finset.mem_range]
      exact (Int.toNat_lt (Finset.mem_Ico.mp hxi).1).mpr (Finset.mem_Ico.mp hxi).2
    · rw [if_neg hi] at hxi ⊢
      rw [Finset.mem_singleton] at hxi ⊢
      rw [hxi]; rfl
  · intro w _hw
    funext i
    exact Int.toNat_natCast (w i)
  · intro x hx
    rw [intBox, Fintype.mem_piFinset] at hx
    funext i
    have hxi := hx i
    by_cases hi : i ∈ s
    · rw [if_pos hi] at hxi
      exact Int.toNat_of_nonneg (Finset.mem_Ico.mp hxi).1
    · rw [if_neg hi] at hxi
      rw [Finset.mem_singleton] at hxi
      simp [natToSite, hxi]
  · intro w _hw; rfl


/-- `anchoredBox c N` is the integer box `intBox univ (fun i => ⌈N cᵢ⌉.toNat)` when
`c ≥ 0`. -/
theorem anchoredBox_eq_intBox {d : ℕ} {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) (N : ℕ) :
    anchoredBox c N = intBox Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) := by
  unfold anchoredBox intBox
  congr 1
  funext i
  rw [if_pos (Finset.mem_univ i),
    Int.toNat_of_nonneg (Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg N) (hc i)))]

omit [MeasurableSpace Ω] in
/-- The box sum is the box average times the box volume. -/
theorem sum_boxGridSet_eq_boxAvg_mul {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ)
    (s : Finset (Fin d)) (m : Fin d → ℕ) (ω : Ω) :
    ∑ w ∈ boxGridSet s m, h (σ (natToSite w) ω) =
      boxAvg σ h s m ω * ∏ i ∈ s, (m i : ℝ) := by
  rw [boxAvg]
  rcases eq_or_ne (∏ i ∈ s, (m i : ℝ)) 0 with hP | hP
  · obtain ⟨i, hi, hmi⟩ := Finset.prod_eq_zero_iff.mp hP
    have hmi0 : m i = 0 := by exact_mod_cast hmi
    rw [hP, div_zero, zero_mul, Finset.sum_eq_zero]
    intro w hw
    have hmem : w i ∈ (if i ∈ s then Finset.range (m i) else {0}) :=
      Fintype.mem_piFinset.mp hw i
    rw [if_pos hi, Finset.mem_range] at hmem
    omega
  · rw [div_mul_cancel₀ _ hP]

/-- `⌈N c⌉.toNat → ∞` for `c > 0`. -/
theorem tendsto_ceil_toNat_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => ⌈(N : ℝ) * c⌉.toNat) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  have hx : Tendsto (fun N : ℕ => (N : ℝ) * c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc
  filter_upwards [Filter.tendsto_atTop.mp hx ((b : ℝ) + 1)] with N hN
  have hxN : ((b + 1 : ℕ) : ℝ) ≤ (N : ℝ) * c := by
    push_cast; linarith
  have hb : (b : ℤ) ≤ ⌈(N : ℝ) * c⌉ := by
    have h1 : ((b + 1 : ℕ) : ℝ) ≤ ((⌈(N : ℝ) * c⌉ : ℤ) : ℝ) :=
      le_trans hxN (Int.le_ceil _)
    have h2 : ((b + 1 : ℕ) : ℤ) ≤ ⌈(N : ℝ) * c⌉ := by exact_mod_cast h1
    omega
  have := Int.toNat_le_toNat hb
  rwa [Int.toNat_natCast] at this

/-- For `a ≥ 0`, the real value of `⌈a⌉.toNat` is `⌈a⌉`. -/
theorem ceil_toNat_cast (a : ℝ) (ha : 0 ≤ a) :
    (((⌈a⌉).toNat : ℕ) : ℝ) = ((⌈a⌉ : ℤ) : ℝ) := by
  have h : (((⌈a⌉).toNat : ℕ) : ℤ) = ⌈a⌉ := Int.toNat_of_nonneg (Int.ceil_nonneg ha)
  rw [← h]
  exact_mod_cast rfl

/-- `(⌈N c⌉.toNat)/N → c` for `c ≥ 0`. -/
theorem tendsto_ceil_toNat_div {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ => (((⌈(N : ℝ) * c⌉).toNat : ℕ) : ℝ) / (N : ℝ)) atTop
      (𝓝 c) := by
  have hcN : ∀ N : ℕ, 0 ≤ (N : ℝ) * c := fun N => mul_nonneg (Nat.cast_nonneg N) hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using
      tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [le_div_iff₀ hNpos, ceil_toNat_cast _ (hcN N)]
    have := Int.le_ceil ((N : ℝ) * c)
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [div_le_iff₀ hNpos, ceil_toNat_cast _ (hcN N)]
    have hlt := Int.ceil_lt_add_one ((N : ℝ) * c)
    have hexp : (c + (N : ℝ)⁻¹) * (N : ℝ) = (N : ℝ) * c + 1 := by
      rw [add_mul, inv_mul_cancel₀ (ne_of_gt hNpos), mul_comm c (N : ℝ)]
    rw [hexp]
    linarith

/-- The volume ratio `(∏ᵢ ⌈N cᵢ⌉.toNat) / N^d → ∏ᵢ cᵢ` for `c ≥ 0`. -/
theorem tendsto_prod_ceil_toNat_div_pow {d : ℕ} {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) :
    Tendsto (fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) / (N : ℝ) ^ d) atTop
      (𝓝 (∏ i, c i)) := by
  have hfac : Tendsto (fun N : ℕ => ∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ) / (N : ℝ)) atTop
      (𝓝 (∏ i, c i)) :=
    tendsto_finsetProd Finset.univ fun i _ => tendsto_ceil_toNat_div (hc i)
  have heq : ∀ N : ℕ, (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ) / (N : ℝ)) =
      (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) / (N : ℝ) ^ d := by
    intro N
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact hfac.congr' (Filter.Eventually.of_forall heq)


omit [MeasurableSpace Ω] in
/-- The constant-length box average is the grid (cube) average. -/
theorem boxAvg_univ_const_eq_gridAvg {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ)
    (N : ℕ) :
    boxAvg σ h Finset.univ (fun _ => N) = gridAvg σ h Finset.univ N := by
  have hset : boxGridSet Finset.univ (fun _ : Fin d => N) = gridSet d Finset.univ N := rfl
  have hprod : (∏ _i ∈ (Finset.univ : Finset (Fin d)), (N : ℝ)) = (N : ℝ) ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  funext ω
  rw [boxAvg, gridAvg, hset, hprod]
  simp


omit [MeasurableSpace Ω] in
/-- `z + unit i` is `z` with coordinate `i` increased by one. -/
theorem add_unit_eq_update {d : ℕ} (z : Site d) (i : Fin d) :
    z + unit i = Function.update z i (z i + 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [unit, Function.update_self]
  · rw [Pi.add_apply, Function.update_of_ne hj]
    have h0 : unit i j = 0 := by simp [unit, hj]
    rw [h0, add_zero]

omit [MeasurableSpace Ω] in
/-- `z - unit i` is `z` with coordinate `i` decreased by one. -/
theorem sub_unit_eq_update {d : ℕ} (z : Site d) (i : Fin d) :
    z - unit i = Function.update z i (z i - 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [unit, Function.update_self]
  · rw [Pi.sub_apply, Function.update_of_ne hj]
    have h0 : unit i j = 0 := by simp [unit, hj]
    rw [h0, sub_zero]

omit [MeasurableSpace Ω] in
/-- Updating a coordinate of `z` and adding back `unit i` recovers `z`. -/
theorem update_sub_one_add_unit {d : ℕ} (z : Site d) (i : Fin d) :
    Function.update z i (z i - 1) + unit i = z := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [unit, Function.update_self]
  · rw [Pi.add_apply, Function.update_of_ne hj]
    have h0 : unit i j = 0 := by simp [unit, hj]
    rw [h0, add_zero]

omit [MeasurableSpace Ω] in
/-- The `ℓ¹` norm of `Function.update z i c`. -/
theorem sum_natAbs_update {d : ℕ} (z : Site d) (i : Fin d) (c : ℤ) :
    (∑ j, (Function.update z i c j).natAbs)
      = (∑ j ∈ Finset.univ.erase i, (z j).natAbs) + c.natAbs := by
  rw [← Finset.sum_erase_add _ (fun j => (Function.update z i c j).natAbs) (Finset.mem_univ i)]
  congr 1
  · exact Finset.sum_congr rfl
      (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  · rw [Function.update_self]

omit [MeasurableSpace Ω] in
/-- The `ℓ¹` norm of `z` itself, in the same shape. -/
theorem sum_natAbs_eq_erase_add {d : ℕ} (z : Site d) (i : Fin d) :
    (∑ j, (z j).natAbs) = (∑ j ∈ Finset.univ.erase i, (z j).natAbs) + (z i).natAbs := by
  rw [← Finset.sum_erase_add _ (fun j => (z j).natAbs) (Finset.mem_univ i)]

omit [MeasurableSpace Ω] in
/-- **Invariance of a limit under the generators extends to the whole `ℤ^d`-action.**  If `σ` is
additive, `σ 0 = id`, and a function `G` is invariant under every generator `σ (unit j)`,
then it is invariant under `σ z` for every `z : ℤ^d`. -/
theorem comp_sigma_eq_of_comp_unit_eq {d : ℕ} {G : Ω → ℝ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (hσid : ∀ ω, σ 0 ω = ω)
    (hinv : ∀ j : Fin d, G ∘ σ (unit j) = G) (z : Site d) : G ∘ σ z = G := by
  have hzero : σ 0 = id := funext hσid
  have hcomp : ∀ j : Fin d, σ (unit j) ∘ σ (-(unit j)) = σ 0 := by
    intro j
    funext ω
    show σ (unit j) (σ (-(unit j)) ω) = σ 0 ω
    rw [← hσadd (unit j) (-(unit j)) ω, add_neg_cancel]
  have hneg : ∀ j : Fin d, G ∘ σ (-(unit j)) = G := by
    intro j
    exact (calc G = G ∘ id := (Function.comp_id G).symm
      _ = G ∘ (σ (unit j) ∘ σ (-(unit j))) := by rw [hcomp j, hzero]
      _ = (G ∘ σ (unit j)) ∘ σ (-(unit j)) := by rw [Function.comp_assoc]
      _ = G ∘ σ (-(unit j)) := by rw [hinv j]).symm
  suffices H : ∀ n : ℕ, ∀ z : Site d, (∑ i, (z i).natAbs) = n → G ∘ σ z = G by
    exact H _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hz
    by_cases h0 : z = 0
    · rw [h0, hzero, Function.comp_id]
    · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact h0 (funext fun i => h i)
      have hnorm1 : (z i + 1).natAbs < (z i).natAbs ∨ (z i - 1).natAbs < (z i).natAbs := by
        rcases lt_or_gt_of_ne hi with h | h
        · left
          have h1 : (z i + 1).natAbs = (-(z i) - 1).natAbs := by
            rw [show -(z i) - 1 = -(z i + 1) by ring, Int.natAbs_neg]
          have h2 : (z i).natAbs = (-(z i)).natAbs := (Int.natAbs_neg (z i)).symm
          rw [h1, h2]
          exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
        · right
          exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
      rcases hnorm1 with hup | hdown
      · -- z i < 0 : step down to w := z + unit i
        have hnorm : (∑ j, (Function.update z i (z i + 1) j).natAbs) < n := by
          have hsum : (∑ j, (z j).natAbs)
              = (∑ j ∈ Finset.univ.erase i, (z j).natAbs) + (z i).natAbs :=
            sum_natAbs_eq_erase_add z i
          rw [sum_natAbs_update, ← hz, hsum]
          exact add_lt_add_right hup _
        set w : Site d := Function.update z i (z i + 1) with hwdef
        have hw : G ∘ σ w = G := ih _ hnorm w rfl
        have hsw : ∀ ω' : Ω, σ w ω' = σ z (σ (unit i) ω') := by
          intro ω'
          rw [hwdef, ← add_unit_eq_update z i]
          exact hσadd z (unit i) ω'
        have hid : ∀ ω' : Ω, σ (unit i) (σ (-(unit i)) ω') = ω' := by
          intro ω'
          rw [← hσadd (unit i) (-(unit i)) ω', add_neg_cancel, hzero]
          rfl
        funext ω
        calc G (σ z ω) = G (σ z (σ (unit i) (σ (-(unit i)) ω))) := by rw [hid ω]
          _ = G (σ w (σ (-(unit i)) ω)) := by rw [← hsw (σ (-(unit i)) ω)]
          _ = G (σ (-(unit i)) ω) := congrFun hw (σ (-(unit i)) ω)
          _ = G ω := congrFun (hneg i) ω
      · -- z i > 0 : step down to w := z - unit i
        have hnorm : (∑ j, (Function.update z i (z i - 1) j).natAbs) < n := by
          have hsum : (∑ j, (z j).natAbs)
              = (∑ j ∈ Finset.univ.erase i, (z j).natAbs) + (z i).natAbs :=
            sum_natAbs_eq_erase_add z i
          rw [sum_natAbs_update, ← hz, hsum]
          exact add_lt_add_right hdown _
        set w : Site d := Function.update z i (z i - 1) with hwdef
        have hw : G ∘ σ w = G := ih _ hnorm w rfl
        have hsz : ∀ ω' : Ω, σ z ω' = σ w (σ (unit i) ω') := by
          intro ω'
          rw [show z = w + unit i by rw [hwdef, update_sub_one_add_unit]]
          exact hσadd w (unit i) ω'
        funext ω
        calc G (σ z ω) = G (σ w (σ (unit i) ω)) := by rw [hsz ω]
          _ = G (σ (unit i) ω) := congrFun hw (σ (unit i) ω)
          _ = G ω := congrFun (hinv i) ω

/-- **An invariant function is a.e. constant when the invariant sets are trivial.**  If `G` is
measurable and integrable, invariant under the whole action, and every invariant measurable set has
measure `0` or `1`, then `G = ∫ G` a.e. -/
theorem ae_eq_const_of_forall_invariant {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (herg : ∀ A : Set Ω, MeasurableSet A → (∀ z : Site d, σ z ⁻¹' A = A) →
      μ A = 0 ∨ μ A = 1)
    {G : Ω → ℝ} (hGm : Measurable G) (hGint : Integrable G μ)
    (hinv : ∀ z : Site d, G ∘ σ z = G) :
    G =ᵐ[μ] Function.const Ω (∫ ω, G ω ∂μ) := by
  set c : ℝ := ∫ ω, G ω ∂μ with hc
  have hpre : ∀ (q : ℝ) (z : Site d), σ z ⁻¹' {ω | q < G ω} = {ω | q < G ω} := by
    intro q z
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [show G (σ z ω) = G ω from congrFun (hinv z) ω]
  have hpre' : ∀ (q : ℝ) (z : Site d), σ z ⁻¹' {ω | G ω < q} = {ω | G ω < q} := by
    intro q z
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [show G (σ z ω) = G ω from congrFun (hinv z) ω]
  have hpos : μ {ω | c < G ω} = 0 := by
    rcases herg _ (measurableSet_lt measurable_const hGm) (fun z => hpre c z) with h0 | h1
    · exact h0
    · exfalso
      have hnull : μ ({ω | c < G ω} : Set Ω)ᶜ = 0 := by
        rw [measure_compl (measurableSet_lt measurable_const hGm) (measure_ne_top μ _), h1]
        simp
      have hfnn : 0 ≤ᵐ[μ] fun ω => G ω - c := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
        show (0 : ℝ) ≤ G ω - c
        linarith
      have hf0 : ∫ ω, (G ω - c) ∂μ = 0 := by
        rw [integral_sub hGint (integrable_const c), integral_const, hc]
        simp
      have hfae := (integral_eq_zero_iff_of_nonneg_ae hfnn (hGint.sub (integrable_const c))).1 hf0
      have hzero : μ {ω | c < G ω} = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hfae] with ω hω
        simp only [Pi.zero_apply, sub_eq_zero] at hω
        simp only [Set.mem_setOf_eq, not_lt, hω, le_refl]
      rw [hzero] at h1
      exact zero_ne_one h1
  have hneg : μ {ω | G ω < c} = 0 := by
    rcases herg _ (measurableSet_lt hGm measurable_const) (fun z => hpre' c z) with h0 | h1
    · exact h0
    · exfalso
      have hnull : μ ({ω | G ω < c} : Set Ω)ᶜ = 0 := by
        rw [measure_compl (measurableSet_lt hGm measurable_const) (measure_ne_top μ _), h1]
        simp
      have hfnn : 0 ≤ᵐ[μ] fun ω => c - G ω := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
        show (0 : ℝ) ≤ c - G ω
        linarith
      have hf0 : ∫ ω, (c - G ω) ∂μ = 0 := by
        rw [integral_sub (integrable_const c) hGint, integral_const, hc]
        simp
      have hfae := (integral_eq_zero_iff_of_nonneg_ae hfnn ((integrable_const c).sub hGint)).1 hf0
      have hzero : μ {ω | G ω < c} = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hfae] with ω hω
        simp only [Pi.zero_apply, sub_eq_zero] at hω
        simp only [Set.mem_setOf_eq, not_lt, hω, le_refl]
      rw [hzero] at h1
      exact zero_ne_one h1
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpos, measure_eq_zero_iff_ae_notMem.1 hneg]
    with ω hp hn
  simp only [Set.mem_setOf_eq, not_lt] at hp hn
  exact le_antisymm hp hn

/-- **The anchored-box almost-everywhere ergodic theorem (bounded `h`).**  For a measure-preserving
additive action of `ℤ^d` and a bounded measurable `h`, there is a bounded measurable limit `G`
with `∫ G = ∫ h` such that, for every `c ≥ 0`, the normalized anchored-box average converges
a.e.
to `(∏ᵢ cᵢ) G`, where `G` is the (sequence-independent) box limit produced by the coordinate
iteration.  This is the cube-to-box step of the multiparameter pointwise ergodic theorem, proved
without a maximal inequality. -/
theorem exists_ae_tendsto_anchoredBox_with_integral {d : ℕ} {σ : Site d → Ω → Ω}
    {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧
      (∀ j : Fin d, G ∘ σ (unit j) = G) ∧
      ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ anchoredBox c N, h (σ x ω)) atTop (𝓝 ((∏ i, c i) * G ω)) := by
  obtain ⟨G, hGm, hGb, hGconv, hinv_gen⟩ :=
    exists_ae_tendsto_boxAvg hσ hσadd hh hM hb Finset.univ
  have hinvg : ∀ j : Fin d, G ∘ σ (unit j) = G := fun j => hinv_gen j (Finset.mem_univ j)
  have hGint : ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ := by
    have hconv : ∀ᵐ ω ∂μ, Tendsto (fun N => gridAvg σ h Finset.univ N ω) atTop
        (𝓝 (G ω)) := by
      have h := hGconv (fun N _ => N) (fun i _ => tendsto_id)
      simpa only [boxAvg_univ_const_eq_gridAvg] using h
    have h1 : Tendsto (fun N : ℕ => ∫ ω, gridAvg σ h Finset.univ N ω ∂μ) atTop
        (𝓝 (∫ ω, G ω ∂μ)) :=
      tendsto_integral_of_dominated_convergence (fun _ : Ω => M)
        (fun N => (measurable_gridAvg hσ hh Finset.univ N).aestronglyMeasurable)
        (integrable_const M)
        (fun N => by
          filter_upwards with ω
          rw [Real.norm_eq_abs]
          exact abs_gridAvg_le σ h hM hb Finset.univ N ω) hconv
    have hEq : (fun N : ℕ => ∫ ω, gridAvg σ h Finset.univ N ω ∂μ) =ᶠ[atTop]
        fun _ : ℕ => ∫ ω, h ω ∂μ :=
      eventually_atTop.mpr ⟨1, fun n hn => integral_gridAvg_univ_eq_integral hσ hh hb hn⟩
    exact (tendsto_nhds_unique tendsto_const_nhds (Tendsto.congr' hEq h1)).symm
  refine ⟨G, hGm, hGb, hinvg, hGint, ?_⟩
  by_cases hpos : ∀ i, 0 < c i
  · have hmi : ∀ i, Tendsto (fun N : ℕ => ⌈(N : ℝ) * c i⌉.toNat) atTop atTop :=
      fun i => tendsto_ceil_toNat_atTop (hpos i)
    have hconv := hGconv (fun N i => ⌈(N : ℝ) * c i⌉.toNat) (fun i _ => hmi i)
    have hscale : Tendsto (fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) *
        ((N : ℝ) ^ (-(d : ℝ)))) atTop (𝓝 (∏ i, c i)) := by
      have h := tendsto_prod_ceil_toNat_div_pow hc
      have heq : (fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) *
          ((N : ℝ) ^ (-(d : ℝ)))) =
          fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) / (N : ℝ) ^ d := by
        funext N
        rw [Real.rpow_neg (Nat.cast_nonneg N) (d : ℝ), Real.rpow_natCast (N : ℝ) d,
          div_eq_mul_inv]
      rw [heq]; exact h
    filter_upwards [hconv] with ω hω
    have heq : (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, h (σ x ω)) =
        fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) * ((N : ℝ) ^ (-(d : ℝ))) *
            boxAvg σ h Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω := by
      funext N
      rw [anchoredBox_eq_intBox hc N,
        ← sum_boxGridSet_eq_sum_intBox Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat)
            (fun x => h (σ x ω)),
        sum_boxGridSet_eq_boxAvg_mul σ h Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω]
      ring
    rw [heq]
    exact hscale.mul hω
  · simp only [not_forall, not_lt] at hpos
    obtain ⟨i, hi⟩ := hpos
    have hci : c i = 0 := le_antisymm hi (hc i)
    filter_upwards with ω
    have hemp : ∀ N : ℕ, anchoredBox c N = ∅ := by
      intro N
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_anchoredBox] at hx
      have := hx i
      rw [hci, mul_zero, Int.ceil_zero, Finset.mem_Ico] at this
      omega
    have hprod : (∏ i, c i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hci
    have hconst : (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
        ∑ x ∈ anchoredBox c N, h (σ x ω)) = fun _ : ℕ => 0 := by
      funext N
      rw [hemp N, Finset.sum_empty, mul_zero]
    rw [hconst, hprod, zero_mul]
    exact tendsto_const_nhds

/-- **Ergodic anchored-box almost-everywhere ergodic theorem.**  Adding `σ 0 = id` and the
triviality of the invariant sets to the anchored-box theorem upgrades the limit from the abstract
box limit `G` to the constant `∫ h`. -/
theorem exists_ae_tendsto_anchoredBox_ergodic {d : ℕ} {σ : Site d → Ω → Ω}
    {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (hσid : ∀ ω, σ 0 ω = ω)
    (herg : ∀ A : Set Ω, MeasurableSet A → (∀ z : Site d, σ z ⁻¹' A = A) →
      μ A = 0 ∨ μ A = 1)
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
        ∑ x ∈ anchoredBox c N, h (σ x ω)) atTop
        (𝓝 ((∏ i, c i) * ∫ ω, h ω ∂μ)) := by
  obtain ⟨G, hGm, hGb, hinvg, hGint, hconv⟩ :=
    exists_ae_tendsto_anchoredBox_with_integral hσ hσadd hh hM hb hc
  have hinv : ∀ z : Site d, G ∘ σ z = G :=
    fun z => comp_sigma_eq_of_comp_unit_eq hσadd hσid (fun j => hinvg j) z
  have hGint' : Integrable G μ := Integrable.of_bound hGm.aestronglyMeasurable M (by
    filter_upwards with x; rw [Real.norm_eq_abs]; exact hGb x)
  have hconst := ae_eq_const_of_forall_invariant herg hGm hGint' hinv
  filter_upwards [hconv, hconst] with ω hω hcω
  rw [hcω, hGint] at hω
  exact hω


end LatticeProb
