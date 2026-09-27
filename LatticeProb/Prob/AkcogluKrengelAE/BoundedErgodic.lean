import LatticeProb.Prob.AkcogluKrengelAE.BoxCombinatorics

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# The pointwise ergodic theorem along cubes for bounded functions (Step 2)

A multiparameter pointwise ergodic theorem for bounded functions along cubes, for any
measure-preserving additive action `σ` of `ℤ^d`, obtained by iterating the one-parameter Birkhoff
theorem of the library one coordinate at a time. Boundedness makes the iteration elementary: if `g n
→ G` a.e. with `|g n| ≤ M`, the Birkhoff averages of `g n` converge to the Birkhoff limit of `G`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Iterating the action by `unit i` for `j` steps from `z` agrees with composing the action at `z`
with the `j`-fold iterate of `σ (unit i)`. -/
theorem action_add_smul_unit_eq_iterate {d : ℕ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (z : Site d) (i : Fin d) (ω : Ω) (j : ℕ) :
    σ (z + (j : ℤ) • unit i) ω = (σ (unit i))^[j] (σ z ω) := by
  revert ω
  induction j with
  | zero => intro ω; simp
  | succ j ih =>
    intro ω
    have hcomm : σ z (σ (unit i) ω) = σ (unit i) (σ z ω) :=
      (hσadd z (unit i) ω).symm.trans
        ((congrArg (fun w => σ w ω) (add_comm z (unit i))).trans (hσadd (unit i) z ω))
    rw [Nat.cast_succ, add_smul, one_smul]
    rw [show z + ((j : ℤ) • unit i + unit i) = z + (j : ℤ) • unit i + unit i by abel]
    rw [hσadd (z + (j : ℤ) • unit i) (unit i) ω]
    rw [ih (σ (unit i) ω), hcomm, Function.iterate_succ_apply]


omit [MeasurableSpace Ω] in
/-- The action at `z` commutes with the `j`-fold iterate of the action at `u`. -/
theorem action_commute_iterate {d : ℕ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (z u : Site d) (j : ℕ) (ω : Ω) :
    σ z ((σ u)^[j] ω) = (σ u)^[j] (σ z ω) := by
  exact (Function.Commute.iterate_right (f := σ z) (g := σ u) (by
      intro ω'; rw [← hσadd z u ω', ← hσadd u z ω', add_comm]) j) ω


/-- Updating coordinate `i` of a grid point `w` (zero there) to `j` shifts `natToSite w` by `j`
units in direction `i`. -/
theorem natToSite_update_eq_add_smul_unit {d : ℕ} (w : Fin d → ℕ) (i : Fin d) (hw : w i = 0)
    (j : ℕ) :
    natToSite (Function.update w i j) = natToSite w + (j : ℤ) • unit i := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [natToSite, unit,   hw]
  · simp [natToSite, unit,   hl]


/-- The numerator of `gridAvg` over `insert i s` splits, via the grid reindexing
`sum_gridSet_insert` and the additivity of the action, into a sum over the range of the new
coordinate of sums over `gridSet d s n`. -/
theorem sum_gridSet_insert_eq_sum_range_sum_iterate {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (n : ℕ) (ω : Ω) :
    ∑ w ∈ gridSet d (insert i s) n, h (σ (natToSite w) ω) =
      ∑ k ∈ Finset.range n, ∑ w ∈ gridSet d s n,
        h (σ (natToSite w) ((σ (unit i))^[k] ω)) := by
  rw [sum_gridSet_insert s i hi n (fun w => h (σ (natToSite w) ω)), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro w hw
  rw [natToSite_update_eq_add_smul_unit w i (gridSet_apply_eq_zero_of_notMem hw hi) j,
      action_add_smul_unit_eq_iterate hσadd (natToSite w) i ω j,
      ← action_commute_iterate hσadd (natToSite w) (unit i) j ω]

/-- The grid average over `insert i s` equals the Birkhoff average, along the action of `unit i`, of
the grid average over `s`. -/
theorem gridAvg_insert_eq_bAvg_gridAvg {d : ℕ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (n : ℕ) (ω : Ω) :
    gridAvg σ h (insert i s) n ω = bAvg (σ (unit i)) (gridAvg σ h s n) n ω := by
  simp only [gridAvg, bAvg, birkhoffSum]
  rw [Finset.card_insert_of_notMem hi, pow_succ, sum_gridSet_insert_eq_sum_range_sum_iterate hσadd h
      s i hi n ω]
  rw [← Finset.sum_div, div_div]


/-- The partial grid `gridSet d s n` has `n ^ s.card` points. -/
theorem card_gridSet_eq_pow_card {d : ℕ} (s : Finset (Fin d)) (n : ℕ) :
    (gridSet d s n).card = n ^ s.card := by
  unfold gridSet
  rw [Fintype.card_piFinset]
  have hcoe : ∀ i : Fin d, (if i ∈ s then Finset.range n else ({0} : Finset ℕ)).card
      = (if i ∈ s then n else 1) := by
    intro i
    by_cases hi : i ∈ s <;> simp [hi]
  simp only [hcoe]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

omit [MeasurableSpace Ω] in
/-- A sum of a function bounded by `M` over the partial grid `gridSet d s n` is bounded in absolute
value by `n ^ s.card * M`. -/
theorem abs_sum_gridSet_le {d : ℕ} {σ : Site d → Ω → Ω} {h : Ω → ℝ} {M : ℝ}
    (hh : ∀ x, |h x| ≤ M) (s : Finset (Fin d)) (n : ℕ) (ω : Ω) :
    |∑ w ∈ gridSet d s n, h (σ (natToSite w) ω)| ≤ (n : ℝ) ^ s.card * M := by
  have hconst : (∑ _w ∈ gridSet d s n, M) = (n : ℝ) ^ s.card * M := by
    rw [Finset.sum_const, card_gridSet_eq_pow_card, nsmul_eq_mul, Nat.cast_pow]
  calc |∑ w ∈ gridSet d s n, h (σ (natToSite w) ω)|
      ≤ ∑ w ∈ gridSet d s n, |h (σ (natToSite w) ω)| :=
        Finset.abs_sum_le_sum_abs (fun w => h (σ (natToSite w) ω)) (gridSet d s n)
    _ ≤ ∑ _w ∈ gridSet d s n, M := Finset.sum_le_sum fun w _ => hh (σ (natToSite w) ω)
    _ = (n : ℝ) ^ s.card * M := hconst

omit [MeasurableSpace Ω] in
/-- The grid average `gridAvg σ h s n` is bounded in absolute value by the bound `M` on `h`. -/
theorem abs_gridAvg_le {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hh : ∀ x, |h x| ≤ M) (s : Finset (Fin d)) (n : ℕ) (ω : Ω) :
    |gridAvg σ h s n ω| ≤ M := by
  rw [gridAvg]
  have hDn : 0 ≤ (n : ℝ) ^ s.card := pow_nonneg (Nat.cast_nonneg n) _
  rw [abs_div, abs_of_nonneg hDn]
  by_cases hD : (n : ℝ) ^ s.card = 0
  · rw [hD, div_zero]
    exact hM
  · have hDp : 0 < (n : ℝ) ^ s.card := lt_of_le_of_ne hDn (Ne.symm hD)
    rw [div_le_iff₀ hDp]
    refine le_trans (abs_sum_gridSet_le hh s n ω) ?_
    rw [mul_comm]


/-- `gridAvg σ h s n` is measurable when `h` is measurable and each `σ z` is measurable. -/
theorem measurable_gridAvg {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) {h : Ω → ℝ} (hh : Measurable h)
    (s : Finset (Fin d)) (n : ℕ) : Measurable (gridAvg σ h s n) := by
  unfold gridAvg
  exact (Finset.measurable_sum _ (fun w _ => hh.comp (hσ (natToSite w)).measurable)).div_const _


/-- For a measure-preserving map, the integral of the Birkhoff average `bAvg T h n` equals the
integral of `h`, for every `n ≥ 1`. -/
theorem integral_bAvg_eq_integral {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {h : Ω → ℝ} (hInt : Integrable h μ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, bAvg T h n x ∂μ = ∫ x, h x ∂μ := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : ∀ k ∈ Finset.range n, Integrable (fun x => h (T^[k] x)) μ := fun k _ =>
    ((hT.iterate k).integrable_comp hInt.aestronglyMeasurable).mpr hInt
  have hid : (fun x => bAvg T h n x) = fun x => (∑ k ∈ Finset.range n, h (T^[k] x)) / (n : ℝ) := by
    funext x
    simp only [bAvg, birkhoffSum]
  rw [hid, integral_div, integral_finsetSum _ hterm]
  rw [Finset.sum_congr rfl (fun k _ => integral_comp_iterate hT hInt k)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hn0]

/-- For a bounded measurable `h`, the integral of the Birkhoff limsup `bLimsup T h` equals the
integral of `h`. -/
theorem integral_bLimsup_eq_integral {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |h x| ≤ M) :
    ∫ x, bLimsup T h x ∂μ = ∫ x, h x ∂μ := by
  have hInt : Integrable h μ :=
    Integrable.of_bound hh.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hb x)
  have hbdd : ∀ n x, |bAvg T h n x| ≤ M := fun n x => abs_bAvg_le hM hb n x
  have hae : ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T h n x) atTop (𝓝 (bLimsup T h x)) :=
      ae_tendsto_bLimsup hT hh hInt
  have hlim : Tendsto (fun n => ∫ x, bAvg T h n x ∂μ) atTop (𝓝 (∫ x, bLimsup T h x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun n => (measurable_bAvg hT.measurable hh n).aestronglyMeasurable)
      (integrable_const M)
      (fun n => Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hbdd n x)
      hae
  refine tendsto_nhds_unique hlim ?_
  exact Tendsto.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => (integral_bAvg_eq_integral hT
      hInt hn).symm⟩) tendsto_const_nhds


omit [MeasurableSpace Ω] in
/-- If `0 ≤ g ≤ g' ≤ M` pointwise, then `bLimsup T g` and `bLimsup T g'` are ordered the same way
and lie in `[0, M]`. -/
theorem bLimsup_nonneg_le_of_le {T : Ω → Ω} {g g' : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ M) (hg' : ∀ x, 0 ≤ g' x ∧ g' x ≤ M) (hle : ∀ x, g x ≤ g' x)
    (ω : Ω) :
    0 ≤ bLimsup T g ω ∧ bLimsup T g ω ≤ bLimsup T g' ω ∧ bLimsup T g' ω ≤ M := by
  have hgabs : ∀ x, |g x| ≤ M :=
    fun x => abs_le.mpr ⟨(neg_nonpos.mpr hM).trans (hg x).1, (hg x).2⟩
  have hg'abs : ∀ x, |g' x| ≤ M :=
    fun x => abs_le.mpr ⟨(neg_nonpos.mpr hM).trans (hg' x).1, (hg' x).2⟩
  have hg_le : ∀ n, bAvg T g n ω ≤ M := fun n => (abs_le.mp (abs_bAvg_le hM hgabs n ω)).2
  have hg'_le : ∀ n, bAvg T g' n ω ≤ M := fun n => (abs_le.mp (abs_bAvg_le hM hg'abs n ω)).2
  have hg'_ge : ∀ n, -M ≤ bAvg T g' n ω := fun n => (abs_le.mp (abs_bAvg_le hM hg'abs n ω)).1
  have hg_nonneg : ∀ n, 0 ≤ bAvg T g n ω := fun n =>
    div_nonneg (Finset.sum_nonneg fun k _ => (hg _).1) (Nat.cast_nonneg n)
  have hmono : ∀ n, bAvg T g n ω ≤ bAvg T g' n ω := fun n =>
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun k _ => hle _) (Nat.cast_nonneg n)
  refine ⟨?_, ?_, ?_⟩
  · simp only [bLimsup]
    exact le_limsup_of_frequently_le (Frequently.of_forall hg_nonneg) (isBoundedUnder_le_of hg_le)
  · simp only [bLimsup]
    exact limsup_le_limsup (Eventually.of_forall hmono)
      (isBoundedUnder_ge_of hg_nonneg).isCoboundedUnder_le (isBoundedUnder_le_of hg'_le)
  · simp only [bLimsup]
    exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hg'_ge) (Eventually.of_forall hg'_le)


omit [MeasurableSpace Ω] in
/-- `bLimsup T h` is bounded in absolute value by any bound `M` on `h`. -/
theorem abs_bLimsup_le_of_abs_le {T : Ω → Ω} {h : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (ω : Ω) : |bLimsup T h ω| ≤ M := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [bLimsup]
    refine le_limsup_of_frequently_le ?_ ?_
    · exact (Eventually.of_forall fun n => (abs_le.mp (abs_bAvg_le hM hb n ω)).1).frequently
    · exact isBoundedUnder_le_of fun n => (abs_le.mp (abs_bAvg_le hM hb n ω)).2
  · rw [bLimsup]
    refine limsup_le_of_le ?_ ?_
    · exact (isBoundedUnder_ge_of fun n => (abs_le.mp (abs_bAvg_le hM hb n
        ω)).1).isCoboundedUnder_le
    · exact Eventually.of_forall fun n => (abs_le.mp (abs_bAvg_le hM hb n ω)).2


omit [MeasurableSpace Ω] in
/-- A nonnegative, pointwise antitone sequence of functions converges pointwise to its infimum. -/
theorem tendsto_ciInf_of_antitone_nonneg {E : ℕ → Ω → ℝ} (hb : ∀ N x, 0 ≤ E N x)
    (hanti : ∀ N x, E (N + 1) x ≤ E N x) (x : Ω) :
    Tendsto (fun N => E N x) atTop (𝓝 (⨅ N, E N x)) := by
  exact tendsto_atTop_ciInf (antitone_nat_of_succ_le fun N => hanti N x)
    ⟨0, fun _ ⟨N, hN⟩ => hN ▸ hb N x⟩

/-- If a bounded, nonnegative sequence of measurable functions has integrals tending to `0`, its
pointwise infimum is integrable, nonnegative, and has integral `0`. -/
theorem integral_ciInf_eq_zero_of_tendsto_zero {μ : Measure Ω} [IsProbabilityMeasure μ] {E :
    ℕ → Ω → ℝ} {M : ℝ}
    (hE : ∀ N, Measurable (E N)) (hb : ∀ N x, 0 ≤ E N x ∧ E N x ≤ M)
    (hint : Tendsto (fun N => ∫ x, E N x ∂μ) atTop (𝓝 0)) :
    ∫ x, (⨅ N, E N x) ∂μ = 0 ∧ Integrable (fun x => ⨅ N, E N x) μ ∧ ∀ x, 0 ≤ ⨅ N, E N x := by
  have hbdd : ∀ x, BddBelow (Set.range fun N => E N x) :=
    fun x => ⟨0, fun _ ⟨N, hN⟩ => hN ▸ (hb N x).1⟩
  have hnn : ∀ x, 0 ≤ ⨅ N, E N x := fun x => le_ciInf fun N => (hb N x).1
  have hint' : Integrable (fun x => ⨅ N, E N x) μ :=
    Integrable.of_bound (Measurable.iInf hE).aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]; exact (ciInf_le (hbdd x) 0).trans (hb 0 x).2)
  have hEi : ∀ N, Integrable (E N) μ := fun N =>
    Integrable.of_bound (hE N).aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb N x).1]; exact (hb N x).2)
  refine ⟨le_antisymm (ge_of_tendsto' hint fun N => integral_mono hint' (hEi N)
    fun x => ciInf_le (hbdd x) N) (integral_nonneg hnn), hint', hnn⟩

/-- Under the hypotheses of `integral_ciInf_eq_zero_of_tendsto_zero`, the pointwise infimum vanishes
almost everywhere. -/
theorem ciInf_eq_zero_ae_of_tendsto_zero {μ : Measure Ω} [IsProbabilityMeasure μ] {E : ℕ → Ω
    → ℝ} {M : ℝ}
    (hE : ∀ N, Measurable (E N)) (hb : ∀ N x, 0 ≤ E N x ∧ E N x ≤ M)
    (hint : Tendsto (fun N => ∫ x, E N x ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, (⨅ N, E N x) = 0 := by
  obtain ⟨h0, hi, hnn⟩ := integral_ciInf_eq_zero_of_tendsto_zero hE hb hint
  exact (integral_eq_zero_iff_of_nonneg (fun x => hnn x) hi).1 h0

/-- A bounded, pointwise antitone sequence of measurable functions whose integrals tend to `0` tends
to `0` almost everywhere. -/
theorem tendsto_zero_ae_of_antitone_integral_tendsto_zero {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : ℕ → Ω → ℝ} {M : ℝ}
    (hE : ∀ N, Measurable (E N)) (hb : ∀ N x, 0 ≤ E N x ∧ E N x ≤ M)
    (hanti : ∀ N x, E (N + 1) x ≤ E N x)
    (hint : Tendsto (fun N => ∫ x, E N x ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (fun N => E N x) atTop (𝓝 0) := by
  filter_upwards [ciInf_eq_zero_ae_of_tendsto_zero hE hb hint] with x hx
  have h := tendsto_ciInf_of_antitone_nonneg (fun N x => (hb N x).1) hanti x
  rwa [hx] at h

omit [MeasurableSpace Ω] in
/-- `supDev g G N` is nonnegative, bounded by `2M`, antitone in `N`, and dominates every tail
deviation `|g n x - G x|` for `n ≥ N`. -/
theorem supDev_nonneg_le_antitone_bound {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (_unused_hM : 0
    ≤ M)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M) (N : ℕ) (x : Ω) :
    0 ≤ supDev g G N x ∧ supDev g G N x ≤ 2 * M ∧ supDev g G (N + 1) x ≤ supDev g G N x ∧
      ∀ n, N ≤ n → |g n x - G x| ≤ supDev g G N x := by
  have hbound : ∀ k : ℕ, |g (N + k) x - G x| ≤ 2 * M := fun k => by
    linarith [hg (N + k) x, hG x, abs_sub (g (N + k) x) (G x)]
  have hbdd : BddAbove (Set.range fun k : ℕ => |g (N + k) x - G x|) :=
    ⟨2 * M, fun y hy => hy.elim fun k hk => hk ▸ hbound k⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold supDev
    exact Real.iSup_nonneg fun k => abs_nonneg _
  · unfold supDev
    exact ciSup_le hbound
  · unfold supDev
    apply ciSup_le
    intro k
    have hidx : N + 1 + k = N + (k + 1) :=
      (Nat.add_assoc N 1 k).trans (congrArg (Nat.add N) (Nat.add_comm 1 k))
    rw [hidx]
    exact le_ciSup hbdd (k + 1)
  · intro n hn
    unfold supDev
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact le_ciSup hbdd k


/-- Each `supDev g G N` is measurable, and at a point where `g n x → G x`, the tail suprema `supDev
g G N x` tend to `0` as `N → ∞`. -/
theorem measurable_supDev_and_tendsto_zero {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (_unused_hM :
    0 ≤ M)
    (hgm : ∀ n, Measurable (g n)) (hGm : Measurable G)
    (_unused_hg : ∀ n x, |g n x| ≤ M) (_unused_hG : ∀ x, |G x| ≤ M) :
    (∀ N, Measurable (supDev g G N)) ∧
      ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (G x)) →
        Tendsto (fun N => supDev g G N x) atTop (𝓝 0) := by
  constructor
  · intro N
    exact Measurable.iSup fun k => ((hgm (N + k)).sub hGm).abs
  · intro x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases Metric.tendsto_atTop.mp hx (ε / 2) (by linarith) with ⟨N₀, hN₀⟩
    refine ⟨N₀, fun N hN => ?_⟩
    have hnn : 0 ≤ (⨆ k : ℕ, |g (N + k) x - G x|) := Real.iSup_nonneg fun k => abs_nonneg _
    have hle : (⨆ k : ℕ, |g (N + k) x - G x|) ≤ ε / 2 := ciSup_le fun k => by
      have hk : N₀ ≤ N + k := le_trans hN (Nat.le_add_right N k)
      have hh := hN₀ (N + k) hk
      rw [Real.dist_eq] at hh
      linarith
    show dist (⨆ k : ℕ, |g (N + k) x - G x|) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith


omit [MeasurableSpace Ω] in
/-- If `|g - G| ≤ D` pointwise, the Birkhoff averages satisfy `|bAvg T g n - bAvg T G n| ≤ bAvg T D
n`. -/
theorem abs_bAvg_sub_le_bAvg_of_abs_sub_le {T : Ω → Ω} {g G D : Ω → ℝ} (hD : ∀ x, |g x - G
    x| ≤ D x) (n : ℕ)
    (ω : Ω) : |bAvg T g n ω - bAvg T G n ω| ≤ bAvg T D n ω := by
  rw [bAvg, bAvg, bAvg, ← sub_div]
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  apply div_le_div_of_nonneg_right
  · show |(∑ k ∈ Finset.range n, g (T^[k] ω)) - ∑ k ∈ Finset.range n, G (T^[k] ω)|
      ≤ ∑ k ∈ Finset.range n, D (T^[k] ω)
    rw [← Finset.sum_sub_distrib]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => hD _)
  · exact Nat.cast_nonneg n


/-- For a bounded, a.e. converging family `g n → G`, the Birkhoff limsup of the tail deviation
`supDev g G N` tends to `0` a.e. as `N → ∞`. -/
theorem tendsto_bLimsup_supDev_zero {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hgm : ∀ n, Measurable (g n)) (hGm : Measurable G)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (G x))) :
    ∀ᵐ x ∂μ, Tendsto (fun N => bLimsup T (supDev g G N) x) atTop (𝓝 0) := by
  have hTm : Measurable T := hT.measurable
  have hDmeas : ∀ N, Measurable (supDev g G N) :=
    (measurable_supDev_and_tendsto_zero hM hgm hGm hg hG).1
  have hDbound : ∀ N x, |supDev g G N x| ≤ 2 * M := fun N x => by
    have h := supDev_nonneg_le_antitone_bound hM hg hG N x
    rw [abs_of_nonneg h.1]; exact h.2.1
  have hEmeas : ∀ N, Measurable (fun x => bLimsup T (supDev g G N) x) :=
    fun N => measurable_bLimsup hTm (hDmeas N)
  have hEbound : ∀ N x, 0 ≤ bLimsup T (supDev g G N) x ∧
      bLimsup T (supDev g G N) x ≤ 2 * M := fun N x => by
    have h2M : (0 : ℝ) ≤ 2 * M := by linarith
    have h := bLimsup_nonneg_le_of_le (T := T) h2M
      (fun y => ⟨(supDev_nonneg_le_antitone_bound hM hg hG N y).1, (supDev_nonneg_le_antitone_bound
          hM hg hG N y).2.1⟩)
      (fun y => ⟨(supDev_nonneg_le_antitone_bound hM hg hG N y).1, (supDev_nonneg_le_antitone_bound
          hM hg hG N y).2.1⟩)
      (fun y => le_rfl) x
    exact ⟨h.1, h.2.2⟩
  have hEanti : ∀ N x, bLimsup T (supDev g G (N + 1)) x ≤ bLimsup T (supDev g G N) x :=
    fun N x => by
      have h2M : (0 : ℝ) ≤ 2 * M := by linarith
      have h := bLimsup_nonneg_le_of_le (T := T) h2M
        (fun y => ⟨(supDev_nonneg_le_antitone_bound hM hg hG (N + 1) y).1,
          (supDev_nonneg_le_antitone_bound hM hg hG (N + 1) y).2.1⟩)
        (fun y => ⟨(supDev_nonneg_le_antitone_bound hM hg hG N y).1,
          (supDev_nonneg_le_antitone_bound hM hg hG N y).2.1⟩)
        (fun y => (supDev_nonneg_le_antitone_bound hM hg hG N y).2.2.1) x
      exact h.2.1
  have hIntD : Tendsto (fun N => ∫ x, supDev g G N x ∂μ) atTop (𝓝 0) := by
    have hbdd : Integrable (fun _ : Ω => 2 * M) μ := integrable_const (2 * M)
    have hle : ∀ N, ∀ᵐ x ∂μ, ‖supDev g G N x‖ ≤ (fun _ : Ω => 2 * M) x := fun N => by
      filter_upwards with x; rw [Real.norm_eq_abs]; exact hDbound N x
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun N => supDev g G N x) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hconv] with x hx
      exact (measurable_supDev_and_tendsto_zero hM hgm hGm hg hG).2 x hx
    have hmain := tendsto_integral_of_dominated_convergence (fun _ : Ω => 2 * M)
      (fun N => (hDmeas N).aestronglyMeasurable) hbdd hle hlim
    simpa using hmain
  have hEintT : Tendsto (fun N => ∫ x, bLimsup T (supDev g G N) x ∂μ) atTop (𝓝 0) := by
    have hEq : (fun N => ∫ x, bLimsup T (supDev g G N) x ∂μ) =
        (fun N => ∫ x, supDev g G N x ∂μ) := by
      funext N
      exact integral_bLimsup_eq_integral hT (hDmeas N) (by
          linarith : (0:ℝ) ≤ 2 * M) (fun x => hDbound N x)
    rw [hEq]; exact hIntD
  exact tendsto_zero_ae_of_antitone_integral_tendsto_zero hEmeas hEbound hEanti hEintT

omit [MeasurableSpace Ω] in
/-- An `ε`-argument combining a vanishing Birkhoff limsup of the tail deviation with the
Birkhoff-limsup convergence of `G` and of each `supDev g G N` yields convergence of `bAvg T (g
n) n` to `bLimsup T G`. -/
theorem tendsto_bAvg_movingTarget_of_tendsto_bLimsup_supDev {T : Ω → Ω} {g : ℕ → Ω → ℝ} {G :
    Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M) {x : Ω}
    (hx0 : Tendsto (fun N => bLimsup T (supDev g G N) x) atTop (𝓝 0))
    (hxG : Tendsto (fun n => bAvg T G n x) atTop (𝓝 (bLimsup T G x)))
    (hxD : ∀ N, Tendsto (fun n => bAvg T (supDev g G N) n x) atTop
      (𝓝 (bLimsup T (supDev g G N) x))) :
    Tendsto (fun n => bAvg T (g n) n x) atTop (𝓝 (bLimsup T G x)) := by
  rw [Metric.tendsto_atTop] at hx0 hxG ⊢
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨N0, hN0⟩ := hx0 (ε / 4) hε4
  obtain ⟨N1, hN1⟩ := hxG (ε / 2) hε2
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp (hxD N0)) (ε / 4) hε4
  refine ⟨max N0 (max N1 N2), fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hN0lt : bLimsup T (supDev g G N0) x < ε / 4 := by
    have h := hN0 N0 le_rfl
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hBlt : bAvg T (supDev g G N0) n x < ε / 2 := by
    have hB : bAvg T (supDev g G N0) n x ≤ bLimsup T (supDev g G N0) x +
        |bAvg T (supDev g G N0) n x - bLimsup T (supDev g G N0) x| := by
      have hb := le_abs_self (bAvg T (supDev g G N0) n x - bLimsup T (supDev g G N0) x)
      linarith
    have h2 := hN2 n hn2
    rw [Real.dist_eq] at h2
    linarith
  have hX : |bAvg T (g n) n x - bAvg T G n x| < ε / 2 := by
    have h1 := abs_bAvg_sub_le_bAvg_of_abs_sub_le (T := T)
      (fun y => (supDev_nonneg_le_antitone_bound hM hg hG N0 y).2.2.2 n hn0) n x
    linarith
  have hY : dist (bAvg T G n x) (bLimsup T G x) < ε / 2 := hN1 n hn1
  calc dist (bAvg T (g n) n x) (bLimsup T G x)
      ≤ dist (bAvg T (g n) n x) (bAvg T G n x) + dist (bAvg T G n x) (bLimsup T G x) :=
        dist_triangle _ _ _
    _ < ε := by rw [Real.dist_eq]; linarith

/-- Moving-target Birkhoff theorem for bounded functions: if `g n → G` a.e. with a uniform bound,
then `bAvg T (g n) n → bLimsup T G` a.e. -/
theorem ae_tendsto_bAvg_movingTarget {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hgm : ∀ n, Measurable (g n)) (hGm : Measurable G)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (G x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T (g n) n x) atTop (𝓝 (bLimsup T G x)) := by
  have hTm : Measurable T := hT.measurable
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
  have haeG : ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T G n x) atTop (𝓝 (bLimsup T G x)) :=
    ae_tendsto_bLimsup hT hGm hGint
  have haeD : ∀ᵐ x ∂μ, ∀ N, Tendsto (fun n => bAvg T (supDev g G N) n x) atTop
      (𝓝 (bLimsup T (supDev g G N) x)) :=
    ae_all_iff.mpr (fun N => ae_tendsto_bLimsup hT (hDmeas N) (hDint N))
  filter_upwards [hae0, haeG, haeD] with x hx0 hxG hxD
  exact tendsto_bAvg_movingTarget_of_tendsto_bLimsup_supDev hM hg hG hx0 hxG hxD


omit [MeasurableSpace Ω] in
/-- The grid average over the empty coordinate set is the single value `h (σ (natToSite 0))`. -/
theorem gridAvg_empty_eq_apply {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) (n : ℕ) (ω : Ω) :
    gridAvg σ h ∅ n ω = h (σ (natToSite 0) ω) := by
  simp [gridAvg, gridSet_empty]

/-- If the grid average over `s` converges a.e. to `G`, then the grid average over `insert i s`
converges a.e. to the Birkhoff limsup of `G` along `σ (unit i)`. -/
theorem ae_tendsto_gridAvg_insert_of_ae_tendsto {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) {G : Ω → ℝ} (hGm : Measurable G)
    (hGb : ∀ x, |G x| ≤ M)
    (hG : ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h s n ω) atTop (𝓝 (G ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h (insert i s) n ω) atTop
      (𝓝 (bLimsup (σ (unit i)) G ω)) := by
  have h35 := ae_tendsto_bAvg_movingTarget (hσ (unit i)) hM (fun n => measurable_gridAvg hσ hh s n)
      hGm
    (fun n x => abs_gridAvg_le σ h hM hb s n x) hGb hG
  filter_upwards [h35] with ω hω
  simpa only [gridAvg_insert_eq_bAvg_gridAvg hσadd h s i hi] using hω

/-- For each coordinate subset `s`, the grid average `gridAvg σ h s n` converges a.e., as `n → ∞`,
to some bounded measurable limit, by induction on `s` via
`ae_tendsto_gridAvg_insert_of_ae_tendsto`. -/
theorem exists_ae_tendsto_gridAvg {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (s : Finset (Fin d)) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h s n ω) atTop (𝓝 (G ω)) := by
  induction s using Finset.induction with
  | empty =>
    refine ⟨fun ω => h (σ (natToSite 0) ω), hh.comp (hσ _).measurable, fun x => hb _, ?_⟩
    exact ae_of_all _ fun ω => by simp only [gridAvg_empty_eq_apply]; exact tendsto_const_nhds
  | insert i s hi ih =>
    obtain ⟨G, hGm, hGb, hG⟩ := ih
    exact ⟨bLimsup (σ (unit i)) G, measurable_bLimsup (hσ _).measurable hGm,
      fun x => abs_bLimsup_le_of_abs_le hM hGb x, ae_tendsto_gridAvg_insert_of_ae_tendsto hσ hσadd
          hh hM hb s
          i hi hGm hGb hG⟩

/-- The integral of the full grid average `gridAvg σ h Finset.univ n` equals the integral of `h`,
for every `n ≥ 1`. -/
theorem integral_gridAvg_univ_eq_integral {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) {h : Ω → ℝ} (hh : Measurable h) {M : ℝ}
    (hb : ∀ x, |h x| ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, gridAvg σ h Finset.univ n ω ∂μ = ∫ ω, h ω ∂μ := by
  have hInt : ∀ w : Fin d → ℕ, Integrable (fun ω => h (σ (natToSite w) ω)) μ
  · intro w
    refine Integrable.of_bound (hh.comp (hσ (natToSite w)).measurable).aestronglyMeasurable M ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hb (σ (natToSite w) y)
  have hz : ∀ w : Fin d → ℕ, ∫ ω, h (σ (natToSite w) ω) ∂μ = ∫ ω, h ω ∂μ
  · intro w
    have hmap : ∫ y, h y ∂(Measure.map (σ (natToSite w)) μ) = ∫ ω, h (σ (natToSite w) ω) ∂μ
    · exact integral_map (hσ (natToSite w)).aemeasurable hh.aestronglyMeasurable
    rw [(hσ (natToSite w)).map_eq] at hmap
    exact hmap.symm
  have hfun : (fun ω => gridAvg σ h Finset.univ n ω) = fun ω => (∑ w ∈ gridSet d Finset.univ n, h (σ
      (natToSite w) ω)) / (n : ℝ) ^ d
  · funext ω
    simp only [gridAvg]
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hfun, integral_div, integral_finsetSum (gridSet d Finset.univ n) (fun w _ => hInt w)]
  rw [Finset.sum_congr rfl (fun w _ => hz w)]
  rw [Finset.sum_const, card_gridSet_eq_pow_card, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow]
  have hn0 : (n : ℝ) ≠ 0
  · exact_mod_cast (by omega : n ≠ 0)
  exact mul_div_cancel_left₀ _ (pow_ne_zero d hn0)


/-- Multiparameter pointwise ergodic theorem along cubes for bounded `h`: the full grid average
`gridAvg σ h Finset.univ n` converges a.e. to a bounded measurable limit `G` with `∫ G = ∫ h`. -/
theorem exists_ae_tendsto_gridAvg_univ_with_integral {d : ℕ} {σ : Site d → Ω → Ω} {μ :
    Measure Ω} [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧ ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h Finset.univ n ω) atTop (𝓝 (G ω)) := by
  obtain ⟨G, hGm, hGb, hGconv⟩ := exists_ae_tendsto_gridAvg hσ hσadd hh hM hb Finset.univ
  have h1 : Tendsto (fun n : ℕ => ∫ ω, gridAvg σ h Finset.univ n ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ : Ω => M)
      (fun n => (measurable_gridAvg hσ hh Finset.univ n).aestronglyMeasurable)
      (integrable_const M)
      (fun n => by
        filter_upwards with ω
        rw [Real.norm_eq_abs]
        exact abs_gridAvg_le σ h hM hb Finset.univ n ω)
      hGconv
  have hEq : (fun n : ℕ => ∫ ω, gridAvg σ h Finset.univ n ω ∂μ) =ᶠ[atTop] (fun _ : ℕ => ∫ ω, h ω ∂μ)
      :=
    eventually_atTop.mpr ⟨1, fun n hn => integral_gridAvg_univ_eq_integral hσ hh hb hn⟩
  have htest : Tendsto (fun _ : ℕ => ∫ ω, h ω ∂μ) atTop (𝓝 (∫ ω, h ω ∂μ)) := tendsto_const_nhds
  have h2 : Tendsto (fun _ : ℕ => ∫ ω, h ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) := Tendsto.congr' hEq h1
  exact ⟨G, hGm, hGb, (tendsto_nhds_unique htest h2).symm, hGconv⟩

end LatticeProb
