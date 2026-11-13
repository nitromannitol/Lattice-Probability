/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedRemainderMartingaleTools at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.MartingaleL2MaximalEnvelope
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedRemainderIncrementEnergy

/-!
# Generic tools for the stopped-remainder vanishing argument

Three self-contained ingredients of `Forms/StoppedRemainderVanishing`, none of which mentions
the reflected walk:

1. **Orthogonal increments of an `L²` martingale** (`integral_sq_eq_sum_sq_increments`): along
   any monotone sequence of times `E[N_{θ n}²] = E[N_{θ 0}²] + Σ_k E[(N_{θ(k+1)} − N_{θ k})²]`.
2. **Doob's `L²` inequality over a countable set of times** (`lintegral_iSup_sq_le`): from the
   finite-set version `martingale_abs_finset_maximal_integral_le` by monotone convergence.
3. **The pathwise partition bound** (`sum_sq_stopped_increments_le`): for a real path `r` and a
   stopping value `τ`, the square sum of the increments of the stopped path along the uniform
   grid of `[0, t]` is at most the square sum of the unstopped increments plus one
   *partial-interval* term `partialTerm r τ t n`, which vanishes as `n → ∞` when `r` is
   continuous at `τ` (`partialTerm_tendsto_zero`) and is dominated by four times the largest
   square of the stopped path on the grid (`partialTerm_le`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped NNReal ENNReal

namespace ReflectedGMS.StoppedRemainderTools

/-! ## Orthogonal increments -/

section Orthogonality

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ}

theorem integral_mul_eq_integral_sq (hN : Martingale N F P) (h2 : ∀ t, MemLp (N t) 2 P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, N s ω * N t ω ∂P = ∫ ω, (N s ω) ^ 2 ∂P := by
  have hsm : StronglyMeasurable[F s] (N s) := hN.stronglyMeasurable s
  have hint : Integrable (N s * N t) P := (h2 s).integrable_mul (h2 t)
  have hpull := condExp_mul_of_stronglyMeasurable_left hsm hint (hN.integrable t)
  have hce := hN.condExp_ae_eq hst
  have h1 : ∫ ω, (N s * N t) ω ∂P = ∫ ω, (P[N s * N t | F s]) ω ∂P :=
    (integral_condExp (F.le s)).symm
  have h2' : (P[N s * N t | F s]) =ᵐ[P] fun ω ↦ (N s ω) ^ 2 := by
    filter_upwards [hpull, hce] with ω hω1 hω2
    rw [hω1, Pi.mul_apply, hω2, pow_two]
  calc ∫ ω, N s ω * N t ω ∂P = ∫ ω, (N s * N t) ω ∂P := rfl
    _ = ∫ ω, (P[N s * N t | F s]) ω ∂P := h1
    _ = ∫ ω, (N s ω) ^ 2 ∂P := integral_congr_ae h2'

theorem integral_sq_sub_eq (hN : Martingale N F P) (h2 : ∀ t, MemLp (N t) 2 P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (N t ω - N s ω) ^ 2 ∂P = (∫ ω, (N t ω) ^ 2 ∂P) - ∫ ω, (N s ω) ^ 2 ∂P := by
  have hts : Integrable (fun ω ↦ (N t ω) ^ 2) P := (h2 t).integrable_sq
  have hss : Integrable (fun ω ↦ (N s ω) ^ 2) P := (h2 s).integrable_sq
  have hm : Integrable (fun ω ↦ N s ω * N t ω) P := (h2 s).integrable_mul (h2 t)
  have hexp : ∀ ω, (N t ω - N s ω) ^ 2 =
      ((N t ω) ^ 2 - 2 * (N s ω * N t ω)) + (N s ω) ^ 2 := fun ω ↦ by ring
  have h1 : Integrable (fun ω ↦ (N t ω) ^ 2 - 2 * (N s ω * N t ω)) P :=
    hts.sub (hm.const_mul 2)
  simp_rw [hexp]
  rw [integral_add h1 hss, integral_sub hts (hm.const_mul 2),
    integral_const_mul, integral_mul_eq_integral_sq hN h2 hst]
  ring

/-- **Orthogonal increments along a monotone sequence of times.** -/
theorem integral_sq_eq_sum_sq_increments (hN : Martingale N F P) (h2 : ∀ t, MemLp (N t) 2 P)
    (θ : ℕ → ℝ≥0) (hθ : Monotone θ) (n : ℕ) :
    ∫ ω, (N (θ n) ω) ^ 2 ∂P =
      (∫ ω, (N (θ 0) ω) ^ 2 ∂P) +
        ∑ k ∈ range n, ∫ ω, (N (θ (k + 1)) ω - N (θ k) ω) ^ 2 ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← add_assoc, ← ih, integral_sq_sub_eq hN h2 (hθ (Nat.le_succ n))]
    ring

/-! ## Doob's `L²` inequality over a countable family of times -/

/-- **Countable Doob `L²` bound.**  For an `L²` martingale and any sequence of times `θ i ≤ T`,
`E[sup_i N_{θ i}²] ≤ 4 E[N_T²]`, as Lebesgue integrals. -/
theorem lintegral_iSup_sq_le (hN : Martingale N F P) (h2 : ∀ t, MemLp (N t) 2 P)
    (θ : ℕ → ℝ≥0) (T : ℝ≥0) (hθ : ∀ i, θ i ≤ T) :
    ∫⁻ ω, ⨆ i, ENNReal.ofReal ((N (θ i) ω) ^ 2) ∂P ≤
      ENNReal.ofReal (4 * ∫ ω, (N T ω) ^ 2 ∂P) := by
  classical
  let S : ℕ → Finset ℝ≥0 := fun i ↦ insert T ((range (i + 1)).image θ)
  have hS : ∀ i, (S i).Nonempty := fun i ↦ insert_nonempty _ _
  let g : ℕ → Ω → ℝ := fun i ω ↦ ((S i).sup' (hS i) fun t ↦ |N t ω|) ^ 2
  have hmeasN : ∀ t, Measurable (N t) := fun t ↦
    ((hN.stronglyMeasurable t).mono (F.le t)).measurable
  have hg_meas : ∀ i, Measurable (g i) := by
    intro i
    have hsup : Measurable ((S i).sup' (hS i) fun t ↦ fun ω ↦ |N t ω|) :=
      Finset.measurable_sup' (hS i) fun t _ ↦ continuous_abs.measurable.comp (hmeasN t)
    have heq : g i = fun ω ↦ (((S i).sup' (hS i) fun t ↦ fun ω ↦ |N t ω|) ω) ^ 2 := by
      funext ω
      simp only [g, Finset.sup'_apply]
    rw [heq]
    exact hsup.pow_const 2
  have hg_nonneg : ∀ i ω, 0 ≤ g i ω := fun i ω ↦ sq_nonneg _
  have hsup_nonneg : ∀ i ω, 0 ≤ (S i).sup' (hS i) fun t ↦ |N t ω| := fun i ω ↦
    (abs_nonneg (N T ω)).trans (Finset.le_sup' (fun t ↦ |N t ω|) (mem_insert_self T _))
  have hg_mono : Monotone fun i ω ↦ ENNReal.ofReal (g i ω) := by
    intro i j hij ω
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (hsup_nonneg i ω)
    have hsub : S i ⊆ S j := by
      apply Finset.insert_subset_insert
      apply image_subset_image
      exact Finset.range_mono (Nat.succ_le_succ hij)
    exact Finset.sup'_mono (fun t ↦ |N t ω|) hsub (hS i)
  have hg_bound : ∀ i, ∫⁻ ω, ENNReal.ofReal (g i ω) ∂P ≤
      ENNReal.ofReal (4 * ∫ ω, (N T ω) ^ 2 ∂P) := by
    intro i
    have hint : Integrable (g i) P := by
      refine Integrable.mono' (integrable_finsetSum (S i) fun t _ ↦ (h2 t).integrable_sq)
        (hg_meas i).aestronglyMeasurable ?_
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg i ω)]
      obtain ⟨t₀, ht₀, heq⟩ := Finset.exists_mem_eq_sup' (hS i) (fun t ↦ |N t ω|)
      simp only [g]
      rw [heq, sq_abs]
      exact Finset.single_le_sum (fun t _ ↦ sq_nonneg (N t ω)) ht₀
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (hg_nonneg i))]
    apply ENNReal.ofReal_le_ofReal
    have hsT : ∀ t ∈ (range (i + 1)).image θ, t ≤ T := by
      intro t ht
      obtain ⟨k, _, rfl⟩ := mem_image.1 ht
      exact hθ k
    exact martingale_abs_finset_maximal_integral_le hN h2 ((range (i + 1)).image θ) T hsT
  calc ∫⁻ ω, ⨆ i, ENNReal.ofReal ((N (θ i) ω) ^ 2) ∂P
      ≤ ∫⁻ ω, ⨆ i, ENNReal.ofReal (g i ω) ∂P := by
        apply lintegral_mono
        intro ω
        apply iSup_le
        intro i
        apply le_iSup_of_le i
        apply ENNReal.ofReal_le_ofReal
        rw [← sq_abs]
        apply pow_le_pow_left₀ (abs_nonneg _)
        exact Finset.le_sup' (fun t ↦ |N t ω|)
          (mem_insert_of_mem (mem_image_of_mem θ (mem_range.2 (Nat.lt_succ_self i))))
    _ = ⨆ i, ∫⁻ ω, ENNReal.ofReal (g i ω) ∂P :=
        lintegral_iSup (fun i ↦ (hg_meas i).ennreal_ofReal) hg_mono
    _ ≤ _ := iSup_le hg_bound

end Orthogonality

/-! ## A sum of indicators with at most one live term -/

theorem sum_ite_le_of_pairwise {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (hp : ∀ a ∈ s, ∀ b ∈ s, p a → p b → a = b) (f : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ a ∈ s, p a → f a ≤ c) :
    ∑ a ∈ s, (if p a then f a else 0) ≤ c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hcard : (s.filter p).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦
    hp a (mem_filter.1 ha).1 b (mem_filter.1 hb).1 (mem_filter.1 ha).2 (mem_filter.1 hb).2
  calc ∑ a ∈ s.filter p, f a ≤ ∑ a ∈ s.filter p, c :=
        Finset.sum_le_sum fun a ha ↦ hf a (mem_filter.1 ha).1 (mem_filter.1 ha).2
    _ = (s.filter p).card • c := Finset.sum_const c
    _ ≤ 1 • c := nsmul_le_nsmul_left hc hcard
    _ = c := one_nsmul c

/-! ## The uniform grid -/

theorem uniformGrid_mono (t : ℝ≥0) (n : ℕ) {k k' : ℕ} (h : k ≤ k') :
    uniformGrid t n k ≤ uniformGrid t n k' := by
  have hk : (k : ℝ≥0) ≤ k' := by exact_mod_cast h
  unfold uniformGrid
  gcongr

theorem uniformGrid_zero (t : ℝ≥0) (n : ℕ) : uniformGrid t n 0 = 0 := by
  simp [uniformGrid]

theorem uniformGrid_self (t : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : uniformGrid t n n = t := by
  unfold uniformGrid
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  rw [mul_comm, mul_div_assoc, div_self hn', mul_one]

theorem uniformGrid_le (t : ℝ≥0) {n k : ℕ} (hk : k ≤ n) : uniformGrid t n k ≤ t := by
  unfold uniformGrid
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_iff₀ (by exact_mod_cast hn)]
    have hk' : (k : ℝ≥0) ≤ n := by exact_mod_cast hk
    calc (k : ℝ≥0) * t ≤ (n : ℝ≥0) * t := by gcongr
      _ = t * n := mul_comm _ _

/-- At most one grid interval `(t_k, t_{k+1})` contains `τ`. -/
theorem uniformGrid_interval_unique (t : ℝ≥0) (n : ℕ) (τ : WithTop ℝ≥0) {k k' : ℕ}
    (hk : (uniformGrid t n k : WithTop ℝ≥0) < τ ∧ τ < uniformGrid t n (k + 1))
    (hk' : (uniformGrid t n k' : WithTop ℝ≥0) < τ ∧ τ < uniformGrid t n (k' + 1)) :
    k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hle : (uniformGrid t n (k + 1) : WithTop ℝ≥0) ≤ uniformGrid t n k' :=
      WithTop.coe_le_coe.2 (uniformGrid_mono t n (Nat.succ_le_of_lt h))
    exact lt_irrefl _ ((hle.trans_lt hk'.1).trans hk.2)
  · have hle : (uniformGrid t n (k' + 1) : WithTop ℝ≥0) ≤ uniformGrid t n k :=
      WithTop.coe_le_coe.2 (uniformGrid_mono t n (Nat.succ_le_of_lt h))
    exact lt_irrefl _ ((hle.trans_lt hk.1).trans hk'.2)

/-! ## The pathwise partition bound for a stopped path -/

theorem untopA_coe' (b : ℝ≥0) : ((b : WithTop ℝ≥0)).untopA = b := by
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
  exact WithTop.coe_inj.1 (WithTop.coe_untop _ _)

open Classical in
/-- The square of a stopped increment over `[a, b]` is at most the square of the unstopped
increment plus a partial-interval term, present only when `τ ∈ (a, b)`. -/
theorem sq_stopped_sub_le (r : ℝ≥0 → ℝ) (τ : WithTop ℝ≥0) {a b : ℝ≥0} (hab : a ≤ b) :
    (r (min (b : WithTop ℝ≥0) τ).untopA - r (min (a : WithTop ℝ≥0) τ).untopA) ^ 2 ≤
      (r b - r a) ^ 2 +
        (if (a : WithTop ℝ≥0) < τ ∧ τ < b then (r τ.untopA - r a) ^ 2 else 0) := by
  have h0 : 0 ≤ (if (a : WithTop ℝ≥0) < τ ∧ τ < b then (r τ.untopA - r a) ^ 2 else 0) := by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  by_cases hτa : τ ≤ a
  · rw [min_eq_right hτa, min_eq_right (hτa.trans (WithTop.coe_le_coe.2 hab)), sub_self,
      zero_pow two_ne_zero]
    exact add_nonneg (sq_nonneg _) h0
  · push_neg at hτa
    by_cases hbτ : (b : WithTop ℝ≥0) ≤ τ
    · rw [min_eq_left hbτ, min_eq_left hτa.le, untopA_coe', untopA_coe']
      linarith
    · push_neg at hbτ
      rw [min_eq_right hbτ.le, min_eq_left hτa.le, untopA_coe', if_pos ⟨hτa, hbτ⟩]
      linarith [sq_nonneg (r b - r a)]

open Classical in
/-- The partial-interval term of the uniform grid of `[0, t]` with `n` pieces. -/
noncomputable def partialTerm (r : ℝ≥0 → ℝ) (τ : WithTop ℝ≥0) (t : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ k ∈ range n,
    if (uniformGrid t n k : WithTop ℝ≥0) < τ ∧ τ < uniformGrid t n (k + 1)
    then (r τ.untopA - r (uniformGrid t n k)) ^ 2 else 0

theorem partialTerm_nonneg (r : ℝ≥0 → ℝ) (τ : WithTop ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    0 ≤ partialTerm r τ t n := by
  unfold partialTerm
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- **The pathwise partition bound.** -/
theorem sum_sq_stopped_increments_le (r : ℝ≥0 → ℝ) (τ : WithTop ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    ∑ k ∈ range n,
        (r (min (uniformGrid t n (k + 1) : WithTop ℝ≥0) τ).untopA -
          r (min (uniformGrid t n k : WithTop ℝ≥0) τ).untopA) ^ 2 ≤
      (∑ k ∈ range n, (r (uniformGrid t n (k + 1)) - r (uniformGrid t n k)) ^ 2) +
        partialTerm r τ t n := by
  classical
  unfold partialTerm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ ↦ sq_stopped_sub_le r τ (uniformGrid_le_succ t n k)

/-- No partial interval when `τ ≥ t`. -/
theorem partialTerm_eq_zero_of_le (r : ℝ≥0 → ℝ) (τ : WithTop ℝ≥0) (t : ℝ≥0) (n : ℕ)
    (hτ : (t : WithTop ℝ≥0) ≤ τ) : partialTerm r τ t n = 0 := by
  classical
  unfold partialTerm
  apply Finset.sum_eq_zero
  intro k hk
  split_ifs with hc
  · exfalso
    have hle : (uniformGrid t n (k + 1) : WithTop ℝ≥0) ≤ t :=
      WithTop.coe_le_coe.2 (uniformGrid_le t (Nat.succ_le_of_lt (mem_range.1 hk)))
    exact lt_irrefl _ ((hc.2.trans_le hle).trans_le hτ)
  · rfl

/-- **The partial-interval term vanishes** for a path continuous at a finite stopping value. -/
theorem partialTerm_tendsto_zero (r : ℝ≥0 → ℝ) (τ₀ t : ℝ≥0) (hr : ContinuousAt r τ₀) :
    Tendsto (fun n ↦ partialTerm r (τ₀ : WithTop ℝ≥0) t n) atTop (𝓝 0) := by
  classical
  rw [tendsto_order]
  refine ⟨fun b hb ↦ Eventually.of_forall fun n ↦ hb.trans_le (partialTerm_nonneg r _ t n),
    fun b hb ↦ ?_⟩
  set ε : ℝ := Real.sqrt b / 2 with hε_def
  have hε : 0 < ε := by positivity
  have hεb : ε ^ 2 < b := by
    rw [hε_def, div_pow, Real.sq_sqrt hb.le]
    linarith
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hr ε hε
  have hmesh : Tendsto (fun n : ℕ ↦ (t : ℝ) / n) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (t : ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using this
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ), eventually_ne_atTop 0] with n hn hn0
  refine lt_of_le_of_lt ?_ hεb
  unfold partialTerm
  apply sum_ite_le_of_pairwise _ _ (fun k _ k' _ hk hk' ↦ uniformGrid_interval_unique t n _ hk hk')
    _ (sq_nonneg ε)
  intro k _ hk
  rw [untopA_coe']
  have hk1 : (uniformGrid t n k : ℝ) < τ₀ := by exact_mod_cast hk.1
  have hk2 : (τ₀ : ℝ) < uniformGrid t n (k + 1) := by exact_mod_cast hk.2
  have hdist : dist (uniformGrid t n k) τ₀ < δ := by
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
    have := uniformGrid_succ_sub t hn0 k
    linarith
  have hr' := hδε hdist
  rw [Real.dist_eq, abs_sub_comm] at hr'
  calc (r τ₀ - r (uniformGrid t n k)) ^ 2 = |r τ₀ - r (uniformGrid t n k)| ^ 2 := (sq_abs _).symm
    _ ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hr'.le 2

/-- **Domination of the partial-interval term** by four times the largest square of the
stopped path on the grid. -/
theorem partialTerm_le (r : ℝ≥0 → ℝ) (τ : WithTop ℝ≥0) (t : ℝ≥0) (n : ℕ) {S : ℝ}
    (hS : ∀ k ≤ n, (r (min (uniformGrid t n k : WithTop ℝ≥0) τ).untopA) ^ 2 ≤ S) :
    partialTerm r τ t n ≤ 4 * S := by
  classical
  have hS0 : 0 ≤ S := (sq_nonneg _).trans (hS 0 (Nat.zero_le n))
  unfold partialTerm
  apply sum_ite_le_of_pairwise _ _ (fun k _ k' _ hk hk' ↦ uniformGrid_interval_unique t n _ hk hk')
    _ (by linarith)
  intro k hkn hk
  have hk1 : k ≤ n := (mem_range.1 hkn).le
  have hk2 : k + 1 ≤ n := Nat.succ_le_of_lt (mem_range.1 hkn)
  have hA := hS (k + 1) hk2
  have hB := hS k hk1
  rw [min_eq_right hk.2.le] at hA
  rw [min_eq_left hk.1.le, untopA_coe'] at hB
  nlinarith [sq_nonneg (r τ.untopA + r (uniformGrid t n k)), hA, hB]

end ReflectedGMS.StoppedRemainderTools
