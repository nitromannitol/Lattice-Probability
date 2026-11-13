import Mathlib
import LatticeProb.Prob.Percolation.LSS.Basic

/-!
# The Lovász local lemma for weighted expectations

The conditional bound of Liggett, Schonmann and Stacey for a field of bits with a bounded-degree
dependence graph, in the form of a Lovász local lemma for weighted expectations.

For a field of bits whose dependence graph has degree at most `Δ`, whose bits are `false` with
probability at most `q`, and whose finite product weight is bounded below by `g` off a set `V`,
the weighted probability that one more bit is `false` is at most `ε` times the weight total,
provided `q ≤ ε g^Δ (1 - Δ ε)`. The estimate is proved by induction on the finite product set,
splitting every induction step into the neighbours and the non-neighbours of the tested
coordinate.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb.Percolation.LSS

variable {S : Type}

/-- A function of one coordinate is measurable. -/
theorem xlss_meas_coord (f : Bool → ℝ) (s : S) : Measurable fun x : S → Bool => f (x s) :=
  (measurable_of_finite f).comp (measurable_pi_apply s)

/-- A finite product of functions of single coordinates is measurable. -/
theorem xlss_meas_prod (U : Finset S) (w : S → Bool → ℝ) :
    Measurable fun x : S → Bool => ∏ l ∈ U, w l (x l) :=
  Finset.measurable_prod U fun l _ => xlss_meas_coord (w l) l

/-- A finite product of values in `[0,1]` is integrable. -/
theorem xlss_integrable_prod (μ : Measure (S → Bool)) [IsProbabilityMeasure μ] (U : Finset S)
    (w : S → Bool → ℝ) (hw : ∀ l ∈ U, ∀ b, 0 ≤ w l b ∧ w l b ≤ 1) :
    Integrable (fun x : S → Bool => ∏ l ∈ U, w l (x l)) μ := by
  refine Integrable.of_bound (C := 1) (xlss_meas_prod U w).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h0 : 0 ≤ ∏ l ∈ U, w l (x l) := Finset.prod_nonneg fun l hl => (hw l hl _).1
  have h1 : ∏ l ∈ U, w l (x l) ≤ 1 := Finset.prod_le_one₀ (fun l hl => (hw l hl _).1)
    (fun l hl => (hw l hl _).2)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1


/-- Independence of one coordinate from the coordinates in a finite set of non-neighbours. -/
theorem xlss_indep_integral [DecidableEq S] (G : SimpleGraph S) (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ] (hdep : HasDependenceGraph G μ) (j : S) (U : Finset S) (hjU : j ∉ U)
    (hadj : ∀ b ∈ U, ¬ G.Adj j b) (φ : Bool → ℝ) (ψ : S → Bool → ℝ) :
    ∫ x, φ (x j) * ∏ l ∈ U, ψ l (x l) ∂μ =
      (∫ x, φ (x j) ∂μ) * ∫ x, ∏ l ∈ U, ψ l (x l) ∂μ := by
  have hind := hdep {j} U (by simpa using hjU) (by simpa using hadj)
  let φ' : (({j} : Finset S) → Bool) → ℝ := fun v => φ (v ⟨j, Finset.mem_singleton_self j⟩)
  let ψ' : (U → Bool) → ℝ := fun v => ∏ k : U, ψ k (v k)
  have hφ' : Measurable φ' := measurable_of_finite _
  have hψ' : Measurable ψ' := measurable_of_finite _
  have h2 := (hind.comp hφ' hψ').integral_fun_mul_eq_mul_integral
    ((hφ'.comp (Measurable.of_eval fun i => measurable_pi_apply _)).aestronglyMeasurable)
    ((hψ'.comp (Measurable.of_eval fun i => measurable_pi_apply _)).aestronglyMeasurable)
  have e1 : ∀ x : S → Bool, φ' (fun i : ({j} : Finset S) => x (i : S)) = φ (x j) :=
    fun x => rfl
  have e2 : ∀ x : S → Bool, ψ' (fun k : U => x (k : S)) = ∏ l ∈ U, ψ l (x l) := by
    intro x
    simp only [ψ']
    exact Finset.prod_coe_sort U fun l => ψ l (x l)
  simpa only [Function.comp_apply, e1, e2] using h2

/-- The indicator of a coordinate being `false` times a finite product is integrable. -/
theorem xlss_integrable_ind_prod (μ : Measure (S → Bool)) [IsProbabilityMeasure μ] (j : S)
    (U : Finset S) (w : S → Bool → ℝ) (hw : ∀ l ∈ U, ∀ b, 0 ≤ w l b ∧ w l b ≤ 1) :
    Integrable (fun x : S → Bool =>
      (if x j = false then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l)) μ := by
  have hm : Measurable fun x : S → Bool =>
      (if x j = false then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l) :=
    (xlss_meas_coord (fun b => if b = false then (1 : ℝ) else 0) j).mul (xlss_meas_prod U w)
  refine Integrable.of_bound (C := 1) hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h0 : 0 ≤ ∏ l ∈ U, w l (x l) := Finset.prod_nonneg fun l hl => (hw l hl _).1
  have h1 : ∏ l ∈ U, w l (x l) ≤ 1 := Finset.prod_le_one₀ (fun l hl => (hw l hl _).1)
    (fun l hl => (hw l hl _).2)
  have h2 : (0 : ℝ) ≤ (if x j = false then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h3 : (if x j = false then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 h0)]
  calc (if x j = false then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l)
      ≤ 1 * 1 := mul_le_mul h3 h1 h0 zero_le_one
    _ = 1 := one_mul 1

/-- The union bound for the indicator of all of a finite set of coordinates being `true`. -/
theorem xlss_bonferroni (x : S → Bool) (N : Finset S) :
    1 - ∑ l ∈ N, (if x l = false then (1 : ℝ) else 0) ≤
      ∏ l ∈ N, (if x l = true then (1 : ℝ) else 0) := by
  classical
  induction N using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs : 0 ≤ ∑ l ∈ s, (if x l = false then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun l _ => by split_ifs <;> norm_num
    cases hxa : x a
    · simp only [Bool.false_eq_true, ite_false, ite_true, zero_mul]
      linarith
    · simp only [ite_true, Bool.true_eq_false, ite_false, one_mul]
      linarith

/-- **The conditional bound of Liggett, Schonmann and Stacey.**  For a field of bits whose
dependence graph has degree at most `Δ`, whose bits are `false` with probability at most `q`, and
weights `w l b ∈ [0,1]` that are at least `g` unless the bit `l` is in `V` and the value `b` is
`false`, the weighted probability that a further bit `j` is `false` is at most `ε` times the weight
total, provided `q ≤ ε g^Δ (1 - Δ ε)`. -/
theorem xlss_lll [DecidableEq S] (G : SimpleGraph S) (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ] (Δ : ℕ) (hdeg : ∀ s, (G.neighborSet s).Finite ∧
      (G.neighborSet s).ncard ≤ Δ)
    (hdep : HasDependenceGraph G μ) (q ε g : ℝ) (hε : 0 < ε)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hqε : q ≤ ε * g ^ Δ * (1 - Δ * ε))
    (hmarg : ∀ s, μ.real {x | x s = false} ≤ q)
    (V : Finset S) (w : S → Bool → ℝ) (U : Finset S)
    (hbd : ∀ l ∈ U, (∀ b, 0 ≤ w l b ∧ w l b ≤ 1) ∧ ∀ b, (l ∉ V ∨ b = true) → g ≤ w l b)
    (j : S) (hj : j ∉ U) :
    ∫ x, (if x j = false then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l) ∂μ ≤
      ε * ∫ x, ∏ l ∈ U, w l (x l) ∂μ := by
  induction U using Finset.strongInduction generalizing j with
  | H U ih =>
  classical
  set A := U.filter (fun l => ¬ G.Adj j l) with hA
  set N := U.filter (fun l => G.Adj j l) with hN
  set N1 := N.filter (fun l => l ∈ V) with hN1
  have hAsub : A ⊆ U := Finset.filter_subset _ _
  have hNsub : N ⊆ U := Finset.filter_subset _ _
  have hjA : j ∉ A := fun h => hj (hAsub h)
  have hAadj : ∀ b ∈ A, ¬ G.Adj j b := fun b hb => (Finset.mem_filter.1 hb).2
  have hNcard : N.card ≤ Δ := by
    obtain ⟨hfin, hle⟩ := hdeg j
    have hsub : (N : Set S) ⊆ G.neighborSet j := fun l hl => (Finset.mem_filter.1 hl).2
    calc N.card = (N : Set S).ncard := (Set.ncard_coe_finset N).symm
      _ ≤ (G.neighborSet j).ncard := Set.ncard_le_ncard hsub hfin
      _ ≤ Δ := hle
  have hN1card : N1.card ≤ Δ := (Finset.card_le_card (Finset.filter_subset _ _)).trans hNcard
  have hwb : ∀ l ∈ U, ∀ b, 0 ≤ w l b ∧ w l b ≤ 1 := fun l hl => (hbd l hl).1
  have hwA : ∀ l ∈ A, ∀ b, 0 ≤ w l b ∧ w l b ≤ 1 := fun l hl => hwb l (hAsub hl)
  have hprod : ∀ x : S → Bool, ∏ l ∈ U, w l (x l) =
      (∏ l ∈ N, w l (x l)) * ∏ l ∈ A, w l (x l) := fun x =>
    (Finset.prod_filter_mul_prod_filter_not U (fun l => G.Adj j l) (fun l => w l (x l))).symm
  have hwA0 : ∀ x : S → Bool, 0 ≤ ∏ l ∈ A, w l (x l) := fun x =>
    Finset.prod_nonneg fun l hl => (hwA l hl _).1
  have hwN0 : ∀ x : S → Bool, 0 ≤ ∏ l ∈ N, w l (x l) := fun x =>
    Finset.prod_nonneg fun l hl => (hwb l (hNsub hl) _).1
  have hwN1 : ∀ x : S → Bool, ∏ l ∈ N, w l (x l) ≤ 1 := fun x =>
    Finset.prod_le_one₀ (fun l hl => (hwb l (hNsub hl) _).1) (fun l hl => (hwb l (hNsub hl) _).2)
  have hind0 : ∀ (y : S → Bool) (i : S), (0 : ℝ) ≤ (if y i = false then (1 : ℝ) else 0) :=
    fun y i => by split_ifs <;> norm_num
  set IA := ∫ x, ∏ l ∈ A, w l (x l) ∂μ with hIA
  have hIA0 : 0 ≤ IA := integral_nonneg hwA0
  have intA := xlss_integrable_prod μ A w hwA
  have intU := xlss_integrable_prod μ U w hwb
  -- the upper bound
  have hmeas_apply : Measurable (fun f : S → Bool => f j) := measurable_pi_apply j
  have hmeas_j : MeasurableSet {x : S → Bool | x j = false} :=
    hmeas_apply (measurableSet_singleton false)
  have hEind : ∫ x, (if x j = false then (1 : ℝ) else 0) ∂μ = μ.real {x | x j = false} := by
    have : (fun x : S → Bool => if x j = false then (1 : ℝ) else 0) =
        Set.indicator {x : S → Bool | x j = false} (fun _ => (1 : ℝ)) := by
      funext x; simp [Set.indicator_apply]
    rw [this, integral_indicator_const _ hmeas_j]
    simp
  have hup : ∫ x, (if x j = false then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l) ∂μ ≤ q * IA := by
    calc ∫ x, (if x j = false then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l) ∂μ
        ≤ ∫ x, (if x j = false then (1 : ℝ) else 0) * ∏ l ∈ A, w l (x l) ∂μ := by
          refine integral_mono (xlss_integrable_ind_prod μ j U w hwb)
            (xlss_integrable_ind_prod μ j A w hwA) fun x => ?_
          rw [hprod x]
          have := mul_le_mul_of_nonneg_right (hwN1 x) (hwA0 x)
          rw [one_mul] at this
          exact mul_le_mul_of_nonneg_left this (hind0 x j)
      _ = μ.real {x | x j = false} * IA := by
          have := xlss_indep_integral G μ hdep j A hjA hAadj
            (fun b => if b = false then (1 : ℝ) else 0) w
          rw [this, hEind]
      _ ≤ q * IA := mul_le_mul_of_nonneg_right (hmarg j) hIA0
  -- the lower bound
  have hpt : ∀ x : S → Bool, g ^ Δ * ((∏ l ∈ A, w l (x l)) *
      ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0)) ≤ ∏ l ∈ U, w l (x l) := by
    intro x
    by_cases hall : ∀ l ∈ N1, x l = true
    · have h1 : ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0) = 1 :=
        Finset.prod_eq_one fun l hl => by simp [hall l hl]
      rw [h1, mul_one, hprod x]
      have hgN : g ^ N.card ≤ ∏ l ∈ N, w l (x l) := by
        rw [← Finset.prod_const]
        refine Finset.prod_le_prod₀ (fun l _ => hg0) fun l hl => ?_
        refine (hbd l (hNsub hl)).2 (x l) ?_
        by_cases hlV : l ∈ V
        · exact Or.inr (hall l (Finset.mem_filter.2 ⟨hl, hlV⟩))
        · exact Or.inl hlV
      have hgΔ : g ^ Δ ≤ g ^ N.card := pow_le_pow_of_le_one hg0 hg1 hNcard
      exact mul_le_mul_of_nonneg_right (hgΔ.trans hgN) (hwA0 x)
    · obtain ⟨l, hl, hxl⟩ : ∃ l ∈ N1, x l ≠ true := by
        by_contra hcon
        exact hall fun l hl => by
          by_contra h
          exact hcon ⟨l, hl, h⟩
      have h1 : ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero hl (by simp [hxl])
      rw [h1, mul_zero, mul_zero, hprod x]
      exact mul_nonneg (hwN0 x) (hwA0 x)
  have hIH : ∀ l ∈ N1, ∫ x, (if x l = false then (1 : ℝ) else 0) * ∏ k ∈ A, w k (x k) ∂μ ≤
      ε * IA := by
    intro l hl
    have hlN : l ∈ N := (Finset.mem_filter.1 hl).1
    have hlU : l ∈ U := hNsub hlN
    have hlA : l ∉ A := fun h => (Finset.mem_filter.1 h).2 (Finset.mem_filter.1 hlN).2
    have hss : A ⊂ U := Finset.ssubset_iff_subset_ne.2 ⟨hAsub, fun h => hlA (h ▸ hlU)⟩
    exact ih A hss (fun k hk => hbd k (hAsub hk)) l hlA
  have hlow : g ^ Δ * (1 - Δ * ε) * IA ≤ ∫ x, ∏ l ∈ U, w l (x l) ∂μ := by
    have hmeasI : Measurable fun x : S → Bool =>
        ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0) :=
      Finset.measurable_prod N1 fun l _ =>
        xlss_meas_coord (fun b => if b = true then (1 : ℝ) else 0) l
    have intI : Integrable (fun x : S → Bool => (∏ l ∈ A, w l (x l)) *
        ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0)) μ := by
      refine Integrable.of_bound (C := 1) ((xlss_meas_prod A w).mul hmeasI).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun x => ?_
      have h0 : 0 ≤ ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0) :=
        Finset.prod_nonneg fun l _ => by split_ifs <;> norm_num
      have h1 : ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0) ≤ 1 :=
        Finset.prod_le_one₀ (fun l _ => by split_ifs <;> norm_num) fun l _ => by split_ifs <;> norm_num
      have hA1 : ∏ l ∈ A, w l (x l) ≤ 1 :=
        Finset.prod_le_one₀ (fun l hl => (hwA l hl _).1) fun l hl => (hwA l hl _).2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwA0 x) h0)]
      calc (∏ l ∈ A, w l (x l)) * ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0)
          ≤ 1 * 1 := mul_le_mul hA1 h1 h0 zero_le_one
        _ = 1 := one_mul 1
    have hstep1 : g ^ Δ * ∫ x, (∏ l ∈ A, w l (x l)) *
        ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0) ∂μ ≤ ∫ x, ∏ l ∈ U, w l (x l) ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono (intI.const_mul _) intU hpt
    have hstep2 : IA - ∑ l ∈ N1, ∫ x, (if x l = false then (1 : ℝ) else 0) *
        ∏ k ∈ A, w k (x k) ∂μ ≤ ∫ x, (∏ l ∈ A, w l (x l)) *
        ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0) ∂μ := by
      rw [← integral_finsetSum _ (fun l _ => xlss_integrable_ind_prod μ l A w hwA),
        hIA, ← integral_sub intA
          (integrable_finsetSum _ (fun l _ => xlss_integrable_ind_prod μ l A w hwA))]
      refine integral_mono (intA.sub
          (integrable_finsetSum _ (fun l _ => xlss_integrable_ind_prod μ l A w hwA))) intI
        fun x => ?_
      have hb := xlss_bonferroni x N1
      have := mul_le_mul_of_nonneg_left hb (hwA0 x)
      calc (∏ l ∈ A, w l (x l)) - ∑ l ∈ N1, (if x l = false then (1 : ℝ) else 0) *
            ∏ k ∈ A, w k (x k)
          = (∏ l ∈ A, w l (x l)) * (1 - ∑ l ∈ N1, (if x l = false then (1 : ℝ) else 0)) := by
            rw [← Finset.sum_mul]; ring
        _ ≤ _ := this
    have hsum : ∑ l ∈ N1, ∫ x, (if x l = false then (1 : ℝ) else 0) *
        ∏ k ∈ A, w k (x k) ∂μ ≤ Δ * (ε * IA) := by
      calc ∑ l ∈ N1, ∫ x, (if x l = false then (1 : ℝ) else 0) * ∏ k ∈ A, w k (x k) ∂μ
          ≤ ∑ l ∈ N1, (ε * IA) := Finset.sum_le_sum hIH
        _ = N1.card * (ε * IA) := by simp
        _ ≤ Δ * (ε * IA) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hN1card) (mul_nonneg hε.le hIA0)
    have hg : 0 ≤ g ^ Δ := pow_nonneg hg0 Δ
    calc g ^ Δ * (1 - Δ * ε) * IA = g ^ Δ * (IA - Δ * (ε * IA)) := by ring
      _ ≤ g ^ Δ * ∫ x, (∏ l ∈ A, w l (x l)) *
          ∏ l ∈ N1, (if x l = true then (1 : ℝ) else 0) ∂μ :=
        mul_le_mul_of_nonneg_left (by linarith) hg
      _ ≤ _ := hstep1
  calc ∫ x, (if x j = false then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l) ∂μ ≤ q * IA := hup
    _ ≤ ε * g ^ Δ * (1 - Δ * ε) * IA := mul_le_mul_of_nonneg_right hqε hIA0
    _ = ε * (g ^ Δ * (1 - Δ * ε) * IA) := by ring
    _ ≤ ε * ∫ x, ∏ l ∈ U, w l (x l) ∂μ := mul_le_mul_of_nonneg_left hlow hε.le

end LatticeProb.Percolation.LSS
