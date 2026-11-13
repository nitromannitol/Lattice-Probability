import LatticeProb.Prob.Percolation.LSS.LocalLemma

/-!
# Thinning of a field of bits

The thinning construction of Liggett, Schonmann and Stacey: a finite set of
coordinates is thinned to a subset whose law is exactly the product law, while
it is almost surely contained in the set of occupied coordinates of the given
field.  The one-site extension step is the weighted local-lemma estimate of
`LatticeProb.Percolation.LSS.LocalLemma`.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb.Percolation.LSS

variable {S : Type}

/-- The indicator of a coordinate being `true` times a finite product is integrable. -/
theorem xlss_integrable_true_ind_prod (μ : Measure (S → Bool)) [IsProbabilityMeasure μ] (j : S)
    (U : Finset S) (w : S → Bool → ℝ) (hw : ∀ l ∈ U, ∀ b, 0 ≤ w l b ∧ w l b ≤ 1) :
    Integrable (fun x : S → Bool =>
      (if x j = true then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l)) μ := by
  have hm : Measurable fun x : S → Bool =>
      (if x j = true then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l) :=
    (xlss_meas_coord (fun b => if b = true then (1 : ℝ) else 0) j).mul (xlss_meas_prod U w)
  refine Integrable.of_bound (C := 1) hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h0 : 0 ≤ ∏ l ∈ U, w l (x l) := Finset.prod_nonneg fun l hl => (hw l hl _).1
  have h1 : ∏ l ∈ U, w l (x l) ≤ 1 := Finset.prod_le_one₀ (fun l hl => (hw l hl _).1)
    (fun l hl => (hw l hl _).2)
  have h2 : (0 : ℝ) ≤ (if x j = true then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h3 : (if x j = true then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 h0)]
  calc (if x j = true then (1 : ℝ) else 0) * ∏ l ∈ U, w l (x l)
      ≤ 1 * 1 := mul_le_mul h3 h1 h0 zero_le_one
    _ = 1 := one_mul 1

/-- Splitting an integral of a function that is piecewise constant in one coordinate. -/
theorem xlss_integral_ite (μ : Measure (S → Bool)) [IsProbabilityMeasure μ] (a : S) (u v : ℝ)
    (p : (S → Bool) → ℝ) (hp : Integrable p μ) :
    ∫ x, (if x a = true then u else v) * p x ∂μ =
      u * ∫ x, (if x a = true then (1 : ℝ) else 0) * p x ∂μ +
        v * ∫ x, (if x a = false then (1 : ℝ) else 0) * p x ∂μ := by
  have ht : Integrable (fun x => (if x a = true then (1 : ℝ) else 0) * p x) μ := by
    refine (hp.indicator (measurable_pi_apply a (measurableSet_singleton true))).congr ?_
    filter_upwards with x
    by_cases h : x a = true <;> simp [h]
  have hf : Integrable (fun x => (if x a = false then (1 : ℝ) else 0) * p x) μ := by
    refine (hp.indicator (measurable_pi_apply a (measurableSet_singleton false))).congr ?_
    filter_upwards with x
    by_cases h : x a = false <;> simp [h]
  have hpt : (fun x => (if x a = true then u else v) * p x) =
      fun x => u * ((if x a = true then (1 : ℝ) else 0) * p x) +
        v * ((if x a = false then (1 : ℝ) else 0) * p x) := by
    funext x
    by_cases h : x a <;> simp [h]
  rw [hpt, integral_add (ht.const_mul u) (hf.const_mul v), integral_const_mul, integral_const_mul]

/-- The weights of a thinning of the law `μ` of a field of bits on the finite set `T`: the
probability that the thinned configuration is `V` given the field `x` is `∏ l ∈ T, w l (x l) V`. -/
structure XlssThin [DecidableEq S] (μ : Measure (S → Bool)) (ρ γ : ℝ) (T : Finset S)
    (w : S → Bool → Finset S → ℝ) : Prop where
  bd : ∀ l ∈ T, ∀ V ⊆ T, ∀ b, 0 ≤ w l b V ∧ w l b V ≤ 1
  pos : ∀ l ∈ T, ∀ V ⊆ T, l ∈ V → w l false V = 0 ∧ ρ ≤ w l true V
  neg : ∀ l ∈ T, ∀ V ⊆ T, l ∉ V → w l false V = 1 ∧ γ ≤ w l true V
  norm : ∀ x : S → Bool, ∑ V ∈ T.powerset, ∏ l ∈ T, w l (x l) V = 1
  marg : ∀ V ⊆ T, ∫ x, ∏ l ∈ T, w l (x l) V ∂μ = ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)

/-- The empty thinning: the only subset of the empty set is the empty set, and its law is the
point mass at the empty set, which is the product law. -/
theorem xlss_thin_empty [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) : ∃ w, XlssThin μ ρ γ ∅ w := by
  refine ⟨fun _ _ _ => 1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l hl; exact absurd hl (Finset.notMem_empty l)
  · intro l hl; exact absurd hl (Finset.notMem_empty l)
  · intro l hl; exact absurd hl (Finset.notMem_empty l)
  · intro x
    rw [Finset.powerset_empty, Finset.sum_singleton]
    simp
  · intro V hV
    rw [Finset.subset_empty] at hV
    subst hV
    simp

/-- One step of the sequential construction of the thinning: a new site is added.  Given a
thinning on `T`, the site `a` is retained on the event that it is occupied, with a conditional
probability chosen so that the marginal of the new thinning stays product, and the weighted
local-lemma estimate guarantees that this probability stays between `ρ` and `ρ / (1 - ε)`. -/
theorem xlss_thin_step [DecidableEq S] (G : SimpleGraph S) (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ] (Δ : ℕ)
    (hdeg : ∀ s, (G.neighborSet s).Finite ∧ (G.neighborSet s).ncard ≤ Δ)
    (hdep : HasDependenceGraph G μ) (q ρ ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hερ : ε < 1 - ρ) (hmarg : ∀ s, μ.real {x | x s = false} ≤ q)
    (hqε : q ≤ ε * (min ρ (1 - ρ / (1 - ε))) ^ Δ * (1 - Δ * ε))
    (T : Finset S) (a : S) (ha : a ∉ T) (w : S → Bool → Finset S → ℝ)
    (hw : XlssThin μ ρ (1 - ρ / (1 - ε)) T w) :
    ∃ w', XlssThin μ ρ (1 - ρ / (1 - ε)) (insert a T) w' := by
  have hε1 : (0 : ℝ) < 1 - ε := by linarith
  have hγ0 : 0 < 1 - ρ / (1 - ε) := by
    rw [sub_pos, div_lt_one hε1]; linarith
  set g : ℝ := min ρ (1 - ρ / (1 - ε)) with hg
  have hg0 : 0 ≤ g := by rw [hg]; exact le_min hρ0.le hγ0.le
  have hg1 : g ≤ 1 := by rw [hg]; exact (min_le_left _ _).trans hρ1.le
  have hqg : q ≤ ε * g ^ Δ * (1 - Δ * ε) := by rwa [hg] at hqε
  have hEraseSub : ∀ V' ⊆ insert a T, V'.erase a ⊆ T := by
    intro V' hV' x hx
    obtain ⟨hxa, hxV'⟩ := Finset.mem_erase.mp hx
    rcases Finset.mem_insert.mp (hV' hxV') with h | h
    · exact absurd h hxa
    · exact h
  have hSubOfNotMem : ∀ V' ⊆ insert a T, a ∉ V' → V' ⊆ T := by
    intro V' hV' haV' x hx
    rcases Finset.mem_insert.mp (hV' hx) with h | h
    · exact absurd (h ▸ hx) haV'
    · exact h
  let B : Finset S → ℝ := fun V => ∫ x, ∏ l ∈ T, w l (x l) V ∂μ
  let D : Finset S → ℝ := fun V =>
    ∫ x, (if x a = false then (1 : ℝ) else 0) * ∏ l ∈ T, w l (x l) V ∂μ
  let A : Finset S → ℝ := fun V =>
    ∫ x, (if x a = true then (1 : ℝ) else 0) * ∏ l ∈ T, w l (x l) V ∂μ
  let cadd : Finset S → ℝ := fun V => ρ * B V / A V
  have hInt : ∀ V ⊆ T, Integrable (fun x : S → Bool => ∏ l ∈ T, w l (x l) V) μ := fun V hV =>
    xlss_integrable_prod μ T (fun l b => w l b V) (fun l hl => hw.bd l hl V hV)
  have hBpos : ∀ V ⊆ T, 0 < B V := by
    intro V hV
    dsimp only [B]
    rw [hw.marg V hV]
    exact mul_pos (pow_pos hρ0 _) (pow_pos (by linarith) _)
  have hDle : ∀ V ⊆ T, D V ≤ ε * B V := by
    intro V hV
    have hbdV : ∀ l ∈ T, (∀ b, 0 ≤ w l b V ∧ w l b V ≤ 1) ∧
        ∀ b, (l ∉ V ∨ b = true) → g ≤ w l b V := by
      intro l hl
      refine ⟨fun b => hw.bd l hl V hV b, ?_⟩
      intro b hb
      by_cases hlV : l ∈ V
      · rcases hb with hb | hb
        · exact absurd hlV hb
        · subst hb
          exact (min_le_left _ _).trans (hw.pos l hl V hV hlV).2
      · cases b
        · rw [(hw.neg l hl V hV hlV).1]; exact hg1
        · exact (min_le_right _ _).trans (hw.neg l hl V hV hlV).2
    have := xlss_lll G μ Δ hdeg hdep q ε g hε hg0 hg1 hqg hmarg V
      (fun l b => w l b V) T hbdV a ha
    dsimp only [B, D]
    simpa using this
  have hABD : ∀ V ⊆ T, A V + D V = B V := by
    intro V hV
    have ht : Integrable (fun x : S → Bool =>
        (if x a = true then (1 : ℝ) else 0) * ∏ l ∈ T, w l (x l) V) μ :=
      xlss_integrable_true_ind_prod μ a T (fun l b => w l b V)
        (fun l hl => hw.bd l hl V hV)
    have hf : Integrable (fun x : S → Bool =>
        (if x a = false then (1 : ℝ) else 0) * ∏ l ∈ T, w l (x l) V) μ :=
      xlss_integrable_ind_prod μ a T (fun l b => w l b V)
        (fun l hl => hw.bd l hl V hV)
    dsimp only [A, D, B]
    rw [← integral_add ht hf]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases h : x a <;> simp [h]
  have hApos : ∀ V ⊆ T, 0 < A V := by
    intro V hV
    have hb := hBpos V hV
    have hd := hDle V hV
    have habd := hABD V hV
    nlinarith
  have hcadd0 : ∀ V ⊆ T, 0 ≤ cadd V := by
    intro V hV
    dsimp only [cadd]
    exact div_nonneg (mul_nonneg hρ0.le (hBpos V hV).le) (hApos V hV).le
  have hcadd_ge : ∀ V ⊆ T, ρ ≤ cadd V := by
    intro V hV
    have hApos' := hApos V hV
    have hAle : A V ≤ B V := by
      have habd := hABD V hV
      have hd0 : 0 ≤ D V := by
        dsimp only [D]
        exact integral_nonneg fun x => by
          have : (0 : ℝ) ≤ (if x a = false then (1 : ℝ) else 0) := by split_ifs <;> norm_num
          exact mul_nonneg this (Finset.prod_nonneg fun l hl => (hw.bd l hl V hV _).1)
      linarith
    dsimp only [cadd]
    rw [le_div_iff₀ hApos']
    nlinarith [hAle]
  have hcadd_le : ∀ V ⊆ T, cadd V ≤ ρ / (1 - ε) := by
    intro V hV
    have hApos' := hApos V hV
    have hd := hDle V hV
    have habd := hABD V hV
    dsimp only [cadd]
    rw [div_le_iff₀ hApos', div_mul_eq_mul_div, le_div_iff₀' hε1]
    nlinarith
  have hcadd1 : ∀ V ⊆ T, cadd V ≤ 1 := by
    intro V hV
    have h1 := hcadd_le V hV
    have h2 : ρ / (1 - ε) ≤ 1 := by rw [div_le_one hε1]; linarith
    linarith
  have hcadd_mul : ∀ V ⊆ T, cadd V * A V = ρ * B V := by
    intro V hV
    dsimp only [cadd]
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt (hApos V hV)), mul_one]
  let w' : S → Bool → Finset S → ℝ := fun l b V' =>
    if l = a then
      (if a ∈ V' then (if b then cadd (V'.erase a) else 0)
       else (if b then 1 - cadd (V'.erase a) else 1))
    else w l b (V'.erase a)
  have hw'T : ∀ l ∈ T, ∀ b V', w' l b V' = w l b (V'.erase a) := by
    intro l hl b V'
    dsimp only [w']
    rw [ite_eq_right]
    exact fun h => ha (h ▸ hl)
  have hw'a : ∀ b V', w' a b V' =
      (if a ∈ V' then (if b then cadd (V'.erase a) else 0)
       else (if b then 1 - cadd (V'.erase a) else 1)) := by
    intro b V'
    dsimp only [w']
    rw [ite_eq_left rfl]
  refine ⟨w', ?_, ?_, ?_, ?_, ?_⟩
  · -- bd
    intro l hl V' hV' b
    rcases Finset.mem_insert.mp hl with h | h
    · subst l
      rw [hw'a]
      by_cases hmem : a ∈ V'
      · rw [ite_eq_left hmem]
        cases b
        · simp only [Bool.false_eq_true, ite_false]
          exact ⟨le_refl 0, zero_le_one⟩
        · simp only [ite_true]
          exact ⟨hcadd0 _ (hEraseSub V' hV'), hcadd1 _ (hEraseSub V' hV')⟩
      · rw [ite_eq_right hmem]
        cases b
        · simp only [Bool.false_eq_true, ite_false]
          exact ⟨zero_le_one, le_refl 1⟩
        · simp only [ite_true]
          exact ⟨sub_nonneg.mpr (hcadd1 _ (hEraseSub V' hV')),
            by linarith [hcadd0 _ (hEraseSub V' hV')]⟩
    · rw [hw'T l h b V']
      exact hw.bd l h (V'.erase a) (hEraseSub V' hV') b
  · -- pos
    intro l hl V' hV' hlV'
    rcases Finset.mem_insert.mp hl with h | h
    · subst l
      rw [hw'a false V', hw'a true V', ite_eq_left hlV', ite_eq_left hlV']
      simp only [Bool.false_eq_true, ite_false, ite_true]
      exact ⟨trivial, hcadd_ge _ (hEraseSub V' hV')⟩
    · have hl' : l ∈ V'.erase a := Finset.mem_erase.mpr
        ⟨fun hh => ha (hh ▸ h), hlV'⟩
      rw [hw'T l h false V', hw'T l h true V']
      exact hw.pos l h (V'.erase a) (hEraseSub V' hV') hl'
  · -- neg
    intro l hl V' hV' hlV'
    rcases Finset.mem_insert.mp hl with h | h
    · subst l
      rw [hw'a false V', hw'a true V', ite_eq_right hlV', ite_eq_right hlV']
      simp only [Bool.false_eq_true, ite_false, ite_true]
      exact ⟨trivial, by
        have h1 := hcadd_le _ (hEraseSub V' hV')
        linarith⟩
    · have hl' : l ∉ V'.erase a := fun hx => hlV' (Finset.mem_of_mem_erase hx)
      rw [hw'T l h false V', hw'T l h true V']
      exact hw.neg l h (V'.erase a) (hEraseSub V' hV') hl'
  · -- norm
    intro x
    rw [Finset.sum_powerset_insert ha]
    have h1 : ∀ V ∈ T.powerset,
        ∏ l ∈ insert a T, w' l (x l) V =
          (if x a = true then 1 - cadd V else 1) * ∏ l ∈ T, w l (x l) V := by
      intro V hV
      have hVT : V ⊆ T := Finset.mem_powerset.mp hV
      have haV : a ∉ V := fun h => ha (hVT h)
      rw [Finset.prod_insert ha, hw'a, ite_eq_right haV]
      have hTa : ∏ l ∈ T, w' l (x l) V = ∏ l ∈ T, w l (x l) V := by
        refine Finset.prod_congr rfl fun l hl => ?_
        rw [hw'T l hl, Finset.erase_eq_of_notMem haV]
      rw [hTa, Finset.erase_eq_of_notMem haV]
    have h2 : ∀ V ∈ T.powerset,
        ∏ l ∈ insert a T, w' l (x l) (insert a V) =
          (if x a = true then cadd V else 0) * ∏ l ∈ T, w l (x l) V := by
      intro V hV
      have hVT : V ⊆ T := Finset.mem_powerset.mp hV
      have haV : a ∉ V := fun h => ha (hVT h)
      rw [Finset.prod_insert ha, hw'a, ite_eq_left (Finset.mem_insert_self a V)]
      have hTa : ∏ l ∈ T, w' l (x l) (insert a V) = ∏ l ∈ T, w l (x l) V := by
        refine Finset.prod_congr rfl fun l hl => ?_
        rw [hw'T l hl, Finset.erase_insert haV]
      rw [hTa, Finset.erase_insert haV]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun V hV => ?_), hw.norm x]
    have : (if x a = true then 1 - cadd V else 1) +
        (if x a = true then cadd V else 0) = 1 := by
      by_cases h : x a = true <;> simp [h]
    rw [← add_mul, this, one_mul]
  · -- marg
    intro V' hV'
    have hV'T : V'.erase a ⊆ T := hEraseSub V' hV'
    by_cases hmem : a ∈ V'
    · have hfac : ∀ x : S → Bool, ∏ l ∈ insert a T, w' l (x l) V' =
          (if x a = true then cadd (V'.erase a) else 0) *
            ∏ l ∈ T, w l (x l) (V'.erase a) := by
        intro x
        rw [Finset.prod_insert ha, hw'a, ite_eq_left hmem]
        have hTa : ∏ l ∈ T, w' l (x l) V' = ∏ l ∈ T, w l (x l) (V'.erase a) := by
          refine Finset.prod_congr rfl fun l hl => ?_
          rw [hw'T l hl]
        rw [hTa]
      simp_rw [hfac]
      rw [xlss_integral_ite μ a (cadd (V'.erase a)) 0
        (fun x => ∏ l ∈ T, w l (x l) (V'.erase a)) (hInt _ hV'T)]
      rw [zero_mul, add_zero]
      have hkey : cadd (V'.erase a) *
          ∫ x, (if x a = true then (1 : ℝ) else 0) *
            ∏ l ∈ T, w l (x l) (V'.erase a) ∂μ = ρ * B (V'.erase a) :=
        hcadd_mul (V'.erase a) hV'T
      rw [hkey]
      dsimp only [B]
      rw [hw.marg (V'.erase a) hV'T]
      have hcard : V'.card = (V'.erase a).card + 1 := by
        have := Finset.card_erase_add_one hmem
        omega
      have hTcard : (insert a T).card = T.card + 1 := Finset.card_insert_of_notMem ha
      rw [hTcard, hcard, pow_succ]
      have hexp : T.card + 1 - ((V'.erase a).card + 1) = T.card - (V'.erase a).card := by
        have : (V'.erase a).card ≤ T.card := Finset.card_le_card hV'T
        omega
      rw [hexp]
      ring
    · have hVT : V' ⊆ T := hSubOfNotMem V' hV' hmem
      have hfac : ∀ x : S → Bool, ∏ l ∈ insert a T, w' l (x l) V' =
          (if x a = true then 1 - cadd V' else 1) * ∏ l ∈ T, w l (x l) V' := by
        intro x
        rw [Finset.prod_insert ha, hw'a, ite_eq_right hmem]
        have hTa : ∏ l ∈ T, w' l (x l) V' = ∏ l ∈ T, w l (x l) V' := by
          refine Finset.prod_congr rfl fun l hl => ?_
          rw [hw'T l hl, Finset.erase_eq_of_notMem hmem]
        rw [hTa, Finset.erase_eq_of_notMem hmem]
      simp_rw [hfac]
      rw [xlss_integral_ite μ a (1 - cadd V') 1
        (fun x => ∏ l ∈ T, w l (x l) V') (hInt V' hVT)]
      rw [one_mul]
      have hgoal : (1 - cadd V') * A V' + D V' = (1 - ρ) * B V' := by
        have habd := hABD V' hVT
        have hcm := hcadd_mul V' hVT
        nlinarith
      rw [hgoal]
      dsimp only [B]
      rw [hw.marg V' hVT]
      have hTcard : (insert a T).card = T.card + 1 := Finset.card_insert_of_notMem ha
      rw [hTcard]
      have hexp : T.card + 1 - V'.card = (T.card - V'.card) + 1 := by
        have : V'.card ≤ T.card := Finset.card_le_card hVT
        omega
      rw [hexp, pow_succ]
      ring

/-- The thinning exists on every finite set of coordinates. -/
theorem xlss_thin_exists [DecidableEq S] (G : SimpleGraph S) (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ] (Δ : ℕ)
    (hdeg : ∀ s, (G.neighborSet s).Finite ∧ (G.neighborSet s).ncard ≤ Δ)
    (hdep : HasDependenceGraph G μ) (q ρ ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hερ : ε < 1 - ρ) (hmarg : ∀ s, μ.real {x | x s = false} ≤ q)
    (hqε : q ≤ ε * (min ρ (1 - ρ / (1 - ε))) ^ Δ * (1 - Δ * ε))
    (T : Finset S) :
    ∃ w, XlssThin μ ρ (1 - ρ / (1 - ε)) T w := by
  induction T using Finset.induction_on with
  | empty => exact xlss_thin_empty μ ρ (1 - ρ / (1 - ε))
  | insert a T ha ih =>
    obtain ⟨w, hw⟩ := ih
    exact xlss_thin_step G μ Δ hdeg hdep q ρ ε hρ0 hρ1 hε hερ hmarg hqε T a ha w hw

end LatticeProb.Percolation.LSS
