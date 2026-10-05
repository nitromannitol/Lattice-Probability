import Mathlib

namespace LatticeProb

open MeasureTheory ProbabilityTheory Set
open scoped Real

/-- A lower Lebesgue integral over `ℝ` is bounded as soon as its truncations to the symmetric
intervals `[-n, n]` are. -/
theorem mvbe_perim_lintegral_le_of_Icc {g : ℝ → ENNReal} (hg : AEMeasurable g volume) {c : ENNReal}
    (h : ∀ n : ℕ, ∫⁻ t in Icc (-(n : ℝ)) n, g t ≤ c) : ∫⁻ t, g t ≤ c := by
  have hsup : ∫⁻ t, g t = ⨆ n : ℕ, ∫⁻ t, (Icc (-(n : ℝ)) n).indicator g t := by
    rw [← lintegral_iSup']
    · congr 1
      ext t
      apply le_antisymm
      · obtain ⟨n, hn⟩ := exists_nat_ge |t|
        refine le_iSup_of_le n ?_
        have ht : t ∈ Icc (-(n : ℝ)) n := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
        simp [indicator_of_mem ht]
      · exact iSup_le fun n => indicator_le_self _ _ t
    · exact fun n => hg.indicator measurableSet_Icc
    · refine Filter.Eventually.of_forall fun t n m hnm => ?_
      refine indicator_le_indicator_of_subset (Icc_subset_Icc ?_ ?_) (fun _ => zero_le) t
      · exact neg_le_neg (by exact_mod_cast hnm)
      · exact_mod_cast hnm
  rw [hsup]
  refine iSup_le fun n => ?_
  rw [lintegral_indicator measurableSet_Icc]
  exact h n

/-- **One-dimensional change-of-variables bound.**  For a monotone `1`-Lipschitz `u` and a
nonnegative continuous integrable `ψ`, `∫ ψ(u t) u'(t) dt ≤ ∫ ψ`. -/
theorem mvbe_perim_lintegral_comp_mul_deriv_le {u ψ : ℝ → ℝ} (hu : Monotone u)
    (hL : LipschitzWith 1 u) (hψc : Continuous ψ) (hψ0 : ∀ v, 0 ≤ ψ v)
    (hψi : Integrable ψ) :
    ∫⁻ t, ENNReal.ofReal (ψ (u t) * deriv u t) ≤ ENNReal.ofReal (∫ v, ψ v) := by
  set G : ℝ → ℝ := fun v => ∫ s in (0 : ℝ)..v, ψ s with hG
  have hGd : ∀ v, HasDerivAt G (ψ v) v := fun v =>
    (hψc.integral_hasStrictDerivAt 0 v).hasDerivAt
  have hGm : Monotone G := monotone_of_deriv_nonneg (fun v => (hGd v).differentiableAt)
    (fun v => by rw [(hGd v).deriv]; exact hψ0 v)
  set H : ℝ → ℝ := G ∘ u with hH
  have hHm : Monotone H := hGm.comp hu
  have hHd : ∀ t, DifferentiableAt ℝ u t → HasDerivAt H (ψ (u t) * deriv u t) t :=
    fun t ht => (hGd (u t)).comp t ht.hasDerivAt
  have hae : ∀ᵐ t : ℝ, deriv H t = ψ (u t) * deriv u t := by
    filter_upwards [hL.ae_differentiableAt_of_real] with t ht using (hHd t ht).deriv
  have hmeas : Measurable fun t => ψ (u t) * deriv u t :=
    (hψc.measurable.comp hL.continuous.measurable).mul (measurable_deriv u)
  refine mvbe_perim_lintegral_le_of_Icc (hmeas.ennreal_ofReal.aemeasurable) fun n => ?_
  have hn : (-(n : ℝ)) ≤ n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hint : IntervalIntegrable (deriv H) volume (-(n : ℝ)) n :=
    (hHm.monotoneOn _).intervalIntegrable_deriv
  have hmem := (hHm.monotoneOn (uIcc (-(n : ℝ)) n)).intervalIntegral_deriv_mem_uIcc
  have hnn : 0 ≤ H n - H (-(n : ℝ)) := sub_nonneg.mpr (hHm hn)
  have hle : ∫ t in (-(n : ℝ))..n, deriv H t ≤ H n - H (-(n : ℝ)) := by
    rw [uIcc_of_le hnn] at hmem
    exact hmem.2
  have hGle : H n - H (-(n : ℝ)) ≤ ∫ v, ψ v := by
    have hu' : u (-(n : ℝ)) ≤ u n := hu hn
    have h1 : IntervalIntegrable ψ volume 0 (u n) := hψc.intervalIntegrable _ _
    have h2 : IntervalIntegrable ψ volume 0 (u (-(n : ℝ))) := hψc.intervalIntegrable _ _
    have : H n - H (-(n : ℝ)) = ∫ s in (u (-(n : ℝ)))..(u n), ψ s :=
      intervalIntegral.integral_interval_sub_left h1 h2
    rw [this, intervalIntegral.integral_of_le hu']
    exact setIntegral_le_integral hψi (Filter.Eventually.of_forall hψ0)
  have hIcc : IntegrableOn (deriv H) (Icc (-(n : ℝ)) n) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hn).mp hint
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (-(n : ℝ)) n)] deriv H :=
    Filter.Eventually.of_forall fun t => hHm.deriv_nonneg
  calc ∫⁻ t in Icc (-(n : ℝ)) n, ENNReal.ofReal (ψ (u t) * deriv u t)
      = ∫⁻ t in Icc (-(n : ℝ)) n, ENNReal.ofReal (deriv H t) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae hae] with t ht using by rw [ht]
    _ = ENNReal.ofReal (∫ t in Icc (-(n : ℝ)) n, deriv H t) :=
        (ofReal_integral_eq_lintegral_ofReal hIcc hnonneg).symm
    _ = ENNReal.ofReal (∫ t in (-(n : ℝ))..n, deriv H t) := by
        rw [intervalIntegral.integral_of_le hn, integral_Icc_eq_integral_Ioc]
    _ ≤ ENNReal.ofReal (∫ v, ψ v) := ENNReal.ofReal_le_ofReal (hle.trans hGle)


/-- A continuous trapezoid dominating the indicator of `(a, b]`, with integral at most
`b - a + 2ε`. -/
theorem mvbe_perim_exists_trapezoid {a b : ℝ} (hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ v, 0 ≤ ψ v) ∧ (∀ v, a < v → v ≤ b → 1 ≤ ψ v) ∧
      Integrable ψ ∧ ∫ v, ψ v ≤ b - a + 2 * ε := by
  set ψ : ℝ → ℝ := fun v => max 0 (min 1 (min ((v - a) / ε + 1) ((b - v) / ε + 1))) with hψ
  have hcont : Continuous ψ := by fun_prop
  have hnn : ∀ v, 0 ≤ ψ v := fun v => le_max_left _ _
  have hle : ∀ v, ψ v ≤ (Icc (a - ε) (b + ε)).indicator (fun _ => (1 : ℝ)) v := by
    intro v
    by_cases hv : v ∈ Icc (a - ε) (b + ε)
    · rw [indicator_of_mem hv]
      exact max_le zero_le_one (min_le_left _ _)
    · rw [indicator_of_notMem hv]
      simp only [mem_Icc, not_and_or, not_le] at hv
      rcases hv with hv | hv
      · have : (v - a) / ε + 1 < 0 + 1 := by
          have : (v - a) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
          linarith
        have h2 : (v - a) / ε + 1 ≤ 0 := by
          rw [div_add_one hε.ne', div_nonpos_iff]
          right
          exact ⟨by linarith, hε.le⟩
        exact max_le le_rfl ((min_le_right _ _).trans ((min_le_left _ _).trans h2))
      · have h2 : (b - v) / ε + 1 ≤ 0 := by
          rw [div_add_one hε.ne', div_nonpos_iff]
          right
          exact ⟨by linarith, hε.le⟩
        exact max_le le_rfl ((min_le_right _ _).trans ((min_le_right _ _).trans h2))
  have hind : Integrable ((Icc (a - ε) (b + ε)).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have hint : Integrable ψ :=
    hind.mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn v)]; exact hle v)
  refine ⟨ψ, hcont, hnn, ?_, hint, ?_⟩
  · intro v hv1 hv2
    have h1 : 1 ≤ (v - a) / ε + 1 := by
      have : 0 ≤ (v - a) / ε := div_nonneg (by linarith) hε.le
      linarith
    have h2 : 1 ≤ (b - v) / ε + 1 := by
      have : 0 ≤ (b - v) / ε := div_nonneg (by linarith) hε.le
      linarith
    exact le_max_of_le_right (le_min le_rfl (le_min h1 h2))
  · calc ∫ v, ψ v ≤ ∫ v, (Icc (a - ε) (b + ε)).indicator (fun _ => (1 : ℝ)) v :=
          integral_mono hint hind hle
      _ = volume.real (Icc (a - ε) (b + ε)) := by
          rw [integral_indicator measurableSet_Icc]; simp
      _ = b - a + 2 * ε := by
          rw [Real.volume_real_Icc, max_eq_left (by linarith)]; ring

/-- The standard Gaussian density is at most `1 / √(2π)`. -/
theorem mvbe_perim_gaussianPDF_le (t : ℝ) :
    gaussianPDF 0 1 t ≤ ENNReal.ofReal (1 / √(2 * π)) := by
  rw [gaussianPDF_def]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [gaussianPDFReal_def]
  have h1 : Real.exp (-(t - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    have h : 0 ≤ (t - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)) := by positivity
    linarith
  have h2 : (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹ = 1 / √(2 * π) := by
    simp
  rw [h2]
  calc 1 / √(2 * π) * Real.exp (-(t - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)))
      ≤ 1 / √(2 * π) * 1 := by gcongr
    _ = 1 / √(2 * π) := mul_one _

/-- **One-dimensional Gaussian layer bound.**  For `u` monotone and `1`-Lipschitz and `a < b`,
`∫ 1_{a < u ≤ b} u' dγ ≤ (b - a) / √(2π)`. -/
theorem mvbe_perim_gaussian_layer_deriv_le {u : ℝ → ℝ} (hu : Monotone u) (hL : LipschitzWith 1 u)
    {a b : ℝ} (hab : a < b) :
    ∫⁻ t, {t | a < u t ∧ u t ≤ b}.indicator (fun t => ENNReal.ofReal (deriv u t)) t
        ∂(gaussianReal 0 1) ≤ ENNReal.ofReal ((b - a) / √(2 * π)) := by
  set c : ℝ := 1 / √(2 * π) with hc
  have hc0 : 0 ≤ c := by positivity
  have key : ∀ ε : ℝ, 0 < ε →
      ∫⁻ t, {t | a < u t ∧ u t ≤ b}.indicator (fun t => ENNReal.ofReal (deriv u t)) t
        ∂(gaussianReal 0 1) ≤ ENNReal.ofReal (c * (b - a + 2 * ε)) := by
    intro ε hε
    obtain ⟨ψ, hψc, hψ0, hψ1, hψi, hψint⟩ := mvbe_perim_exists_trapezoid hab hε
    have hmeas : Measurable fun t => ENNReal.ofReal (ψ (u t) * deriv u t) :=
      ((hψc.measurable.comp hL.continuous.measurable).mul (measurable_deriv u)).ennreal_ofReal
    have hpt : ∀ t, {t | a < u t ∧ u t ≤ b}.indicator
        (fun t => ENNReal.ofReal (deriv u t)) t ≤ ENNReal.ofReal (ψ (u t) * deriv u t) := by
      intro t
      by_cases ht : t ∈ {t | a < u t ∧ u t ≤ b}
      · rw [indicator_of_mem ht]
        refine ENNReal.ofReal_le_ofReal ?_
        have := hu.deriv_nonneg (x := t)
        nlinarith [hψ1 (u t) ht.1 ht.2]
      · rw [indicator_of_notMem ht]; exact zero_le
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
    calc ∫⁻ t, {t | a < u t ∧ u t ≤ b}.indicator (fun t => ENNReal.ofReal (deriv u t)) t
            ∂(volume.withDensity (gaussianPDF 0 1))
        ≤ ∫⁻ t, ENNReal.ofReal (ψ (u t) * deriv u t) ∂(volume.withDensity (gaussianPDF 0 1)) :=
          lintegral_mono hpt
      _ = ∫⁻ t, (gaussianPDF 0 1 * fun t => ENNReal.ofReal (ψ (u t) * deriv u t)) t := by
          rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hmeas]
      _ ≤ ∫⁻ t, ENNReal.ofReal c * ENNReal.ofReal (ψ (u t) * deriv u t) := by
          refine lintegral_mono fun t => ?_
          exact mul_le_mul_left (mvbe_perim_gaussianPDF_le t) _
      _ = ENNReal.ofReal c * ∫⁻ t, ENNReal.ofReal (ψ (u t) * deriv u t) :=
          lintegral_const_mul _ hmeas
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (∫ v, ψ v) := by
          gcongr
          exact mvbe_perim_lintegral_comp_mul_deriv_le hu hL hψc hψ0 hψi
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (b - a + 2 * ε) := by
          gcongr
      _ = ENNReal.ofReal (c * (b - a + 2 * ε)) := (ENNReal.ofReal_mul hc0).symm
  have hlim : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (c * (b - a + 2 * ε)))
      (nhdsWithin 0 (Ioi 0)) (nhds (ENNReal.ofReal ((b - a) / √(2 * π)))) := by
    have h : Filter.Tendsto (fun ε : ℝ => c * (b - a + 2 * ε)) (nhdsWithin 0 (Ioi 0))
        (nhds ((b - a) / √(2 * π))) := by
      have h0 : Continuous fun ε : ℝ => c * (b - a + 2 * ε) := by fun_prop
      have := (h0.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      convert this using 2
      simp [hc]
      ring
    exact ENNReal.tendsto_ofReal h
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)


/-- Resampling one coordinate of the standard Gaussian product measure with an independent
`N(0,1)` variable leaves it invariant. -/
theorem mvbe_perim_pi_map_update {m : ℕ} (j : Fin m) :
    ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p => Function.update p.1 j p.2) = Measure.pi fun _ : Fin m => gaussianReal 0 1 := by
  classical
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable (fun p : (Fin m → ℝ) × ℝ => Function.update p.1 j p.2) :=
    measurable_update'
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin m → ℝ) × ℝ => Function.update p.1 j p.2) ⁻¹' (univ.pi s) =
      (univ.pi (Function.update s j univ)) ×ˢ (s j) := by
    ext ⟨y, t⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod, Function.update_apply]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h j⟩
      by_cases hij : i = j
      · simp [hij]
      · simpa [hij] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hij : i = j
      · subst hij; simpa using h2
      · simpa [hij] using h1 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : ∀ i, gaussianReal 0 1 (Function.update s j univ i) =
      Function.update (fun k => gaussianReal 0 1 (s k)) j 1 i := by
    intro i
    rw [Function.apply_update (fun _ S => gaussianReal 0 1 S)]
    simp
  simp_rw [this]
  rw [Finset.prod_update_of_mem (Finset.mem_univ j), one_mul,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)]
  ring


/-- Fubini along one coordinate for the standard Gaussian product measure. -/
theorem mvbe_perim_lintegral_pi_update {m : ℕ} (j : Fin m) {g : (Fin m → ℝ) → ENNReal}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) =
      ∫⁻ y, ∫⁻ t, g (Function.update y j t) ∂(gaussianReal 0 1)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  classical
  have hmeas : Measurable (fun p : (Fin m → ℝ) × ℝ => Function.update p.1 j p.2) :=
    measurable_update'
  conv_lhs => rw [← mvbe_perim_pi_map_update j]
  rw [lintegral_map hg hmeas,
    lintegral_prod (fun p : (Fin m → ℝ) × ℝ => g (Function.update p.1 j p.2))
      (hg.comp hmeas).aemeasurable]

/-- Measurability of the `j`-th partial derivative along coordinate lines. -/
theorem mvbe_perim_measurable_partial {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hFc : Continuous F)
    (j : Fin m) :
    Measurable fun x : Fin m → ℝ => deriv (fun t => F (Function.update x j t)) (x j) := by
  classical
  have hf : Continuous (Function.uncurry fun (x : Fin m → ℝ) (t : ℝ) =>
      F (Function.update x j t)) :=
    hFc.comp (continuous_fst.update j continuous_snd)
  exact (measurable_deriv_with_param hf).comp (measurable_id.prodMk (measurable_pi_apply j))

/-- **Coordinate step.**  The `j`-th term of the perimeter bound. -/
theorem mvbe_perim_pi_coord_step {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hFc : Continuous F)
    (hmono : ∀ (x : Fin m → ℝ) (j : Fin m), Monotone fun t => F (Function.update x j t))
    (hlip : ∀ (x : Fin m → ℝ) (j : Fin m), LipschitzWith 1 fun t => F (Function.update x j t))
    {a b : ℝ} (hab : a < b) (j : Fin m) :
    ∫⁻ x, {x | a < F x ∧ F x ≤ b}.indicator
        (fun x => ENNReal.ofReal (deriv (fun t => F (Function.update x j t)) (x j))) x
      ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤
      ENNReal.ofReal ((b - a) / √(2 * π)) := by
  classical
  have hS : MeasurableSet {x : Fin m → ℝ | a < F x ∧ F x ≤ b} :=
    (measurableSet_lt measurable_const hFc.measurable).inter
      (measurableSet_le hFc.measurable measurable_const)
  have hg : Measurable fun x : Fin m → ℝ => {x | a < F x ∧ F x ≤ b}.indicator
      (fun x => ENNReal.ofReal (deriv (fun t => F (Function.update x j t)) (x j))) x :=
    ((mvbe_perim_measurable_partial hFc j).ennreal_ofReal).indicator hS
  rw [mvbe_perim_lintegral_pi_update j hg]
  calc ∫⁻ y, ∫⁻ t, {x | a < F x ∧ F x ≤ b}.indicator
          (fun x => ENNReal.ofReal (deriv (fun t => F (Function.update x j t)) (x j)))
          (Function.update y j t) ∂(gaussianReal 0 1)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ ∫⁻ _y, ENNReal.ofReal ((b - a) / √(2 * π))
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
        refine lintegral_mono fun y => ?_
        have h := mvbe_perim_gaussian_layer_deriv_le (hmono y j) (hlip y j) hab
        refine le_trans (le_of_eq ?_) h
        refine lintegral_congr fun t => ?_
        simp only [indicator, mem_setOf_eq, Function.update_idem, Function.update_self]
    _ = ENNReal.ofReal ((b - a) / √(2 * π)) := by simp

/-- **Perimeter bound on the product space.**  Let `F` be continuous on `Fin m → ℝ`, monotone
and `1`-Lipschitz in each coordinate separately, and such that the squared partial derivatives
along the coordinate lines sum to `1` almost everywhere for the product Gaussian measure.
Then every layer `{a < F ≤ b}` has Gaussian measure at most `m (b - a) / √(2π)`. -/
theorem mvbe_perim_pi_layer_le {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hFc : Continuous F)
    (hmono : ∀ (x : Fin m → ℝ) (j : Fin m), Monotone fun t => F (Function.update x j t))
    (hlip : ∀ (x : Fin m → ℝ) (j : Fin m), LipschitzWith 1 fun t => F (Function.update x j t))
    (hgrad : ∀ᵐ x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1),
      ∑ j, (deriv (fun t => F (Function.update x j t)) (x j)) ^ 2 = 1)
    {a b : ℝ} (hab : a < b) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1) {x | a < F x ∧ F x ≤ b} ≤
      ENNReal.ofReal ((m / √(2 * π)) * (b - a)) := by
  classical
  set P : Measure (Fin m → ℝ) := Measure.pi fun _ : Fin m => gaussianReal 0 1 with hP
  set S : Set (Fin m → ℝ) := {x | a < F x ∧ F x ≤ b} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const hFc.measurable).inter
      (measurableSet_le hFc.measurable measurable_const)
  set d : Fin m → (Fin m → ℝ) → ℝ :=
    fun j x => deriv (fun t => F (Function.update x j t)) (x j) with hd
  have hd0 : ∀ j x, 0 ≤ d j x := fun j x => (hmono x j).deriv_nonneg
  have hd1 : ∀ j x, d j x ≤ 1 := by
    intro j x
    have := norm_deriv_le_of_lipschitz (x₀ := x j) (hlip x j)
    simpa [hd] using (le_abs_self _).trans (by simpa using this)
  have hpt : ∀ᵐ x ∂P, S.indicator (fun _ => (1 : ENNReal)) x ≤
      ∑ j, S.indicator (fun x => ENNReal.ofReal (d j x)) x := by
    filter_upwards [hgrad] with x hx
    by_cases hxS : x ∈ S
    · simp only [indicator_of_mem hxS]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hd0 j x), ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (1 : ℝ) = ∑ j, (d j x) ^ 2 := hx.symm
        _ ≤ ∑ j, d j x := Finset.sum_le_sum fun j _ => by
            have h0 := hd0 j x
            have h1 := hd1 j x
            nlinarith
    · simp [indicator_of_notMem hxS]
  have hmeasj : ∀ j : Fin m, Measurable fun x => S.indicator
      (fun x => ENNReal.ofReal (d j x)) x := fun j =>
    ((mvbe_perim_measurable_partial hFc j).ennreal_ofReal).indicator hS
  calc P S = ∫⁻ x, S.indicator (fun _ => (1 : ENNReal)) x ∂P := by
        rw [lintegral_indicator_const hS, one_mul]
    _ ≤ ∫⁻ x, ∑ j, S.indicator (fun x => ENNReal.ofReal (d j x)) x ∂P :=
        lintegral_mono_ae hpt
    _ = ∑ j, ∫⁻ x, S.indicator (fun x => ENNReal.ofReal (d j x)) x ∂P :=
        lintegral_finsetSum _ fun j _ => hmeasj j
    _ ≤ ∑ _j : Fin m, ENNReal.ofReal ((b - a) / √(2 * π)) :=
        Finset.sum_le_sum fun j _ => mvbe_perim_pi_coord_step hFc hmono hlip hab j
    _ = ENNReal.ofReal ((m / √(2 * π)) * (b - a)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
        congr 1
        ring

/-- Updating one coordinate corresponds to translating along the corresponding basis vector. -/
theorem mvbe_perim_toLp_update {m : ℕ} (x : Fin m → ℝ) (j : Fin m) (t : ℝ) :
    WithLp.toLp 2 (Function.update x j t) =
      WithLp.toLp 2 x + (t - x j) • EuclideanSpace.single j (1 : ℝ) := by
  classical
  ext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- **Linear-in-`m` Gaussian layer bound** (report item L5).  Let `ρ` be `1`-Lipschitz,
nondecreasing in each coordinate, and differentiable `γ`-a.e. with
`∑ⱼ (∂ⱼ ρ)² = 1` a.e.  Then `γ{a < ρ ≤ b} ≤ m (b - a) / √(2π)`. -/
theorem mvbe_perim_stdGaussian_layer_le {m : ℕ} {ρ : EuclideanSpace ℝ (Fin m) → ℝ}
    (h1 : LipschitzWith 1 ρ)
    (h2 : ∀ (j : Fin m) (x : EuclideanSpace ℝ (Fin m)) (s t : ℝ), s ≤ t →
      ρ (x + s • EuclideanSpace.single j (1 : ℝ)) ≤ ρ (x + t • EuclideanSpace.single j (1 : ℝ)))
    (h3 : ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (Fin m))),
      DifferentiableAt ℝ ρ x ∧
        ∑ j, (fderiv ℝ ρ x (EuclideanSpace.single j (1 : ℝ))) ^ 2 = 1)
    {a b : ℝ} (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < ρ x ∧ ρ x ≤ b} ≤
      ENNReal.ofReal ((m / Real.sqrt (2 * Real.pi)) * (b - a)) := by
  classical
  set F : (Fin m → ℝ) → ℝ := fun y => ρ (WithLp.toLp 2 y) with hF
  have hFc : Continuous F := h1.continuous.comp (PiLp.continuous_toLp 2 _)
  -- the line `t ↦ toLp (update x j t)` is an isometric parametrisation of the `j`-th line
  have hline : ∀ (x : Fin m → ℝ) (j : Fin m),
      (fun t => F (Function.update x j t)) =
        fun t => ρ (WithLp.toLp 2 x + (t - x j) • EuclideanSpace.single j (1 : ℝ)) := by
    intro x j
    funext t
    simp only [hF, mvbe_perim_toLp_update]
  have hmono : ∀ (x : Fin m → ℝ) (j : Fin m), Monotone fun t => F (Function.update x j t) := by
    intro x j s t hst
    rw [hline]
    exact h2 j _ _ _ (by linarith)
  have hlip : ∀ (x : Fin m → ℝ) (j : Fin m),
      LipschitzWith 1 fun t => F (Function.update x j t) := by
    intro x j
    rw [hline]
    have hg : LipschitzWith 1 fun t : ℝ =>
        WithLp.toLp 2 x + (t - x j) • EuclideanSpace.single j (1 : ℝ) := by
      refine LipschitzWith.of_dist_le_mul fun s t => ?_
      have : WithLp.toLp 2 x + (s - x j) • EuclideanSpace.single j (1 : ℝ) -
          (WithLp.toLp 2 x + (t - x j) • EuclideanSpace.single j (1 : ℝ)) =
          (s - t) • EuclideanSpace.single j (1 : ℝ) := by module
      rw [dist_eq_norm, this, norm_smul, PiLp.norm_single]
      simp [Real.dist_eq]
    have := h1.comp hg
    rw [one_mul] at this
    exact this
  have hgrad : ∀ᵐ x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1),
      ∑ j, (deriv (fun t => F (Function.update x j t)) (x j)) ^ 2 = 1 := by
    rw [← map_pi_eq_stdGaussian] at h3
    have h3' := ae_of_ae_map (PiLp.continuous_toLp 2 _).aemeasurable h3
    filter_upwards [h3'] with x hx
    obtain ⟨hdiff, hsum⟩ := hx
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [hline]
    have hg : HasDerivAt (fun t : ℝ =>
        WithLp.toLp 2 x + (t - x j) • EuclideanSpace.single j (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) (x j) := by
      have := ((hasDerivAt_id (x j)).sub_const (x j)).smul_const
        (EuclideanSpace.single j (1 : ℝ))
      simpa using this.const_add (WithLp.toLp 2 x)
    have hx0 : WithLp.toLp 2 x + (x j - x j) • EuclideanSpace.single j (1 : ℝ) =
        WithLp.toLp 2 x := by simp
    have hρ : HasFDerivAt ρ (fderiv ℝ ρ (WithLp.toLp 2 x))
        (WithLp.toLp 2 x + (x j - x j) • EuclideanSpace.single j (1 : ℝ)) := by
      rw [hx0]; exact hdiff.hasFDerivAt
    exact (hρ.comp_hasDerivAt (x j) hg).deriv
  have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin m) | a < ρ y ∧ ρ y ≤ b} :=
    (measurableSet_lt measurable_const h1.continuous.measurable).inter
      (measurableSet_le h1.continuous.measurable measurable_const)
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (PiLp.continuous_toLp 2 _).measurable hS]
  exact mvbe_perim_pi_layer_le hFc hmono hlip hgrad hab

/-- **Sanity check, `m = 1`, `ρ = id`.**  The hypotheses of `mvbe_perim_stdGaussian_layer_le`
hold for the coordinate function on `EuclideanSpace ℝ (Fin 1)`, recovering the one-dimensional bound
`γ(a, b] ≤ (b - a) / √(2π)`. -/
theorem mvbe_perim_stdGaussian_layer_le_one {a b : ℝ} (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin 1)) {x | a < x 0 ∧ x 0 ≤ b} ≤
      ENNReal.ofReal ((b - a) / Real.sqrt (2 * Real.pi)) := by
  classical
  have h1 : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin 1) => x 0) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := PiLp.norm_apply_le (x - y) 0
    simpa [Real.dist_eq, dist_eq_norm] using this
  have h2 : ∀ (j : Fin 1) (x : EuclideanSpace ℝ (Fin 1)) (s t : ℝ), s ≤ t →
      (fun x : EuclideanSpace ℝ (Fin 1) => x 0) (x + s • EuclideanSpace.single j (1 : ℝ)) ≤
        (fun x : EuclideanSpace ℝ (Fin 1) => x 0) (x + t • EuclideanSpace.single j (1 : ℝ)) := by
    intro j x s t hst
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simpa using hst
  have hproj : (fun x : EuclideanSpace ℝ (Fin 1) => x 0) =
      ⇑(EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) := rfl
  have hf : ∀ x : EuclideanSpace ℝ (Fin 1), fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 1) => x 0) x =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) := by
    intro x
    rw [hproj]
    exact ContinuousLinearMap.fderiv _
  have h3 : ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (Fin 1))),
      DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin 1) => x 0) x ∧
        ∑ j, (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 1) => x 0) x
          (EuclideanSpace.single j (1 : ℝ))) ^ 2 = 1 := by
    refine Filter.Eventually.of_forall fun x => ⟨?_, ?_⟩
    · rw [hproj]
      exact ContinuousLinearMap.differentiableAt
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)
    · simp [hf]
  have := mvbe_perim_stdGaussian_layer_le h1 h2 h3 hab
  refine this.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

end LatticeProb
