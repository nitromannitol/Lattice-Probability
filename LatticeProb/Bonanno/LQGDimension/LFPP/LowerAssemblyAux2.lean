/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.LowerAssemblyAux2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.LowerAssemblyAux1
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality

/-!
# Finite-dimensional probability estimates for the lower assembly (`LA`)

* `map_adjoint_isometry_stdGaussian`: the adjoint of a linear isometry `ι : E → F` pushes the
  standard Gaussian of `F` to the standard Gaussian of `E` (so `⟪ι a, y⟫ = ⟪a, ι† y⟫` realises
  the glued band field of `C36` with its original law).
* `stdGaussian_exists_abs_inner_gt_le`: Chernoff bound plus union bound for
  `max_{s ∈ S} |⟪w s, y⟫|` when `‖w s‖² ≤ C`.
* `measure_preimage_eq_stdGaussian`: transfer of the law of a finite vector (`P1`) to Gram space.
* `prob_all_cost_gt_le`: the key estimate.  With the band Gram vectors `u`, the selection
  `sel`, the coupling `(ι, V)` of `C36`, and the finite point set `S` containing all Riemann
  points, the probability that *every* polygon has Riemann cost `> t` under `h_ε` is at most
  `2|S| e^{-lT + C_ρ l²/2} + e^{ξ T} E[cost_band(sel)] / t`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.LowerAsm

open Blueprint.Draft

section Gauss

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The adjoint of a linear isometry `E → F` maps the standard Gaussian of `F` to the standard
Gaussian of `E`. -/
theorem map_adjoint_isometry_stdGaussian (ι : E →ₗᵢ[ℝ] F) :
    (stdGaussian F).map (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) =
      stdGaussian E := by
  apply IsGaussian.ext
  · simp only [id]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id, integral_id_stdGaussian,
      map_zero, integral_id_stdGaussian]
  · ext u w
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      covarianceBilin_stdGaussian, ContinuousLinearMap.adjoint_adjoint, innerSL_apply_apply,
      innerSL_apply_apply]
    exact ι.inner_map_map u w

/-- Chernoff and union bound: `P(∃ s ∈ S, |⟪w s, y⟫| > T) ≤ 2 |S| e^{-lT + C l²/2}`. -/
theorem stdGaussian_exists_abs_inner_gt_le {ι : Type*} (S : Finset ι) (w : ι → E) {C T l : ℝ}
    (hl : 0 ≤ l) (hw : ∀ s ∈ S, ‖w s‖ ^ 2 ≤ C) :
    stdGaussian E {y | ∃ s ∈ S, T < |⟪w s, y⟫|} ≤
      ENNReal.ofReal (2 * S.card * Real.exp (-l * T + C * l ^ 2 / 2)) := by
  have hone : ∀ s ∈ S, (stdGaussian E).real {y | T < |⟪w s, y⟫|} ≤
      2 * Real.exp (-l * T + C * l ^ 2 / 2) := by
    intro s hs
    have hsub : {y | T < |⟪w s, y⟫|} ⊆ {y | T ≤ ⟪w s, y⟫} ∪ {y | T ≤ ⟪-w s, y⟫} := by
      intro y hy
      simp only [mem_ofPred_eq, mem_union, inner_neg_left] at hy ⊢
      rcases le_or_gt 0 ⟪w s, y⟫ with h0 | h0
      · left
        rw [abs_of_nonneg h0] at hy
        exact hy.le
      · right
        rw [abs_of_neg h0] at hy
        exact hy.le
    have h1 := measure_ge_le_exp_mul_mgf (μ := stdGaussian E) (X := fun y => ⟪w s, y⟫) T hl
      (GaussianMax.integrable_exp_mul_inner (w s) l)
    have h2 := measure_ge_le_exp_mul_mgf (μ := stdGaussian E) (X := fun y => ⟪-w s, y⟫) T hl
      (GaussianMax.integrable_exp_mul_inner (-w s) l)
    rw [GaussianMax.mgf_inner] at h1 h2
    rw [norm_neg] at h2
    have hb : Real.exp (-l * T) * Real.exp (‖w s‖ ^ 2 * l ^ 2 / 2) ≤
        Real.exp (-l * T + C * l ^ 2 / 2) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_right (hw s hs) (sq_nonneg l)
      linarith
    calc (stdGaussian E).real {y | T < |⟪w s, y⟫|}
        ≤ (stdGaussian E).real ({y | T ≤ ⟪w s, y⟫} ∪ {y | T ≤ ⟪-w s, y⟫}) :=
          measureReal_mono hsub
      _ ≤ (stdGaussian E).real {y | T ≤ ⟪w s, y⟫} +
            (stdGaussian E).real {y | T ≤ ⟪-w s, y⟫} :=
          measureReal_union_le _ _
      _ ≤ _ := by linarith
  have hset : {y | ∃ s ∈ S, T < |⟪w s, y⟫|} = ⋃ s ∈ S, {y | T < |⟪w s, y⟫|} := by
    ext y
    simp
  rw [hset, ← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (stdGaussian E).real (⋃ s ∈ S, {y | T < |⟪w s, y⟫|})
      ≤ ∑ s ∈ S, (stdGaussian E).real {y | T < |⟪w s, y⟫|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ S, 2 * Real.exp (-l * T + C * l ^ 2 / 2) := Finset.sum_le_sum hone
    _ = 2 * S.card * Real.exp (-l * T + C * l ^ 2 / 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

omit [BorelSpace E] in
/-- Markov's inequality under the standard Gaussian, in `ENNReal` form. -/
theorem stdGaussian_ge_le_integral_div (g : E → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hint : Integrable g (stdGaussian E)) {c : ℝ} (hc : 0 < c) :
    stdGaussian E {x | c ≤ g x} ≤ ENNReal.ofReal ((∫ x, g x ∂stdGaussian E) / c) := by
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hc]
  have := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hg0) hint c
  linarith

/-- If a finite random vector has the Gaussian law with covariance `C` on `S`, and `V` is a
Gram realisation of `C` on `S`, then the probability of any measurable event of the vector is
the Gram-space probability. -/
theorem measure_preimage_eq_stdGaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} (S : Finset ι) (X : Ω → S → ℝ) (C : ι → ι → ℝ)
    (hX : HasLaw X (gaussVecLaw S C) P) (V : ι → E)
    (hV : ∀ i ∈ S, ∀ j ∈ S, ⟪V i, V j⟫ = C i j) {A : Set (S → ℝ)} (hA : MeasurableSet A) :
    P (X ⁻¹' A) = stdGaussian E {y | (fun i : S => ⟪V i, y⟫) ∈ A} := by
  have hM : (Matrix.of fun i j : S => C i j) = Matrix.of fun i j : S => ⟪V i, V j⟫ := by
    ext i j
    simp [hV i i.2 j j.2]
  have hco : Measurable (fun (x : EuclideanSpace ℝ S) (i : S) => x i) := by fun_prop
  rw [← Measure.map_apply_of_aemeasurable hX.aemeasurable hA, hX.map_eq]
  unfold gaussVecLaw
  rw [hM, ← map_gramMap_stdGaussian S V, Measure.map_map hco (gramMap S V).continuous.measurable,
    Measure.map_apply (hco.comp (gramMap S V).continuous.measurable) hA]
  congr 1

/-- **Key finite-dimensional estimate.**  Let `S` contain all Riemann points of the polygons
`poly i`, let `u` be Gram vectors (band field) with a selection `sel` whose selected cost is
integrable, and let `(ι, V)` be a coupling as in `C36`: `V` realises the circle-average
covariance at `ε` on `S` and `‖V s - ι (u s)‖² ≤ C_ρ`.  Then
`P(∀ i, cost_i(h_ε) > t) ≤ 2|S| e^{-lT + C_ρ l²/2} + e^{ξ T} E[cost_band(sel)] / t`. -/
theorem prob_all_cost_gt_le (hP1 : SegCombLaw) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : ℝ → ℂ → Ω → ℝ} (hG : IsGFFCircleAverage h P) {ε ξ : ℝ} (hε : 0 < ε) (hξ : 0 ≤ ξ)
    {m Nr : ℕ} (poly : Fin m → List ℂ) (S : Finset ℂ)
    (hpts : ∀ i, riemannPts Nr (poly i) ⊆ ↑S) (u : ℂ → E) (sel : E → Fin m)
    (hint : Integrable (fun x => riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫))
      (stdGaussian E))
    (ι : E →ₗᵢ[ℝ] F) (V : ℂ → F)
    (hV : ∀ s ∈ S, ∀ s' ∈ S, ⟪V s, V s'⟫ = gffCircleCov ε s ε s')
    {Cρ : ℝ} (hw : ∀ s ∈ S, ‖V s - ι (u s)‖ ^ 2 ≤ Cρ) {t T l : ℝ} (ht : 0 < t) (hl : 0 ≤ l) :
    P {ω | ∀ i, t < riemannCost ξ Nr (poly i) (fun z => h ε z ω)} ≤
      ENNReal.ofReal (2 * S.card * Real.exp (-l * T + Cρ * l ^ 2 / 2)) +
      ENNReal.ofReal (Real.exp (ξ * T) *
        (∫ x, riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫) ∂stdGaussian E) / t) := by
  set g : E → ℝ := fun x => riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫) with hg
  -- the finite vector `(h_ε(s))_{s ∈ S}` and its law (node `P1` with point masses)
  have hX := hP1 Ω P h hG ε hε ℂ S ptComb
  have hXval : ∀ ω (i : S), (ptComb (i : ℂ)).avg (fun z => h ε z ω) = h ε i ω :=
    fun ω i => avg_ptComb _ _
  -- the event, as a measurable set of vectors
  have hA : MeasurableSet {v : S → ℝ | ∀ i, t < riemannCost ξ Nr (poly i) (extS S v)} := by
    have e : {v : S → ℝ | ∀ i, t < riemannCost ξ Nr (poly i) (extS S v)} =
        ⋂ i, {v : S → ℝ | t < riemannCost ξ Nr (poly i) (extS S v)} := by
      ext v
      simp
    rw [e]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (continuous_riemannCost_extS ξ Nr (poly i) S).measurable
  have hsub1 : {ω | ∀ i, t < riemannCost ξ Nr (poly i) (fun z => h ε z ω)} ⊆
      (fun ω (i : S) => (ptComb (i : ℂ)).avg (fun z => h ε z ω)) ⁻¹'
        {v : S → ℝ | ∀ i, t < riemannCost ξ Nr (poly i) (extS S v)} := by
    intro ω hω i
    refine lt_of_lt_of_eq (hω i) (riemannCost_congr ξ Nr (poly i) fun p hp => ?_)
    rw [extS_of_mem _ (hpts i hp)]
    exact (hXval ω ⟨p, hpts i hp⟩).symm
  have hVC : ∀ i ∈ S, ∀ j ∈ S, ⟪V i, V j⟫ = (ptComb i).circCov ε (ptComb j) := by
    intro i hi j hj
    rw [circCov_ptComb]
    exact hV i hi j hj
  have htr := measure_preimage_eq_stdGaussian S _ _ hX V hVC hA
  -- Gram space: the band field is `⟪u s, pr y⟫` with `pr = ι†`
  set pr : F →L[ℝ] E := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hpr
  have hprinner : ∀ a y, ⟪ι a, y⟫ = ⟪a, pr y⟫ := by
    intro a y
    rw [hpr, ContinuousLinearMap.adjoint_inner_right]
    rfl
  set c : ℝ := t * Real.exp (-(ξ * T)) with hc
  have hc0 : 0 < c := by positivity
  have hsub2 : {y : F | (fun i : S => ⟪V i, y⟫) ∈
        {v : S → ℝ | ∀ i, t < riemannCost ξ Nr (poly i) (extS S v)}} ⊆
      {y | ∃ s ∈ S, T < |⟪V s - ι (u s), y⟫|} ∪ pr ⁻¹' {x | c ≤ g x} := by
    intro y hy
    by_cases hbad : ∃ s ∈ S, T < |⟪V s - ι (u s), y⟫|
    · exact Or.inl hbad
    · right
      push Not at hbad
      show c ≤ g (pr y)
      have h1 := hy (sel (pr y))
      have hc1 : riemannCost ξ Nr (poly (sel (pr y))) (extS S fun i : S => ⟪V i, y⟫) =
          riemannCost ξ Nr (poly (sel (pr y))) (fun z => ⟪V z, y⟫) :=
        riemannCost_congr _ _ _ fun p hp => by rw [extS_of_mem _ (hpts _ hp)]
      rw [hc1] at h1
      have h2 := riemannCost_le_exp_mul ξ hξ Nr (poly (sel (pr y))) (φ := fun z => ⟪V z, y⟫)
        (ψ := fun z => ⟪u z, pr y⟫) T (fun p hp => by
          have := hbad p (hpts _ hp)
          rw [inner_sub_left, hprinner] at this
          linarith [le_abs_self (⟪V p, y⟫ - ⟪u p, pr y⟫)])
      have h3 : t < Real.exp (ξ * T) * g (pr y) := lt_of_lt_of_le h1 h2
      calc c = t * Real.exp (-(ξ * T)) := rfl
        _ ≤ Real.exp (ξ * T) * g (pr y) * Real.exp (-(ξ * T)) :=
          mul_le_mul_of_nonneg_right h3.le (Real.exp_pos _).le
        _ = g (pr y) := by
          rw [mul_comm (Real.exp (ξ * T)), mul_assoc, ← Real.exp_add, add_neg_cancel,
            Real.exp_zero, mul_one]
  have hfirst : stdGaussian F {y | ∃ s ∈ S, T < |⟪V s - ι (u s), y⟫|} ≤
      ENNReal.ofReal (2 * S.card * Real.exp (-l * T + Cρ * l ^ 2 / 2)) :=
    stdGaussian_exists_abs_inner_gt_le S (fun s => V s - ι (u s)) hl hw
  have hsecond : stdGaussian F (pr ⁻¹' {x | c ≤ g x}) ≤
      ENNReal.ofReal (Real.exp (ξ * T) * (∫ x, g x ∂stdGaussian E) / t) := by
    calc stdGaussian F (pr ⁻¹' {x | c ≤ g x}) ≤ (stdGaussian F).map pr {x | c ≤ g x} :=
          Measure.le_map_apply pr.continuous.aemeasurable _
      _ = stdGaussian E {x | c ≤ g x} := by rw [hpr, map_adjoint_isometry_stdGaussian]
      _ ≤ ENNReal.ofReal ((∫ x, g x ∂stdGaussian E) / c) :=
          stdGaussian_ge_le_integral_div g (fun x => riemannCost_nonneg _ _ _ _) hint hc0
      _ = ENNReal.ofReal (Real.exp (ξ * T) * (∫ x, g x ∂stdGaussian E) / t) := by
          congr 1
          rw [hc, Real.exp_neg]
          field_simp
  calc P {ω | ∀ i, t < riemannCost ξ Nr (poly i) (fun z => h ε z ω)}
      ≤ P ((fun ω (i : S) => (ptComb (i : ℂ)).avg (fun z => h ε z ω)) ⁻¹'
          {v : S → ℝ | ∀ i, t < riemannCost ξ Nr (poly i) (extS S v)}) := measure_mono hsub1
    _ = stdGaussian F {y : F | (fun i : S => ⟪V i, y⟫) ∈
          {v : S → ℝ | ∀ i, t < riemannCost ξ Nr (poly i) (extS S v)}} := htr
    _ ≤ stdGaussian F {y | ∃ s ∈ S, T < |⟪V s - ι (u s), y⟫|} +
          stdGaussian F (pr ⁻¹' {x | c ≤ g x}) :=
        (measure_mono hsub2).trans (measure_union_le _ _)
    _ ≤ _ := add_le_add hfirst hsecond

end Gauss

end LQGDimension.LowerAsm
