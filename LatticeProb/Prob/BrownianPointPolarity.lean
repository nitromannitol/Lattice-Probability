import LatticeProb.Prob.BrownianExitKelvin
import LatticeProb.Prob.BrownianExitPosition
import LatticeProb.Prob.BrownianOpenExitFinite

/-!
# Points are polar for planar Brownian motion

Let `B` be a Brownian motion on `ℝ²` (`LatticeProb.IsBrownianSpace 2 x B P`) started at `x`, and
let `y ≠ x`. For radii `0 < ε < ‖x - y‖ < R`, let `τ` be the exit time of the open annulus
`{z | ε < ‖z - y‖ < R}`. The function `log ‖· - y‖` is harmonic on a neighbourhood of the closed
annulus, so `E log ‖B_τ - y‖ = log ‖x - y‖`; the exit position lies on one of the two boundary
circles almost surely, which gives the classical harmonic measure of the inner circle,
`P(‖B_τ - y‖ ≤ ε) = (log R - log ‖x - y‖) / (log R - log ε)`.

If the path visits `y` at time `t₀`, then for `R` larger than `sup_{s ≤ t₀} ‖B_s - y‖` the path
leaves every such annulus through the inner circle. Letting `ε → 0` for fixed `R`, and then taking
the union over integer `R`, shows that `B` almost surely never visits `y`.

## Main results

* `LatticeProb.IsBrownianSpace.aemeasurable_openExitPosition`: the exit position of a Brownian
  motion from an open set is almost everywhere measurable.
* `LatticeProb.IsBrownianSpace.measureReal_annulus_exit_inner`: the harmonic measure of the inner
  circle of an annulus around `y`.
* `LatticeProb.IsBrownianSpace.ae_forall_ne`: a planar Brownian motion started at `x` almost surely
  never visits a point `y ≠ x` (points are polar).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The exit position of a Brownian motion from an open set is almost everywhere measurable: it
agrees almost surely with a measurable functional of the continuous version of the path. -/
theorem IsBrownianSpace.aemeasurable_openExitPosition {d : ℕ} (hd : 1 ≤ d)
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    AEMeasurable (fun ω ↦ B (openExitTime B U ω).toNNReal ω) P := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hsd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  obtain ⟨C, hCm, hC, -, hCW, -⟩ := hB.exists_continuousVersion
  have hVopen : IsOpen ((fun w ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) :=
    hU.preimage (by fun_prop)
  have hτ := measurable_continuousExitTime hVopen 0
  have haff : Measurable fun v : EuclideanSpace ℝ (Fin d) ↦ x + (Real.sqrt d)⁻¹ • v := by
    fun_prop
  have hG := (haff.comp (measurable_eval_random_time hτ)).comp (measurable_pathMap C hCm hC)
  refine hG.aemeasurable.congr ?_
  filter_upwards [ae_openExitTime_eq_continuousExitTime hd hC hCW, hCW] with ω h1 h2
  rw [h1]
  simp [h2, inv_smul_smul₀ hsd]

/-- The open annulus `{z | ε < ‖z - y‖ < R}` is open. -/
private lemma isOpen_setOf_annulus {E : Type*} [NormedAddCommGroup E] (y : E) (ε R : ℝ) :
    IsOpen {z : E | ε < ‖z - y‖ ∧ ‖z - y‖ < R} := by
  have hc : Continuous fun z : E ↦ ‖z - y‖ := (continuous_id.sub continuous_const).norm
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

/-- The closure of the open annulus lies in the closed annulus. -/
private lemma closure_setOf_annulus_subset {E : Type*} [NormedAddCommGroup E] (y : E)
    (ε R : ℝ) :
    closure {z : E | ε < ‖z - y‖ ∧ ‖z - y‖ < R} ⊆ {z | ε ≤ ‖z - y‖ ∧ ‖z - y‖ ≤ R} := by
  have hc : Continuous fun z : E ↦ ‖z - y‖ := (continuous_id.sub continuous_const).norm
  exact closure_minimal (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩)
    ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const))

/-- **Harmonic measure of the inner circle of an annulus.** For a Brownian motion on `ℝ²` started
at `x` and radii `0 < ε < ‖x - y‖ < R`, the probability that the exit position from the annulus
`{z | ε < ‖z - y‖ < R}` lies on the inner circle is `(log R - log ‖x - y‖) / (log R - log ε)`. -/
theorem IsBrownianSpace.measureReal_annulus_exit_inner {x y : EuclideanSpace ℝ (Fin 2)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)} (hB : IsBrownianSpace 2 x B P) {ε R : ℝ}
    (hε : 0 < ε) (hεx : ε < ‖x - y‖) (hxR : ‖x - y‖ < R) :
    P.real {ω | ‖B (openExitTime B {z | ε < ‖z - y‖ ∧ ‖z - y‖ < R} ω).toNNReal ω - y‖ ≤ ε} =
      (Real.log R - Real.log ‖x - y‖) / (Real.log R - Real.log ε) := by
  have := hB.isProbabilityMeasure
  set U : Set (EuclideanSpace ℝ (Fin 2)) := {z | ε < ‖z - y‖ ∧ ‖z - y‖ < R} with hUdef
  set F : Ω → EuclideanSpace ℝ (Fin 2) := fun ω ↦ B (openExitTime B U ω).toNNReal ω with hFdef
  have hU : IsOpen U := isOpen_setOf_annulus y ε R
  have hUb : Bornology.IsBounded U :=
    isBounded_ball.subset fun z hz ↦ by rw [mem_ball, dist_eq_norm]; exact hz.2
  have hxU : x ∈ U := ⟨hεx, hxR⟩
  have hεR : ε < R := hεx.trans hxR
  have hFm : AEMeasurable F P := hB.aemeasurable_openExitPosition (by norm_num) hU
  have hcirc : ∀ᵐ ω ∂P, ‖F ω - y‖ = ε ∨ ‖F ω - y‖ = R := by
    filter_upwards [hB.start, ae_openExitTime_ne_top (by norm_num) hB hUb, hB.cont]
      with ω hstart hfin hcont
    have hfr := openExitTime_mem_frontier hU hcont (by rw [hstart]; exact hxU) hfin
    rw [hU.frontier_eq] at hfr
    obtain ⟨h1, h2⟩ := closure_setOf_annulus_subset y ε R hfr.1
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact absurd ⟨h1, h2⟩ hfr.2
      · exact Or.inr h2
    · exact Or.inl h1.symm
  have hsub : closure U ⊆ {y}ᶜ := fun z hz hzy ↦ by
    have h := (closure_setOf_annulus_subset y ε R hz).1
    rw [mem_singleton_iff.1 hzy, sub_self, norm_zero] at h
    linarith
  have hh : HarmonicNearClosure (fun z ↦ Real.log ‖z - y‖) U :=
    harmonicNearClosure_iff.2 ((harmonicOnNhd_log_norm_sub y).mono hsub)
  have key := integral_openExit_harmonicNearClosure (by norm_num) hB hU hUb hh
  set S : Set (EuclideanSpace ℝ (Fin 2)) := {z | ‖z - y‖ ≤ ε} with hSdef
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hae : (fun ω ↦ Real.log ‖F ω - y‖) =ᵐ[P]
      fun ω ↦ Real.log R - (Real.log R - Real.log ε) * S.indicator 1 (F ω) := by
    filter_upwards [hcirc] with ω hω
    rcases hω with h | h
    · rw [indicator_of_mem (show F ω ∈ S from h.le), h]
      simp
    · have hnot : F ω ∉ S := fun hS' ↦ by
        have h' : ‖F ω - y‖ ≤ ε := hS'
        linarith
      rw [indicator_of_notMem hnot, h]
      simp
  have hind : ∫ ω, S.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ) (F ω) ∂P =
      P.real {ω | ‖F ω - y‖ ≤ ε} := by
    rw [← integral_map hFm (measurable_one.indicator hS).aestronglyMeasurable,
      integral_indicator_one hS]
    simp only [Measure.real, Measure.map_apply_of_aemeasurable hFm hS]
    rfl
  have hint : Integrable (fun ω ↦ S.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ) (F ω)) P :=
    (integrable_const (1 : ℝ)).mono'
      ((measurable_one.indicator hS).comp_aemeasurable hFm).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ (norm_indicator_le_norm_self _ _).trans (by simp))
  rw [integral_congr_ae hae, integral_sub (integrable_const _) (hint.const_mul _),
    integral_const, integral_const_mul, hind] at key
  simp only [probReal_univ, one_smul] at key
  have hc : 0 < Real.log R - Real.log ε := sub_pos.2 (Real.log_lt_log hε hεR)
  rw [eq_div_iff hc.ne']
  linear_combination -key

/-- **Points are polar for planar Brownian motion.** A Brownian motion on `ℝ²` started at `x`
almost surely never visits a point `y ≠ x`. -/
theorem IsBrownianSpace.ae_forall_ne {x y : EuclideanSpace ℝ (Fin 2)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)} (hB : IsBrownianSpace 2 x B P) (hxy : x ≠ y) :
    ∀ᵐ ω ∂P, ∀ t, B t ω ≠ y := by
  have := hB.isProbabilityMeasure
  have hρ : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  let ε : ℕ → ℝ := fun n ↦ ‖x - y‖ / ((n : ℝ) + 2)
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hεlt : ∀ n, ε n < ‖x - y‖ := fun n ↦
    div_lt_self hρ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  let A : ℕ → ℕ → Set Ω := fun R n ↦
    {ω | ‖B (openExitTime B {z | ε n < ‖z - y‖ ∧ ‖z - y‖ < (R : ℝ)} ω).toNNReal ω - y‖ ≤ ε n}
  have hnull : ∀ R : ℕ, ‖x - y‖ < R → P (⋂ n, A R n) = 0 := by
    intro R hR
    have hden : Tendsto (fun n : ℕ ↦ Real.log R - Real.log (ε n)) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 2)) atTop atTop :=
        Real.tendsto_log_atTop.comp
          (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      refine (tendsto_atTop_add_const_left _ (Real.log R - Real.log ‖x - y‖) h1).congr
        fun n ↦ ?_
      simp only [ε]
      rw [Real.log_div hρ.ne' (by positivity)]
      ring
    have hlim := (tendsto_const_nhds (x := Real.log R - Real.log ‖x - y‖)).div_atTop hden
    have hbound : ∀ n, P.real (⋂ n, A R n) ≤
        (Real.log R - Real.log ‖x - y‖) / (Real.log R - Real.log (ε n)) := fun n ↦
      (measureReal_mono (iInter_subset _ n)).trans_eq
        (hB.measureReal_annulus_exit_inner (hεpos n) (hεlt n) hR)
    have h0 : P.real (⋂ n, A R n) ≤ 0 := ge_of_tendsto' hlim hbound
    exact (measureReal_eq_zero_iff (measure_ne_top P _)).1 (le_antisymm h0 measureReal_nonneg)
  have hincl : ∀ᵐ ω ∂P, (∃ t, B t ω = y) → ∃ R : ℕ, ‖x - y‖ < R ∧ ∀ n, ω ∈ A R n := by
    filter_upwards [hB.cont] with ω hcont
    rintro ⟨t₀, ht₀⟩
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t₀)).exists_bound_of_continuousOn
      ((hcont.sub continuous_const).continuousOn)
    obtain ⟨R, hR⟩ := exists_nat_gt (max M ‖x - y‖)
    refine ⟨R, (le_max_right _ _).trans_lt hR, fun n ↦ ?_⟩
    set U : Set (EuclideanSpace ℝ (Fin 2)) := {z | ε n < ‖z - y‖ ∧ ‖z - y‖ < (R : ℝ)}
      with hUdef
    have hU : IsOpen U := isOpen_setOf_annulus y _ _
    have hle : openExitTime B U ω ≤ t₀ := openExitTime_le_of_not_mem fun h ↦ by
      have h' := h.1
      rw [ht₀, sub_self, norm_zero] at h'
      linarith [hεpos n]
    have hfin : openExitTime B U ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    have hτle : (openExitTime B U ω).toNNReal ≤ t₀ := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
      exact hle
    have hout := openExitTime_not_mem hU hcont hfin
    have hbd := hM _ ⟨bot_le, hτle⟩
    show ‖B (openExitTime B U ω).toNNReal ω - y‖ ≤ ε n
    by_contra hgt
    exact hout ⟨not_le.1 hgt, hbd.trans_lt ((le_max_left _ _).trans_lt hR)⟩
  have hN : ∀ᵐ ω ∂P, ∀ R : ℕ, ‖x - y‖ < R → ω ∉ ⋂ n, A R n := by
    rw [ae_all_iff]
    intro R
    by_cases hR : ‖x - y‖ < R
    · have h : ∀ᵐ ω ∂P, ω ∉ ⋂ n, A R n :=
        ae_iff.2 (measure_mono_null (fun ω hω ↦ not_not.1 hω) (hnull R hR))
      filter_upwards [h] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h ↦ absurd h hR
  filter_upwards [hincl, hN] with ω h1 h2 t ht
  obtain ⟨R, hR, hmem⟩ := h1 ⟨t, ht⟩
  exact h2 R hR (mem_iInter.2 hmem)

end LatticeProb
