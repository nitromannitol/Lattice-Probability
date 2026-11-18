import LatticeProb.Prob.BrownianExitKelvin
import LatticeProb.Prob.BrownianExitPosition
import LatticeProb.Prob.BrownianOpenExitFinite
import LatticeProb.Prob.BrownianRestartCanonical

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
Letting instead `R → ∞` for fixed `ε`, the probability of leaving through the inner
circle tends to `1`, so `B` almost surely visits the closed disc of radius `ε` about `y`.

## Main results

* `LatticeProb.IsBrownianSpace.aemeasurable_openExitPosition`: the exit position of a Brownian
  motion from an open set is almost everywhere measurable.
* `LatticeProb.IsBrownianSpace.measureReal_annulus_exit_inner`: the harmonic measure of the inner
  circle of an annulus around `y`.
* `LatticeProb.IsBrownianSpace.ae_forall_ne`: a planar Brownian motion started at `x` almost surely
  never visits a point `y ≠ x` (points are polar).
* `LatticeProb.IsBrownianSpace.ae_exists_norm_sub_le`: a planar Brownian motion almost surely
  visits every closed disc of positive radius (neighbourhood recurrence).
* `LatticeProb.IsBrownianSpace.exists_continuous_modification`: a Brownian motion has an
  indistinguishable modification with continuous paths and measurable values, which is again a
  Brownian motion (`LatticeProb.IsBrownianSpace.congr_ae`).
* `LatticeProb.IsBrownianSpace.ae_exists_le_norm_sub_lt`: almost surely, a planar Brownian motion
  comes within any `ε > 0` of `y` after any time `T` (restart at `T` by the Markov property, then
  neighbourhood recurrence from the random position `B_T`).
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


/-- **Neighbourhood recurrence of planar Brownian motion.** A Brownian motion on `ℝ²` almost
surely visits the closed disc of radius `ε > 0` about any point `y`: the probability of leaving
the annulus `{ε < ‖z - y‖ < R}` through the outer circle is
`(log ‖x - y‖ - log ε) / (log R - log ε)`, which tends to `0` as `R → ∞`. -/
theorem IsBrownianSpace.ae_exists_norm_sub_le {x y : EuclideanSpace ℝ (Fin 2)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)} (hB : IsBrownianSpace 2 x B P) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∃ t, ‖B t ω - y‖ ≤ ε := by
  have := hB.isProbabilityMeasure
  rcases le_or_gt ‖x - y‖ ε with hxε | hxε
  · filter_upwards [hB.start] with ω h
    exact ⟨0, by rw [h]; exact hxε⟩
  let R : ℕ → ℝ := fun n ↦ ‖x - y‖ + n + 1
  have hR : ∀ n, ‖x - y‖ < R n := fun n ↦ by
    simp only [R]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  let E : ℕ → Set Ω := fun n ↦
    {ω | ‖B (openExitTime B {z | ε < ‖z - y‖ ∧ ‖z - y‖ < R n} ω).toNNReal ω - y‖ ≤ ε}
  have hsub : ∀ n, {ω | ¬ ∃ t, ‖B t ω - y‖ ≤ ε} ⊆ (E n)ᶜ := fun n _ hω hE ↦ hω ⟨_, hE⟩
  have hcompl : ∀ n, P.real (E n)ᶜ =
      (Real.log ‖x - y‖ - Real.log ε) / (Real.log (R n) - Real.log ε) := by
    intro n
    have hFm := hB.aemeasurable_openExitPosition (by norm_num) (isOpen_setOf_annulus y ε (R n))
    have hS : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | ‖z - y‖ ≤ ε} :=
      measurableSet_le (by fun_prop) measurable_const
    have hnm : NullMeasurableSet (E n) P := hFm.nullMeasurable hS
    have hadd : P.real (E n) + P.real (E n)ᶜ = 1 := by
      rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add (measure_ne_top _ _)
        (measure_ne_top _ _), measure_add_measure_compl₀ hnm, measure_univ, ENNReal.toReal_one]
    have hc : 0 < Real.log (R n) - Real.log ε :=
      sub_pos.2 (Real.log_lt_log hε (hxε.trans (hR n)))
    have hp' : P.real (E n) * (Real.log (R n) - Real.log ε) =
        Real.log (R n) - Real.log ‖x - y‖ :=
      (eq_div_iff hc.ne').1 (hB.measureReal_annulus_exit_inner hε hxε (hR n))
    rw [eq_div_iff hc.ne']
    linear_combination (Real.log (R n) - Real.log ε) * hadd - hp'
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (R n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_left _ ‖x - y‖ tendsto_natCast_atTop_atTop))
  have hden : Tendsto (fun n : ℕ ↦ Real.log (R n) - Real.log ε) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-Real.log ε) hlog).congr fun n ↦ (sub_eq_add_neg _ _).symm
  have hlim := (tendsto_const_nhds (x := Real.log ‖x - y‖ - Real.log ε)).div_atTop hden
  have hbound : ∀ n, P.real {ω | ¬ ∃ t, ‖B t ω - y‖ ≤ ε} ≤
      (Real.log ‖x - y‖ - Real.log ε) / (Real.log (R n) - Real.log ε) := fun n ↦
    (measureReal_mono (hsub n)).trans_eq (hcompl n)
  have h0 := ge_of_tendsto' hlim hbound
  exact ae_iff.2 ((measureReal_eq_zero_iff (measure_ne_top P _)).1
    (le_antisymm h0 measureReal_nonneg))

/-- **Indistinguishable modifications.** A process whose paths almost surely agree with those of
a Brownian motion on `ℝ ^ d` is a Brownian motion on `ℝ ^ d`. -/
theorem IsBrownianSpace.congr_ae {d : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    {B B' : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (h : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) : IsBrownianSpace d x B' P where
  start := by
    filter_upwards [hB.start, h] with ω h0 hω
    rw [hω, h0]
  coord i :=
    { toIsPreBrownianReal := (hB.coord i).toIsPreBrownianReal.congr fun t => by
        filter_upwards [h] with ω hω
        rw [hω]
      cont := by
        filter_upwards [(hB.coord i).cont, h] with ω hc hω
        simpa only [hω] using hc }
  indep := (ProbabilityTheory.iIndepFun_congr fun i => by
    filter_upwards [h] with ω hω
    funext t
    rw [hω]).1 hB.indep

/-- **A continuous modification.** A Brownian motion on `ℝ ^ d`, `d ≥ 1`, has an
indistinguishable modification whose paths are all continuous and whose values are measurable. -/
theorem IsBrownianSpace.exists_continuous_modification {d : ℕ} (hd : 1 ≤ d)
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) :
    ∃ B' : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d), (∀ t, Measurable (B' t)) ∧
      (∀ ω, Continuous fun t => B' t ω) ∧ ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω := by
  obtain ⟨C, hCm, hC, -, hCW, -⟩ := hB.exists_continuousVersion
  have hs : Real.sqrt d ≠ 0 :=
    Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (Nat.lt_of_lt_of_le Nat.zero_lt_one hd))
  refine ⟨fun t ω => x + (Real.sqrt d)⁻¹ • C t ω, fun t => by have := hCm t; fun_prop, fun ω => by have := hC ω; fun_prop, ?_⟩
  filter_upwards [hCW] with ω hω t
  rw [hω t, smul_smul, inv_mul_cancel₀ hs, one_smul]
  abel

/-- **Recurrence after a fixed time, for a continuous measurable version.** -/
theorem IsBrownianSpace.ae_exists_le_norm_sub_lt_of_continuous {x y : EuclideanSpace ℝ (Fin 2)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)} (hB : IsBrownianSpace 2 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ t, T ≤ t ∧ ‖B t ω - y‖ < ε := by
  have := hB.isProbabilityMeasure
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let S : Set (EuclideanSpace ℝ (Fin 2) × BrownianPath 2) :=
    ⋃ q ∈ D, {p | ‖p.1 + p.2 q - y‖ < ε}
  have hevm : ∀ q : ℝ≥0, Measurable fun w : BrownianPath 2 => w q := fun q =>
    ContinuousMapBorel.ContinuousMap.measurable_iff_eval.1 measurable_id q
  have hSm : MeasurableSet S := by
    refine MeasurableSet.biUnion hDc fun q _ => ?_
    exact measurableSet_lt
      ((measurable_fst.add ((hevm q).comp measurable_snd)).sub_const y).norm measurable_const
  have hdense : ∀ (v : EuclideanSpace ℝ (Fin 2)) (w : BrownianPath 2) (t : ℝ≥0),
      ‖v + w t - y‖ < ε → (v, w) ∈ S := by
    intro v w t ht
    have hU : IsOpen {s : ℝ≥0 | ‖v + w s - y‖ < ε} :=
      isOpen_lt ((continuous_const.add w.continuous).sub continuous_const).norm continuous_const
    obtain ⟨q, hqD, hqU⟩ := hDd.exists_mem_open hU ⟨t, ht⟩
    exact mem_iUnion₂.2 ⟨q, hqD, hqU⟩
  have hR0 := measurable_restartPath hm hcont (measurable_const (a := (0 : ℝ≥0)))
  have hinner : ∀ v : EuclideanSpace ℝ (Fin 2),
      ∀ᵐ w ∂(P.map (restartPath B hcont fun _ => 0)), (v, w) ∈ S := by
    intro v
    rw [ae_map_iff hR0.aemeasurable (measurable_prodMk_left hSm)]
    filter_upwards [hB.ae_exists_norm_sub_le (y := y - v + x) (half_pos hε), hB.start]
      with ω ⟨t, ht⟩ h0
    refine hdense v _ t ?_
    have heq : v + (restartPath B hcont (fun _ => 0) ω) t - y = B t ω - (y - v + x) := by
      change v + (B (0 + t) ω - B 0 ω) - y = _
      rw [zero_add, h0]
      abel
    rw [heq]
    exact lt_of_le_of_lt ht (half_lt_self hε)
  have hτ := isStoppingTime_const (natFiltration B hm) T
  have hY : Measurable[hτ.measurableSpace] (B T) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact (Filtration.stronglyAdapted_natural hm T).measurable
  have hlaw := hB.map_prod_restartPath hm hcont (τ := fun _ => T) hτ hY MeasurableSet.univ
  rw [Measure.restrict_univ] at hlaw
  have hprod : ∀ᵐ p ∂((P.map (B T)).prod (P.map (restartPath B hcont fun _ => 0))), p ∈ S :=
    (Measure.ae_prod_iff_ae_ae hSm).2 (Eventually.of_forall hinner)
  rw [← hlaw] at hprod
  have hpair := (ae_map_iff (p := fun p => p ∈ S) ((hm T).measurable.prodMk
    (measurable_restartPath hm hcont (measurable_const (a := T)))).aemeasurable hSm).1 hprod
  filter_upwards [hpair] with ω hω
  obtain ⟨q, -, hq⟩ := mem_iUnion₂.1 hω
  refine ⟨T + q, le_self_add, ?_⟩
  have heq : B T ω + (restartPath B hcont (fun _ => T) ω) q - y = B (T + q) ω - y := by
    change B T ω + (B (T + q) ω - B T ω) - y = _
    abel
  rw [← heq]
  exact hq

/-- **Neighbourhood recurrence after any time.** A planar Brownian motion almost surely comes
within distance `ε > 0` of any point `y` after any time `T`: restart at the deterministic time `T`
(the restarted path is a Brownian motion independent of `B_T`) and apply neighbourhood recurrence
from the position `B_T`. -/
theorem IsBrownianSpace.ae_exists_le_norm_sub_lt {x y : EuclideanSpace ℝ (Fin 2)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)} (hB : IsBrownianSpace 2 x B P)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ t, T ≤ t ∧ ‖B t ω - y‖ < ε := by
  obtain ⟨B', hm, hc, hBB'⟩ := hB.exists_continuous_modification (by norm_num)
  filter_upwards [(hB.congr_ae hBB').ae_exists_le_norm_sub_lt_of_continuous
    (fun t => (hm t).stronglyMeasurable) hc (y := y) hε T, hBB'] with ω ⟨t, hTt, ht⟩ hω
  exact ⟨t, hTt, by rwa [hω t] at ht⟩

/-- **Planar Brownian motion is neighbourhood recurrent.** Almost surely, for every point `y`,
every `ε > 0` and every time `T`, the path comes within distance `ε` of `y` after time `T`. -/
theorem IsBrownianSpace.ae_forall_exists_le_norm_sub_lt {x : EuclideanSpace ℝ (Fin 2)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)} (hB : IsBrownianSpace 2 x B P) :
    ∀ᵐ ω ∂P, ∀ (y : EuclideanSpace ℝ (Fin 2)) (ε : ℝ), 0 < ε → ∀ T : ℝ≥0,
      ∃ t, T ≤ t ∧ ‖B t ω - y‖ < ε := by
  obtain ⟨Y, hYc, hYd⟩ := TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ (Fin 2))
  have hall : ∀ᵐ ω ∂P, ∀ y ∈ Y, ∀ n m : ℕ,
      ∃ t, (n : ℝ≥0) ≤ t ∧ ‖B t ω - y‖ < 1 / ((m : ℝ) + 1) := by
    rw [ae_ball_iff hYc]
    intro y _
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    exact hB.ae_exists_le_norm_sub_lt (y := y) Nat.one_div_pos_of_nat (n : ℝ≥0)
  filter_upwards [hall] with ω hω y ε hε T
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨y', hy'Y, hy'⟩ := hYd.exists_dist_lt y (half_pos hε)
  obtain ⟨n, hn⟩ := exists_nat_ge (T : ℝ)
  obtain ⟨t, hnt, ht⟩ := hω y' hy'Y n m
  refine ⟨t, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast hn) hnt
  · calc ‖B t ω - y‖ ≤ ‖B t ω - y'‖ + ‖y' - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := by
          gcongr
          · exact ht.trans hm
          · rw [← dist_eq_norm, dist_comm]; exact hy'
      _ = ε := add_halves ε

end LatticeProb
