/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.OccupationHit2 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: set_option autoImplicit true after the imports, the default of the source repository (this library disables it).
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.OccupationHit
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.GaussKernel

set_option autoImplicit true

/-!
Third part of node W3 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), towards the four remaining
statements `occ_shift_neg`, `occ_shift_pos`, `occDens_nonneg_const` and `prob_hit_neg`.

* `lt_of_never_hit_pos` / `lt_of_never_hit_neg`: a continuous path started at `0` that never hits
  the level `a` stays strictly below `a` (if `a > 0`) resp. strictly above `a` (if `a < 0`). Own
  elementary proofs (intermediate value theorem), the companion of `lt_hitLevel_of_pos` /
  `hitLevel_lt_of_neg` of `OccupationHit.lean`.
* `occ_eq_hit_mul`: **the measure identity of the strong Markov property at the first hitting time
  of `a`.** If the level `a` is never entered before `τ_a` (`hside`: `A` lies strictly on the far
  side of the starting point, and `hoff`: off the hitting event the path avoids `A`), then
  `occ σ μ A = P(τ_a < ∞) * occ σ μ (A - a)`. Proof: apply the strong Markov property
  (`strongMarkov_hit` with the constant past functional `1` and the functional
  `G_r(w) = 1_{A-a}(w r)`) at every fixed time `r`, integrate the resulting identity over
  `r ∈ (0, ∞)` by Tonelli (`measurable_uncurry_dpath_hitLevel`), and identify both sides with
  occupation integrals (`occ_eq_lintegral` on `A` and on `A - a`); the pointwise input is the
  deterministic identity `lintegral_Ioi_indicator_restart` of `OccupationHit.lean`.
* `occ_shift_neg`: for `y < 0` and `A ⊆ (-∞, y]` the occupation measure satisfies
  `occ σ μ A = P(τ_y < ∞) * occ σ μ (A - y)`.
* `occ_shift_pos`: for `x > 0`, `σ, μ > 0` and `B ⊆ (0, ∞)` the occupation measure is invariant
  under a shift to the right: `occ σ μ (B + x) = occ σ μ B`, the factor `P(τ_x < ∞)` being `1`
  by `ae_exists_eq_level`. **The hypotheses `0 < σ`, `0 < μ` are needed and are added to the
  handed-down statement, which is false without them** (see the docstring of `occ_shift_pos`).
* `occDens_nonneg`, `occ_Ioc_eq_ofReal_integral`: the occupation density of an interval, in a form
  usable together with `eqOn_Ioi_of_integral_Ioc_eq` / `eqOn_Iio_of_integral_Ioc_eq`.
* `prob_hit_neg`: for `σ, μ > 0` and `y < 0`, `P(τ_y < ∞) = occDens σ μ y / occDens σ μ 0` and
  `0 < occDens σ μ 0`; proof: `occ_shift_neg` on intervals `(a+y, c+y] ⊆ (-∞, y]`, the density
  form of `occ`, and the limit `w ↑ 0` with `continuous_occDens`.
* `occDens_nonneg_const`: for `σ, μ > 0` the occupation density is constant on `[0, ∞)`. This
statement has **no `GoodBM b P` argument**, so the blueprint's strong-Markov proof at `τ_x` is not
available for it: it is instead the classical Gaussian identity
`∫_0^∞ m^{-1/2} e^{-a/m-bm} dm = √(π/b)e^{-2√(ab)}`, proved in `GaussKernel.lean`
(`occDens_eq_inv_mu`: `occDens σ μ y = 1/μ` for `y > 0`, and `occDens_zero_eq_inv_mu` for `y = 0`
by continuity with `continuous_occDens`). Neither `prob_hit_neg` above nor `occDens_pos_zero`
(`OccupationHit.lean`) gives this constancy: the analytic input is needed.

Sources: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. VI §1 (local time,
occupation densities) and Ch. VII Prop 3.2, printed pp. 301–302 (hitting probabilities);
the deterministic facts are own elementary proofs (intermediate value theorem), the assembly is
own bookkeeping on top of the committed `strongMarkov_hit`.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}

/-! ## A path that never hits a level stays on one side of it -/

/-- A continuous path started at `0` that never hits a *negative* level `a` stays strictly above
`a`. Own elementary proof (intermediate value theorem). -/
theorem lt_of_never_hit_neg {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {a : ℝ}
    (ha : a < 0) (h : ¬ ∃ t : ℝ≥0, w t = a) : ∀ m : ℝ≥0, a < w m := by
  intro m
  by_contra hma
  push_neg at hma
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ m by simp) hw.continuousOn
    (show a ∈ Set.Icc (w m) (w 0) from ⟨hma, by rw [hw0]; exact ha.le⟩)
  exact h ⟨s, hs⟩

/-! ## The measure identity of the strong Markov property at a first hitting time -/

/-- **The strong Markov identity at the first hit of a level**, at the level of occupation
measures: if `A` is only occupied after the first hitting time `τ_a` of `a` (hypotheses `hside`
and `hoff`), then

`occ σ μ A = P(τ_a < ∞) * occ σ μ (A - a)`,  where `A - a = {z | z + a ∈ A}`.

The proof applies `strongMarkov_hit` with the constant past functional `1` and
`G_r(w) = 1_{A-a}(w r)` for each fixed `r`, integrates over `r ∈ (0, ∞)` and identifies the two
sides with `occ_eq_lintegral`. -/
theorem occ_eq_hit_mul (hb : GoodBM b P) (σ μ a : ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hside : ∀ (ω : Ω) (m : ℝ≥0), m < hitLevel (dpath σ μ b ω) a → dpath σ μ b ω m ∉ A)
    (hoff : ∀ (ω : Ω), (¬ ∃ t : ℝ≥0, dpath σ μ b ω t = a) → ∀ m : ℝ≥0, dpath σ μ b ω m ∉ A) :
    occ σ μ A = P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a} * occ σ μ ((fun z => z + a) ⁻¹' A) := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  set S : Set ℝ := (fun z => z + a) ⁻¹' A with hS
  have hSm : MeasurableSet S := hA.preimage (measurable_id.add_const a)
  set E : Set Ω := {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a} with hE
  have hEm : MeasurableSet E := measurableSet_exists_dpath_eq hb σ μ a
  have hPEne : P E ≠ ∞ := by
    have hle : P E ≤ P Set.univ := measure_mono (Set.subset_univ E)
    rw [measure_univ] at hle
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  -- the restarted integrand
  set G : Ω → ℝ≥0∞ := fun ω => ∫⁻ u in Set.Ioi (0 : ℝ),
    S.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + u.toNNReal) - a)
    with hG
  -- (0) the deterministic identity `lintegral_Ioi_indicator_restart`, for every `ω`
  have hdet (ω : Ω) : (∫⁻ m in Set.Ioi (0 : ℝ),
      A.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω m.toNNReal)) = G ω :=
    lintegral_Ioi_indicator_restart ((continuous_dpath hb σ μ ω).measurable) hA (hside ω)
  -- (1) off the hitting event the occupation of `A` vanishes
  have hoff0 (ω : Ω) (hω : ω ∉ E) : (∫⁻ m in Set.Ioi (0 : ℝ),
      A.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω m.toNNReal)) = 0 := by
    have hno : ¬ ∃ t : ℝ≥0, dpath σ μ b ω t = a := fun h => hω (by rw [hE]; exact h)
    refine le_antisymm ?_ bot_le
    refine (lintegral_mono fun m => ?_).trans_eq lintegral_zero
    rw [Set.indicator_of_notMem (hoff ω hno m.toNNReal)]
  -- (2) reduce the `ω`-integral to the hitting event
  have hstep1 : (∫⁻ ω, ∫⁻ m in Set.Ioi (0 : ℝ),
        A.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω m.toNNReal) ∂volume ∂P)
      = ∫⁻ ω in E, G ω ∂P := by
    have hcongr : (fun ω => ∫⁻ m in Set.Ioi (0 : ℝ),
          A.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω m.toNNReal))
        = fun ω => E.indicator G ω := by
      funext ω
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω]; exact hdet ω
      · rw [Set.indicator_of_notMem hω]; exact hoff0 ω hω
    rw [hcongr]
    exact lintegral_indicator hEm G
  -- (3) Tonelli: integrate the restarted integrand in the shift first
  have hgm : Measurable fun p : ℝ × Ω => S.indicator (1 : ℝ → ℝ≥0∞)
      (dpath σ μ b p.2 (hitLevel (dpath σ μ b p.2) a + p.1.toNNReal) - a) :=
    (measurable_const.indicator hSm).comp
      (((measurable_uncurry_dpath_hitLevel hb σ μ a).comp
        (measurable_snd.prodMk (measurable_fst.real_toNNReal))).sub measurable_const)
  have hswap : (∫⁻ ω in E, G ω ∂P) = ∫⁻ u in Set.Ioi (0 : ℝ),
      (∫⁻ ω in E, S.indicator (1 : ℝ → ℝ≥0∞)
        (dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + u.toNNReal) - a) ∂P) := by
    have h := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (ν := P.restrict E)
      (f := fun u (ω : Ω) => S.indicator (1 : ℝ → ℝ≥0∞)
        (dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + u.toNNReal) - a)) hgm.aemeasurable
    exact h.symm
  -- (4) strong Markov at each fixed shift
  have hsm (r : ℝ≥0) : (∫⁻ ω in E, S.indicator (1 : ℝ → ℝ≥0∞)
        (dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + r) - a) ∂P)
      = P E * ∫⁻ ω, S.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω r) ∂P := by
    have hGm : Measurable fun w' : ℝ≥0 → ℝ => S.indicator (1 : ℝ → ℝ≥0∞) (w' r) :=
      (measurable_const.indicator hSm).comp (measurable_pi_apply r)
    have h := strongMarkov_hit hb σ μ a
      (A := fun _ : ℝ≥0 → ℝ => (1 : ℝ≥0∞))
      (G := fun w' : ℝ≥0 → ℝ => S.indicator (1 : ℝ → ℝ≥0∞) (w' r)) measurable_const hGm
    have huniv : (∫⁻ _ : Ω in E, (1 : ℝ≥0∞) ∂P) = P E := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      simp
    rw [huniv] at h
    simpa using h
  -- (5) the occupation integral of `S = A - a`
  have hocc : (∫⁻ u in Set.Ioi (0 : ℝ),
      ∫⁻ ω, S.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω u.toNNReal) ∂P) = occ σ μ S := by
    rw [occ_eq_lintegral hb σ μ S hSm]
    refine lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := P)
      (f := fun u (ω : Ω) => S.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω u.toNNReal)) ?_
    exact ((measurable_const.indicator hSm).comp
      (measurable_uncurry_dpath_toNNReal hb σ μ)).aemeasurable
  calc occ σ μ A
      = (∫⁻ ω, ∫⁻ m in Set.Ioi (0 : ℝ),
          A.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω m.toNNReal) ∂volume ∂P) :=
        occ_eq_lintegral hb σ μ A hA
    _ = ∫⁻ ω in E, G ω ∂P := hstep1
    _ = ∫⁻ u in Set.Ioi (0 : ℝ), (∫⁻ ω in E, S.indicator (1 : ℝ → ℝ≥0∞)
          (dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + u.toNNReal) - a) ∂P) := hswap
    _ = ∫⁻ u in Set.Ioi (0 : ℝ),
          P E * ∫⁻ ω, S.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω u.toNNReal) ∂P := by
        refine lintegral_congr fun u => hsm u.toNNReal
    _ = P E * ∫⁻ u in Set.Ioi (0 : ℝ),
          ∫⁻ ω, S.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω u.toNNReal) ∂P :=
        lintegral_const_mul' (P E) _ hPEne
    _ = P E * occ σ μ ((fun z => z + a) ⁻¹' A) := by rw [hocc]

/-! ## The two shift identities of the occupation measure -/

/-- **W3, negative side.** For `y < 0` and `A ⊆ (-∞, y]`, the occupation measure of `A` is
`P(τ_y < ∞)` times the occupation measure of `A` shifted by `-y`. Indeed `A` is only occupied
after the first hit of `y` (`hitLevel_lt_of_neg`), and after `τ_y` the restarted path
`u ↦ Y_{τ_y+u} - y` is a fresh Brownian motion (`strongMarkov_hit`): this is `occ_eq_hit_mul`. -/
theorem occ_shift_neg (hb : GoodBM b P) (σ μ : ℝ) {y : ℝ} (hy : y < 0) {A : Set ℝ}
    (hA : MeasurableSet A) (hAy : A ⊆ Set.Iic y) :
    occ σ μ A = P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y} * occ σ μ ((fun z => z + y) ⁻¹' A) := by
  refine occ_eq_hit_mul hb σ μ y hA ?_ ?_
  · intro ω m hm
    exact fun hmem => absurd (hAy hmem) (not_le.mpr
      (hitLevel_lt_of_neg (continuous_dpath hb σ μ ω) (by simp [dpath, hb.zero ω]) hy hm))
  · intro ω hω m
    exact fun hmem => absurd (hAy hmem) (not_le.mpr
      (lt_of_never_hit_neg (continuous_dpath hb σ μ ω) (by simp [dpath, hb.zero ω]) hy hω m))

/-! ## The occupation measure of an interval, in terms of the density -/

/-- Nonnegativity of the occupation density (the integrand is a Gaussian density). Own elementary
proof. -/
theorem occDens_nonneg (σ μ : ℝ) (y : ℝ) : 0 ≤ occDens σ μ y :=
  integral_nonneg fun m => gaussianPDFReal_nonneg (μ * m) (occVar σ m) y

/-- The occupation measure of an interval is the integral of the occupation density over it
(`occ_eq`); both sides are written as `∫⁻` of `ENNReal.ofReal` of an honest real integral. -/
theorem occ_Ioc_eq_ofReal_integral (hσ : 0 < σ) (hμ : 0 < μ) {a b : ℝ} (hab : a ≤ b) :
    occ σ μ (Set.Ioc a b) = ENNReal.ofReal (∫ x in a..b, occDens σ μ x) := by
  have hInt : IntegrableOn (occDens σ μ) (Set.Ioc a b) :=
    ((continuous_occDens hσ hμ).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  rw [occ_eq hσ hμ, withDensity_apply _ measurableSet_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all _ fun x => occDens_nonneg σ μ x)]
  rw [← intervalIntegral.integral_of_le hab]

/-- **Extraction of a pointwise identity from interval integrals, negative half-line.** Mirror of
`eqOn_Ioi_of_integral_Ioc_eq` for `(-∞, 0)`, by reflection: if the integrals of `f` and `g` agree
on every interval `(a, b)` with `b ≤ 0`, then `f = g` on `(-∞, 0)`. Own elementary proof. -/
theorem eqOn_Iio_of_integral_Ioc_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a b : ℝ, a < b → b ≤ 0 → ∫ x in a..b, f x = ∫ x in a..b, g x) :
    Set.EqOn f g (Set.Iio 0) := by
  have h' : ∀ a b : ℝ, 0 < a → a < b →
      ∫ x in a..b, f (-x) = ∫ x in a..b, g (-x) := by
    intro a b ha hab
    rw [intervalIntegral.integral_comp_neg (f := f),
      intervalIntegral.integral_comp_neg (f := g)]
    exact h (-b) (-a) (by linarith) (by linarith)
  have h2 := eqOn_Ioi_of_integral_Ioc_eq (hf.comp continuous_neg) (hg.comp continuous_neg) h'
  intro t ht
  have ht' : t < 0 := ht
  have ht0 : (0 : ℝ) < -t := by linarith
  simpa using h2 ht0

/-! ## The probability of hitting a negative level -/

/-- **W3.** For `σ, μ > 0` and `y < 0`, the probability that the drift Brownian motion ever hits
the negative level `y` is `occDens σ μ y / occDens σ μ 0`, and the density at `0` is positive.
This is the blueprint's "negative side: for `A ⊆ (-∞,y]`, `ν(A) = P(τ_y<∞)·ν(A−y)`, and
evaluating at the point `y` gives the formula": here `occ_shift_neg` on intervals gives
`c(w+y) = P(τ_y<∞)·c(w)` for `w < 0`, and letting `w ↑ 0` with `continuous_occDens` gives
`c(y) = P(τ_y<∞)·c(0)`. -/
theorem prob_hit_neg (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {y : ℝ} (hy : y < 0) :
    0 < occDens σ μ 0 ∧ P.real {ω | ∃ t, dpath σ μ b ω t = y} = occDens σ μ y / occDens σ μ 0 := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  refine ⟨occDens_pos_zero hσ hμ, ?_⟩
  have hstep : ∀ a c : ℝ, a < c → c ≤ 0 →
      ∫ w in a..c, occDens σ μ (w + y)
        = ∫ w in a..c, (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal * occDens σ μ w := by
    intro a c hac hc0
    have hAy : Set.Ioc (a + y) (c + y) ⊆ Set.Iic y := fun z hz =>
      Set.mem_Iic.mpr (by linarith [hz.2, hc0])
    have hpre : (fun z => z + y) ⁻¹' (Set.Ioc (a + y) (c + y)) = Set.Ioc a c := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Ioc]
      constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
    have hmeasure := occ_shift_neg hb σ μ hy measurableSet_Ioc hAy
    rw [hpre] at hmeasure
    have h1 := occ_Ioc_eq_ofReal_integral hσ hμ (a := a + y) (b := c + y) (by linarith)
    have h2 := occ_Ioc_eq_ofReal_integral hσ hμ (a := a) (b := c) hac.le
    rw [h1, h2] at hmeasure
    have hPE : P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}
        = ENNReal.ofReal (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    rw [hPE, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hmeasure
    rw [← intervalIntegral.integral_comp_add_right (f := occDens σ μ) (d := y)] at hmeasure
    have hnn1 : 0 ≤ ∫ w in a..c, occDens σ μ (w + y) :=
      intervalIntegral.integral_nonneg_of_forall hac.le fun w => occDens_nonneg σ μ (w + y)
    have hnn2 : 0 ≤ (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal
        * ∫ w in a..c, occDens σ μ w :=
      mul_nonneg ENNReal.toReal_nonneg
        (intervalIntegral.integral_nonneg_of_forall hac.le fun w => occDens_nonneg σ μ w)
    have hreal : ∫ w in a..c, occDens σ μ (w + y)
        = (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal * ∫ w in a..c, occDens σ μ w :=
      (ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2).mp hmeasure
    rw [hreal, ← intervalIntegral.integral_const_mul (r :=
      (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal)]
  have hEqOn := eqOn_Iio_of_integral_Ioc_eq
    ((continuous_occDens hσ hμ).comp (continuous_id.add continuous_const))
    (continuous_const.mul (continuous_occDens hσ hμ)) hstep
  have hlim : occDens σ μ y
      = (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal * occDens σ μ 0 := by
    have hcont1 : Continuous fun w : ℝ => occDens σ μ (w + y) :=
      (continuous_occDens hσ hμ).comp (continuous_id.add continuous_const)
    have hcont2 : Continuous fun w : ℝ =>
        (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal * occDens σ μ w :=
      continuous_const.mul (continuous_occDens hσ hμ)
    have ht1 : Tendsto (fun w : ℝ => occDens σ μ (w + y)) (𝓝[<] (0 : ℝ)) (𝓝 (occDens σ μ y)) := by
      have h0 : (fun w : ℝ => occDens σ μ (w + y)) 0 = occDens σ μ y := by simp
      rw [← h0]
      exact hcont1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun w : ℝ =>
        (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal * occDens σ μ w)
        (𝓝[<] (0 : ℝ))
        (𝓝 ((P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal * occDens σ μ 0)) :=
      hcont2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (fun w : ℝ => occDens σ μ (w + y)) =ᶠ[𝓝[<] (0 : ℝ)]
        fun w => (P {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = y}).toReal * occDens σ μ w :=
      eventually_of_mem self_mem_nhdsWithin fun w hw => hEqOn hw
    exact tendsto_nhds_unique (ht1.congr' hev) ht2
  rw [Measure.real_def, hlim, mul_div_assoc,
    div_self (ne_of_gt (occDens_pos_zero hσ hμ)), mul_one]

/-! ## Constancy of the density on the positive half-line -/

/-- **W3.** For `σ, μ > 0` the occupation density is constant on `[0, ∞)`: the blueprint's
"for `x > 0` and `A ⊆ (0,∞)`, the strong Markov property at `τ_x` gives `ν(A+x) = ν(A)`, so the
densities agree, then everywhere by continuity". The strong-Markov route needs a `GoodBM b P`,
which this statement does not provide, so the constancy is obtained analytically in
`GaussKernel.lean` (`occDens_eq_inv_mu`, `occDens_zero_eq_inv_mu`: the density is `1/μ`). -/
theorem occDens_nonneg_const (hσ : 0 < σ) (hμ : 0 < μ) (y : ℝ) (hy : 0 ≤ y) :
    occDens σ μ y = occDens σ μ 0 := by
  rcases eq_or_lt_of_le hy with rfl | hypos
  · rfl
  · rw [occDens_eq_inv_mu hσ hμ hypos, occDens_zero_eq_inv_mu hσ hμ]

end QuantumZipper.Williams
