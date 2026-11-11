import LatticeProb.LQG.LocalMeasureKernel2

/-!
# Local decoder: approximants and kernel

The generic countable determination on a locally compact metric space, the dyadic approximants `approxX`, the discrete
decoder `discDecoder` and the kernel `kernelMeas`. Statements and proofs are those of the preceding layer, with `ℂ`
replaced by a locally compact metric space.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG

universe u

namespace LatticeProb.LocalMeasureKernel

namespace LocalDecoderCommon

/-! ### Generic countable determination on a locally compact metric space

The countable test family (`TestFamily`, `exists_testFamily`) with `ℂ` replaced by a locally compact metric space `X`
and the balls `closedBall 0 n` replaced by a compact exhaustion `K`. Applied to `X = ↥(ball c R)`. -/

section Approximants

open scoped CompactlySupported

/-- The disc `ball c R` is locally compact (an open subset of `ℂ`). -/
instance locallyCompactSpace_ball (c : ℂ) (R : ℝ) : LocallyCompactSpace (ball c R) :=
  isOpen_ball.locallyCompactSpace

/-- The Lebesgue measure of the disc `ball c R` (the pullback of `volume` under the inclusion; `Subtype.measureSpace`
is not a global instance). -/
noncomputable def ballVol (c : ℂ) (R : ℝ) : Measure (ball c R) :=
  Measure.comap (Subtype.val : ball c R → ℂ) (volume : Measure ℂ)

theorem isLocallyFiniteMeasure_ballVol (c : ℂ) (R : ℝ) : IsLocallyFiniteMeasure (ballVol c R) := by
  refine ⟨fun x => ?_⟩
  have hx : dist (x : ℂ) c < R := mem_ball.1 x.2
  have hρ : 0 < (R - dist (x : ℂ) c) / 2 := by linarith
  refine ⟨Subtype.val ⁻¹' ball (x : ℂ) ((R - dist (x : ℂ) c) / 2), ?_, ?_⟩
  · exact (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hρ)
  · unfold ballVol
    rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt measure_ball_lt_top

/-- The radial retraction of `ℂ` onto the closed disc `closedBall c s` (the identity on that disc). -/
noncomputable def projBall (c : ℂ) (s : ℝ) (z : ℂ) : ℂ :=
  c + (s / max (dist z c) s) • (z - c)

theorem continuous_projBall {c : ℂ} {s : ℝ} (hs : 0 < s) : Continuous (projBall c s) := by
  have h1 : Continuous fun z : ℂ => s / max (dist z c) s :=
    continuous_const.div ((continuous_id.dist continuous_const).max continuous_const)
      fun z => (lt_max_of_lt_right hs).ne'
  have h2 : Continuous fun z : ℂ => z - c := continuous_id.sub continuous_const
  unfold projBall
  exact continuous_const.add (h1.smul h2)

theorem dist_projBall_le {c : ℂ} {s : ℝ} (hs : 0 < s) (z : ℂ) : dist (projBall c s z) c ≤ s := by
  unfold projBall
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg hs.le (le_max_of_le_right hs.le)), ← dist_eq_norm]
  rw [div_mul_eq_mul_div, div_le_iff₀ (lt_max_of_lt_right hs)]
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) hs.le

theorem projBall_of_dist_le {c : ℂ} {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : dist z c ≤ s) :
    projBall c s z = z := by
  unfold projBall
  rw [max_eq_right hz, div_self hs.ne', one_smul, add_sub_cancel]

/-- The point `(2^{-k}, projBall z)` of `LocalParam c R`, for `2ε < R`. -/
noncomputable def localPoint (c : ℂ) {R ε : ℝ} (hε : 0 < ε) (h2 : 2 * ε < R) (z : ℂ) : LocalParam c R :=
  ⟨(ε, projBall c (R - 2 * ε) z), ⟨hε, by
    show dist (projBall c (R - 2 * ε) z) c + ε < R
    linarith [dist_projBall_le (c := c) (sub_pos.2 h2) z]⟩⟩

theorem continuous_localPoint (c : ℂ) {R ε : ℝ} (hε : 0 < ε) (h2 : 2 * ε < R) :
    Continuous (localPoint c hε h2) :=
  Continuous.subtype_mk (continuous_const.prodMk ((continuous_projBall (sub_pos.2 h2)).comp continuous_id)) _

/-- The real density `ε^{γ²/2} e^{γ F(ε,z)}` of the dyadic approximant at scale `ε = 2^{-k}` read at
the projected point; `0` when `2ε ≥ R` (then no test function of a disc is seen). -/
noncomputable def approxDens (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) (z : ℂ) : ℝ :=
  if h : 2 * dyadicScale k < R then
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * F (localPoint c (ProfileDerived.dyadicScale_pos k) h z))
  else 0

theorem continuous_approxDens_prod (γ : ℝ) (c : ℂ) (R : ℝ) (k : ℕ) :
    Continuous fun q : C(LocalParam c R, ℝ) × ℂ => approxDens γ c R q.1 k q.2 := by
  by_cases h : 2 * dyadicScale k < R
  · have hE : Continuous fun q : C(LocalParam c R, ℝ) × ℂ =>
        q.1 (localPoint c (ProfileDerived.dyadicScale_pos k) h q.2) :=
      continuous_eval.comp
        (continuous_fst.prodMk ((continuous_localPoint c (ProfileDerived.dyadicScale_pos k) h).comp continuous_snd))
    have hEq : (fun q : C(LocalParam c R, ℝ) × ℂ => approxDens γ c R q.1 k q.2) = fun q =>
        dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * q.1 (localPoint c (ProfileDerived.dyadicScale_pos k) h q.2)) := by
      funext q
      simp only [approxDens, h, ↓reduceDIte]
    rw [hEq]
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hE))
  · have hEq : (fun q : C(LocalParam c R, ℝ) × ℂ => approxDens γ c R q.1 k q.2) = fun _ => 0 := by
      funext q
      simp only [approxDens, h, ↓reduceDIte]
    rw [hEq]
    exact continuous_const

theorem approxDens_nonneg (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) (z : ℂ) :
    0 ≤ approxDens γ c R F k z := by
  by_cases h : 2 * dyadicScale k < R
  · simp only [approxDens, h, ↓reduceDIte]
    exact mul_nonneg (Real.rpow_nonneg (ProfileDerived.dyadicScale_pos k).le _) (Real.exp_pos _).le
  · simp only [approxDens, h, ↓reduceDIte]
    exact le_refl 0

instance sFinite_ballVol (c : ℂ) (R : ℝ) : SFinite (ballVol c R) := by
  have := isLocallyFiniteMeasure_ballVol c R
  have : LocallyCompactSpace (ball c R) := isOpen_ball.locallyCompactSpace
  infer_instance

/-- The dyadic approximant `ε^{γ²/2} e^{γ F(ε,z)} dz` on the disc `X = ball c R` (the Lebesgue measure of `X`
weighted by `approxDens`). -/
noncomputable def approxX (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) : Measure (ball c R) :=
  (ballVol c R).withDensity fun x => ENNReal.ofReal (approxDens γ c R F k x.1)

theorem continuous_approxDens_X (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) :
    Continuous fun x : ball c R => approxDens γ c R F k x.1 :=
  (continuous_approxDens_prod γ c R k).comp (continuous_const.prodMk (continuous_subtype_val))

theorem integral_approxX (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ)
    (g : ball c R → ℝ) :
    ∫ x, g x ∂(approxX γ c R F k) = ∫ x, g x * approxDens γ c R F k x.1 ∂(ballVol c R) := by
  unfold approxX
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun x : ball c R => ENNReal.ofReal (approxDens γ c R F k x.1))
    (continuous_approxDens_X γ c R F k).measurable.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [smul_eq_mul, ENNReal.toReal_ofReal (approxDens_nonneg γ c R F k x.1), mul_comm]

theorem isLocallyFiniteMeasure_approxX (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) :
    IsLocallyFiniteMeasure (approxX γ c R F k) := by
  have := isLocallyFiniteMeasure_ballVol c R
  unfold approxX
  exact IsLocallyFiniteMeasure.withDensity_ofReal (continuous_approxDens_X γ c R F k)

theorem measurable_integral_approxX (γ : ℝ) (c : ℂ) (R : ℝ) (k : ℕ) (g : C_c(ball c R, ℝ)) :
    Measurable fun F : C(LocalParam c R, ℝ) =>
      ∫ x, g x * approxDens γ c R F k x.1 ∂(ballVol c R) := by
  have hcont : Continuous fun q : C(LocalParam c R, ℝ) × ball c R =>
      g q.2 * approxDens γ c R q.1 k q.2.1 :=
    (g.continuous.comp continuous_snd).mul
      ((continuous_approxDens_prod γ c R k).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hSM : StronglyMeasurable (Function.uncurry fun (F : C(LocalParam c R, ℝ)) (x : ball c R) =>
      g x * approxDens γ c R F k x.1) := hcont.stronglyMeasurable
  exact (hSM.integral_prod_right (ν := ballVol c R)).measurable

/-- Extension by zero of a compactly supported continuous function on the disc `ball c R` to `ℂ`. -/
theorem exists_extend_zero_ball {c : ℂ} {R : ℝ} (g : C_c(ball c R, ℝ)) :
    ∃ f : C_c(ℂ, ℝ), (∀ x : ball c R, f x.1 = g x) ∧ ∀ z, z ∉ Subtype.val '' tsupport g → f z = 0 := by
  classical
  let K : Set ℂ := Subtype.val '' tsupport g
  have hK : IsCompact K := (g.hasCompactSupport.isCompact).image continuous_subtype_val
  have hKball : K ⊆ ball c R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let f : ℂ → ℝ := fun z => if h : z ∈ ball c R then g ⟨z, h⟩ else 0
  have hfx : ∀ x : ball c R, f x.1 = g x := by
    intro x
    simp only [f, x.2, ↓reduceDIte, Subtype.coe_eta]
  have hzero : ∀ z, z ∉ K → f z = 0 := by
    intro z hz
    by_cases hzb : z ∈ ball c R
    · have hnot : (⟨z, hzb⟩ : ball c R) ∉ tsupport g := fun h => hz ⟨_, h, rfl⟩
      simp only [f, hzb, ↓reduceDIte]
      exact image_eq_zero_of_notMem_tsupport hnot
    · simp only [f, hzb, ↓reduceDIte]
  have hcontOn : ContinuousOn f (ball c R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : (ball c R).domRestrict f = ⇑g := funext fun x => hfx x
    rw [hres]
    exact g.continuous
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 fun z0 => ?_
    by_cases hz0 : z0 ∈ ball c R
    · exact hcontOn.continuousAt (isOpen_ball.mem_nhds hz0)
    · have hz0K : z0 ∉ K := fun h => hz0 (hKball h)
      refine (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) z0).congr ?_
      exact Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hz0K)
        fun z hz => (hzero z hz).symm
  exact ⟨⟨⟨f, hcont⟩, HasCompactSupport.intro hK fun z hz => hzero z hz⟩, hfx, hzero⟩

/-- On the closed disc: where `F` is the centred circle profile `fieldCircleAverage - P`, the
approximant density is `e^{γP}` times the Lebesgue density of `lqgApprox` at scale `2^{-k}`. -/
theorem approxDens_mul_exp (γ α P : ℝ) {c : ℂ} {R : ℝ} (hc : ℝ → ℂ → ℝ) (F : C(LocalParam c R, ℝ))
    (hF : ∀ p : LocalParam c R, F p = fieldCircleAverage α hc p.1.1 p.1.2 - P) (k : ℕ)
    (h2 : 2 * dyadicScale k < R) {z : ℂ} (hz : dist z c ≤ R - 2 * dyadicScale k) :
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z) =
      Real.exp (γ * P) * approxDens γ c R F k z := by
  have hε : 0 < dyadicScale k := ProfileDerived.dyadicScale_pos k
  have hp : projBall c (R - 2 * dyadicScale k) z = z := projBall_of_dist_le (sub_pos.2 h2) hz
  have hFz : F (localPoint c hε h2 z) = fieldCircleAverage α hc (dyadicScale k) z - P := by
    rw [hF]
    show fieldCircleAverage α hc (dyadicScale k) (projBall c (R - 2 * dyadicScale k) z) - P = _
    rw [hp]
  simp only [approxDens, h2, ↓reduceDIte]
  rw [hFz]
  have hexp : Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z) =
      Real.exp (γ * P) * Real.exp (γ * (fieldCircleAverage α hc (dyadicScale k) z - P)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Locally finite pull-back of a locally finite measure to the disc (general version of
`isLocallyFiniteMeasure_ballVol`). -/
theorem isLocallyFiniteMeasure_comap_ball (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (c : ℂ) (R : ℝ) :
    IsLocallyFiniteMeasure (Measure.comap (Subtype.val : ball c R → ℂ) μ) := by
  refine ⟨fun x => ?_⟩
  have hx : dist (x : ℂ) c < R := mem_ball.1 x.2
  have hρ : 0 < (R - dist (x : ℂ) c) / 2 := by linarith
  refine ⟨Subtype.val ⁻¹' ball (x : ℂ) ((R - dist (x : ℂ) c) / 2), ?_, ?_⟩
  · exact (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hρ)
  · rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt measure_ball_lt_top

/-- Identity with `lqgApprox`: for `f` continuous and supported in the disc, `∫ f d(lqgApprox)` is
`e^{γP}` times `∫ f · approxDens`, where `F` is the centred circle profile (`hF`). -/
theorem integral_lqgApprox_eq_approx (γ α P : ℝ) {c : ℂ} {R : ℝ} (hc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hc ε)) (F : C(LocalParam c R, ℝ))
    (hF : ∀ p : LocalParam c R, F p = fieldCircleAverage α hc p.1.1 p.1.2 - P) (k : ℕ)
    (h2 : 2 * dyadicScale k < R) {f : ℂ → ℝ} (hsupp : ∀ z, f z ≠ 0 → dist z c ≤ R - 2 * dyadicScale k) :
    ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α hc) (dyadicScale k)) =
      Real.exp (γ * P) * ∫ z, f z * approxDens γ c R F k z := by
  have hε : 0 < dyadicScale k := ProfileDerived.dyadicScale_pos k
  have hfca : Continuous fun z => fieldCircleAverage α hc (dyadicScale k) z := by
    have h1 : Continuous fun z => hc (dyadicScale k) z := hcont _ hε
    have h3 : Continuous fun z : ℂ => Real.log (max (dyadicScale k) ‖z‖) :=
      (continuous_const.max continuous_norm).log fun z => (lt_max_of_lt_left hε).ne'
    have hEq : (fun z => fieldCircleAverage α hc (dyadicScale k) z) =
        fun z => hc (dyadicScale k) z - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      unfold fieldCircleAverage
      rw [circleAverage_log_norm_eq_max hε z]
    rw [hEq]
    exact h1.sub (continuous_const.mul h3)
  have hD : Continuous fun z => dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hfca))
  unfold lqgApprox
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z)))
    hD.measurable.ennreal_ofReal (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul]
  congr 1
  funext z
  by_cases hfz : f z = 0
  · simp [hfz]
  · have hz := hsupp z hfz
    have hnn : 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z) :=
      mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
    rw [smul_eq_mul, ENNReal.toReal_ofReal hnn, approxDens_mul_exp γ α P hc F hF k h2 hz]
    ring

/-- The integral over the disc of the approximant density reduces to the integral over `ℂ` (the support of `f`
lies in the disc). -/
theorem integral_approxX_eq_ball (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) {f : ℂ → ℝ}
    (hsupp : ∀ z, f z ≠ 0 → dist z c < R) :
    ∫ x : ball c R, f x.1 * approxDens γ c R F k x.1 ∂(ballVol c R) =
      ∫ z, f z * approxDens γ c R F k z := by
  unfold ballVol
  refine (integral_subtype_comap measurableSet_ball (fun z => f z * approxDens γ c R F k z)).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_)
  by_cases hfz : f z = 0
  · simp [hfz]
  · exact absurd (mem_ball.2 (hsupp z hfz)) hz

/-- A compact subset of the disc lies in a closed disc of radius `s < R`. -/
theorem exists_radius_of_compact {c : ℂ} {R : ℝ} (hR : 0 < R) {K : Set ℂ} (hK : IsCompact K)
    (hKb : K ⊆ ball c R) : ∃ s : ℝ, 0 ≤ s ∧ s < R ∧ ∀ z ∈ K, dist z c ≤ s := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨R / 2, by linarith, by linarith, fun z hz => by simp [hE] at hz⟩
  · obtain ⟨z0, hz0, hmax⟩ := hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
    exact ⟨dist z0 c, dist_nonneg, mem_ball.1 (hKb hz0), fun z hz => isMaxOn_iff.1 hmax z hz⟩

/-- The dyadic scales eventually satisfy `2 · 2^{-k} < t`. -/
theorem eventually_two_dyadicScale_lt {t : ℝ} (ht : 0 < t) :
    ∀ᶠ k : ℕ in atTop, 2 * dyadicScale k < t := by
  have h : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : Tendsto (fun k : ℕ => 2 * dyadicScale k) atTop (𝓝 0) := by
    simpa using h.const_mul 2
  exact h2.eventually (gt_mem_nhds ht)

/-- Riesz limit on the disc: if the centred profile `F` is `fieldCircleAverage - P` and `μ` is the
γ-LQG measure of `hc` (`IsLQGLimit`), the approximants integrate every `g ∈ C_c(ball c R)` to
`∫ g d(comap val (e^{-γP} • μ))`. -/
theorem tendsto_approxX_integral (γ α P : ℝ) {c : ℂ} {R : ℝ} (hR : 0 < R) (hc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hc ε)) (μ : Measure ℂ)
    (hμ : IsLQGLimit γ (fieldCircleAverage α hc) μ)
    (F : C(LocalParam c R, ℝ))
    (hF : ∀ p : LocalParam c R, F p = fieldCircleAverage α hc p.1.1 p.1.2 - P)
    (g : C_c(ball c R, ℝ)) :
    Tendsto (fun k => ∫ x, g x ∂(approxX γ c R F k)) atTop
      (𝓝 (∫ x, g x ∂(Measure.comap (Subtype.val : ball c R → ℂ)
        (ENNReal.ofReal (Real.exp (-(γ * P))) • μ)))) := by
  obtain ⟨fc, hfg, hfz⟩ := exists_extend_zero_ball g
  have hcompact : IsCompact (Subtype.val '' tsupport g) :=
    (g.hasCompactSupport.isCompact).image continuous_subtype_val
  have hKb : Subtype.val '' tsupport g ⊆ ball c R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨s, hs0, hsR, hsK⟩ := exists_radius_of_compact hR hcompact hKb
  have hfsupp : ∀ z, fc z ≠ 0 → dist z c ≤ s := fun z hz =>
    hsK z (by
      by_contra hK
      exact hz (hfz z hK))
  have hev : ∀ᶠ k : ℕ in atTop, 2 * dyadicScale k < R - s :=
    eventually_two_dyadicScale_lt (by linarith)
  have hgf : ∀ x : ball c R, g x = fc x.1 := fun x => (hfg x).symm
  have hL : ∫ x, g x ∂(Measure.comap (Subtype.val : ball c R → ℂ)
      (ENNReal.ofReal (Real.exp (-(γ * P))) • μ)) = Real.exp (-(γ * P)) * ∫ z, fc z ∂μ := by
    simp only [hgf]
    rw [integral_subtype_comap measurableSet_ball (fun z => fc z)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      by_contra hne
      exact hz (mem_ball.2 (lt_of_le_of_lt (hfsupp z hne) hsR)))]
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hexp : Real.exp (-(γ * P)) * Real.exp (γ * P) = 1 := by
    rw [← Real.exp_add]
    simp
  have heq : (fun k => ∫ x, g x ∂(approxX γ c R F k)) =ᶠ[atTop] fun k =>
      Real.exp (-(γ * P)) * ∫ z, fc z ∂(lqgApprox γ (fieldCircleAverage α hc) (dyadicScale k)) := by
    filter_upwards [hev] with k hk
    have hk2 : 2 * dyadicScale k < R := by linarith
    have hsupp1 : ∀ z, fc z ≠ 0 → dist z c ≤ R - 2 * dyadicScale k := fun z hz => by
      linarith [hfsupp z hz]
    have hsupp2 : ∀ z, fc z ≠ 0 → dist z c < R := fun z hz => by
      linarith [hfsupp z hz]
    rw [integral_lqgApprox_eq_approx γ α P hc hcont F hF k hk2 hsupp1, ← mul_assoc, hexp, one_mul]
    rw [integral_approxX γ c R F k (fun x => g x)]
    have hcongr : (fun x : ball c R => g x * approxDens γ c R F k x.1) =
        fun x : ball c R => fc x.1 * approxDens γ c R F k x.1 := by
      funext x
      rw [hgf x]
    rw [hcongr, integral_approxX_eq_ball γ c R F k hsupp2]
  have hT := (hμ.tendsto_integral (⇑fc) fc.continuous fc.hasCompactSupport).const_mul (Real.exp (-(γ * P)))
  rw [hL]
  exact Tendsto.congr' heq.symm hT

/-- Locally finite scalar multiples of a locally finite measure (`ENNReal.ofReal r • μ`). -/
instance isLocallyFiniteMeasure_ofReal_smul (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (r : ℝ) :
    IsLocallyFiniteMeasure (ENNReal.ofReal r • μ) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, hμU⟩ := IsLocallyFiniteMeasure.finiteAtNhds (μ := μ) x
  exact ⟨U, hU, by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμU⟩

/-- A compact exhaustion of the disc `ball c R` (for the vague decoder). -/
theorem ball_exhaustion (c : ℂ) (R : ℝ) :
    ∃ K : ℕ → Set (ball c R), (∀ n, IsCompact (K n)) ∧
      (∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) := by
  have : LocallyCompactSpace (ball c R) := isOpen_ball.locallyCompactSpace
  let E : CompactExhaustion (ball c R) := CompactExhaustion.choice (ball c R)
  exact ⟨fun n => E n, fun n => E.isCompact n, fun s hs => E.exists_superset_of_isCompact hs⟩

/-- The decoded disc measure: the vague decoder `decoderX` of the dyadic approximants built from the decoded centred
profile `decodeF y`. -/
noncomputable def discDecoder {Y : Type*} [MeasurableSpace Y] {c : ℂ} {R γ : ℝ} {K : ℕ → Set (ball c R)}
    (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) : Y → Measure (ball c R) :=
  decoderX hKs T (fun y k => approxX γ c R (decodeF y) k)
    (fun y k => isLocallyFiniteMeasure_approxX γ c R (decodeF y) k)

/-- Identity of the decoded measure: if the decoded centred profile of `y` is `fieldCircleAverage - P`
and `μ` is the γ-LQG measure of `hc`, the decoded disc measure is `comap val (e^{-γP} • μ)`. -/
theorem discDecoder_eq_comap {Y : Type*} [MeasurableSpace Y] (γ α P : ℝ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ℝ → ℂ → ℝ) (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hc ε)) (μ : Measure ℂ)
    (hμ : IsLQGLimit γ (fieldCircleAverage α hc) μ)
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y)
    (hF : ∀ p : LocalParam c R, decodeF y p = fieldCircleAverage α hc p.1.1 p.1.2 - P) :
    discDecoder (γ := γ) hKs T decodeF y =
      Measure.comap (Subtype.val : ball c R → ℂ) (ENNReal.ofReal (Real.exp (-(γ * P))) • μ) := by
  have : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  have : LocallyCompactSpace (ball c R) := isOpen_ball.locallyCompactSpace
  have : (discDecoder (γ := γ) hKs T decodeF y).Regular := by
    unfold discDecoder decoderX
    infer_instance
  have : IsLocallyFiniteMeasure (ENNReal.ofReal (Real.exp (-(γ * P))) • μ) := inferInstance
  have := isLocallyFiniteMeasure_comap_ball (ENNReal.ofReal (Real.exp (-(γ * P))) • μ) c R
  have : (Measure.comap (Subtype.val : ball c R → ℂ)
      (ENNReal.ofReal (Real.exp (-(γ * P))) • μ)).Regular := inferInstance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  have hconv : y ∈ convSetX T (fun y k => approxX γ c R (decodeF y) k) := fun m =>
    ⟨_, tendsto_approxX_integral γ α P hR hc hcont μ hμ (decodeF y) hF (T.D m)⟩
  unfold discDecoder
  rw [integral_decoderX hKs T _ _ y g, decoderFunctionalX_of_mem hKs T _ _ hconv g]
  exact (tendsto_approxX_integral γ α P hR hc hcont μ hμ (decodeF y) hF g).limUnder_eq

/-- The kernel: `κ(y) = (1 + m_y(D))⁻¹ • map val m_y` for the decoded disc measure `m_y`; it is a
finite measure (`≤ 1` in mass), so the kernel is s-finite. -/
noncomputable def kernelMeas {Y : Type*} [MeasurableSpace Y] {c : ℂ} {R γ : ℝ} {K : ℕ → Set (ball c R)}
    (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y) : Measure ℂ :=
  (1 + discDecoder (γ := γ) hKs T decodeF y univ)⁻¹ •
    Measure.map (Subtype.val : ball c R → ℂ) (discDecoder (γ := γ) hKs T decodeF y)

theorem measurable_kernelMeas {Y : Type*} [MeasurableSpace Y] (γ : ℝ) {c : ℂ} {R : ℝ}
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (hdec : Measurable decodeF) :
    Measurable (kernelMeas (γ := γ) hKs T decodeF) := by
  have hm : Measurable (discDecoder (γ := γ) hKs T decodeF) := by
    unfold discDecoder
    refine measurable_decoderX hKs T _ _ (fun g k => ?_)
    have hfun : (fun y => ∫ x, g x ∂(approxX γ c R (decodeF y) k)) =
        fun y => ∫ x, g x * approxDens γ c R (decodeF y) k x.1 ∂(ballVol c R) := by
      funext y
      exact integral_approxX γ c R (decodeF y) k g
    rw [hfun]
    exact (measurable_integral_approxX γ c R k g).comp hdec
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hfun : (fun y => kernelMeas (γ := γ) hKs T decodeF y S) = fun y =>
      (1 + discDecoder (γ := γ) hKs T decodeF y univ)⁻¹ *
        discDecoder (γ := γ) hKs T decodeF y (Subtype.val ⁻¹' S) := by
    funext y
    rw [kernelMeas, Measure.smul_apply, Measure.map_apply measurable_subtype_coe hS, smul_eq_mul]
  rw [hfun]
  exact ((measurable_const.add ((Measure.measurable_coe MeasurableSet.univ).comp hm)).inv).mul
    ((Measure.measurable_coe (measurable_subtype_coe hS)).comp hm)

/-- Clause A of the kernel, for one observation: on the disc, the kernel of the decoded observation is
a positive multiple of the restricted γ-LQG measure. -/
theorem kernelMeas_restrict_eq (γ α P : ℝ) {c : ℂ} {R : ℝ} (hR : 0 < R) (hc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hc ε)) (μ : Measure ℂ)
    (hμ : IsLQGLimit γ (fieldCircleAverage α hc) μ)
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    {Y : Type*} [MeasurableSpace Y] (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y)
    (hF : ∀ p : LocalParam c R, decodeF y p = fieldCircleAverage α hc p.1.1 p.1.2 - P) :
    ∃ a : ℝ, 0 < a ∧ (kernelMeas (γ := γ) hKs T decodeF y).restrict (ball c R) =
      ENNReal.ofReal a • μ.restrict (ball c R) := by
  have : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  obtain ⟨ν, hν⟩ : ∃ ν : Measure ℂ, ν = ENNReal.ofReal (Real.exp (-(γ * P))) • μ := ⟨_, rfl⟩
  have hs : 0 < Real.exp (-(γ * P)) := Real.exp_pos _
  have hres : ν.restrict (ball c R) = ENNReal.ofReal (Real.exp (-(γ * P))) • μ.restrict (ball c R) := by
    rw [hν, Measure.restrict_smul]
  have hMfin : ν (ball c R) ≠ ⊤ := by
    rw [hν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ball_lt_top).ne
  have h1M : (1 + ν (ball c R)) ≠ 0 := fun h => one_ne_zero (add_eq_zero.1 h).1
  have hK0 : (1 + ν (ball c R))⁻¹ * ENNReal.ofReal (Real.exp (-(γ * P))) ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hMfin⟩))
      (ENNReal.ofReal_pos.2 hs).ne'
  have hKtop : (1 + ν (ball c R))⁻¹ * ENNReal.ofReal (Real.exp (-(γ * P))) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h1M) ENNReal.ofReal_ne_top
  refine ⟨((1 + ν (ball c R))⁻¹ * ENNReal.ofReal (Real.exp (-(γ * P)))).toReal,
    ENNReal.toReal_pos hK0 hKtop, ?_⟩
  have hdisc := discDecoder_eq_comap γ α P hR hc hcont μ hμ hKs T decodeF y hF
  unfold kernelMeas
  rw [hdisc, ← hν]
  have hM : Measure.comap (Subtype.val : ball c R → ℂ) ν univ = ν (ball c R) := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply, image_univ, Subtype.range_coe]
  rw [hM, map_comap_subtype_coe measurableSet_ball ν, Measure.restrict_smul,
    Measure.restrict_restrict measurableSet_ball, Set.inter_self, hres, smul_smul,
    ENNReal.ofReal_toReal hKtop]


end Approximants

end LocalDecoderCommon

end LatticeProb.LocalMeasureKernel
