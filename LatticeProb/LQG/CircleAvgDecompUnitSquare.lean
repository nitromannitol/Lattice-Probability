import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm

/-!
# Circle averages of the whole-plane GFF on the unit square: almost-sure decomposition

Let `h₀` be the whole-plane Gaussian free field of a white noise `W`, and `h^𝕍` the white-noise
zero-boundary GFF of the open unit square `𝕍`. The domain Markov decomposition
`h₀ − h₀_1(0) = h^𝕍 + 𝔥` on `𝕍` holds at the level of circle averages: for a continuous
modification `Y` of the circle averages of `h₀ − h₀_1(0) − h^𝕍` on a box `B` at distance at least
`1/10` from `∂𝕍`, for each fixed centre `z` and radius `r` with `B̄(z, r) ⊆ B`,
`h₀_r(z) − h₀_1(0) = h^𝕍_r(z) + ∫ Y dσ_{z,r}` almost surely.

This file exchanges the quantifiers: almost surely, for every compact `K` in the interior of `B`
and every large `k`, the identity holds at radius `2^{-k}` for Lebesgue-almost every `z ∈ K`. The
exchange is Fubini's theorem on `Ω × ℂ`, which needs the joint measurability in `(ω, z)` of the
three circle-average terms.

## Main results

* `LatticeProb.LQG.ae_forall_ae_mem_of_forall_mem_ae`: Fubini exchange for countably many
  jointly measurable families.
* `LatticeProb.LQG.eventually_forall_lt_infDist_compl`: a compact subset of an open set is
  eventually at distance more than `ρ k → 0` from the complement.
* `LatticeProb.LQG.ae_circleAvg_sub_eq_avgReg_add_integral`: the almost-sure decomposition.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb.LQG

/-- **Fubini exchange for countably many families.** If, for every index `k` and every `z ∈ S k`,
two jointly measurable families agree almost surely, then almost surely, for every `k`, they agree
at Lebesgue-almost every `z ∈ S k`. -/
theorem ae_forall_ae_mem_of_forall_mem_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [SFinite P] {f g : ℕ → Ω → ℂ → ℝ} (hf : ∀ k, Measurable fun q : Ω × ℂ => f k q.1 q.2)
    (hg : ∀ k, Measurable fun q : Ω × ℂ => g k q.1 q.2) {S : ℕ → Set ℂ}
    (hS : ∀ k, MeasurableSet (S k)) (h : ∀ k, ∀ z ∈ S k, (fun ω => f k ω z) =ᵐ[P] fun ω => g k ω z) :
    ∀ᵐ ω ∂P, ∀ k, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ S k → f k ω z = g k ω z := by
  rw [ae_all_iff]
  intro k
  have hm : MeasurableSet {q : Ω × ℂ | q.2 ∈ S k → f k q.1 q.2 = g k q.1 q.2} := by
    have he : {q : Ω × ℂ | q.2 ∈ S k → f k q.1 q.2 = g k q.1 q.2} =
        (Prod.snd ⁻¹' S k)ᶜ ∪ {q : Ω × ℂ | f k q.1 q.2 = g k q.1 q.2} := by
      ext q
      simp [imp_iff_not_or]
    rw [he]
    exact (measurable_snd (hS k)).compl.union (measurableSet_eq_fun (hf k) (hg k))
  refine (Measure.ae_ae_comm (μ := P) (ν := (volume : Measure ℂ))
    (p := fun ω z => z ∈ S k → f k ω z = g k ω z) hm).2 (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ S k
  · filter_upwards [h k z hz] with ω hω _ using hω
  · exact Eventually.of_forall fun ω hz' => absurd hz' hz

/-- A point at distance more than `ρ` from the complement of `U` has its closed ball of radius `ρ`
inside `U`. -/
theorem closedBall_subset_of_lt_infDist {U : Set ℂ} {z : ℂ} {ρ : ℝ}
    (h : ρ < Metric.infDist z Uᶜ) : Metric.closedBall z ρ ⊆ U := by
  intro w hw
  by_contra hwU
  have h1 := Metric.infDist_le_dist_of_mem (x := z) (show w ∈ Uᶜ from hwU)
  rw [Metric.mem_closedBall, dist_comm] at hw
  linarith

/-- For a compact `K` inside an open set `U ≠ ℂ` and radii `ρ k → 0`, eventually every point of `K`
is at distance more than `ρ k` from the complement of `U`. -/
theorem eventually_forall_lt_infDist_compl {U K : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    (hK : IsCompact K) (hKU : K ⊆ U) {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∀ᶠ k in atTop, ∀ z ∈ K, ρ k < Metric.infDist z Uᶜ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun _ z hz => by simp at hz
  obtain ⟨z₀, hz₀, hmin⟩ :=
    hK.exists_isMinOn hne (Metric.continuous_infDist_pt (Uᶜ)).continuousOn
  have hpos : 0 < Metric.infDist z₀ Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 fun h => h (hKU hz₀)
  filter_upwards [hρ.eventually (gt_mem_nhds hpos)] with k hk z hz
  exact lt_of_lt_of_le hk (hmin hz)

end LatticeProb.LQG

namespace LQGMetric

open QuantumZipper GMCIdent3 GMCIdent WhiteNoise

/-- The circle averages `(ω, z) ↦ h_{2^{-k}}(z)` of the white-noise zero-boundary GFF of the unit
square are jointly measurable. -/
theorem _root_.LatticeProb.LQG.measurable_avgReg_wnField {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (k : ℕ) :
    Measurable fun q : Ω × ℂ => avgReg (GMCIdent3.wnField W q.1) k q.2 :=
  (measurable_avgReg k).comp
    ((measurable_circExt.comp ((measurable_wnCircVec hW).comp measurable_fst)).prodMk
      measurable_snd)

/-- For a measurable random distribution `h₀`, the normalized circle averages
`(ω, z) ↦ h₀_r(z) − h₀_1(0)` are jointly measurable. -/
theorem _root_.LatticeProb.LQG.measurable_circleAvg_sub_circleAvg {Ω : Type*} [MeasurableSpace Ω]
    {h₀ : Ω → DistC} (hm : Measurable h₀) (r : ℝ) :
    Measurable fun q : Ω × ℂ =>
      LQGMetric.circleAvg (h₀ q.1) r q.2 - LQGMetric.circleAvg (h₀ q.1) 1 0 := by
  have h1 : Measurable fun q : Ω × ℂ => LQGMetric.circleAvg (h₀ q.1) r q.2 :=
    LQGMetric.measurable_circleAvg.comp
      (f := fun q : Ω × ℂ => ((h₀ q.1, r, q.2) : DistC × ℝ × ℂ))
      ((hm.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have h2 : Measurable fun q : Ω × ℂ => LQGMetric.circleAvg (h₀ q.1) 1 0 :=
    LQGMetric.measurable_circleAvg.comp
      (f := fun q : Ω × ℂ => ((h₀ q.1, 1, 0) : DistC × ℝ × ℂ))
      ((hm.comp measurable_fst).prodMk measurable_const)
  exact h1.sub h2

/-- For a random function `Y` continuous in `z` for every `ω` and measurable in `ω` for every `z`,
the circle averages `(ω, z) ↦ ∫ Y(·, ω) dσ_{z,r}` are jointly measurable. -/
theorem _root_.LatticeProb.LQG.measurable_integral_circleUnif {Ω : Type*} [MeasurableSpace Ω]
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun z => Y z ω) (hYm : ∀ z, Measurable (Y z))
    (r : ℝ) : Measurable fun q : Ω × ℂ => ∫ x, Y x q.1 ∂(circleUnif q.2 r) := by
  have hY : Measurable (Function.uncurry Y) :=
    measurable_uncurry_of_continuous_of_measurable hYc hYm
  have hm : Measurable fun q : (Ω × ℂ) × ℝ => Y (circleMap q.1.2 r q.2) q.1.1 :=
    have hcm : Continuous fun p : ℂ × ℝ => circleMap p.1 r p.2 :=
      continuous_fst.add (continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))
    hY.comp ((hcm.measurable.comp ((measurable_snd.comp measurable_fst).prodMk
      measurable_snd)).prodMk (measurable_fst.comp measurable_fst))
  have := (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).const_smul (2 * Real.pi)⁻¹
  convert this.measurable using 1
  funext q
  rw [QuantumZipper.CoordReg.integral_circleUnif_eq_circleAverage (hYc q.1).measurable]
  simp only [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rfl

/-- **Circle-average decomposition on the unit square, almost surely on compacts.** Let `h₀` be
the whole-plane GFF of a white noise `W` (or any measurable random distribution), and `Y` a
random function, continuous in `z` and measurable in `ω`, whose circle averages over discs in a
box `B` at distance `≥ 1/10` from the boundary of the unit square `𝕍` are almost surely those of
`h₀ − h₀_1(0)` minus those of the white-noise zero-boundary GFF `h^𝕍` of `𝕍`. Then almost surely,
for every compact `K` in the interior of `B`, for all large `k`, at Lebesgue-almost every `z ∈ K`,
`h₀_{2^{-k}}(z) − h₀_1(0) = h^𝕍_{2^{-k}}(z) + ∫ Y dσ_{z,2^{-k}}`. -/
theorem _root_.LatticeProb.LQG.ae_circleAvg_sub_eq_avgReg_add_integral
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → Measure ℂ → ℝ} (hX : IsZeroBoundaryGFFOn openSquare X P')
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {h₀ : Ω → DistC} (hm : Measurable h₀)
    {B : Set ℂ} (hB : ∀ z ∈ B, Metric.ball z (1 / 10) ⊆ openSquare)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun z => Y z ω) (hYm : ∀ z, Measurable (Y z))
    (hF : ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ B →
      (fun ω => ∫ x, Y x ω ∂(circleUnif z r)) =ᵐ[P] fun ω =>
        LQGMetric.circleAvg (h₀ ω) r z - LQGMetric.circleAvg (h₀ ω) 1 0 -
          Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω) :
    ∀ᵐ ω ∂P, ∀ K, IsCompact K → K ⊆ interior B → ∀ᶠ k in atTop,
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ K →
        LQGMetric.circleAvg (h₀ ω) (radius k) z - LQGMetric.circleAvg (h₀ ω) 1 0 =
          avgReg (GMCIdent3.wnField W ω) k z + ∫ x, Y x ω ∂(circleUnif z (radius k)) := by
  have hBsq : B ⊆ openSquare := fun z hz => hB z hz (Metric.mem_ball_self (by norm_num))
  have hUc : (interior B)ᶜ.Nonempty := ⟨0, fun h0 => by
    have h1 := openSquare_subset_H (hBsq (interior_subset h0))
    simp [H] at h1⟩
  have hkey := LatticeProb.LQG.ae_forall_ae_mem_of_forall_mem_ae (P := P)
    (f := fun k ω z => LQGMetric.circleAvg (h₀ ω) (radius k) z - LQGMetric.circleAvg (h₀ ω) 1 0)
    (g := fun k ω z => avgReg (GMCIdent3.wnField W ω) k z + ∫ x, Y x ω ∂(circleUnif z (radius k)))
    (S := fun k => {z | 2 * radius k < Metric.infDist z (interior B)ᶜ})
    (fun k => LatticeProb.LQG.measurable_circleAvg_sub_circleAvg hm _)
    (fun k => (LatticeProb.LQG.measurable_avgReg_wnField hW k).add
      (LatticeProb.LQG.measurable_integral_circleUnif hYc hYm _))
    (fun k => measurableSet_lt measurable_const (Metric.continuous_infDist_pt _).measurable)
    (fun k z hz => by
      have h2 : Metric.closedBall z (2 * radius k) ⊆ interior B :=
        LatticeProb.LQG.closedBall_subset_of_lt_infDist hz
      have hr := radius_pos k
      have h1 : Metric.closedBall z (radius k) ⊆ B :=
        ((Metric.closedBall_subset_closedBall (by linarith)).trans h2).trans interior_subset
      have h2' : Metric.closedBall z (2 * radius k) ⊆ openSquare :=
        (h2.trans interior_subset).trans hBsq
      filter_upwards [hF z (radius k) hr h1, avgReg_ae_eq_wn hX hW h2'] with ω e1 e2
      linarith)
  have hρ : Tendsto (fun k => 2 * radius k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul (2 : ℝ)
    rw [mul_zero] at this
    exact this
  filter_upwards [hkey] with ω hω K hK hKU
  filter_upwards [LatticeProb.LQG.eventually_forall_lt_infDist_compl isOpen_interior hUc hK hKU
    hρ] with k hk
  filter_upwards [hω k] with z hz hzK
  exact hz (hk z hzK)

end LQGMetric
