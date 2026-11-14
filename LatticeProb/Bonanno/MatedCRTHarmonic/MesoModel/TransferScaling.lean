/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.TransferScaling at commit fdb5cad;
   selected declarations and their proof closure, with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

/-- Rescale a two-sided Brownian path so mesh `ε` becomes unit mesh. -/
def unitRescalePath (ε : ℝ) (ω : MatedCRT.Path2) : MatedCRT.Path2 :=
  ⟨fun t => (Real.sqrt ε)⁻¹ • ω (ε * t), by fun_prop⟩

theorem lrCoord_unitRescalePath (ε : ℝ) (ω : MatedCRT.Path2)
    (i : Fin 2) (t : ℝ) :
    MatedCRT.lrCoord i t (unitRescalePath ε ω) =
      (Real.sqrt ε)⁻¹ * MatedCRT.lrCoord i (ε * t) ω := by
  fin_cases i <;> rfl

private theorem intervalInf_unitRescalePath {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b)
    (ω : MatedCRT.Path2) (i : Fin 2) :
    MatedCRT.intervalInf (fun t => MatedCRT.lrCoord i t (unitRescalePath ε ω)) a b =
      (Real.sqrt ε)⁻¹ *
        MatedCRT.intervalInf (fun t => MatedCRT.lrCoord i t ω) (ε * a) (ε * b) := by
  let c : ℝ := (Real.sqrt ε)⁻¹
  let X : ℝ → ℝ := fun t => MatedCRT.lrCoord i t ω
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hX : Continuous X := by
    dsimp [X, MatedCRT.lrCoord]
    split_ifs with hi
    · exact continuous_fst.comp ω.continuous
    · exact continuous_snd.comp ω.continuous
  have htime : (fun t => MatedCRT.lrCoord i t (unitRescalePath ε ω)) =
      (fun t => c * X (ε * t)) := by
    funext t
    simp [c, X, lrCoord_unitRescalePath]
  unfold MatedCRT.intervalInf
  rw [htime]
  let S : Set ℝ := X '' Set.Icc (ε * a) (ε * b)
  have hIcc : (fun t : ℝ => ε * t) '' Set.Icc a b = Set.Icc (ε * a) (ε * b) := by
    exact image_mul_left_Icc' hε a b
  have himage : (fun t => c * X (ε * t)) '' Set.Icc a b = (fun x => c * x) '' S := by
    dsimp [S]
    calc
      (fun t => c * X (ε * t)) '' Set.Icc a b =
          (fun z => c * X z) '' ((fun t => ε * t) '' Set.Icc a b) := by
        change ((fun z => c * X z) ∘ (fun t => ε * t)) '' Set.Icc a b = _
        rw [Set.image_image]
        rfl
      _ = ((fun x => c * x) '' (X '' Set.Icc (ε * a) (ε * b))) := by
        rw [hIcc]
        rw [← Set.image_image]
  rw [himage]
  change sInf ((fun x => c * x) '' S) = c * sInf S
  have hcompact : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.image hX
  have hSnon : S.Nonempty := by
    refine ⟨X (ε * a), ?_⟩
    refine ⟨ε * a, ⟨le_rfl, ?_⟩, rfl⟩
    exact mul_le_mul_of_nonneg_left hab hε.le
  have hbounded : BddBelow S := hcompact.bddBelow
  have hglb : IsGLB S (sInf S) := isGLB_csInf hSnon hbounded
  have hscaled : IsGLB ((fun x => c * x) '' S) (c * sInf S) := hglb.mul_left hc.le
  have hscaledInf : IsGLB ((fun x => c * x) '' S)
      (sInf ((fun x => c * x) '' S)) :=
    isGLB_csInf (hSnon.image _) hscaled.bddBelow
  exact hscaled.unique hscaledInf |>.symm

/-- The side-minimum condition for mesh `ε` is exactly the unit-mesh condition of the rescaled
path. -/
theorem sideCond_unitRescalePath {ε : ℝ} (hε : 0 < ε) (ω : MatedCRT.Path2)
    (i : Fin 2) {x y : ℤ} (hxy : x < y) :
    MatedCRT.SideCond ε (fun t => MatedCRT.lrCoord i t ω) x y ↔
      MatedCRT.SideCond 1 (fun t => MatedCRT.lrCoord i t (unitRescalePath ε ω)) x y := by
  have hc : 0 < (Real.sqrt ε)⁻¹ := by positivity
  have hxy' : x + 1 ≤ y := by omega
  have hmidZ : x ≤ y - 1 := by omega
  have hleft : (x : ℝ) - 1 ≤ x := by linarith
  have hright : (y : ℝ) - 1 ≤ y := by linarith
  have hmiddle : (x : ℝ) ≤ (y : ℝ) - 1 := by exact_mod_cast hmidZ
  have hA := intervalInf_unitRescalePath hε hleft ω i
    (a := (x : ℝ) - 1) (b := (x : ℝ))
  have hB := intervalInf_unitRescalePath hε hright ω i
    (a := (y : ℝ) - 1) (b := (y : ℝ))
  have hC := intervalInf_unitRescalePath hε hmiddle ω i
    (a := (x : ℝ)) (b := (y : ℝ) - 1)
  rw [MatedCRT.SideCond, MatedCRT.SideCond]
  simp only [one_mul]
  rw [hA, hB, hC, max_le_iff, max_le_iff]
  constructor
  · intro h
    rcases h with ⟨ha, hb⟩
    exact ⟨(mul_le_mul_iff_right₀ hc).2 ha, (mul_le_mul_iff_right₀ hc).2 hb⟩
  · intro h
    rcases h with ⟨ha, hb⟩
    exact ⟨(mul_le_mul_iff_right₀ hc).1 ha, (mul_le_mul_iff_right₀ hc).1 hb⟩

private theorem sideCond_bool_unitRescalePath {ε : ℝ} (hε : 0 < ε)
    (ω : MatedCRT.Path2) (b : Bool) {x y : ℤ} (hxy : x < y) :
    MatedCRT.SideCond ε (fun t => if b then (ω t).2 else (ω t).1) x y ↔
      MatedCRT.SideCond 1
        (fun t => if b then (unitRescalePath ε ω t).2 else (unitRescalePath ε ω t).1) x y := by
  cases b
  · simpa [MatedCRT.lrCoord] using
      (sideCond_unitRescalePath hε ω 0 hxy)
  · simpa [MatedCRT.lrCoord] using
      (sideCond_unitRescalePath hε ω 1 hxy)

/-- The labelled edge criterion is invariant under unit-mesh Brownian rescaling. -/
theorem isEdge_unitRescalePath {ε : ℝ} (hε : 0 < ε) (ω : MatedCRT.Path2)
    (e : ℤ × ℤ × Bool) :
    MatedCRT.IsEdge ε ω e ↔ MatedCRT.IsEdge 1 (unitRescalePath ε ω) e := by
  unfold MatedCRT.IsEdge
  constructor
  · rintro ⟨hxy, hcase⟩
    refine ⟨hxy, ?_⟩
    rcases hcase with hcon | ⟨hne, hside⟩
    · exact Or.inl hcon
    · exact Or.inr ⟨hne, (sideCond_bool_unitRescalePath hε ω e.2.2 hxy).1 hside⟩
  · rintro ⟨hxy, hcase⟩
    refine ⟨hxy, ?_⟩
    rcases hcase with hcon | ⟨hne, hside⟩
    · exact Or.inl hcon
    · exact Or.inr ⟨hne, (sideCond_bool_unitRescalePath hε ω e.2.2 hxy).2 hside⟩

/-- The edge predicates agree pointwise, by the minima scaling calculation. -/
theorem edgePredicateEq_unitRescalePath {ε : ℝ} (hε : 0 < ε)
    (ω : MatedCRT.Path2) :
    MatedCRT.IsEdge ε ω = MatedCRT.IsEdge 1 (unitRescalePath ε ω) := by
  funext e
  exact propext (isEdge_unitRescalePath hε ω e)

/-- Positive Brownian time scaling is homogeneous for the two-sided minimum kernel. -/
private theorem twoSidedMin_unitScale {ε s t : ℝ} (hε : 0 < ε) :
    MatedCRT.twoSidedMin (ε * s) (ε * t) = ε * MatedCRT.twoSidedMin s t := by
  have hmax (r : ℝ) : max (ε * r) 0 = ε * max r 0 := by
    simpa using (mul_max_of_nonneg r 0 hε.le).symm
  have hmaxNeg (r : ℝ) : max (-(ε * r)) 0 = ε * max (-r) 0 := by
    rw [show -(ε * r) = ε * (-r) by ring]
    exact hmax (-r)
  have hmin (a b : ℝ) : min (ε * a) (ε * b) = ε * min a b := by
    rw [← mul_min_of_nonneg a b hε.le]
  unfold MatedCRT.twoSidedMin
  rw [hmax s, hmax t, hmaxNeg s, hmaxNeg t,
    hmin (max s 0) (max t 0), hmin (max (-s) 0) (max (-t) 0), ← mul_add]

/-- The path-valued unit-rescaling map is Borel measurable. -/
theorem measurable_unitRescalePath (ε : ℝ) :
    Measurable (unitRescalePath ε : MatedCRT.Path2 → MatedCRT.Path2) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  change Measurable (fun ω : MatedCRT.Path2 =>
    (Real.sqrt ε)⁻¹ • ω (ε * t))
  apply Measurable.prodMk
  · simpa [mul_comm] using
      (measurable_fst.comp (ContinuousMap.measurable_eval (ε * t))).const_mul
        ((Real.sqrt ε)⁻¹)
  · simpa [mul_comm] using
      (measurable_snd.comp (ContinuousMap.measurable_eval (ε * t))).const_mul
        ((Real.sqrt ε)⁻¹)

private theorem measurable_transferLrCoord (p : Fin 2 × ℝ) :
    Measurable (fun ω : MatedCRT.Path2 => MatedCRT.lrCoord p.1 p.2 ω) := by
  unfold MatedCRT.lrCoord
  split_ifs with hi
  · exact measurable_fst.comp (ContinuousMap.measurable_eval p.2)
  · exact measurable_snd.comp (ContinuousMap.measurable_eval p.2)

private def transferEval (I : Finset (Fin 2 × ℝ)) (ω : MatedCRT.Path2) : I → ℝ :=
  fun p => MatedCRT.lrCoord p.1.1 p.1.2 ω

private theorem measurable_transferEval (I : Finset (Fin 2 × ℝ)) :
    Measurable (transferEval I) := by
  apply Measurable.of_eval
  intro p
  exact measurable_transferLrCoord p.1

/-- Brownian scaling preserves the correlated two-sided Brownian path law. The time change is
`t ↦ εt` and the space factor is `ε⁻¹ᐟ²`, the factors required to change mesh `ε` to mesh one. -/
theorem isCorrelatedBM2_map_unitRescalePath {γ ε : ℝ} {μ : Measure MatedCRT.Path2}
    (hε : 0 < ε) (hμ : MatedCRT.IsCorrelatedBM2 γ μ) :
    MatedCRT.IsCorrelatedBM2 γ (μ.map (unitRescalePath ε)) := by
  let c : ℝ := (Real.sqrt ε)⁻¹
  let F : MatedCRT.Path2 → MatedCRT.Path2 := unitRescalePath ε
  let coord : Fin 2 × ℝ → MatedCRT.Path2 → ℝ :=
    fun p ω => MatedCRT.lrCoord p.1 p.2 ω
  let time : Fin 2 × ℝ → Fin 2 × ℝ := fun p => (p.1, ε * p.2)
  let scaledCoord : Fin 2 × ℝ → MatedCRT.Path2 → ℝ :=
    fun p ω => c * coord (time p) ω
  have hcoord (p : Fin 2 × ℝ) (ω : MatedCRT.Path2) :
      coord p (F ω) = scaledCoord p ω := by
    simp [coord, scaledCoord, time, F, c, lrCoord_unitRescalePath]
  have hscaledGP : IsGaussianProcess scaledCoord μ := by
    have hbase : IsGaussianProcess coord μ := hμ.isGaussianProcess
    change IsGaussianProcess (fun p : Fin 2 × ℝ => fun ω =>
      MatedCRT.lrCoord p.1 p.2 ω) μ at hbase
    change IsGaussianProcess (fun p : Fin 2 × ℝ => fun ω => c *
      MatedCRT.lrCoord p.1 (ε * p.2) ω) μ
    exact (hbase.comp_right time).smul (fun _ => c)
  have hFmeas : Measurable F := by
    exact measurable_unitRescalePath ε
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  refine ⟨?_, ?_, ?_, ?_⟩
  · infer_instance
  · refine ⟨fun I => ?_⟩
    refine ⟨(measurable_transferEval I).aemeasurable, ?_⟩
    change IsGaussian ((μ.map F).map (transferEval I))
    rw [AEMeasurable.map_map_of_aemeasurable
      (measurable_transferEval I).aemeasurable hFmeas.aemeasurable]
    have heq : transferEval I ∘ F =
        (fun ω => I.restrict (fun p => scaledCoord p ω)) := by
      funext ω
      funext p
      change MatedCRT.lrCoord p.1.1 p.1.2 (F ω) = scaledCoord p.1 ω
      exact hcoord p.1 ω
    rw [heq]
    exact (hscaledGP.hasGaussianLaw I).isGaussian_map
  · intro i t
    rw [integral_map hFmeas.aemeasurable
      (measurable_transferLrCoord (i, t)).aestronglyMeasurable]
    change ∫ ω, MatedCRT.lrCoord i t (F ω) ∂μ = 0
    have hcoord' : (fun ω => MatedCRT.lrCoord i t (F ω)) =
        (fun ω => c * MatedCRT.lrCoord i (ε * t) ω) := by
      funext ω
      simpa [F, c] using lrCoord_unitRescalePath ε ω i t
    rw [hcoord']
    rw [integral_const_mul, hμ.integral_eq_zero i (ε * t), mul_zero]
  · intro i j s t
    rw [covariance_map (measurable_transferLrCoord (i, s)).aestronglyMeasurable
      (measurable_transferLrCoord (j, t)).aestronglyMeasurable hFmeas.aemeasurable]
    change cov[MatedCRT.lrCoord i s ∘ F, MatedCRT.lrCoord j t ∘ F; μ] = _
    rw [show MatedCRT.lrCoord i s ∘ F = fun ω => c * MatedCRT.lrCoord i (ε * s) ω by
        funext ω
        exact hcoord (i, s) ω,
      show MatedCRT.lrCoord j t ∘ F = fun ω => c * MatedCRT.lrCoord j (ε * t) ω by
        funext ω
        exact hcoord (j, t) ω,
      covariance_const_mul_left, covariance_const_mul_right,
      hμ.covariance_eq i j (ε * s) (ε * t)]
    have hc : c * c * ε = 1 := by
      dsimp [c]
      have hsqrt : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε).ne'
      field_simp [hsqrt]
      rw [Real.sq_sqrt hε.le]
    rw [twoSidedMin_unitScale hε]
    calc
      c * (c * (MatedCRT.lrCov γ i j * (ε * MatedCRT.twoSidedMin s t))) =
          c * c * (MatedCRT.lrCov γ i j * (ε * MatedCRT.twoSidedMin s t)) := by ring
      _ =
          (c * c * ε) * (MatedCRT.lrCov γ i j * MatedCRT.twoSidedMin s t) := by ring
      _ = MatedCRT.lrCov γ i j * MatedCRT.twoSidedMin s t := by rw [hc, one_mul]


end MatedCRTHarmonic.MesoModel
