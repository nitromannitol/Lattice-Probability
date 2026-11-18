import LatticeProb.Topology.RerootedExitWindowLaw
import LatticeProb.Prob.FirstHitSpacedExitTrial
import LatticeProb.Prob.ContinuousStoppedPath
import LatticeProb.Prob.BrownianOpenExit
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOMain

/-!
# The exit-window ball bound from the conditional bound for the first-hit path law

Let `ηL` be the whole-plane space-filling SLE curve of a mating-of-trees coupling, parametrized
by Lebesgue measure, and let `ν` be the law of its path after the first hit of the origin,
in Euclidean coordinates on `[0, ∞)`. Assume the conditional lower bound: for every
`q ∈ (0, 1)`, given the path stopped at its exit from the unit ball, a ball of radius `a q`
lies in the trace between the exits from `ball 0 1` and from `ball 0 (1 + q)` with conditional
probability at least `p > 0`, `ν`-almost surely.

Since `ηL` is rooted at the origin at time `0` almost surely, the exit window of `ηL` at
radius `1` (the exit time and the curve observed up to it) is a measurable function of the
stopped path. Integrating the conditional bound over the preimage of a measurable set `S` of
exit windows gives the integrated lower bound: with `δ = min a (1/2)` and `p' = min p (1/2)`,
for every `ε ∈ (0, 1)`, a ball of radius `δ ε` lies in the trace of `ηL` between its exits from
`ball 0 1` and from `ball 0 (1 + ε)` with probability at least `p'` times the probability that
the exit window lies in `S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

section Deterministic

/-- The complex curve on `ℝ` read off a path on `[0, ∞)` in Euclidean coordinates, frozen at
its initial value on negative times. -/
def nonnegComplexCurve (u : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) : C(ℝ, ℂ) :=
  (⟨Complex.orthonormalBasisOneI.repr.symm, Complex.orthonormalBasisOneI.repr.symm.continuous⟩ :
    C(EuclideanSpace ℝ (Fin 2), ℂ)).comp (u.comp ⟨Real.toNNReal, continuous_real_toNNReal⟩)

theorem nonnegComplexCurve_apply (u : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) (t : ℝ) :
    nonnegComplexCurve u t = Complex.orthonormalBasisOneI.repr.symm (u t.toNNReal) := rfl

theorem continuous_nonnegComplexCurve : Continuous nonnegComplexCurve :=
  (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)

theorem exitTimeAfter_zero_nonneg (c : ℝ → ℂ) (r : ℝ) : 0 ≤ exitTimeAfter c 0 0 r :=
  Real.sInf_nonneg fun _ hx => hx.1

/-- If a continuous curve leaves `ball 0 r` at a nonnegative time, its first exit time after
`0` is attained. -/
theorem exitTimeAfter_zero_mem (c : C(ℝ, ℂ)) {r : ℝ}
    (hex : ∃ t, 0 ≤ t ∧ c t ∉ ball (0 : ℂ) r) :
    0 ≤ exitTimeAfter c 0 0 r ∧ c (exitTimeAfter c 0 0 r) ∉ ball (0 : ℂ) r := by
  have hcl : IsClosed {t : ℝ | 0 ≤ t ∧ c t ∉ ball (0 : ℂ) r} :=
    (isClosed_le continuous_const continuous_id).inter
      (isOpen_ball.isClosed_compl.preimage c.continuous)
  exact hcl.csInf_mem hex ⟨0, fun _ ht => ht.1⟩

theorem mem_ball_of_lt_exitTimeAfter_zero (c : C(ℝ, ℂ)) {r t : ℝ} (ht : 0 ≤ t)
    (hlt : t < exitTimeAfter c 0 0 r) : c t ∈ ball (0 : ℂ) r := by
  by_contra h
  exact (not_le.2 hlt) (csInf_le ⟨0, fun _ h => h.1⟩ ⟨ht, h⟩)

variable {v : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))} {c : C(ℝ, ℂ)}

/-- Exit sets from centered balls agree for a Euclidean path and a complex curve that agree on
`[0, ∞)`. -/
theorem sInf_euclidean_exit_eq_exitTimeAfter
    (hv : ∀ t : ℝ≥0, v t = Complex.orthonormalBasisOneI.repr (c t)) (r : ℝ) :
    sInf {t : ℝ | 0 ≤ t ∧ v t.toNNReal ∉ ball 0 r} = exitTimeAfter c 0 0 r := by
  unfold exitTimeAfter
  congr 1
  refine Set.ext fun t => and_congr_right fun ht => ?_
  rw [hv, Real.coe_toNNReal _ ht, mem_ball_zero_iff, mem_ball_zero_iff,
    LinearIsometryEquiv.norm_map]

/-- The open exit time of the Euclidean path from `ball 0 r` is the exit time of the complex
curve after `0`. -/
theorem openExitTime_euclidean_eq_exitTimeAfter
    (hv : ∀ t : ℝ≥0, v t = Complex.orthonormalBasisOneI.repr (c t)) {r : ℝ}
    (hex : ∃ t, 0 ≤ t ∧ c t ∉ ball (0 : ℂ) r) :
    openExitTime (fun t (_ : Unit) => v t) (ball 0 r) () =
      ((exitTimeAfter c 0 0 r).toNNReal : ℝ≥0∞) := by
  obtain ⟨hT0, hmem⟩ := exitTimeAfter_zero_mem c hex
  have key : ∀ t : ℝ≥0, v t ∉ ball 0 r ↔ c t ∉ ball (0 : ℂ) r := by
    intro t
    rw [hv, mem_ball_zero_iff, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  unfold openExitTime
  apply le_antisymm
  · refine iInf_le_of_le ⟨(exitTimeAfter c 0 0 r).toNNReal, ?_⟩ le_rfl
    rw [key, Real.coe_toNNReal _ hT0]
    exact hmem
  · refine le_iInf fun t => ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ?_)
    exact csInf_le ⟨0, fun _ h => h.1⟩ ⟨t.val.2, (key t.val).1 t.prop⟩

/-- **The exit window is read off the stopped Euclidean path.** -/
theorem originExitWindow_nonnegComplexCurve_stoppedPath
    (hv : ∀ t : ℝ≥0, v t = Complex.orthonormalBasisOneI.repr (c t)) {r : ℝ}
    (hex : ∃ t, 0 ≤ t ∧ c t ∉ ball (0 : ℂ) r) :
    originExitWindow r (nonnegComplexCurve
      (stoppedPath (openExitTime (fun t (_ : Unit) => v t) (ball 0 r) ()) v)) =
      originExitWindow r c := by
  obtain ⟨hT0, hmem⟩ := exitTimeAfter_zero_mem c hex
  set T := exitTimeAfter c 0 0 r with hT
  have hW : nonnegComplexCurve
      (stoppedPath (openExitTime (fun t (_ : Unit) => v t) (ball 0 r) ()) v) =
      realWindowCurve 0 T c := by
    ext s
    rw [nonnegComplexCurve_apply, stoppedPath_apply, openExitTime_euclidean_eq_exitTimeAfter hv hex,
      ← ENNReal.coe_min, ENNReal.toNNReal_coe, hv, LinearIsometryEquiv.symm_apply_apply,
      realWindowCurve_apply, NNReal.coe_min, Real.coe_toNNReal', Real.coe_toNNReal _ hT0]
  have hexit : exitTimeAfter (realWindowCurve 0 T c) 0 0 r = T := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨hT0, ?_⟩
      rw [realWindowCurve_apply, max_eq_left hT0, min_self]
      exact hmem
    · rintro t ⟨ht0, ht⟩
      refine le_of_not_gt fun hlt => ht ?_
      rw [realWindowCurve_apply, max_eq_left ht0, min_eq_left hlt.le]
      exact mem_ball_of_lt_exitTimeAfter_zero c ht0 hlt
  have hidem : realWindowCurve 0 T (realWindowCurve 0 T c) = realWindowCurve 0 T c := by
    ext s
    rw [realWindowCurve_apply, realWindowCurve_apply, realWindowCurve_apply,
      max_eq_left (le_min (le_max_right _ _) hT0), min_assoc, min_self]
  rw [hW]
  unfold originExitWindow
  rw [hexit, hidem]

/-- A ball in the Euclidean trace between two exits gives a ball, of any smaller radius, in the
complex trace between the corresponding exits. -/
theorem exists_ball_subset_exitWindow_of_euclidean
    (hv : ∀ t : ℝ≥0, v t = Complex.orthonormalBasisOneI.repr (c t)) {a b ρ ρ' : ℝ}
    (hρ : ρ' ≤ ρ)
    (h : ∃ y, ball y ρ ⊆ (fun t : ℝ => v t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ v t.toNNReal ∉ ball 0 a})
      (sInf {t : ℝ | 0 ≤ t ∧ v t.toNNReal ∉ ball 0 b})) :
    ∃ x, ball x ρ' ⊆ c '' Icc (exitTimeAfter c 0 0 a) (exitTimeAfter c 0 0 b) := by
  rw [sInf_euclidean_exit_eq_exitTimeAfter hv, sInf_euclidean_exit_eq_exitTimeAfter hv] at h
  obtain ⟨y, hy⟩ := h
  let e := Complex.orthonormalBasisOneI.repr
  refine ⟨e.symm y, fun x hx => ?_⟩
  have hd : dist (e x) y = dist x (e.symm y) := by
    have := e.symm.dist_map (e x) y
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    exact this.symm
  have hx' : e x ∈ ball y ρ := by
    rw [mem_ball, hd]
    exact (mem_ball.1 hx).trans_le hρ
  obtain ⟨t, ht, hte⟩ := hy hx'
  refine ⟨t, ht, e.injective ?_⟩
  have hte' : v t.toNNReal = e x := hte
  rw [← hte', hv, Real.coe_toNNReal _ ((exitTimeAfter_zero_nonneg c a).trans ht.1)]

end Deterministic

section Coupling

variable {γ : ℝ} {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **Integrated exit-window ball bound from the conditional bound for the first-hit path law.**
If, for every `q ∈ (0, 1)`, given the first-hit path of the origin stopped at its exit from the
unit ball, a ball of radius `a q` lies in its trace between the exits from `ball 0 1` and
`ball 0 (1 + q)` with conditional probability at least `p > 0`, then with `δ = min a (1/2)` and
`p' = min p (1/2)`, for every `ε ∈ (0, 1)` and every measurable set `S` of exit windows, a ball
of radius `δ ε` lies in the trace of `ηL` between its exits from `ball 0 1` and
`ball 0 (1 + ε)` with probability at least `p'` times the probability that the exit window of
`ηL` at radius `1` lies in `S`. -/
theorem IsMatingOfTreesCoupling.exitWindow_ball_bound_of_reference
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ηsize p : ℝ} (hη : 0 < ηsize) (hp : 0 < p)
    (href : ∀ q : ℝ, 0 < q → q < 1 →
      let ν := P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)
      let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
        ∃ y, ball y (ηsize * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
      let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => stoppedPath
        (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
      ∀ᵐ w ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap O inferInstance] w) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∃ p ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ S : Set (ℝ × C(ℝ, ℂ)), MeasurableSet S →
        ENNReal.ofReal p * P {ω | (exitTimeAfter (ηL ω) 0 0 1,
            realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} ≤
          P ({ω | (exitTimeAfter (ηL ω) 0 0 1,
              realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} ∩
            {ω | ∃ w, ball w (δ * ε) ⊆ ηL ω '' Icc (exitTimeAfter (ηL ω) 0 0 1)
              (exitTimeAfter (ηL ω) 0 0 (1 + ε))}) := by
  have := hC.isProbabilityMeasure
  let Φ := fun ω => firstHitNonnegativeCurve (ηL ω) 0
  have hm : Measurable Φ := by
    change Measurable ((fun q : C(ℝ, ℂ) × ℂ => firstHitNonnegativeCurve q.1 q.2) ∘
      (fun ω => (ηL ω, (0 : ℂ))))
    exact measurable_firstHitNonnegativeCurve.comp
      (hC.measurable_curves.1.prodMk measurable_const)
  have hgood : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, Φ ω t = Complex.orthonormalBasisOneI.repr (ηL ω t)) ∧
      ∀ R : ℝ, ∃ t, 0 ≤ t ∧ ηL ω t ∉ ball (0 : ℂ) R := by
    filter_upwards [CellScaling.JointScalingO.ae_firstHit_zero_of_coupling hC, hC.spaceFilling]
      with ω hroot hω
    refine ⟨fun t => ?_, fun R => exists_exit_of_tendsto_cocompact hω.2.1 0 0 R⟩
    have hroot' : GMS4b.hitTime (ηL ω) 0 = 0 := hroot
    change Complex.orthonormalBasisOneI.repr
      (ηL ω (GMS4b.hitTime (ηL ω) 0 + (t : ℝ)) - 0) = _
    rw [hroot', zero_add, sub_zero]
  refine ⟨min ηsize (1 / 2), ⟨lt_min hη (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩,
    min p (1 / 2), ⟨lt_min hp (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩,
    fun ε hε S hS => ?_⟩
  let ν := P.map Φ
  let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
    ∃ y, ball y (ηsize * ε) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + ε)})}
  let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => stoppedPath
    (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
  have h1 : ∀ᵐ w ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap O inferInstance] w := href ε hε.1 hε.2
  have hν : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hpos : ∀ f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) → ℝ, (∀ w, f w = 0) →
      ¬ ∀ᵐ w ∂ν, p ≤ f w := by
    intro f hf hae
    obtain ⟨w, hw⟩ := hae.exists
    rw [hf] at hw
    linarith
  have hle : MeasurableSpace.comap O inferInstance ≤
      (inferInstance : MeasurableSpace C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) := by
    by_contra hne
    exact hpos _ (fun w => by rw [condExp_of_not_le hne]; rfl) h1
  have hint : Integrable (A.indicator (fun _ => (1 : ℝ))) ν := by
    by_contra hne
    exact hpos _ (fun w => by rw [condExp_of_not_integrable hne]; rfl) h1
  let g : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) → ℝ × C(ℝ, ℂ) :=
    fun u => originExitWindow 1 (nonnegComplexCurve u)
  have hg : Measurable g :=
    (measurable_originExitWindow 1).comp continuous_nonnegComplexCurve.measurable
  let T := O ⁻¹' (g ⁻¹' S)
  have hTm : MeasurableSet[MeasurableSpace.comap O inferInstance] T := ⟨g ⁻¹' S, hg hS, rfl⟩
  have hT : MeasurableSet T := hle _ hTm
  have hA : NullMeasurableSet A ν := by
    have h := hint.aestronglyMeasurable.aemeasurable.nullMeasurable
      (measurableSet_singleton (1 : ℝ))
    have hpre : A.indicator (fun _ => (1 : ℝ)) ⁻¹' {1} = A := by
      ext w
      by_cases hw : w ∈ A <;> simp [hw]
    rwa [hpre] at h
  have hind : ∫ w in T, A.indicator (fun _ => (1 : ℝ)) w ∂ν = ν.real (T ∩ A) := by
    rw [integral_indicator₀ (hA.mono_ac Measure.restrict_le_self.absolutelyContinuous),
      setIntegral_const, smul_eq_mul, mul_one, Measure.real, Measure.real,
      Measure.restrict_apply' hT, inter_comm]
  have hlow : p * ν.real T ≤ ν.real (T ∩ A) := by
    rw [← hind, ← setIntegral_condExp hle hint hTm]
    have hc : ∫ w in T, p ∂ν = ν.real T * p := by
      rw [setIntegral_const, smul_eq_mul]
    rw [mul_comm, ← hc]
    exact setIntegral_mono_ae (integrable_const p).integrableOn integrable_condExp.integrableOn h1
  have hENN : ENNReal.ofReal p * ν T ≤ ν (T ∩ A) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν T),
      ← ENNReal.ofReal_toReal (measure_ne_top ν (T ∩ A)), ← ENNReal.ofReal_mul hp.le]
    exact ENNReal.ofReal_le_ofReal hlow
  have hSeq : {ω | (exitTimeAfter (ηL ω) 0 0 1,
      realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} =ᵐ[P] Φ ⁻¹' T := by
    filter_upwards [hgood] with ω hω
    change (originExitWindow 1 (ηL ω) ∈ S) = (g (O (Φ ω)) ∈ S)
    rw [show g (O (Φ ω)) = originExitWindow 1 (ηL ω) from
      originExitWindow_nonnegComplexCurve_stoppedPath hω.1 (hω.2 1)]
  have hsub : Φ ⁻¹' (T ∩ A) ≤ᵐ[P] ({ω | (exitTimeAfter (ηL ω) 0 0 1,
      realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} ∩
        {ω | ∃ w, ball w (min ηsize (1 / 2) * ε) ⊆ ηL ω '' Icc (exitTimeAfter (ηL ω) 0 0 1)
          (exitTimeAfter (ηL ω) 0 0 (1 + ε))} : Set Ω) := by
    filter_upwards [hgood] with ω hω hmem
    obtain ⟨hmT, hmA⟩ := hmem
    refine ⟨?_, exists_ball_subset_exitWindow_of_euclidean hω.1
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hε.1.le) hmA⟩
    change originExitWindow 1 (ηL ω) ∈ S
    rw [← originExitWindow_nonnegComplexCurve_stoppedPath hω.1 (hω.2 1)]
    exact hmT
  calc ENNReal.ofReal (min p (1 / 2)) * P {ω | (exitTimeAfter (ηL ω) 0 0 1,
          realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S}
      ≤ ENNReal.ofReal p * P {ω | (exitTimeAfter (ηL ω) 0 0 1,
          realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} := by
        gcongr
        exact min_le_left _ _
    _ = ENNReal.ofReal p * ν T := by rw [Measure.map_apply hm hT, measure_congr hSeq]
    _ ≤ ν (T ∩ A) := hENN
    _ = P (Φ ⁻¹' (T ∩ A)) := Measure.map_apply₀ hm.aemeasurable (hT.nullMeasurableSet.inter hA)
    _ ≤ _ := measure_mono_ae hsub

end Coupling

end LatticeProb.LQG
