/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepCirc at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepZB
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# GM Lemma 2.7: the circle average `h_{1+s}(z)` is determined by `h|_{ℂ∖U}`

GM l. 974–976 (`literature/src/1905.00383/uniqueness-final.tex`) use that `h_{1+s}(z)` is a
function of `h|_{ℂ∖U}` (the circle `∂B_{1+s}(z)` lies in `ℂ ∖ U`), so that the recentred field
`(h − h_{1+s}(z))|_{B_1(z)}` splits into the zero-boundary part and an `h|_{ℂ∖U}`-measurable part.
Here: `h_r(z)` is measurable for `σ(h|_{B_ε(∂B_r(z))})` for every `ε > 0`
(`measurable_circleAvg_fieldSigma`), hence for `σ(h|_K)` (`fieldSigmaClosed`) whenever
`∂B_r(z) ⊆ K`. Own elementary arguments (as `MeasurableAvg.measurable_circleAvg`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric

namespace LQGMetric.GM

open Blueprint

/-- `σ(h|_V) ≤ σ(h|_W)` for `V ≤ W` -/
theorem fieldSigma_mono {Ω : Type} (h : Ω → DistC) {V W : Opens ℂ} (hVW : V ≤ W) :
    fieldSigma h V ≤ fieldSigma h W := by
  let res : DistOn W → DistOn V := fun S => S.comp (testIncl V W)
  have hres : Measurable res := measurable_distOn_iff.2 fun φ =>
    measurable_distOn_apply (testIncl V W φ)
  have he : (fun ω => restrictTo V (h ω)) = res ∘ fun ω => restrictTo W (h ω) := by
    funext ω
    refine DFunLike.ext _ _ fun φ => ?_
    exact restrictTo_apply_testIncl hVW (h ω) φ
  unfold fieldSigma
  rw [he, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hres.comap_le

/-- a pairing with a test function supported in `V` is `σ(h|_V)`-measurable -/
theorem measurable_pair_fieldSigma {Ω : Type} (h : Ω → DistC) {V : Opens ℂ} (φ : TestC)
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ V) : Measurable[fieldSigma h V] fun ω => h ω φ := by
  let φV : TestOn V := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
  have e : (fun ω => h ω φ) = (fun S : DistOn V => S φV) ∘ fun ω => restrictTo V (h ω) := by
    funext ω
    show h ω φ = h ω (TestFunction.monoCLM ℝ φV)
    congr 1
    ext x
    simp [TestFunction.monoCLM_apply, φV]
  rw [e]
  exact (measurable_distOn_apply φV).comp (comap_measurable _)

/-- `h_r(z)` is measurable as soon as the pairings with the mollifiers centred on the circle are,
from some index on -/
theorem measurable_circleAvg_of {Ω : Type} [MeasurableSpace Ω] {h : Ω → DistC} (r : ℝ) (z : ℂ)
    (N : ℕ) (hpair : ∀ n, N ≤ n → ∀ θ : ℝ,
      Measurable fun ω => h ω (bumpTest n (circleMap z r θ))) :
    Measurable fun ω => circleAvg (h ω) r z := by
  have hn : ∀ n : ℕ, StronglyMeasurable fun ω =>
      Real.circleAverage (fun x => h ω (bumpTest (n + N) x)) z r := by
    intro n
    have hm : Measurable fun q : Ω × ℝ => h q.1 (bumpTest (n + N) (circleMap z r q.2)) := by
      have := measurable_uncurry_of_continuous_of_measurable
        (u := fun (θ : ℝ) (ω : Ω) => h ω (bumpTest (n + N) (circleMap z r θ)))
        (fun ω => (map_continuous (h ω)).comp
          ((continuous_bumpTest (n + N)).comp (continuous_circleMap z r)))
        (fun θ => hpair (n + N) (Nat.le_add_left N n) θ)
      exact this.comp measurable_swap
    have := (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).const_smul (2 * Real.pi)⁻¹
    convert this using 1
    funext ω
    simp only [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rfl
  have hlim := (StronglyMeasurable.limUnder (l := atTop) hn).measurable
  convert hlim using 1
  funext ω
  rw [circleAvg]
  unfold limUnder
  congr 1
  set F : ℕ → ℝ := fun n => Real.circleAverage (fun x => h ω (bumpTest n x)) z r
  show map F atTop = map (F ∘ fun n => n + N) atTop
  rw [← Filter.map_map, Filter.map_add_atTop_eq_nat]

lemma tsupport_bumpTest (n : ℕ) (x : ℂ) :
    tsupport (bumpTest n x : ℂ → ℝ) = closedBall x ((2 : ℝ)⁻¹ ^ n) :=
  ContDiffBump.tsupport_normed_eq (CircleAvg.bumpAt n x)

/-- **`h_r(z)` is `σ(h|_{B_ε(∂B_r(z))})`-measurable** -/
theorem measurable_circleAvg_fieldSigma {Ω : Type} (h : Ω → DistC) (r : ℝ) (z : ℂ) {ε : ℝ}
    (hε : 0 < ε) :
    Measurable[fieldSigma h (nbhdO ε (sphere z |r|))] fun ω => circleAvg (h ω) r z := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine @measurable_circleAvg_of Ω (fieldSigma h (nbhdO ε (sphere z |r|))) h r z N
    fun n hn θ => measurable_pair_fieldSigma h _ ?_
  rw [tsupport_bumpTest]
  intro y hy
  show y ∈ thickening ε (sphere z |r|)
  refine mem_thickening_iff.2 ⟨circleMap z r θ, circleMap_mem_sphere' z r θ, ?_⟩
  rw [mem_closedBall] at hy
  calc dist y (circleMap z r θ) ≤ (2 : ℝ)⁻¹ ^ n := hy
    _ ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ < ε := hN

/-- **`h_r(z)` is `σ(h|_K)`-measurable when `∂B_r(z) ⊆ K`** -/
theorem measurable_circleAvg_fieldSigmaClosed {Ω : Type} (h : Ω → DistC) (r : ℝ) (z : ℂ)
    {K : Set ℂ} (hK : sphere z |r| ⊆ K) :
    Measurable[fieldSigmaClosed h K] fun ω => circleAvg (h ω) r z := by
  intro s hs
  unfold fieldSigmaClosed
  rw [MeasurableSpace.measurableSet_iInf]
  intro ε
  rw [MeasurableSpace.measurableSet_iInf]
  intro hε
  exact fieldSigma_mono h (V := nbhdO ε (sphere z |r|)) (W := nbhdO ε K)
    (fun x hx => thickening_subset_of_subset ε hK hx) _
    (measurable_circleAvg_fieldSigma h r z hε hs)

end LQGMetric.GM
