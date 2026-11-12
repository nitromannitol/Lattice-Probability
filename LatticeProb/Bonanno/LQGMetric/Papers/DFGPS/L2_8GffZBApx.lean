/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffZBApx at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLoc
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLin
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Bdd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The zero-boundary analogue of DFGPS Lemma 2.1 at a fixed point (T:883–885, first step)

DFGPS (arXiv:1905.00380, T:883–885): "Lemma 2.1 remains true with `D_{h̊}^ε`, `D̂_{h̊}^ε` in
place of `D_h^ε`, `D̂_h^ε` … with the same proof (actually, the proof is simpler since one does
not need Lemma 2.2)." For the extended zero-boundary GFF on `V = (-1,2)²` the difference
`h̊*_ε(x) − ĥ̊*_ε(x)` is the pairing of `h̊` with the tail density
`(1 − ψ_ε(x − ·)) p_{ε²/2}(x, ·) 1_V`, which is `≤ 2 e^{−1/(8ε)} p_{ε²}(x, ·)`
(`heatKernel_half_le`, as in the GFF case T:726–733). Hence (`zbLoc_law`): for each `x` with
`B̄_{√ε}(x) ⊆ V`, `Y_{ε²}(x) − ĥ̊*_ε(x)` is a centred Gaussian of variance
`≤ (18/π) · 2e^{−1/(8ε)} · 4 · 2e^{−1/(8ε)} (2πε²)⁻¹` (variance bound `zbVar_sq_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open LFPP HeatSq Blueprint

/-- pointwise bound for the tail density -/
lemma abs_heat_sub_locTest_le {ε : ℝ} (hε : 0 < ε) {V : Set ℂ} (x w : ℂ)
    (hsupp : tsupport (locTest ε hε x : ℂ → ℝ) ⊆ V) :
    |V.indicator (fun w => heatKernel (ε ^ 2 / 2) x w) w - locTest ε hε x w| ≤
      2 * Real.exp (-(1 / (8 * ε))) * heatKernel (ε ^ 2) x w := by
  have hR : 0 ≤ 2 * Real.exp (-(1 / (8 * ε))) * heatKernel (ε ^ 2) x w :=
    mul_nonneg (by positivity) (heatKernel_nonneg _ (by positivity) _ _)
  by_cases hw : w ∈ V
  · rw [indicator_of_mem hw, locTest_apply' ε hε x w]
    have hp := heatKernel_nonneg (ε ^ 2 / 2) (by positivity) x w
    have hb0 := locBump_nonneg ε hε (x - w)
    have hb1 := locBump_le_one ε hε (x - w)
    by_cases hn : ‖x - w‖ ≤ Real.sqrt ε / 2
    · rw [locBump_eq_one ε hε hn, one_mul, sub_self, abs_zero]; exact hR
    · have hk := heatKernel_half_le hε x w (le_of_lt (not_le.1 hn))
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
  · have h0 : locTest ε hε x w = 0 := image_eq_zero_of_notMem_tsupport fun h' => hw (hsupp h')
    rw [indicator_of_notMem hw, h0, sub_zero, abs_zero]; exact hR

/-- **Law of `Y_{ε²}(x) − ĥ̊*_ε(x)`** (`V = (-1,2)²`, Markov-coupling data `Xh`, `hz`). -/
theorem zbLoc_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P)
    {hz : Ω → DistC}
    (hlink : ∀ φ : TestOn (sqOpens (-1) 3), Xh φ.toBddOn =ᵐ[P]
      fun ω => restrictTo (sqOpens (-1) 3) (hz ω) φ)
    {Y : ℂ → Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hY : IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (ε ^ 2 / 2) x)) Y P) {x : ℂ}
    (hball : closedBall x (Real.sqrt ε) ⊆ sqOpen (-1) 3) :
    ∃ v : ℝ≥0, P.map (fun ω => Y x ω - locMollify ε hε (hz ω) x) = gaussianReal 0 v ∧
      (v : ℝ) ≤ 18 / Real.pi * ((2 * Real.exp (-(1 / (8 * ε)))) *
        (4 * (2 * Real.exp (-(1 / (8 * ε))) * (2 * Real.pi * ε ^ 2)⁻¹))) := by
  set V := sqOpens (-1) 3
  have hsupp : tsupport (locTest ε hε x : ℂ → ℝ) ⊆ (V : Set ℂ) :=
    (tsupport_locTest_subset ε hε x).trans hball
  set heat : BddOn (sqOpen (-1) 3) := heatBdd (sqOpens (-1) 3) (ε ^ 2 / 2) x
  set loc : BddOn (sqOpen (-1) 3) := (testOnOf V (locTest ε hε x) hsupp).toBddOn
  have hs : 0 < ε ^ 2 / 2 := by positivity
  have hheat : heat.1 = (sqOpen (-1) 3).indicator (fun w => heatKernel (ε ^ 2 / 2) x w) :=
    heatBdd_val (measurableSet_sqOpen (-1) 3) hs x
  have hloc : ∀ w, loc.1 w = locTest ε hε x w := fun w => rfl
  have hpt : ∀ w, |heat.1 w - loc.1 w| ≤ 2 * Real.exp (-(1 / (8 * ε))) * heatKernel (ε ^ 2) x w :=
    fun w => by rw [hheat, hloc]; exact abs_heat_sub_locTest_le hε x w hsupp
  set C : ℝ := 2 * Real.exp (-(1 / (8 * ε))) * (2 * Real.pi * ε ^ 2)⁻¹
  have hC : ∀ w, |heat.1 w - loc.1 w| ≤ C := fun w =>
    (hpt w).trans (mul_le_mul_of_nonneg_left
      (KilledHeat.heatKernel_le_inv _ (by positivity) x w) (by positivity))
  have hI : ∫ w, |heat.1 w - loc.1 w| ≤ 2 * Real.exp (-(1 / (8 * ε))) := by
    have hi := (integrable_heatKernel (ε ^ 2) (by positivity) x).const_mul
      (2 * Real.exp (-(1 / (8 * ε))))
    calc ∫ w, |heat.1 w - loc.1 w| ≤ ∫ w, 2 * Real.exp (-(1 / (8 * ε))) * heatKernel (ε ^ 2) x w :=
          integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _) hi (ae_of_all _ hpt)
      _ = 2 * Real.exp (-(1 / (8 * ε))) := by
          rw [integral_const_mul, integral_heatKernel _ (by positivity), mul_one]
  have hae : (fun ω => Y x ω - locMollify ε hε (hz ω) x) =ᵐ[P]
      fun ω => Xh heat ω - Xh loc ω := by
    filter_upwards [hY.2.2 x, hlink (testOnOf V (locTest ε hε x) hsupp)] with ω h1 h2
    rw [h1]
    congr 1
    rw [h2]
    exact (restrictTo_testOnOf V (hz ω) _ hsupp).symm
  refine ⟨_, (Measure.map_congr hae).trans (map_sub_zbExt hX heat loc), ?_⟩
  rw [Real.coe_toNNReal']
  refine max_le ?_ (by positivity)
  refine (zbVar_sq_le (by norm_num : (0 : ℝ) < 3) heat loc hC).trans ?_
  rw [integral_mul_const]
  have h18 : 2 * (3 : ℝ) ^ 2 / Real.pi = 18 / Real.pi := by ring
  rw [h18]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right hI (by positivity)

/-- the tail density `p_{ε²/2}(x − ·) 1_V − ψ_ε(x − ·) p_{ε²/2}(x, ·)` on `V = (-1,2)²` -/
def zbTail {ε : ℝ} (hε : 0 < ε) (x : ℂ)
    (hsupp : tsupport (locTest ε hε x : ℂ → ℝ) ⊆ (sqOpens (-1) 3 : Set ℂ)) :
    BddOn (sqOpen (-1) 3) :=
  bddSub (heatBdd (sqOpens (-1) 3) (ε ^ 2 / 2) x)
    (testOnOf (sqOpens (-1) 3) (locTest ε hε x) hsupp).toBddOn

/-- **Pairing form**: `Y_{ε²}(x) − ĥ̊*_ε(x) = Xh(tail density)` a.s. -/
theorem zbLoc_ae_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P)
    {hz : Ω → DistC}
    (hlink : ∀ φ : TestOn (sqOpens (-1) 3), Xh φ.toBddOn =ᵐ[P]
      fun ω => restrictTo (sqOpens (-1) 3) (hz ω) φ)
    {Y : ℂ → Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hY : IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (ε ^ 2 / 2) x)) Y P) (x : ℂ)
    (hsupp : tsupport (locTest ε hε x : ℂ → ℝ) ⊆ (sqOpens (-1) 3 : Set ℂ)) :
    (fun ω => Y x ω - locMollify ε hε (hz ω) x) =ᵐ[P] Xh (zbTail hε x hsupp) := by
  filter_upwards [hY.2.2 x, hlink (testOnOf (sqOpens (-1) 3) (locTest ε hε x) hsupp),
    zbExt_sub_ae (by norm_num : (0 : ℝ) < 3) hX (heatBdd (sqOpens (-1) 3) (ε ^ 2 / 2) x)
      (testOnOf (sqOpens (-1) 3) (locTest ε hε x) hsupp).toBddOn] with ω h1 h2 h3
  rw [h1, show locMollify ε hε (hz ω) x = Xh (testOnOf (sqOpens (-1) 3) (locTest ε hε x)
    hsupp).toBddOn ω by rw [h2]; exact (restrictTo_testOnOf _ (hz ω) _ hsupp).symm]
  exact h3

end LQGMetric.DFGPS
