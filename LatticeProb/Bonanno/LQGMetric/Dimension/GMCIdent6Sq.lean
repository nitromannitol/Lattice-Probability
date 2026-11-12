/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent6Sq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent6Grid
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Cov

/-!
# Uniform moments of the band integral over a square (P2-GMCID6)

* `lintegral_cell0_eq` : `∫_{[0,1)²} G = ∫_{t ∈ [0,1)²} ∑_{i ∈ grid j} 4^{-j} G(cellMap j i t) dt`
  (the level-`j` cells partition `[0,1)²`);
* **`lintegral_square_rpow_le`** : for `q < 0` or `q > 1`, if the reference family `Z`
  (`γ²`-log-correlated) has `E gM_j(Z_j)^q ≤ C₀` for all `j`, then
  `E (∫_{[0,1)²} f_n(a + L y) dy)^q ≤ e^{q(q−1)(γ²(log 4 + 1) + c)/2} C₀` for every
  `m ≤ n`, `a`, `L > 0` with `2^{-m} ≤ 4L` (`f_n = fineDens`): Jensen in the offset `t`,
  Tonelli, and the Kahane step `lintegral_gridSum_rpow_le` at a level `j` with `2^{-j} ≤ 2^{-n}/L`.
  This is the route of `uniform_moment_areaApprox_sqIn` (GMCMomentPos2Fin).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Finset
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent6

open WhiteNoise DGMC GMCIdent GMCIdent4 GMCIdent5

lemma mem_cell0_of_mem_cell {j : ℕ} {i : ℕ × ℕ} (hi : i ∈ grid j) {z : ℂ} (hz : z ∈ cell j i) :
    z ∈ cell0 := by
  rw [mem_grid] at hi
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have a1 : (i.1 : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast hi.1
  have a2 : (i.2 : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast hi.2
  have b1 : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
  have b2 : (0 : ℝ) ≤ i.2 := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

lemma eq_cellIdx_of_mem_cell {j : ℕ} {i : ℕ × ℕ} {z : ℂ} (hz : z ∈ cell j i) : i = cellIdx j z := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have b1 : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
  have b2 : (0 : ℝ) ≤ i.2 := Nat.cast_nonneg _
  refine Prod.ext ?_ ?_ <;> simp only [cellIdx]
  · exact ((Nat.floor_eq_iff (by linarith)).2 ⟨h1, h2⟩).symm
  · exact ((Nat.floor_eq_iff (by linarith)).2 ⟨h3, h4⟩).symm

lemma cellIdx_mem_grid {j : ℕ} {z : ℂ} (hz : z ∈ cell0) : cellIdx j z ∈ grid j := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  rw [mem_grid]
  constructor
  · refine (Nat.floor_lt (by positivity)).2 ?_
    push_cast; nlinarith
  · refine (Nat.floor_lt (by positivity)).2 ?_
    push_cast; nlinarith

lemma indicator_cell0_eq_sum (G : ℂ → ℝ≥0∞) (j : ℕ) (z : ℂ) :
    cell0.indicator G z = ∑ i ∈ grid j, (cell j i).indicator G z := by
  by_cases hz : z ∈ cell0
  · rw [indicator_of_mem hz, Finset.sum_eq_single (cellIdx j z)]
    · exact (indicator_of_mem (mem_cell_cellIdx j hz.1 hz.2.2.1) G).symm
    · intro i _ hi
      exact indicator_of_notMem (fun h => hi (eq_cellIdx_of_mem_cell h)) G
    · intro h; exact absurd (cellIdx_mem_grid hz) h
  · rw [indicator_of_notMem hz]
    refine (Finset.sum_eq_zero fun i hi => indicator_of_notMem
      (fun h => hz (mem_cell0_of_mem_cell hi h)) G).symm

/-- **averaged Riemann sums**: `∫_{[0,1)²} G = ∫_{t ∈ [0,1)²} ∑_i 4^{-j} G(cellMap j i t)` -/
lemma lintegral_cell0_eq (G : ℂ → ℝ≥0∞) (hG : Measurable G) (j : ℕ) :
    ∫⁻ y in cell0, G y = ∫⁻ t in cell0, ∑ i ∈ grid j,
      ENNReal.ofReal ((4 : ℝ)⁻¹ ^ j) * G (cellMap j i t) := by
  calc ∫⁻ y in cell0, G y = ∫⁻ y, cell0.indicator G y :=
        (lintegral_indicator measurableSet_cell0 G).symm
    _ = ∫⁻ z, ∑ i ∈ grid j, (cell j i).indicator G z :=
        lintegral_congr fun z => indicator_cell0_eq_sum G j z
    _ = ∑ i ∈ grid j, ∫⁻ z in cell j i, G z := by
        rw [lintegral_finset_sum _ fun i _ => hG.indicator (measurableSet_cell j i)]
        exact Finset.sum_congr rfl fun i _ => lintegral_indicator (measurableSet_cell j i) G
    _ = ∑ i ∈ grid j, ENNReal.ofReal ((4 : ℝ)⁻¹ ^ j) * ∫⁻ t in cell0, G (cellMap j i t) :=
        Finset.sum_congr rfl fun i _ => lintegral_cell G hG j i
    _ = _ := by
        symm
        have hm : ∀ i ∈ grid j, Measurable fun t => ENNReal.ofReal ((4 : ℝ)⁻¹ ^ j) *
            G (cellMap j i t) := fun i _ => (hG.comp (measurable_cellMap j i)).const_mul _
        rw [lintegral_finset_sum _ hm]
        exact Finset.sum_congr rfl fun i _ => lintegral_const_mul _ (hG.comp (measurable_cellMap j i))

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}
variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}

omit [MeasurableSpace Ω'] in
lemma fineDens_pos (γ : ℝ) (m n : ℕ) (z : ℂ) (ω : Ω') : 0 < fineDens W γ m n z ω := by
  unfold fineDens wnWeight; positivity

attribute [local irreducible] fineDens in
/-- **uniform moments of the band integral over a square** -/
theorem lintegral_square_rpow_le (hW : IsWhiteNoise P' W) (γ : ℝ) {Z : ℕ → ℂ → Ω₀ → ℝ} {c : ℝ}
    (hZ : LogCorr Z P₀ (γ ^ 2) c) {q : ℝ} (hq : q < 0 ∨ 1 < q) {C₀ : ℝ}
    (hC₀ : ∀ j, ∫ ω, gM (Z j) P₀ j (grid j) ω ^ q ∂P₀ ≤ C₀) {m n : ℕ} (hmn : m ≤ n) (a : ℂ)
    {L : ℝ} (hL : 0 < L) (hδL : (2 : ℝ)⁻¹ ^ m ≤ 4 * L) :
    ∫⁻ ω, (∫⁻ y in cell0, ENNReal.ofReal (fineDens W γ m n (a + (L : ℂ) * y) ω)) ^ q ∂P' ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) * C₀) := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < (2 : ℝ)⁻¹ ^ n / L by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have hq' : q ≤ 0 ∨ 1 ≤ q := hq.imp le_of_lt le_of_lt
  have hP := hW.isProbabilityMeasure
  have hmeas := measurable_fineDens' hW γ m n
  set G : Ω' → ℂ → ℝ≥0∞ := fun ω y => ENNReal.ofReal (fineDens W γ m n (a + (L : ℂ) * y) ω)
  have hGm : Measurable fun p : ℂ × Ω' => G p.2 p.1 :=
    ENNReal.measurable_ofReal.comp (hmeas.comp
      ((measurable_const.add (measurable_const.mul measurable_fst)).prodMk measurable_snd))
  set V : ℂ → Ω' → ℝ≥0∞ := fun t ω =>
    ∑ i ∈ grid j, ENNReal.ofReal ((4 : ℝ)⁻¹ ^ j) * G ω (cellMap j i t)
  have hV : ∀ ω, ∫⁻ y in cell0, G ω y = ∫⁻ t in cell0, V t ω := fun ω =>
    lintegral_cell0_eq (G ω) (hGm.comp (measurable_id.prodMk measurable_const)) j
  have hVm : Measurable fun p : ℂ × Ω' => V p.1 p.2 :=
    Finset.measurable_sum _ fun i _ => Measurable.const_mul (hGm.comp
      (((measurable_cellMap j i).comp measurable_fst).prodMk measurable_snd)) _
  have hpoint : ∀ t, ∫⁻ ω, V t ω ^ q ∂P' ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) * C₀) := by
    intro t
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_))
      ((lintegral_gridSum_rpow_le (a := a) hW γ hmn hL hδL hj.le t hZ hq').trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hC₀ j) (Real.exp_pos _).le)))
    have hpos : 0 < ∑ i : ↥(grid j), (4 : ℝ)⁻¹ ^ j * fineDens W γ m n (rPt a L j t i) ω := by
      haveI := DGMC.grid_nonempty j
      exact Finset.sum_pos (fun i _ => mul_pos (by positivity) (fineDens_pos γ m n _ ω))
        Finset.univ_nonempty
    rw [← ENNReal.ofReal_rpow_of_pos hpos]
    congr 1
    simp only [V, G, rPt]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (mul_pos (by positivity)
      (fineDens_pos γ m n _ ω)).le), ← Finset.sum_coe_sort (grid j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have hjen : ∀ ω, (∫⁻ t in cell0, V t ω) ^ q ≤ ∫⁻ t in cell0, V t ω ^ q := fun ω => by
    have hm : AEMeasurable (fun t => V t ω) (volume.restrict cell0) :=
      (hVm.comp (measurable_id.prodMk (measurable_const (a := ω)))).aemeasurable
    rcases hq with hq | hq
    · exact Neg3.rpow_lintegral_le_of_neg hm hq
    · exact rpow_lintegral_le hm hq
  calc ∫⁻ ω, (∫⁻ y in cell0, G ω y) ^ q ∂P'
      = ∫⁻ ω, (∫⁻ t in cell0, V t ω) ^ q ∂P' := lintegral_congr fun ω => by rw [hV ω]
    _ ≤ ∫⁻ ω, (∫⁻ t in cell0, V t ω ^ q) ∂P' := lintegral_mono hjen
    _ = ∫⁻ t in cell0, ∫⁻ ω, V t ω ^ q ∂P' :=
        lintegral_lintegral_swap ((hVm.comp (measurable_snd.prodMk measurable_fst)).pow_const
          q).aemeasurable
    _ ≤ ∫⁻ (_t : ℂ) in cell0, ENNReal.ofReal
          (Real.exp (q * (q - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) * C₀) :=
        lintegral_mono fun t => hpoint t
    _ = _ := by rw [setLIntegral_const, volume_cell0, mul_one]

end GMCIdent6
end LQGMetric
