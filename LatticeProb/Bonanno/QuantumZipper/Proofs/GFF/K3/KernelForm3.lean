/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.KernelForm3 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm2

/-!
# GFF-K3 §3, node C2: the kernel form for bounded densities touching `∂D`

Blueprint `blueprint/GFF_K3_BLUEPRINT.md` §3 node **C2**, `dualCov_conformal_withDensity`, first
the dual norm (`dualNormSq_conformal_withDensity`).  The density `g` may touch `∂D`, where the
pushforward along `φ` need not be admissible.  Route (the blueprint's): exhaust `D` by the compact
sets `exhaust D n`; on `g·1_{exhaust D n}` the pushforward has bounded density with compact
support in `ℍ`, so C2 (`KernelForm.lean`) applies; the kernel side converges by monotone
convergence (`G_ℍ ≥ 0` on `ℍ × ℍ`); the dual-norm side converges because the dual norm of the
remainder `g·1_{D \ exhaust D n}` is at most its Green energy on `ℍ` (F6, H7), which tends to `0`
by dominated convergence, and the dual norm satisfies the triangle inequality.

Hypothesis `D ⊆ H` (not in the blueprint's C2 signature): it is used for the remainder bound
(F6 domain monotonicity into `ℍ`), exactly as in the blueprint's proof sketch ("`≤ B`-energy
`→ 0` (F6, H3)"); every application (Loewner domains `H \ K_t` and their bubbles) has `D ⊆ ℍ`.
-/

noncomputable section

open MeasureTheory Set Function Filter Topology
open Classical
open scoped ENNReal

namespace QuantumZipper.K3

variable {φ : ℂ → ℂ} {D : Set ℂ}

lemma isFiniteMeasure_withDensity_bdd {g : ℂ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M < ⊤)
    (hgM : ∀ z, g z ≤ M) {R : ℝ} (hgR : ∀ z, z ∉ Metric.closedBall 0 R → g z = 0) :
    IsFiniteMeasure (volume.withDensity g) := by
  refine isFiniteMeasure_withDensity (ne_of_lt ?_)
  have hle : ∀ z, g z ≤ (Metric.closedBall (0 : ℂ) R).indicator (fun _ => M) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
    · rw [indicator_of_mem hz]; exact hgM z
    · rw [indicator_of_notMem hz, hgR z hz]
  calc ∫⁻ z, g z ≤ ∫⁻ z, (Metric.closedBall (0 : ℂ) R).indicator (fun _ => M) z := lintegral_mono hle
    _ = M * volume (Metric.closedBall (0 : ℂ) R) :=
        lintegral_indicator_const Metric.isClosed_closedBall.measurableSet M
    _ < ⊤ := ENNReal.mul_lt_top hM (isCompact_closedBall _ _).measure_lt_top

/-- **Node C2, dual norm of a bounded density touching `∂D`.** -/
theorem dualNormSq_conformal_withDensity (hφ : IsConformalOnto φ D H) (hDH : D ⊆ H)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) {M : ℝ≥0∞} (hM : M < ⊤) (hgM : ∀ z, g z ≤ M) {R : ℝ}
    (hgR : ∀ z, z ∉ Metric.closedBall 0 R → g z = 0) :
    dualNormSq D (zeroSpace D) (volume.withDensity g) =
      ∫⁻ p, D.indicator g p.1 * (D.indicator g p.2 * confKer φ D p)
        ∂((volume : Measure ℂ).prod volume) := by
  have hDm : MeasurableSet D := hφ.isOpen.measurableSet
  have hDc : Dᶜ.Nonempty := ⟨0, fun h0 => by
    have h := hDH h0
    change (0 : ℝ) < (0 : ℂ).im at h
    simp at h⟩
  have := isFiniteMeasure_withDensity_bdd hM hgM hgR
  set gh := D.indicator g with hghdef
  have hgh : Measurable gh := hg.indicator hDm
  rw [dualNormSq_zeroSpace_restrict hφ.isOpen, restrict_withDensity hDm,
    ← withDensity_indicator hDm]
  -- the pieces
  set gn : ℕ → ℂ → ℝ≥0∞ := fun n => (exhaust D n).indicator gh with hgndef
  set ln : ℕ → ℂ → ℝ≥0∞ := fun n => (exhaust D n)ᶜ.indicator gh with hlndef
  have hEm : ∀ n, MeasurableSet (exhaust D n) := fun n => (isCompact_exhaust D n).measurableSet
  have hgnm : ∀ n, Measurable (gn n) := fun n => hgh.indicator (hEm n)
  have hlnm : ∀ n, Measurable (ln n) := fun n => hgh.indicator (hEm n).compl
  have hghM : ∀ z, gh z ≤ M := fun z => (indicator_le_self _ _ z).trans (hgM z)
  have hghR : ∀ z, z ∉ D ∩ Metric.closedBall 0 R → gh z = 0 := by
    intro z hz
    by_cases hzD : z ∈ D
    · rw [hghdef, indicator_of_mem hzD]; exact hgR z fun h => hz ⟨hzD, h⟩
    · exact indicator_of_notMem hzD _
  have hgnM : ∀ n z, gn n z ≤ M := fun n z => (indicator_le_self _ _ z).trans (hghM z)
  have hlnM : ∀ n z, ln n z ≤ M := fun n z => (indicator_le_self _ _ z).trans (hghM z)
  have hgnR : ∀ n z, z ∉ D ∩ Metric.closedBall 0 R → gn n z = 0 := fun n z hz => by
    simp only [hgndef, indicator_apply_eq_zero]; exact fun _ => hghR z hz
  have hlnR : ∀ n z, z ∉ D ∩ Metric.closedBall 0 R → ln n z = 0 := fun n z hz => by
    simp only [hlndef, indicator_apply_eq_zero]; exact fun _ => hghR z hz
  have hAg := isAdmissibleDual_withDensity hφ hDH hgh hM hghM hghR
  have hAn := fun n => isAdmissibleDual_withDensity hφ hDH (hgnm n) hM (hgnM n) (hgnR n)
  have hBn := fun n => isAdmissibleDual_withDensity hφ hDH (hlnm n) hM (hlnM n) (hlnR n)
  have hsplit : ∀ n, volume.withDensity gh = volume.withDensity (gn n) + volume.withDensity (ln n) :=
    fun n => by rw [← withDensity_add_left (hgnm n), hgndef, hlndef, indicator_self_add_compl]
  -- eventual behaviour of the exhaustion
  have hev : ∀ x, ∀ᶠ n in atTop, gn n x = gh x := by
    intro x
    by_cases hx : x ∈ D
    · filter_upwards [eventually_mem_exhaust hφ.isOpen hDc hx] with n hn
      exact indicator_of_mem hn _
    · refine Eventually.of_forall fun n => ?_
      show (exhaust D n).indicator gh x = gh x
      rw [indicator_of_notMem (fun h => hx (exhaust_subset D n h)),
        hghdef, indicator_of_notMem hx]
  have hevl : ∀ x, ∀ᶠ n in atTop, ln n x = 0 := by
    intro x
    filter_upwards [hev x] with n hn
    have h2 : gn n x + ln n x = gh x := by
      simp only [hgndef, hlndef]; exact congrFun (indicator_self_add_compl _ gh) x
    by_cases hxe : x ∈ exhaust D n
    · exact indicator_of_notMem (Set.notMem_compl_iff.2 hxe) _
    · have h3 : ln n x = gh x := indicator_of_mem hxe _
      rw [h3, ← hn]
      exact indicator_of_notMem hxe _
  -- a n = kernel energy of gn n
  set J : (ℂ → ℝ≥0∞) → ℝ≥0∞ := fun h =>
    ∫⁻ p, h p.1 * (h p.2 * confKer φ D p) ∂((volume : Measure ℂ).prod volume) with hJdef
  have ha : ∀ n, dualNormSq D (zeroSpace D) (volume.withDensity (gn n)) = J (gn n) := by
    intro n
    have := (hAn n).1.1
    have hgnK : ∀ z ∉ exhaust D n, gn n z = 0 := fun z hz => indicator_of_notMem hz _
    rw [dualNormSq_conformal_eq_lintegral hφ (isAdmissibleH_map_withDensity hφ hDH (hgnm n) hM
      (hgnM n) (isCompact_exhaust D n) (exhaust_subset D n) hgnK),
      withDensity_restrict_eq_self hDm (fun z hz => hgnK z fun h => hz (exhaust_subset D n h))]
    exact lintegral_withDensity_kernel (hgnm n) (measurable_confKer hφ)
  -- monotone convergence of the kernel side
  have hJ : Tendsto (fun n => J (gn n)) atTop (𝓝 (J gh)) := by
    have hK := measurable_confKer hφ
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) ?_ ?_
    · have := hgnm n; exact (by fun_prop : Measurable fun p : ℂ × ℂ =>
        gn n p.1 * (gn n p.2 * confKer φ D p)).aemeasurable
    · refine Eventually.of_forall fun p n m hnm => ?_
      have hmono : ∀ x, gn n x ≤ gn m x := fun x =>
        indicator_le_indicator_of_subset (exhaust_mono D hnm) (fun _ => bot_le) x
      exact mul_le_mul' (hmono _) (mul_le_mul' (hmono _) le_rfl)
    · refine Eventually.of_forall fun p => tendsto_const_nhds.congr' ?_
      filter_upwards [hev p.1, hev p.2] with n h1 h2
      rw [h1, h2]
  -- the remainder tends to zero
  set JH : (ℂ → ℝ≥0∞) → ℝ≥0∞ := fun h =>
    ∫⁻ p, h p.1 * (h p.2 * ENNReal.ofReal (greenH p.1 p.2)) ∂((volume : Measure ℂ).prod volume)
    with hJHdef
  have hb : ∀ n, dualNormSq D (zeroSpace D) (volume.withDensity (ln n)) ≤ JH (ln n) := fun n =>
    (dualNormSq_zeroSpace_mono hφ.isOpen hDH).trans_eq
      (dualNormSq_H_withDensity (hlnm n) (hBn n).1)
  have hJH : Tendsto (fun n => JH (ln n)) atTop (𝓝 0) := by
    have hfin : JH gh ≠ ⊤ := by
      have h1 : JH gh = dualNormSq H (zeroSpace H) (volume.withDensity gh) :=
        (dualNormSq_H_withDensity hgh hAg.1).symm
      rw [h1]
      exact (isAdmissibleDual_H_of_isAdmissibleH hAg.1).2.2.ne
    have hlim := tendsto_lintegral_of_dominated_convergence
      (μ := (volume : Measure ℂ).prod volume) (f := fun _ => 0)
      (fun p : ℂ × ℂ => gh p.1 * (gh p.2 * ENNReal.ofReal (greenH p.1 p.2)))
      (F := fun n p => ln n p.1 * (ln n p.2 * ENNReal.ofReal (greenH p.1 p.2)))
      (fun n => by
        have := hlnm n
        have hG : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (greenH p.1 p.2) :=
          ENNReal.measurable_ofReal.comp measurable_greenH
        fun_prop)
      (fun n => Eventually.of_forall fun p =>
        mul_le_mul' (indicator_le_self _ _ _) (mul_le_mul' (indicator_le_self _ _ _) le_rfl))
      hfin
      (Eventually.of_forall fun p => tendsto_const_nhds.congr' (by
        filter_upwards [hevl p.1] with n hn
        simp [hn]))
    simpa using hlim
  have hbt : Tendsto (fun n => Real.sqrt (dualNormSq D (zeroSpace D)
      (volume.withDensity (ln n))).toReal) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => dualNormSq D (zeroSpace D) (volume.withDensity (ln n))) atTop
        (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hJH
          (fun n => bot_le) hb
    have h1 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0).sqrt
    simpa using h1
  -- the triangle inequality
  set c := dualNormSq D (zeroSpace D) (volume.withDensity gh) with hcdef
  have htri : ∀ n, |Real.sqrt c.toReal -
      Real.sqrt (dualNormSq D (zeroSpace D) (volume.withDensity (gn n))).toReal| ≤
      Real.sqrt (dualNormSq D (zeroSpace D) (volume.withDensity (ln n))).toReal := fun n => by
    rw [hcdef, hsplit n]; exact abs_sqrt_dualNormSq_add_sub_le (hAn n).2 (hBn n).2
  have hsq : Tendsto (fun n => Real.sqrt
      (dualNormSq D (zeroSpace D) (volume.withDensity (gn n))).toReal) atTop
      (𝓝 (Real.sqrt c.toReal)) := by
    have hd : Tendsto (fun n => Real.sqrt c.toReal - Real.sqrt
        (dualNormSq D (zeroSpace D) (volume.withDensity (gn n))).toReal) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact htri n) hbt
    have := (tendsto_const_nhds (x := Real.sqrt c.toReal)).sub hd
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  have hreal : Tendsto (fun n =>
      (dualNormSq D (zeroSpace D) (volume.withDensity (gn n))).toReal) atTop (𝓝 c.toReal) := by
    have := hsq.pow 2
    simp only [Real.sq_sqrt ENNReal.toReal_nonneg] at this
    exact this
  have hennr : Tendsto (fun n => dualNormSq D (zeroSpace D) (volume.withDensity (gn n))) atTop
      (𝓝 c) := by
    have := ENNReal.tendsto_ofReal hreal
    rw [ENNReal.ofReal_toReal hAg.2.2.2.ne] at this
    refine this.congr fun n => ?_
    exact ENNReal.ofReal_toReal (hAn n).2.2.2.ne
  have hJ' : Tendsto (fun n => J (gn n)) atTop (𝓝 c) := hennr.congr ha
  exact tendsto_nhds_unique hJ' hJ

end QuantumZipper.K3
