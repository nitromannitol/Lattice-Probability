/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.KernelForm2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm

/-!
# GFF-K3 §3, node C2: helpers for the density form

Helpers for `dualCov_conformal_withDensity` (`KernelForm3.lean`), blueprint
`blueprint/GFF_K3_BLUEPRINT.md` §3 node **C2**:

* `dualNormSq_conformal_eq_lintegral`: the kernel form of C2 as an `ℝ≥0∞` double integral;
* `lintegral_withDensity_kernel`: double integrals against `volume.withDensity h` as integrals
  over `ℂ × ℂ`;
* `isAdmissibleH_map_withDensity`: the pushforward along a conformal map of a bounded density
  with compact support in `D` is `IsAdmissibleH` (`Pushforward.log_dist_comparison`,
  `isAdmissibleH_map`);
* `isAdmissibleDual_withDensity`: bounded densities with bounded support in `D ⊆ ℍ` are
  admissible for the dual norm on `D` (domain monotonicity F6 and H3/H7);
* `abs_sqrt_dualNormSq_add_sub_le`: the triangle inequality for the dual norm (Riesz vectors);
* `exhaust D n`: an increasing exhaustion of `D` by compact sets.
-/

noncomputable section

open MeasureTheory Set Function Filter Topology
open Classical
open scoped ENNReal RealInnerProductSpace

namespace QuantumZipper.K3

variable {φ : ℂ → ℂ} {D : Set ℂ}

/-- The kernel `G_ℍ(φ x, φ y)` (with the measurable modification of `φ`) in `ℝ≥0∞`. -/
def confKer (φ : ℂ → ℂ) (D : Set ℂ) (p : ℂ × ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (greenH (confMod φ D p.1) (confMod φ D p.2))

lemma measurable_confKer (hφ : IsConformalOnto φ D H) : Measurable (confKer φ D) := by
  have hm := measurable_confMod hφ
  exact ENNReal.measurable_ofReal.comp
    (measurable_greenH.comp ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)))

/-- C2 as an `ℝ≥0∞` double integral. -/
lemma dualNormSq_conformal_eq_lintegral (hφ : IsConformalOnto φ D H) {m : Measure ℂ}
    [IsFiniteMeasure m] (hm' : IsAdmissibleH ((m.restrict D).map φ)) :
    dualNormSq D (zeroSpace D) m =
      ∫⁻ x, ∫⁻ y, confKer φ D (x, y) ∂(m.restrict D) ∂(m.restrict D) := by
  obtain ⟨h1, h2⟩ := kernelCov_eq_toReal hm' hm'
  rw [dualNormSq_conformal hφ m, dualNormSq_H_eq hm', h1, ENNReal.ofReal_toReal h2.ne,
    map_restrict_confMod hφ m]
  have hmeas := measurable_confMod hφ
  have hin : ∀ x, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂((m.restrict D).map (confMod φ D)) =
      ∫⁻ y, ENNReal.ofReal (greenH x (confMod φ D y)) ∂(m.restrict D) := fun x =>
    lintegral_map (ENNReal.measurable_ofReal.comp (measurable_greenH_left x)) hmeas
  simp_rw [hin]
  exact lintegral_map (Measurable.lintegral_prod_right'
    (f := fun p : ℂ × ℂ => ENNReal.ofReal (greenH p.1 (confMod φ D p.2)))
    (ENNReal.measurable_ofReal.comp
      (measurable_greenH.comp (measurable_fst.prodMk (hmeas.comp measurable_snd))))) hmeas

/-- Double integrals against a density, as integrals over `ℂ × ℂ`. -/
lemma lintegral_withDensity_kernel {h : ℂ → ℝ≥0∞} (hh : Measurable h) {k : ℂ × ℂ → ℝ≥0∞}
    (hk : Measurable k) :
    ∫⁻ x, ∫⁻ y, k (x, y) ∂(volume.withDensity h) ∂(volume.withDensity h) =
      ∫⁻ p, h p.1 * (h p.2 * k p) ∂((volume : Measure ℂ).prod volume) := by
  have hin : ∀ x, ∫⁻ y, k (x, y) ∂(volume.withDensity h) = ∫⁻ y, h y * k (x, y) := fun x => by
    exact lintegral_withDensity_eq_lintegral_mul _ hh (hk.comp measurable_prodMk_left)
  simp_rw [hin]
  have hm2 : Measurable fun p : ℂ × ℂ => h p.2 * k p := by fun_prop
  have hm3 : Measurable fun p : ℂ × ℂ => h p.1 * (h p.2 * k p) := by fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hh hm2.lintegral_prod_right',
    lintegral_prod _ hm3.aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [Pi.mul_apply]
  exact (lintegral_const_mul _ (hm2.comp measurable_prodMk_left)).symm

lemma withDensity_restrict_eq_self {h : ℂ → ℝ≥0∞} (hD : MeasurableSet D)
    (hhD : ∀ z ∉ D, h z = 0) : (volume.withDensity h).restrict D = volume.withDensity h := by
  rw [restrict_withDensity hD, ← withDensity_indicator hD,
    indicator_eq_self.2 (fun z hz => by_contra fun hzD => hz (hhD z hzD))]

lemma withDensity_compl_null {h : ℂ → ℝ≥0∞} {K : Set ℂ} (hK : MeasurableSet K)
    (hhK : ∀ z ∉ K, h z = 0) : volume.withDensity h Kᶜ = 0 := by
  rw [withDensity_apply _ hK.compl]
  exact (setLIntegral_congr_fun hK.compl (fun z hz => hhK z hz)).trans lintegral_zero

/-- The pushforward of a bounded density with compact support in `D`. -/
lemma isAdmissibleH_map_withDensity (hφ : IsConformalOnto φ D H) (hDH : D ⊆ H)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) {M : ℝ≥0∞} (hM : M < ⊤) (hhM : ∀ z, h z ≤ M)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D) (hhK : ∀ z ∉ K, h z = 0) :
    IsAdmissibleH (((volume.withDensity h).restrict D).map φ) := by
  rw [map_restrict_confMod hφ, withDensity_restrict_eq_self hφ.isOpen.measurableSet
    (fun z hz => hhK z fun hzK => hz (hKD hzK))]
  have hKH : K ⊆ Hbar := fun z hz => (show (0 : ℝ) < z.im from hDH (hKD hz)).le
  have hμ := isAdmissibleH_withDensity hh hM hhM hK hKH hhK
  obtain ⟨C, hC⟩ := log_dist_comparison hφ.isOpen hφ.diffOn hφ.injOn hφ.deriv_ne hK hKD
  refine isAdmissibleH_map hμ hK (withDensity_compl_null hK.measurableSet hhK)
    (measurable_confMod hφ) ?_ ?_ (Real.exp_pos (-C)) ?_
  · exact (hφ.diffOn.continuousOn.mono hKD).congr fun z hz => confMod_eqOn (hKD hz)
  · rintro _ ⟨z, hz, rfl⟩
    rw [confMod_eqOn (hKD hz)]
    have : φ z ∈ H := hφ.image_eq ▸ ⟨z, hKD hz, rfl⟩
    exact (show (0 : ℝ) < (φ z).im from this).le
  · intro x hx y hy
    rw [confMod_eqOn (hKD hx), confMod_eqOn (hKD hy)]
    rcases eq_or_ne x y with rfl | hxy
    · simp
    have h1 := hC x hx y hy hxy
    have hpos1 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hpos2 : 0 < ‖φ x - φ y‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 fun he => hxy (hφ.injOn (hKD hx) (hKD hy) he))
    have hle : Real.log ‖x - y‖ - C ≤ Real.log ‖φ x - φ y‖ := by linarith [(abs_le.1 h1).1]
    calc Real.exp (-C) * ‖x - y‖ = Real.exp (Real.log ‖x - y‖ - C) := by
          rw [Real.exp_sub, Real.exp_log hpos1, Real.exp_neg]; ring
      _ ≤ Real.exp (Real.log ‖φ x - φ y‖) := Real.exp_le_exp.2 hle
      _ = ‖φ x - φ y‖ := Real.exp_log hpos2

/-- Bounded densities with bounded support in `D ⊆ ℍ` are admissible on `ℍ` and on `D`. -/
lemma isAdmissibleDual_withDensity (hφ : IsConformalOnto φ D H) (hDH : D ⊆ H)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) {M : ℝ≥0∞} (hM : M < ⊤) (hhM : ∀ z, h z ≤ M) {R : ℝ}
    (hhR : ∀ z, z ∉ D ∩ Metric.closedBall 0 R → h z = 0) :
    IsAdmissibleH (volume.withDensity h) ∧ IsAdmissibleDual D (zeroSpace D) (volume.withDensity h) := by
  set K := Metric.closedBall (0 : ℂ) R ∩ closure D
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right isClosed_closure
  have hKD : K ⊆ closure D := inter_subset_right
  have hKH : K ⊆ Hbar := hKD.trans ((closure_mono hDH).trans closure_H_K3.subset)
  have hhK : ∀ z ∉ K, h z = 0 := fun z hz =>
    hhR z fun hz' => hz ⟨hz'.2, subset_closure hz'.1⟩
  have hμ := isAdmissibleH_withDensity hh hM hhM hK hKH hhK
  exact ⟨hμ, hμ.1, ⟨K, hK, hKD, withDensity_compl_null hK.measurableSet hhK⟩,
    (dualNormSq_zeroSpace_mono hφ.isOpen hDH).trans_lt
      (isAdmissibleDual_H_of_isAdmissibleH hμ).2.2⟩

/-- The dual norm on `ℍ` of a bounded density as an integral over `ℂ × ℂ`. -/
lemma dualNormSq_H_withDensity {h : ℂ → ℝ≥0∞} (hh : Measurable h)
    (hμ : IsAdmissibleH (volume.withDensity h)) :
    dualNormSq H (zeroSpace H) (volume.withDensity h) =
      ∫⁻ p, h p.1 * (h p.2 * ENNReal.ofReal (greenH p.1 p.2)) ∂((volume : Measure ℂ).prod volume) := by
  obtain ⟨h1, h2⟩ := kernelCov_eq_toReal hμ hμ
  rw [dualNormSq_H_eq hμ, h1, ENNReal.ofReal_toReal h2.ne]
  exact lintegral_withDensity_kernel hh (k := fun p => ENNReal.ofReal (greenH p.1 p.2))
    (ENNReal.measurable_ofReal.comp measurable_greenH)

/-- **Triangle inequality** for the dual norm. -/
lemma abs_sqrt_dualNormSq_add_sub_le {μ ν : Measure ℂ}
    (hμ : IsAdmissibleDual D (zeroSpace D) μ) (hν : IsAdmissibleDual D (zeroSpace D) ν) :
    |Real.sqrt (dualNormSq D (zeroSpace D) (μ + ν)).toReal -
        Real.sqrt (dualNormSq D (zeroSpace D) μ).toReal| ≤
      Real.sqrt (dualNormSq D (zeroSpace D) ν).toReal := by
  have hV := isDNSpace_zeroSpace D
  by_cases hpos : ∃ f ∈ zeroSpace D, 0 < dirichletEnergyOn D f
  · have := hμ.1; have := hν.1
    obtain ⟨-, ⟨K, hK, -, hKμ⟩, hfμ⟩ := id hμ
    obtain ⟨-, ⟨K', hK', -, hKν⟩, hfν⟩ := id hν
    rw [dualNormSq_eq_of_pairing hV (add_mem rieszVec_mem rieszVec_mem) (pair_add hV hμ hν hpos),
      dualNormSq_eq_norm_rieszVec hV ⟨K, hK, hKμ⟩ hfμ,
      dualNormSq_eq_norm_rieszVec hV ⟨K', hK', hKν⟩ hfν]
    simp only [ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have := abs_norm_sub_norm_le (rieszVec D (zeroSpace D) μ + rieszVec D (zeroSpace D) ν)
      (rieszVec D (zeroSpace D) μ)
    rwa [add_sub_cancel_left] at this
  · rw [dualNormSq_eq_zero_of_nopos hpos, dualNormSq_eq_zero_of_nopos hpos,
      dualNormSq_eq_zero_of_nopos hpos]
    simp

/-! ## A compact exhaustion -/

/-- `exhaust D n = {‖z‖ ≤ n, dist(z, Dᶜ) ≥ 1/(n+1)}`. -/
def exhaust (D : Set ℂ) (n : ℕ) : Set ℂ :=
  Metric.closedBall 0 n ∩ {z | ((n : ℝ) + 1)⁻¹ ≤ Metric.infDist z Dᶜ}

lemma isCompact_exhaust (D : Set ℂ) (n : ℕ) : IsCompact (exhaust D n) :=
  (isCompact_closedBall 0 _).inter_right
    (isClosed_le continuous_const (Metric.continuous_infDist_pt _))

lemma exhaust_subset (D : Set ℂ) (n : ℕ) : exhaust D n ⊆ D := by
  intro z hz
  by_contra hzD
  have h := hz.2
  simp only [mem_ofPred_eq, Metric.infDist_zero_of_mem (show z ∈ Dᶜ from hzD)] at h
  have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  linarith

lemma exhaust_mono (D : Set ℂ) : Monotone (exhaust D) := by
  intro n m hnm z hz
  refine ⟨Metric.closedBall_subset_closedBall (by exact_mod_cast hnm) hz.1, ?_⟩
  have h2 : ((n : ℝ) + 1)⁻¹ ≤ Metric.infDist z Dᶜ := hz.2
  show ((m : ℝ) + 1)⁻¹ ≤ _
  refine le_trans ?_ h2
  have : (n : ℝ) + 1 ≤ m + 1 := by exact_mod_cast Nat.succ_le_succ hnm
  exact inv_anti₀ (by positivity) this

lemma eventually_mem_exhaust (hD : IsOpen D) (hDc : Dᶜ.Nonempty) {z : ℂ} (hz : z ∈ D) :
    ∀ᶠ n in atTop, z ∈ exhaust D n := by
  have hd : 0 < Metric.infDist z Dᶜ :=
    (hD.isClosed_compl.notMem_iff_infDist_pos hDc).1 (fun h => h hz)
  obtain ⟨N₁, hN₁⟩ := exists_nat_one_div_lt hd
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge ‖z‖
  refine eventually_atTop.2 ⟨max N₁ N₂, fun n hn => ?_⟩
  refine exhaust_mono D hn ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hN₂.trans (by exact_mod_cast le_max_right N₁ N₂)
  · show ((max N₁ N₂ : ℕ) + 1 : ℝ)⁻¹ ≤ _
    refine le_trans ?_ hN₁.le
    rw [one_div]
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ (le_max_left N₁ N₂))

end QuantumZipper.K3
