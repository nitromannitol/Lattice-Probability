/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127B1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108R1
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatGreen
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs

/-!
# D127 N2: the dual Dirichlet norm is bounded by the killed-Green form (BP Lemma 1.38)

Packet P-127B of DEC-127 (§3, item N2). For a bounded open `U`, write
`B(a, b) := ∫∫ a(y) b(y') G_U(y, y') dy dy'` with `G_U = π ∫₀^∞ p_U` (`KilledHeat.killedGreen`).

* `killedGreenForm_eq_inner`: `B(a, b) = π ⟪K a, K b⟫` with `K = uKerL2 U (Ioi 0)` (the
  Chapman–Kolmogorov identity `inner_uKerL2`, S3D108R1); hence
* `killedGreenForm_psd` (`B(a, a) ≥ 0`) and `killedGreenForm_cs` (`B(a, b)² ≤ B(a, a) B(b, b)`);
* **`dualNormSq_le_killedGreen`**: for `ρ ≥ 0` bounded measurable vanishing off `U`, and given
  N1 (`∫ G_U(y, x) Δg(x) dx = −2π g(y)` for `g ∈ C_c^∞(U)`, `y ∈ U`; packet P-127A),
  `dualNormSq U (zeroSpace U) (ρ dx) ≤ B(ρ, ρ)`.

Source: Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*, arXiv:2404.16642,
§1.5, Lemma 1.38 (`literature/pdf/2404.16642.txt` l. 1659–1683): `∫ g ρ = ∫∫ G(x,y)(−Δg)(y) ρ(x)`,
then Cauchy–Schwarz. BP apply Cauchy–Schwarz to `∫ ∇g · ∇(G ρ)` (which needs the regularity of
`G ρ`, Lemma 1.37); following DEC-127 §3 N2 we apply it instead to the positive semidefinite form
`B` (positive by Chapman–Kolmogorov) and evaluate `B(−Δg, −Δg) = 2π ∫ (−Δg) g = 2π ∫ |∇g|²` with
N1 and Green's first identity (`QuantumZipper.K3.integral_norm_fderiv_sq_eq_neg_integral_mul_laplacian`).
The integrability bookkeeping repeats the proof of `inner_uKerL2` (S3D108R1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Laplacian
open scoped NNReal ENNReal RealInnerProductSpace Real

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-- the killed-Green bilinear form `B(a, b) = ∫∫ a(y) b(y') G_U(y, y')` -/
def killedGreenForm (U : Set ℂ) (a b : ℂ → ℝ) : ℝ :=
  ∫ q : ℂ × ℂ, a q.1 * b q.2 * killedGreen U q.1 q.2

/-- `B(a, b) = π ⟪K a, K b⟫` -/
theorem killedGreenForm_eq_inner (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) {C : ℝ} (haC : ∀ z, |a z| ≤ C)
    (hbC : ∀ z, |b z| ≤ C) (hai : Integrable a) (hbi : Integrable b) :
    killedGreenForm U a b = π * ⟪uKerL2 U (Ioi 0) a, uKerL2 U (Ioi 0) b⟫ := by
  rw [inner_uKerL2 hU hR hUR measurableSet_Ioi subset_rfl ha hb haC hbC hai hbi,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only [killedGreen]
  ring

theorem killedGreenForm_psd (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a : ℂ → ℝ} (ha : Measurable a) {C : ℝ} (haC : ∀ z, |a z| ≤ C) (hai : Integrable a) :
    0 ≤ killedGreenForm U a a := by
  rw [killedGreenForm_eq_inner hU hR hUR ha ha haC haC hai hai]
  exact mul_nonneg Real.pi_pos.le real_inner_self_nonneg

/-- **Cauchy–Schwarz for the killed-Green form** -/
theorem killedGreenForm_cs (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) {C : ℝ} (haC : ∀ z, |a z| ≤ C)
    (hbC : ∀ z, |b z| ≤ C) (hai : Integrable a) (hbi : Integrable b) :
    killedGreenForm U a b ^ 2 ≤ killedGreenForm U a a * killedGreenForm U b b := by
  rw [killedGreenForm_eq_inner hU hR hUR ha hb haC hbC hai hbi,
    killedGreenForm_eq_inner hU hR hUR ha ha haC haC hai hai,
    killedGreenForm_eq_inner hU hR hUR hb hb hbC hbC hbi hbi]
  have := real_inner_mul_inner_self_le (uKerL2 U (Ioi 0) a) (uKerL2 U (Ioi 0) b)
  have hπ : 0 ≤ π ^ 2 := sq_nonneg _
  calc (π * ⟪uKerL2 U (Ioi 0) a, uKerL2 U (Ioi 0) b⟫) ^ 2
      = π ^ 2 * (⟪uKerL2 U (Ioi 0) a, uKerL2 U (Ioi 0) b⟫ *
          ⟪uKerL2 U (Ioi 0) a, uKerL2 U (Ioi 0) b⟫) := by ring
    _ ≤ π ^ 2 * (⟪uKerL2 U (Ioi 0) a, uKerL2 U (Ioi 0) a⟫ *
          ⟪uKerL2 U (Ioi 0) b, uKerL2 U (Ioi 0) b⟫) := mul_le_mul_of_nonneg_left this hπ
    _ = _ := by ring

/-- the integrand of `B(a, b)` is integrable on `ℂ × ℂ` (as in the proof of `inner_uKerL2`) -/
theorem integrable_killedGreenForm (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) {C : ℝ}
    (hbC : ∀ z, |b z| ≤ C) (hai : Integrable a) (hbi : Integrable b) :
    Integrable (fun q : ℂ × ℂ => a q.1 * b q.2 * killedGreen U q.1 q.2) := by
  set I : Set ℝ := Ioi 0
  have hI : MeasurableSet I := measurableSet_Ioi
  set F : (ℝ × ℂ) → (ℂ × ℂ) → ℝ := fun p q =>
    (a q.1 * wndKernel U I q.1 p) * (b q.2 * wndKernel U I q.2 p) with hFdef
  have hFm : Measurable (Function.uncurry F) :=
    ((ha.comp (measurable_fst.comp measurable_snd)).mul (measurable_wndKernel_comp hU hI
      (measurable_fst.comp measurable_snd) measurable_fst)).mul
      ((hb.comp (measurable_snd.comp measurable_snd)).mul (measurable_wndKernel_comp hU hI
      (measurable_snd.comp measurable_snd) measurable_fst))
  have hFi : Integrable (Function.uncurry F) ((volume : Measure (ℝ × ℂ)).prod
      (volume : Measure (ℂ × ℂ))) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have ht := lintegral_triple_lt_top hU hR hUR hI subset_rfl ha.enorm hb.enorm
      hai.hasFiniteIntegral.ne (enorm_le_ofReal hbC) hbi.hasFiniteIntegral.ne
    rw [Measure.volume_eq_prod (α := ℝ × ℂ) (β := ℂ × ℂ)] at ht
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) ht
    simp only [Function.uncurry, hFdef, enorm_mul,
      Real.enorm_of_nonneg (wndKernel_nonneg _ _ _ _)]
    ring
  have h2 := (hFi.integral_prod_right).const_mul π
  refine h2.congr (Eventually.of_forall fun q => ?_)
  simp only [hFdef, killedGreen, Function.uncurry]
  rw [← integral_wnd_mul hU hI subset_rfl, ← integral_const_mul, ← integral_const_mul,
    ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun p => by ring)

/-- the iterated form of `B(a, b)` -/
theorem killedGreenForm_eq_iter (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) {C : ℝ}
    (hbC : ∀ z, |b z| ≤ C) (hai : Integrable a) (hbi : Integrable b) :
    killedGreenForm U a b = ∫ y, a y * ∫ x, killedGreen U y x * b x := by
  unfold killedGreenForm
  rw [Measure.volume_eq_prod (α := ℂ) (β := ℂ),
    integral_prod _ (by
      simpa [Measure.volume_eq_prod] using integrable_killedGreenForm hU hR hUR ha hb hbC hai hbi)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

/-! ## The test function `−Δg` -/

lemma contDiff_laplacian_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    Continuous (Δ g) :=
  QuantumZipper.K3.continuous_laplacian_K3 (hg.of_le (by simp))

lemma laplacian_eq_zero_of_notMem_tsupport {g : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport g) :
    Δ g z = 0 := by
  have h : g =ᶠ[nhds z] fun _ => (0 : ℝ) := by
    have : (tsupport g)ᶜ ∈ nhds z := (isClosed_tsupport g).isOpen_compl.mem_nhds hz
    filter_upwards [this] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  rw [(InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds]
  simp

/-- the facts about `a = −Δg` used below -/
lemma negLap_props {g : ℂ → ℝ} (hg : g ∈ QuantumZipper.zeroSpace U) :
    Measurable (fun x => -Δ g x) ∧ (∃ C, ∀ z, |-Δ g z| ≤ C) ∧
      Integrable (fun x => -Δ g x) ∧ ∀ z, z ∉ U → -Δ g z = 0 := by
  obtain ⟨hs, hc, hsub⟩ := hg
  have hcont : Continuous (fun x => -Δ g x) := (contDiff_laplacian_of_smooth hs).neg
  have hcs : HasCompactSupport (fun x => -Δ g x) :=
    (QuantumZipper.K3.hasCompactSupport_laplacian_K3 hc).neg
  refine ⟨hcont.measurable, ?_, hcont.integrable_of_hasCompactSupport hcs, fun z hz => ?_⟩
  · obtain ⟨C, hC⟩ := hcont.norm.bddAbove_range_of_hasCompactSupport hcs.norm
    exact ⟨C, fun z => by simpa [Real.norm_eq_abs] using hC ⟨z, rfl⟩⟩
  · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hz (hsub h)), neg_zero]

/-- the Dirichlet energy of `g ∈ C_c^∞(U)` as a whole-plane integral -/
lemma dirichletEnergyOn_eq {g : ℂ → ℝ} (hg : g ∈ QuantumZipper.zeroSpace U) :
    QuantumZipper.dirichletEnergyOn U g = (2 * π)⁻¹ * ∫ z, g z * (-Δ g z) := by
  obtain ⟨hs, hc, hsub⟩ := hg
  unfold QuantumZipper.dirichletEnergyOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_),
    QuantumZipper.K3.integral_norm_fderiv_sq_eq_neg_integral_mul_laplacian
      (hs.of_le (by simp)) hc, ← integral_neg]
  · simp only [mul_neg]
  · have : z ∉ Function.support (fderiv ℝ g) := fun h => hz (hsub (support_fderiv_subset ℝ h))
    rw [Function.notMem_support.1 this]; simp

/-! ## N2: the upper bound -/

/-- a bounded measurable function vanishing off a bounded set is integrable -/
lemma integrable_of_bdd_of_vanish (hUR : U ⊆ Metric.ball c R) {ρ : ℂ → ℝ} (hρ : Measurable ρ)
    {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) (hρU : ∀ z, z ∉ U → ρ z = 0) : Integrable ρ := by
  have hb : IntegrableOn ρ (Metric.ball c R) :=
    Measure.integrableOn_of_bounded (M := C) measure_ball_lt_top.ne hρ.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hC z)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hb
  intro z hz
  by_contra h
  exact hz (hρU z fun h' => h (hUR h'))

/-- N1 integrated against a density vanishing off `U` -/
lemma integral_mul_green_negLap (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {g : ℂ → ℝ} (hg : g ∈ QuantumZipper.zeroSpace U) {a : ℂ → ℝ} (haU : ∀ z, z ∉ U → a z = 0) :
    ∫ y, a y * ∫ x, killedGreen U y x * (-Δ g x) = 2 * π * ∫ y, a y * g y := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ U
  · simp only [mul_neg, integral_neg, hN1 g hg y hy]
    ring
  · simp [haU y hy]

/-- `B(ρ, −Δg) = 2π ∫ ρ g` (BP Lemma 1.38, first display) -/
theorem killedGreenForm_negLap_right (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {ρ : ℂ → ℝ} (hρ : Measurable ρ) (hρi : Integrable ρ) (hρU : ∀ z, z ∉ U → ρ z = 0)
    {g : ℂ → ℝ} (hg : g ∈ QuantumZipper.zeroSpace U) :
    killedGreenForm U ρ (fun x => -Δ g x) = 2 * π * ∫ y, ρ y * g y := by
  obtain ⟨am, ⟨C', hC'⟩, ai, -⟩ := negLap_props hg
  rw [killedGreenForm_eq_iter hU hR hUR hρ am hC' hρi ai,
    integral_mul_green_negLap hN1 hg hρU]

/-- `B(−Δg, −Δg) = (2π)² (g, g)_∇` (N1 and Green's first identity) -/
theorem killedGreenForm_negLap_self (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {g : ℂ → ℝ} (hg : g ∈ QuantumZipper.zeroSpace U) :
    killedGreenForm U (fun x => -Δ g x) (fun x => -Δ g x) =
      (2 * π) ^ 2 * QuantumZipper.dirichletEnergyOn U g := by
  obtain ⟨am, ⟨C', hC'⟩, ai, aU⟩ := negLap_props hg
  rw [killedGreenForm_eq_iter hU hR hUR am am hC' ai ai,
    integral_mul_green_negLap hN1 hg aU, dirichletEnergyOn_eq hg]
  have hπ : (2 * π) ≠ 0 := by positivity
  have e : ∫ y, -Δ g y * g y = ∫ z, g z * -Δ g z :=
    integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  rw [e]
  field_simp

/-- **D127 N2 (BP Lemma 1.38)**: for `ρ ≥ 0` bounded measurable vanishing off the bounded open
set `U`, given N1, `dualNormSq U (zeroSpace U) (ρ dx) ≤ ∫∫ ρ ρ G_U` -/
theorem dualNormSq_le_killedGreen (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρU : ∀ z, z ∉ U → ρ z = 0) :
    QuantumZipper.dualNormSq U (QuantumZipper.zeroSpace U)
        (volume.withDensity fun z => ENNReal.ofReal (ρ z)) ≤
      ENNReal.ofReal (killedGreenForm U ρ ρ) := by
  have hρi := integrable_of_bdd_of_vanish hUR hρ hC hρU
  refine iSup₂_le fun g hg => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨hgZ, hE⟩ := hg
  have hint : ∫ x, g x ∂(volume.withDensity fun z => ENNReal.ofReal (ρ z)) =
      ∫ y, ρ y * g y := by
    rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [ENNReal.toReal_ofReal (hρ0 y), smul_eq_mul]
  obtain ⟨am, ⟨C', hC'⟩, ai, -⟩ := negLap_props hgZ
  have hcs := killedGreenForm_cs hU hR hUR hρ am (C := max C C')
    (fun z => (hC z).trans (le_max_left _ _)) (fun z => (hC' z).trans (le_max_right _ _)) hρi ai
  rw [killedGreenForm_negLap_right hU hR hUR hN1 hρ hρi hρU hgZ,
    killedGreenForm_negLap_self hU hR hUR hN1 hgZ] at hcs
  rw [hint, div_le_iff₀ hE]
  have h4 : 0 < (2 * π) ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ h4
  calc (2 * π) ^ 2 * (∫ y, ρ y * g y) ^ 2 = (2 * π * ∫ y, ρ y * g y) ^ 2 := by ring
    _ ≤ _ := hcs
    _ = _ := by ring

lemma ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]

end LQGMetric.CONF.ZBM
