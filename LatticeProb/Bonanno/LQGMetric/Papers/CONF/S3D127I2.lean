/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127I2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127I1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127H4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Cont
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentTilde

/-!
# (L4) of D127, part 2: the continuous coarse field `h_{t,∞}` at one level of the white-noise
filtration (packet P-127I, P2-HEATI)

CONF (arXiv:1905.00381, `confluence-final.tex`) C:722–731: `h^U = h_{0,t} + h_{t,∞}`, the coarse
part `h_{t,∞}` continuous ("easily checked using Kolmogorov", C:725–727) and measurable for the
white noise on the times `> t`.

* `exists_continuous_modification_of_holder_law`: Kolmogorov–Čentsov for a field with centred
  Gaussian increments of variance `≤ K|x − x'|^α` on any probability space (copy of the proof of
  `ZBM.exists_continuous_modification_of_kernel_holder`, S3D127G3, with the white-noise law of the
  increments replaced by a hypothesis), so that it can be run on a trimmed σ-algebra;
* `exists_coarseVersion`: the continuous version of `wnField W U (Ioi t)` measurable for any
  sub-σ-algebra carrying the `W (K^{(t,∞)}_x)` (as `exists_zbDistU_of_le`, S3D127H3, does for the
  full field);
* `measurable_mkC`: a continuous field with measurable coordinates is a measurable map into
  `C(ℂ, ℝ)`;
* `indep_comap_of_ae_eq`, `indep_distC_of_pairings`: independence of a random distribution from a
  σ-algebra through versions of its finite-dimensional pairings;
* `ae_integral_mul_coarse`: stochastic Fubini `∫ ψ h_{t,∞} = W(√π K^{(t,∞)}(ψ 1_U))` a.s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ

section KC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Kolmogorov–Čentsov with Hölder Gaussian increments** (copy of the proof of
`exists_continuous_modification_of_kernel_holder`, S3D127G3). -/
theorem exists_continuous_modification_of_holder_law (X : ℂ → Ω → ℝ)
    (hXm : ∀ x, Measurable (X x)) (v : ℂ → ℂ → ℝ≥0)
    (hlaw : ∀ x x', HasLaw (fun ω => X x ω - X x' ω) (gaussianReal 0 (v x x')) P)
    {K α : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hv : ∀ x x', (v x x' : ℝ) ≤ K * ‖x - x'‖ ^ α) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] X x := by
  set m : ℕ := ⌈3 / α⌉₊ + 1 with hm
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈3 / α⌉₊]
  have hma : (2 : ℝ) < m * α := by
    have h1 : 3 / α ≤ (⌈3 / α⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (3 : ℝ) ≤ ⌈3 / α⌉₊ * α := by rwa [div_le_iff₀ hα] at h1
    rw [hm]; push_cast; nlinarith
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q => X (finTwoToC q) with hZ
  have hZmeas : ∀ q, Measurable (Z q) := fun q => hXm _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧
      QuantumZipper.KolmG.MomentBoundG Z P (2 * m) (m * α) K R := by
    intro R
    refine ⟨(K * 2 ^ α) ^ m * QuantumZipper.gaussianAbsMoment (2 * m), by
      have := QuantumZipper.gaussianAbsMoment_nonneg (2 * m); positivity, fun q _ q' _ => ?_⟩
    have e := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hZmeas q).sub (hZmeas q')) m (hlaw (finTwoToC q) (finTwoToC q')).map_eq
    simp only [Pi.sub_apply] at e
    refine e.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have hn := norm_finTwoToC_sub_le q q'
    have hv' : ((v (finTwoToC q) (finTwoToC q') : ℝ)) ≤ K * 2 ^ α * ‖q - q'‖ ^ α := by
      refine (hv _ _).trans ?_
      rw [show K * 2 ^ α * ‖q - q'‖ ^ α = K * (2 * ‖q - q'‖) ^ α by
        rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]; ring]
      gcongr
    have hM := QuantumZipper.gaussianAbsMoment_nonneg (2 * m)
    have hv0 : 0 ≤ ((v (finTwoToC q) (finTwoToC q') : ℝ)) := NNReal.coe_nonneg _
    calc ((v (finTwoToC q) (finTwoToC q') : ℝ)) ^ m * QuantumZipper.gaussianAbsMoment (2 * m)
        ≤ (K * 2 ^ α * ‖q - q'‖ ^ α) ^ m * QuantumZipper.gaussianAbsMoment (2 * m) := by
          gcongr
      _ = (K * 2 ^ α) ^ m * QuantumZipper.gaussianAbsMoment (2 * m) * ‖q - q'‖ ^ ((m : ℝ) * α) := by
          rw [mul_pow, mul_comm (m : ℝ) α, Real.rpow_mul_natCast (norm_nonneg _)]; ring
  obtain ⟨Y₀, hYc₀, hYm₀, hYt⟩ := QuantumZipper.KolmN.exists_continuous_modification_N
    (d := 2) (P := P) (Z := Z) (fun q => (hZmeas _).aemeasurable)
    (p := 2 * m) (by positivity) (a := m * α) (by push_cast; linarith) hmom
  -- a measurable full-measure set on which the dyadic values converge to `Y₀`
  set B : Set Ω := {ω | ¬ ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
    (nhds (Y₀ q ω))} with hB
  set G : Set Ω := (toMeasurable P B)ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simp only [hG, mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable]
    exact ae_iff.mp hYt
  have hGt : ∀ ω ∈ G, ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
      (nhds (Y₀ q ω)) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  set Y : (Fin 2 → ℝ) → Ω → ℝ := fun q ω => G.indicator (fun ω => Y₀ q ω) ω with hY
  have hYc : ∀ ω, Continuous fun q => Y q ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hY, indicator_of_mem hω]; exact hYc₀ ω
    · simp only [hY, indicator_of_notMem hω]; exact continuous_const
  have hYmeas : ∀ q, Measurable (Y q) := by
    intro q
    refine measurable_of_tendsto_metrizable
      (f := fun n => G.indicator (Z (QuantumZipper.KolmD.rndD n q)))
      (fun n => (hZmeas _).indicator hGm) (tendsto_pi_nhds.mpr fun ω => ?_)
    by_cases hω : ω ∈ G
    · simp only [hY, indicator_of_mem hω]; exact hGt ω hω q
    · simp only [hY, indicator_of_notMem hω]; exact tendsto_const_nhds
  have hYm : ∀ q, (fun ω => Y q ω) =ᵐ[P] Z q := by
    intro q
    filter_upwards [hGae, hYm₀ q] with ω h1 h2
    simp only [hY, indicator_of_mem h1]
    exact h2
  let fromC : ℂ → Fin 2 → ℝ := fun z => ![z.re, z.im]
  have hfc : Continuous fromC := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_re
    · exact Complex.continuous_im
  have hft : ∀ z, finTwoToC (fromC z) = z := fun z => by
    apply Complex.ext <;> simp [finTwoToC, fromC]
  refine ⟨fun x ω => Y (fromC x) ω, fun ω => (hYc ω).comp hfc, fun x => hYmeas _, fun x => ?_⟩
  have := hYm (fromC x)
  simp only [hZ, hft] at this
  exact this

end KC

/-- a continuous field with measurable coordinates is a measurable map into `C(ℂ, ℝ)` -/
lemma measurable_mkC {α : Type*} {m : MeasurableSpace α} {Y : ℂ → α → ℝ}
    (hc : ∀ a, Continuous fun x => Y x a) (hm : ∀ x, Measurable (Y x)) :
    Measurable fun a => (⟨fun x => Y x a, hc a⟩ : C(ℂ, ℝ)) := by
  rw [measurable_iff_comap_le, ContinuousMap.measurableSpace_eq_iSup_comap_eval,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun x => ?_
  rw [MeasurableSpace.comap_comp]
  exact (hm x).comap_le

section Indep

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- independence passes to an a.e. equal random variable -/
lemma indep_comap_of_ae_eq {β : Type*} [MeasurableSpace β] {𝓖 : MeasurableSpace Ω}
    {f g : Ω → β} (hfg : f =ᵐ[P] g) (h : Indep 𝓖 (MeasurableSpace.comap g inferInstance) P) :
    Indep 𝓖 (MeasurableSpace.comap f inferInstance) P := by
  rw [Indep_iff] at h ⊢
  rintro a _ ha ⟨B, hB, rfl⟩
  have e : (f ⁻¹' B : Set Ω) =ᵐ[P] (g ⁻¹' B : Set Ω) := hfg.mono fun ω hω => by
    show (f ω ∈ B) = (g ω ∈ B)
    rw [hω]
  rw [measure_congr (ae_eq_set_inter (ae_eq_refl a) e), measure_congr e]
  exact h a _ ha ⟨B, hB, rfl⟩

/-- **independence of a random distribution from a σ-algebra**, through versions of its
finite-dimensional pairings -/
lemma indep_distC_of_pairings [IsProbabilityMeasure P] {𝓖 : MeasurableSpace Ω} (h𝓖 : 𝓖 ≤ mΩ)
    {R : Ω → DistC} (hR : Measurable[mΩ] R) {V : TestC → Ω → ℝ}
    (hRV : ∀ φ, (fun ω => R ω φ) =ᵐ[P] V φ)
    (hV : ∀ s : Finset TestC,
      Indep 𝓖 (MeasurableSpace.comap (fun ω (φ : s) => V φ ω) MeasurableSpace.pi) P) :
    Indep 𝓖 (MeasurableSpace.comap R inferInstance) P := by
  let _ : MeasurableSpace Ω := mΩ
  set F : Ω → TestC → ℝ := fun ω φ => R ω φ with hFdef
  have hF : Measurable F := measurable_pi_iff.2 fun φ => (measurable_distOn_apply φ).comp hR
  have hc : MeasurableSpace.comap R inferInstance = MeasurableSpace.comap F MeasurableSpace.pi := by
    show MeasurableSpace.comap R (MeasurableSpace.comap (fun (h : DistC) (φ : TestC) => h φ)
      MeasurableSpace.pi) = _
    rw [MeasurableSpace.comap_comp]; rfl
  rw [hc, ← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
  refine IndepSets.indep h𝓖 ?_ (@MeasurableSpace.isPiSystem_measurableSet Ω 𝓖)
    (isPiSystem_measurableCylinders.comap F) (@MeasurableSpace.generateFrom_measurableSet Ω 𝓖).symm
    rfl ?_
  · rw [← MeasurableSpace.comap_generateFrom, generateFrom_measurableCylinders]
    exact hF.comap_le
  · rw [IndepSets_iff]
    rintro a _ ha ⟨_, hcyl, rfl⟩
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hcyl
    have hae : (fun ω (φ : s) => R ω φ) =ᵐ[P] fun ω (φ : s) => V φ ω := by
      have : ∀ᵐ ω ∂P, ∀ φ : s, R ω φ = V φ ω := ae_all_iff.2 fun φ => hRV φ
      filter_upwards [this] with ω hω
      funext φ; exact hω φ
    have h := indep_comap_of_ae_eq hae (hV s)
    rw [Indep_iff] at h
    exact h a _ ha ⟨S, hS, rfl⟩

end Indep

section Coarse

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **the continuous coarse field `h_{t,∞}`, measurable for a sub-σ-algebra** carrying the
`W (K^{(t,∞)}_x)` -/
theorem exists_coarseVersion (hW : IsWhiteNoise P W) {U : Set ℂ} {t : ℝ}
    {m' : MeasurableSpace Ω} (hm' : m' ≤ mΩ)
    (hmeas : ∀ x, Measurable[m'] (W (wndKernelL2 U (Ioi t) x)))
    {K α : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hF : ∀ x x', ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2 ≤ K * ‖x - x'‖ ^ α) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable[m'] (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] wnField W U (Ioi t) x := by
  let _ : MeasurableSpace Ω := mΩ
  have := hW.isProbabilityMeasure
  set k : ℂ → WNSpace := fun x => wndKernelL2 U (Ioi t) x with hk
  set Z : ℂ → Ω → ℝ := fun x ω => Real.sqrt Real.pi * W (k x) ω with hZ
  have hZm : ∀ x, Measurable[m'] (Z x) := fun x => (hmeas x).const_mul _
  have hPt : @IsProbabilityMeasure Ω m' (P.trim hm') :=
    ⟨by rw [trim_measurableSet_eq hm' (@MeasurableSet.univ Ω m')]; exact measure_univ⟩
  have hlaw : ∀ x x', @HasLaw Ω ℝ m' _ (fun ω => Z x ω - Z x' ω)
      (gaussianReal 0 (‖Real.sqrt Real.pi • k x + (-Real.sqrt Real.pi) • k x'‖ ^ 2).toNNReal)
      (P.trim hm') := by
    intro x x'
    have h := hW.hasLaw ![k x, k x'] ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hm : Measurable[m'] (fun ω => Z x ω - Z x' ω) := (hZm x).sub (hZm x')
    refine @HasLaw.mk Ω ℝ m' _ _ _ _ (@Measurable.aemeasurable Ω ℝ m' _ _ _ hm) ?_
    rw [map_trim_of_measurable hm' hm, ← h.map_eq]
    congr 1; funext ω; simp only [hZ]; ring
  obtain ⟨Y, hYc, hYm, hYZ⟩ := @exists_continuous_modification_of_holder_law Ω m' (P.trim hm')
    Z hZm _ hlaw (Real.pi * K) α (by positivity) hα (fun x x' => by
      rw [Real.coe_toNNReal', max_le_iff]
      refine ⟨?_, by positivity⟩
      rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul, mul_pow,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt Real.pi_pos.le, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hF x x') Real.pi_pos.le)
  exact ⟨Y, hYc, hYm, fun x => ae_eq_of_ae_eq_trim (hYZ x)⟩

end Coarse

end LQGMetric.CONF.ZBM
