/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CoordRegFubini at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample

/-!
# Stochastic Fubini for a family of admissible measures (helper for RC2)

`integral_kernelAvg_ae_eq_bind` generalizes `RegSample.integral_fcAvg_ae_eq_bind_real` from the
folded-circle kernel `u ↦ fc(u, r)` to an arbitrary Markov kernel `Φ` whose measures have a
uniform support bound and a uniform logarithmic potential bound on a set `K'`: if `Y u` is a
version of `X(Φ u) − X(Φ z₀)` continuous in `u ∈ Hbar`, then almost surely
`∫ Y u dν(u) = X(ν.bind Φ) − X(ν(ℂ) • Φ z₀)`.
The proof is the one of `integral_fcAvg_ae_eq_bind_real`, verbatim up to the kernel.

Source: none — **own elementary proof** (the same argument as
`RegSample.integral_fcAvg_ae_eq_bind_real`, `LQG/RegularSample.lean`, with an arbitrary Markov
kernel; no published source treats this general form).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace CoordReg

open CircleFubini

/-! ## Integrals against `ν.bind Φ` -/

section BindKernel

variable (ν : Measure ℂ) [IsFiniteMeasure ν] (Φ : ProbabilityTheory.Kernel ℂ ℂ)
  [IsMarkovKernel Φ]

theorem integral_bind_kernel {F : ℂ → ℝ} (hF : Integrable F (ν.bind Φ)) :
    Integrable (fun w => ∫ x, F x ∂Φ w) ν ∧
      ∫ x, F x ∂(ν.bind Φ) = ∫ w, ∫ x, F x ∂Φ w ∂ν := by
  change Integrable F (Φ ∘ₘ ν) at hF
  change Integrable (fun w => ∫ x, F x ∂Φ w) ν ∧ ∫ x, F x ∂(Φ ∘ₘ ν) = ∫ w, ∫ x, F x ∂Φ w ∂ν
  rw [Measure.comp_eq_comp_const_apply] at hF ⊢
  refine ⟨?_, ?_⟩
  · simpa using hF.integral_comp
  · rw [ProbabilityTheory.Kernel.integral_comp hF]; simp

theorem bind_kernel_apply {A : Set ℂ} (hA : MeasurableSet A) :
    (ν.bind Φ) A = ∫⁻ w, Φ w A ∂ν :=
  Measure.bind_apply hA Φ.measurable.aemeasurable

theorem bind_kernel_univ : (ν.bind Φ) Set.univ = ν Set.univ := by
  rw [bind_kernel_apply ν Φ MeasurableSet.univ]; simp

theorem isFiniteMeasure_bind_kernel : IsFiniteMeasure (ν.bind Φ) :=
  ⟨by rw [bind_kernel_univ]; exact measure_lt_top _ _⟩

theorem bind_kernel_support {K : Set ℂ} (hνK : ν Kᶜ = 0) {R : ℝ}
    (hS : ∀ z ∈ K, Φ z (ballH R)ᶜ = 0) : (ν.bind Φ) (ballH R)ᶜ = 0 := by
  rw [bind_kernel_apply ν Φ (measurableSet_ballH R).compl]
  have hae : ∀ᵐ w ∂ν, w ∈ K := mem_ae_iff.mpr hνK
  rw [lintegral_congr_ae (hae.mono fun w hw => hS w hw), lintegral_zero]

theorem bind_kernel_pot {K : Set ℂ} (hνK : ν Kᶜ = 0) {C : ℝ≥0∞}
    (hC : ∀ z ∈ K, ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂Φ z ≤ C) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(ν.bind Φ) ≤ ν Set.univ * C := by
  rw [Measure.lintegral_bind Φ.measurable.aemeasurable (measurable_logPot y).aemeasurable]
  have hae : ∀ᵐ w ∂ν, w ∈ K := mem_ae_iff.mpr hνK
  calc ∫⁻ w, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂Φ w ∂ν
      ≤ ∫⁻ _, C ∂ν := lintegral_mono_ae (hae.mono fun w hw => hC w hw y)
    _ = ν Set.univ * C := by rw [lintegral_const, mul_comm]

/-- Linearity of `kernelCov neumannH` in the first measure under `bind`. -/
theorem kernelCov_bind_kernel {R : ℝ} (hS : (ν.bind Φ) (ballH R)ᶜ = 0)
    {μ' : Measure ℂ} [IsFiniteMeasure μ'] (hμ' : μ' (ballH R)ᶜ = 0) {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ' ≤ C) :
    Integrable (fun w => kernelCov neumannH (Φ w) μ') ν ∧
      ∫ w, kernelCov neumannH (Φ w) μ' ∂ν = kernelCov neumannH (ν.bind Φ) μ' := by
  have := isFiniteMeasure_bind_kernel ν Φ
  have hint := integrable_neumannH hS hμ' hCt hC
  have hF : Integrable (fun x => ∫ y, neumannH x y ∂μ') (ν.bind Φ) :=
    hint.integral_prod_left
  obtain ⟨h1, h2⟩ := integral_bind_kernel ν Φ hF
  exact ⟨h1, h2.symm⟩

end BindKernel

/-! ## Stochastic Fubini -/

theorem integral_kernelAvg_ae_eq_bind
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (Φ : ProbabilityTheory.Kernel ℂ ℂ)
    [IsMarkovKernel Φ] {K' : Set ℂ} {R : ℝ} {Cc : ℝ≥0∞} (hCct : Cc ≠ ⊤)
    (hcS : ∀ z ∈ K', Φ z (ballH R)ᶜ = 0)
    (hcP : ∀ z ∈ K', ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂Φ z ≤ Cc)
    {z₀ : ℂ} (hz₀ : z₀ ∈ K')
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hY : ∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P] fun ω => X ω (Φ z) - X ω (Φ z₀))
    (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hKK : K ⊆ K') (hνK : ν Kᶜ = 0) :
    (fun ω => ∫ z, Y z ω ∂ν) =ᵐ[P] fun ω =>
      X ω (ν.bind Φ) - X ω (ν Set.univ • Φ z₀) := by
  set νk := ν.bind Φ with hνk_def
  set μ₀ := ν Set.univ • Φ z₀ with hμ₀_def
  have : IsFiniteMeasure νk := isFiniteMeasure_bind_kernel ν Φ
  have : IsFiniteMeasure μ₀ := isFiniteMeasure_smul' _ (measure_ne_top _ _) _
  have hcA : ∀ z ∈ K', IsAdmissibleH (Φ z) := fun z hz =>
    admissible_of_bounds (hcS z hz) hCct (hcP z hz)
  have hmCt : ν Set.univ * Cc ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) hCct
  have hkS : νk (ballH R)ᶜ = 0 := bind_kernel_support ν Φ hνK fun z hz => hcS z (hKK hz)
  have hkP : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂νk ≤ ν Set.univ * Cc :=
    bind_kernel_pot ν Φ hνK fun z hz => hcP z (hKK hz)
  have hkA : IsAdmissibleH νk := admissible_of_bounds hkS hmCt hkP
  have hkU : νk Set.univ = ν Set.univ := bind_kernel_univ ν Φ
  have h0S : μ₀ (ballH R)ᶜ = 0 := by
    rw [hμ₀_def, Measure.smul_apply, hcS z₀ hz₀, smul_zero]
  have h0P : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ₀ ≤ ν Set.univ * Cc :=
    smul_pot (hcP z₀ hz₀)
  have h0A : IsAdmissibleH μ₀ := admissible_of_bounds h0S hmCt h0P
  have h0U : μ₀ Set.univ = ν Set.univ := by
    rw [hμ₀_def, Measure.smul_apply, measure_univ (μ := Φ z₀), smul_eq_mul, mul_one]
  -- the random variables
  set W : ℂ → Ω → ℝ := fun z ω => X ω (Φ z) - X ω (Φ z₀) with hW_def
  set D : Ω → ℝ := fun ω => X ω νk - X ω μ₀ with hD_def
  have hWm : ∀ z, Measurable (W z) := fun z =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hDm : Measurable D := (hX.measurable_coord _).sub (hX.measurable_coord _)
  have h11 : ∀ z : ℂ, (Φ z) Set.univ = (Φ z₀) Set.univ := by
    intro z; simp
  have hqU : νk Set.univ = μ₀ Set.univ := by rw [hkU, h0U]
  have hWL2 : ∀ z ∈ K, MemLp (W z) 2 P := fun z hz =>
    gff_memLp (p := (Φ z, Φ z₀)) hX (hcA z (hKK hz)) (hcA z₀ hz₀) (h11 z)
  have hDL2 : MemLp D 2 P := gff_memLp (p := (νk, μ₀)) hX hkA h0A hqU
  have hEWW : ∀ z ∈ K, ∀ z' ∈ K, ∫ ω, W z ω * W z' ω ∂P
      = kernelCov2 neumannH (Φ z, Φ z₀) (Φ z', Φ z₀) :=
    fun z hz z' hz' => gff_integral_mul (p := (Φ z, Φ z₀)) (q := (Φ z', Φ z₀)) hX
      (hcA z (hKK hz)) (hcA z₀ hz₀) (h11 z) (hcA z' (hKK hz')) (hcA z₀ hz₀) (h11 z')
  have hEWD : ∀ z ∈ K, ∫ ω, W z ω * D ω ∂P = kernelCov2 neumannH (Φ z, Φ z₀) (νk, μ₀) :=
    fun z hz => gff_integral_mul (p := (Φ z, Φ z₀)) (q := (νk, μ₀)) hX (hcA z (hKK hz))
      (hcA z₀ hz₀) (h11 z) hkA h0A hqU
  have hEDW : ∀ z ∈ K, ∫ ω, D ω * W z ω ∂P = kernelCov2 neumannH (νk, μ₀) (Φ z, Φ z₀) :=
    fun z hz => gff_integral_mul (p := (νk, μ₀)) (q := (Φ z, Φ z₀)) hX hkA h0A hqU
      (hcA z (hKK hz)) (hcA z₀ hz₀) (h11 z)
  have hEDD : ∫ ω, D ω * D ω ∂P = kernelCov2 neumannH (νk, μ₀) (νk, μ₀) :=
    gff_integral_mul (p := (νk, μ₀)) (q := (νk, μ₀)) hX hkA h0A hqU hkA h0A hqU
  -- a jointly measurable version of `Y`
  obtain ⟨Z, hZm, hZc, hZY, hZW⟩ := exists_measurable_version hYc hWm hY
  have hZL2 : ∀ z ∈ K, MemLp (Z z) 2 P := fun z hz =>
    (hWL2 z hz).ae_eq (hZW z (hKH hz)).symm
  -- the uniform variance bound
  set b := (nBound (Φ z₀) (Φ z₀) R Cc).toReal with hb_def
  have hkc : ∀ z z', z ∈ K' → z' ∈ K' →
      |kernelCov neumannH (Φ z) (Φ z')| ≤ b := by
    intro z z' hz hz'
    have := abs_kernelCov_le (hcS z hz) (hcS z' hz') hCct (hcP z' hz')
    have he : nBound (Φ z) (Φ z') R Cc = nBound (Φ z₀) (Φ z₀) R Cc := by
      simp only [nBound, measure_univ]
    rwa [he] at this
  have hB : ∀ z ∈ K, ∫ ω, Z z ω ^ 2 ∂P ≤ 4 * b := by
    intro z hz
    have e1 : ∫ ω, Z z ω ^ 2 ∂P = ∫ ω, W z ω * W z ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hZW z (hKH hz)] with ω hω
      rw [hω, sq]
    rw [e1, hEWW z hz z hz]
    simp only [kernelCov2]
    have a1 := abs_le.1 (hkc z z (hKK hz) (hKK hz))
    have a2 := abs_le.1 (hkc z z₀ (hKK hz) hz₀)
    have a3 := abs_le.1 (hkc z₀ z hz₀ (hKK hz))
    have a4 := abs_le.1 (hkc z₀ z₀ hz₀ hz₀)
    linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have hmom : ∀ z ∈ K, Integrable (fun ω => Z z ω ^ 2) P := fun z hz =>
    (hZL2 z hz).integrable_sq
  -- linearity of the covariance under `bind`
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.mpr hνK
  have hsmul : ∀ μ' : Measure ℂ, kernelCov neumannH μ₀ μ'
      = (ν Set.univ).toReal * kernelCov neumannH (Φ z₀) μ' := by
    intro μ'; simp only [kernelCov, hμ₀_def, integral_smul_measure, smul_eq_mul]
  have hlin2 : ∀ (a b' : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b'],
      a (ballH R)ᶜ = 0 → b' (ballH R)ᶜ = 0 → ∀ {C C' : ℝ≥0∞}, C ≠ ⊤ → C' ≠ ⊤ →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂a ≤ C) →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂b' ≤ C') →
      ∫ w, kernelCov2 neumannH (Φ w, Φ z₀) (a, b') ∂ν
        = kernelCov2 neumannH (νk, μ₀) (a, b') := by
    intro a b' _ _ ha hb' C C' hC hC' hCa hCb
    obtain ⟨ia, ea⟩ := kernelCov_bind_kernel ν Φ hkS ha hC hCa
    obtain ⟨ib, eb⟩ := kernelCov_bind_kernel ν Φ hkS hb' hC' hCb
    simp only [kernelCov2]
    rw [integral_add (f := fun w => kernelCov neumannH (Φ w) a
          - kernelCov neumannH (Φ w) b' - kernelCov neumannH (Φ z₀) a)
        (g := fun _ => kernelCov neumannH (Φ z₀) b')
        ((ia.sub ib).sub (integrable_const _)) (integrable_const _),
      integral_sub (f := fun w => kernelCov neumannH (Φ w) a - kernelCov neumannH (Φ w) b')
        (g := fun _ => kernelCov neumannH (Φ z₀) a) (ia.sub ib) (integrable_const _),
      integral_sub ia ib, ea, eb,
      integral_const, integral_const, smul_eq_mul, smul_eq_mul, measureReal_def, hsmul, hsmul]
  -- the second moments of `L = ∫ Z z dν`
  obtain ⟨hLm, hLL2⟩ := memLp_integral (B := 4 * b) hZm hνK hK hZc hmom hB
  set L : Ω → ℝ := fun ω => ∫ z, Z z ω ∂ν with hL_def
  have hZmz : ∀ z, Measurable (Z z) := fun z => hZm.of_uncurry_left
  have hZD : ∀ z ∈ K, ∫ ω, Z z ω * D ω ∂P
      = kernelCov2 neumannH (Φ z, Φ z₀) (νk, μ₀) := by
    intro z hz
    rw [← hEWD z hz]
    refine integral_congr_ae ?_
    filter_upwards [hZW z (hKH hz)] with ω hω
    rw [hω]
  have E1 : ∫ ω, L ω * D ω ∂P = kernelCov2 neumannH (νk, μ₀) (νk, μ₀) := by
    rw [fubini_mul hZm hνK hmom hB hDm hDL2]
    calc ∫ z, ∫ ω, Z z ω * D ω ∂P ∂ν
        = ∫ z, kernelCov2 neumannH (Φ z, Φ z₀) (νk, μ₀) ∂ν :=
          integral_congr_ae (hae.mono fun z hz => hZD z hz)
      _ = _ := hlin2 νk μ₀ hkS h0S hmCt hmCt hkP h0P
  have E2 : ∫ ω, L ω * L ω ∂P = ∫ ω, L ω * D ω ∂P := by
    rw [fubini_mul hZm hνK hmom hB hLm hLL2, fubini_mul hZm hνK hmom hB hDm hDL2]
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    show ∫ ω, Z z ω * L ω ∂P = ∫ ω, Z z ω * D ω ∂P
    have i1 : ∫ ω, Z z ω * L ω ∂P = ∫ ω, L ω * Z z ω ∂P := by simp_rw [mul_comm]
    rw [i1, fubini_mul hZm hνK hmom hB (hZmz z) (hZL2 z hz)]
    calc ∫ z', ∫ ω, Z z' ω * Z z ω ∂P ∂ν
        = ∫ z', kernelCov2 neumannH (Φ z', Φ z₀) (Φ z, Φ z₀) ∂ν := by
          refine integral_congr_ae (hae.mono fun z' hz' => ?_)
          show ∫ ω, Z z' ω * Z z ω ∂P = _
          beta_reduce
          rw [← hEWW z' hz' z hz]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz), hZW z' (hKH hz')] with ω hω hω'
          rw [hω, hω']
      _ = kernelCov2 neumannH (νk, μ₀) (Φ z, Φ z₀) :=
          hlin2 _ _ (hcS z (hKK hz)) (hcS z₀ hz₀) hCct hCct (hcP z (hKK hz)) (hcP z₀ hz₀)
      _ = ∫ ω, Z z ω * D ω ∂P := by
          rw [← hEDW z hz]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz)] with ω hω
          rw [hω, mul_comm]
  -- conclusion: `E[(L - D)²] = 0`
  have hsq : ∫ ω, (L ω - D ω) ^ 2 ∂P = 0 := by
    have : ∀ ω, (L ω - D ω) ^ 2 = (L ω * L ω - 2 * (L ω * D ω)) + D ω * D ω := fun ω => by
      ring
    simp_rw [this]
    have iLL := integrable_mul_of_memLp_two hLL2 hLL2
    have iLD := integrable_mul_of_memLp_two hLL2 hDL2
    have iDD := integrable_mul_of_memLp_two hDL2 hDL2
    rw [integral_add (f := fun ω => L ω * L ω - 2 * (L ω * D ω)) (g := fun ω => D ω * D ω)
        (iLL.sub (iLD.const_mul 2)) iDD,
      integral_sub (f := fun ω => L ω * L ω) (g := fun ω => 2 * (L ω * D ω)) iLL
        (iLD.const_mul 2),
      integral_const_mul, E2, E1, hEDD]
    ring
  have hint : Integrable (fun ω => (L ω - D ω) ^ 2) P := (hLL2.sub hDL2).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (L ω - D ω)) hint).1 hsq
  filter_upwards [h0, hZY] with ω hω hωY
  have hLD : L ω = D ω := by
    have h2 : (L ω - D ω) ^ 2 = 0 := hω
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h2
    linarith
  show ∫ z, Y z ω ∂ν = D ω
  rw [← hLD]
  exact integral_congr_ae (hae.mono fun z hz => (hωY z (hKH hz)).symm)

end CoordReg
end QuantumZipper
