/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.RegularSample at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible

/-!
# Every-circle regularity of the free GFF (blueprint node M4-R3)

Main result: `ae_isRegularSample`: for a free-boundary GFF modulo constants `X`,
almost surely `X ω` is a regular sample (`RegularSampleDefs`).

Route (one process, four real parameters). For `q ∈ ℝ⁴` put `w = q₀ + i|q₁|`, `r = 2^{q₂}`,
`ρ = |q₃|` and `ν_q = (foldedCircle w r).bind (foldedCircle · ρ)` (for `ρ = 0` this is
`foldedCircle w r` itself). The potential of `ν_q` is
`x ↦ ∫ circPot r w d(foldedCircle x ρ)` (Fubini for two admissible circles), which is
Lipschitz in `q` uniformly in `x` on every box; hence `Var(X(ν_q) − X(ν_{q'})) ≤ L_R ‖q − q'‖`,
and the dyadic Kolmogorov theorem in four parameters (`KolmD`) gives a continuous
modification `Ṽ`. The witness is `F (w, r) = Ṽ (w, r, 0)`: clause (i) is the dyadic convergence
along the Kolmogorov lattice; clause (ii) follows because `∫ F(·, ρ) d(foldedCircle w r)` and
`Ṽ (w, r, ρ)` are continuous and agree almost surely at each point (stochastic Fubini at an
arbitrary radius), hence everywhere, and `Ṽ` is jointly continuous up to `ρ = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace RegSample

open CircleFubini

/-! ## 0. Stochastic Fubini for folded circles of an arbitrary radius

Verbatim generalization of `integral_circleAvg_ae_eq_bind` (which is stated for the radii
`radius k`; its proof only uses `0 < r`). -/

theorem integral_fcAvg_ae_eq_bind_real
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r) {z₀ : ℂ} (hz₀ : z₀ ∈ Hbar)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hY : ∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P]
      fun ω => X ω (foldedCircle z r) - X ω (foldedCircle z₀ r))
    (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hνK : ν Kᶜ = 0) :
    (fun ω => ∫ z, Y z ω ∂ν) =ᵐ[P] fun ω =>
      X ω (ν.bind fun w => foldedCircle w r)
        - X ω (ν Set.univ • foldedCircle z₀ r) := by
  set νk := ν.bind fun w => foldedCircle w r with hνk_def
  set μ₀ := ν Set.univ • foldedCircle z₀ r with hμ₀_def
  have : IsFiniteMeasure νk := isFiniteMeasure_bind_circle ν
  have : IsFiniteMeasure μ₀ := isFiniteMeasure_smul' _ (measure_ne_top _ _) _
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R₀ := max R₁ ‖z₀‖ with hR₀_def
  set R := R₀ + r with hR_def
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R₀ := fun z hz => by
    have := hR₁ hz
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hz₀R : ‖z₀‖ ≤ R₀ := le_max_right _ _
  set Cc : ℝ≥0∞ := 2 * ENNReal.ofReal (potConst r) with hCc_def
  have hCct : Cc ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hcP : ∀ z y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂foldedCircle z r ≤ Cc :=
    fun z y => foldedCircle_pot_le hr z y
  have hcS : ∀ z, ‖z‖ ≤ R₀ → foldedCircle z r (ballH R)ᶜ = 0 := fun z hz =>
    foldedCircle_support hr.le (by linarith)
  have hcA : ∀ z, ‖z‖ ≤ R₀ → IsAdmissibleH (foldedCircle z r) := fun z hz =>
    admissible_of_bounds (hcS z hz) hCct (hcP z)
  have hmCt : ν Set.univ * Cc ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) hCct
  have hkS : νk (ballH R)ᶜ = 0 := bind_circle_support ν hr.le hνK hKR (le_refl _)
  have hkP : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂νk ≤ ν Set.univ * Cc :=
    bind_circle_pot ν hcP
  have hkA : IsAdmissibleH νk := admissible_of_bounds hkS hmCt hkP
  have hkU : νk Set.univ = ν Set.univ := bind_circle_univ ν
  have h0S : μ₀ (ballH R)ᶜ = 0 := by
    rw [hμ₀_def, Measure.smul_apply, hcS z₀ hz₀R, smul_zero]
  have h0P : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ₀ ≤ ν Set.univ * Cc :=
    smul_pot (hcP z₀)
  have h0A : IsAdmissibleH μ₀ := admissible_of_bounds h0S hmCt h0P
  have h0U : μ₀ Set.univ = ν Set.univ := by
    rw [hμ₀_def, Measure.smul_apply, measure_univ (μ := foldedCircle z₀ r), smul_eq_mul, mul_one]
  -- the random variables
  set W : ℂ → Ω → ℝ := fun z ω => X ω (foldedCircle z r) - X ω (foldedCircle z₀ r) with hW_def
  set D : Ω → ℝ := fun ω => X ω νk - X ω μ₀ with hD_def
  have hWm : ∀ z, Measurable (W z) := fun z =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hDm : Measurable D := (hX.measurable_coord _).sub (hX.measurable_coord _)
  have h11 : ∀ z : ℂ, (foldedCircle z r) Set.univ = (foldedCircle z₀ r) Set.univ := by
    intro z; simp
  have hqU : νk Set.univ = μ₀ Set.univ := by rw [hkU, h0U]
  have hWL2 : ∀ z ∈ K, MemLp (W z) 2 P := fun z hz =>
    gff_memLp (p := (foldedCircle z r, foldedCircle z₀ r)) hX (hcA z (hKR z hz))
      (hcA z₀ hz₀R) (h11 z)
  have hDL2 : MemLp D 2 P := gff_memLp (p := (νk, μ₀)) hX hkA h0A hqU
  have hEWW : ∀ z ∈ K, ∀ z' ∈ K, ∫ ω, W z ω * W z' ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r)
          (foldedCircle z' r, foldedCircle z₀ r) :=
    fun z hz z' hz' => gff_integral_mul (p := (foldedCircle z r, foldedCircle z₀ r))
      (q := (foldedCircle z' r, foldedCircle z₀ r)) hX (hcA z (hKR z hz)) (hcA z₀ hz₀R) (h11 z)
      (hcA z' (hKR z' hz')) (hcA z₀ hz₀R) (h11 z')
  have hEWD : ∀ z ∈ K, ∫ ω, W z ω * D ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) :=
    fun z hz => gff_integral_mul (p := (foldedCircle z r, foldedCircle z₀ r)) (q := (νk, μ₀)) hX (hcA z (hKR z hz))
      (hcA z₀ hz₀R) (h11 z) hkA h0A hqU
  have hEDW : ∀ z ∈ K, ∫ ω, D ω * W z ω ∂P
      = kernelCov2 neumannH (νk, μ₀) (foldedCircle z r, foldedCircle z₀ r) :=
    fun z hz => gff_integral_mul (p := (νk, μ₀)) (q := (foldedCircle z r, foldedCircle z₀ r)) hX hkA h0A hqU (hcA z (hKR z hz)) (hcA z₀ hz₀R) (h11 z)
  have hEDD : ∫ ω, D ω * D ω ∂P = kernelCov2 neumannH (νk, μ₀) (νk, μ₀) :=
    gff_integral_mul (p := (νk, μ₀)) (q := (νk, μ₀)) hX hkA h0A hqU hkA h0A hqU
  -- a jointly measurable version of `Y`
  obtain ⟨Z, hZm, hZc, hZY, hZW⟩ := exists_measurable_version hYc hWm hY
  have hZL2 : ∀ z ∈ K, MemLp (Z z) 2 P := fun z hz =>
    (hWL2 z hz).ae_eq (hZW z (hKH hz)).symm
  -- the uniform variance bound
  set b := (nBound (foldedCircle z₀ r) (foldedCircle z₀ r) R Cc).toReal with hb_def
  have hkc : ∀ z z', ‖z‖ ≤ R₀ → ‖z'‖ ≤ R₀ →
      |kernelCov neumannH (foldedCircle z r) (foldedCircle z' r)| ≤ b := by
    intro z z' hz hz'
    have := abs_kernelCov_le (hcS z hz) (hcS z' hz') hCct (hcP z')
    have he : nBound (foldedCircle z r) (foldedCircle z' r) R Cc
        = nBound (foldedCircle z₀ r) (foldedCircle z₀ r) R Cc := by
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
    have a1 := abs_le.1 (hkc z z (hKR z hz) (hKR z hz))
    have a2 := abs_le.1 (hkc z z₀ (hKR z hz) hz₀R)
    have a3 := abs_le.1 (hkc z₀ z hz₀R (hKR z hz))
    have a4 := abs_le.1 (hkc z₀ z₀ hz₀R hz₀R)
    linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have hmom : ∀ z ∈ K, Integrable (fun ω => Z z ω ^ 2) P := fun z hz =>
    (hZL2 z hz).integrable_sq
  -- linearity of the covariance under `bind`
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.mpr hνK
  have hsmul : ∀ μ' : Measure ℂ, kernelCov neumannH μ₀ μ'
      = (ν Set.univ).toReal * kernelCov neumannH (foldedCircle z₀ r) μ' := by
    intro μ'; simp only [kernelCov, hμ₀_def, integral_smul_measure, smul_eq_mul]
  have hlin2 : ∀ (a b' : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b'],
      a (ballH R)ᶜ = 0 → b' (ballH R)ᶜ = 0 → ∀ {C C' : ℝ≥0∞}, C ≠ ⊤ → C' ≠ ⊤ →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂a ≤ C) →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂b' ≤ C') →
      ∫ w, kernelCov2 neumannH (foldedCircle w r, foldedCircle z₀ r) (a, b') ∂ν
        = kernelCov2 neumannH (νk, μ₀) (a, b') := by
    intro a b' _ _ ha hb' C C' hC hC' hCa hCb
    obtain ⟨ia, ea⟩ := kernelCov_bind ν hkS ha hC hCa
    obtain ⟨ib, eb⟩ := kernelCov_bind ν hkS hb' hC' hCb
    simp only [kernelCov2]
    rw [integral_add (f := fun w => kernelCov neumannH (foldedCircle w r) a
          - kernelCov neumannH (foldedCircle w r) b' - kernelCov neumannH (foldedCircle z₀ r) a)
        (g := fun _ => kernelCov neumannH (foldedCircle z₀ r) b')
        ((ia.sub ib).sub (integrable_const _)) (integrable_const _),
      integral_sub (f := fun w => kernelCov neumannH (foldedCircle w r) a
          - kernelCov neumannH (foldedCircle w r) b')
        (g := fun _ => kernelCov neumannH (foldedCircle z₀ r) a) (ia.sub ib) (integrable_const _),
      integral_sub ia ib, ea, eb,
      integral_const, integral_const, smul_eq_mul, smul_eq_mul, measureReal_def, hsmul, hsmul]
  -- the second moments of `L = ∫ Z z dν`
  obtain ⟨hLm, hLL2⟩ := memLp_integral (B := 4 * b) hZm hνK hK hZc hmom hB
  set L : Ω → ℝ := fun ω => ∫ z, Z z ω ∂ν with hL_def
  have hZmz : ∀ z, Measurable (Z z) := fun z => hZm.of_uncurry_left
  have hZD : ∀ z ∈ K, ∫ ω, Z z ω * D ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) := by
    intro z hz
    rw [← hEWD z hz]
    refine integral_congr_ae ?_
    filter_upwards [hZW z (hKH hz)] with ω hω
    rw [hω]
  have E1 : ∫ ω, L ω * D ω ∂P = kernelCov2 neumannH (νk, μ₀) (νk, μ₀) := by
    rw [fubini_mul hZm hνK hmom hB hDm hDL2]
    calc ∫ z, ∫ ω, Z z ω * D ω ∂P ∂ν
        = ∫ z, kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) ∂ν :=
          integral_congr_ae (hae.mono fun z hz => hZD z hz)
      _ = _ := hlin2 νk μ₀ hkS h0S hmCt hmCt hkP h0P
  have E2 : ∫ ω, L ω * L ω ∂P = ∫ ω, L ω * D ω ∂P := by
    rw [fubini_mul hZm hνK hmom hB hLm hLL2, fubini_mul hZm hνK hmom hB hDm hDL2]
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    show ∫ ω, Z z ω * L ω ∂P = ∫ ω, Z z ω * D ω ∂P
    have i1 : ∫ ω, Z z ω * L ω ∂P = ∫ ω, L ω * Z z ω ∂P := by simp_rw [mul_comm]
    rw [i1, fubini_mul hZm hνK hmom hB (hZmz z) (hZL2 z hz)]
    calc ∫ z', ∫ ω, Z z' ω * Z z ω ∂P ∂ν
        = ∫ z', kernelCov2 neumannH (foldedCircle z' r, foldedCircle z₀ r)
            (foldedCircle z r, foldedCircle z₀ r) ∂ν := by
          refine integral_congr_ae (hae.mono fun z' hz' => ?_)
          show ∫ ω, Z z' ω * Z z ω ∂P = _
          beta_reduce
          rw [← hEWW z' hz' z hz]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz), hZW z' (hKH hz')] with ω hω hω'
          rw [hω, hω']
      _ = kernelCov2 neumannH (νk, μ₀) (foldedCircle z r, foldedCircle z₀ r) :=
          hlin2 _ _ (hcS z (hKR z hz)) (hcS z₀ hz₀R) hCct hCct (hcP z) (hcP z₀)
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

/-! ## 1. The four-parameter family of measures -/

/-- Centre `q₀ + i|q₁|`. -/
def cen (q : Fin 4 → ℝ) : ℂ := ⟨q 0, |q 1|⟩

/-- Radius `2^{q₂}`. -/
def rad (q : Fin 4 → ℝ) : ℝ := Real.exp (Real.log 2 * q 2)

/-- Smoothing radius `|q₃|`. -/
def sm (q : Fin 4 → ℝ) : ℝ := |q 3|

/-- The measure `ν_q`: the folded circle `(cen q, rad q)` smoothed by folded circles of radius
`sm q`. -/
def nuQ (q : Fin 4 → ℝ) : Measure ℂ :=
  (foldedCircle (cen q) (rad q)).bind fun u => foldedCircle u (sm q)

theorem cen_mem (q : Fin 4 → ℝ) : cen q ∈ Hbar := show 0 ≤ |q 1| from abs_nonneg _

theorem rad_pos (q : Fin 4 → ℝ) : 0 < rad q := Real.exp_pos _

theorem sm_nonneg (q : Fin 4 → ℝ) : 0 ≤ sm q := abs_nonneg _

theorem circleUnif_zero (u : ℂ) : circleUnif u 0 = Measure.dirac u := by
  ext s hs
  rw [circleUnif, Measure.smul_apply, Measure.map_apply (measurable_circleMap u 0) hs,
    Measure.dirac_apply' _ hs, circleMap_zero_radius]
  by_cases hu : u ∈ s
  · have e : (Function.const ℝ u) ⁻¹' s = univ := by ext; simp [hu]
    rw [e, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ico, sub_zero,
      indicator_of_mem hu, smul_eq_mul,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top]
    rfl
  · have e : (Function.const ℝ u) ⁻¹' s = ∅ := by ext; simp [hu]
    rw [e, indicator_of_notMem hu]; simp

theorem fc_zero (u : ℂ) : foldedCircle u 0 = Measure.dirac (foldH u) := by
  rw [foldedCircle, circleUnif_zero, Measure.map_dirac' measurable_foldH]

theorem nuQ_of_sm_zero {q : Fin 4 → ℝ} (h : sm q = 0) :
    nuQ q = foldedCircle (cen q) (rad q) := by
  unfold nuQ
  rw [h]
  simp_rw [fc_zero]
  rw [Measure.bind_dirac_eq_map _ measurable_foldH, foldedCircle,
    Measure.map_map measurable_foldH measurable_foldH]
  congr 1
  funext u
  exact foldH_of_mem' (foldH_mem_Hbar' u)

instance isProbabilityMeasure_nuQ (q : Fin 4 → ℝ) : IsProbabilityMeasure (nuQ q) :=
  ⟨by rw [nuQ, bind_circle_univ]; exact measure_univ⟩

theorem nuQ_support (q : Fin 4 → ℝ) : nuQ q (ballH (‖cen q‖ + rad q + sm q))ᶜ = 0 :=
  bind_circle_support _ (sm_nonneg q) (K := ballH (‖cen q‖ + rad q))
    (foldedCircle_support (rad_pos q).le le_rfl)
    (fun z hz => by have := hz.1; rwa [mem_closedBall, dist_zero_right] at this) le_rfl

theorem nuQ_ae_mem (q : Fin 4 → ℝ) : ∀ᵐ u ∂nuQ q, u ∈ Hbar :=
  (ae_iff.2 (nuQ_support q)).mono fun _ hu => hu.2

theorem isAdmissibleH_nuQ (q : Fin 4 → ℝ) : IsAdmissibleH (nuQ q) := by
  rcases (sm_nonneg q).eq_or_lt with h | h
  · rw [nuQ_of_sm_zero h.symm]; exact isAdmissibleH_foldedCircle (cen_mem q) (rad_pos q)
  · refine admissible_of_bounds (nuQ_support q)
      (C := (foldedCircle (cen q) (rad q)) univ * (2 * ENNReal.ofReal (potConst (sm q)))) ?_
      (bind_circle_pot _ fun z y => foldedCircle_pot_le h z y)
    rw [measure_univ, one_mul]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

theorem integrable_nuQ {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (q : Fin 4 → ℝ) :
    Integrable g (nuQ q) := by
  have h := (hg.mono inter_subset_right).integrableOn_compact (μ := nuQ q)
    (isCompact_ballH (‖cen q‖ + rad q + sm q))
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (nuQ_support q))] at h

/-! ## 2. Potentials of `ν_q` and the variance bound -/

open CircleCont (circPot continuous_circPot integral_neumannH_foldedCircle_right)

/-- The potential of `ν_q` at `x`, in the form obtained after exchanging the two circle
integrations. -/
def PiQ (q : Fin 4 → ℝ) (x : ℂ) : ℝ :=
  ∫ v, circPot (rad q) (cen q) v ∂foldedCircle x (sm q)

theorem circPot_symm (ρ : ℝ) (u x : ℂ) : circPot ρ u x = circPot ρ x u := by
  unfold circPot
  rw [norm_sub_rev u x, show ‖u - conj x‖ = ‖x - conj u‖ by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj, norm_sub_rev]]

theorem integral_neumannH_nuQ {q : Fin 4 → ℝ} {x : ℂ} (hx : x ∈ Hbar)
    (hint : Integrable (fun y => neumannH x y) (nuQ q)) :
    ∫ y, neumannH x y ∂nuQ q = PiQ q x := by
  unfold PiQ
  rcases (sm_nonneg q).eq_or_lt with h | h
  · rw [nuQ_of_sm_zero h.symm, integral_neumannH_foldedCircle_right _ _ (rad_pos q), ← h, fc_zero,
      integral_dirac, foldH_of_mem' hx]
  · unfold nuQ at hint ⊢
    rw [(integral_bind_circle _ hint).2]
    have e1 : ∀ u, ∫ y, neumannH x y ∂foldedCircle u (sm q) =
        ∫ v, neumannH v u ∂foldedCircle x (sm q) := by
      intro u
      rw [integral_neumannH_foldedCircle_right u x h, circPot_symm]
      exact (integral_neumannH_foldedCircle x u h).symm
    simp_rw [e1]
    have hint2 : Integrable (Function.uncurry fun u v => neumannH v u)
        ((foldedCircle (cen q) (rad q)).prod (foldedCircle x (sm q))) :=
      (integrable_neumannH_prod (isAdmissibleH_foldedCircle hx h)
        (isAdmissibleH_foldedCircle (cen_mem q) (rad_pos q))).swap
    rw [integral_integral_swap hint2]
    exact integral_congr_ae (ae_of_all _ fun v =>
      integral_neumannH_foldedCircle_right _ _ (rad_pos q))

theorem kernelCov_nuQ (a b : Fin 4 → ℝ) :
    kernelCov neumannH (nuQ a) (nuQ b) = ∫ x, PiQ b x ∂nuQ a := by
  unfold kernelCov
  refine integral_congr_ae ?_
  filter_upwards [nuQ_ae_mem a, (integrable_neumannH_prod (isAdmissibleH_nuQ a)
    (isAdmissibleH_nuQ b)).prod_right_ae] with x hx hint
  exact integral_neumannH_nuQ hx hint

theorem abs_log_max_sub_le' {r r' s s' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    |Real.log (max r s) - Real.log (max r' s')| ≤ (|r - r'| + |s - s'|) / min r r' := by
  have hm : 0 < min r r' := lt_min hr hr'
  have hA : min r r' ≤ max r s := (min_le_left _ _).trans (le_max_left _ _)
  have hB : min r r' ≤ max r' s' := (min_le_right _ _).trans (le_max_left _ _)
  have hmax : |max r s - max r' s'| ≤ |r - r'| + |s - s'| :=
    (abs_max_sub_max_le_max _ _ _ _).trans (max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _)))
  have h1 := CircleMV.log_sub_log_le hm hA hB
  have h2 := CircleMV.log_sub_log_le hm hB hA
  rw [abs_sub_comm (max r' s')] at h2
  have h3 : |max r s - max r' s'| / min r r' ≤ (|r - r'| + |s - s'|) / min r r' :=
    div_le_div_of_nonneg_right hmax hm.le
  rw [abs_sub_le_iff]; constructor <;> linarith

theorem abs_circPot_sub_le' {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (w w' v v' : ℂ) :
    |circPot r w v - circPot r' w' v'| ≤
      2 * (|r - r'| + ‖w - w'‖ + ‖v - v'‖) / min r r' := by
  unfold circPot
  have hm : 0 < min r r' := lt_min hr hr'
  have hs : |‖w - v‖ - ‖w' - v'‖| ≤ ‖w - w'‖ + ‖v - v'‖ := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [show w - v - (w' - v') = (w - w') - (v - v') by ring]
    exact norm_sub_le _ _
  have hs' : |‖w - conj v‖ - ‖w' - conj v'‖| ≤ ‖w - w'‖ + ‖v - v'‖ := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [show w - conj v - (w' - conj v') = (w - w') - conj (v - v') by simp only [map_sub]; ring]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_conj]
  have h1 := abs_log_max_sub_le' (s := ‖w - v‖) (s' := ‖w' - v'‖) hr hr'
  have h2 := abs_log_max_sub_le' (s := ‖w - conj v‖) (s' := ‖w' - conj v'‖) hr hr'
  have e3 : (|r - r'| + |‖w - v‖ - ‖w' - v'‖|) / min r r' ≤
      (|r - r'| + (‖w - w'‖ + ‖v - v'‖)) / min r r' :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  have e4 : (|r - r'| + |‖w - conj v‖ - ‖w' - conj v'‖|) / min r r' ≤
      (|r - r'| + (‖w - w'‖ + ‖v - v'‖)) / min r r' :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  have e : -Real.log (max r ‖w - v‖) - Real.log (max r ‖w - conj v‖) -
      (-Real.log (max r' ‖w' - v'‖) - Real.log (max r' ‖w' - conj v'‖)) =
      -((Real.log (max r ‖w - v‖) - Real.log (max r' ‖w' - v'‖)) +
        (Real.log (max r ‖w - conj v‖) - Real.log (max r' ‖w' - conj v'‖))) := by ring
  rw [e, abs_neg]
  have key : (|r - r'| + (‖w - w'‖ + ‖v - v'‖)) / min r r' +
      (|r - r'| + (‖w - w'‖ + ‖v - v'‖)) / min r r' =
      2 * (|r - r'| + ‖w - w'‖ + ‖v - v'‖) / min r r' := by ring
  linarith [abs_add_le (Real.log (max r ‖w - v‖) - Real.log (max r' ‖w' - v'‖))
    (Real.log (max r ‖w - conj v‖) - Real.log (max r' ‖w' - conj v'‖))]

theorem norm_foldH_sub_le (a b : ℂ) : ‖foldH a - foldH b‖ ≤ ‖a - b‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  have h := sq_le_sq.2 (abs_abs_sub_abs_le a.im b.im)
  simp only [Complex.normSq_apply, foldH_eq_mk, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  nlinarith

theorem norm_circleMap_sub_radius (x : ℂ) (ρ ρ' θ : ℝ) :
    ‖circleMap x ρ θ - circleMap x ρ' θ‖ = |ρ - ρ'| := by
  simp only [circleMap]
  rw [show x + (ρ : ℂ) * Complex.exp (θ * Complex.I) - (x + (ρ' : ℂ) * Complex.exp (θ * Complex.I))
      = ((ρ - ρ' : ℝ) : ℂ) * Complex.exp (θ * Complex.I) by push_cast; ring,
    norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem abs_PiQ_sub_le (q q' : Fin 4 → ℝ) (x : ℂ) :
    |PiQ q x - PiQ q' x| ≤
      2 * (|rad q - rad q'| + ‖cen q - cen q'‖ + |sm q - sm q'|) / min (rad q) (rad q') := by
  unfold PiQ
  refine RegClosure.abs_integral_fc_sub_le (continuous_circPot (rad_pos q) _).continuousOn
    (continuous_circPot (rad_pos q') _).continuousOn fun θ => ?_
  refine (abs_circPot_sub_le' (rad_pos q) (rad_pos q') _ _ _ _).trans ?_
  have h := (norm_foldH_sub_le (circleMap x (sm q) θ) (circleMap x (sm q') θ)).trans
    (norm_circleMap_sub_radius x (sm q) (sm q') θ).le
  exact div_le_div_of_nonneg_right (by linarith) (lt_min (rad_pos q) (rad_pos q')).le

theorem continuousOn_PiQ (q : Fin 4 → ℝ) : ContinuousOn (PiQ q) Hbar :=
  RegClosure.continuousOn_integral_fc (P := ℂ) (S := Hbar)
    (H := fun _ v => circPot (rad q) (cen q) v) (c := fun x => x) (r := fun _ => sm q)
    ((continuous_circPot (rad_pos q) _).comp continuous_snd).continuousOn continuousOn_id
    continuousOn_const

/-- **Increment variance bound** for the four-parameter family. -/
theorem kernelCov2_nuQ_le (q q' : Fin 4 → ℝ) :
    kernelCov2 neumannH (nuQ q, nuQ q') (nuQ q, nuQ q') ≤
      4 * (|rad q - rad q'| + ‖cen q - cen q'‖ + |sm q - sm q'|) / min (rad q) (rad q') := by
  set B := 2 * (|rad q - rad q'| + ‖cen q - cen q'‖ + |sm q - sm q'|) / min (rad q) (rad q')
    with hB
  simp only [kernelCov2, kernelCov_nuQ]
  have hi : ∀ a b, Integrable (PiQ a) (nuQ b) := fun a b => integrable_nuQ (continuousOn_PiQ a) b
  have hD : ∀ b, |∫ x, PiQ q x ∂nuQ b - ∫ x, PiQ q' x ∂nuQ b| ≤ B := by
    intro b
    rw [← integral_sub (hi q b) (hi q' b)]
    have := norm_integral_le_of_norm_le_const (μ := nuQ b) (f := fun x => PiQ q x - PiQ q' x)
      (C := B) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_PiQ_sub_le q q' x)
    simpa [Real.norm_eq_abs] using this
  have h1 := hD q
  have h2 := hD q'
  rw [abs_le] at h1 h2
  have : 4 * (|rad q - rad q'| + ‖cen q - cen q'‖ + |sm q - sm q'|) / min (rad q) (rad q') =
      B + B := by rw [hB]; ring
  linarith [h1.2, h2.1]

/-! ## 3. Lipschitz bounds for the parameters on boxes -/

open KolmD

theorem abs_exp_sub_exp_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (le_of_not_ge hab)
  rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hab)), abs_of_nonneg (sub_nonneg.2 hab)]
  have e : Real.exp a * Real.exp (b - a) = Real.exp b := by rw [← Real.exp_add]; ring_nf
  have h2 : 1 - Real.exp (b - a) ≤ a - b := by linarith [Real.add_one_le_exp (b - a)]
  have h3 : 0 ≤ 1 - Real.exp (b - a) := by
    linarith [Real.exp_le_one_iff.2 (by linarith : b - a ≤ 0)]
  calc Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b - a)) := by rw [mul_sub, e]; ring
    _ ≤ Real.exp M * (a - b) := mul_le_mul (Real.exp_le_exp.2 ha) h2 h3 (Real.exp_pos _).le

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith

theorem rad_ge {R : ℕ} {q : Fin 4 → ℝ} (hq : q ∈ boxD R) : Real.exp (-R) ≤ rad q := by
  apply Real.exp_le_exp.2
  have h := abs_le.1 (hq 2)
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h1 := log_two_le_one
  nlinarith

theorem param_lip {R : ℕ} {q q' : Fin 4 → ℝ} (hq : q ∈ boxD R) (hq' : q' ∈ boxD R) :
    |rad q - rad q'| + ‖cen q - cen q'‖ + |sm q - sm q'| ≤ (Real.exp R + 3) * ‖q - q'‖ := by
  have hi : ∀ i, |q i - q' i| ≤ ‖q - q'‖ := fun i => by
    simpa using norm_le_pi_norm (q - q') i
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h1 := log_two_le_one
  have hM : ∀ p ∈ boxD (d := 4) R, Real.log 2 * p 2 ≤ R := fun p hp => by
    have := abs_le.1 (hp 2); nlinarith
  have hr : |rad q - rad q'| ≤ Real.exp R * ‖q - q'‖ := by
    refine (abs_exp_sub_exp_le (hM q hq) (hM q' hq')).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    rw [← mul_sub, abs_mul, abs_of_pos h2]
    nlinarith [hi 2, abs_nonneg (q 2 - q' 2)]
  have hc : ‖cen q - cen q'‖ ≤ 2 * ‖q - q'‖ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (cen q - cen q').re = q 0 - q' 0 := rfl
    have e2 : (cen q - cen q').im = |q 1| - |q' 1| := rfl
    rw [e1, e2]
    linarith [hi 0, hi 1, abs_abs_sub_abs_le (q 1) (q' 1)]
  have hs : |sm q - sm q'| ≤ ‖q - q'‖ := (abs_abs_sub_abs_le _ _).trans (hi 3)
  linarith

theorem kernelCov2_nuQ_le_box {R : ℕ} {q q' : Fin 4 → ℝ} (hq : q ∈ boxD R) (hq' : q' ∈ boxD R) :
    kernelCov2 neumannH (nuQ q, nuQ q') (nuQ q, nuQ q') ≤
      4 * (Real.exp R + 3) * Real.exp R * ‖q - q'‖ := by
  refine (kernelCov2_nuQ_le q q').trans ?_
  have hm : Real.exp (-R) ≤ min (rad q) (rad q') := le_min (rad_ge hq) (rad_ge hq')
  have hpos : 0 < Real.exp (-(R : ℝ)) := Real.exp_pos _
  have hnum : 0 ≤ 4 * (|rad q - rad q'| + ‖cen q - cen q'‖ + |sm q - sm q'|) := by positivity
  calc 4 * (|rad q - rad q'| + ‖cen q - cen q'‖ + |sm q - sm q'|) / min (rad q) (rad q')
      ≤ 4 * (|rad q - rad q'| + ‖cen q - cen q'‖ + |sm q - sm q'|) / Real.exp (-R) :=
        div_le_div_of_nonneg_left hnum hpos hm
    _ ≤ 4 * ((Real.exp R + 3) * ‖q - q'‖) / Real.exp (-R) :=
        div_le_div_of_nonneg_right (by linarith [param_lip hq hq']) hpos.le
    _ = 4 * (Real.exp R + 3) * Real.exp R * ‖q - q'‖ := by
        rw [Real.exp_neg]; field_simp

/-! ## 4. Gaussian moments -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem map_nuQ_diff_eq_gaussianReal (hX : IsFreeGFFModConstH X P) (q q' : Fin 4 → ℝ) :
    P.map (fun ω => X ω (nuQ q) - X ω (nuQ q')) =
      gaussianReal 0 (kernelCov2 neumannH (nuQ q, nuQ q') (nuQ q, nuQ q')).toNNReal := by
  have hadz := isAdmissibleH_nuQ q
  have hadw := isAdmissibleH_nuQ q'
  have hmass : (nuQ q) univ = (nuQ q') univ := by simp [measure_univ]
  have hG : HasGaussianLaw (fun ω => X ω (nuQ q) - X ω (nuQ q')) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(nuQ q, nuQ q'), hadz, hadw, hmass⟩
  have hm : AEMeasurable (fun ω => X ω (nuQ q) - X ω (nuQ q')) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hc : P[fun ω => X ω (nuQ q) - X ω (nuQ q')] = 0 := hX.centered _ _ hadz hadw hmass
  have hcov : cov[fun ω => X ω (nuQ q) - X ω (nuQ q'),
      fun ω => X ω (nuQ q) - X ω (nuQ q'); P] =
      kernelCov2 neumannH (nuQ q, nuQ q') (nuQ q, nuQ q') :=
    hX.covariance_eq (nuQ q, nuQ q') (nuQ q, nuQ q') hadz hadw hmass hadz hadw hmass
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

theorem integrable_abs_pow16_gaussianReal (v : NNReal) :
    Integrable (fun x : ℝ => |x| ^ 16) (gaussianReal 0 v) := by
  have hmem : MemLp (fun x : ℝ => x) ((16 : ℕ) : NNReal) (gaussianReal 0 v) :=
    memLp_id_gaussianReal 16
  have hint : Integrable (fun x : ℝ => ‖x‖ ^ 16) (gaussianReal 0 v) := hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

theorem integral_abs_pow16_gaussianReal (v : NNReal) :
    ∫ x, |x| ^ 16 ∂(gaussianReal 0 v) = (v : ℝ) ^ 8 * gaussianAbsMoment 16 := by
  have hv0 : (0 : ℝ) ≤ v := v.coe_nonneg
  have hcsq : Real.sqrt (v : ℝ) ^ 2 = v := Real.sq_sqrt hv0
  have hmap : gaussianReal (0 : ℝ) v =
      (gaussianReal (0 : ℝ) 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      push_cast
      rw [hcsq]
      ring
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, |Real.sqrt v * x| ^ 16 = (v : ℝ) ^ 8 * |x| ^ 16 := by
    intro x
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      show Real.sqrt (v : ℝ) ^ 16 = (Real.sqrt (v : ℝ) ^ 2) ^ 8 by ring, hcsq]
  simp_rw [hpt]
  rw [integral_const_mul]
  rfl

theorem lintegral_pow16_of_map_eq {U : Ω → ℝ} (hU : Measurable U) {v : NNReal}
    (hlaw : P.map U = gaussianReal 0 v) :
    ∫⁻ ω, ENNReal.ofReal (|U ω| ^ 16) ∂P =
      ENNReal.ofReal ((v : ℝ) ^ 8 * gaussianAbsMoment 16) := by
  have hi := integrable_abs_pow16_gaussianReal v
  rw [← hlaw] at hi
  rw [← integral_abs_pow16_gaussianReal, ← hlaw,
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
  exact (lintegral_map (f := fun x : ℝ => ENNReal.ofReal (|x| ^ 16))
    (Measurable.ennreal_ofReal (by fun_prop)) hU).symm

theorem momentBound_nuQ (hX : IsFreeGFFModConstH X P) (R : ℕ) :
    MomentBoundD (fun q ω => X ω (nuQ q)) P
      ((4 * (Real.exp R + 3) * Real.exp R) ^ 8 * gaussianAbsMoment 16) R := by
  intro q hq q' hq'
  rw [lintegral_pow16_of_map_eq (U := fun ω => X ω (nuQ q) - X ω (nuQ q'))
    ((hX.measurable_coord _).sub (hX.measurable_coord _))
    (map_nuQ_diff_eq_gaussianReal hX q q')]
  apply ENNReal.ofReal_le_ofReal
  set L := 4 * (Real.exp R + 3) * Real.exp R with hL
  have hkb := kernelCov2_nuQ_le_box hq hq'
  have hnn : 0 ≤ L * ‖q - q'‖ := by positivity
  have hv : ((kernelCov2 neumannH (nuQ q, nuQ q') (nuQ q, nuQ q')).toNNReal : ℝ) ≤
      L * ‖q - q'‖ := by
    rw [Real.coe_toNNReal']; exact max_le hkb hnn
  have h8 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 8
  calc _ ≤ (L * ‖q - q'‖) ^ 8 * gaussianAbsMoment 16 :=
        mul_le_mul_of_nonneg_right h8 (gaussianAbsMoment_nonneg 16)
    _ = L ^ 8 * gaussianAbsMoment 16 * ‖q - q'‖ ^ 8 := by ring

/-! ## 5. Coordinates `(w, r, ρ) ↦ q` -/

/-- The parameter point of the circle `(w, r)` smoothed at radius `ρ`. -/
def pr (w : ℂ) (r ρ : ℝ) : Fin 4 → ℝ := ![w.re, w.im, Real.log r / Real.log 2, ρ]

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem cen_pr {w : ℂ} (hw : w ∈ Hbar) (r ρ : ℝ) : cen (pr w r ρ) = w := by
  show (⟨w.re, |w.im|⟩ : ℂ) = w
  exact Complex.ext rfl (abs_of_nonneg (show 0 ≤ w.im from hw))

theorem rad_pr (w : ℂ) {r : ℝ} (hr : 0 < r) (ρ : ℝ) : rad (pr w r ρ) = r := by
  show Real.exp (Real.log 2 * (Real.log r / Real.log 2)) = r
  rw [mul_div_cancel₀ _ log_two_pos.ne', Real.exp_log hr]

theorem sm_pr (w : ℂ) (r : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : sm (pr w r ρ) = ρ := by
  show |ρ| = ρ
  exact abs_of_nonneg hρ

theorem nuQ_pr {w : ℂ} (hw : w ∈ Hbar) {r : ℝ} (hr : 0 < r) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    nuQ (pr w r ρ) = (foldedCircle w r).bind fun u => foldedCircle u ρ := by
  unfold nuQ; rw [cen_pr hw, rad_pr w hr, sm_pr w r hρ]

theorem nuQ_pr_zero {w : ℂ} (hw : w ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    nuQ (pr w r 0) = foldedCircle w r := by
  rw [nuQ_of_sm_zero (sm_pr w r le_rfl), cen_pr hw, rad_pr w hr]

theorem continuousOn_pr :
    ContinuousOn (fun p : (ℂ × ℝ) × ℝ => pr p.1.1 p.1.2 p.2) {p | 0 < p.1.2} := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · show ContinuousOn (fun p : (ℂ × ℝ) × ℝ => p.1.1.re) _
    exact (Complex.continuous_re.comp (continuous_fst.comp continuous_fst)).continuousOn
  · show ContinuousOn (fun p : (ℂ × ℝ) × ℝ => p.1.1.im) _
    exact (Complex.continuous_im.comp (continuous_fst.comp continuous_fst)).continuousOn
  · show ContinuousOn (fun p : (ℂ × ℝ) × ℝ => Real.log p.1.2 / Real.log 2) _
    exact ((Real.continuousOn_log.comp (continuous_snd.comp continuous_fst).continuousOn
      fun p (hp : 0 < p.1.2) => show p.1.2 ∈ ({0}ᶜ : Set ℝ) from hp.ne').div_const _)
  · show ContinuousOn (fun p : (ℂ × ℝ) × ℝ => p.2) _
    exact continuous_snd.continuousOn

theorem dyadicRound_intCast (n : ℕ) (m : ℤ) : dyadicRound n (m : ℝ) = m := by
  unfold dyadicRound
  rw [show (2 : ℝ) ^ n * m = ((2 ^ n * m : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
  push_cast
  field_simp

theorem log_radius_div (k : ℕ) : Real.log (radius k) / Real.log 2 = ((-(k : ℤ) : ℤ) : ℝ) := by
  rw [radius, Real.log_pow, Real.log_inv]
  field_simp [log_two_pos.ne']
  push_cast; ring

theorem rndD_pr (n k : ℕ) (z : ℂ) :
    rndD n (pr z (radius k) 0) = pr (dyadicRoundC n z) (radius k) 0 := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · show dyadicRound n (Real.log (radius k) / Real.log 2) = Real.log (radius k) / Real.log 2
    rw [log_radius_div, dyadicRound_intCast]
  · show dyadicRound n 0 = 0
    simpa using dyadicRound_intCast n 0

theorem continuous_pr_fst (r ρ : ℝ) : Continuous fun u : ℂ => pr u r ρ := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · show Continuous fun u : ℂ => u.re
    exact Complex.continuous_re
  · show Continuous fun u : ℂ => u.im
    exact Complex.continuous_im
  · exact continuous_const
  · exact continuous_const

/-! ## 6. Locally uniform convergence from joint continuity -/

theorem tluo_of_continuousOn {Φ : (ℂ × ℝ) × ℝ → ℝ}
    (hΦ : ContinuousOn Φ ((Hbar ×ˢ Ioi 0) ×ˢ Ici 0)) :
    TendstoLocallyUniformlyOn (fun ρ p => Φ (p, ρ)) (fun p => Φ (p, 0)) (𝓝[>] 0)
      (Hbar ×ˢ Ioi 0) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  have hx2 : 0 < x.2 := hx.2
  set K : Set (ℂ × ℝ) := (closedBall x.1 1 ∩ Hbar) ×ˢ Icc (x.2 / 2) (x.2 + 1) with hK
  have hKc : IsCompact K :=
    ((isCompact_closedBall _ _).inter_right isClosed_Hbar).prod isCompact_Icc
  have hKS : K ⊆ Hbar ×ˢ Ioi 0 := fun p hp =>
    ⟨hp.1.2, lt_of_lt_of_le (by linarith) hp.2.1⟩
  have hKn : K ∈ 𝓝[Hbar ×ˢ Ioi 0] x := by
    rw [mem_nhdsWithin]
    refine ⟨ball x.1 1 ×ˢ Ioo (x.2 / 2) (x.2 + 1), isOpen_ball.prod isOpen_Ioo,
      ⟨mem_ball_self one_pos, by constructor <;> linarith⟩, ?_⟩
    rintro p ⟨⟨h1, h2⟩, h3, -⟩
    exact ⟨⟨ball_subset_closedBall h1, h3⟩, h2.1.le, h2.2.le⟩
  have hKI : IsCompact (K ×ˢ Icc (0 : ℝ) 1) := hKc.prod isCompact_Icc
  have hKIS : K ×ˢ Icc (0 : ℝ) 1 ⊆ (Hbar ×ˢ Ioi 0) ×ˢ Ici 0 := fun p hp =>
    ⟨hKS hp.1, hp.2.1⟩
  have huc := hKI.uniformContinuousOn_of_continuous (hΦ.mono hKIS)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  refine ⟨K, hKn, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min δ 1 from lt_min hδ one_pos)] with ρ hρ y hy
  have h1 : (y, (0 : ℝ)) ∈ K ×ˢ Icc (0 : ℝ) 1 := ⟨hy, le_rfl, zero_le_one⟩
  have h2 : (y, ρ) ∈ K ×ˢ Icc (0 : ℝ) 1 := ⟨hy, hρ.1.le, (hρ.2.trans_le (min_le_right _ _)).le⟩
  refine hδ' _ h1 _ h2 ?_
  rw [Prod.dist_eq, dist_self, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hρ.1]
  exact max_lt hδ (hρ.2.trans_le (min_le_left _ _))

/-! ## 7. Assembly -/

theorem eqOn_of_dense {S D : Set ((ℂ × ℝ) × ℝ)} (hDS : D ⊆ S) (hSD : S ⊆ closure D)
    {f g : (ℂ × ℝ) × ℝ → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S) (h : EqOn f g D) :
    EqOn f g S := by
  intro p hp
  obtain ⟨u, huD, hu⟩ := mem_closure_iff_seq_limit.1 (hSD hp)
  have hu' : Tendsto u atTop (𝓝[S] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall fun n => hDS (huD n)⟩
  have h1 := (hf p hp).tendsto.comp hu'
  have h2 := (hg p hp).tendsto.comp hu'
  have e : (f ∘ u) = (g ∘ u) := funext fun n => h (huD n)
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

/-- **M4-R3: every-circle regularity of the free GFF.** Almost every sample of a
free-boundary GFF modulo constants is a regular sample. -/
theorem ae_isRegularSample [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, IsRegularSample (X ω) := by
  classical
  set V : (Fin 4 → ℝ) → Ω → ℝ := fun q ω => X ω (nuQ q) with hV
  have hVm : ∀ q, AEMeasurable (V q) P := fun q => (hX.measurable_coord _).aemeasurable
  obtain ⟨W, hWc, hWV, hWlim⟩ := exists_continuous_modification_D (d := 4) le_rfl hVm
    fun R => ⟨_, mul_nonneg (pow_nonneg (by positivity) 8) (gaussianAbsMoment_nonneg 16),
      momentBound_nuQ hX R⟩
  -- the sets of parameters
  set S : Set (ℂ × ℝ) := Hbar ×ˢ Ioi 0 with hS
  set S3 : Set ((ℂ × ℝ) × ℝ) := S ×ˢ Ioi 0 with hS3
  have hpr3 : ∀ p ∈ S3, (0 : ℝ) < p.1.2 := fun p hp => hp.1.2
  have hWpr : ∀ ω, ContinuousOn (fun p : (ℂ × ℝ) × ℝ => W (pr p.1.1 p.1.2 p.2) ω)
      {p | 0 < p.1.2} := fun ω => (hWc ω).comp_continuousOn continuousOn_pr
  -- the smoothed witness agrees with `W` almost surely at each point
  have hpt : ∀ p ∈ S3, ∀ᵐ ω ∂P, ∫ u, W (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2 =
      W (pr p.1.1 p.1.2 p.2) ω := by
    rintro ⟨⟨w, r⟩, ρ⟩ ⟨⟨hw, hr⟩, hρ⟩
    simp only [mem_Ioi] at hr hρ
    show ∀ᵐ ω ∂P, ∫ u, W (pr u ρ 0) ω ∂foldedCircle w r = W (pr w r ρ) ω
    have hYc : ∀ ω, ContinuousOn (fun u => W (pr u ρ 0) ω - W (pr w ρ 0) ω) Hbar := fun ω =>
      (((hWc ω).comp (continuous_pr_fst ρ 0)).sub continuous_const).continuousOn
    have hY : ∀ u ∈ Hbar, (fun ω => W (pr u ρ 0) ω - W (pr w ρ 0) ω) =ᵐ[P]
        fun ω => X ω (foldedCircle u ρ) - X ω (foldedCircle w ρ) := by
      intro u hu
      filter_upwards [hWV (pr u ρ 0), hWV (pr w ρ 0)] with ω h1 h2
      simp only [h1, h2, hV, nuQ_pr_zero hu hρ, nuQ_pr_zero hw hρ]
    have hF := integral_fcAvg_ae_eq_bind_real hX hρ hw hYc hY (foldedCircle w r)
      (isCompact_ballH (‖w‖ + r)) inter_subset_right (foldedCircle_support hr.le le_rfl)
    filter_upwards [hF, hWV (pr w ρ 0), hWV (pr w r ρ)] with ω h1 h2 h3
    have hint : Integrable (fun u => W (pr u ρ 0) ω) (foldedCircle w r) :=
      RegClosure.integrable_fc ((hWc ω).comp (continuous_pr_fst ρ 0)).continuousOn w hr.le
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ,
      one_smul, measure_univ, one_smul] at h1
    simp only [hV] at h2 h3
    rw [nuQ_pr_zero hw hρ] at h2
    rw [h3, nuQ_pr hw hr hρ.le]
    linarith
  -- a countable dense set of parameters
  obtain ⟨D, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S3
  have hall : ∀ᵐ ω ∂P, ∀ p ∈ D, ∫ u, W (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2 =
      W (pr p.1.1 p.1.2 p.2) ω :=
    (eventually_countable_ball hDc).2 fun p hp => hpt p (hDS hp)
  filter_upwards [hWlim, hall] with ω hlim hD
  -- the witness
  set F : ℂ × ℝ → ℝ := fun q => W (pr q.1 q.2 0) ω with hF
  have hFc : ContinuousOn F S :=
    (hWpr ω).comp (continuous_id.prodMk continuous_const).continuousOn fun q hq => hq.2
  -- the smoothed witness equals `W` everywhere on `S3`
  have hG : ContinuousOn (fun p : (ℂ × ℝ) × ℝ =>
      ∫ u, W (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2) S3 := by
    have hH : ContinuousOn (fun q : ((ℂ × ℝ) × ℝ) × ℂ => W (pr q.2 q.1.2 0) ω) (S3 ×ˢ Hbar) := by
      have hm : Continuous fun q : ((ℂ × ℝ) × ℝ) × ℂ => ((q.2, q.1.2), (0 : ℝ)) := by fun_prop
      exact (hWpr ω).comp hm.continuousOn fun q hq => (show (0 : ℝ) < q.1.2 from hq.1.2)
    exact RegClosure.continuousOn_integral_fc (P := (ℂ × ℝ) × ℝ)
      (H := fun p u => W (pr u p.2 0) ω) (c := fun p => p.1.1) (r := fun p => p.1.2) hH
      (continuous_fst.comp continuous_fst).continuousOn
      (continuous_snd.comp continuous_fst).continuousOn
  have hEq : EqOn (fun p : (ℂ × ℝ) × ℝ => ∫ u, W (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2)
      (fun p => W (pr p.1.1 p.1.2 p.2) ω) S3 :=
    eqOn_of_dense hDS hSD hG ((hWpr ω).mono fun p hp => hpr3 p hp) fun p hp => hD p hp
  refine ⟨F, hFc, fun k z hz => ?_, ?_⟩
  · -- clause (i)
    have h := hlim (pr z (radius k) 0)
    simp only [rndD_pr, hV] at h
    have e : ∀ n, nuQ (pr (dyadicRoundC n z) (radius k) 0) =
        foldedCircle (dyadicRoundC n z) (radius k) := fun n =>
      nuQ_pr_zero (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k)
    simp only [e] at h
    exact h
  · -- clause (ii)
    have hΦ : ContinuousOn (fun p : (ℂ × ℝ) × ℝ => W (pr p.1.1 p.1.2 p.2) ω)
        (S ×ˢ Ici 0) := (hWpr ω).mono fun p hp => hp.1.2
    refine RegClosure.tluo_of_dist_le (tluo_of_continuousOn hΦ) ?_
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
    have := hEq (show (q, ρ) ∈ S3 from ⟨hq, hρ⟩)
    simp only at this
    simp only [hF, this, le_refl]

end RegSample
end QuantumZipper
