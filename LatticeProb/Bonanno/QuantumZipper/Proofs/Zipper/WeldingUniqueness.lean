/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.WeldingUniqueness at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Blueprint.ComplexAnalysis
import LatticeProb.Bonanno.QuantumZipper.Analysis.Removability
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseHolo
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Deterministic conformal-welding uniqueness (blueprint node A3)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 (proof of
Theorem 1.4). If two reverse Loewner hulls are simple arcs with the same welding homeomorphism,
and the (reflected) arc is conformally removable, then the two reverse Loewner maps coincide on
`ℍ`, hence so do the hulls.

The argument: let `F, F'` be the Carathéodory extensions of `revMap W T`, `revMap W' T'` to `ℍ̄`
(`Blueprint.RevMapCaratheodory`). Since the weldings agree, `ψ := F' ∘ F⁻¹` is well defined on
`ℍ̄`; it is continuous because `F` is a proper, hence closed, map. Reflection gives a
homeomorphism `Ψ` of `ℂ`, holomorphic off `K ∪ K̄ ∪ ℝ`, hence (Painlevé,
`painleveRealLine`, proved here from Morera's theorem) off `K ∪ K̄`. Removability makes `Ψ` entire; the hydrodynamic
normalization makes `Ψ - id` bounded, so Liouville and `Ψ 0 = 0` give `Ψ = id`.
-/

noncomputable section

open Set Filter Complex Topology
open scoped ComplexConjugate Interval

namespace QuantumZipper

namespace WeldingUniqueness

theorem wu_isOpen_H : IsOpen H := isOpen_lt continuous_const Complex.continuous_im

theorem wu_isClosed_Hbar : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im

theorem wu_H_subset_Hbar : H ⊆ Hbar := fun z hz =>
  show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from hz)

/-! ### The far-field estimate for the reverse Loewner map -/

theorem revSol_norm_gt_half {W : ℝ → ℝ} {z : ℂ} {T M : ℝ} {u : ℝ → ℂ}
    (hu : IsReverseSol W z T u) (hM : ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ M)
    (hz : 4 * (M + T + 1) ≤ ‖z‖) : ∀ s ∈ Icc (0 : ℝ) T, ‖z‖ / 2 < ‖u s‖ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨s₁, hs₁, hs₁'⟩ := hcon
  have hT : 0 ≤ T := hs₁.1.trans hs₁.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hzpos : 0 < ‖z‖ := by linarith
  set S : Set ℝ := Icc (0 : ℝ) T ∩ u ⁻¹' {w | ‖w‖ ≤ ‖z‖ / 2} with hSdef
  have hSc : IsClosed S :=
    hu.1.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_le continuous_norm continuous_const)
  have hSne : S.Nonempty := ⟨s₁, hs₁, hs₁'⟩
  have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  have hs₀ : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  set s₀ := sInf S
  have hlt : ∀ r ∈ Icc (0 : ℝ) T, r < s₀ → ‖z‖ / 2 < ‖u r‖ := fun r hr hrs => by
    by_contra h
    push_neg at h
    exact absurd (csInf_le hSbdd ⟨hr, h⟩) (not_le.2 hrs)
  have heq := (hu.2 s₀ hs₀.1).2
  have hint : ‖∫ r in (0 : ℝ)..s₀, 2 / u r‖ ≤ 4 / ‖z‖ * |s₀ - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [(Set.countable_singleton s₀).ae_notMem MeasureTheory.volume] with r hr hrI
    rw [Set.uIoc_of_le hs₀.1.1] at hrI
    have hrs : r < s₀ := lt_of_le_of_ne hrI.2 (Set.mem_singleton_iff.not.1 hr)
    have h1 := hlt r ⟨hrI.1.le, hrI.2.trans hs₀.1.2⟩ hrs
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    calc 2 / ‖u r‖ ≤ 2 / (‖z‖ / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) h1.le
      _ = 4 / ‖z‖ := by field_simp; ring
  have hW : ‖((W s₀ : ℝ) : ℂ)‖ ≤ M := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s₀ hs₀.1
  have hlow : ‖z‖ - M - 4 / ‖z‖ * |s₀ - 0| ≤ ‖u s₀‖ := by
    rw [heq]
    have h1 := norm_sub_norm_le z (z - (W s₀ : ℂ) - ∫ r in (0 : ℝ)..s₀, 2 / u r)
    have h2 : z - (z - (W s₀ : ℂ) - ∫ r in (0 : ℝ)..s₀, 2 / u r) =
        (W s₀ : ℂ) + ∫ r in (0 : ℝ)..s₀, 2 / u r := by ring
    rw [h2] at h1
    have h3 := norm_add_le ((W s₀ : ℂ)) (∫ r in (0 : ℝ)..s₀, 2 / u r)
    linarith
  have hs0T : |s₀ - 0| ≤ T := by
    rw [sub_zero, abs_of_nonneg hs₀.1.1]; exact hs₀.1.2
  have h4 : 4 / ‖z‖ * |s₀ - 0| ≤ T := by
    have : 4 / ‖z‖ ≤ 1 := by rw [div_le_one hzpos]; linarith
    calc 4 / ‖z‖ * |s₀ - 0| ≤ 1 * T :=
          mul_le_mul this hs0T (abs_nonneg _) zero_le_one
      _ = T := one_mul T
  have h5 : ‖u s₀‖ ≤ ‖z‖ / 2 := hs₀.2
  linarith

/-- The far-field estimate: `revMap W T z = z - W T + O(1/|z|)` uniformly on `ℍ`. -/
theorem norm_revMap_sub_far {W : ℝ → ℝ} (hW : Continuous W) {T M : ℝ} (hT : 0 ≤ T)
    (hM : ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ M) {z : ℂ} (hz : z ∈ H) (hzR : 4 * (M + T + 1) ≤ ‖z‖) :
    ‖revMap W T z - (z - W T)‖ ≤ 4 * T / ‖z‖ := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hzpos : 0 < ‖z‖ := by linarith
  have hb := revSol_norm_gt_half hu hM hzR
  rw [revMap_eq W hW z hT le_rfl hu, (hu.2 T ⟨hT, le_rfl⟩).2]
  have : z - (W T : ℂ) - (∫ r in (0 : ℝ)..T, 2 / u r) - (z - (W T : ℂ)) =
      -∫ r in (0 : ℝ)..T, 2 / u r := by ring
  rw [this, norm_neg]
  calc ‖∫ r in (0 : ℝ)..T, 2 / u r‖ ≤ 4 / ‖z‖ * |T - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro r hr
        rw [Set.uIoc_of_le hT] at hr
        have h1 := hb r ⟨hr.1.le, hr.2⟩
        rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
        calc 2 / ‖u r‖ ≤ 2 / (‖z‖ / 2) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) h1.le
          _ = 4 / ‖z‖ := by field_simp; ring
    _ = 4 * T / ‖z‖ := by rw [sub_zero, abs_of_nonneg hT]; ring

theorem exists_far_bound_revMap {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C R : ℝ, ∀ z ∈ H, R ≤ ‖z‖ → ‖revMap W T z - z‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hM' : ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ M := fun s hs => by
    simpa [Real.norm_eq_abs] using hM s hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0 ⟨le_rfl, hT⟩)
  refine ⟨T + M, 4 * (M + T + 1), fun z hz hzR => ?_⟩
  have hzpos : 0 < ‖z‖ := by linarith
  have h1 := norm_revMap_sub_far hW hT hM' hz hzR
  have h2 : 4 * T / ‖z‖ ≤ T := by
    rw [div_le_iff₀ hzpos]; nlinarith
  have h3 : revMap W T z - z = (revMap W T z - (z - W T)) + (-(W T : ℂ)) := by ring
  rw [h3]
  calc ‖(revMap W T z - (z - W T)) + (-(W T : ℂ))‖
      ≤ ‖revMap W T z - (z - W T)‖ + ‖-(W T : ℂ)‖ := norm_add_le _ _
    _ ≤ T + M := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
        linarith [hM' T ⟨hT, le_rfl⟩]

/-- Second-order far-field estimate: `revMap W T z = z - W T - 2T/z + O(1/|z|²)` on `ℍ`. -/
theorem norm_revMap_sub_far2 {W : ℝ → ℝ} (hW : Continuous W) {T M : ℝ} (hT : 0 ≤ T)
    (hM : ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ M) {z : ℂ} (hz : z ∈ H) (hzR : 4 * (M + T + 1) ≤ ‖z‖) :
    ‖revMap W T z - (z - W T) + 2 * T / z‖ ≤ 4 * (M + T) / ‖z‖ ^ 2 * T := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hb := revSol_norm_gt_half hu hM hzR
  have hu0 : ∀ r ∈ Icc (0 : ℝ) T, u r ≠ 0 := fun r hr h => by
    have := hb r hr; rw [h, norm_zero] at this; linarith
  have hdiff : ∀ r ∈ Icc (0 : ℝ) T, ‖2 / u r - 2 / z‖ ≤ 4 * (M + T) / ‖z‖ ^ 2 := by
    intro r hr
    have hur := hb r hr
    have hzu : ‖z - u r‖ ≤ M + T := by
      rw [(hu.2 r hr).2]
      have h1 : z - (z - (W r : ℂ) - ∫ s in (0 : ℝ)..r, 2 / u s) =
          (W r : ℂ) + ∫ s in (0 : ℝ)..r, 2 / u s := by ring
      rw [h1]
      have hI : ‖∫ s in (0 : ℝ)..r, 2 / u s‖ ≤ 4 / ‖z‖ * |r - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [Set.uIoc_of_le hr.1] at hs
        have h2 := hb s ⟨hs.1.le, hs.2.trans hr.2⟩
        rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
        calc 2 / ‖u s‖ ≤ 2 / (‖z‖ / 2) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) h2.le
          _ = 4 / ‖z‖ := by field_simp; ring
      have h3 : 4 / ‖z‖ * |r - 0| ≤ T := by
        have : 4 / ‖z‖ ≤ 1 := by rw [div_le_one hzpos]; linarith
        rw [sub_zero, abs_of_nonneg hr.1]
        calc 4 / ‖z‖ * r ≤ 1 * T := mul_le_mul this hr.2 hr.1 zero_le_one
          _ = T := one_mul T
      have h4 := norm_add_le (W r : ℂ) (∫ s in (0 : ℝ)..r, 2 / u s)
      rw [Complex.norm_real, Real.norm_eq_abs] at h4
      linarith [hM r hr]
    have heq : 2 / u r - 2 / z = 2 * (z - u r) / (u r * z) := by
      field_simp [hu0 r hr, hz0]
    rw [heq, norm_div, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
    calc 2 * ‖z - u r‖ / (‖u r‖ * ‖z‖) ≤ 2 * (M + T) / (‖z‖ / 2 * ‖z‖) :=
          div_le_div₀ (by positivity) (by linarith) (by positivity)
            (mul_le_mul_of_nonneg_right hur.le (norm_nonneg _))
      _ = 4 * (M + T) / ‖z‖ ^ 2 := by field_simp; ring
  rw [revMap_eq W hW z hT le_rfl hu, (hu.2 T ⟨hT, le_rfl⟩).2]
  have hi1 : IntervalIntegrable (fun r => 2 / u r) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact continuousOn_const.div hu.1 hu0
  have hconst : (2 * T / z : ℂ) = ∫ _ in (0 : ℝ)..T, (2 / z : ℂ) := by
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]; ring
  have h5 : z - (W T : ℂ) - (∫ r in (0 : ℝ)..T, 2 / u r) - (z - (W T : ℂ)) + 2 * T / z =
      -∫ r in (0 : ℝ)..T, (2 / u r - 2 / z) := by
    rw [hconst, intervalIntegral.integral_sub hi1 intervalIntegrable_const]; ring
  rw [h5, norm_neg]
  calc ‖∫ r in (0 : ℝ)..T, (2 / u r - 2 / z)‖ ≤ 4 * (M + T) / ‖z‖ ^ 2 * |T - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro r hr
        rw [Set.uIoc_of_le hT] at hr
        exact hdiff r ⟨hr.1.le, hr.2⟩
    _ = 4 * (M + T) / ‖z‖ ^ 2 * T := by rw [sub_zero, abs_of_nonneg hT]

theorem exists_abs_drive_bound {W : ℝ → ℝ} (hW : Continuous W) (T : ℝ) :
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  exact ⟨M, fun s hs => by simpa [Real.norm_eq_abs] using hM s hs⟩

/-- The reverse Loewner map at a fixed time determines the terminal driver value and the time
(half-plane capacity), via the expansion `revMap W T z = z - W T - 2T/z + O(|z|⁻²)`. -/
theorem drive_and_time_eq_of_revMap_eq {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') (h : EqOn (revMap W' T') (revMap W T) H) :
    W T = W' T' ∧ T = T' := by
  obtain ⟨M, hM⟩ := exists_abs_drive_bound hW T
  obtain ⟨M', hM'⟩ := exists_abs_drive_bound hW' T'
  set R := max (max (4 * (M + T + 1)) (4 * (M' + T' + 1))) 1 with hR
  have hzH : ∀ y : ℝ, 0 < y → ((y : ℂ) * I) ∈ H := fun y hy => by
    show (0 : ℝ) < ((y : ℂ) * I).im; simpa using hy
  have hnorm : ∀ y : ℝ, 0 < y → ‖(y : ℂ) * I‖ = y := fun y hy => by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have hRy : ∀ y : ℝ, R ≤ y → 0 < y ∧ 4 * (M + T + 1) ≤ y ∧ 4 * (M' + T' + 1) ≤ y := by
    intro y hy
    refine ⟨lt_of_lt_of_le one_pos ((le_max_right _ _).trans hy),
      (le_max_left _ _).trans ((le_max_left _ _).trans hy),
      (le_max_right _ _).trans ((le_max_left _ _).trans hy)⟩
  have hdr : W T = W' T' := by
    have hb : ∀ y : ℝ, R ≤ y → |W T - W' T'| ≤ (4 * T + 4 * T') / y := by
      intro y hy
      obtain ⟨hy0, hy1, hy2⟩ := hRy y hy
      set z : ℂ := (y : ℂ) * I
      have e1 := norm_revMap_sub_far hW hT hM (hzH y hy0) (by rw [hnorm y hy0]; exact hy1)
      have e2 := norm_revMap_sub_far hW' hT' hM' (hzH y hy0) (by rw [hnorm y hy0]; exact hy2)
      rw [h (hzH y hy0), hnorm y hy0] at e2
      rw [hnorm y hy0] at e1
      have : ((W T - W' T' : ℝ) : ℂ) = (revMap W T z - (z - W T)) - (revMap W T z - (z - W' T')) := by
        push_cast; ring
      have h6 := norm_sub_le (revMap W T z - (z - W T)) (revMap W T z - (z - W' T'))
      rw [← this, Complex.norm_real, Real.norm_eq_abs] at h6
      calc |W T - W' T'| ≤ 4 * T' / y + 4 * T / y := by linarith
        _ = (4 * T + 4 * T') / y := by ring
    have ht : Tendsto (fun y : ℝ => (4 * T + 4 * T') / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := ge_of_tendsto ht ((eventually_ge_atTop R).mono hb)
    have h0 : |W T - W' T'| = 0 := le_antisymm this (abs_nonneg _)
    linarith [abs_eq_zero.1 h0]
  refine ⟨hdr, ?_⟩
  set C := 4 * (M + T) * T + 4 * (M' + T') * T' with hC
  have hb : ∀ y : ℝ, R ≤ y → |2 * (T - T')| ≤ C / y := by
    intro y hy
    obtain ⟨hy0, hy1, hy2⟩ := hRy y hy
    set z : ℂ := (y : ℂ) * I
    have e1 := norm_revMap_sub_far2 hW hT hM (hzH y hy0) (by rw [hnorm y hy0]; exact hy1)
    have e2 := norm_revMap_sub_far2 hW' hT' hM' (hzH y hy0) (by rw [hnorm y hy0]; exact hy2)
    rw [h (hzH y hy0), hnorm y hy0] at e2
    rw [hnorm y hy0] at e1
    have : ((2 * (T - T') : ℝ) : ℂ) / z =
        (revMap W T z - (z - W T) + 2 * T / z) - (revMap W T z - (z - W' T') + 2 * T' / z) := by
      rw [hdr]; push_cast; ring
    have h6 := norm_sub_le (revMap W T z - (z - W T) + 2 * T / z)
      (revMap W T z - (z - W' T') + 2 * T' / z)
    rw [← this, norm_div, Complex.norm_real, Real.norm_eq_abs, hnorm y hy0] at h6
    rw [div_le_iff₀ hy0] at h6
    rw [le_div_iff₀ hy0]
    have hyy : 0 < y * y := by positivity
    calc |2 * (T - T')| * y
        ≤ (‖revMap W T z - (z - W T) + 2 * T / z‖ +
            ‖revMap W T z - (z - W' T') + 2 * T' / z‖) * y * y :=
          mul_le_mul_of_nonneg_right h6 hy0.le
      _ ≤ (4 * (M + T) / y ^ 2 * T + 4 * (M' + T') / y ^ 2 * T') * (y * y) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (add_le_add e1 e2) hyy.le
      _ = C := by rw [hC]; field_simp
  have ht : Tendsto (fun y : ℝ => C / y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have := ge_of_tendsto ht ((eventually_ge_atTop R).mono hb)
  have h0 : |2 * (T - T')| = 0 := le_antisymm this (abs_nonneg _)
  have := abs_eq_zero.1 h0
  linarith

/-! ### Extension of bounds from `ℍ` to `ℍ̄` -/

theorem mem_of_Hbar_of_H {g : ℂ → ℂ} (hg : ContinuousOn g Hbar) {P : Set ℂ} (hP : IsClosed P)
    {R : ℝ} (h : ∀ z ∈ H, R ≤ ‖z‖ → g z ∈ P) {z : ℂ} (hz : z ∈ Hbar) (hzR : R < ‖z‖) :
    g z ∈ P := by
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z.im from hz) with h1 | h1
  · exact h z h1 hzR.le
  · have hc : Tendsto (fun y : ℝ => z + y * I) (𝓝[>] 0) (𝓝 z) := by
      have : Continuous (fun y : ℝ => z + y * I) := by fun_prop
      have h0 := this.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hH : ∀ᶠ y : ℝ in 𝓝[>] 0, z + y * I ∈ H := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      show 0 < (z + y * I).im
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      rw [← h1]; simpa using hy
    have hlim : Tendsto (fun y : ℝ => z + y * I) (𝓝[>] 0) (𝓝[Hbar] z) :=
      tendsto_nhdsWithin_iff.2 ⟨hc, hH.mono fun y hy => wu_H_subset_Hbar hy⟩
    have hR : ∀ᶠ y : ℝ in 𝓝[>] 0, R ≤ ‖z + y * I‖ :=
      (hc.norm).eventually_const_le hzR
    apply hP.mem_of_tendsto ((hg z hz).tendsto.comp hlim)
    filter_upwards [hH, hR] with y hy1 hy2
    exact h _ hy1 hy2

/-! ### The abstract gluing -/

/-- The boundary data of a Carathéodory extension used in the gluing. -/
structure GlueData (F : ℂ → ℂ) (a b : ℝ) (φ : ℝ → ℝ) : Prop where
  cont : ContinuousOn F Hbar
  surj : SurjOn F Hbar Hbar
  mapsH : MapsTo F H H
  zero : F a = 0
  real_iff : ∀ x : ℝ, (F x).im = 0 ↔ (x ≤ a ∨ b ≤ x)
  fiber : ∀ x ∈ Hbar, ∀ y ∈ Hbar, F x = F y ↔ (x = y ∨ Blueprint.WeldingRel a φ x y)
  far : ∃ C R : ℝ, ∀ z ∈ H, R ≤ ‖z‖ → ‖F z - z‖ ≤ C

open Classical in
/-- A choice of preimage under `F` in `ℍ̄`. -/
def glueInv (F : ℂ → ℂ) (w : ℂ) : ℂ := if h : ∃ x ∈ Hbar, F x = w then h.choose else 0

/-- The glued map `ψ = F' ∘ F⁻¹` on `ℍ̄`. -/
def glueMap (F F' : ℂ → ℂ) (w : ℂ) : ℂ := F' (glueInv F w)

/-- The Schwarz reflection of the glued map to all of `ℂ`. -/
def glueExt (F F' : ℂ → ℂ) (w : ℂ) : ℂ :=
  if 0 ≤ w.im then glueMap F F' w else conj (glueMap F F' (conj w))

theorem weldingRel_congr {a : ℝ} {φ φ' : ℝ → ℝ} (hφ : EqOn φ φ' (Icc a 0)) {x y : ℂ}
    (h : Blueprint.WeldingRel a φ x y) : Blueprint.WeldingRel a φ' x y := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, by rwa [hφ hs] at h⟩

section Glue

variable {F F' : ℂ → ℂ} {a b : ℝ} {φ φ' : ℝ → ℝ}

theorem GlueData.mapsHbar (hF : GlueData F a b φ) : MapsTo F Hbar Hbar := fun z hz =>
  mem_of_Hbar_of_H hF.cont wu_isClosed_Hbar (R := -1)
    (fun w hw _ => wu_H_subset_Hbar (hF.mapsH hw)) hz
    (lt_of_lt_of_le (by norm_num) (norm_nonneg z))

theorem GlueData.bound (hF : GlueData F a b φ) : ∃ C : ℝ, ∀ z ∈ Hbar, ‖F z - z‖ ≤ C := by
  obtain ⟨C, R, hCR⟩ := hF.far
  have hc : ContinuousOn (fun z => F z - z) Hbar := hF.cont.sub continuousOn_id
  obtain ⟨C', hC'⟩ := ((isCompact_closedBall (0 : ℂ) R).inter_left wu_isClosed_Hbar
    ).exists_bound_of_continuousOn (hc.mono inter_subset_left)
  refine ⟨max C C', fun z hz => ?_⟩
  by_cases hzR : R < ‖z‖
  · have := mem_of_Hbar_of_H hc (isClosed_le continuous_norm continuous_const) (P := {w | ‖w‖ ≤ C})
      (fun w hw hwR => hCR w hw hwR) hz hzR
    exact this.trans (le_max_left _ _)
  · push_neg at hzR
    exact (hC' z ⟨hz, by simpa using hzR⟩).trans (le_max_right _ _)

theorem glueInv_spec (hF : GlueData F a b φ) {w : ℂ} (hw : w ∈ Hbar) :
    glueInv F w ∈ Hbar ∧ F (glueInv F w) = w := by
  have h : ∃ x ∈ Hbar, F x = w := hF.surj hw
  unfold glueInv
  rw [dif_pos h]
  exact h.choose_spec

theorem glueMap_apply (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) {x : ℂ} (hx : x ∈ Hbar) : glueMap F F' (F x) = F' x := by
  obtain ⟨h1, h2⟩ := glueInv_spec hF (hF.mapsHbar hx)
  unfold glueMap
  rcases (hF.fiber _ h1 x hx).1 h2 with h | h
  · rw [h]
  · exact (hF'.fiber _ h1 x hx).2 (Or.inr (weldingRel_congr hφ h))

theorem glueMap_mem (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) {w : ℂ} (hw : w ∈ Hbar) : glueMap F F' w ∈ Hbar := by
  obtain ⟨x, hx, rfl⟩ := hF.surj hw
  rw [glueMap_apply hF hF' hφ hx]
  exact hF'.mapsHbar hx

theorem glueMap_real (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) {w : ℂ} (hw : w ∈ Hbar) (hw0 : w.im = 0) :
    (glueMap F F' w).im = 0 := by
  obtain ⟨x, hx, rfl⟩ := hF.surj hw
  rw [glueMap_apply hF hF' hφ hx]
  have hx0 : x.im = 0 := by
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ x.im from hx) with h | h
    · have := hF.mapsH h
      exact absurd hw0 (ne_of_gt this)
    · exact h.symm
  have hxr : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [hx0])
  rw [hxr] at hw0 ⊢
  exact (hF'.real_iff _).2 ((hF.real_iff _).1 hw0)

theorem glueMap_inv (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) {w : ℂ} (hw : w ∈ Hbar) :
    glueMap F' F (glueMap F F' w) = w := by
  obtain ⟨x, hx, rfl⟩ := hF.surj hw
  rw [glueMap_apply hF hF' hφ hx, glueMap_apply hF' hF (fun s hs => (hφ hs).symm) hx]

theorem glueMap_H (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) {w : ℂ} (hw : w ∈ H) : glueMap F F' w ∈ H := by
  have hm := glueMap_mem hF hF' hφ (wu_H_subset_Hbar hw)
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ (glueMap F F' w).im from hm) with h | h
  · exact h
  · have h1 := glueMap_real hF' hF (fun s hs => (hφ hs).symm) hm h.symm
    rw [glueMap_inv hF hF' hφ (wu_H_subset_Hbar hw)] at h1
    exact absurd h1 (ne_of_gt hw)

theorem glueMap_zero (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) : glueMap F F' 0 = 0 := by
  have ha : ((a : ℝ) : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ ((a : ℝ) : ℂ).im; simp
  have := glueMap_apply hF hF' hφ ha
  rw [hF.zero, hF'.zero] at this
  exact this

/-- The reflection retraction `ℂ → ℍ̄`. -/
def reflHbar (z : ℂ) : ℂ := if 0 ≤ z.im then z else conj z

theorem reflHbar_mem (z : ℂ) : reflHbar z ∈ Hbar := by
  unfold reflHbar
  split_ifs with h
  · exact h
  · show (0 : ℝ) ≤ (conj z).im
    simp only [conj_im]; push_neg at h; linarith

theorem reflHbar_of_mem {z : ℂ} (hz : z ∈ Hbar) : reflHbar z = z := if_pos hz

theorem norm_reflHbar (z : ℂ) : ‖reflHbar z‖ = ‖z‖ := by
  unfold reflHbar; split_ifs <;> simp

theorem continuous_reflHbar : Continuous reflHbar := by
  apply continuous_if_le continuous_const Complex.continuous_im continuous_id.continuousOn
    Complex.continuous_conj.continuousOn
  intro z hz
  exact (Complex.conj_eq_iff_im.2 hz.symm).symm

theorem isClosedMap_comp_reflHbar (hF : GlueData F a b φ) :
    IsClosedMap (fun z => F (reflHbar z)) := by
  have hc : Continuous (fun z => F (reflHbar z)) :=
    hF.cont.comp_continuous continuous_reflHbar reflHbar_mem
  obtain ⟨C, hC⟩ := hF.bound
  have ht : Tendsto (fun z => F (reflHbar z)) (cocompact ℂ) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    have h1 : Tendsto (fun z : ℂ => ‖z‖ - C) (Bornology.cobounded ℂ) atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_norm_cobounded_atTop
    refine tendsto_atTop_mono (fun z => ?_) h1
    have h2 := hC _ (reflHbar_mem z)
    have h3 := norm_sub_norm_le (reflHbar z) (F (reflHbar z))
    rw [norm_sub_rev (reflHbar z), norm_reflHbar] at h3
    linarith
  exact (isProperMap_iff_tendsto_cocompact.2 ⟨hc, ht⟩).isClosedMap

theorem continuousOn_glueMap (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) : ContinuousOn (glueMap F F') Hbar := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨(fun z => F (reflHbar z)) '' (Hbar ∩ F' ⁻¹' t),
    isClosedMap_comp_reflHbar hF _ (hF'.cont.preimage_isClosed_of_isClosed wu_isClosed_Hbar ht),
    ?_⟩
  ext w
  constructor
  · rintro ⟨hwt, hw⟩
    obtain ⟨x, hx, rfl⟩ := hF.surj hw
    refine ⟨⟨x, ⟨hx, ?_⟩, by simp [reflHbar_of_mem hx]⟩, hw⟩
    have : glueMap F F' (F x) ∈ t := hwt
    rwa [glueMap_apply hF hF' hφ hx] at this
  · rintro ⟨⟨x, ⟨hx, hxt⟩, rfl⟩, hw⟩
    refine ⟨?_, hw⟩
    show glueMap F F' (F (reflHbar x)) ∈ t
    rw [reflHbar_of_mem hx, glueMap_apply hF hF' hφ hx]
    exact hxt

theorem continuous_glueExt (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) : Continuous (glueExt F F') := by
  have hc := continuousOn_glueMap hF hF' hφ
  apply continuous_if_le continuous_const Complex.continuous_im hc
  · refine Complex.continuous_conj.comp_continuousOn
      (hc.comp Complex.continuous_conj.continuousOn fun z hz => ?_)
    show (0 : ℝ) ≤ (conj z).im
    simp only [conj_im]; have : z.im ≤ 0 := hz; linarith
  · intro z hz
    have hz' : conj z = z := Complex.conj_eq_iff_im.2 hz.symm
    rw [hz']
    have hr := glueMap_real hF hF' hφ (show (0 : ℝ) ≤ z.im from hz.le) hz.symm
    exact (Complex.conj_eq_iff_im.2 hr).symm

theorem glueExt_inv (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) (w : ℂ) : glueExt F' F (glueExt F F' w) = w := by
  have hφ' : EqOn φ' φ (Icc a 0) := fun s hs => (hφ hs).symm
  by_cases hw : 0 ≤ w.im
  · have hm := glueMap_mem hF hF' hφ hw
    simp only [glueExt, if_pos hw, if_pos (show 0 ≤ (glueMap F F' w).im from hm)]
    exact glueMap_inv hF hF' hφ hw
  · push_neg at hw
    have hcw : conj w ∈ H := by show (0 : ℝ) < (conj w).im; simp only [conj_im]; linarith
    have hm := glueMap_H hF hF' hφ hcw
    have hneg : ¬ (0 ≤ (conj (glueMap F F' (conj w))).im) := by
      simp only [conj_im, not_le, neg_neg_iff_pos]; exact hm
    simp only [glueExt, if_neg (not_le.2 hw), if_neg hneg, Complex.conj_conj]
    rw [glueMap_inv hF hF' hφ (wu_H_subset_Hbar hcw), Complex.conj_conj]

theorem glueExt_bound (hF : GlueData F a b φ) (hF' : GlueData F' a b φ')
    (hφ : EqOn φ φ' (Icc a 0)) : ∃ C : ℝ, ∀ w, ‖glueExt F F' w - w‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF.bound
  obtain ⟨C', hC'⟩ := hF'.bound
  have hHbar : ∀ w ∈ Hbar, ‖glueMap F F' w - w‖ ≤ C' + C := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hF.surj hw
    rw [glueMap_apply hF hF' hφ hx]
    have : F' x - F x = (F' x - x) - (F x - x) := by ring
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add (hC' x hx) (hC x hx))
  refine ⟨C' + C, fun w => ?_⟩
  by_cases hw : 0 ≤ w.im
  · simp only [glueExt, if_pos hw]; exact hHbar w hw
  · push_neg at hw
    have hcw : conj w ∈ Hbar := by
      show (0 : ℝ) ≤ (conj w).im; simp only [conj_im]; linarith
    simp only [glueExt, if_neg (not_le.2 hw)]
    have : conj (glueMap F F' (conj w)) - w = conj (glueMap F F' (conj w) - conj w) := by
      simp
    rw [this, Complex.norm_conj]
    exact hHbar _ hcw

end Glue

/-! ### Holomorphy of a map through a conformal chart -/

theorem differentiableAt_of_comp_eq {f h φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z : ℂ}
    (hz : z ∈ U) {f' : ℂ} (hf : HasStrictDerivAt f f' z) (hf' : f' ≠ 0)
    (hh : DifferentiableAt ℂ h z) (hφ : ∀ x ∈ U, φ (f x) = h x) :
    DifferentiableAt ℂ φ (f z) := by
  set g := HasStrictDerivAt.localInverse f f' z hf hf' with hgdef
  have hg : HasStrictDerivAt g f'⁻¹ (f z) := hf.to_localInverse hf'
  have hgz : g (f z) = z := (hf.eventually_left_inverse hf').self_of_nhds
  have hgU : ∀ᶠ y in 𝓝 (f z), g y ∈ U :=
    hg.hasDerivAt.continuousAt.preimage_mem_nhds (by rw [hgz]; exact hU.mem_nhds hz)
  have hfg := hf.eventually_right_inverse hf'
  have heq : φ =ᶠ[𝓝 (f z)] fun y => h (g y) := by
    filter_upwards [hgU, hfg] with y hy1 hy2
    rw [← hφ _ hy1, hy2]
  have hd : DifferentiableAt ℂ (fun y => h (g y)) (f z) := by
    have : DifferentiableAt ℂ h (g (f z)) := by rw [hgz]; exact hh
    exact this.comp (f z) hg.hasDerivAt.differentiableAt
  exact hd.congr_of_eventuallyEq heq

theorem hasStrictDerivAt_revMap {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) : HasStrictDerivAt (revMap W T) (deriv (revMap W T) z) z :=
  ((differentiableOn_revMap W hW hT).analyticAt (wu_isOpen_H.mem_nhds hz)).hasStrictDerivAt

/-! ### From the Carathéodory data to `GlueData` -/

theorem glueData_of_caratheodory {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {F : ℂ → ℂ} (hF : Blueprint.IsCaratheodoryRevExt W T F) :
    GlueData F (zeroMinus W T) (zeroPlus W T) (weldingHom W T) := by
  obtain ⟨heq, hc, hs, hz, _, hr, hfib⟩ := hF
  refine ⟨hc, hs, fun z hzH => ?_, hz, hr, hfib, ?_⟩
  · rw [heq hzH]
    exact lt_of_lt_of_le hzH (im_le_im_revMap W hW z hzH hT.le)
  · obtain ⟨C, R, h⟩ := exists_far_bound_revMap hW hT.le
    exact ⟨C, R, fun z hzH hzR => by rw [heq hzH]; exact h z hzH hzR⟩

theorem zeroMinus_nonpos (W : ℝ → ℝ) (T : ℝ) : zeroMinus W T ≤ 0 :=
  Real.sSup_nonpos fun _ hx => hx.1.le

/-! ### Painlevé's theorem for the real line (via Morera) -/

theorem clamp_avoid_zero (y₁ y₂ m t : ℝ) (hm : m = max (min y₁ y₂) (min 0 (max y₁ y₂))) :
    (t ∈ Ioo (min y₁ m) (max y₁ m) → t ≠ 0) ∧ (t ∈ Ioo (min m y₂) (max m y₂) → t ≠ 0) := by
  subst hm
  constructor <;> rintro ⟨h1, h2⟩ rfl <;> simp only [min_def, max_def] at h1 h2 <;>
    split_ifs at h1 h2 <;> linarith

theorem clamp_mem_uIcc (y₁ y₂ m : ℝ) (hm : m = max (min y₁ y₂) (min 0 (max y₁ y₂))) :
    m ∈ [[y₁, y₂]] := by
  subst hm
  rw [Set.mem_uIcc]
  simp only [min_def, max_def]
  split_ifs <;> first | (left; constructor <;> linarith) | (right; constructor <;> linarith)

end WeldingUniqueness

open WeldingUniqueness in
/-- **Painlevé's theorem for a line**, proved from Morera's theorem: the rectangle integrals of
a function continuous on `U` and holomorphic off `ℝ` vanish, since each rectangle splits along
`ℝ` into two rectangles whose interiors avoid `ℝ`. -/
theorem painleveRealLine : Blueprint.PainleveRealLine := by
  intro g U hU hc hd
  have hopen : IsOpen (U \ {z : ℂ | z.im = 0}) :=
    hU.sdiff (isClosed_eq Complex.continuous_im continuous_const)
  have hdA : ∀ v ∈ U, v.im ≠ 0 → DifferentiableAt ℂ g v := fun v hv hv0 =>
    hd.differentiableAt (hopen.mem_nhds ⟨hv, hv0⟩)
  refine (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).1 ⟨?_, hc⟩
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  set m := max (min z.im w.im) (min 0 (max z.im w.im)) with hm
  have hmem : m ∈ [[z.im, w.im]] := clamp_mem_uIcc _ _ _ hm
  have hsub1 : [[z.re, w.re]] ×ℂ [[z.im, m]] ⊆ U :=
    (inter_subset_inter (preimage_mono subset_rfl)
      (preimage_mono (uIcc_subset_uIcc left_mem_uIcc hmem))).trans hzw
  have hsub2 : [[z.re, w.re]] ×ℂ [[m, w.im]] ⊆ U :=
    (inter_subset_inter (preimage_mono subset_rfl)
      (preimage_mono (uIcc_subset_uIcc hmem right_mem_uIcc))).trans hzw
  have h1 := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn g z
    ⟨w.re, m⟩ (hc.mono hsub1) (by
      intro v hv
      apply DifferentiableAt.differentiableWithinAt
      exact hdA v (hsub1 ⟨Ioo_subset_Icc_self hv.1, Ioo_subset_Icc_self hv.2⟩)
        ((clamp_avoid_zero _ _ _ v.im hm).1 hv.2))
  have h2 := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn g
    ⟨z.re, m⟩ w (hc.mono hsub2) (by
      intro v hv
      apply DifferentiableAt.differentiableWithinAt
      exact hdA v (hsub2 ⟨Ioo_subset_Icc_self hv.1, Ioo_subset_Icc_self hv.2⟩)
        ((clamp_avoid_zero _ _ _ v.im hm).2 hv.2))
  have hint : ∀ (x : ℝ), x ∈ [[z.re, w.re]] → ∀ a b : ℝ, [[a, b]] ⊆ [[z.im, w.im]] →
      IntervalIntegrable (fun y : ℝ => g (x + y * I)) MeasureTheory.volume a b := by
    intro x hx a b hab
    apply ContinuousOn.intervalIntegrable
    refine hc.comp (by fun_prop : Continuous fun y : ℝ => (x : ℂ) + y * I).continuousOn ?_
    intro y hy
    apply hzw
    refine ⟨?_, ?_⟩
    · show (↑x + ↑y * I).re ∈ [[z.re, w.re]]; simpa using hx
    · show (↑x + ↑y * I).im ∈ [[z.im, w.im]]; simpa using hab hy
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint w.re right_mem_uIcc z.im m (uIcc_subset_uIcc left_mem_uIcc hmem))
      (hint w.re right_mem_uIcc m w.im (uIcc_subset_uIcc hmem right_mem_uIcc)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hint z.re left_mem_uIcc z.im m (uIcc_subset_uIcc left_mem_uIcc hmem))
      (hint z.re left_mem_uIcc m w.im (uIcc_subset_uIcc hmem right_mem_uIcc))]
  dsimp only at h1 h2
  simp only [smul_eq_mul] at h1 h2 ⊢
  linear_combination h1 + h2

open WeldingUniqueness

/-- **Deterministic conformal-welding uniqueness** (blueprint A3; Sheffield §1.4). Let `W, W'` be
continuous drivers with `W 0 = W' 0 = 0` and `T, T' > 0`, whose reverse hulls are simple arcs
with the same welding (`zeroMinus` and `weldingHom` on `[zeroMinus W T, 0]`), and suppose the
reflected closed arc is conformally removable. Then, given the Carathéodory extension of reverse
Loewner maps (`Blueprint.RevMapCaratheodory`), the two reverse Loewner maps agree on `ℍ`.
(Painlevé's theorem for a line is proved here, `painleveRealLine`.) -/
theorem revMap_eq_of_welding_eq (hCar : Blueprint.RevMapCaratheodory)
    {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (hK : IsSimpleCurveHull (revHull W T))
    (hK' : IsSimpleCurveHull (revHull W' T')) (hzm : zeroMinus W T = zeroMinus W' T')
    (hweld : EqOn (weldingHom W T) (weldingHom W' T') (Icc (zeroMinus W T) 0))
    (hrem : IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T))) :
    EqOn (revMap W' T') (revMap W T) H := by
  obtain ⟨F, hF⟩ := hCar W hW hW0 T hT hK
  obtain ⟨F', hF'⟩ := hCar W' hW' hW'0 T' hT' hK'
  have hFeq : EqOn F (revMap W T) H := hF.1
  have hF'eq : EqOn F' (revMap W' T') H := hF'.1
  have hwz : weldingHom W T (zeroMinus W T) = zeroPlus W T := hF.2.2.2.2.1
  have hwz' : weldingHom W' T' (zeroMinus W' T') = zeroPlus W' T' := hF'.2.2.2.2.1
  have hzp : zeroPlus W T = zeroPlus W' T' := by
    rw [← hwz, ← hwz', ← hzm]
    exact hweld ⟨le_rfl, zeroMinus_nonpos W T⟩
  have hG := glueData_of_caratheodory hW hT hF
  have hG' : GlueData F' (zeroMinus W T) (zeroPlus W T) (weldingHom W' T') := by
    rw [hzm, hzp]; exact glueData_of_caratheodory hW' hT' hF'
  -- the glued homeomorphism
  let e : ℂ ≃ₜ ℂ :=
    { toFun := glueExt F F'
      invFun := glueExt F' F
      left_inv := glueExt_inv hG hG' hweld
      right_inv := glueExt_inv hG' hG (fun s hs => (hweld hs).symm)
      continuous_toFun := continuous_glueExt hG hG' hweld
      continuous_invFun := continuous_glueExt hG' hG (fun s hs => (hweld hs).symm) }
  set K := revHull W T with hKdef
  set K₀ := closure K ∪ conj '' closure K with hK₀def
  -- holomorphy of the glued map on `ℍ \ K`
  have hdH : ∀ w ∈ H, w ∉ K → DifferentiableAt ℂ (glueExt F F') w := by
    intro w hw hwK
    have hwim : w ∈ revMap W T '' H := by
      by_contra hcon; exact hwK ⟨hw, hcon⟩
    obtain ⟨z, hz, rfl⟩ := hwim
    have hd : DifferentiableAt ℂ (glueMap F F') (revMap W T z) :=
      differentiableAt_of_comp_eq wu_isOpen_H hz (hasStrictDerivAt_revMap hW hT.le hz)
        (deriv_revMap_ne_zero W hW hT.le hz)
        ((differentiableOn_revMap W' hW' hT'.le).differentiableAt (wu_isOpen_H.mem_nhds hz))
        (fun x hx => by
          rw [← hFeq hx, glueMap_apply hG hG' hweld (wu_H_subset_Hbar hx), hF'eq hx])
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [wu_isOpen_H.mem_nhds hw] with y hy
    simp only [glueExt, if_pos (le_of_lt (show (0 : ℝ) < y.im from hy))]
  -- holomorphy off `K₀` and off the real line
  have hdoff : DifferentiableOn ℂ (glueExt F F') (K₀ᶜ \ {z | z.im = 0}) := by
    intro w ⟨hwK, hw0⟩
    have hw0' : w.im ≠ 0 := hw0
    apply DifferentiableAt.differentiableWithinAt
    rcases lt_or_gt_of_ne hw0' with hneg | hpos
    · have hcw : conj w ∈ H := by show (0 : ℝ) < (conj w).im; simp only [conj_im]; linarith
      have hcwK : conj w ∉ K := fun h =>
        hwK (Or.inr ⟨conj w, subset_closure h, Complex.conj_conj w⟩)
      have hd := (hdH _ hcw hcwK)
      have hd2 : DifferentiableAt ℂ (conj ∘ glueExt F F' ∘ conj) w := by
        have := hd.conj_conj
        rwa [Complex.conj_conj] at this
      refine hd2.congr_of_eventuallyEq ?_
      have hopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
      filter_upwards [hopen.mem_nhds hneg] with y hy
      have hy' : y.im < 0 := hy
      have hcy : 0 ≤ (conj y).im := by simp only [conj_im]; linarith
      simp only [glueExt, Function.comp, if_neg (not_le.2 hy'), if_pos hcy]
    · exact hdH w hpos fun h => hwK (Or.inl (subset_closure h))
  have hK₀c : IsOpen K₀ᶜ := hrem.1.isClosed.isOpen_compl
  have hdiffOn : DifferentiableOn ℂ e K₀ᶜ :=
    painleveRealLine _ _ hK₀c (continuous_glueExt hG hG' hweld).continuousOn hdoff
  have hdiff : Differentiable ℂ e := hrem.2 e hdiffOn
  -- Liouville
  obtain ⟨C, hC⟩ := glueExt_bound hG hG' hweld
  have hid : ∀ w, glueExt F F' w = w := by
    intro w
    have hd : Differentiable ℂ (fun w => glueExt F F' w - w) := hdiff.sub differentiable_id
    have hb : Bornology.IsBounded (range fun w => glueExt F F' w - w) := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨C, by rintro _ ⟨v, rfl⟩; exact hC v⟩
    have h1 := hd.apply_eq_apply_of_bounded hb w 0
    have h0 : glueExt F F' 0 = 0 := by
      simp only [glueExt, zero_im, le_refl, if_true]
      exact glueMap_zero hG hG' hweld
    rw [h0, sub_zero] at h1
    exact sub_eq_zero.1 h1
  intro z hz
  have h1 := hid (revMap W T z)
  have hmem : revMap W T z ∈ Hbar := by
    rw [← hFeq hz]; exact hG.mapsHbar (wu_H_subset_Hbar hz)
  simp only [glueExt, if_pos (show 0 ≤ (revMap W T z).im from hmem)] at h1
  rw [← hFeq hz, glueMap_apply hG hG' hweld (wu_H_subset_Hbar hz), hF'eq hz] at h1
  rw [hFeq hz] at h1
  exact h1

/-- The hulls coincide (A3, hull form). -/
theorem revHull_eq_of_welding_eq (hCar : Blueprint.RevMapCaratheodory)
    {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (hK : IsSimpleCurveHull (revHull W T))
    (hK' : IsSimpleCurveHull (revHull W' T')) (hzm : zeroMinus W T = zeroMinus W' T')
    (hweld : EqOn (weldingHom W T) (weldingHom W' T') (Icc (zeroMinus W T) 0))
    (hrem : IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T))) :
    revHull W' T' = revHull W T := by
  have h := revMap_eq_of_welding_eq hCar hW hW' hW0 hW'0 hT hT' hK hK' hzm hweld hrem
  unfold revHull
  rw [h.image_eq]

/-- Equal weldings force equal capacities and equal terminal driver values (A3, time form). -/
theorem time_eq_of_welding_eq (hCar : Blueprint.RevMapCaratheodory)
    {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (hK : IsSimpleCurveHull (revHull W T))
    (hK' : IsSimpleCurveHull (revHull W' T')) (hzm : zeroMinus W T = zeroMinus W' T')
    (hweld : EqOn (weldingHom W T) (weldingHom W' T') (Icc (zeroMinus W T) 0))
    (hrem : IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T))) :
    T' = T ∧ W' T' = W T := by
  have h := revMap_eq_of_welding_eq hCar hW hW' hW0 hW'0 hT hT' hK hK' hzm hweld hrem
  obtain ⟨h1, h2⟩ := drive_and_time_eq_of_revMap_eq hW hW' hT.le hT'.le h
  exact ⟨h2.symm, h1.symm⟩

end QuantumZipper
