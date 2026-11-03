/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.MixedM7D2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedM7D1

/-!
# K3-mixed M7-a3, half-disc covariance, step D2: the reflection upper bound

For a finite measure `μ` on `Hbar ∩ closedBall t r'` (`r' < r`) and a smooth `f` vanishing on a
neighbourhood of the *closed* semicircle `sphere t r ∩ Hbar`,

  `(∫ f dμ)² ≤ ½ ‖μ̃‖²_{B} · E_U(f)`,  `μ̃ = μ + conj_* μ`, `B = ball t r`, `U = B ∩ H`,

where `‖·‖²_B = dualNormSq B (zeroSpace B)` (`sq_integral_le_of_vanish_m7d`). Proof: the smooth
even folds `G_n = χ · (f ∘ evFold ε_n)` (`MixedM7D1.lean`, `χ` a bump equal to `1` where
`f ∘ evFold ε_n` may be nonzero) lie in `zeroSpace B`, `∫ G_n dμ̃ = 2 ∫ f ∘ evFold ε_n dμ →
2 ∫ f dμ` and `E_B(G_n) = 2 E_U(f ∘ evFold ε_n) → 2 E_U(f)` (reflection symmetry and dominated
convergence).

Own elementary argument (reflection principle for the Neumann condition on the diameter).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Real Topology ComplexConjugate

namespace QuantumZipper.K3

theorem continuous_evAbs'_m7d {ε : ℝ} (hε : 0 < ε) : Continuous (evAbs' ε) := by
  unfold evAbs'
  exact continuous_id.div (by fun_prop) fun y => (Real.sqrt_pos.2 (by positivity)).ne'

/-- A nonempty open set carries a smooth bump of positive energy in `zeroSpace`
(as `exists_pos_energy_mixedSpace`). -/
theorem exists_pos_energy_zeroSpace_m7d {D : Set ℂ} (hD : IsOpen D) (hne : D.Nonempty) :
    ∃ g ∈ zeroSpace D, 0 < dirichletEnergyOn D g := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hD p hp
  let β : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (β : ℂ → ℝ) := β.contDiff
  have hsuppD : tsupport (β : ℂ → ℝ) ⊆ D := by
    rw [β.tsupport_eq]
    exact (closedBall_subset_ball (by show r / 2 < r; linarith)).trans hball
  have hF : Continuous fun z => ‖fderiv ℝ (β : ℂ → ℝ) z‖ ^ 2 :=
    ((hgs.continuous_fderiv (by simp)).norm).pow 2
  have hFc : HasCompactSupport fun z => ‖fderiv ℝ (β : ℂ → ℝ) z‖ ^ 2 :=
    (β.hasCompactSupport.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => ‖L‖ ^ 2)
      (by simp)
  have hout : ∀ z, z ∉ D → ‖fderiv ℝ (β : ℂ → ℝ) z‖ ^ 2 = 0 := by
    intro z hz
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hsuppD h))]; simp
  refine ⟨β, ⟨hgs, β.hasCompactSupport, hsuppD⟩, ?_⟩
  have hex : ∃ x, ‖fderiv ℝ (β : ℂ → ℝ) x‖ ^ 2 ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : ∀ x, fderiv ℝ (β : ℂ → ℝ) x = 0 := fun x => by simpa using hall x
    have hc := is_const_of_fderiv_eq_zero (hgs.differentiable (by simp)) h0 p (p + r)
    have h1 : (β : ℂ → ℝ) p = 1 := β.one_of_mem_closedBall (mem_closedBall_self (by
      show (0 : ℝ) ≤ r / 4; positivity))
    have h2 : (β : ℂ → ℝ) (p + r) = 0 := β.zero_of_le_dist (by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
      show r / 2 ≤ r; linarith)
    rw [h1, h2] at hc; exact one_ne_zero hc
  obtain ⟨x, hx⟩ := hex
  have hpos := hF.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hFc
    (fun _ => by positivity) hx
  unfold dirichletEnergyOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  exact mul_pos (by positivity) hpos

/-- A function vanishing near the closed semicircle vanishes on a whole half-annulus. -/
theorem exists_vanish_radius_m7d {t r r' : ℝ} (hr'r : r' < r) {f : ℂ → ℝ} {N : Set ℂ}
    (hN : IsOpen N) (hsN : sphere (t : ℂ) r ∩ Hbar ⊆ N) (hf0 : ∀ z ∈ N, f z = 0) :
    ∃ ρ, r' ≤ ρ ∧ ρ < r ∧ ∀ w ∈ Hbar, ρ < ‖w - t‖ → ‖w - t‖ ≤ r → f w = 0 := by
  set C := (closedBall (t : ℂ) r ∩ Hbar) \ N
  have hC : IsCompact C := ((isCompact_closedBall _ _).inter_right isClosed_Hbar).diff hN
  rcases C.eq_empty_or_nonempty with h | hne
  · refine ⟨r', le_rfl, hr'r, fun w hw _ hwr => hf0 w ?_⟩
    by_contra hwN
    have : w ∈ C := ⟨⟨by rw [mem_closedBall, dist_eq_norm]; exact hwr, hw⟩, hwN⟩
    rw [h] at this; exact this
  · obtain ⟨w₀, hw₀C, hmax⟩ := hC.exists_isMaxOn hne
      ((continuous_id.sub continuous_const).norm.continuousOn :
        ContinuousOn (fun w : ℂ => ‖w - (t : ℂ)‖) C)
    have h1 : ‖w₀ - t‖ ≤ r := by
      have := hw₀C.1.1; rwa [mem_closedBall, dist_eq_norm] at this
    have hw₀r : ‖w₀ - t‖ < r := by
      refine lt_of_le_of_ne h1 fun heq => hw₀C.2 (hsN ⟨?_, hw₀C.1.2⟩)
      rw [mem_sphere, dist_eq_norm, heq]
    refine ⟨max r' ‖w₀ - t‖, le_max_left _ _, max_lt hr'r hw₀r, fun w hw hρw hwr => hf0 w ?_⟩
    by_contra hwN
    have hwC : w ∈ C := ⟨⟨by rw [mem_closedBall, dist_eq_norm]; exact hwr, hw⟩, hwN⟩
    have : ‖w - (t : ℂ)‖ ≤ ‖w₀ - (t : ℂ)‖ := isMaxOn_iff.1 hmax w hwC
    linarith [le_max_right r' ‖w₀ - t‖]

/-- **D2 (reflection upper bound, vanishing case).** -/
theorem sq_integral_le_of_vanish_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (hμH : ∀ᵐ z ∂μ, z ∈ Hbar)
    (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0)
    (hfin : dualNormSq (ball (t : ℂ) r) (zeroSpace (ball (t : ℂ) r)) (μ + μ.map conj) < ⊤)
    {f : ℂ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {N : Set ℂ} (hN : IsOpen N)
    (hsN : sphere (t : ℂ) r ∩ Hbar ⊆ N) (hf0 : ∀ z ∈ N, f z = 0) :
    (∫ x, f x ∂μ) ^ 2 ≤ (dualNormSq (ball (t : ℂ) r) (zeroSpace (ball (t : ℂ) r))
      (μ + μ.map conj)).toReal / 2 * dirichletEnergyOn (ball (t : ℂ) r ∩ H) f := by
  have hr : 0 < r := hr'.trans hr'r
  set B := ball (t : ℂ) r with hBdef
  set μt := μ + μ.map conj with hμt
  set Nn := (dualNormSq B (zeroSpace B) μt).toReal
  obtain ⟨ρ, hρr', hρr, hvan⟩ := exists_vanish_radius_m7d hr'r hN hsN hf0
  set δ := (r - ρ) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ε : ℕ → ℝ := fun n => δ / ((n : ℝ) + 1) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hεδ : ∀ n, ε n ≤ δ := fun n =>
    div_le_self hδ0.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa [hεdef, div_eq_mul_one_div δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul δ
  set a := (ρ + r) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  let χ : ContDiffBump (t : ℂ) := ⟨a, (a + r) / 2, ha0, by linarith⟩
  set g : ℕ → ℂ → ℝ := fun n => f ∘ evFold (ε n) with hgdef
  set G : ℕ → ℂ → ℝ := fun n z => χ z * g n z with hGdef
  have hgvan : ∀ n (z : ℂ), a < ‖z - t‖ → ‖z - t‖ < r → g n z = 0 := by
    intro n z h1 h2
    refine hvan _ (evFold_mem_Hbar_m7d (hε0 n).le z) ?_
      ((norm_evFold_sub_le_m7d (hε0 n).le z t).trans h2.le)
    have := norm_sub_le_evFold_m7d (hε0 n).le z t
    linarith [hεδ n]
  have hGB : ∀ n, ∀ z ∈ B, G n z = g n z := by
    intro n z hz
    have hz' : ‖z - t‖ < r := by rwa [hBdef, mem_ball, dist_eq_norm] at hz
    by_cases h : ‖z - t‖ ≤ a
    · have : χ z = 1 := χ.one_of_mem_closedBall (show z ∈ closedBall (t : ℂ) a by
        rw [mem_closedBall, dist_eq_norm]; exact h)
      simp only [hGdef, this, one_mul]
    · simp only [hGdef, hgvan n z (not_le.1 h) hz', mul_zero]
  have hgs : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g n) := fun n =>
    hf.comp (contDiff_evFold_m7d (hε0 n))
  have hGmem : ∀ n, G n ∈ zeroSpace B := by
    intro n
    refine ⟨χ.contDiff.mul (hgs n), χ.hasCompactSupport.mul_right, ?_⟩
    refine tsupport_mul_subset_left.trans ?_
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by show (a + r) / 2 < r; linarith)
  -- energies
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  set q : ℕ → ℂ → ℝ := fun n z => (fderiv ℝ f (evFold (ε n) z) 1) ^ 2 +
      (evAbs' (ε n) z.im * fderiv ℝ f (evFold (ε n) z) Complex.I) ^ 2 with hqdef
  have hq : ∀ n z, ‖fderiv ℝ (g n) z‖ ^ 2 = q n z := fun n z =>
    sq_norm_fderiv_comp_evFold_m7d (hε0 n) hfd z
  have hqconj : ∀ n z, q n (conj z) = q n z := by
    intro n z; simp only [hqdef, evFold_conj_m7d, Complex.conj_im, evAbs'_neg_m7d]; ring
  have hqc : ∀ n, Continuous (q n) := by
    intro n
    have hc := hfdc.comp (contDiff_evFold_m7d (hε0 n)).continuous
    have h1 : Continuous fun z => fderiv ℝ f (evFold (ε n) z) 1 := hc.clm_apply continuous_const
    have h2 : Continuous fun z => fderiv ℝ f (evFold (ε n) z) Complex.I :=
      hc.clm_apply continuous_const
    exact (h1.pow 2).add ((((continuous_evAbs'_m7d (hε0 n)).comp Complex.continuous_im).mul
      h2).pow 2)
  have hEG : ∀ n, dirichletEnergyOn B (G n) = 2 * ((2 * π)⁻¹ * ∫ z in B ∩ H, q n z) := by
    intro n
    unfold dirichletEnergyOn
    have h1 : ∫ z in B, ‖fderiv ℝ (G n) z‖ ^ 2 = ∫ z in B, q n z := by
      refine setIntegral_congr_fun isOpen_ball.measurableSet fun z hz => ?_
      have : G n =ᶠ[𝓝 z] g n := by
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hGB n w hw
      rw [this.fderiv_eq, hq]
    rw [h1]
    have hint : Integrable (B.indicator (q n)) :=
      (((hqc n).continuousOn.integrableOn_compact (isCompact_closedBall (t : ℂ) r)).mono_set
        ball_subset_closedBall).integrable_indicator isOpen_ball.measurableSet
    have heven : ∀ z, B.indicator (q n) (conj z) = B.indicator (q n) z := by
      intro z
      simp only [hBdef, Set.indicator, mem_ball, dist_eq_norm, norm_conj_sub_ofReal_k3, hqconj]
    have h2 := integral_eq_two_mul_setIntegral_H hint heven
    rw [integral_indicator isOpen_ball.measurableSet,
      setIntegral_indicator isOpen_ball.measurableSet] at h2
    rw [h2, Set.inter_comm H B]
    ring
  obtain ⟨M, hM⟩ := (isCompact_closedBall (t : ℂ) r).exists_bound_of_continuousOn
    hfdc.continuousOn
  have hElim : Tendsto (fun n => ∫ z in B ∩ H, q n z) atTop
      (𝓝 (∫ z in B ∩ H, ‖fderiv ℝ f z‖ ^ 2)) := by
    have hsq : ∀ x : ℝ, |x| ≤ M → x ^ 2 ≤ M ^ 2 := fun x hx => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    have hmeas : MeasurableSet (B ∩ H) := isOpen_ball.measurableSet.inter measurableSet_H_k3
    have hfin' : volume (B ∩ H) < ⊤ :=
      (measure_mono inter_subset_left).trans_lt measure_ball_lt_top
    refine tendsto_integral_of_dominated_convergence (fun _ => 2 * M ^ 2)
      (fun n => (hqc n).aestronglyMeasurable) (integrableOn_const hfin'.ne)
      (fun n => (ae_restrict_iff' hmeas).2 (Eventually.of_forall fun z hz => ?_))
      ((ae_restrict_iff' hmeas).2 (Eventually.of_forall fun z hz => ?_))
    · have hw : evFold (ε n) z ∈ closedBall (t : ℂ) r := by
        rw [mem_closedBall, dist_eq_norm]
        refine (norm_evFold_sub_le_m7d (hε0 n).le z t).trans ?_
        have := hz.1; rw [hBdef, mem_ball, dist_eq_norm] at this; exact this.le
      have hL := hM _ hw
      set L := fderiv ℝ f (evFold (ε n) z)
      have e1 : |L 1| ≤ M := by
        have := L.le_opNorm 1
        rw [norm_one, mul_one, Real.norm_eq_abs] at this; linarith
      have e2 : |evAbs' (ε n) z.im * L Complex.I| ≤ M := by
        have := L.le_opNorm Complex.I
        rw [Complex.norm_I, mul_one, Real.norm_eq_abs] at this
        rw [abs_mul]
        calc |evAbs' (ε n) z.im| * |L Complex.I| ≤ 1 * |L Complex.I| :=
              mul_le_mul_of_nonneg_right (abs_evAbs'_le_m7d _ _) (abs_nonneg _)
          _ ≤ M := by linarith
      have hqn : 0 ≤ q n z := by positivity
      rw [Real.norm_of_nonneg hqn]
      linarith [hsq _ e1, hsq _ e2]
    · have hzH : z ∈ H := hz.2
      have hT := ((continuous_evFold_eps_m7d z).tendsto 0).comp hεlim
      rw [Function.comp_def, evFold_zero_of_mem_Hbar_m7d
        (show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from hzH))] at hT
      have hD := (hfdc.tendsto z).comp hT
      have happ : ∀ v : ℂ, Tendsto (fun n => fderiv ℝ f (evFold (ε n) z) v) atTop
          (𝓝 (fderiv ℝ f z v)) := fun v =>
        ((continuous_id.clm_apply continuous_const : Continuous fun L : ℂ →L[ℝ] ℝ => L v).tendsto
          _).comp hD
      have hφ := (tendsto_evAbs'_m7d hzH).comp hεlim
      have := ((happ 1).pow 2).add ((hφ.mul (happ Complex.I)).pow 2)
      rw [norm_sq_clm_complex]
      simpa [one_mul] using this
  -- pairings
  have hμK' : ∀ᵐ z ∂μ, z ∈ closedBall (t : ℂ) r' := mem_ae_iff.2 hμK
  have hconjm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hGint : ∀ n (ν : Measure ℂ) [IsFiniteMeasure ν], Integrable (G n) ν := fun n ν _ =>
    (hGmem n).1.continuous.integrable_of_hasCompactSupport (hGmem n).2.1
  have hpair : ∀ n, ∫ z, G n z ∂μt = 2 * ∫ z, g n z ∂μ := by
    intro n
    rw [hμt, integral_add_measure (hGint n μ) (hGint n _),
      integral_map hconjm.aemeasurable (hGmem n).1.continuous.aestronglyMeasurable]
    have e1 : ∫ z, G n z ∂μ = ∫ z, g n z ∂μ := integral_congr_ae (by
      filter_upwards [hμK'] with z hz using hGB n z (closedBall_subset_ball hr'r hz))
    have e2 : ∫ z, G n (conj z) ∂μ = ∫ z, g n z ∂μ := integral_congr_ae (by
      filter_upwards [hμK'] with z hz
      have hz' : conj z ∈ B := by
        rw [mem_closedBall, dist_eq_norm] at hz
        rw [hBdef, mem_ball, dist_eq_norm, norm_conj_sub_ofReal_k3]; linarith
      rw [hGB n _ hz']
      show f (evFold (ε n) (conj z)) = f (evFold (ε n) z)
      rw [evFold_conj_m7d])
    rw [e1, e2]; ring
  have hPlim : Tendsto (fun n => ∫ z, g n z ∂μ) atTop (𝓝 (∫ z, f z ∂μ)) := by
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (t : ℂ) r).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    refine tendsto_integral_of_dominated_convergence (fun _ => M₀)
      (fun n => (hgs n).continuous.aestronglyMeasurable) (integrable_const M₀) (fun n => ?_) ?_
    · filter_upwards [hμK'] with z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      exact hM₀ _ (by
        rw [mem_closedBall, dist_eq_norm]
        exact (norm_evFold_sub_le_m7d (hε0 n).le z t).trans (hz.trans hr'r.le))
    · filter_upwards [hμH] with z hz
      have hT := ((continuous_evFold_eps_m7d z).tendsto 0).comp hεlim
      rw [Function.comp_def, evFold_zero_of_mem_Hbar_m7d hz] at hT
      exact (hf.continuous.tendsto z).comp hT
  -- assembly
  have hsupp : ∃ K, IsCompact K ∧ μt Kᶜ = 0 := by
    refine ⟨closedBall (t : ℂ) r', isCompact_closedBall _ _, ?_⟩
    rw [hμt, Measure.add_apply, hμK, zero_add,
      Measure.map_apply hconjm isClosed_closedBall.measurableSet.compl]
    convert hμK using 2
    ext z
    simp [mem_closedBall, dist_eq_norm, norm_conj_sub_ofReal_k3]
  have hDN := isDNSpace_zeroSpace B
  have hpos := exists_pos_energy_zeroSpace_m7d (isOpen_ball (x := (t : ℂ)) (ε := r))
    ⟨(t : ℂ), mem_ball_self hr⟩
  have hineq : ∀ n, (2 * ∫ z, g n z ∂μ) ^ 2 ≤
      Nn * (2 * ((2 * π)⁻¹ * ∫ z in B ∩ H, q n z)) := by
    intro n
    have h := sq_integral_le hDN hsupp hfin hpos (hGmem n)
    rw [norm_gradFeat_sq (hDN.smooth _ (hGmem n)) (hDN.energy _ (hGmem n)), hEG n,
      hpair n] at h
    exact h
  have hlim1 := (hPlim.const_mul 2).pow 2
  have hlim2 := ((hElim.const_mul (2 * π)⁻¹).const_mul 2).const_mul Nn
  have key := le_of_tendsto_of_tendsto' hlim1 hlim2 hineq
  unfold dirichletEnergyOn
  linarith

end QuantumZipper.K3
