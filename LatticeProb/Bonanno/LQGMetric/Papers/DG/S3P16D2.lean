/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P16D2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P16D1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.16, lower bound: the deterministic covering argument (packet P-126)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.16
(DG:1443–1512): on the regularity event (eqn-use-circle-avg-approx) (DG:1445–1449) the sum
`Σ_j δ e^{ξ ĥ_δ(v_{S_j})}` over a chain of squares built from an LFPP path `P` is bounded by
`δ^{−ζ}` times the LFPP length of `P` (DG:1478–1512); the squares crossed only in short time
before the first long crossing (the gap at DG:1500–1512, DEC-126 §1) lie near `z` and cost
`δ e^{ξ ĥ_δ(v_{S_z})}` each, which is the corrected error term (D126).

Route (DEC-126 §4, DV-D126-2, in place of DG's loop erasure DG:1458–1476): sample the path at
mesh `1/N` (uniform continuity), build a chain through the sampled squares
(`p16d_chain_of_samples`); for each square `S` of the chain either the path leaves the
`2a`-neighbourhood `N(S)` (then an arc of displacement `≥ a ≥ δ/2` lies in `N(S)`, and
`δ e^{ξ φ̂(v_S)} ≤ 2 e^{ξ η log δ⁻¹} ∫_{p⁻¹N(S)} e^{ξ φ(p)} |p'|`), or it stays in `N(S)` (then
`|v_S − v_{S_z}| ≤ 6δ` and `e^{ξ φ̂(v_S)} ≤ e^{ξ η log δ⁻¹} e^{ξ ĥ_δ(v_{S_z})}`); every point
lies in at most `36` of the `N(S)`. Hypotheses at distance `6δ` (DG use `4δ`).

* `p16d_lower_path`: the bound for one DG path.
* `p16_lower_det`: `D̂^δ_{φ̂}(z,w;𝕊) ≤ 72 e^{ξ η log δ⁻¹} (D^δ_φ(z,w;𝕊) + δ e^{ξ ĥ_δ(v_{S_z})})`.
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric.DG

open Blueprint

/-- **DG P3.16, lower bound, for one path** (DG:1458–1512, corrected, covering argument) -/
theorem p16d_lower_path {δ ξ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hξ : 0 < ξ)
    {φ φh : ℂ → ℝ} (hφ : ContinuousOn φ closedUnitSquare)
    (H : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ 6 * δ →
      φh y ≤ φ x + η * Real.log δ⁻¹)
    (H' : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ 6 * δ →
      φh y ≤ φh x + η * Real.log δ⁻¹)
    {z w : ℂ} (hz : z ∈ closedUnitSquare) {p : ℝ → ℂ} (hp : IsDGPath closedUnitSquare z w p) :
    dgApproxLFPP ξ δ φh z w ≤ 72 * Real.exp (ξ * (η * Real.log δ⁻¹)) *
      (LQGDimension.lfppLength ξ φ p + δ * Real.exp (ξ * dgMaxSq δ φh z)) := by
  classical
  obtain ⟨haδ, hδa, -, -⟩ := p17s_dgM hδ0 hδ1
  set m := dgM δ with hm
  set a : ℝ := (2 : ℝ)⁻¹ ^ m with ha_def
  have ha : 0 < a := by positivity
  set ℓ := η * Real.log δ⁻¹ with hℓ
  set E := Real.exp (ξ * ℓ) with hE
  set Mx := dgMaxSq δ φh z with hMx
  set f : ℝ → ℝ := fun r => Real.exp (ξ * φ (p r)) * ‖deriv p r‖ with hf_def
  have hfint : IntegrableOn f (Icc 0 1) := p16d_integrableOn hφ hp
  have hf0 : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ f r := fun r _ => by simp only [hf_def]; positivity
  -- samples of the path
  have huc : UniformContinuousOn p (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hp.continuousOn
  obtain ⟨ε, hε, hεp⟩ := Metric.uniformContinuousOn_iff.1 huc a ha
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  set N : ℕ := n + 1 with hN_def
  have hNr : (N : ℝ) = n + 1 := by rw [hN_def]; push_cast; ring
  have hN : (0 : ℝ) < N := by rw [hNr]; positivity
  have hmem : ∀ i ≤ N, (i / N : ℝ) ∈ Icc (0 : ℝ) 1 := fun i hi =>
    ⟨by positivity, (div_le_one hN).2 (by exact_mod_cast hi)⟩
  set x : ℕ → ℂ := fun i => p (i / N) with hx_def
  have hstep : ∀ i < N, p16dSup (x i - x (i + 1)) < a := fun i hi => by
    refine (p16d_sup_le_norm _).trans_lt ?_
    rw [← dist_eq_norm]
    refine hεp _ (hmem i hi.le) _ (hmem (i + 1) hi) ?_
    rw [Real.dist_eq]
    have e : (i : ℝ) / N - ((i + 1 : ℕ) : ℝ) / N = -(1 / ((n : ℝ) + 1)) := by
      rw [hNr]; push_cast; field_simp; ring
    rw [e, abs_neg, abs_of_pos (by positivity)]
    exact hn
  have hx0 : x 0 = z := by simp only [hx_def]; rw [Nat.cast_zero, zero_div]; exact hp.source
  have hxN : x N = w := by simp only [hx_def]; rw [div_self hN.ne']; exact hp.target
  obtain ⟨L, hL, hLnear⟩ := p16d_chain_of_samples m x N
    (fun i hi => hp.mapsTo (hmem i hi)) hx0 hxN hstep
  -- `D̂ ≤ Σ_{S ∈ L} δ e^{ξ φ̂(v_S)}`
  have h1 : dgApproxLFPP ξ δ φh z w ≤
      ∑ k ∈ L.toFinset, δ * Real.exp (ξ * φh (dgCenter m k)) := by
    rw [List.sum_toFinset _ hL.1]
    unfold dgApproxLFPP
    refine ciInf_le ⟨0, ?_⟩ (⟨L, hL⟩ : {L : List (ℤ × ℤ) // IsDGSqChain m z w L})
    rintro _ ⟨L', rfl⟩
    exact List.sum_nonneg fun y hy => by obtain ⟨k, -, rfl⟩ := List.mem_map.1 hy; positivity
  set F := L.toFinset with hF
  -- the time sets `A_S = p⁻¹(N(S))`
  set A : ℤ × ℤ → Set ℝ := fun k =>
    Icc 0 1 ∩ p ⁻¹' {y | p16dSup (y - dgCenter m k) ≤ 5 * a / 2} with hA_def
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (hp.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_le (p16d_continuous_sup.comp (continuous_id.sub continuous_const))
        continuous_const)).measurableSet
  have hAs : ∀ k, A k ⊆ Icc 0 1 := fun k => inter_subset_left
  obtain ⟨kz, hkz, hzkz⟩ := p17_exists_sq m hz
  -- the bound for one square
  have hk : ∀ k ∈ F, δ * Real.exp (ξ * φh (dgCenter m k)) ≤
      2 * E * (∫ r in A k, f r) +
        (if p16dSup (z - dgCenter m k) ≤ 5 * a / 2 then E * (δ * Real.exp (ξ * Mx)) else 0) := by
    intro k hkF
    have hkL := List.mem_toFinset.1 hkF
    have hkI := hL.2.1 k hkL
    obtain ⟨i, hi, hik⟩ := hLnear k hkL
    have hint0 : 0 ≤ ∫ r in A k, f r := setIntegral_nonneg (hAm k) fun r hr => hf0 r hr.1
    by_cases hleave : ∃ s ∈ Icc (0 : ℝ) 1, 5 * a / 2 ≤ p16dSup (p s - dgCenter m k)
    · obtain ⟨s, hs, hs'⟩ := hleave
      obtain ⟨u, v, hu, huv, hv, harc, hdisp⟩ := p16d_exit hp ha (hmem i hi) hs hik hs'
      have hc : ∀ r ∈ Icc u v, φh (dgCenter m k) - ℓ ≤ φ (p r) := fun r hr => by
        have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hu.trans hr.1, hr.2.trans hv⟩
        have hn2 := p16d_norm_le_sup (p r - dgCenter m k)
        have := H (p r) (hp.mapsTo hr01) (dgCenter m k) (p16d_center_mem hkI)
          (by linarith [harc r hr])
        linarith
      have harc' := p16d_arc_ge hξ.le hφ hp hu huv hv hc
      have hset := p16d_interval_le_set hf0 hfint (hAm k) (hAs k) huv
        fun r hr => ⟨⟨hu.trans hr.1, hr.2.trans hv⟩, harc r hr⟩
      have hexp : Real.exp (ξ * φh (dgCenter m k)) =
          E * Real.exp (ξ * (φh (dgCenter m k) - ℓ)) := by
        rw [hE, ← Real.exp_add]; ring_nf
      have hite : 0 ≤ (if p16dSup (z - dgCenter m k) ≤ 5 * a / 2 then
          E * (δ * Real.exp (ξ * Mx)) else 0) := by split_ifs <;> positivity
      calc δ * Real.exp (ξ * φh (dgCenter m k))
          ≤ 2 * a * Real.exp (ξ * φh (dgCenter m k)) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = 2 * E * (Real.exp (ξ * (φh (dgCenter m k) - ℓ)) * a) := by rw [hexp]; ring
        _ ≤ 2 * E * (Real.exp (ξ * (φh (dgCenter m k) - ℓ)) * ‖p v - p u‖) := by
            gcongr
        _ ≤ 2 * E * (∫ r in A k, f r) := by
            gcongr; exact harc'.trans hset
        _ ≤ _ := le_add_of_nonneg_right hite
    · push Not at hleave
      have hz5 : p16dSup (z - dgCenter m k) ≤ 5 * a / 2 := by
        have := hleave 0 ⟨le_rfl, zero_le_one⟩
        rw [hp.source] at this; linarith
      rw [if_pos hz5]
      have hd : ‖dgCenter m kz - dgCenter m k‖ ≤ 6 * δ := by
        have h1 := p16d_sup_sub (dgCenter m kz - dgCenter m k) (z - dgCenter m k)
        rw [sub_sub_sub_cancel_right] at h1
        have h2 := p16d_sup_center hzkz
        rw [p16d_sup_comm] at h2
        have h3 := p16d_norm_le_sup (dgCenter m kz - dgCenter m k)
        linarith
      have h4 := H' (dgCenter m kz) (p16d_center_mem hkz) (dgCenter m k) (p16d_center_mem hkI) hd
      have hM := p16d_le_dgMaxSq φh hkz hzkz
      have h5 : 0 ≤ 2 * E * (∫ r in A k, f r) := by positivity
      calc δ * Real.exp (ξ * φh (dgCenter m k)) ≤ δ * Real.exp (ξ * (Mx + ℓ)) := by
            gcongr
            linarith
        _ = E * (δ * Real.exp (ξ * Mx)) := by rw [hE, mul_add, Real.exp_add]; ring
        _ ≤ _ := le_add_of_nonneg_left h5
  -- multiplicity
  have hM36 : ∀ r ∈ Icc (0 : ℝ) 1, ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) r ≤ 36 := by
    intro r hr
    have e : ∀ k, (A k).indicator (fun _ => (1 : ℝ)) r =
        if p16dSup (p r - dgCenter m k) ≤ 5 * a / 2 then 1 else 0 := fun k => by
      by_cases h : p16dSup (p r - dgCenter m k) ≤ 5 * a / 2
      · rw [indicator_of_mem (show r ∈ A k from ⟨hr, h⟩), if_pos h]
      · rw [indicator_of_notMem (show r ∉ A k from fun hh => h hh.2), if_neg h]
    simp only [e]
    rw [Finset.sum_boole]
    exact_mod_cast p16d_card_near m F (p r)
  have hsum := p16d_sum_restrict_le F A (fun k _ => hAm k) (fun k _ => hAs k) hf0 hfint hM36
  have hite : ∑ k ∈ F, (if p16dSup (z - dgCenter m k) ≤ 5 * a / 2 then
      E * (δ * Real.exp (ξ * Mx)) else 0) ≤ 36 * (E * (δ * Real.exp (ξ * Mx))) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast p16d_card_near m F z
  have hlen : LQGDimension.lfppLength ξ φ p = ∫ r in Icc 0 1, f r := by
    unfold LQGDimension.lfppLength
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  have hEδ : 0 ≤ E * (δ * Real.exp (ξ * Mx)) := by positivity
  calc dgApproxLFPP ξ δ φh z w ≤ ∑ k ∈ F, δ * Real.exp (ξ * φh (dgCenter m k)) := h1
    _ ≤ ∑ k ∈ F, (2 * E * (∫ r in A k, f r) +
        (if p16dSup (z - dgCenter m k) ≤ 5 * a / 2 then E * (δ * Real.exp (ξ * Mx)) else 0)) :=
        Finset.sum_le_sum hk
    _ = 2 * E * (∑ k ∈ F, ∫ r in A k, f r) + ∑ k ∈ F, (if p16dSup (z - dgCenter m k) ≤ 5 * a / 2
        then E * (δ * Real.exp (ξ * Mx)) else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * E * (36 * ∫ r in Icc 0 1, f r) + 36 * (E * (δ * Real.exp (ξ * Mx))) :=
        add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) hite
    _ ≤ 72 * E * (LQGDimension.lfppLength ξ φ p + δ * Real.exp (ξ * Mx)) := by
        rw [hlen]; nlinarith

/-- **DG P3.16, lower bound, deterministic form** (DG:1458–1512, corrected, covering argument) -/
theorem p16_lower_det {δ ξ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hξ : 0 < ξ) (hη : 0 ≤ η)
    {φ φh : ℂ → ℝ} (hφ : ContinuousOn φ closedUnitSquare)
    (H : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ 6 * δ →
      φh y ≤ φ x + η * Real.log δ⁻¹)
    (H' : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ 6 * δ →
      φh y ≤ φh x + η * Real.log δ⁻¹)
    {z w : ℂ} (hz : z ∈ closedUnitSquare) (hw : w ∈ closedUnitSquare) :
    dgApproxLFPP ξ δ φh z w ≤ 72 * Real.exp (ξ * (η * Real.log δ⁻¹)) *
      (dgLFPP ξ φ closedUnitSquare z w + δ * Real.exp (ξ * dgMaxSq δ φh z)) := by
  set K := 72 * Real.exp (ξ * (η * Real.log δ⁻¹)) with hK_def
  have hK : 0 < K := by positivity
  have : Nonempty {p : ℝ → ℂ // IsDGPath closedUnitSquare z w p} :=
    ⟨⟨_, p16_isDGPath_segment p16_convex_sq hw hz⟩⟩
  have h : dgApproxLFPP ξ δ φh z w / K - δ * Real.exp (ξ * dgMaxSq δ φh z) ≤
      dgLFPP ξ φ closedUnitSquare z w := by
    refine le_ciInf fun p => ?_
    have h1 := p16d_lower_path hδ0 hδ1 hξ hφ H H' hz p.2
    rw [← hK_def] at h1
    have h2 : dgApproxLFPP ξ δ φh z w / K ≤
        LQGDimension.lfppLength ξ φ p.1 + δ * Real.exp (ξ * dgMaxSq δ φh z) := by
      rw [div_le_iff₀ hK]; linarith
    linarith
  have h3 : dgApproxLFPP ξ δ φh z w / K ≤
      dgLFPP ξ φ closedUnitSquare z w + δ * Real.exp (ξ * dgMaxSq δ φh z) := by linarith
  rw [div_le_iff₀ hK] at h3
  linarith

end LQGMetric.DG
