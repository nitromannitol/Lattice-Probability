/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate6L47S at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate5Core

/-!
# Lemma 4.7 / `T4_2PairOne` at a fixed scale with a scale-free candidate radius (P2-M2K6)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.7 (l. 1890–1940)
and of Proposition 4.17 (l. 2404–2433). `gm_h47_kS` and `gm_T42_fixedS` are `gm_h47_k`
(Iterate4L47kG.lean) and `gm_T42_fixed` (Iterate5Core.lean) with the same proofs, where the
slack `1` in the radius `‖𝕫‖ + (4λ₄ε)^{-M}𝕣 + 2λ₄ε𝕣 + 1` of the candidate set `gmCandSet` (and of
the far test function) is any `sl > 0`. The fixed `1` does not scale with `𝕣`: the number of
candidates is then `≍ 𝕣^{-2}` for small `𝕣`, so the rate bound of `T4_2PairOne`, whose constant
is uniform in the base scale `R`, cannot be obtained from it; with `sl = 𝕣` it scales (GM's
candidate set `𝒵_k` lies within `ρ' + 2λ₄ε𝕣` of `𝕫`, l. 1894–1902).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **GM (4.14) at index `k`**, `gm_h47_k` with the slack `sl` -/
theorem gm_h47_kS [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {𝕣 ε β M δ sl : ℝ} (k : ℕ) (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hδ : 0 < δ)
    (hlam0 : 0 < R.lam 0) (hlam02 : R.lam 0 ≤ 2)
    (hlam3 : 1 < R.lam 3) (hlam1 : 0 ≤ R.lam 1) (hlam11 : R.lam 1 ≤ 1) (hlam2 : 0 ≤ R.lam 2)
    (hlam21 : R.lam 2 ≤ 1)
    (hRadsI : ∀ r ∈ p4Rads R 𝕣 ε, ε ^ (1 + R.ν) * 𝕣 ≤ r ∧ r ≤ ε * 𝕣)
    (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC)
    {Λ : ℝ} (hΛ : 0 < Λ) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1) (h0 : ∀ ω, h ω ψ₀ = 0)
    (hψ : tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball (0 : ℂ) (‖𝕫‖ +
      (4 * R.lam 3 * ε) ^ (-M) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + sl + ε * 𝕣))ᶜ)
    (hE2 : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma
      (fun ω => addConst (h ω) (-circleAvg (h ω) (R.lam 4 * r) z))
      (annulus z (R.lam 0 * r) (R.lam 3 * r))) (h ⁻¹' R.E r z))
    (hEf2 : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma h (ballO z (R.lam 3 * r)) ⊔
      MeasurableSpace.comap (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω)) (Metric.ball z (R.lam 3 * r)))
        inferInstance) (h ⁻¹' Ef r z 𝕫 𝕨))
    (h4 : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, 𝕫 ∉ Metric.ball z (R.lam 3 * r) →
      𝕨 ∉ Metric.ball z (R.lam 3 * r) →
      (fun ω => Λ⁻¹ * (P[(h ⁻¹' R.E r z ∩
          {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}).indicator
          (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (R.lam 2 * r))ᶜ]) ω) ≤ᵐ[P]
        P[(h ⁻¹' Ef r z 𝕫 𝕨 ∩
          {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}).indicator
          (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (R.lam 2 * r))ᶜ])
    (Rads : Finset ℝ) (hRads : (Rads : Set ℝ) = p4Rads R 𝕣 ε)
    (hL48 : P {ω | ∀ t : ℝ, 0 < t →
      filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 ((4 * R.lam 3 * ε) ^ (-M) * 𝕣) →
      𝕨 ∉ filledBall (D (h ω)) 𝕫 t → ∀ (G : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) G L 𝕫 𝕨 →
      ∀ σ : ℝ, 0 < σ → σ ≤ R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4 →
      ∀ Rads : Finset ℝ, (∀ r ∈ Rads, 2 * σ ≤ r ∧ r ≤ ε * 𝕣) →
      ∀ S : Finset (ℂ × ℝ), (∀ p ∈ S, p ∈ candSet (filledBall (D (h ω)) 𝕫 t) (R.lam 0) (R.lam 3)
          ε R.ν 𝕣 (Rads : Set ℝ) ∧ (G '' Icc 0 L ∩ ball p.1 p.2).Nonempty) →
      (S.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) ≤
        Rads.card * ENNReal.ofReal ((4 * R.lam 3 * ε) ^ (2 - 1 / M) * 𝕣 ^ 2)}ᶜ ≤
      ENNReal.ofReal δ)
    {Reg : Set Ω}
    (hReg : ∀ᵐ ω ∂P, ω ∈ Reg → ω ∈ {ω | 𝕨 ∉ thickening (3 * R.lam 3 * ε * 𝕣)
      (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))} ∩
      ({ω | filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆
          ball 𝕫 ((4 * R.lam 3 * ε) ^ (-M) * 𝕣)} ∩
        {ω | 𝕨 ∉ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)})) (hsl : 0 < sl) :
    P.real {ω | ω ∈ Reg ∧
      P[{ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty}.indicator (fun _ => (1 : ℝ)) |
        gmFilt h38 hγ hγ2 hD hh hη R.ℓ 𝕣 ε β k] ω <
      (Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1))⁻¹ *
        P[{ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty}.indicator (fun _ => (1 : ℝ)) |
          gmFilt h38 hγ hγ2 hD hh hη R.ℓ 𝕣 ε β k] ω -
      ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + sl)).ncard
          : ℝ) * Real.sqrt δ /
        (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1)} ≤ Real.sqrt δ := by
  classical
  set ρ' : ℝ := (4 * R.lam 3 * ε) ^ (-M) * 𝕣
  set L : ℝ := ‖𝕫‖ + ρ' + 2 * R.lam 3 * ε * 𝕣 + sl
  have hc : 0 < R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4 := by
    have := Real.rpow_pos_of_pos hε (1 + R.ν); positivity
  have hfin := gm_gmCandSet_finite R L hc
  set S := hfin.toFinset
  set Kt : Ω → Set ℂ := fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)
  have hKc : ∀ ω, IsClosed (Kt ω) := fun ω => gm_filledBall_isClosed _ _ _
  have he : 0 < ε * 𝕣 := mul_pos hε h𝕣
  have hRads' : ∀ r ∈ p4Rads R 𝕣 ε, 0 < r ∧ r ≤ ε * 𝕣 := fun r hr =>
    ⟨lt_of_lt_of_le (by have := Real.rpow_pos_of_pos hε (1 + R.ν); positivity)
      (hRadsI r hr).1, (hRadsI r hr).2⟩
  -- `G` is an event of `𝓕_k`
  have hG : MeasurableSet[gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β k]
      ({ω | Kt ω ⊆ ball 𝕫 ρ'} ∩ {ω | 𝕨 ∉ Kt ω}) := by
    have e1 : {ω | Kt ω ⊆ ball 𝕫 ρ'} = {ω | (Kt ω ∩ (ball 𝕫 ρ')ᶜ).Nonempty}ᶜ := by
      ext ω; simp only [mem_compl_iff, mem_setOf_eq, inter_compl_nonempty_iff, not_not]
    have e2 : {ω | 𝕨 ∉ Kt ω} = {ω | (Kt ω ∩ {𝕨}).Nonempty}ᶜ := by
      ext ω; simp only [mem_compl_iff, mem_setOf_eq, inter_singleton_nonempty]
    have hm : MeasurableSet[setSigma Kt] ({ω | Kt ω ⊆ ball 𝕫 ρ'} ∩ {ω | 𝕨 ∉ Kt ω}) := by
      rw [e1, e2]
      exact MeasurableSet.inter (m := setSigma Kt)
        (MeasurableSet.compl (m := setSigma Kt) (gm_setSigma_hit_closed hKc isOpen_ball.isClosed_compl))
        (MeasurableSet.compl (m := setSigma Kt) (gm_setSigma_hit_compact Kt hKc isCompact_singleton))
    exact (le_sup_left : gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k) ≤ _) _
      (gm_setSigma_le_localSigma h _ _ hm)
  -- the pairs of `𝒵_k` are in `S` on `G`
  have hS : ∀ ω ∈ {ω | Kt ω ⊆ ball 𝕫 ρ'} ∩ {ω | 𝕨 ∉ Kt ω},
      ∀ p ∈ zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω, p ∈ S := by
    rintro ω ⟨hsub, -⟩ p ⟨⟨hg, -, hr, hlo, hhi⟩, -⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨hg, ?_⟩, hr⟩
    have hpos : 0 < R.lam 3 * ε * 𝕣 := by rw [mul_assoc]; exact mul_pos (by linarith) he
    have hfr : (frontier (Kt ω)).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      simp only [Kt, hne, infDist_empty] at hlo
      linarith
    obtain ⟨q, hq, hpq⟩ := (infDist_lt_iff hfr).1
      (lt_of_le_of_lt hhi (lt_add_of_pos_right (2 * R.lam 3 * ε * 𝕣) hsl))
    have hqK : q ∈ Kt ω := (hKc ω).frontier_subset hq
    have hq𝕫 := hsub hqK
    rw [mem_ball] at hq𝕫
    have t1 := norm_le_norm_add_norm_sub' p.1 𝕫
    have t2 : ‖p.1 - 𝕫‖ ≤ dist p.1 q + dist q 𝕫 := by
      rw [← dist_eq_norm]; exact dist_triangle _ _ _
    simp only [L, ρ']
    linarith
  -- `ψ₀` is far from the balls of `S`
  have hψS : ∀ i ∈ S, tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball i.1 (R.lam 2 * i.2))ᶜ := by
    intro i hi
    rw [Set.Finite.mem_toFinset] at hi
    obtain ⟨⟨-, hz⟩, hr⟩ := hi
    obtain ⟨hr0, hre⟩ := hRads' _ hr
    refine hψ.trans (compl_subset_compl.2 fun x hx => ?_)
    rw [mem_ball] at hx ⊢
    rw [dist_zero_right]
    have : R.lam 2 * i.2 ≤ ε * 𝕣 := (mul_le_of_le_one_left hr0.le hlam21).trans hre
    have t1 := norm_le_norm_add_norm_sub' x i.1
    rw [← dist_eq_norm] at t1
    linarith
  -- the count bound
  have hP := gm_h47_count (P := P) R h𝕫𝕨 sel (by filter_upwards [hη] with ω hω; exact hω.1) k
    hℓ𝕣 hε h𝕣 hδ.le hlam0 (by linarith) hlam02 hlam11 Ef Rads hRads hRadsI S hL48 (β := β)
  have hK0 : 0 ≤ Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M) * 𝕣 ^ 2) /
      (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 := by
    have : 0 ≤ (4 * R.lam 3 * ε) ^ (2 - 1 / M) :=
      Real.rpow_nonneg (by have : 0 < R.lam 3 := by linarith
                           positivity) _
    positivity
  have hcard : (S.card : ℝ) ≤ (gmCandSet R 𝕣 ε L).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
  refine gm_h47_k_core h38 hC24 hC27 hC14 hγ hγ2 hD hh R h𝕫𝕨 sel hη k hℓ𝕣 hε h𝕣 hlam3 hlam1
    hlam11 hlam2 hlam21 hRads' Ef hΛ hψ₀ h0 S hψS hE2 hEf2 h4 hG hS (by linarith) hcard hδ
    (le_trans (measureReal_mono (inter_subset_inter_left _ fun x hx => ?_)) hP) hReg
  simp only [mem_setOf_eq] at hx ⊢
  linarith

open scoped Classical in
/-- **`T4_2PairOne` at a fixed scale** (GM l. 2361–2441), `gm_T42_fixed` with the slack `1` of
the candidate radius replaced by any `sl > 0` -/
theorem gm_T42_fixedS {b β θ ν ζ : ℝ} (hb : 0 < b) (hθ : 0 < θ) (hθβ : θ < β)
    (hζ : 0 < ζ) (hβν : 4 * ν + ζ < β) (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
    ∀ (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7) (hC14 : CONFThm1_4)
      {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
      (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] [P.IsComplete] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
      (R : RegPar), R.ν = ν → ∀ {𝕫 𝕨 : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨)
      (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
      (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
      {𝕣 M₈ δ δ₁ L sl : ℝ} {K : ℕ}, 0 < sl → 0 < R.ℓ * 𝕣 → 0 < 𝕣 → 0 < δ →
      0 < R.lam 0 → R.lam 0 ≤ 2 → 1 < R.lam 3 → 0 ≤ R.lam 1 → R.lam 1 ≤ 1 → 0 ≤ R.lam 2 →
      R.lam 2 ≤ 1 → 0 ≤ R.lam 4 →
      (∀ r ∈ p4Rads R 𝕣 ε, ε ^ (1 + R.ν) * 𝕣 ≤ r ∧ r ≤ ε * 𝕣) →
      ∀ (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) {Λ : ℝ}, 0 < Λ → ∀ {ψ₀ : TestC}, ∫ x, ψ₀ x = 1 →
      (∀ ω, h ω ψ₀ = 0) →
      tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball (0 : ℂ) (‖𝕫‖ +
        (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + sl + ε * 𝕣))ᶜ →
      (∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma
        (fun ω => addConst (h ω) (-circleAvg (h ω) (R.lam 4 * r) z))
        (annulus z (R.lam 0 * r) (R.lam 3 * r))) (h ⁻¹' R.E r z)) →
      (∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma h (ballO z (R.lam 3 * r)) ⊔
        MeasurableSpace.comap (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω))
          (Metric.ball z (R.lam 3 * r))) inferInstance) (h ⁻¹' Ef r z 𝕫 𝕨)) →
      (∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, 𝕫 ∉ Metric.ball z (R.lam 3 * r) →
        𝕨 ∉ Metric.ball z (R.lam 3 * r) →
        (fun ω => Λ⁻¹ * (P[(h ⁻¹' R.E r z ∩
            {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}).indicator
            (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (R.lam 2 * r))ᶜ]) ω) ≤ᵐ[P]
          P[(h ⁻¹' Ef r z 𝕫 𝕨 ∩
            {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}).indicator
            (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (R.lam 2 * r))ᶜ]) →
      ∀ (Rads : Finset ℝ), (Rads : Set ℝ) = p4Rads R 𝕣 ε →
      P {ω | ∀ t : ℝ, 0 < t →
        filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 ((4 * R.lam 3 * ε) ^ (-M₈) * 𝕣) →
        𝕨 ∉ filledBall (D (h ω)) 𝕫 t → ∀ (G : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) G L 𝕫 𝕨 →
        ∀ σ : ℝ, 0 < σ → σ ≤ R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4 →
        ∀ Rads : Finset ℝ, (∀ r ∈ Rads, 2 * σ ≤ r ∧ r ≤ ε * 𝕣) →
        ∀ S : Finset (ℂ × ℝ), (∀ p ∈ S, p ∈ candSet (filledBall (D (h ω)) 𝕫 t) (R.lam 0)
            (R.lam 3) ε R.ν 𝕣 (Rads : Set ℝ) ∧ (G '' Icc 0 L ∩ ball p.1 p.2).Nonempty) →
        (S.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) ≤
          Rads.card * ENNReal.ofReal ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2)}ᶜ ≤
        ENNReal.ofReal δ →
      ∀ (Reg : Set Ω), 1 ≤ K → b * ε ^ (-β) ≤ K + 2 →
      (∀ k ≤ K, ∀ᵐ ω ∂P, ω ∈ Reg → ω ∈ gmFk D h R 𝕫 𝕨 𝕣 ε β k) →
      (∀ k ≤ K, ∀ᵐ ω ∂P, ω ∈ Reg → ω ∈ {ω | 𝕨 ∉ thickening (3 * R.lam 3 * ε * 𝕣)
        (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))} ∩
        ({ω | filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆
            ball 𝕫 ((4 * R.lam 3 * ε) ^ (-M₈) * 𝕣)} ∩
          {ω | 𝕨 ∉ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)})) →
      (∀ ω ∈ Reg, ∀ k ≤ K, filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆ ball 𝕫 L) →
      L + 3 * R.lam 3 * ε * 𝕣 < ‖𝕫 - 𝕨‖ →
      P.real (Reg ∩ {ω | ((((Finset.range (K + 1)).filter
          (fun k => (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty)).card : ℕ) : ℝ) <
        (1 - ε ^ θ) * K}) ≤ δ₁ →
      ε ^ (2 * ν + ζ / 2) ≤
        (Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1))⁻¹ / 2 -
        ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + sl)).ncard
          : ℝ) * Real.sqrt δ /
        (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1) →
      (Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1))⁻¹ / 2 -
        ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + sl)).ncard
          : ℝ) * Real.sqrt δ /
        (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1) ≤ 1 →
      P.real (Reg ∩ {ω | ¬ t42Wit sel h Ef R.lam R.rr R.μ 𝕣 ε 𝕫 𝕨 ω}) ≤
        δ₁ + (K + 1) * Real.sqrt δ + 2 * ε ^ M := by
  obtain ⟨ε₀, hε₀, H⟩ := gm_P4_17_ae hb hθ hθβ hζ hβν M
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε h38 hC24 hC27 hC14 γ D c' hγ hγ2 hD Ω _ P _ _ h hh R hRν 𝕫 𝕨 h𝕫𝕨 sel hη 𝕣 M₈ δ
    δ₁ L sl K hsl hℓ𝕣 h𝕣 hδ hl0 hl02 hl3 hl1 hl11 hl2 hl21 hl4 hRadsI Ef Λ hΛ ψ₀ hψ₀ h0 hψ hE2 hEf2
    h4 Rads hRads hL48 Reg hK1 hbK hRegF hRegW hRegG hfar h412 hrate hrate1
  subst hRν
  have hε0 : 0 < ε := hε.1
  have hRads3 : ∀ r ∈ p4Rads R 𝕣 ε, 0 < r ∧ r ≤ ε * 𝕣 ∧ R.lam 1 * r ≤ 2 * R.lam 3 * (ε * 𝕣) :=
    fun r hr => by
      have h1 := hRadsI r hr
      have hp : 0 < ε ^ (1 + R.ν) * 𝕣 := mul_pos (Real.rpow_pos_of_pos hε0 _) h𝕣
      refine ⟨lt_of_lt_of_le hp h1.1, h1.2, ?_⟩
      have hr0 : 0 ≤ r := (lt_of_lt_of_le hp h1.1).le
      have : R.lam 1 * r ≤ 1 * r := mul_le_mul_of_nonneg_right hl11 hr0
      nlinarith
  set ℱ := gmFilt h38 hγ hγ2 hD hh hη R.ℓ 𝕣 ε β with hℱ
  have hmono : ∀ k, gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1) ≤ ℱ (k + 1) :=
    fun k => gm_le_supFilt _ _ (k + 1)
  have hmeas := fun k => gm_measurableSet_zkE_zkF (β := β) h38 hC24 hC27 hC14 hγ hγ2 hD hh R sel
    hη k hε0 h𝕣 hl3 Ef hE2 hEf2
  have key := H ε hε K hbK ℱ (μ := P) Reg (fun k => gmFk D h R 𝕫 𝕨 𝕣 ε β k)
    (fun k => {ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty})
    (fun k => {ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty})
    (κ := (Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1))⁻¹)
    (fun k => gm_aeEventIn_mono' (hmono k)
      (gm_gmFk_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) hℓ𝕣 hε0
        (by rw [mul_assoc]; exact mul_pos (by linarith) (mul_pos hε0 h𝕣)) k))
    (fun k => gm_aeEventIn_mono' (hmono k)
      (gm_L4_20E h38 hC24 hC27 hC14 hγ hγ2 hD hh R h𝕫𝕨 sel hη hℓ𝕣 hε0 h𝕣 hl3 hl4 hRads3 hE2 k))
    (fun k => gm_aeEventIn_mono' (hmono k)
      (gm_L4_20F h38 hC24 hC27 hC14 hγ hγ2 hD hh R h𝕫𝕨 sel hη Ef hℓ𝕣 hε0 h𝕣 hl3 hl4 hRads3
        hEf2 k))
    (fun k => (hmeas k).1) (fun k => (hmeas k).2) hRegF
    (by
      have : 0 < Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1) := by positivity
      exact (inv_pos.2 this).le)
    hrate hrate1 h412
    (fun k _ => gm_h47_kS h38 hC24 hC27 hC14 hγ hγ2 hD hh R h𝕫𝕨 sel hη k hℓ𝕣 hε0 h𝕣 hδ hl0 hl02
      hl3 hl1 hl11 hl2 hl21 hRadsI Ef hΛ hψ₀ h0 hψ hE2 hEf2 h4 Rads hRads hL48
      (hRegW k ‹_›) hsl)
  refine gm_T4_2_pair_bound P sel h R Ef Reg hK1 (Real.rpow_pos_of_pos hε0 (2 * R.ν + ζ)) hℓ𝕣 hε0 h𝕣
    (by linarith) (fun r hr => (hRadsI r hr).2) hfar hRegG ?_
  exact key


end LQGMetric.GM
