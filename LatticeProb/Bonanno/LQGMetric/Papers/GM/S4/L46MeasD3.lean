/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasD3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD2

/-!
# GM Lemma 4.6 (b) (task P2-E3c)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 4.6, first claim, proof l. 1705–1708 ("By Axiom II (locality), it then follows that
`Stab_{k,r}(z)` is determined by `h|_{ℂ∖B_r(z)}`"), with GM.S4.1 (l. 1648–1654).

* `gm_stab_ae_eq_stabSetN`: a.s., `Stab_{k,r}(z)` equals the event `gmStabSetN` (GM.S4.1:
  the arcs of `𝓘_k` partition `∂𝓑^•_{t_k}`; `gm_stabCond_iff_not_split`);
* `gm_L4_6b`: GM Lemma 4.6 (b), from `DFGPSLem3_8`, the CONF inputs of GM.S4.1 (already inputs of
  GM Lemma 4.5, `gm_L4_5_E2b`) and the analyticity of the two relations `GMArcRelAn`,
  `GMAvoidRelAn` (measurability, not discussed by GM).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- a.s., `Stab_{k,r}(z) = gmStabSetN` (GM.S4.1) -/
theorem gm_stab_ae_eq_stabSetN (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P)
    {𝕫 z : ℂ} {ℓ 𝕣 ε β lam1 lam4 ν r : ℝ} {k : ℕ} {Rads : Set ℝ}
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) :
    {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω)) lam1 lam4 ε ν 𝕣
        Rads ∧ stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω) z r} =ᵐ[P]
      h ⁻¹' (D ⁻¹' gmStabSetN 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) lam1 lam4
        ε ν 𝕣 Rads z r) := by
  set c₁ := 1 + k * ε ^ β
  set cc := 1 + k * ε ^ β + ε ^ (2 * β)
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hc₁ : 1 ≤ c₁ := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    simp only [c₁]
    linarith
  have hc₁c : c₁ < cc := by simp only [c₁, cc]; linarith
  have hc : 1 < cc := by linarith
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [gm_S4_1 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫,
    ae_mem_lenSet h38 hγ hγ2 hD P h hh] with ω h41 hlen
  set d := D (h ω)
  have hl : d.IsLength := isLength_of_mem_lenSet hlen
  simp only [mem_ofPred_eq, mem_preimage, gmStabSetN, gm_s4T_eq, gm_s4S_eq]
  change (candEvD d 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r ∧
      stabCond d 𝕫 (tauD d 𝕫 (ℓ * 𝕣) * c₁) (tauD d 𝕫 (ℓ * 𝕣) * cc) z r) ↔
    (candEvD d 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r ∧
      ¬ gmSplit d 𝕫 (tauD d 𝕫 (ℓ * 𝕣) * c₁) (tauD d 𝕫 (ℓ * 𝕣) * cc) z r)
  refine and_congr_right fun hcand => ?_
  set τ := tauD d 𝕫 (ℓ * 𝕣)
  have hpos := (gm_agree_of_candEvD (d₂ := d) hl hl hc ha le_rfl isOpen_univ (subset_univ _)
    (fun _ _ _ _ => rfl) hcand).1.pos
  have hτ : 0 < τ := pos_of_mul_pos_left hpos (by linarith)
  have hs : 0 < τ * c₁ := mul_pos hτ (by linarith)
  have hst : τ * c₁ < τ * cc := mul_lt_mul_of_pos_left hc₁c hτ
  obtain ⟨-, -, hdisj, hcov⟩ := h41 _ _ hs hst
  have hne : (frontier (filledBall d 𝕫 (τ * cc))).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨⟨𝕫, Or.inl (subset_closure ?_)⟩, fun hu => hcand.2.1 (hu ▸ mem_univ z)⟩
    show d.1 (𝕫, 𝕫) < τ * cc
    rw [d.2.self_eq_zero]
    exact hpos
  exact gm_stabCond_iff_not_split hdisj hcov hne

/-- **GM Lemma 4.6 (b)** (l. 1705–1708) for `ρ ≤ min(r, λ₄ε𝕣)` (GM: `ρ = r`): `Stab_{k,r}(z)` is
a.s. an event of `σ(h|_{ℂ∖B_ρ(z)})`. -/
theorem gm_L4_6b (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P)
    {𝕫 z : ℂ} {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ}
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) (hρr : ρ ≤ r)
    (hArcAn : GMArcRelAn 𝕫) (hAvAn : GMAvoidRelAn 𝕫 z r) :
    AEEventIn P (fieldSigmaClosed h (Metric.ball z ρ)ᶜ)
      {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω)) lam1 lam4 ε ν 𝕣
        Rads ∧ stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω) z r} := by
  set cc := 1 + k * ε ^ β + ε ^ (2 * β)
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hc : 1 < cc := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    simp only [cc]
    linarith
  have hc₁ : 1 + k * ε ^ β ≤ cc := by simp only [cc]; linarith
  obtain ⟨F, hF, hEF⟩ := gm_aeEventIn_of_local hD (Tight.isGFFPlusCont_of_wp hh) lenSet
    measurableSet_lenSet (fun d hd => isLength_of_mem_lenSet hd)
    (ae_mem_lenSet h38 hγ hγ2 hD P h hh) z ρ _
    (gm_uMeasurableSet_stabSetN hArcAn hAvAn (ℓ * 𝕣) (1 + k * ε ^ β) cc lam1 lam4 ε ν 𝕣 Rads)
    (fun d₁ hd₁ d₂ hd₂ U hU hUρ heq hB => gm_stabSetN_of_internal_eq
      (isLength_of_mem_lenSet hd₁) (isLength_of_mem_lenSet hd₂) hc hc₁ ha hρ hρr hU hUρ heq hB)
  exact ⟨F, hF, (gm_stab_ae_eq_stabSetN h38 hC24 hC27 hC14 hγ hγ2 hD hh hε ha).trans hEF⟩

end LQGMetric.GM
