/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19R6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19R5
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11In4
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11In5

/-!
# DG Lemma 3.19 at `μ = μ_ĥ`: assembly of `L319LevelInput` (node 4, P2-DG105r)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.19
(DG:1638–1660) as used in the proof of Lemma 3.21 (DG:1699–1706), on the box
`K₀ = [1/10, 9/10]²` of `μ_ĥ` and annuli `s𝒜_n + b` with `s𝒜_n' + b ⊆ [1/6,5/6]²`, on the grid
of side `s/32` (D116). The assembly follows `l311LevelInput_muHat` (S3L11R3):

* the fine events `E k z` are DG's `E_S^{e^k}` (DG:1642–1643) for `μ_{ĥ^tr}` of the rescaled
  noise `W ∘ U_{s, c_z}` in the unit frame (`l319Ev`, S3L19R2), at threshold `e^{−k/(d+ζ)}`;
* (eqn-perc-prob') (DG:1644–1648): `l319_unit_unif` (DG Lemma 3.20 at `𝕍̄_{u,5/8}`, input
  `DZZL61Whp`, and the heavy grid balls);
* independence (DG:1656): `l311_indep_of_local` with the locality `l319Ev_loc` (S3L19R3) and the
  coarse factor `T_S` (`l319X_local`);
* the exceptional event `Z = ⋃_z {max_{K₀} |ĥ_{W_z} − ĥ^tr_{W_z}| > A_n}` (DG:1650) with
  `γ A_n = (d + ζ)√n/2`: `prob_iUnion_tail_le`;
* the pathwise step: `ae_l319_scale` (S3L19R4) with `m_φ = min_{𝒜_n'} ĥ_s`, so that the level
  is DG's `T_S`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **the single-square inputs of DG Lemma 3.19 at `μ = μ_ĥ`** (DG:1638–1660, 1699–1706), for
`d = 2/χ`, given DZZ Proposition 3.17 + Lemma 6.1 at `μIn` on `𝕍̄_{u,5/8}`, `u = 1/2 + i/2`
(`hDZZ`, the input of `dg_lemma320`). -/
theorem l319LevelInput_muHat (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5), Metric.ball z (1 / 10) ⊆ openSquare)
    {χ : ℝ} (hχ : 0 < χ) (hDZZ : DZZL61Whp P (DZZ.dzzMuIn γ W) (5 / 8) χ l319U)
    {Q : Set ℂ} (hQ : Q ⊆ Icc (1 / 6) (5 / 6) ×ℂ Icc (1 / 6) (5 / 6)) :
    L319LevelInput P W (fun ω => muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) hK ω) γ (2 / χ) Q := by
  intro ζ₁ h0 h1
  have hb : (0 : ℝ) < 4 / 5 := by norm_num
  have hdz : 0 < 2 / χ + ζ₁ := by positivity
  obtain ⟨εs₀, hεs₀, hunif⟩ := l319_unit_unif hW hγ hγ2 hb hK l319_hR hχ hDZZ h0
    (p := (32⁻¹ : ℝ≥0∞) ^ 100) (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) _)
  set κ : ℝ := ((2 / χ + ζ₁) / (2 * γ)) ^ 2 with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨a₂, a₃, ha₂, ha₃, hZb⟩ := prob_iUnion_tail_le hW hb hK hκ (N := 9409) (by norm_num)
  refine ⟨1, εs₀ / 2, a₂, a₃, one_pos, by positivity, ha₂, ha₃, fun j n b hQ' ε hε => ?_⟩
  set s : ℝ := (2 : ℝ)⁻¹ ^ j with hsdef
  have hs : 0 < s := by positivity
  set c₀ : ℤ := ((32 * n / 2 : ℕ) : ℤ) with hc₀
  set Wx : ℤ × ℤ → WNSpace → Ω → ℝ := fun (z : ℤ × ℤ) f ω =>
    W (wnScaleDy j (l319Corner s b c₀ z) f) ω
  have hWx : ∀ z, IsWhiteNoise P (Wx z) := fun z =>
    (dgN5_wnScaleDy hW j (l319Corner s b c₀ z)).1
  set E : ℤ → ℤ × ℤ → Set Ω := fun k z => {ω | l319Site n z ∧
    l319Ev (muTr (hWx z) γ hb hK ω) (Real.exp k) (Real.exp k ^ (-(1 / (2 / χ + ζ₁))))}
    with hEdef
  set Z : Set Ω := ⋃ i ∈ l319Idx n, {ω | ¬ ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5),
    |hatMod (hWx i) hb hK z ω| ≤ √(κ * n) / 2 ∧ |trMod (hWx i) hb hK z ω| ≤ √(κ * n) / 2}
  obtain ⟨T', hT'm, hTT⟩ := l319X_local hW γ ε j n b
  have hRC : ∀ z : ℤ × ℤ, Disjoint (l319LocReg j (l319Corner s b c₀ z)) (coarseReg s) := by
    intro z
    rw [Set.disjoint_left]
    rintro ⟨t, w⟩ ⟨ht, -⟩ ⟨ht', -⟩
    exact absurd (mem_Ici.1 ht') (not_le.2 (mem_Ioo.1 ht).2)
  have hE : ∀ (k : ℤ) (z : ℤ × ℤ), ∃ A',
      MeasurableSet[wnSigma W (l319LocReg j (l319Corner s b c₀ z))] A' ∧ E k z =ᵐ[P] A' := by
    intro k z
    by_cases hz : l319Site n z
    · obtain ⟨A', hA', hAE⟩ := l319Ev_loc hW hγ hγ2 hb hK (l319_hDK.trans interior_subset) j
        (l319Corner s b c₀ z) (Real.exp k) (Real.exp k ^ (-(1 / (2 / χ + ζ₁))))
      refine ⟨A', hA', ?_⟩
      have e : E k z = {ω | l319Ev (muTr (hWx z) γ hb hK ω) (Real.exp k)
          (Real.exp k ^ (-(1 / (2 / χ + ζ₁))))} := by
        ext ω; simp only [hEdef, mem_ofPred_eq, hz, true_and]
      rw [e]; exact hAE
    · refine ⟨∅, @MeasurableSet.empty Ω (wnSigma W (l319LocReg j (l319Corner s b c₀ z))), ?_⟩
      have e : E k z = ∅ := by
        ext ω; simp only [hEdef, mem_ofPred_eq, hz, false_and, mem_empty_iff_false]
      rw [e]
  obtain ⟨hFg, hindT, hprod⟩ := l311_indep_of_local hW hRC hE hT'm hTT
    (fun F => ∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 9 x y)
    (fun F hF x hx y hy hxy => l319LocReg_disjoint (hF x hx y hy hxy))
  refine ⟨measurable_l319X hW γ ε j n b, {A | ∃ k z, A = E k z}, E, Z,
    hZb n (l319Idx n) Wx hWx (card_l319Idx n), hFg, hindT, ?_,
    fun k _ F _ hfar => hprod k F hfar, ?_⟩
  · intro k hk z hz
    have e : (E k z)ᶜ = {ω | ¬ l319Ev (muTr (hWx z) γ hb hK ω) (Real.exp k)
        (Real.exp k ^ (-(1 / (2 / χ + ζ₁))))} := by
      ext ω; simp only [hEdef, mem_compl_iff, mem_ofPred_eq, show l319Site n z from hz, true_and]
    rw [e]
    exact hunif (Real.exp k) (Real.exp_pos k) (by linarith) (Wx z) (hWx z)
  · have hae : ∀ z : ℤ × ℤ, ∀ᵐ ω ∂P, l319Site n z → ∀ ε' mφ A t M : ℝ,
        (∀ x ∈ affineC s (l319Corner s b c₀ z) '' closedBall l319U l319r,
          mφ ≤ hatDelta W P s x ω) →
        (∀ w ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5), |hatMod (hWx z) hb hK w ω| ≤ A / 2 ∧
          |trMod (hWx z) hb hK w ω| ≤ A / 2) →
        Real.exp (γ * A) * ((s ^ (2 + γ ^ 2 / 2) * Real.exp (γ * mφ))⁻¹ * ε') ≤ t →
        l319Ev (muTr (hWx z) γ hb hK ω) t M →
        ENNReal.ofReal M ≤ (dgLGDSet (muHat hW γ hb hK ω) ε' univ (annSq (s / 32) b c₀ z)
          (frontier (annSqHalf (s / 32) b c₀ z)) : ℝ≥0∞) := by
      intro z
      by_cases hz : l319Site n z
      · filter_upwards [ae_l319_scale hW hγ hγ2 hb hK j (l319Corner s b c₀ z)
          (l319_hTK hz j (hQ'.trans hQ)) l319_hDK (isClosed_annSq _ _ _ _)
          (l319_hA₀ hs b c₀ z) (l319_hB₀ hs b c₀ z)] with ω hω _
        exact hω
      · exact Eventually.of_forall fun ω h => absurd h hz
    filter_upwards [ae_all_iff.2 hae] with ω hω hZ k z hk hEz
    obtain ⟨hz, hev⟩ := hEz
    set mφ : ℝ := sInf ((fun x => DDDF.phiVer W P s 1 x ω) '' l321Out s b n) with hmφdef
    have hcont : Continuous fun x => hatDelta W P s x ω :=
      (hatDelta_spec hW hs (pow_le_one₀ (by norm_num) (by norm_num))).cont ω
    have hcpt : IsCompact (l321Out s b n) := isCompact_Icc.reProdIm isCompact_Icc
    have hbdd : BddBelow ((fun x => DDDF.phiVer W P s 1 x ω) '' l321Out s b n) :=
      hcpt.bddBelow_image hcont.continuousOn
    have hmφ : ∀ x ∈ affineC s (l319Corner s b c₀ z) '' closedBall l319U l319r,
        mφ ≤ hatDelta W P s x ω := fun x hx =>
      csInf_le hbdd (mem_image_of_mem _ (l319_TD hz hs b hx))
    have hbnd : ∀ w ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5),
        |hatMod (hWx z) hb hK w ω| ≤ √(κ * n) / 2 ∧ |trMod (hWx z) hb hK w ω| ≤ √(κ * n) / 2 := by
      by_contra hc
      exact hZ (mem_iUnion₂.2 ⟨z, mem_l319Idx hz, hc⟩)
    have hA : γ * √(κ * n) = (2 / χ + ζ₁) / 2 * √(n : ℝ) := by
      rw [Real.sqrt_mul hκ.le, hκdef, Real.sqrt_sq (by positivity)]
      field_simp
    have hXeq : l319X P W γ ε j n b ω = (s ^ (2 + γ ^ 2 / 2) * Real.exp (γ * mφ))⁻¹ * ε := by
      simp only [l319X]
      rw [mul_inv, Real.exp_neg]
      ring
    have ht : Real.exp (γ * √(κ * n)) * ((s ^ (2 + γ ^ 2 / 2) * Real.exp (γ * mφ))⁻¹ * ε) ≤
        Real.exp k := by
      rw [← hXeq, hA, mul_comm]; exact hk
    have hM : Real.exp k ^ (-(1 / (2 / χ + ζ₁))) = 1 * Real.exp (-(k / (2 / χ + ζ₁))) := by
      rw [← Real.exp_mul, one_mul]; ring_nf
    have h := hω z hz ε mφ _ _ _ hmφ hbnd ht hev
    unfold goodAnn
    rw [← hM]
    exact h

end DG
end LQGMetric
