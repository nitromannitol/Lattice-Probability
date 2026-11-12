/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11R5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11R4

/-!
# DG Lemma 3.11 for vertical rectangles at `μ = μ_ĥ`: assembly of `L311LevelInputV` (P2-DG105r)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1335 ("similarly"), with the
proof of Lemma 3.11 (DG:1226–1278) and of Lemma 3.13 (DG:1300–1305). This is the assembly of
`l311LevelInput_muHat` (S3L11R3) for the squares of the vertical rectangle `l313StrV s b n`
in the original coordinates: site `x` of the reflected grid is the square of site `x.swap` of
the grid with offset `l311BV (s/32) b` (S3L11R4), and the reflection enters only through
`goodSq_map_swapC`. The fine events, the locality hypothesis `L311TrLocal` (node 2(a)), the
probability bound `prob_not_goodSq_muTr_unif` and the exceptional event are those of the
horizontal case, at the corners `l311Corner s (l311BV (s/32) b) x.swap`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **the single-square inputs of DG Lemma 3.11 for vertical rectangles at `μ = μ_ĥ`**
(DG:1335 with DG:1226–1278, 1300–1305), for `d = 2/χ`, from the same hypotheses as the
horizontal `l311LevelInput_muHat`. -/
theorem l311LevelInputV_muHat (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5), Metric.ball z (1 / 10) ⊆ openSquare)
    {χ : ℝ} (hχ : 0 < χ) (hd : 1 ≤ 2 / χ) (hDZZ : DZZL53Whp P (DZZ.dzzMuIn γ W) χ)
    (hloc : L311TrLocal P hW γ (by norm_num : (0 : ℝ) < 4 / 5) hK)
    {Q : Set ℂ} (hQ : Q ⊆ Icc (1 / 6) (5 / 6) ×ℂ Icc (1 / 6) (5 / 6)) :
    L311LevelInputV P W (fun ω => muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) hK ω) γ (2 / χ)
      Q := by
  intro ζ₁ h0 h1
  have hb : (0 : ℝ) < 4 / 5 := by norm_num
  have hdz : 0 < 2 / χ - ζ₁ := by linarith
  obtain ⟨εs₀, hεs₀, hunif⟩ := prob_not_goodSq_muTr_unif hW hγ hγ2 hb hK hχ hDZZ
    (s := 1 / 32) (by norm_num) (b' := l311UnitB) (x := (0, 0)) l311_unit_mids l311_unit_sub h0
    (by linarith) (p := (32⁻¹ : ℝ≥0∞) ^ 100) (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) _)
  set κ : ℝ := ((2 / χ - ζ₁) / (2 * γ)) ^ 2 with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨a₂, a₃, ha₂, ha₃, hZb⟩ := prob_iUnion_tail_le hW hb hK hκ (N := 2048) (by norm_num)
  refine ⟨1, εs₀ / 2, a₂, a₃, one_pos, by positivity, ha₂, ha₃, fun j n b hQ' ε hε => ?_⟩
  set s : ℝ := (2 : ℝ)⁻¹ ^ j with hsdef
  have hs : 0 < s := by positivity
  set b' : ℂ := l311BV (s / 32) b with hb'def
  set Wx : ℤ × ℤ → WNSpace → Ω → ℝ := fun x f ω => W (wnScaleDy j (l311Corner s b' x.swap) f) ω
  have hWx : ∀ x, IsWhiteNoise P (Wx x) := fun x => (dgN5_wnScaleDy hW j (l311Corner s b' x.swap)).1
  set E : ℤ → ℤ × ℤ → Set Ω := fun k x => {ω | l311Grid n x ∧
    goodSq (muTr (hWx x) γ hb hK ω) (Real.exp k) (1 / 32) l311UnitB
      (Real.exp k ^ (-(1 / (2 / χ - ζ₁)))) (0, 0)} with hEdef
  set Z : Set Ω := ⋃ i ∈ l311Idx n, {ω | ¬ ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5),
    |hatMod (hWx i) hb hK z ω| ≤ √(κ * n) / 2 ∧ |trMod (hWx i) hb hK z ω| ≤ √(κ * n) / 2}
  obtain ⟨T', hT'm, hTT⟩ := l311TV_local hW γ ε j n b
  have hRC : ∀ x : ℤ × ℤ, Disjoint (l311LocReg j (l311Corner s b' x.swap)) (coarseReg s) := by
    intro x
    rw [Set.disjoint_left]
    rintro ⟨t, z⟩ ⟨ht, -⟩ ⟨ht', -⟩
    exact absurd (mem_Ici.1 ht') (not_le.2 (mem_Ioo.1 ht).2)
  have hE : ∀ (k : ℤ) (x : ℤ × ℤ), ∃ A', MeasurableSet[wnSigma W (l311LocReg j (l311Corner s b' x.swap))] A' ∧
      E k x =ᵐ[P] A' := by
    intro k x
    by_cases hx : l311Grid n x
    · obtain ⟨A', hA', hAE⟩ := hloc j (l311Corner s b' x.swap) (Real.exp k)
        (Real.exp k ^ (-(1 / (2 / χ - ζ₁))))
      refine ⟨A', hA', ?_⟩
      have e : E k x = {ω | goodSq (muTr (hWx x) γ hb hK ω) (Real.exp k) (1 / 32) l311UnitB
          (Real.exp k ^ (-(1 / (2 / χ - ζ₁)))) (0, 0)} := by
        ext ω; simp only [hEdef, mem_ofPred_eq, hx, true_and]
      rw [e]; exact hAE
    · refine ⟨∅, @MeasurableSet.empty Ω (wnSigma W (l311LocReg j (l311Corner s b' x.swap))), ?_⟩
      have e : E k x = ∅ := by ext ω; simp only [hEdef, mem_ofPred_eq, hx, false_and,
        mem_empty_iff_false]
      rw [e]
  obtain ⟨hFg, hindT, hprod⟩ := l311_indep_of_local hW hRC hE hT'm hTT
    (fun F => ∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 9 x y)
    (fun F hF x hx y hy hxy => l311LocReg_disjoint (percFar_swap (hF x hx y hy hxy)))
  refine ⟨measurable_l311TV hW γ ε j n b, {A | ∃ k x, A = E k x}, E, Z,
    hZb n (l311Idx n) Wx hWx (card_l311Idx n), hFg, hindT, ?_,
    fun k _ F _ hfar => hprod k F hfar, ?_⟩
  · intro k hk x hx
    have e : (E k x)ᶜ = {ω | ¬ goodSq (muTr (hWx x) γ hb hK ω) (Real.exp k) (1 / 32) l311UnitB
        (Real.exp k ^ (-(1 / (2 / χ - ζ₁)))) (0, 0)} := by
      ext ω; simp only [hEdef, mem_compl_iff, mem_ofPred_eq, hx, true_and]
    rw [e]
    exact hunif (Real.exp k) (Real.exp_pos k) (by linarith) (Wx x) (hWx x)
  · have hae : ∀ x : ℤ × ℤ, ∀ᵐ ω ∂P, l311Grid n x → ∀ ε' Mφ M : ℝ,
        (∀ z ∈ sqOne (s / 32) b' x.swap, hatDelta W P s z ω ≤ Mφ) →
        goodSq (muHat (hWx x) γ hb hK ω) ((s ^ (2 + γ ^ 2 / 2) * Real.exp (γ * Mφ))⁻¹ * ε')
          (1 / 32) l311UnitB M (0, 0) →
        goodSq (muHat hW γ hb hK ω) ε' (s / 32) b' M x.swap := by
      intro x
      by_cases hx : l311Grid n x
      · filter_upwards [ae_goodSq_scale hW hγ hγ2 hb hK j b' x.swap
          (l311_affine_K0V hx hs (hQ'.trans hQ)) (l311_sqOne_sub_affine hs b' x.swap)] with ω hω _
        exact hω
      · exact Eventually.of_forall fun ω h => absurd h hx
    filter_upwards [ae_all_iff.2 hae] with ω hω hZ k x hk hEx
    obtain ⟨hx, hgood⟩ := hEx
    set Mφ : ℝ := sSup ((fun z => DDDF.phiVer W P s 1 z ω) '' l313StrV s b n) with hMφdef
    have hcont : Continuous fun z => hatDelta W P s z ω :=
      (hatDelta_spec hW hs (pow_le_one₀ (by norm_num) (by norm_num))).cont ω
    have hcptV : IsCompact (l313StrV s b n) := isCompact_Icc.reProdIm isCompact_Icc
    have hbdd : BddAbove ((fun z => DDDF.phiVer W P s 1 z ω) '' l313StrV s b n) :=
      hcptV.bddAbove_image hcont.continuousOn
    have hMφ : ∀ z ∈ sqOne (s / 32) b' x.swap, hatDelta W P s z ω ≤ Mφ := fun z hz =>
      le_csSup hbdd (mem_image_of_mem _ (l311_sqOne_sub_strV hx hs b hz))
    have hbnd : ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5),
        |hatMod (hWx x) hb hK z ω| ≤ √(κ * n) / 2 ∧ |trMod (hWx x) hb hK z ω| ≤ √(κ * n) / 2 := by
      by_contra hc
      exact hZ (mem_iUnion₂.2 ⟨x, mem_l311Idx hx, hc⟩)
    have hA : γ * √(κ * n) = (2 / χ - ζ₁) / 2 * √(n : ℝ) := by
      rw [Real.sqrt_mul hκ.le, hκdef, Real.sqrt_sq (by positivity)]
      field_simp
    have hTeq : l311TV P W γ ε j n b ω = (s ^ (2 + γ ^ 2 / 2) * Real.exp (γ * Mφ))⁻¹ * ε := by
      simp only [l311TV]
      rw [mul_inv, Real.exp_neg]
      ring
    have hε' : Real.exp (γ * √(κ * n)) * Real.exp k ≤
        (s ^ (2 + γ ^ 2 / 2) * Real.exp (γ * Mφ))⁻¹ * ε := by
      rw [← hTeq, hA]
      have := mul_le_mul_of_nonneg_left hk (Real.exp_pos ((2 / χ - ζ₁) / 2 * √(n : ℝ))).le
      refine this.trans (le_of_eq ?_)
      rw [mul_comm (l311TV P W γ ε j n b ω), ← mul_assoc, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, one_mul]
    have hM : Real.exp k ^ (-(1 / (2 / χ - ζ₁))) = 1 * Real.exp (-(k / (2 / χ - ζ₁))) := by
      rw [← Real.exp_mul, one_mul]; ring_nf
    have hg := goodSq_muHat_of_muTr (hWx x) hγ.le hb hK l311_unit_sub hbnd hε' hgood
    rw [hM] at hg
    exact goodSq_map_swapC (hω x hx _ Mφ _ hMφ hg)

end DG
end LQGMetric
