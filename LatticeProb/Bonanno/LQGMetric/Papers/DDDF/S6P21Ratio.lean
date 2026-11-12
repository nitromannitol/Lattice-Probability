/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P21Ratio at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Path
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DDen

/-!
# DDDF Proposition 21, Steps 1–3: the pathwise bound of the Condition (T) ratio (task P2-DDDF6c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 976–996 (proof of `Prop:CondSatisfied`).

* `S6.exists_nearGeodSel`: measurable `(1+η)`-near-geodesic selections exist (D-DDDF-5; from
  `exists_nearGeodesic`).
* `S6.ratio_pathwise` (Steps 1–3): for any left–right crossing `γ` of `[0,1]²` and `K ≥ 2`,
  `ratio · L^{(K)}_{1,1}(φ) ≤ 4 · 2^{-K} e^{ξ M} e^{2ξ X} e^{6ξ O}` with
  `M = sup_{[0,1]²} |φ_{0,K}|`, `X = Xbig` (DDDF's `X_1`, here on `[-2,3]²`) and `O = Obig`
  (`2^{-K} sup ‖∇φ_{0,K}‖`). DDDF: Step 1 `Σ e^{2ξψ} ≤ e^{ξ max ψ} Σ e^{ξψ}`,
  `max_{π^K} ψ_{0,K} ≤ max φ_{0,K} + X_1`; Step 2 (`eq:CoarseToPath`, `S6.rectLen_le_coarse`)
  `Σ e^{ξψ} ≥ e^{-ξX_1} e^{-ξ max osc} 2^K L^{(K)}_{1,1}(φ)`. DDDF take the max over the blocks of
  `𝒫_K^1` (inside `[0,1]²`); the blocks of `π^K` touching `∂[0,1]²` from outside are handled by
  the oscillation term (`3 O`), so the max is the sup over `[0,1]²` (own elementary step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail T20 T20C T20D

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace S6

/-- measurable `(1+η)`-near-geodesic selections exist (D-DDDF-5) -/
theorem exists_nearGeodSel (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ γ : ℕ → Ω → ℝ → ℂ, IsNearGeodSel ξ Q W P η γ := by
  have h : ∀ n : ℕ, ∃ (Qn : ℕ → ℝ → ℂ) (J : Ω → ℕ), (∀ j, AdmPath (rectAB 1 1).toSet
      (rectAB 1 1).side₁ (rectAB 1 1).side₂ (Qn j)) ∧ Measurable J ∧
      ∀ ω, lfppLen ξ (fun x => psiMN Q W P 0 n x ω) (Qn (J ω)) <
        (1 + ENNReal.ofReal η) * rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) := by
    intro n
    have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    obtain ⟨Qn, hQa, -, -, -, hJ⟩ := exists_nearGeodesic (ξ := ξ) (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) hψ.cont hψ.meas (ENNReal.ofReal_pos.2 hη)
    obtain ⟨J, hJm, hJ⟩ := hJ (by simp [rectAB, MarkedRect.crossWidth])
    exact ⟨Qn, J, hQa, hJm, hJ⟩
  choose Qn J hQa hJm hJ using h
  refine ⟨fun n ω => Qn n (J n ω), ⟨fun n ω => hQa n _, fun n ω => ?_, fun n K b => ?_⟩⟩
  · refine (hJ n ω).le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add zero_le_one hη.le, ENNReal.ofReal_one]
  · exact hJm n (DiscreteMeasurableSpace.forall_measurableSet {j | b ∈ coarseBlocks K (Qn n j)})

lemma dyBlock_sub_hatBox {K : ℕ} {b : ℤ × ℤ} {x : ℂ} (hx : x ∈ dyBlock K b) : x ∈ hatBox K b := by
  obtain ⟨q1, q2, q3, q4⟩ := mem_dyBlock hx
  have hp := h_pos' K
  unfold hatBox; rw [Complex.mem_reProdIm]
  exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

/-- **DDDF Prop 21, Steps 1–3** (l. 976–996), pathwise. -/
theorem ratio_pathwise (Q : PsiParams) {ξ : ℝ} (hξ : 0 < ξ) {K : ℕ} (hK : 2 ≤ K)
    {Y : ℂ → Ω → ℝ} {ω : Ω} (hYc : ContDiff ℝ 1 fun x => Y x ω)
    (hYω : ∀ x, Y x ω = phiMN W P 0 K x ω)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + cBig) ω) 5 5 ≠ ⊤) {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ) :
    condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) γ * lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω ≤
      4 * (2 : ℝ)⁻¹ ^ K * Real.exp (ξ * ⨆ z : ferniqueBox 0 1, |Y z ω|) *
        Real.exp (2 * ξ * Xbig Q W P ω) * Real.exp (6 * ξ * Obig K Y ω) := by
  classical
  set S := coarseBlocks K γ
  set X := Xbig Q W P ω
  set O := Obig K Y ω
  set M := ⨆ z : ferniqueBox 0 1, |Y z ω|
  set h := (2 : ℝ)⁻¹ ^ K
  have hp : 0 < h := h_pos' K
  have hq := h_le_quarter hK
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hO0 : 0 ≤ O := Obig_nonneg K Y ω
  have hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet := by
    obtain ⟨-, -, -, -, -, hU⟩ := hγ; exact hU
  have hcB : ∀ b ∈ S, dyCenter K b ∈ bigBox := by
    intro b hb
    obtain ⟨c1, c2, c3, c4⟩ := center_near hK (Finset.mem_filter.1 hb).1
    simp only [bigBox, Complex.mem_reProdIm, mem_Icc]
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  have hφψ : ∀ b ∈ S, |Y (dyCenter K b) ω - psiMN Q W P 0 K (dyCenter K b) ω| ≤ X := by
    intro b hb; rw [hYω]; exact abs_sub_le_Xbig Q hfin K (hcB b hb)
  have hcpt : IsCompact (ferniqueBox (0 : ℂ) 1) := by
    rw [← rectAB_one_toSet]; exact (rectAB 1 1).isCompact_toSet
  have hbdd : BddAbove (range fun z : ferniqueBox (0 : ℂ) 1 => |Y z ω|) := by
    have := isCompact_iff_compactSpace.1 hcpt
    exact (isCompact_range (continuous_abs.comp
      (hYc.continuous.comp continuous_subtype_val))).bddAbove
  -- Step 1: `ψ_{0,K}(P) ≤ M + 3O + X` on `π^K`
  have hmax : ∀ b ∈ S, psiMN Q W P 0 K (dyCenter K b) ω ≤ M + 3 * O + X := by
    intro b hb
    obtain ⟨hbI, t, ht, hbt⟩ := Finset.mem_filter.1 hb
    have h1 := abs_le.1 (osc_hatBox_le hK hYc hbI (dyBlock_sub_hatBox hbt))
    have hxF : γ t ∈ ferniqueBox (0 : ℂ) 1 := by rw [← rectAB_one_toSet]; exact hU t ht
    have h2 : |Y (γ t) ω| ≤ M := le_ciSup hbdd (⟨γ t, hxF⟩ : ferniqueBox (0 : ℂ) 1)
    have h3 := abs_le.1 (hφψ b hb)
    have h4 := (abs_le.1 h2)
    linarith [h1.1, h1.2, h3.1, h3.2, h4.1, h4.2]
  -- Step 2: `L ≤ 4h e^{3ξO} Σ e^{ξ φ_{0,K}(P)}`
  have hw : ∀ b ∈ S, ∀ x ∈ hatBox K b, Real.exp (ξ * phiMN W P 0 K x ω) ≤
      Real.exp (ξ * (Y (dyCenter K b) ω + 3 * O)) := by
    intro b hb x hx
    have h1 := abs_le.1 (osc_hatBox_le hK hYc (Finset.mem_filter.1 hb).1 hx)
    rw [← hYω]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [h1.2]) hξ.le)
  have hL := rectLen_le_coarse (f := fun x => phiMN W P 0 K x ω) hγ hw
  have hL' : lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω ≤
      4 * h * ∑ b ∈ S, Real.exp (ξ * (Y (dyCenter K b) ω + 3 * O)) :=
    ENNReal.toReal_le_of_le_ofReal (by
      have := Finset.sum_nonneg fun b (_ : b ∈ S) =>
        (Real.exp_pos (ξ * (Y (dyCenter K b) ω + 3 * O))).le
      positivity) hL
  set D := ∑ b ∈ S, Real.exp (ξ * psiMN Q W P 0 K (dyCenter K b) ω)
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun b _ => (Real.exp_pos _).le
  have hφD : ∑ b ∈ S, Real.exp (ξ * (Y (dyCenter K b) ω + 3 * O)) ≤
      Real.exp (ξ * X) * Real.exp (3 * ξ * O) * D := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hφψ b hb)).2
    nlinarith
  have hN : ∑ b ∈ S, Real.exp (2 * ξ * psiMN Q W P 0 K (dyCenter K b) ω) ≤
      Real.exp (ξ * (M + 3 * O + X)) * D := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [show 2 * ξ * psiMN Q W P 0 K (dyCenter K b) ω = ξ * psiMN Q W P 0 K (dyCenter K b) ω +
      ξ * psiMN Q W P 0 K (dyCenter K b) ω by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (hmax b hb) hξ.le)) (Real.exp_pos _).le
  have hRHS : 0 ≤ 4 * h * Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O) := by
    positivity
  have hR : condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) γ =
      (∑ b ∈ S, Real.exp (2 * ξ * psiMN Q W P 0 K (dyCenter K b) ω)) / D ^ 2 := rfl
  rcases hD0.eq_or_lt with hD | hD
  · have : condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) γ = 0 := by
      rw [hR, ← hD]; simp
    rw [this, zero_mul]; exact hRHS
  · have hR0 : 0 ≤ condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) γ := by
      rw [hR]; exact div_nonneg (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le) (sq_nonneg _)
    calc condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) γ * lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω
        ≤ condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) γ *
            (4 * h * (Real.exp (ξ * X) * Real.exp (3 * ξ * O) * D)) :=
          mul_le_mul_of_nonneg_left (hL'.trans (mul_le_mul_of_nonneg_left hφD (by positivity))) hR0
      _ = 4 * h * Real.exp (ξ * X) * Real.exp (3 * ξ * O) *
            ((∑ b ∈ S, Real.exp (2 * ξ * psiMN Q W P 0 K (dyCenter K b) ω)) / D) := by
          rw [hR]; field_simp
      _ ≤ 4 * h * Real.exp (ξ * X) * Real.exp (3 * ξ * O) * Real.exp (ξ * (M + 3 * O + X)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_iff₀ hD]; exact hN
      _ = 4 * h * Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O) := by
          simp only [mul_assoc, ← Real.exp_add]; congr 2; ring_nf

end S6
end DDDF
end LQGMetric
