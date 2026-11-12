/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28L1C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28L1B

/-!
# DDDF Prop 28 Part 2 Step 1 for the family: the bound at one scale (task P2-DDDF28L)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1455–1472, for `δ = 2^{-n-r}` (l. 1648).
`level_bound`: for `h = 2^{-K} ≥ δ`, the event `E_K` that some `x, x' ∈ [0,1]²` with
`4h ≤ |x − x'| ≤ 8h` have `λ_δ^{-1} d_δ(x,x') < c|x − x'|^α` is contained in
`{sup_{[0,1]²} |φ_{h,1}| ≥ M} ∪ ⋃_{P, i} {L(φ_{δ,h}, R_i^S(P)) ≤ t}` (up to a null set), when
`λ_δ^{-1} e^{-ξM} t ≥ c (8h)^α` (DDDF `eq:BoundHolderLowR`, with `φ_δ = φ_{δ,h} + φ_{h,1}` in
place of `φ_{0,n} = φ_{0,k} + φ_{k,n}`); the crossing lengths have the law of
`h L(φ_{δ/h,1}, R_{1,3})` (`law_mrect_phiVer`, DDDF "and scaling", l. 1466). DDDF's
`P ∈ 𝒫^1_{k+2}` are the `≤ 4·4^K` blocks of level `K` meeting `[0,1]²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28L

open WhiteNoise SupTail Blueprint LFPP S6P28

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- `d_f(x,y) ≥ v` from `ofReal v ≤ crossLenIn` (finiteness of `d_f` for continuous `f`) -/
lemma le_lenMetricOn_of {f : ℂ → ℝ} (hf : Continuous f) {x y : ℂ} (hx : x ∈ closedUnitSquare)
    (hy : y ∈ closedUnitSquare) {v : ℝ}
    (hv : ENNReal.ofReal v ≤ crossLenIn ξ f closedUnitSquare {x} {y}) :
    v ≤ lenMetricOn ξ f closedUnitSquare x y := by
  obtain ⟨B, hB⟩ := (isCompact_ferniqueBox 0 1).bddAbove_image
    ((Real.continuous_exp.comp (continuous_const.mul hf)).continuousOn)
  have hfin : crossLenIn ξ f closedUnitSquare {x} {y} ≠ ⊤ := by
    rw [DFGPS.crossLenIn_singleton]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lfppDOn_le_of_bound_on (B := B) DFGPS.convex_closedUnitSquare hx hy fun z hz =>
        hB ⟨z, closedUnitSquare_sub_box hz, rfl⟩)
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hv

/-- the block of level `K` containing a point of `[0,1]²` -/
lemma exists_block {K : ℕ} {x : ℂ} (hx : x ∈ closedUnitSquare) :
    ∃ b ∈ Finset.Icc (0 : ℤ) (2 ^ K) ×ˢ Finset.Icc (0 : ℤ) (2 ^ K), x ∈ T20.dyBlock K b := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  set h : ℝ := (2 : ℝ)⁻¹ ^ K with hh_def
  have hh : 0 < h := by positivity
  have hinv : 1 / h = (2 : ℝ) ^ K := by rw [hh_def, inv_pow, one_div, inv_inv]
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ ⌊t / h⌋ ∧ ⌊t / h⌋ ≤ 2 ^ K ∧
      (⌊t / h⌋ : ℝ) * h ≤ t ∧ t ≤ ((⌊t / h⌋ : ℝ) + 1) * h := by
    intro t ht0 ht1
    refine ⟨Int.floor_nonneg.2 (div_nonneg ht0 hh.le), ?_, ?_, ?_⟩
    · have : (⌊t / h⌋ : ℝ) ≤ ((2 ^ K : ℤ) : ℝ) := by
        push_cast
        calc (⌊t / h⌋ : ℝ) ≤ t / h := Int.floor_le _
          _ ≤ 1 / h := div_le_div_of_nonneg_right ht1 hh.le
          _ = 2 ^ K := hinv
      exact_mod_cast this
    · exact (le_div_iff₀ hh).1 (Int.floor_le _)
    · exact ((div_lt_iff₀ hh).1 (Int.lt_floor_add_one _)).le
  obtain ⟨a1, a2, a3, a4⟩ := key x.re h1 h2
  obtain ⟨b1, b2, b3, b4⟩ := key x.im h3 h4
  refine ⟨(⌊x.re / h⌋, ⌊x.im / h⌋), Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨a1, a2⟩,
    Finset.mem_Icc.2 ⟨b1, b2⟩⟩, ?_⟩
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc]
  exact ⟨⟨a3, a4⟩, b3, b4⟩

lemma card_blocks_le (K : ℕ) :
    ((Finset.Icc (0 : ℤ) (2 ^ K) ×ˢ Finset.Icc (0 : ℤ) (2 ^ K)).card : ℝ) ≤ 4 * 4 ^ K := by
  rw [Finset.card_product, Int.card_Icc]
  have e : ((2 : ℤ) ^ K + 1 - 0).toNat = 2 ^ K + 1 := by
    rw [sub_zero]; exact_mod_cast Int.toNat_natCast (2 ^ K + 1)
  rw [e]
  push_cast
  have h1 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have e4 : (4 : ℝ) ^ K = 2 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
  rw [e4]; nlinarith

/-- a point at distance `≥ 4h` from `x ∈ P` lies outside the open box `\hat P°` -/
lemma not_mem_box {K : ℕ} {b : ℤ × ℤ} {x y : ℂ} (hx : x ∈ T20.dyBlock K b)
    (hxy : 4 * (2 : ℝ)⁻¹ ^ K ≤ ‖x - y‖) :
    y ∉ Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) := by
  intro hy
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc] at hx
  simp only [Complex.mem_reProdIm, mem_Ioo] at hy
  have e1 : |(x - y).re| < 2 * (2 : ℝ)⁻¹ ^ K := by
    rw [Complex.sub_re, abs_lt]; constructor <;> nlinarith [hx.1.1, hx.1.2, hy.1.1, hy.1.2]
  have e2 : |(x - y).im| < 2 * (2 : ℝ)⁻¹ ^ K := by
    rw [Complex.sub_im, abs_lt]; constructor <;> nlinarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
  have := Complex.norm_le_abs_re_add_abs_im (x - y)
  linarith

/-- **One scale of DDDF Prop 28 Part 2 Step 1** (l. 1457–1470, `eq:BoundHolderLowR`). -/
theorem level_bound (hW : IsWhiteNoise P W) (hξ : 0 < ξ) {δ : ℝ} (hδ0 : 0 < δ) (K : ℕ)
    (hδh : δ ≤ (2 : ℝ)⁻¹ ^ K) {α c M t : ℝ} (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hlam : 0 < lambdaDelta ξ W P δ)
    (hct : c * (8 * (2 : ℝ)⁻¹ ^ K) ^ α ≤
      (lambdaDelta ξ W P δ)⁻¹ * (Real.exp (-(ξ * M)) * t)) :
    P {ω | ∃ x y : closedUnitSquare, 4 * (2 : ℝ)⁻¹ ^ K ≤ ‖(x : ℂ) - y‖ ∧
        ‖(x : ℂ) - y‖ ≤ 8 * (2 : ℝ)⁻¹ ^ K ∧ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y < c * ‖(x : ℂ) - y‖ ^ α}
      ≤ P {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P ((2 : ℝ)⁻¹ ^ K) 1 z ω|} +
        ENNReal.ofReal (4 * (4 * 4 ^ K)) * P {ω | (2 : ℝ)⁻¹ ^ K *
          lenObs ξ (phiVer W P (δ / (2 : ℝ)⁻¹ ^ K) 1) (rectAB 1 3) ω ≤ t} := by
  classical
  have hP := hW.isProbabilityMeasure
  set h : ℝ := (2 : ℝ)⁻¹ ^ K with hh_def
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hY := isPhiVersion_phiVer hW hδ0 (hδh.trans hh1)
  have hLo := isPhiVersion_phiVer hW hh hh1
  have hHi := isPhiVersion_phiVer hW hδ0 hδh
  set Y := phiVer W P δ 1
  set Lo := phiVer W P h 1
  set Hi := phiVer W P δ h
  have hG : ∀ᵐ ω ∂P, ∀ x, Y x ω = Hi x ω + Lo x ω := by
    refine ae_eq_of_continuous_modification (Y₂ := fun x ω => Hi x ω + Lo x ω) hY.cont
      (fun ω => (hHi.cont ω).add (hLo.cont ω)) fun x => ?_
    filter_upwards [hY.ae_eq x, hLo.ae_eq x, hHi.ae_eq x, phi_add_ae hW hδ0 hδh hh1 x] with
      ω h1 h2 h3 h4
    rw [h1, h4, h2, h3]
  have hGc : P {ω | ¬ ∀ x, Y x ω = Hi x ω + Lo x ω} = 0 := ae_iff.1 hG
  set B : Finset (ℤ × ℤ) := Finset.Icc (0 : ℤ) (2 ^ K) ×ˢ Finset.Icc (0 : ℤ) (2 ^ K)
  set F : Circle × ℂ → Set Ω := fun j =>
    {ω | T20B.mrectLen ξ (fun x => Hi x ω) K j.1 j.2 1 3 ≤ t}
  set p := P {ω | h * lenObs ξ (phiVer W P (δ / h) 1) (rectAB 1 3) ω ≤ t}
  have hF : ∀ j, P (F j) = p := fun j =>
    law_mrect_phiVer hW hδ0 K hδh j.1 j.2 1 3 measurableSet_Iic
  have hsub : {ω | ∃ x y : closedUnitSquare, 4 * h ≤ ‖(x : ℂ) - y‖ ∧ ‖(x : ℂ) - y‖ ≤ 8 * h ∧
        (lambdaDelta ξ W P δ)⁻¹ * lenMetricOn ξ (fun z => Y z ω) closedUnitSquare x y <
          c * ‖(x : ℂ) - y‖ ^ α} ⊆
      ({ω | ¬ ∀ x, Y x ω = Hi x ω + Lo x ω} ∪
        {ω | M ≤ ⨆ z : ferniqueBox 0 1, |Lo z ω|}) ∪ ⋃ b ∈ B, ⋃ j ∈ T20D.shortJ K b, F j := by
    rintro ω ⟨x, y, h4, h8, hlt⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists, not_le, F] at hcon
    obtain ⟨⟨hGω, hsup⟩, hbad⟩ := hcon
    rw [not_not] at hGω
    obtain ⟨b, hb, hxb⟩ := exists_block (K := K) x.2
    have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |Lo v ω|) := by
      have := (isCompact_ferniqueBox 0 1).bddAbove_image
        (continuous_abs.comp (hLo.cont ω)).continuousOn
      rwa [Set.image_eq_range] at this
    have hM : ∀ z ∈ closedUnitSquare, |Hi z ω - Y z ω| ≤ M := fun z hz => by
      rw [hGω z, show Hi z ω - (Hi z ω + Lo z ω) = -Lo z ω by ring, abs_neg]
      exact (le_ciSup hbdd ⟨z, closedUnitSquare_sub_box hz⟩).trans hsup.le
    have hm : ∀ j ∈ T20D.shortJ K b, ENNReal.ofReal t ≤
        crossLenIn ξ (fun x => Hi x ω) (T20D.RS K j) (T20D.RS₁ K j) (T20D.RS₂ K j) :=
      fun j hj => ENNReal.ofReal_le_of_le_toReal (hbad b hb j hj).le
    have hcr := cross_lower hξ.le hM hxb (not_mem_box hxb h4) hm
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le] at hcr
    have hd := le_lenMetricOn_of (hY.cont ω) x.2 y.2 hcr
    have hpow : ‖(x : ℂ) - y‖ ^ α ≤ (8 * h) ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) h8 hα
    have : c * ‖(x : ℂ) - y‖ ^ α ≤ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => Y z ω) closedUnitSquare x y :=
      (mul_le_mul_of_nonneg_left hpow hc).trans
        (hct.trans (mul_le_mul_of_nonneg_left hd (inv_nonneg.2 hlam.le)))
    exact absurd hlt (not_lt.2 this)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (by rw [hGc, zero_add])) ?_))
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ b ∈ B, P (⋃ j ∈ T20D.shortJ K b, F j)
      ≤ ∑ b ∈ B, ∑ j ∈ T20D.shortJ K b, P (F j) :=
        Finset.sum_le_sum fun b _ => measure_biUnion_finset_le _ _
    _ = ∑ b ∈ B, ((T20D.shortJ K b).card : ℝ≥0∞) * p := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hF, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _b ∈ B, (4 : ℝ≥0∞) * p := by
        refine Finset.sum_le_sum fun b _ => ?_
        gcongr
        exact_mod_cast T20D.card_shortJ_le K b
    _ = (B.card : ℝ≥0∞) * (4 * p) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (4 * (4 * 4 ^ K)) * p := by
        rw [← mul_assoc]
        gcongr
        rw [ENNReal.ofReal_mul (by norm_num), mul_comm, ENNReal.ofReal_ofNat]
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (card_blocks_le K)

end S6P28L
end DDDF
end LQGMetric
