/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L7Tele at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7

/-!
# DZZ Lemma 2.7: telescoping over the scale bands and the lemma (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 553, 573–574: with
`Δ_0 = h̃_1 − η_1`, `Δ_i = h̃_{2^{-i}}^{2^{-i+1}} − η_{2^{-i}}^{2^{-i+1}}`,
`h̃_{2^{-j}}(v) − η_{2^{-j}}(v) = Σ_{i ≤ j} Δ_i(v)` (a.s., for each `v`, `j`): the time set
`(4^{-j}, ∞)` is the disjoint union of the bands up to the null set of band endpoints, and the
white noise is linear (`dzz_telescope`). With continuous versions this gives DZZ Lemma 2.7
(`dzz_lemma27`), modulo `BridgeShellBound`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

lemma indicator_Ioi_split {a' a s : ℝ} (h : a' ≤ a) (hs : s ≠ a) (f : ℝ → ℝ) :
    (Ioi a').indicator f s = (Ioi a).indicator f s + (Ioo a' a).indicator f s := by
  rcases lt_or_gt_of_ne hs with h2 | h2
  · by_cases h3 : a' < s
    · simp [indicator_apply, h3, h2, not_lt.2 h2.le]
    · simp [indicator_apply, h3, not_lt.2 h2.le]
  · simp [indicator_apply, h2, h.trans_lt h2, not_lt.2 h2.le]

/-- `{p | p.1 = b²}` is null (as `WhiteNoise.PsiParams.ae_ne_sq`). -/
lemma ae_fst_ne_sq (b : ℝ) : ∀ᵐ p : ℝ × ℂ ∂volume, p.1 ≠ b ^ 2 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have : {p : ℝ × ℂ | p.1 = b ^ 2} = {b ^ 2} ×ˢ univ := by ext p; simp
  rw [this, show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod]
  simp

lemma wndKernelL2_split {a' b : ℝ} (ha' : 0 < a') (h : a' ≤ b ^ 2) (v : ℂ) :
    wndKernelL2 openSquare (Ioi a') v =
      wndKernelL2 openSquare (Ioi (b ^ 2)) v + wndKernelL2 openSquare (Ioo a' (b ^ 2)) v := by
  have m1 := memLp_wndKernel LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball (I := Ioi a') measurableSet_Ioi ha' subset_rfl v
  have m2 := memLp_wndKernel LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball (I := Ioi (b ^ 2)) measurableSet_Ioi ha' (Ioi_subset_Ioi h) v
  have m3 := memLp_wndKernel LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball (I := Ioo a' (b ^ 2)) measurableSet_Ioo ha' Ioo_subset_Ioi_self v
  rw [wndKernelL2, wndKernelL2, wndKernelL2, dite_eq_left_of_eq_true (eq_true m1),
    dite_eq_left_of_eq_true (eq_true m2), dite_eq_left_of_eq_true (eq_true m3),
    ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [ae_fst_ne_sq b] with p hp
  simp only [Pi.add_apply, wndKernel]
  exact indicator_Ioi_split h hp _

lemma etaKernelL2_split {a' b : ℝ} (ha' : 0 < a') (h : a' ≤ b ^ 2) (v : ℂ) :
    etaKernelL2 (Ioi a') v = etaKernelL2 (Ioi (b ^ 2)) v + etaKernelL2 (Ioo a' (b ^ 2)) v := by
  have m1 := memLp_etaKernel (I := Ioi a') measurableSet_Ioi ha' subset_rfl v
  have m2 := memLp_etaKernel (I := Ioi (b ^ 2)) measurableSet_Ioi ha' (Ioi_subset_Ioi h) v
  have m3 := memLp_etaKernel (I := Ioo a' (b ^ 2)) measurableSet_Ioo ha' Ioo_subset_Ioi_self v
  rw [etaKernelL2, etaKernelL2, etaKernelL2, dite_eq_left_of_eq_true (eq_true m1),
    dite_eq_left_of_eq_true (eq_true m2), dite_eq_left_of_eq_true (eq_true m3),
    ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [ae_fst_ne_sq b] with p hp
  simp only [Pi.add_apply, etaKernel]
  exact indicator_Ioi_split h hp _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ l. 553, 573–574**: `h̃_{2^{-j}}(v) − η_{2^{-j}}(v) = Σ_{i ≤ j} Δ_i(v)` a.s. -/
theorem dzz_telescope (hW : IsWhiteNoise P W) (j : ℕ) (v : ℂ) :
    (fun ω => tildeHInf W ((1 / 2 : ℝ) ^ j) v ω - etaInf W ((1 / 2 : ℝ) ^ j) v ω) =ᵐ[P]
      fun ω => ∑ i ∈ Finset.range (j + 1), dzzDelta W i v ω := by
  induction j with
  | zero => exact Eventually.of_forall fun ω => by simp [dzzDelta]
  | succ j ih =>
    have ha' : (0 : ℝ) < ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 := by positivity
    have hle : ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 ≤ ((1 / 2 : ℝ) ^ j) ^ 2 :=
      pow_le_pow_left₀ (by positivity)
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ j)) 2
    have e1 := hW.add_ae (wndKernelL2 openSquare (Ioi (((1 / 2 : ℝ) ^ j) ^ 2)) v)
      (wndKernelL2 openSquare (Ioo (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) (((1 / 2 : ℝ) ^ j) ^ 2)) v)
    have e2 := hW.add_ae (etaKernelL2 (Ioi (((1 / 2 : ℝ) ^ j) ^ 2)) v)
      (etaKernelL2 (Ioo (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) (((1 / 2 : ℝ) ^ j) ^ 2)) v)
    filter_upwards [ih, e1, e2] with ω h0 h1 h2
    rw [Finset.sum_range_succ, ← h0]
    simp only [tildeHInf, etaInf, wnField, etaField, dzzDelta, tildeH, eta,
      Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [wndKernelL2_split ha' hle, etaKernelL2_split ha' hle, h1, h2]
    ring

/-- Rational points are dense (copy of `GM.denseRange_ratPt`, AttainedP36Conf.lean). -/
lemma denseRange_ratPt' : DenseRange ratPt := by
  have h1 : DenseRange (Prod.map (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h2 : DenseRange (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) :=
    Complex.equivRealProdCLM.symm.surjective.denseRange
  have := h2.comp h1 Complex.equivRealProdCLM.symm.continuous
  convert this using 1
  funext q
  apply Complex.ext <;> simp [ratPt]

universe u

/-- **DZZ Lemma 2.7** (`lem-tilde-h-eta`, l. 548–576), assuming `BridgeShellBound`: for continuous
versions `Z_j` of `h̃_{2^{-j}} − η_{2^{-j}}`,
`P(max_{v ∈ [0,1]²} max_{j ≥ 0} |Z_j(v)| ≥ λ) ≤ C e^{−λ²/C}` with an absolute constant `C`. -/
theorem dzz_lemma27 {C₀ : ℝ} (hC0 : 0 ≤ C₀) (hC : BridgeShellBound C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Z : ℕ → ℂ → Ω → ℝ,
      (∀ j ω, Continuous fun x => Z j x ω) →
      (∀ j x, Z j x =ᵐ[P] fun ω => tildeHInf W ((1 / 2 : ℝ) ^ j) x ω -
        etaInf W ((1 / 2 : ℝ) ^ j) x ω) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) := by
  obtain ⟨C, hCpos, hsum⟩ := dzz_lemma27_sum.{u} hC0 hC
  refine ⟨C, hCpos, fun {Ω} _ {P} {W} hW Z hZc hZ lam hlam => ?_⟩
  have := hW.isProbabilityMeasure
  obtain ⟨Y, hYc, -, hY⟩ := exists_continuous_dzzDelta hC0 hC hW
  -- `Z_j = Σ_{i ≤ j} Y_i` simultaneously for all `j` and `x`, a.s.
  have hpt : ∀ j x, Z j x =ᵐ[P] fun ω => ∑ i ∈ Finset.range (j + 1), Y i x ω := by
    intro j x
    have hs : (fun ω => ∑ i ∈ Finset.range (j + 1), Y i x ω) =ᵐ[P]
        fun ω => ∑ i ∈ Finset.range (j + 1), dzzDelta W i x ω := by
      have : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (j + 1), Y i x ω = dzzDelta W i x ω :=
        (Finset.eventually_all _).2 fun i _ => hY i x
      filter_upwards [this] with ω hω
      exact Finset.sum_congr rfl hω
    exact (hZ j x).trans ((dzz_telescope hW j x).trans hs.symm)
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ q : ℚ × ℚ,
      Z j (ratPt q) ω = ∑ i ∈ Finset.range (j + 1), Y i (ratPt q) ω := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro q; exact hpt j (ratPt q)
  have hall' : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ x : ℂ,
      Z j x ω = ∑ i ∈ Finset.range (j + 1), Y i x ω := by
    filter_upwards [hall] with ω hω j
    have hS : Continuous fun x => ∑ i ∈ Finset.range (j + 1), Y i x ω :=
      continuous_finset_sum _ fun i _ => hYc i ω
    have := denseRange_ratPt'.equalizer (hZc j ω) hS (funext fun q => hω j q)
    exact fun x => congrFun this x
  have hsub : {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤ᵐ[P]
      {ω | ∃ v ∈ ferniqueBox 0 1, ∃ n : ℕ, lam ≤ ∑ i ∈ Finset.range n, |Y i v ω|} := by
    filter_upwards [hall'] with ω hω hE
    obtain ⟨v, hv, j, hj⟩ := hE
    refine ⟨v, hv, j + 1, hj.trans ?_⟩
    rw [hω j v]
    exact Finset.abs_sum_le_sum_abs _ _
  refine (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans ?_
  exact hsum hW Y hYc hY lam hlam

end DZZ
end LQGMetric
