/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D125B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D125A
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2BridgeLemmas

/-!
# D125 packet P-125 (B): DZZ Lemma 2.9 for similarities, uniform in a dyadic scale factor
(P2-DZZ125)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) lem-scaling-coupling, l. 611–624, with the coarse
band `ĥ^1_{‖a‖}` bounded on the image box (l. 2537–2545; DEC-125 §4 C). The proof is the one of
`dzz_lemma29_simU` (S5D117A, itself `dzz_lemma29_sim` of S5L53B5), copied and modified at the
three `a`-dependent places:
* DZZ L2.8 for the coupled noise along `‖a‖ 2^{-j} = 2^{-(m+j)}` is `dzz_lemma28_uncond` after
  the index shift of `dzzLemma27Along_pow` (S5D117C2), constant independent of `m`;
* the coarse band `ĥ^1_{‖a‖}[W₂]` is bounded on `simSmallBox a b` (side `3‖a‖`) by
  `dzz_hat_sup_tail_small` (S5D125A), tail `2 e^{18 C_F²} e^{−λ²/(4(m+1))}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail WNPush

universe u

/-- **DZZ Lemma 2.9 for similarities with `‖a‖ = 2^{−m}`, constant uniform in `m` and `b`**
(DZZ l. 611–624 and l. 2537–2545): tail `C e^{−λ²/(C(m+1))}`. -/
theorem dzz_lemma29_simScale {ξ : ℝ} (hξ : 0 < ξ) (hξ2 : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : ℂ) (ha : a ≠ 0), ‖a‖ = (1 / 2 : ℝ) ^ m → ∀ (b : ℂ)
    {V₁ : Set ℂ}, V₁ ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) →
    simMap a b '' V₁ ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W W' : WNSpace → Ω → ℝ},
    IsWhiteNoise P W → IsWhiteNoise P W' →
    IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P →
    IsWhiteNoise P (coupledNoise (confHyp_simMap ha b) W W') ∧
    ∀ Z1 Z2 : ℕ → ℂ → Ω → ℝ, (∀ j ω, Continuous fun x => Z1 j x ω) →
      (∀ j ω, Continuous fun x => Z2 j x ω) →
      (∀ j x, Z1 j x =ᵐ[P] etaInf W ((1 / 2 : ℝ) ^ j) x) →
      (∀ j x, Z2 j x =ᵐ[P]
        etaInf (coupledNoise (confHyp_simMap ha b) W W') (‖a‖ * (1 / 2 : ℝ) ^ j) x) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ V₁, ∃ j : ℕ, lam ≤ |Z1 j v ω - Z2 j (simMap a b v) ω|} ≤
          C * Real.exp (-lam ^ 2 / (C * (m + 1))) := by
  have hs : (0 : ℝ) < 1 - 2 * ξ := by linarith
  obtain ⟨C1, hC1, h28⟩ := dzz_lemma28_uncond.{u} hξ hξ2
  set C3 := 2 * Real.exp (18 * ferniqueCF ^ 2) with hC3def
  have hC3 : 2 ≤ C3 := by
    have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ 18 * ferniqueCF ^ 2); linarith
  set M := max C1 C3 with hM
  have hM0 : 0 < M := lt_max_of_lt_left hC1
  refine ⟨36 * M, by positivity, fun m a ha hma b V₁ hV₁ hV₂ Ω _ P W W' hW hW' hind => ?_⟩
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  have ha1 : ‖a‖ ≤ 1 := hma ▸ pow_le_one₀ (by norm_num) (by norm_num)
  set Wt := coupledNoise (confHyp_simMap ha b) W W' with hWt_def
  have hWt : IsWhiteNoise P Wt := isWhiteNoise_coupledNoise _ hW hW' hind
  refine ⟨hWt, fun Z1 Z2 hZ1c hZ2c hZ1 hZ2 lam hlam => ?_⟩
  have := hW.isProbabilityMeasure
  set box := ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) with hbox
  set θ := simMap a b
  have hθc : Continuous θ := continuous_simMap a b
  have hj0 : ∀ j : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ j := fun j => by positivity
  have haj : ∀ j : ℕ, ‖a‖ * (1 / 2 : ℝ) ^ j ≤ ‖a‖ := fun j =>
    mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))
  -- continuous versions
  have e1 := fun j : ℕ => exists_continuous_phi hW (hj0 j) 1
  have e2 := fun j : ℕ => exists_continuous_phi hWt (mul_pos hr (hj0 j)) 1
  choose Φ1 hΦ1c hΦ1 using e1
  choose Φ2 hΦ2c hΦ2 using e2
  obtain ⟨H, hHc, hH⟩ := exists_continuous_phi hWt hr 1
  have h3 := dzz_hat_sup_tail_small hWt hma
    ⟨(θ ⟨1 / 2, 1 / 2⟩).re - 3 * ‖a‖ / 2, (θ ⟨1 / 2, 1 / 2⟩).im - 3 * ‖a‖ / 2⟩ hHc hH
  set D1 : ℕ → ℂ → Ω → ℝ := fun j x ω => Φ1 j x ω - Z1 j x ω
  set D2 : ℕ → ℂ → Ω → ℝ := fun j x ω => Φ2 j x ω - Z2 j x ω
  have hD1c : ∀ j ω, Continuous fun x => D1 j x ω := fun j ω => (hΦ1c j ω).sub (hZ1c j ω)
  have hD2c : ∀ j ω, Continuous fun x => D2 j x ω := fun j ω => (hΦ2c j ω).sub (hZ2c j ω)
  have hD1 : ∀ j x, D1 j x =ᵐ[P] fun ω => phi W ((1 / 2 : ℝ) ^ j) 1 x ω -
      etaInf W ((1 / 2 : ℝ) ^ j) x ω := fun j x => by
    filter_upwards [hΦ1 j x, hZ1 j x] with ω h1 h2
    simp only [D1, h1, h2]
  have hD2 : ∀ j x, D2 j x =ᵐ[P] fun ω => phi Wt (‖a‖ * (1 / 2 : ℝ) ^ j) 1 x ω -
      etaInf Wt (‖a‖ * (1 / 2 : ℝ) ^ j) x ω := fun j x => by
    filter_upwards [hΦ2 j x, hZ2 j x] with ω h1 h2
    simp only [D2, h1, h2]
  -- the index shift `‖a‖ 2^{-j} = 2^{-(j+m)}` (as in `dzzLemma27Along_pow`)
  choose Φ3 hΦ3c hΦ3 using fun k : ℕ => exists_continuous_phi hWt (hj0 k) 1
  choose Y3 hY3c hY3m hY3 using fun k : ℕ => exists_continuous_etaInf hWt (hj0 k)
  set D2' : ℕ → ℂ → Ω → ℝ := fun k x ω =>
    if m ≤ k then D2 (k - m) x ω else Φ3 k x ω - Y3 k x ω
  have hD2'c : ∀ k ω, Continuous fun x => D2' k x ω := fun k ω => by
    by_cases hk : m ≤ k
    · simp only [D2', hk, ↓reduceIte]; exact hD2c _ ω
    · simp only [D2', hk, ↓reduceIte]; exact (hΦ3c k ω).sub (hY3c k ω)
  have hD2' : ∀ k x, D2' k x =ᵐ[P] fun ω => phi Wt ((1 / 2 : ℝ) ^ k) 1 x ω -
      etaInf Wt ((1 / 2 : ℝ) ^ k) x ω := fun k x => by
    by_cases hk : m ≤ k
    · simp only [D2', hk, ↓reduceIte]
      have e : ‖a‖ * (1 / 2) ^ (k - m) = (1 / 2 : ℝ) ^ k := by
        rw [hma, ← pow_add, Nat.add_sub_cancel' hk]
      have := hD2 (k - m) x
      rwa [e] at this
    · simp only [D2', hk, ↓reduceIte]
      filter_upwards [hΦ3 k x, hY3 k x] with ω h1 h2
      rw [h1, h2]
  -- the coupling identity `ĥ^1_{a2^{-j}}[W̃](θv) − ĥ^1_a[W̃](θv) = ĥ^1_{2^{-j}}[W](v)`
  have hpt : ∀ j v, ∀ᵐ ω ∂P, Φ2 j (θ v) ω - H (θ v) ω = Φ1 j v ω := by
    intro j v
    have c1 := phi_coupledNoise_simMap ha b hW' (W := W) (hj0 j) 1 v
    rw [mul_one] at c1
    have c2 := phi_add_ae hWt (mul_pos hr (hj0 j)) (haj j) ha1 (θ v)
    filter_upwards [c1, c2, hΦ2 j (θ v), hH (θ v), hΦ1 j v] with ω h1 h2 h3 h4 h5
    rw [h3, h4, h5, h2, ← h1]
    ring
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ x : ℂ, Φ2 j (θ x) ω - H (θ x) ω = Φ1 j x ω := by
    have hq : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ q : ℚ × ℚ,
        Φ2 j (θ (ratPt q)) ω - H (θ (ratPt q)) ω = Φ1 j (ratPt q) ω := by
      rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro q; exact hpt j (ratPt q)
    filter_upwards [hq] with ω hω j
    have hS : Continuous fun x => Φ2 j (θ x) ω - H (θ x) ω :=
      ((hΦ2c j ω).comp hθc).sub ((hHc ω).comp hθc)
    have := denseRange_ratPt'.equalizer hS (hΦ1c j ω) (funext fun q => hω j q)
    exact fun x => congrFun this x
  set sbox := simSmallBox a b with hsbox
  have hθs : θ '' V₁ ⊆ sbox :=
    (image_mono hV₁).trans (simMap_image_ferniqueBox_subset hξ.le a b)
  set E1 := {ω | ∃ v ∈ box, ∃ j : ℕ, lam / 3 ≤ |D1 j v ω|}
  set E2 := {ω | ∃ v ∈ box, ∃ j : ℕ, lam / 3 ≤ |D2' j v ω|}
  set E3 := {ω | lam / 3 ≤ ⨆ v : sbox, |H v ω|}
  have hsub : {ω | ∃ v ∈ V₁, ∃ j : ℕ, lam ≤ |Z1 j v ω - Z2 j (θ v) ω|} ≤ᵐ[P] E1 ∪ E2 ∪ E3 := by
    filter_upwards [hall] with ω hω hE
    obtain ⟨v, hv, j, hj⟩ := hE
    have hθv : θ v ∈ box := hV₂ ⟨v, hv, rfl⟩
    have hθv' : θ v ∈ sbox := hθs ⟨v, hv, rfl⟩
    have hid : Z1 j v ω - Z2 j (θ v) ω = -D1 j v ω + D2 j (θ v) ω - H (θ v) ω := by
      simp only [D1, D2]; rw [← hω j v]; ring
    rw [hid] at hj
    have hb1 := abs_sub (-D1 j v ω + D2 j (θ v) ω) (H (θ v) ω)
    have hb2 := abs_add_le (-D1 j v ω) (D2 j (θ v) ω)
    rw [abs_neg] at hb2
    have : CompactSpace sbox := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox _ _)
    have hbdd : BddAbove (range fun u : sbox => |H u ω|) :=
      (isCompact_range (continuous_abs.comp ((hHc ω).comp continuous_subtype_val))).bddAbove
    have hsup : |H (θ v) ω| ≤ ⨆ u : sbox, |H u ω| :=
      le_ciSup (f := fun u : sbox => |H u ω|) hbdd ⟨θ v, hθv'⟩
    by_cases c1 : lam / 3 ≤ |D1 j v ω|
    · exact Or.inl (Or.inl ⟨v, hV₁ hv, j, c1⟩)
    by_cases c2 : lam / 3 ≤ |D2 j (θ v) ω|
    · refine Or.inl (Or.inr ⟨θ v, hθv, j + m, ?_⟩)
      simp only [D2', Nat.le_add_left m j, ↓reduceIte, Nat.add_sub_cancel]
      exact c2
    · exact Or.inr (show lam / 3 ≤ ⨆ u : sbox, |H u ω| by linarith)
  have hP1 : P.real E1 ≤ C1 * Real.exp (-(lam / 3) ^ 2 / C1) :=
    h28 hW D1 hD1c hD1 (lam / 3) (by linarith)
  have hP2 : P.real E2 ≤ C1 * Real.exp (-(lam / 3) ^ 2 / C1) :=
    h28 hWt D2' hD2'c hD2' (lam / 3) (by linarith)
  have hP3 : P.real E3 ≤ C3 * Real.exp (-(lam / 3) ^ 2 / (4 * (m + 1))) :=
    h3 (lam / 3) (by linarith)
  have hE : P.real {ω | ∃ v ∈ V₁, ∃ j : ℕ, lam ≤ |Z1 j v ω - Z2 j (θ v) ω|} ≤
      P.real E1 + P.real E2 + P.real E3 :=
    (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans
      ((measureReal_union_le _ _).trans (by linarith [measureReal_union_le (μ := P) E1 E2]))
  have hm1 : (1 : ℝ) ≤ m + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hexp : ∀ c d : ℝ, 0 < c → c ≤ M → 0 < d → d ≤ 4 * M * (m + 1) →
      c * Real.exp (-(lam / 3) ^ 2 / d) ≤ M * Real.exp (-lam ^ 2 / (36 * M * (m + 1))) := by
    intro c d hc hcM hd hdM
    refine mul_le_mul hcM (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0.le
    rw [div_pow, neg_div, neg_div, neg_le_neg_iff, div_div]
    exact div_le_div_of_nonneg_left (sq_nonneg lam) (by positivity) (by nlinarith)
  have f1 := hexp C1 C1 hC1 (le_max_left _ _) hC1 (by nlinarith [le_max_left C1 C3])
  have f3 := hexp C3 (4 * (m + 1)) (by linarith) (le_max_right _ _) (by positivity)
    (by nlinarith [le_max_right C1 C3])
  have hpos : 0 ≤ M * Real.exp (-lam ^ 2 / (36 * M * (m + 1))) := by positivity
  linarith

end DZZ
end LQGMetric
