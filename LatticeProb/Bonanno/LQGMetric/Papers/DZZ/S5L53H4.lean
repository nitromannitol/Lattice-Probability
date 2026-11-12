/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53H4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53H3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Side
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW10
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K4

/-!
# DZZ Lemma 5.3, the `d_i` comparison, part 4: one box (P2-DZZ53H)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2380–2385, for one `i < 9`: `l53h_di_one`.
`P(d_i ≤ exp(E X_k + L^{0.96}))ᶜ ≤ e^{−L^{1/4}}` for large `k`, from `l53h_di_chain` (S5L53H2)
with the scales of `l53h_ev` (S5L53H3) and the proved inputs
* the ball cover for cells meeting `K_i` (`l32BallCoverIn_dzzMuIn`, S3P32K2);
* the walled Corollary 3.9 at the dyadic wall `B̄₀ = wsimB₀` (`cor39_boundOn`, S5WallSim1, from
  the walled P3.2 `dzz_prop32UOn_of` with `l32BallCoverOn_inside_dzzMuIn`,
  `l32UpperCrossOn_dzzMuIn`, `dzz_lemma35UOn_wall`, as in `wsim_prop317In_image`, S5WallSim6D);
* (eq-concentration-2) of the walled P3.17 at `K = 𝕍̃_{u,v}` (hypothesis `h317`) and the a.s.
  finiteness `ae_lgd_tilde_lt_top`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

lemma l53h_dist_p : dist (⟨5 / 16, 3 / 8⟩ : ℂ) ⟨7 / 16, 3 / 8⟩ = 1 / 8 := by
  rw [Complex.dist_eq]
  have : (⟨5 / 16, 3 / 8⟩ - ⟨7 / 16, 3 / 8⟩ : ℂ) = ((-1 / 8 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> norm_num
  rw [this, Complex.norm_real, Real.norm_eq_abs]; norm_num

lemma l53h_admB₀ (δ : ℝ) : IsXiAdmissibleAtIn wsimB₀.closedBox (1 / 16) 0 δ
    {(⟨5 / 16, 3 / 8⟩ : ℂ)} {(⟨7 / 16, 3 / 8⟩ : ℂ)} := by
  have hne : (⟨5 / 16, 3 / 8⟩ : ℂ) ≠ ⟨7 / 16, 3 / 8⟩ := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have h2 : 2 * (1 / 16 : ℝ) ≤ dist (⟨5 / 16, 3 / 8⟩ : ℂ) ⟨7 / 16, 3 / 8⟩ := by
    rw [l53h_dist_p]; norm_num
  refine ⟨⟨?_, ?_, Or.inl ⟨_, rfl⟩, Or.inl ⟨_, rfl⟩, ?_⟩, ?_, ?_⟩
  · exact singleton_subset_iff.2 (wsimB₀_subset_dzzVXi (by norm_num) (by norm_num) l53h_p₁_mem)
  · exact singleton_subset_iff.2 (wsimB₀_subset_dzzVXi (by norm_num) (by norm_num) l53h_p₂_mem)
  · intro a ha b hb
    rw [mem_singleton_iff] at ha hb; subst ha hb
    rw [l53h_dist_p]; norm_num
  · rw [wsimB₀_eq_tildeBox]; exact singleton_subset_iff.2 (mem_kXi_tildeBox_left hne h2)
  · rw [wsimB₀_eq_tildeBox]; exact singleton_subset_iff.2 (mem_kXi_tildeBox_right hne h2)

lemma l53h_two_inv_pow (k : ℕ) : (2 : ℝ)⁻¹ ^ k = Real.exp (-((k : ℝ) * Real.log 2)) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k), Real.log_pow, Real.log_inv]
  ring_nf

/-- From `d ≤ e^{T}` in `ℝ≥0∞`: `d < ⊤` and `log d ≤ T` (any `T ≥ 0`). -/
lemma l53h_log_le_of_le {d : ℕ∞} {T : ℝ} (hT : 0 ≤ T)
    (h : (d : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp T)) :
    d ≠ ⊤ ∧ Real.log (d.toNat : ℝ) ≤ T := by
  have hne : d ≠ ⊤ := fun ht => by
    rw [ht, ENat.toENNReal_top, top_le_iff] at h; exact ENNReal.ofReal_ne_top h
  refine ⟨hne, ?_⟩
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hne
  simp only [ENat.toENNReal_coe, ENat.toNat_natCast] at h ⊢
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le] at h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hT
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc Real.log n ≤ Real.log (Real.exp T) := Real.log_le_log hn' h
      _ = T := Real.log_exp T

/-- **The `d_i` comparison for one box** (DZZ l. 2380–2385). -/
theorem l53h_di_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {u v : ℂ} (hu : u ∈ dzzVbar)
    (hv : v ∈ dzzVbar) (huv : u ≠ v) {ξ : ℝ} (hξ : 0 < ξ) (hξu : 2 * ξ ≤ dist u v)
    (hξ4 : ξ ≤ 1 / 4)
    (h317 : DZZProp317In P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) (tildeBox u v) ξ)
    {i : ℕ} (hi : i < 9) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      P (l53DiEvent γ W ((2 : ℝ)⁻¹ ^ k) u v i
        ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) +
          ((k : ℝ) * Real.log 2) ^ (0.96 : ℝ)))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1 / 4 : ℝ))) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C₁, C₂, hC₁, hC₂, hch⟩ := l53h_di_chain hW hγ hγ2 hu hv huv hi
  obtain ⟨cB, hcB, δB, hδB, hball⟩ := l32BallCoverIn_dzzMuIn hW hγ hγ2
    (isClosed_tildeBox (l53W u v i) (l53W u v (i + 1)))
  have hCM := dzzCMc_pos γ
  have h32 := dzz_prop32UOn_of hW hγ hγ2 (ξ := 1 / 16) (ξd := 0) (by norm_num) hCM
    (l32BallCoverOn_inside_dzzMuIn hW hγ hγ2 wsimB₀)
    (l32UpperCrossOn_dzzMuIn hW hγ hγ2 wsimB₀ (by norm_num) hCM)
    (fun _ h => dzz_lemma35UOn_wall hW hγ hγ2 wsimB₀ (by norm_num) h)
  obtain ⟨c₃, hc₃, δ₃, hδ₃, -, hcor⟩ := cor39_boundOn le_rfl h32
    (dzz_lemma35UOn_wall hW hγ hγ2 wsimB₀ (by norm_num) hCM)
  have hu' : u ∈ dzzVXi ξ :=
    dzzVXi_anti hξ4 (tildeBox_subset_dzzVXi hu hv huv (mem_tildeBox_left u v))
  have hv' : v ∈ dzzVXi ξ :=
    dzzVXi_anti hξ4 (tildeBox_subset_dzzVXi hu hv huv (mem_tildeBox_right u v))
  obtain ⟨c, hc, h317'⟩ := h317
  obtain ⟨-, δc, hδc, hconc⟩ := h317' (fun _ => {u}) (fun _ => {v})
    (isXiAdmissible_const_singleton hu' hv' (by linarith [dist_nonneg (x := u) (y := v)]))
    (fun _ _ => ⟨singleton_subset_iff.2 (mem_kXi_tildeBox_left huv hξu),
      singleton_subset_iff.2 (mem_kXi_tildeBox_right huv hξu)⟩)
  have hα := l53hA_norm_pos huv
  have hα1 := l53hA_norm_le hu hv
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    (l53_tendsto_kL.eventually (l53h_ev hα hα1 hcB hc₃ hC₁ hC₂ hδB hδ₃ hδc))
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hk₀ k hk
  rw [l53h_two_inv_pow k]
  set L : ℝ := (k : ℝ) * Real.log 2 with hL
  set α := ‖l53hA u v‖ with hαdef
  set δ := Real.exp (-L) with hδ
  set lam := L ^ (0.6 : ℝ) with hlam
  set δ₁ := Real.exp (-L) * Real.exp (-(2 * L ^ (0.8 : ℝ))) with hδ₁
  set δa := δ₁ * Real.exp (-lam) / (α / 9) with hδa
  set δb := δ * Real.exp lam / α with hδb
  set F := cor39Fac δb δa with hF
  set EX := ∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) δ {u} {v} ∂P with hEX
  have hEX0 : 0 ≤ EX := integral_nonneg fun _ => Real.log_natCast_nonneg _
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ₁0 : 0 < δ₁ := by positivity
  have hδa0 : 0 < δa := by positivity
  have hδb0 : 0 < δb := by positivity
  have hF0 : 0 < F := by rw [hF]; unfold cor39Fac; positivity
  set R := Real.exp (EX + L ^ (0.95 : ℝ)) with hR
  have hch' := hch lam (by positivity) δ δ₁ hδ0 hδ₁0 b2 F R hF0.le (Real.exp_pos _).le
  -- the event inclusion
  have hsub : (l53DiEvent γ W δ u v i (EX + L ^ (0.96 : ℝ)))ᶜ ⊆
      {ω | ENNReal.ofReal (4 * (F * R)) <
          ((approxLGDIn (tildeBox (l53W u v i) (l53W u v (i + 1))) γ W δ (l53W u v i)
            (l53W u v (i + 1)) ω : ℕ∞) : ℝ≥0∞)} := by
    intro ω hω
    simp only [mem_ofPred_eq]
    by_contra hc
    push Not at hc
    apply hω
    have e : 4 * (F * R) = Real.exp (Real.log 4 + Real.log F + (EX + L ^ (0.95 : ℝ))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hF0, hR]; ring
    rw [e] at hc
    have hc' := hc.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith : Real.log 4 +
      Real.log F + (EX + L ^ (0.95 : ℝ)) ≤ EX + L ^ (0.96 : ℝ))))
    have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg one_le_two)
    exact l53h_log_le_of_le (add_nonneg hEX0 (Real.rpow_nonneg hL0 _)) hc'
  -- the ball cover term
  have t1 := hball δ₁ ⟨hδ₁0, b1⟩
  -- the Corollary 3.9 term
  have t2 := hcor δb ⟨hδb0, b3⟩ δa ⟨hδa0, b4⟩ _ _ (l53h_admB₀ δb)
  have e2 : {ω | ¬ ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δa ⟨5 / 16, 3 / 8⟩
        ⟨7 / 16, 3 / 8⟩ : ℕ∞) : ℝ≥0∞) ≤
      ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δb ⟨5 / 16, 3 / 8⟩ ⟨7 / 16, 3 / 8⟩ :
        ℕ∞) : ℝ≥0∞) * ENNReal.ofReal F} =
      (cor39Event (fun ω => dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δb δa
        {(⟨5 / 16, 3 / 8⟩ : ℂ)} {(⟨7 / 16, 3 / 8⟩ : ℂ)})ᶜ := by
    ext ω
    simp only [cor39Event, lgdMinSet_singleton, mem_compl_iff, mem_ofPred_eq, hF, cor39Fac]
  -- the concentration term
  have t3 := hconc δ ⟨hδ0, b5⟩
  have hfin := ae_lgd_tilde_lt_top (P := P) hW hγ hγ2 hu hv huv hδ0
  have t3' : P {ω | ENNReal.ofReal R <
      ((lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v : ℕ∞) : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ)))) := by
    have hnull : P {ω | lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v < ⊤}ᶜ = 0 := by
      exact ae_iff.1 hfin
    refine (l53h_split (A := {ω | ENNReal.ofReal R <
      ((lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v : ℕ∞) : ℝ≥0∞)})
      (C := (∅ : Set Ω)) (B := conc2Event (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) P δ
      {u} {v} ∩ {ω | lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v < ⊤})
      fun ω hB hA => ?_).trans ?_
    · simp only [mem_ofPred_eq] at hA
      exfalso
      obtain ⟨hc2, hlt⟩ := hB
      simp only [conc2Event, mem_ofPred_eq, logMinLGD, lgdMinSet_singleton] at hc2 hlt
      rw [l53h_log_inv_exp, neg_neg] at hc2
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne
      rw [← hn] at hc2 hA
      simp only [ENat.toNat_natCast, ENat.toENNReal_coe] at hc2 hA
      have hle : (n : ℝ) ≤ R := natCast_le_exp_of_log_le (by
        have := (abs_le.1 hc2).2; simp only [hEX, lgdMinSet_singleton, logMinLGD] at this ⊢
        linarith)
      refine absurd hA (not_lt.2 ?_)
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hle
    · rw [measure_empty, add_zero, compl_inter]
      refine (measure_union_le _ _).trans ?_
      rw [hnull, add_zero]
      exact t3
  refine (measure_mono hsub).trans (hch'.trans ?_)
  rw [e2]
  refine (add_le_add (add_le_add (add_le_add (add_le_add t1 le_rfl) t2) le_rfl) t3').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal b6

end DZZ
end LQGMetric
