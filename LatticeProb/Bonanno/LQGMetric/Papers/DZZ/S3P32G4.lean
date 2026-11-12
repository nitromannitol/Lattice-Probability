/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32G4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G3

/-!
# DZZ (eq-B-good-Psi) + union at `μIn`, explicit parameters, with the proved cover (P2-DZZ32G)

Copy of `start_bound_explicit` (S3P32F6, P2-DZZ32F) with the false hypothesis `P32StartGeom`
(`not_p32StartGeom`) replaced by the proved corrected cover `p32StartGeomS` (S3P32G3); it is
applied only to cells, where `r = rP32 γ δ ≤ δ^{C_mc}/8 ≤ s_B/8`.

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1149–1153): with `t = 2^{-q}`, the balls of the start
path (`P32StartGeom`) are covered by the boxes `B̂_j` of level `n_B + q`; if one ball has
`μIn`-mass `> δ²` then on `{M_s(B) ≤ δ²} ∩ G_δ` ((eq-M-tilde-B-bound)) some `B̂_j` has
`M̃_{γ,ε²s,η}(B̂_j) ≥ s² e^{-2αγ√L log L}/4`, of probability `≤ |{B̂_j}| (ts)²/θ = 16 M t² e^E`
((Eq.LQG-tildeM)). The union is over the `≤ 9` boxes per level with `x ∈ B_large`
(`exists_finset_largeBox`) and the levels `1 ≤ n ≤ C_mc log₂ δ⁻¹` (Lemma 3.1).

* **`start_bound_explicitS`**: `P(startPhiC^c) ≤ P(cellSize^c) + P(G_δ^c) + 9 K · 16 M t² e^E`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option maxHeartbeats 1000000 in
/-- **DZZ (eq-B-good-Psi) at `μIn` + the union over cells, explicit parameters** -/
theorem start_bound_explicitS (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (α : ℝ) (G : ℝ → Set Ω) {δ₀ : ℝ}
    (hup : ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ B : DyBox, δ ^ dzzCmc γ ≤ B.side → ∀ ω ∈ G δ,
      approxLQG γ W ω B ≤ δ ^ 2 → ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - B.center‖ ≤ 3 * B.side) →
        wickQArea γ W ω b'.closedBox ≤
          ENNReal.ofReal (Real.exp (2 * α * γ * Real.sqrt (Real.log δ⁻¹) *
            Real.log (Real.log δ⁻¹)) * δ ^ 2 / B.side ^ 2) *
          etaChaos W γ ((2 : ℝ)⁻¹ ^ (B.n + 2 * kL37 γ δ)) b'.closedBox ω)
    {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) δ₀) (hδ1 : δ < 1) {q j : ℕ}
    (hq3 : 3 ≤ q) (hj : 1 ≤ 2 ^ j * rP32 γ δ) {x : ℂ} (hx : x ∈ dzzVIn (rP32 γ δ))
    (hM : (8 * 2 ^ q + 4 * j + 16 : ℝ) ≤ δ ^ (-(dzzCMc γ / 2)) * lamP32 δ) :
    P (startPhiC γ W (dzzMuIn γ W) (rP32 γ δ) δ (dzzCMc γ / 2) x)ᶜ ≤
      P (cellSizeEvent γ W δ)ᶜ + P (G δ)ᶜ +
        ENNReal.ofReal (9 * ⌊dzzCmc γ * Real.logb 2 δ⁻¹⌋₊ *
          (16 * (8 * 2 ^ q + 4 * j + 16) * ((2 : ℝ)⁻¹ ^ q) ^ 2 *
            Real.exp (2 * α * γ * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)))) := by
  classical
  obtain ⟨hδ0, hδδ₀⟩ := hδ
  set r := rP32 γ δ with hrdef
  have hr : 0 < r := (isClipDepth_rP32 γ δ ⟨hδ0, hδ1⟩).1
  set M : ℝ := 8 * 2 ^ q + 4 * j + 16 with hMdef
  set E := 2 * α * γ * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹) with hEdef
  set C := dzzCmc γ with hCdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  set K := ⌊C * Real.logb 2 δ⁻¹⌋₊ with hKdef
  set t : ℝ := (2 : ℝ)⁻¹ ^ q with htdef
  have hM0' : 0 ≤ M := by rw [hMdef]; positivity
  have hcov : ∀ b : DyBox, ∃ S T, (1 ≤ b.n → x ∈ b.largeBox →
      (S.card : ℝ) ≤ M ∧ T.card ≤ 4 * S.card ∧ ∀ b' ∈ T, b'.n = b.n + q) ∧
      (1 ≤ b.n → x ∈ b.largeBox → r ≤ b.side / 2 → StartCover b (b.n + q) r x M S T) := by
    intro b
    by_cases h : 1 ≤ b.n ∧ x ∈ b.largeBox ∧ r ≤ b.side / 2
    · obtain ⟨S, T, hST⟩ := p32StartGeomS b (b.n + q) j r x h.1 (by omega) hr h.2.2
        ((pow_le_one₀ (by norm_num) (by norm_num)).trans hj) hx h.2.1
      rw [show b.n + q - b.n = q by omega] at hST
      exact ⟨S, T, fun _ _ => ⟨hST.1, hST.2.1, fun b' hb' => (hST.2.2.2.2 b' hb').1⟩,
        fun _ _ _ => hST⟩
    · refine ⟨∅, ∅, fun _ _ => ⟨by simpa using hM0', by simp, by simp⟩,
        fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose Sf Tf hST using hcov
  choose F hF9 hF using fun n => exists_finset_largeBox n x
  set θb : DyBox → ℝ := fun b => b.side ^ 2 * Real.exp (-E) / 4 with hθb
  have hθb0 : ∀ b, 0 < θb b := fun b => by have := b.side_pos'; simp only [hθb]; positivity
  set Bad : DyBox → Set Ω := fun b => {ω | 1 ≤ b.n ∧ x ∈ b.largeBox ∧ ∃ b' ∈ Tf b,
    ENNReal.ofReal (θb b) ≤ etaChaos W γ ((2 : ℝ)⁻¹ ^ (b.n + 2 * kL37 γ δ)) b'.closedBox ω}
    with hBad
  -- the inclusion
  have hsub : (startPhiC γ W (dzzMuIn γ W) r δ (dzzCMc γ / 2) x)ᶜ ⊆
      (cellSizeEvent γ W δ)ᶜ ∪ (G δ)ᶜ ∪ ⋃ n ∈ Finset.Icc 1 K, ⋃ b ∈ F n, Bad b := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_iUnion, exists_prop,
      not_exists, not_and] at hc
    obtain ⟨⟨hS, hGω⟩, hnB⟩ := hc
    apply hω
    intro b hb hxb
    set L := Real.log δ⁻¹ with hLdef
    have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL0 : 0 < L := by rw [hLdef, Real.log_inv]; have := Real.log_neg hδ0 hδ1; linarith
    obtain ⟨hs1, hs2⟩ := hS.2 b hb
    rw [← hCdef] at hs1
    have hn1 : 1 ≤ b.n := by
      by_contra h0
      have h0' : b.n = 0 := by omega
      have : b.side = 1 := by unfold DyBox.side; rw [h0', pow_zero]
      have hlt : δ ^ dzzCMc γ < 1 := Real.rpow_lt_one hδ0.le hδ1 (dzzCMc_pos γ)
      linarith
    have hnK : b.n ≤ K := by
      rw [hKdef]
      apply Nat.le_floor
      have h1 := Real.log_le_log (by positivity) hs1
      rw [Real.log_rpow hδ0, hlogδ] at h1
      have h2 : Real.log b.side = -(b.n * Real.log 2) := by
        unfold DyBox.side; rw [Real.log_pow, Real.log_inv]; ring
      rw [h2] at h1
      rw [Real.logb, ← hLdef, mul_div_assoc', le_div_iff₀ hlog2]
      linarith
    have hopen : ∀ b' ∈ Tf b, etaChaos W γ ((2 : ℝ)⁻¹ ^ (b.n + 2 * kL37 γ δ)) b'.closedBox ω ≤
        ENNReal.ofReal (θb b) := by
      intro b' hb'
      by_contra hc
      exact hnB b.n (Finset.mem_Icc.2 ⟨hn1, hnK⟩) b (hF b.n b rfl hxb)
        ⟨hn1, hxb, b', hb', (not_le.1 hc).le⟩
    have hKθ : 4 * (ENNReal.ofReal (Real.exp E * δ ^ 2 / b.side ^ 2) *
        ENNReal.ofReal (θb b)) ≤ ENNReal.ofReal (δ ^ 2) := by
      have := b.side_pos'
      rw [← ENNReal.ofReal_mul (by positivity), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
        ← ENNReal.ofReal_mul (by norm_num)]
      apply le_of_eq; congr 1
      simp only [hθb]
      rw [Real.exp_neg]
      field_simp
    have hrs : r ≤ b.side / 2 := by
      have h1 : r ≤ δ ^ dzzCmc γ / 8 := by
        rw [hrdef, rP32]
        have : (2⁻¹ : ℝ) ^ kL37 γ δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have : 0 < δ ^ dzzCmc γ := Real.rpow_pos_of_pos hδ0 _
        have := mul_le_mul_of_nonneg_left ‹(2⁻¹ : ℝ) ^ kL37 γ δ ≤ 1› this.le
        linarith
      rw [← hCdef] at h1
      have := b.side_pos'
      linarith
    exact ballPathLeC_of_geom ((hST b).2 hn1 hxb hrs) (hup δ ⟨hδ0, hδδ₀⟩ b hs1 ω hGω hb.1.le) hopen hKθ hM
  -- the probability of a bad box
  set Q : ℝ := 16 * M * t ^ 2 * Real.exp E with hQ
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hBadQ : ∀ b, P (Bad b) ≤ ENNReal.ofReal Q := by
    intro b
    by_cases h : 1 ≤ b.n ∧ x ∈ b.largeBox
    · obtain ⟨hS, hTS, hT⟩ := (hST b).1 h.1 h.2
      refine (measure_mono (t := {ω | ∃ b' ∈ Tf b, ENNReal.ofReal (θb b) ≤
        etaChaos W γ ((2 : ℝ)⁻¹ ^ (b.n + 2 * kL37 γ δ)) b'.closedBox ω})
        fun ω hω => hω.2.2).trans ?_
      refine (measure_exists_etaChaos_ge_le hW γ _ (Tf b)
        (ENNReal.ofReal_pos.2 (hθb0 b)).ne' ENNReal.ofReal_ne_top).trans ?_
      have hc : ∀ b' ∈ Tf b, volume b'.closedBox / ENNReal.ofReal (θb b) =
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (b.n + q)) ^ 2 / ENNReal.ofReal (θb b) := by
        intro b' hb'
        rw [volume_closedBox_eq, DyBox.side, (hT b' hb'),
          ENNReal.ofReal_pow (by positivity)]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
        ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_div_of_pos (hθb0 b),
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hcard : ((Tf b).card : ℝ) ≤ 4 * M := by
        have : ((Tf b).card : ℝ) ≤ 4 * (Sf b).card := by exact_mod_cast hTS
        linarith
      have e : ((2 : ℝ)⁻¹ ^ (b.n + q)) ^ 2 / θb b = 4 * t ^ 2 * Real.exp E := by
        simp only [hθb, htdef]
        rw [pow_add, DyBox.side, Real.exp_neg]
        field_simp
      rw [e, hQ]
      have : 0 ≤ 4 * t ^ 2 * Real.exp E := by positivity
      nlinarith
    · have e : Bad b = ∅ := by
        ext ω; simp only [hBad, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, -⟩; exact h ⟨h1, h2⟩
      rw [e, measure_empty]; exact bot_le
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hunion : P (⋃ n ∈ Finset.Icc 1 K, ⋃ b ∈ F n, Bad b) ≤ ENNReal.ofReal (9 * K * Q) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have h1 : ∀ n ∈ Finset.Icc 1 K, P (⋃ b ∈ F n, Bad b) ≤ ENNReal.ofReal (9 * Q) := by
      intro n _
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine (Finset.sum_le_sum fun b _ => hBadQ b).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : ((F n).card : ℝ) ≤ 9 := by exact_mod_cast hF9 n
      nlinarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, show K + 1 - 1 = K by omega,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq; congr 1; ring
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine add_le_add ((measure_union_le _ _)) ?_
  refine hunion.trans (le_of_eq ?_)
  congr 1

end DZZ
end LQGMetric
