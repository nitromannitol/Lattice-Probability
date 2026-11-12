/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G4

/-!
# Walled (Eq.boundDprime), UW8: (eq-B-good-Psi) relative to a dyadic wall, explicit parameters
(P2-DZZUPW, packet P-317K-UP)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1149–1153) with Remark 5.2.

* `ballPathLeC_of_geomOn`: the walled `ballPathLeC_of_geom` (S3P32F5): the start cover is built in
  the pulled-back grid (`StartCover`, the proved `p32StartGeomS`, S3P32G3), its balls map through
  the similarity onto balls inside `B̄w`, where the walled measure is `μIn`, covered by the real
  boxes `wEmb Bw b'`;
* **`start_bound_explicitSW`**: copy of `start_bound_explicitS` (S3P32G4, P2-DZZ32G) for the cells
  `wEmb Bw b` inside the wall (pulled-back point `x`, clipping depth `r_δ / s_{Bw}`, all masses,
  sides and levels those of the real boxes).
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

/-- **The walled start path** (DZZ l. 1149–1151 with Remark 5.2). -/
lemma ballPathLeC_of_geomOn {γ δh δ r M R : ℝ} {ω : Ω} {Bw Bp : DyBox} {N : ℕ} {x : ℂ}
    {S : Finset (ℂ × ℝ)} {T : Finset DyBox} (hc : StartCover Bp N r x M S T) {K θ : ℝ≥0∞}
    (hup : ∀ b' : DyBox,
      (∀ z ∈ b'.closedBox, ‖z - (wEmb Bw Bp).center‖ ≤ 3 * (wEmb Bw Bp).side) →
      wickQArea γ W ω b'.closedBox ≤ K * etaChaos W γ δh b'.closedBox ω)
    (hopen : ∀ b ∈ T, etaChaos W γ δh (wEmb Bw b).closedBox ω ≤ θ)
    (hKθ : 4 * (K * θ) ≤ ENNReal.ofReal (δ ^ 2)) (hMR : M ≤ R) :
    BallPathLeC (wPullMeas Bw (dzzWall Bw.closedBox (dzzMuIn γ W ω))) δ r x
      (frontier Bp.largeBox) R := by
  classical
  obtain ⟨hS, -, ⟨w, p, hw, hpath, hcov⟩, hball, hT⟩ := hc
  refine ⟨S, w, p, hw, hS.trans hMR, hpath, fun q hq => ?_, hcov⟩
  obtain ⟨hsub, Tq, hTq, hTq4, hcovq⟩ := hball q hq
  have hs := wside_pos Bw
  have hballB : ball (wHom Bw q.1) (Bw.side * q.2) ⊆ Bw.closedBox := by
    rw [← image_wHom_ball, ← image_wHom_dzzV]; exact image_mono hsub
  have hcov' : ball (wHom Bw q.1) (Bw.side * q.2) ⊆ ⋃ b ∈ Tq.image (wEmb Bw), b.closedBox := by
    rw [← image_wHom_ball]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 (hcovq hz)
    exact mem_iUnion₂.2 ⟨wEmb Bw b, Finset.mem_image_of_mem _ hb, by
      rw [closedBox_wEmb]; exact ⟨z, hzb, rfl⟩⟩
  have hnear : ∀ b ∈ Tq.image (wEmb Bw), ∀ z ∈ b.closedBox,
      ‖z - (wEmb Bw Bp).center‖ ≤ 3 * (wEmb Bw Bp).side := by
    intro b hb z hz
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
    rw [closedBox_wEmb] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    rw [center_wEmb, norm_wHom_sub, side_wEmb]
    have := (hT b0 (hTq hb0)).2 z0 hz0
    nlinarith
  have hθ : ∀ b ∈ Tq.image (wEmb Bw), etaChaos W γ δh b.closedBox ω ≤ θ := by
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
    exact hopen b0 (hTq hb0)
  rw [wPullMeas_ball, dzzWall_ball_of_subset _ hballB]
  refine (dzzMuIn_ball_le_of_boxes hup (hballB.trans (closedBox_sub_dzzV' Bw)) _ hcov' hnear
    hθ).trans ?_
  refine le_trans ?_ hKθ
  exact mul_le_mul_left (by exact_mod_cast (Finset.card_image_le).trans hTq4) _

set_option maxHeartbeats 1000000 in
/-- **Walled DZZ (eq-B-good-Psi) + the union over the cells inside the wall, explicit
parameters** (copy of `start_bound_explicitS`; `x` is the pulled-back point). -/
theorem start_bound_explicitSW (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (α : ℝ) (G : ℝ → Set Ω) {δ₀ : ℝ}
    (hup : ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ B : DyBox, δ ^ dzzCmc γ ≤ B.side → ∀ ω ∈ G δ,
      approxLQG γ W ω B ≤ δ ^ 2 → ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - B.center‖ ≤ 3 * B.side) →
        wickQArea γ W ω b'.closedBox ≤
          ENNReal.ofReal (Real.exp (2 * α * γ * Real.sqrt (Real.log δ⁻¹) *
            Real.log (Real.log δ⁻¹)) * δ ^ 2 / B.side ^ 2) *
          etaChaos W γ ((2 : ℝ)⁻¹ ^ (B.n + 2 * kL37 γ δ)) b'.closedBox ω)
    {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) δ₀) (hδ1 : δ < 1) (Bw : DyBox)
    (hδs : δ ^ dzzCMc γ < Bw.side) {q j : ℕ}
    (hq3 : 3 ≤ q) (hj : 1 ≤ 2 ^ j * rP32 γ δ) {x : ℂ} (hx : x ∈ dzzVIn (rP32 γ δ / Bw.side))
    (hM : (8 * 2 ^ q + 4 * j + 16 : ℝ) ≤ δ ^ (-(dzzCMc γ / 2)) * lamP32 δ) :
    P (startPhiCOn γ W (fun ω => dzzWall Bw.closedBox (dzzMuIn γ W ω)) Bw (rP32 γ δ / Bw.side) δ
      (dzzCMc γ / 2) x)ᶜ ≤
      P (cellSizeEvent γ W δ)ᶜ + P (G δ)ᶜ +
        ENNReal.ofReal (9 * ⌊dzzCmc γ * Real.logb 2 δ⁻¹⌋₊ *
          (16 * (8 * 2 ^ q + 4 * j + 16) * ((2 : ℝ)⁻¹ ^ q) ^ 2 *
            Real.exp (2 * α * γ * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)))) := by
  classical
  obtain ⟨hδ0, hδδ₀⟩ := hδ
  set r := rP32 γ δ with hrdef
  have hr : 0 < r := (isClipDepth_rP32 γ δ ⟨hδ0, hδ1⟩).1
  have hsw := wside_pos Bw
  have hsw1 : Bw.side ≤ 1 := by unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  set rp := r / Bw.side with hrpdef
  have hrp : 0 < rp := div_pos hr hsw
  have hrrp : r ≤ rp := by rw [hrpdef, le_div_iff₀ hsw]; nlinarith
  have hjp : 1 ≤ 2 ^ j * rp := hj.trans (mul_le_mul_of_nonneg_left hrrp (by positivity))
  set M : ℝ := 8 * 2 ^ q + 4 * j + 16 with hMdef
  set E := 2 * α * γ * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹) with hEdef
  set C := dzzCmc γ with hCdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  set K := ⌊C * Real.logb 2 δ⁻¹⌋₊ with hKdef
  set t : ℝ := (2 : ℝ)⁻¹ ^ q with htdef
  have hM0' : 0 ≤ M := by rw [hMdef]; positivity
  have hcov : ∀ b : DyBox, ∃ S T, (1 ≤ b.n → x ∈ b.largeBox →
      (S.card : ℝ) ≤ M ∧ T.card ≤ 4 * S.card ∧ ∀ b' ∈ T, b'.n = b.n + q) ∧
      (1 ≤ b.n → x ∈ b.largeBox → rp ≤ b.side / 2 → StartCover b (b.n + q) rp x M S T) := by
    intro b
    by_cases h : 1 ≤ b.n ∧ x ∈ b.largeBox ∧ rp ≤ b.side / 2
    · obtain ⟨S, T, hST⟩ := p32StartGeomS b (b.n + q) j rp x h.1 (by omega) hrp h.2.2
        ((pow_le_one₀ (by norm_num) (by norm_num)).trans hjp) hx h.2.1
      rw [show b.n + q - b.n = q by omega] at hST
      exact ⟨S, T, fun _ _ => ⟨hST.1, hST.2.1, fun b' hb' => (hST.2.2.2.2 b' hb').1⟩,
        fun _ _ _ => hST⟩
    · refine ⟨∅, ∅, fun _ _ => ⟨by simpa using hM0', by simp, by simp⟩,
        fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose Sf Tf hST using hcov
  choose F hF9 hF using fun n => exists_finset_largeBox n x
  set θb : DyBox → ℝ := fun b => (wEmb Bw b).side ^ 2 * Real.exp (-E) / 4 with hθb
  have hθb0 : ∀ b, 0 < θb b := fun b => by
    have := (wEmb Bw b).side_pos'; simp only [hθb]; positivity
  set Bad : DyBox → Set Ω := fun b => {ω | 1 ≤ b.n ∧ x ∈ b.largeBox ∧ ∃ b' ∈ Tf b,
    ENNReal.ofReal (θb b) ≤ etaChaos W γ ((2 : ℝ)⁻¹ ^ ((wEmb Bw b).n + 2 * kL37 γ δ))
      (wEmb Bw b').closedBox ω}
    with hBad
  -- the inclusion
  have hsub : (startPhiCOn γ W (fun ω => dzzWall Bw.closedBox (dzzMuIn γ W ω)) Bw rp δ
      (dzzCMc γ / 2) x)ᶜ ⊆
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
    obtain ⟨hs1, hs2⟩ := hS.2 _ hb
    rw [← hCdef] at hs1
    have hn1 : 1 ≤ b.n := by
      by_contra h0
      have h0' : b.n = 0 := by omega
      have : (wEmb Bw b).side = Bw.side := by
        rw [side_wEmb]; unfold DyBox.side; rw [h0', pow_zero, mul_one]
      linarith
    have hnK' : (wEmb Bw b).n ≤ K := by
      rw [hKdef]
      apply Nat.le_floor
      have h1 := Real.log_le_log (by positivity) hs1
      rw [Real.log_rpow hδ0, hlogδ] at h1
      have h2 : Real.log (wEmb Bw b).side = -((wEmb Bw b).n * Real.log 2) := by
        unfold DyBox.side; rw [Real.log_pow, Real.log_inv]; ring
      rw [h2] at h1
      rw [Real.logb, ← hLdef, mul_div_assoc', le_div_iff₀ hlog2]
      linarith
    have hnK : b.n ≤ K := by
      have : (wEmb Bw b).n = Bw.n + b.n := rfl
      omega
    have hopen : ∀ b' ∈ Tf b, etaChaos W γ ((2 : ℝ)⁻¹ ^ ((wEmb Bw b).n + 2 * kL37 γ δ))
        (wEmb Bw b').closedBox ω ≤ ENNReal.ofReal (θb b) := by
      intro b' hb'
      by_contra hc
      exact hnB b.n (Finset.mem_Icc.2 ⟨hn1, hnK⟩) b (hF b.n b rfl hxb)
        ⟨hn1, hxb, b', hb', (not_le.1 hc).le⟩
    have hKθ : 4 * (ENNReal.ofReal (Real.exp E * δ ^ 2 / (wEmb Bw b).side ^ 2) *
        ENNReal.ofReal (θb b)) ≤ ENNReal.ofReal (δ ^ 2) := by
      have := (wEmb Bw b).side_pos'
      rw [← ENNReal.ofReal_mul (by positivity), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
        ← ENNReal.ofReal_mul (by norm_num)]
      apply le_of_eq; congr 1
      simp only [hθb]
      rw [Real.exp_neg]
      field_simp
    have hrs : rp ≤ b.side / 2 := by
      have h1 : r ≤ δ ^ dzzCmc γ / 8 := by
        rw [hrdef, rP32]
        have : (2⁻¹ : ℝ) ^ kL37 γ δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have : 0 < δ ^ dzzCmc γ := Real.rpow_pos_of_pos hδ0 _
        have := mul_le_mul_of_nonneg_left ‹(2⁻¹ : ℝ) ^ kL37 γ δ ≤ 1› this.le
        linarith
      rw [← hCdef] at h1
      have := b.side_pos'
      have hws : (wEmb Bw b).side = Bw.side * b.side := side_wEmb Bw b
      rw [hrpdef, div_le_iff₀ hsw]
      nlinarith
    exact ballPathLeC_of_geomOn ((hST b).2 hn1 hxb hrs)
      (hup δ ⟨hδ0, hδδ₀⟩ (wEmb Bw b) hs1 ω hGω hb.1.le) hopen hKθ hM
  -- the probability of a bad box
  set Q : ℝ := 16 * M * t ^ 2 * Real.exp E with hQ
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hBadQ : ∀ b, P (Bad b) ≤ ENNReal.ofReal Q := by
    intro b
    by_cases h : 1 ≤ b.n ∧ x ∈ b.largeBox
    · obtain ⟨hS, hTS, hT⟩ := (hST b).1 h.1 h.2
      refine (measure_mono (t := {ω | ∃ b' ∈ (Tf b).image (wEmb Bw), ENNReal.ofReal (θb b) ≤
        etaChaos W γ ((2 : ℝ)⁻¹ ^ ((wEmb Bw b).n + 2 * kL37 γ δ)) b'.closedBox ω})
        fun ω hω => by
          obtain ⟨b', hb', hge⟩ := hω.2.2
          exact ⟨wEmb Bw b', Finset.mem_image_of_mem _ hb', hge⟩).trans ?_
      refine (measure_exists_etaChaos_ge_le hW γ _ ((Tf b).image (wEmb Bw))
        (ENNReal.ofReal_pos.2 (hθb0 b)).ne' ENNReal.ofReal_ne_top).trans ?_
      rw [Finset.sum_image (fun b₁ _ b₂ _ h => wEmb_injective Bw h)]
      have hc : ∀ b' ∈ Tf b, volume (wEmb Bw b').closedBox / ENNReal.ofReal (θb b) =
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((wEmb Bw b).n + q)) ^ 2 / ENNReal.ofReal (θb b) := by
        intro b' hb'
        have e : (wEmb Bw b').n = (wEmb Bw b).n + q := by
          simp only [wEmb]; rw [hT b' hb']; ring
        rw [volume_closedBox_eq, DyBox.side, e, ENNReal.ofReal_pow (by positivity)]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
        ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_div_of_pos (hθb0 b),
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hcard : ((Tf b).card : ℝ) ≤ 4 * M := by
        have : ((Tf b).card : ℝ) ≤ 4 * (Sf b).card := by exact_mod_cast hTS
        linarith
      have e : ((2 : ℝ)⁻¹ ^ ((wEmb Bw b).n + q)) ^ 2 / θb b = 4 * t ^ 2 * Real.exp E := by
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
