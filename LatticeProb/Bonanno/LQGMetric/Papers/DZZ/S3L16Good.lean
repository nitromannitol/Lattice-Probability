/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L16Good at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L16Count

/-!
# DZZ Lemma 3.16, second statement (eq-B-good) (P2-DZZ312)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 3.16 (eq-B-good), l. 1373–1375, proof
l. 1406–1412: on `{M_{γ,s}(B) ≤ δ²} ∩ 𝓔_{δ,α}`, every `B' ∈ 𝓑(B, ε*)` has `M_{γ,ε* s}(B') < δ²` except
with probability `≤ e^{−√(log δ⁻¹)}`.

Proof (following DZZ): (eq-LQG-tilde-B) is `approxLQG_fine_le_of_mem` (here with the band
`η^{s}_{ε* s}`, `j = 0`); (eq-for-B'-good) is the union bound over the `4^{k+1}` boxes of `𝓑(B, ε*)`
(`measureReal_boxColl_le`) with the Chernoff bound `measureReal_bandNorm_ge_le` at
`λ = 2/γ² + 1/2` and `Var η^{s}_{ε* s} ≤ log(1/ε*)` (`etaBandVar_le`). DZZ threshold the field at
`(1 + 1/γ + γ/4) log(1/ε*)`; we threshold the normalized exponent at `2 log(1/ε*) − X − 1` (`X` the
`𝓔_{δ,α}` error of (eq-LQG-tilde-B)) and get the exponent `−(4 − γ²)²/(8γ²) log(1/ε*) + O(X)`, which beats
`(ε*)^{-2}` boxes once `α* ≥ (λγα + 1)/q` (`q = l31q γ`). The `𝓔_{δ,α}` here is `eventEFine` (as in L3.7);
the a.s. event `decompEvent` is removed by `ae_decompEvent`.

* **`dzz_lemma316_good`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- The Chernoff parameter `λ = 2/γ² + 1/2`. -/
def l316lam (γ : ℝ) : ℝ := 2 / γ ^ 2 + 1 / 2

lemma one_le_l316lam {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 1 ≤ l316lam γ := by
  unfold l316lam
  have : γ ^ 2 < 4 := by nlinarith
  have : 1 / 2 ≤ 2 / γ ^ 2 := by rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  linarith

lemma l316_exponent {γ : ℝ} (hγ : 0 < γ) (ℓ X : ℝ) :
    2 * ℓ + (l316lam γ * (l316lam γ - 1) * γ ^ 2 * ℓ / 2 - l316lam γ * (2 * ℓ - X - 1)) =
      -(l31q γ * ℓ) + l316lam γ * (X + 1) := by
  unfold l316lam l31q
  field_simp
  ring

lemma center_mem_closedBox (b : DyBox) : b.center ∈ b.closedBox := by
  have := b.side_pos'
  simp only [DyBox.center, DyBox.closedBox, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ Lemma 3.16, (eq-B-good)**, for every `α > 0` and every `α* ≥ (λγα + 1)/q`. -/
theorem dzz_lemma316_good (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {α : ℝ}
    (hα : 0 < α) {αs : ℝ} (hαs : (l316lam γ * γ * α + 1) / l31q γ ≤ αs) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ b : DyBox,
      (b.n : ℝ) ≤ dzzCmc γ * Real.logb 2 δ⁻¹ →
        P ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
          {ω | ∃ b' ∈ boxColl b (epsStarN αs δ), δ ^ 2 ≤ approxLQG γ W ω b'}) ≤
          ENNReal.ofReal (Real.exp (-Real.sqrt (Real.log δ⁻¹))) := by
  have := hW.isProbabilityMeasure
  have hq : 0 < l31q γ := l31q_pos hγ hγ2
  have hlam := one_le_l316lam hγ hγ2
  have hαs0 : 0 < αs := lt_of_lt_of_le (by positivity) hαs
  have hCmc : 0 ≤ dzzCmc γ := dzzCmc_nonneg hγ hγ2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K₁ := l316lam γ * γ ^ 2 * Real.sqrt 8608 * Real.sqrt (dzzCmc γ + 4)
  set K₂ := Real.log 4 + l316lam γ
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  set L₀ := max (max 2 (1 / α)) (Real.exp (1 + K₁ + K₂))
  refine ⟨Real.exp (-L₀), Real.exp_pos _, fun δ hδ b hbn => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  set L := Real.log δ⁻¹ with hLdef
  have hLlog : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hLL₀ : L₀ < L := by
    have := Real.log_lt_log hδ0 hδ.2
    rw [Real.log_exp, hLlog] at this
    linarith
  have hL2 : 2 < L := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hLL₀
  have hL1 : 1 ≤ L := by linarith
  have hαL : 1 ≤ α * L := by
    have h := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hLL₀
    rw [div_lt_iff₀ hα] at h; linarith
  have hlogL : 1 + K₁ + K₂ < Real.log L := by
    have h := lt_of_le_of_lt (le_max_right _ _) hLL₀
    have := Real.log_lt_log (Real.exp_pos _) h
    rwa [Real.log_exp] at this
  set k := epsStarN αs δ with hkdef
  have hk : 1 ≤ k := one_le_epsStarN hαs0 (by linarith)
  set ℓ := (k : ℝ) * Real.log 2 with hℓ
  -- `ℓ ≥ α* √L log L`
  have hℓge : αs * Real.sqrt L * Real.log L ≤ ℓ := by
    have h := epsStar_le_thr αs δ
    unfold epsStar epsStarThr at h
    rw [← hkdef] at h
    have := Real.log_le_log (by positivity) h
    rw [Real.log_exp, Real.log_pow, Real.log_inv] at this
    linarith
  -- the error `X` of (eq-LQG-tilde-B)
  set X := γ * (α * Real.sqrt L * Real.log L) +
    γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4)) with hX
  set a := 2 * ℓ - X - 1 with ha
  -- the bad set
  set S : DyBox → Set Ω := fun bt => {ω | a ≤ bandNorm γ W bt (b.n + 0) ω}
  have hm : (2 : ℝ) ^ b.n ≤ δ ^ (-dzzCmc γ) := by
    rw [Real.rpow_def_of_pos hδ0, hLlog, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ b.n),
      Real.exp_le_exp, Real.log_pow]
    have : (b.n : ℝ) * Real.log 2 ≤ dzzCmc γ * L := by
      have := mul_le_mul_of_nonneg_right hbn hl2.le
      rwa [Real.logb, ← hLdef, show dzzCmc γ * (L / Real.log 2) * Real.log 2 = dzzCmc γ * L by
        field_simp] at this
    linarith
  have hsub : {ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
      {ω | ∃ b' ∈ boxColl b k, δ ^ 2 ≤ approxLQG γ W ω b'} ⊆
      (decompEvent W)ᶜ ∪ {ω | ∃ bt ∈ boxColl b k, ω ∈ S bt} := by
    rintro ω ⟨⟨hM, hE⟩, b', hb', hb'M⟩
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq, not_exists, not_and,
      not_le, S] at hcon
    obtain ⟨hdec, hall⟩ := hcon
    have hc : ‖b.center - b'.center‖ ≤ 8 * b.side := by
      have hmem := hb'.2 (center_mem_closedBox b')
      simp only [DyBox.largeBox, mem_ofPred_eq] at hmem
      have := Complex.norm_le_abs_re_add_abs_im (b.center - b'.center)
      rw [Complex.sub_re, Complex.sub_im, abs_sub_comm, abs_sub_comm b.center.im] at this
      have := b.side_pos'
      linarith [hmem.1, hmem.2]
    have hfine := approxLQG_fine_le_of_mem hW hγ hE.2 hdec hm
      (by rw [pow_zero]; nlinarith) (by rw [hb'.1]; omega) hc hM (hall b' hb').le
    have hratio : (b'.side / b.side) ^ 2 = Real.exp (-(2 * ℓ)) := by
      simp only [DyBox.side, hb'.1, pow_add]
      rw [mul_div_cancel_left₀ _ (by positivity), ← pow_mul, ← Real.exp_log
        (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (k * 2)), Real.log_pow, Real.log_inv]
      congr 1; push_cast; ring
    rw [hratio, ← hLdef] at hfine
    have : δ ^ 2 * Real.exp (-(2 * ℓ)) * Real.exp X * Real.exp a = δ ^ 2 * Real.exp (-1) := by
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; rw [ha]; ring
    rw [this] at hfine
    have : δ ^ 2 * Real.exp (-1) < δ ^ 2 := by
      have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      have : 0 < δ ^ 2 := by positivity
      nlinarith
    linarith
  -- probability of one bad box
  have hone : ∀ bt ∈ boxColl b k, P.real (S bt) ≤
      Real.exp (l316lam γ * (l316lam γ - 1) * γ ^ 2 * ℓ / 2 - l316lam γ * a) := by
    intro bt hbt
    refine measureReal_bandNorm_ge_le hW γ bt (b.n + 0) ?_ hlam
    have hside : bt.side = (2 : ℝ)⁻¹ ^ (b.n + k) := by simp only [DyBox.side, hbt.1]
    have hle : bt.side ≤ (2 : ℝ)⁻¹ ^ (b.n + 0) := by
      rw [hside]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine (etaBandVar_le bt.side_pos' hle bt.center).trans (le_of_eq ?_)
    rw [hside, add_zero, pow_add, div_mul_cancel_left₀ (by positivity), inv_pow, inv_inv,
      Real.log_pow]
  have hdec0 : P.real (decompEvent W)ᶜ = 0 := by
    rw [measureReal_def, show P (decompEvent W)ᶜ = 0 from ae_iff.mp (ae_decompEvent hW)]
    rfl
  have htot : P.real ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
      {ω | ∃ b' ∈ boxColl b k, δ ^ 2 ≤ approxLQG γ W ω b'}) ≤ Real.exp (-Real.sqrt L) := by
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans ?_)
    rw [hdec0, zero_add]
    refine (measureReal_boxColl_le b hk S (by positivity) hone).trans ?_
    have h2k : ((2 : ℝ) ^ (k + 1)) ^ 2 = 4 * Real.exp (2 * ℓ) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (k + 1)) ^ 2), Real.log_pow,
        Real.log_pow, show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm,
        ← Real.exp_add, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      congr 1; push_cast; ring
    rw [h2k, mul_assoc, ← Real.exp_add, l316_exponent hγ ℓ X,
      show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm,
      ← Real.exp_add, Real.exp_le_exp]
    -- the asymptotics
    have hsL : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
    have hlogpos : 0 < Real.log L := by linarith
    have hside : Real.log b.side⁻¹ ≤ dzzCmc γ * L := by
      rw [Real.log_inv, DyBox.log_side, neg_neg]
      have := mul_le_mul_of_nonneg_right hbn hl2.le
      rwa [Real.logb, ← hLdef, show dzzCmc γ * (L / Real.log 2) * Real.log 2 = dzzCmc γ * L by
        field_simp] at this
    have hsq : Real.sqrt (Real.log b.side⁻¹ + 4) ≤ Real.sqrt (dzzCmc γ + 4) * Real.sqrt L := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hX' : X ≤ γ * α * (Real.sqrt L * Real.log L) +
        γ ^ 2 * Real.sqrt 8608 * (Real.sqrt (dzzCmc γ + 4) * Real.sqrt L) := by
      have h8 : 0 ≤ γ ^ 2 * Real.sqrt 8608 := by positivity
      have := mul_le_mul_of_nonneg_left hsq h8
      have e : X = γ * α * (Real.sqrt L * Real.log L) +
          γ ^ 2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4) := by rw [hX]; ring
      rw [e]; linarith
    have hqℓ : (l316lam γ * γ * α + 1) * (Real.sqrt L * Real.log L) ≤ l31q γ * ℓ := by
      have h1 : (l316lam γ * γ * α + 1) ≤ l31q γ * αs := by
        have := (div_le_iff₀ hq).mp hαs
        linarith [mul_comm (l31q γ) αs]
      have h2 : 0 ≤ Real.sqrt L * Real.log L := by positivity
      calc (l316lam γ * γ * α + 1) * (Real.sqrt L * Real.log L)
          ≤ l31q γ * αs * (Real.sqrt L * Real.log L) := mul_le_mul_of_nonneg_right h1 h2
        _ = l31q γ * (αs * Real.sqrt L * Real.log L) := by ring
        _ ≤ l31q γ * ℓ := mul_le_mul_of_nonneg_left hℓge hq.le
    have hmain : Real.sqrt L * (1 + K₁ + K₂) ≤ Real.sqrt L * Real.log L :=
      mul_le_mul_of_nonneg_left hlogL.le (Real.sqrt_nonneg _)
    have hK₂L : K₂ ≤ K₂ * Real.sqrt L := le_mul_of_one_le_right hK₂ hsL
    have hK₁' : l316lam γ * (γ ^ 2 * Real.sqrt 8608 * (Real.sqrt (dzzCmc γ + 4) * Real.sqrt L)) =
        K₁ * Real.sqrt L := by ring
    have hlamX := mul_le_mul_of_nonneg_left hX' (by linarith : (0 : ℝ) ≤ l316lam γ)
    have e1 : l316lam γ * (X + 1) = l316lam γ * X + l316lam γ := by ring
    have e2 : l316lam γ * (γ * α * (Real.sqrt L * Real.log L) +
        γ ^ 2 * Real.sqrt 8608 * (Real.sqrt (dzzCmc γ + 4) * Real.sqrt L)) =
        l316lam γ * γ * α * (Real.sqrt L * Real.log L) + K₁ * Real.sqrt L := by
      rw [← hK₁']; ring
    have e3 : (l316lam γ * γ * α + 1) * (Real.sqrt L * Real.log L) =
        l316lam γ * γ * α * (Real.sqrt L * Real.log L) + Real.sqrt L * Real.log L := by ring
    have e4 : Real.sqrt L * (1 + K₁ + K₂) = Real.sqrt L + K₁ * Real.sqrt L + K₂ * Real.sqrt L := by
      ring
    rw [e1]
    linarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal htot

end DZZ
end LQGMetric
