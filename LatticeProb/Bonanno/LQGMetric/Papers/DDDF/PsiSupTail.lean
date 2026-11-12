/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.PsiSupTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
# Sup tails of a Gaussian field on small boxes (DZZ Lemma 2.7, step (2.40); P2-DDDFPSI)

J. Ding, O. Zeitouni, F. Zhang, arXiv:1807.00422, proof of Lemma 2.7 (LaTeX l. 557–575, in
`LBM_LGDarXiv.tex`): for the per-scale difference `Δ_i` with
`Var(Δ_i(v) − Δ_i(u)) ≤ O(1) 2^i |u − v|`, "Lemmas 2.2 (concentration) and 2.3 (Fernique)" give
the tail of the maximal oscillation on boxes of side `≈ 2^{-i} i^{-4}`, and a union bound over the
boxes. DDDF (arXiv:1904.08021, `tightness.tex` l. 431–437) adapt this to `D_k = φ_{k−1,k} − ψ_{k−1,k}`.

Here, for a centered continuous Gaussian field `G` on `ℂ` with
`E(G v − G u)² ≤ A |u − v|` and `Var G ≤ σ²`:

* `tail_iSup_abs_box`: on a box `B` of side `b`, `P(sup_B |G| ≥ C_F √(A b) + u) ≤ 2 e^{−u²/(2σ²)}`
  (DZZ Lemma 2.3 = `dzz_lemma23_continuous` after scaling by `√(A b)`, then Borell–TIS in the
  form `SupTail.tail_iSup_abs_le`). DZZ apply Lemma 2.2 to the oscillation `Δ_i(u) − Δ_i(v)`
  and bound the grid values `Δ_i(u)` separately ((2.40)–(2.41)); applying Borell–TIS to `|G|`
  on the box directly (variance `≤ σ²`) merges the two steps (own simplification, proposed
  DEVIATION D-DDDF-PSI-2).
* `tail_iSup_abs_square`: the union bound over the `n²` boxes of side `R/n` covering
  `[0,R]²`: `P(sup_{[0,R]²} |G| ≥ C_F √(AR/n) + u) ≤ 2 n² e^{−u²/(2σ²)}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace LQGMetric

namespace SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma iSup_mul_left {T : Type*} [Nonempty T] {f : T → ℝ} (hf : BddAbove (range f)) {κ : ℝ}
    (hκ : 0 ≤ κ) : ⨆ t, κ * f t = κ * ⨆ t, f t :=
  (Real.mul_iSup_of_nonneg hκ f).symm

/-- **Sup tail on one box.** -/
theorem tail_iSup_abs_box {x₀ : ℂ} {b : ℝ} (hb : 0 < b) {G : ℂ → Ω → ℝ}
    (hG : IsGaussianProcess G P) (h0 : ∀ v, ∫ ω, G v ω ∂P = 0)
    (hc : ∀ ω, Continuous fun v => G v ω) {A : ℝ} (hA : 0 < A)
    (hinc : ∀ u v, ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ A * ‖u - v‖) {σ : ℝ} (hσ : 0 < σ)
    (hvar : ∀ v, Var[G v; P] ≤ σ ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | ferniqueCF * √(A * b) + u ≤ ⨆ v : ferniqueBox x₀ b, |G v ω|} ≤
      2 * exp (-u ^ 2 / (2 * σ ^ 2)) := by
  set B := ferniqueBox x₀ b
  haveI : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox x₀ b)
  haveI : Nonempty B := ⟨⟨x₀, mem_ferniqueBox_self hb.le⟩⟩
  set κ : ℝ := √(A * b)
  have hκ : 0 < κ := Real.sqrt_pos.mpr (mul_pos hA hb)
  have hκ2 : κ ^ 2 = A * b := Real.sq_sqrt (mul_pos hA hb).le
  set H : ℂ → Ω → ℝ := fun v ω => κ⁻¹ * G v ω
  have hH : IsGaussianProcess H P := by
    have := hG.smul (fun _ => κ⁻¹)
    simpa [H, smul_eq_mul] using this
  have hH0 : ∀ v, ∫ ω, H v ω ∂P = 0 := fun v => by simp [H, integral_const_mul, h0]
  have hHinc : ∀ u v, ∫ ω, (H v ω - H u ω) ^ 2 ∂P ≤ ‖u - v‖ / b := by
    intro u v
    have e : (fun ω => (H v ω - H u ω) ^ 2) = fun ω => (κ ^ 2)⁻¹ * (G v ω - G u ω) ^ 2 := by
      funext ω; simp only [H]; field_simp
    rw [e, integral_const_mul, hκ2]
    calc (A * b)⁻¹ * ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ (A * b)⁻¹ * (A * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left (hinc u v) (by positivity)
      _ = ‖u - v‖ / b := by field_simp
  have hHB : IsGaussianProcess (fun v : B => H v) P := hH.comp_right (fun v : B => (v : ℂ))
  have hHc : ∀ ω, Continuous fun v : B => H v ω := fun ω =>
    (continuous_const.mul (hc ω)).comp continuous_subtype_val
  have hF := dzz_lemma23_continuous hb hHB (fun v _ => hH0 v) (fun u _ v _ => hHinc u v)
    (fun ω => (continuous_const.mul (hc ω)).continuousOn)
  have hF' := dzz_lemma23_continuous hb (G := fun v ω => -H v ω)
    ((isGaussianProcess_neg hH).comp_right (fun v : B => (v : ℂ)))
    (fun v _ => by simp [integral_neg, hH0]) (fun u _ v _ => by
      have := hHinc u v
      have e : (fun ω => (-H v ω - -H u ω) ^ 2) = fun ω => (H v ω - H u ω) ^ 2 := by
        funext ω; ring
      rw [e]; exact this)
    (fun ω => (continuous_const.mul (hc ω)).neg.continuousOn)
  have hvarH : ∀ v : B, Var[(fun v : B => H v) v; P] ≤ (σ / κ) ^ 2 := by
    intro v
    simp only [H]
    rw [variance_const_mul, div_pow, inv_pow, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hvar v) (sq_nonneg κ)
  have hT := tail_iSup_abs_le hHB (fun v => hH0 v) hHc hF.1 hF'.1 hF.2 hF'.2 hvarH
    (u := u / κ) (by positivity)
  have hset : {ω | ferniqueCF * κ + u ≤ ⨆ v : B, |G v ω|} ⊆
      {ω | ferniqueCF + u / κ ≤ ⨆ v : B, |(fun v : B => H v) v ω|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hbdd : BddAbove (range fun v : B => |H v ω|) :=
      bddAbove_range_of_continuous (X := fun (v : B) ω => |H v ω|)
        (fun ω => (hHc ω).abs) ω
    have e : ⨆ v : B, |G v ω| = κ * ⨆ v : B, |H v ω| := by
      rw [← iSup_mul_left hbdd hκ.le]
      congr 1; funext v
      simp only [H, abs_mul, abs_inv, abs_of_pos hκ]
      field_simp
    rw [e] at hω
    rw [add_div' _ _ _ hκ.ne', div_le_iff₀ hκ]
    linarith
  have hP := hG.isProbabilityMeasure
  refine (measureReal_mono hset (measure_ne_top _ _)).trans (hT.trans (le_of_eq ?_))
  congr 2
  rw [div_pow, div_pow]
  field_simp


/-- Every `t ∈ [0,1]` lies in some `[i/n, (i+1)/n]`, `i < n`. -/
lemma exists_mem_grid {n : ℕ} (hn : 0 < n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ i : Fin n, (i : ℝ) / n ≤ t ∧ t ≤ (i : ℝ) / n + 1 / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases h : ⌊t * n⌋₊ < n
  · refine ⟨⟨⌊t * n⌋₊, h⟩, ?_, ?_⟩
    · rw [div_le_iff₀ hn']; exact Nat.floor_le (by positivity)
    · rw [← add_div, le_div_iff₀ hn']; exact (Nat.lt_floor_add_one _).le
  · push_neg at h
    have h1 : (n : ℝ) ≤ t * n := by
      have := Nat.floor_le (show 0 ≤ t * n by positivity)
      have h2 : ((n : ℕ) : ℝ) ≤ (⌊t * n⌋₊ : ℝ) := Nat.cast_le.mpr h
      linarith
    have ht : t = 1 := le_antisymm ht1 (by nlinarith)
    refine ⟨⟨n - 1, Nat.sub_lt hn one_pos⟩, ?_, ?_⟩
    · rw [ht, div_le_one hn']; simp
    · rw [ht, ← add_div]
      simp only [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne'), Nat.cast_one, sub_add_cancel,
        div_self hn'.ne', le_refl]

/-- Every `t ∈ [0,R]` lies in some `[iR/n, iR/n + R/n]`, `i < n`. -/
lemma exists_mem_gridR {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ R) : ∃ i : Fin n, (i : ℝ) * R / n ≤ t ∧ t ≤ (i : ℝ) * R / n + R / n := by
  obtain ⟨i, h1, h2⟩ := exists_mem_grid hn (div_nonneg ht0 hR.le) ((div_le_one hR).mpr ht1)
  refine ⟨i, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right h1 hR.le
    rw [div_mul_cancel₀ _ hR.ne'] at this
    calc (i : ℝ) * R / n = (i : ℝ) / n * R := by ring
      _ ≤ t := this
  · have := mul_le_mul_of_nonneg_right h2 hR.le
    rw [div_mul_cancel₀ _ hR.ne'] at this
    calc t ≤ ((i : ℝ) / n + 1 / n) * R := this
      _ = (i : ℝ) * R / n + R / n := by ring

/-- The `n²` boxes of side `R/n` cover the square `[0,R]²`. -/
lemma exists_mem_box {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : x ∈ ferniqueBox 0 R) :
    ∃ ij : Fin n × Fin n,
      x ∈ ferniqueBox ((((ij.1 : ℝ) * R / n : ℝ) : ℂ) + (((ij.2 : ℝ) * R / n : ℝ) : ℂ) *
        Complex.I) (R / n) := by
  simp only [ferniqueBox, Complex.zero_re, Complex.zero_im, zero_add] at hx
  obtain ⟨hre, him⟩ := (Complex.mem_reProdIm).mp hx
  obtain ⟨i, hi1, hi2⟩ := exists_mem_gridR hn hR hre.1 hre.2
  obtain ⟨j, hj1, hj2⟩ := exists_mem_gridR hn hR him.1 him.2
  refine ⟨(i, j), ?_⟩
  simp only [ferniqueBox]
  refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    exact ⟨hi1, hi2⟩
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, mul_zero,
      Complex.ofReal_re, Complex.I_im, mul_one, zero_add, add_zero]
    exact ⟨hj1, hj2⟩

lemma bddAbove_abs_of_compact {B : Set ℂ} (hB : IsCompact B) {f : ℂ → ℝ} (hf : Continuous f) :
    BddAbove (range fun v : B => |f v|) := by
  exact (hB.image (continuous_abs.comp hf)).bddAbove.mono (by rintro _ ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩)

lemma iSup_ofReal_le {B : Set ℂ} (hB : IsCompact B) {f : ℂ → ℝ} (hf : Continuous f) :
    ⨆ x ∈ B, ENNReal.ofReal |f x| ≤ ENNReal.ofReal (⨆ v : B, |f v|) :=
  iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal
    (le_ciSup (f := fun v : B => |f v|) (bddAbove_abs_of_compact hB hf) ⟨x, hx⟩)

/-- **Union bound over the boxes of side `R/n`**:
`P(sup_{[0,R]²} |G| ≥ C_F √(AR/n) + u) ≤ 2 n² e^{−u²/(2σ²)}`. -/
theorem tail_iSup_abs_square {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) {G : ℂ → Ω → ℝ}
    (hG : IsGaussianProcess G P) (h0 : ∀ v, ∫ ω, G v ω ∂P = 0)
    (hc : ∀ ω, Continuous fun v => G v ω) {A : ℝ} (hA : 0 < A)
    (hinc : ∀ u v, ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ A * ‖u - v‖) {σ : ℝ} (hσ : 0 < σ)
    (hvar : ∀ v, Var[G v; P] ≤ σ ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | ENNReal.ofReal (ferniqueCF * √(A * (R / n)) + u) ≤
        ⨆ x ∈ ferniqueBox 0 R, ENNReal.ofReal |G x ω|} ≤
      ENNReal.ofReal (2 * n ^ 2 * exp (-u ^ 2 / (2 * σ ^ 2))) := by
  have hP := hG.isProbabilityMeasure
  have hn' : (0 : ℝ) < R / n := by positivity
  set c := ferniqueCF * √(A * (R / n)) + u
  have hc0 : 0 ≤ c := by have := ferniqueCF_pos; positivity
  let z : Fin n × Fin n → ℂ := fun ij =>
    (((ij.1 : ℝ) * R / n : ℝ) : ℂ) + (((ij.2 : ℝ) * R / n : ℝ) : ℂ) * Complex.I
  have hsub : {ω | ENNReal.ofReal c ≤ ⨆ x ∈ ferniqueBox 0 R, ENNReal.ofReal |G x ω|} ⊆
      ⋃ ij, {ω | c ≤ ⨆ v : ferniqueBox (z ij) (R / n), |G v ω|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    by_contra hne
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hne
    have hlt : ⨆ x ∈ ferniqueBox 0 R, ENNReal.ofReal |G x ω| < ENNReal.ofReal c := by
      have hfin : ∀ ij, ⨆ x ∈ ferniqueBox (z ij) (R / n), ENNReal.ofReal |G x ω| <
          ENNReal.ofReal c := by
        intro ij
        have : Nonempty (ferniqueBox (z ij) (R / n)) :=
          ⟨⟨z ij, mem_ferniqueBox_self hn'.le⟩⟩
        refine lt_of_le_of_lt (iSup_ofReal_le (isCompact_ferniqueBox _ _) (hc ω)) ?_
        have h1 : |G (z ij) ω| ≤ ⨆ v : ferniqueBox (z ij) (R / n), |G v ω| :=
          le_ciSup (f := fun v : ferniqueBox (z ij) (R / n) => |G v ω|)
            (bddAbove_abs_of_compact (isCompact_ferniqueBox _ _) (hc ω))
            ⟨z ij, mem_ferniqueBox_self hn'.le⟩
        have hcpos : 0 < c := lt_of_le_of_lt ((abs_nonneg _).trans h1) (hne ij)
        exact (ENNReal.ofReal_lt_ofReal_iff hcpos).mpr (hne ij)
      have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
      obtain ⟨ij₀, hij₀⟩ := Finite.exists_max fun ij =>
        ⨆ x ∈ ferniqueBox (z ij) (R / n), ENNReal.ofReal |G x ω|
      refine lt_of_le_of_lt (iSup₂_le fun x hx => ?_) (hfin ij₀)
      obtain ⟨ij, hij⟩ := exists_mem_box hn hR hx
      exact (le_iSup₂_of_le (f := fun x (_ : x ∈ ferniqueBox (z ij) (R / n)) =>
        ENNReal.ofReal |G x ω|) x hij le_rfl).trans (hij₀ ij)
    exact absurd hω (not_le.mpr hlt)
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  have hbox : ∀ ij, P {ω | c ≤ ⨆ v : ferniqueBox (z ij) (R / n), |G v ω|} ≤
      ENNReal.ofReal (2 * exp (-u ^ 2 / (2 * σ ^ 2))) := by
    intro ij
    have h := tail_iSup_abs_box (x₀ := z ij) hn' hG h0 hc hA hinc hσ hvar hu
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h
  refine (Finset.sum_le_sum fun ij _ => hbox ij).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  push_cast; ring

end SupTail

end LQGMetric
