/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2Box at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
# DZZ §2.2: Gaussian tail of the supremum of a field on a small box (task P2-DZZPRE, WP-112)

The step used repeatedly in Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`): proofs of
Lemma 2.6 (l. 556–567), Lemma 2.7 (l. 573–592, "Combined with Lemmas 2.1 and 2.3 this gives
(eq-boring-2)"), Lemma 2.8 (l. 616–621) and Lemma 2.9 (l. 628–633): a continuous centered Gaussian
field on a box `Q` of side `b` with `E(X_v − X_u)² ≤ L|u − v|` and `Var X_v ≤ σ²` has
`E sup_Q X ≤ C_F √(L b)` (DZZ Lemma 2.3, `SupTail.dzz_lemma23_continuous`, after rescaling) and
hence, by the Borell–TIS inequality (the supremum form of DZZ Lemma 2.1,
`SupTail.tail_iSup_abs_le_gaussian`), `P(sup_Q |X| ≥ x) ≤ 2 e^{M²/(2σ²)} e^{−x²/(4σ²)}` for
every `M ≥ C_F √(L b)`.

* `dzz_box_sup_abs_tail` — this statement.
* `exists_mem_subBox`, `subBox_subset` — the box `ferniqueBox x₀ s` is the union of the `m²`
  sub-boxes `subBox x₀ s m k l` of side `s/m` (DZZ's dyadic sub-squares, `eq-def-mathfrak-C`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Gaussian tail of `sup_Q |X|` on a box** (DZZ Lemmas 2.1 + 2.3, as used in the proofs of
Lemmas 2.6–2.9). -/
theorem dzz_box_sup_abs_tail {X : ℂ → Ω → ℝ} (hX : IsGaussianProcess X P)
    (h0 : ∀ v, ∫ ω, X v ω ∂P = 0) {y : ℂ} {b L σ : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hc : ∀ ω, ContinuousOn (fun v => X v ω) (ferniqueBox y b))
    (hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b,
      ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ L * ‖u - v‖)
    (hvar : ∀ v ∈ ferniqueBox y b, Var[X v; P] ≤ σ ^ 2) {M : ℝ}
    (hM : ferniqueCF * Real.sqrt (L * b) ≤ M) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x ≤ ⨆ v : ferniqueBox y b, |X v ω|} ≤
      2 * Real.exp (M ^ 2 / (2 * σ ^ 2)) * Real.exp (-x ^ 2 / (2 * (2 * σ ^ 2))) := by
  set B := ferniqueBox y b
  have : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox y b)
  have : Nonempty B := ⟨⟨y, mem_ferniqueBox_self hb.le⟩⟩
  set XB : B → Ω → ℝ := fun v => X v
  have hXB : IsGaussianProcess XB P := hX.comp_right (fun v : B => (v : ℂ))
  have hLb : 0 < L * b := mul_pos hL hb
  set c : ℝ := (Real.sqrt (L * b))⁻¹ with hc_def
  have hsq : 0 < Real.sqrt (L * b) := Real.sqrt_pos.2 hLb
  have hc0 : 0 < c := inv_pos.2 hsq
  have hc2 : c ^ 2 * L = b⁻¹ := by
    rw [hc_def, inv_pow, Real.sq_sqrt hLb.le]; field_simp
  have hincG : ∀ (ε : ℝ), ε ^ 2 = 1 → ∀ u ∈ B, ∀ v ∈ B,
      ∫ ω, (ε * c * X v ω - ε * c * X u ω) ^ 2 ∂P ≤ ‖u - v‖ / b := by
    intro ε hε u hu v hv
    have e : (fun ω => (ε * c * X v ω - ε * c * X u ω) ^ 2) =
        fun ω => c ^ 2 * (X v ω - X u ω) ^ 2 := by
      funext ω; rw [← mul_sub, mul_pow, mul_pow, hε, one_mul]
    rw [e, integral_const_mul]
    calc c ^ 2 * ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ c ^ 2 * (L * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left (hinc u hu v hv) (sq_nonneg c)
      _ = ‖u - v‖ / b := by rw [← mul_assoc, hc2]; ring
  have hsupG : ∀ (ε : ℝ), ε ^ 2 = 1 →
      Integrable (fun ω => ⨆ v : B, ε * c * X v ω) P ∧
        ∫ ω, (⨆ v : B, ε * c * X v ω) ∂P ≤ ferniqueCF := by
    intro ε hε
    refine dzz_lemma23_continuous hb ?_ (fun v _ => ?_) (hincG ε hε)
      (fun ω => continuousOn_const.mul (hc ω))
    · exact (hXB.smul fun _ => ε * c).congr fun v => Eventually.of_forall fun ω => rfl
    · rw [integral_const_mul, h0, mul_zero]
  have hsup_eq : ∀ (ε : ℝ) ω, (⨆ v : B, ε * X v ω) = c⁻¹ * ⨆ v : B, ε * c * X v ω := by
    intro ε ω
    rw [Real.mul_iSup_of_nonneg (inv_nonneg.2 hc0.le)]
    congr 1; funext v; field_simp
  have hYsup : ∀ (ε : ℝ), ε ^ 2 = 1 → Integrable (fun ω => ⨆ v : B, ε * X v ω) P ∧
      ∫ ω, (⨆ v : B, ε * X v ω) ∂P ≤ M := by
    intro ε hε
    obtain ⟨h1, h2⟩ := hsupG ε hε
    simp_rw [hsup_eq ε]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hc0.le)).trans ?_
    rw [hc_def, inv_inv, mul_comm]
    exact hM
  obtain ⟨hi1, hM1⟩ := hYsup 1 (by norm_num)
  obtain ⟨hi2, hM2⟩ := hYsup (-1) (by norm_num)
  simp only [one_mul, neg_one_mul] at hi1 hM1 hi2 hM2
  exact tail_iSup_abs_le_gaussian hXB (fun v => h0 v)
    (fun ω => continuousOn_iff_continuous_domRestrict.1 (hc ω)) hi1 hi2 hM1 hM2
    (fun v => hvar v v.2) hx

/-- The sub-box of `ferniqueBox x₀ s` with lower-left corner `x₀ + (k s/m, l s/m)`. -/
def subBox (x₀ : ℂ) (s : ℝ) (m k l : ℕ) : Set ℂ :=
  ferniqueBox (x₀ + ⟨k * (s / m), l * (s / m)⟩) (s / m)

/-- One-dimensional covering: `[0, s] = ⋃_{k < m} [k s/m, (k+1) s/m]`. -/
lemma exists_fin_mem_Icc {s y : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m) (hy0 : 0 ≤ y)
    (hys : y ≤ s) : ∃ k : Fin m, (k : ℝ) * (s / m) ≤ y ∧ y ≤ (k : ℝ) * (s / m) + s / m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hh : 0 < s / m := div_pos hs hm'
  by_cases hk : ⌊y / (s / m)⌋₊ < m
  · refine ⟨⟨_, hk⟩, ?_, ?_⟩
    · simp only
      have := Nat.floor_le (div_nonneg hy0 hh.le)
      rwa [le_div_iff₀ hh] at this
    · simp only
      have := Nat.lt_floor_add_one (y / (s / m))
      rw [div_lt_iff₀ hh] at this
      linarith
  · push_neg at hk
    refine ⟨⟨m - 1, Nat.sub_lt hm one_pos⟩, ?_, ?_⟩
    · simp only
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hm.ne'), Nat.cast_one]
      have h1 : (m : ℝ) ≤ y / (s / m) :=
        le_trans (by exact_mod_cast hk) (Nat.floor_le (div_nonneg hy0 hh.le))
      rw [le_div_iff₀ hh] at h1
      nlinarith
    · simp only
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hm.ne'), Nat.cast_one]
      have : ((m : ℝ) - 1) * (s / m) + s / m = s := by field_simp; ring
      linarith

lemma exists_mem_subBox {x₀ v : ℂ} {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m)
    (hv : v ∈ ferniqueBox x₀ s) : ∃ k l : Fin m, v ∈ subBox x₀ s m k l := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv
  obtain ⟨k, hk1, hk2⟩ :=
    exists_fin_mem_Icc hs hm (sub_nonneg.2 h1) (by linarith : v.re - x₀.re ≤ s)
  obtain ⟨l, hl1, hl2⟩ :=
    exists_fin_mem_Icc hs hm (sub_nonneg.2 h3) (by linarith : v.im - x₀.im ≤ s)
  refine ⟨k, l, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩ <;> simp only [Complex.add_re, Complex.add_im] <;> linarith

lemma subBox_subset {x₀ : ℂ} {s : ℝ} (hs : 0 < s) {m : ℕ} (k l : Fin m) :
    subBox x₀ s m k l ⊆ ferniqueBox x₀ s := by
  have hm : 0 < m := Fin.pos k
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hh : 0 < s / m := div_pos hs hm'
  have hk : (k : ℝ) * (s / m) + s / m ≤ s := by
    have : ((k : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast k.2
    calc (k : ℝ) * (s / m) + s / m = ((k : ℝ) + 1) * (s / m) := by ring
      _ ≤ m * (s / m) := mul_le_mul_of_nonneg_right this hh.le
      _ = s := by field_simp
  have hl : (l : ℝ) * (s / m) + s / m ≤ s := by
    have : ((l : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast l.2
    calc (l : ℝ) * (s / m) + s / m = ((l : ℝ) + 1) * (s / m) := by ring
      _ ≤ m * (s / m) := mul_le_mul_of_nonneg_right this hh.le
      _ = s := by field_simp
  have hk0 : 0 ≤ (k : ℝ) * (s / m) := by positivity
  have hl0 : 0 ≤ (l : ℝ) * (s / m) := by positivity
  rintro v ⟨⟨h1, h2⟩, h3, h4⟩
  simp only [Complex.add_re, Complex.add_im] at h1 h2 h3 h4
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end DZZ
end LQGMetric
