/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.GaussianTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField

/-!
# Ding–Goswami §3: the Gaussian tail lemma and the tail part of Prop 3.3 (task P2-DGO, WP-105)

Source: J. Ding, S. Goswami, *Upper bounds on Liouville first passage percolation and Watabiki's
prediction*, arXiv:1610.09998, `literature/src/1610.09998/Watabiki_final.tex` (cited `DGo:`).
In the arXiv numbering used below, Lemma 3.1 is `lem-identity-in-law` (DGo:495), Lemma 3.2 is
`lem:smoothness` (DGo:528), Prop 3.3 is `prop:coupling` (DGo:549) and Lemma 3.4 is
`lem:gaussian_tail` (DGo:557). (Ding–Gwynne arXiv:1807.01072 cite the published numbering, in
which `lem:smoothness` is Lemma 3.1 and `prop:coupling` is Prop 3.2, DG:912, DG:1104.)

* `box_sup_tail`: one box: a continuous centred Gaussian field on a square of side `b` with
  `E(X_v − X_u)² ≤ L|u − v|` and `Var X_v ≤ σ²` has
  `P(sup X ≥ C_F √(L b) + u) ≤ e^{−u²/(2σ²)}`: DGo's (3.6)–(3.7) (DGo:574–582), with Dudley's
  bound (DGo cites Adler 1990 Thm 4.1) replaced by the equivalent chaining bound DZZ Lemma 2.3
  (`SupTail.dzz_lemma23_continuous`) and the Gaussian concentration inequality by Borell–TIS
  (`SupTail.tail_iSup_le`).
* `dgo_lemma34`: **DGo Lemma 3.4** (DGo:557–570) for a finite family of squares:
  `P(max_R max_{v∈R} Y_R(v) ≥ √(2C' log |𝔑|) + C'' + x) ≤ e^{−x²/(2C')}` with
  `C'' = C_F √C`. Proof: the per-box tail and a union bound (own route, see below).
* `dgo_prop33_tail_of_var` (file `DGo/CouplingTail.lean`): the step of the proof of
  **DGo Prop 3.3** after (3.9)–(3.10) (DGo:604–616): subdivide the square `V` into `m² ≍ δ^{-2}`
  squares of diameter `≤ δ` and apply Lemma 3.4; `dgo_prop33_of_var` puts the result in the
  form `C √(log δ⁻¹) + x`.

Deviation (proposed DGo-1): DGo prove Lemma 3.4 by bounding `E max_R max_v Y_R` (eq. (3.8)) and
applying Gaussian concentration to the whole family, which needs the `Y_R` to be jointly
Gaussian (not stated in the lemma). We use instead the per-box Borell–TIS tail and a union
bound, which gives the same inequality, with the same constant `C'' = C'''`, for families that
need not be jointly Gaussian. Squares replace DGo's rectangles; condition (I) is stated with the
side length `b` in place of `diam R = √2 b` (weaker hypothesis).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real

namespace LQGMetric
namespace DGo

open SupTail DZZ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **One box** (DGo (3.6)–(3.7), DGo:574–582): `P(sup_Q X ≥ C_F √(L b) + u) ≤ e^{−u²/(2σ²)}`. -/
theorem box_sup_tail {X : ℂ → Ω → ℝ} (hX : IsGaussianProcess X P)
    (h0 : ∀ v, ∫ ω, X v ω ∂P = 0) {y : ℂ} {b L σ : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hc : ∀ ω, ContinuousOn (fun v => X v ω) (ferniqueBox y b))
    (hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b,
      ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ L * ‖u - v‖)
    (hvar : ∀ v ∈ ferniqueBox y b, Var[X v; P] ≤ σ ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | ferniqueCF * Real.sqrt (L * b) + u ≤ ⨆ v : ferniqueBox y b, X v ω} ≤
      Real.exp (-u ^ 2 / (2 * σ ^ 2)) := by
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
  have hincG : ∀ u ∈ B, ∀ v ∈ B, ∫ ω, (c * X v ω - c * X u ω) ^ 2 ∂P ≤ ‖u - v‖ / b := by
    intro u hu v hv
    have e : (fun ω => (c * X v ω - c * X u ω) ^ 2) = fun ω => c ^ 2 * (X v ω - X u ω) ^ 2 := by
      funext ω; rw [← mul_sub, mul_pow]
    rw [e, integral_const_mul]
    calc c ^ 2 * ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ c ^ 2 * (L * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left (hinc u hu v hv) (sq_nonneg c)
      _ = ‖u - v‖ / b := by rw [← mul_assoc, hc2]; ring
  obtain ⟨h1, h2⟩ := dzz_lemma23_continuous (G := fun v ω => c * X v ω) hb
    ((hXB.smul fun _ => c).congr fun v => Eventually.of_forall fun ω => rfl)
    (fun v _ => by rw [integral_const_mul, h0, mul_zero]) hincG
    (fun ω => continuousOn_const.mul (hc ω))
  have hsup_eq : ∀ ω, (⨆ v : B, X v ω) = c⁻¹ * ⨆ v : B, c * X v ω := by
    intro ω
    rw [Real.mul_iSup_of_nonneg (inv_nonneg.2 hc0.le)]
    congr 1; funext v; field_simp
  have hint : Integrable (fun ω => ⨆ v : B, XB v ω) P := by
    simp_rw [XB, hsup_eq]; exact h1.const_mul _
  have hM : ∫ ω, (⨆ v : B, XB v ω) ∂P ≤ ferniqueCF * Real.sqrt (L * b) := by
    simp_rw [XB, hsup_eq]
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hc0.le)).trans ?_
    rw [hc_def, inv_inv, mul_comm]
  exact tail_iSup_le hXB (fun v => h0 v)
    (fun ω => continuousOn_iff_continuous_domRestrict.1 (hc ω)) hint hM
    (fun v => hvar v v.2) hu

/-- The elementary step of the union bound: with `a = √(2C' log N)`,
`N e^{−(a+x)²/(2C')} ≤ e^{−x²/(2C')}`. -/
lemma card_mul_exp_le {N : ℕ} (hN : 1 ≤ N) {C' x : ℝ} (hC' : 0 < C') (hx : 0 ≤ x) :
    (N : ℝ) * Real.exp (-(Real.sqrt (2 * C' * Real.log N) + x) ^ 2 / (2 * C')) ≤
      Real.exp (-x ^ 2 / (2 * C')) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN'
  set a := Real.sqrt (2 * C' * Real.log N)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * C' * Real.log N := Real.sq_sqrt (by positivity)
  have hNpos : (0 : ℝ) < N := by linarith
  have key : -(a + x) ^ 2 / (2 * C') ≤ -Real.log N + -x ^ 2 / (2 * C') := by
    have e : -Real.log N + -x ^ 2 / (2 * C') = -(a ^ 2 + x ^ 2) / (2 * C') := by
      rw [ha2]; field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg ha hx]
  calc (N : ℝ) * Real.exp (-(a + x) ^ 2 / (2 * C'))
      ≤ N * Real.exp (-Real.log N + -x ^ 2 / (2 * C')) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 key) hNpos.le
    _ = Real.exp (-x ^ 2 / (2 * C')) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hNpos]; field_simp

/-- **DGo Lemma 3.4** (`lem:gaussian_tail`, DGo:557–570) for a finite family of squares
`R_i = ferniqueBox (y i) (b i)`: if each `Y_i` is a centred Gaussian field, continuous on `R_i`,
with (I) `Var(Y_i(v) − Y_i(w)) ≤ C |v − w| / b_i` and (II) `Var Y_i(v) ≤ C'` on `R_i`, then
`P(max_i max_{R_i} Y_i ≥ √(2C' log |ι|) + C_F √C + x) ≤ e^{−x²/(2C')}` for `x ≥ 0`
(`C'' = C_F √C` depends only on `C`). -/
theorem dgo_lemma34 {ι : Type*} [Fintype ι] [Nonempty ι] [IsFiniteMeasure P]
    {Y : ι → ℂ → Ω → ℝ} (hY : ∀ i, IsGaussianProcess (Y i) P)
    (h0 : ∀ i v, ∫ ω, Y i v ω ∂P = 0) {y : ι → ℂ} {b : ι → ℝ} (hb : ∀ i, 0 < b i)
    {C C' : ℝ} (hC : 0 < C) (hC' : 0 < C')
    (hc : ∀ i ω, ContinuousOn (fun v => Y i v ω) (ferniqueBox (y i) (b i)))
    (hinc : ∀ i, ∀ u ∈ ferniqueBox (y i) (b i), ∀ v ∈ ferniqueBox (y i) (b i),
      ∫ ω, (Y i v ω - Y i u ω) ^ 2 ∂P ≤ C * ‖u - v‖ / b i)
    (hvar : ∀ i, ∀ v ∈ ferniqueBox (y i) (b i), Var[Y i v; P] ≤ C') {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | Real.sqrt (2 * C' * Real.log (Fintype.card ι)) + ferniqueCF * Real.sqrt C + x ≤
      ⨆ i, ⨆ v : ferniqueBox (y i) (b i), Y i v ω} ≤ Real.exp (-x ^ 2 / (2 * C')) := by
  set a := Real.sqrt (2 * C' * Real.log (Fintype.card ι))
  set S : ι → Ω → ℝ := fun i ω => ⨆ v : ferniqueBox (y i) (b i), Y i v ω
  have hsub : {ω | a + ferniqueCF * Real.sqrt C + x ≤ ⨆ i, S i ω} ⊆
      ⋃ i, {ω | ferniqueCF * Real.sqrt (C / b i * b i) + (a + x) ≤ S i ω} := by
    intro ω hω
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => S i ω)
    refine mem_iUnion.2 ⟨i, ?_⟩
    simp only [mem_ofPred_eq] at hω ⊢
    rw [div_mul_cancel₀ C (hb i).ne', hi]
    linarith
  have hσ : Real.sqrt C' ^ 2 = C' := Real.sq_sqrt hC'.le
  have hbox : ∀ i, P.real {ω | ferniqueCF * Real.sqrt (C / b i * b i) + (a + x) ≤ S i ω} ≤
      Real.exp (-(a + x) ^ 2 / (2 * C')) := by
    intro i
    have h := box_sup_tail (hY i) (h0 i) (hb i) (div_pos hC (hb i)) (hc i)
      (fun u hu v hv => (hinc i u hu v hv).trans_eq (by ring))
      (fun v hv => (hvar i v hv).trans_eq hσ.symm) (u := a + x) (by positivity)
    rwa [hσ] at h
  have hN : 1 ≤ Fintype.card ι := Fintype.card_pos
  calc P.real {ω | a + ferniqueCF * Real.sqrt C + x ≤ ⨆ i, S i ω}
      ≤ ∑ i, P.real {ω | ferniqueCF * Real.sqrt (C / b i * b i) + (a + x) ≤ S i ω} :=
        (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)
    _ ≤ ∑ _i : ι, Real.exp (-(a + x) ^ 2 / (2 * C')) := Finset.sum_le_sum fun i _ => hbox i
    _ = (Fintype.card ι : ℝ) * Real.exp (-(a + x) ^ 2 / (2 * C')) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Real.exp (-x ^ 2 / (2 * C')) := card_mul_exp_le hN hC' hx

end DGo
end LQGMetric
