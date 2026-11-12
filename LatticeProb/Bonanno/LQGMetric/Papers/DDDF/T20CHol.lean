/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20CHol at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs

/-!
# DDDF Theorem 20, Step 4: the Hölder step (task P2-DDDFT20c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1156–1172: "by applying Hölder inequality and
Cauchy–Schwarz". With `1/α + 1/β = 1` (`α` from Condition (T)) we use Hölder for four factors
with exponents `α, 3β, 3β, 3β`:

  `E[R · e^{C₀X} · e^{C₀K^{ε₀}O} · S²]
     ≤ E[R^α]^{1/α} E[e^{3βC₀X}]^{1/(3β)} E[e^{3βC₀K^{ε₀}O}]^{1/(3β)} E[S^{6β}]^{1/(3β)}`

(`T20C.holder_step`), `R` the Condition (T) ratio, `S` the long/short crossing ratio.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20C

lemma aemeasurable_sup'_fun {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, AEMeasurable (f i) P) : AEMeasurable (fun ω => s.sup' hs fun i => f i ω) P := by
  have e : (fun ω => s.sup' hs fun i => f i ω) = s.sup' hs f := by
    funext ω; rw [Finset.sup'_apply]
  rw [e]
  exact Finset.sup'_induction (p := fun F : Ω → ℝ => AEMeasurable F P) hs f
    (fun _ h1 _ h2 => AEMeasurable.sup h1 h2) hf

lemma measurable_inf'_fun {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable (fun ω => s.inf' hs fun i => f i ω) := by
  have e : (fun ω => s.inf' hs fun i => f i ω) = s.inf' hs f := by
    funext ω; rw [Finset.inf'_apply]
  rw [e]
  exact Finset.inf'_induction (p := fun F : Ω → ℝ => Measurable F) hs f
    (fun _ h1 _ h2 => Measurable.inf h1 h2) hf

lemma condTRatio_nonneg (ξ : ℝ) (K : ℕ) (f : ℂ → ℝ) (γ : ℝ → ℂ) :
    0 ≤ T20.condTRatio ξ K f γ := by
  unfold T20.condTRatio; positivity

lemma lsRatio_nonneg (ξ : ℝ) (K n : ℕ) (J J' : Finset (Circle × ℂ)) (hJ : J.Nonempty)
    (hJ' : J'.Nonempty) (ω : Ω) : 0 ≤ lsRatio ξ W P K n J J' hJ hJ' ω := by
  set g : Circle × ℂ → ℝ := fun j => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1
  set g' : Circle × ℂ → ℝ := fun j => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 1 3
  have h1 : 0 ≤ J.sup' hJ g := by
    obtain ⟨j, hj⟩ := hJ
    exact (ENNReal.toReal_nonneg).trans (Finset.le_sup' g hj)
  have h2 : 0 ≤ J'.inf' hJ' g' := Finset.le_inf' hJ' g' fun j _ => ENNReal.toReal_nonneg
  exact div_nonneg h1 h2

lemma measurable_lsRatio (hW : IsWhiteNoise P W) (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n)
    (J J' : Finset (Circle × ℂ)) (hJ : J.Nonempty) (hJ' : J'.Nonempty) :
    Measurable (lsRatio ξ W P K n J J' hJ hJ') := by
  have h1 : Measurable fun ω => J.sup' hJ fun j =>
      T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1 := by
    have e : (fun ω => J.sup' hJ fun j =>
        T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1) =
        J.sup' hJ fun j ω => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1 := by
      funext ω; rw [Finset.sup'_apply]
    rw [e]
    exact Finset.measurable_sup' hJ fun j _ => T20B.measurable_mrectLen hW hKn _ _ _ _
  have h2 := measurable_inf'_fun hJ' (f := fun j ω =>
    T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 1 3)
    fun j _ => T20B.measurable_mrectLen hW hKn _ _ _ _
  exact h1.div h2

lemma measurable_condTRatio (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ η : ℝ}
    {γ : ℕ → Ω → ℝ → ℂ} (hγ : T20.IsNearGeodSel ξ Q W P η γ) (K n : ℕ) :
    Measurable fun ω => T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) (γ n ω) := by
  classical
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have hs : ∀ g : ℤ × ℤ → Ω → ℝ, (∀ b, Measurable (g b)) →
      Measurable fun ω => ∑ b ∈ T20.coarseBlocks K (γ n ω), g b ω := by
    intro g hg
    have e : (fun ω => ∑ b ∈ T20.coarseBlocks K (γ n ω), g b ω) = fun ω =>
        ∑ b ∈ T20.blkIdx K, if b ∈ T20.coarseBlocks K (γ n ω) then g b ω else 0 := by
      funext ω
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (by unfold T20.coarseBlocks; exact Finset.filter_subset _ _)]
    rw [e]
    exact Finset.measurable_sum _ fun b _ => Measurable.ite (hγ.meas n K b) (hg b) measurable_const
  unfold T20.condTRatio
  exact (hs _ fun b => ((hψ.meas _).const_mul _).exp).div
    ((hs _ fun b => ((hψ.meas _).const_mul _).exp).pow_const 2)

/-- `x^t ≤ x + 1` for `t ∈ [0,1]` -/
lemma rpow_le_add_one {x t : ℝ} (hx : 0 ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : x ^ t ≤ x + 1 := by
  rcases le_total x 1 with h | h
  · linarith [Real.rpow_le_one hx h ht0]
  · have := Real.rpow_le_rpow_of_exponent_le h ht1
    rw [Real.rpow_one] at this; linarith

/-- **Hölder step** of DDDF l. 1156–1172 -/
theorem holder_step {α β : ℝ} (hα : 1 < α) (hβ : β = α / (α - 1)) {R X O S : Ω → ℝ}
    (hR0 : ∀ ω, 0 ≤ R ω) (hS0 : ∀ ω, 0 ≤ S ω)
    (hRm : AEMeasurable R P) (hXm : AEMeasurable X P) (hOm : AEMeasurable O P)
    (hSm : AEMeasurable S P) {C₀ : ℝ} :
    ∫⁻ ω, ENNReal.ofReal (R ω * Real.exp (C₀ * X ω) * Real.exp (O ω) * S ω ^ 2) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal (R ω ^ α) ∂P) ^ (1 / α) *
      (∫⁻ ω, ENNReal.ofReal (Real.exp (3 * β * C₀ * X ω)) ∂P) ^ (3 * β)⁻¹ *
      (∫⁻ ω, ENNReal.ofReal (Real.exp (3 * β * O ω)) ∂P) ^ (3 * β)⁻¹ *
      (∫⁻ ω, ENNReal.ofReal (S ω ^ (6 * β)) ∂P) ^ (3 * β)⁻¹ := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by rw [hβ]; exact div_pos hα0 (by linarith)
  have h3β : 0 < 3 * β := by positivity
  set f : Fin 4 → Ω → ℝ≥0∞ := ![fun ω => ENNReal.ofReal (R ω),
    fun ω => ENNReal.ofReal (Real.exp (C₀ * X ω)), fun ω => ENNReal.ofReal (Real.exp (O ω)),
    fun ω => ENNReal.ofReal (S ω ^ 2)] with hf
  set q : Fin 4 → ℝ := ![α, 3 * β, 3 * β, 3 * β] with hq
  have hfm : ∀ i, AEMeasurable (f i) P := by
    intro i; fin_cases i
    · exact hRm.ennreal_ofReal
    · exact ((hXm.const_mul C₀).exp).ennreal_ofReal
    · exact hOm.exp.ennreal_ofReal
    · exact (hSm.pow_const 2).ennreal_ofReal
  have hqp : ∀ i, 0 < q i := by
    intro i; fin_cases i <;> simp [q, hα0, h3β]
  have hsum : ∑ i, (q i)⁻¹ = 1 := by
    simp only [Fin.sum_univ_four, q, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hβ]; field_simp; ring
  have h := holder4 hfm hqp hsum
  simp only [Fin.prod_univ_four, f, q, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  have hl : ∀ ω, ENNReal.ofReal (R ω * Real.exp (C₀ * X ω) * Real.exp (O ω) * S ω ^ 2) =
      ENNReal.ofReal (R ω) * ENNReal.ofReal (Real.exp (C₀ * X ω)) *
        ENNReal.ofReal (Real.exp (O ω)) * ENNReal.ofReal (S ω ^ 2) := fun ω => by
    rw [ENNReal.ofReal_mul (by have := hR0 ω; positivity),
      ENNReal.ofReal_mul (by have := hR0 ω; positivity), ENNReal.ofReal_mul (hR0 ω)]
  simp_rw [hl]
  refine h.trans (le_of_eq ?_)
  have e1 : ∀ ω, ENNReal.ofReal (R ω) ^ α = ENNReal.ofReal (R ω ^ α) := fun ω =>
    ENNReal.ofReal_rpow_of_nonneg (hR0 ω) hα0.le
  have e2 : ∀ ω, ENNReal.ofReal (Real.exp (C₀ * X ω)) ^ (3 * β) =
      ENNReal.ofReal (Real.exp (3 * β * C₀ * X ω)) := fun ω => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h3β.le, ← Real.exp_mul]
    congr 2; ring
  have e3 : ∀ ω, ENNReal.ofReal (Real.exp (O ω)) ^ (3 * β) =
      ENNReal.ofReal (Real.exp (3 * β * O ω)) := fun ω => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h3β.le, ← Real.exp_mul]
    congr 2; ring
  have e4 : ∀ ω, ENNReal.ofReal (S ω ^ 2) ^ (3 * β) = ENNReal.ofReal (S ω ^ (6 * β)) :=
    fun ω => by
    rw [ENNReal.ofReal_rpow_of_nonneg (by have := hS0 ω; positivity) h3β.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hS0 ω)]
    congr 1; push_cast; ring
  simp_rw [e1, e2, e3, e4, one_div]

end T20C

end DDDF
end LQGMetric
