/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldReparam at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldNormalizedBefore
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem coarse_exp_le_scale (ξ S : ℝ) (hξ : 0 < ξ) (hS : 1 ≤ S) :
    Real.exp (|ξ| * (Real.log S / (2 * ξ))) ≤ S := by
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hlog : 0 ≤ Real.log S := Real.log_nonneg hS
  rw [abs_of_pos hξ]
  have heq : ξ * (Real.log S / (2 * ξ)) = Real.log S / 2 := by
    field_simp
  rw [heq]
  calc
    Real.exp (Real.log S / 2) ≤ Real.exp (Real.log S) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = S := Real.exp_log hS0

 



theorem perc_field_tail_event_sqrt
    (ξ : ℝ) (hξ : 0 < ξ) (T : ℝ) (hT : 9 < T)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {Ω : Type} (D : Ω → ℝ≥0∞) (φ : Ω → ℝ) :
    let S := Real.sqrt T
    let E := ENNReal.ofReal (Real.exp (|ξ| * (Real.log S / (2 * ξ))))
    {ω | D ω < ENNReal.ofReal (Real.exp (ξ * φ ω)) *
        ENNReal.ofReal (T⁻¹ * a)} ⊆
      {ω | E * D ω < ENNReal.ofReal (Real.exp (ξ * φ ω)) *
        ENNReal.ofReal (S⁻¹ * a)} ∧
    {ω | ENNReal.ofReal (Real.exp (ξ * φ ω)) *
        ENNReal.ofReal (T * b) < D ω} ⊆
      {ω | E * (ENNReal.ofReal (Real.exp (ξ * φ ω)) *
        ENNReal.ofReal (S * b)) < D ω} := by
  dsimp
  let S : ℝ := Real.sqrt T
  let e : ℝ := Real.exp (|ξ| * (Real.log S / (2 * ξ)))
  have hS : 3 < S := by
    dsimp [S]
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have hS0 : 0 < S := by linarith
  have hS2 : S ^ 2 = T := by
    dsimp [S]
    exact Real.sq_sqrt (by linarith)
  have he0 : 0 < e := Real.exp_pos _
  have heS : e ≤ S := coarse_exp_le_scale ξ S hξ (by linarith)
  have hE0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.mpr he0).ne'
  have hEtop : ENNReal.ofReal e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlow : ENNReal.ofReal e * ENNReal.ofReal (T⁻¹ * a) ≤
      ENNReal.ofReal (S⁻¹ * a) := by
    rw [← ENNReal.ofReal_mul he0.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      e * (T⁻¹ * a) ≤ S * (T⁻¹ * a) :=
        mul_le_mul_of_nonneg_right heS (by positivity)
      _ = S⁻¹ * a := by
        rw [← hS2]
        field_simp
  have hupp : ENNReal.ofReal e * ENNReal.ofReal (S * b) ≤
      ENNReal.ofReal (T * b) := by
    rw [← ENNReal.ofReal_mul he0.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      e * (S * b) ≤ S * (S * b) :=
        mul_le_mul_of_nonneg_right heS (by positivity)
      _ = T * b := by rw [← hS2]; ring
  constructor
  · intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    calc
      ENNReal.ofReal e * D ω <
          ENNReal.ofReal e *
            (ENNReal.ofReal (Real.exp (ξ * φ ω)) *
              ENNReal.ofReal (T⁻¹ * a)) := by
        rw [mul_comm (ENNReal.ofReal e) (D ω),
          mul_comm (ENNReal.ofReal e)
            (ENNReal.ofReal (Real.exp (ξ * φ ω)) *
              ENNReal.ofReal (T⁻¹ * a))]
        exact ENNReal.mul_lt_mul_left hE0 hEtop hω
      _ = ENNReal.ofReal (Real.exp (ξ * φ ω)) *
          (ENNReal.ofReal e * ENNReal.ofReal (T⁻¹ * a)) := by ac_rfl
      _ ≤ ENNReal.ofReal (Real.exp (ξ * φ ω)) *
          ENNReal.ofReal (S⁻¹ * a) := by gcongr
  · intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    calc
      ENNReal.ofReal e *
          (ENNReal.ofReal (Real.exp (ξ * φ ω)) *
            ENNReal.ofReal (S * b)) =
          ENNReal.ofReal (Real.exp (ξ * φ ω)) *
            (ENNReal.ofReal e * ENNReal.ofReal (S * b)) := by ac_rfl
      _ ≤ ENNReal.ofReal (Real.exp (ξ * φ ω)) *
          ENNReal.ofReal (T * b) := by gcongr
      _ < D ω := hω

 



theorem perc_field_bounded_sqrt_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Opens ℂ) (hU : Bornology.IsBounded (U : Set ℂ))
    (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hconn₁ : IsConnected K₁) (hconn₂ : IsConnected K₂)
    (hnt₁ : K₁.Nontrivial) (hnt₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (hsub₂ : K₂ ⊆ U)
    (hdisj : Disjoint K₁ K₂) (hconnU : IsConnected (U : Set ℂ)) :
    ∃ C c₀ c₁ d₀ d₁ : ℝ,
      0 < C ∧ 0 < c₀ ∧ 0 < c₁ ∧ 0 < d₀ ∧ 0 < d₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 9 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        let S : ℝ := Real.sqrt T
        P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ * (C⁻¹ *
              (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) *
                lambdaN ξ W P n))} ≤
          ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log S) ^ 2)) +
            ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log S) ^ 2)) ∧
        P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T * (C *
              (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
                lambdaN ξ W P n)) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂)} ≤
          ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log S) ^ 2)) +
            ENNReal.ofReal (c₀ * Real.exp
              (-c₁ * (Real.log S) ^ 2 / Real.log (Real.log S))) := by
  obtain ⟨C, c₀, c₁, d₀, d₁, hC, hc₀, hc₁, hd₀, hd₁, hbefore⟩ :=
    perc_field_normalized_before_of_inputs hPerc hExp ξ Q hQ ζ hζ U hU
      K₁ K₂ hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  refine ⟨C, c₀, c₁, d₀, d₁, hC, hc₀, hc₁, hd₀, hd₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  let S : ℝ := Real.sqrt T
  have hS : 3 < S := by
    dsimp [S]
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  obtain ⟨hlo, hhi⟩ := hbefore P W hW n k hkn S hS
  let a : ℝ := C⁻¹ * (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) *
    lambdaN ξ W P n
  let b : ℝ := C * (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
    lambdaN ξ W P n
  have hlam : 0 < lambdaN ξ W P n := lambdaN_pos hW n
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let D : Ω → ℝ≥0∞ := fun ω =>
    crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
      ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * z) '' U)
      ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * z) '' K₁)
      ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * z) '' K₂)
  let φ : Ω → ℝ := fun ω => phiMN W P 0 k 0 ω
  have hevents := perc_field_tail_event_sqrt (ξ : ℝ) ξ.property T hT a b ha hb D φ
  dsimp at hlo hhi ⊢
  constructor
  · exact (measure_mono (by simpa only [D, φ, a, S] using hevents.1)).trans hlo
  · exact (measure_mono (by simpa only [D, φ, b, S] using hevents.2)).trans hhi

end SupercriticalLQGUniqueness.B2.DG20Pt
