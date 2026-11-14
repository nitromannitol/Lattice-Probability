/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RRegular at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RGauss

 












set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 
def laneA4RBad {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams) (ξ Qe ζ : ℝ) (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ) : Fin 4 → Set Ω
  | 0 => {ω | (2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ)) *
        (2 : ℝ) ^ (-(1 - ξ * Qe - ζ) * (K : ℝ)) * lambdaN ξ W P (n - K) <
      lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω}
  | 1 => {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω <
      ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ)))⁻¹ *
        (2 : ℝ) ^ (-(1 - ξ * Qe + ζ) * (K : ℝ)) * lambdaN ξ W P (n - K)}
  | 2 => {ω | ∃ b ∈ laneSourceIdx Q K, ω ∈ j1RoundCutLowerEvent ξ Q W P K n
      (laneBCoarseIndex Q K) ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ))) (lambdaN ξ W P (n - K)) b}
  | 3 => {ω | ∃ b ∈ laneSourceIdx Q K, ω ∈ j1RoundCutUpperEvent ξ Q W P hW K n
      (laneBCoarseIndex Q K) ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ))) (lambdaN ξ W P (n - K)) b}

 
def laneA4RGood {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams) (ξ Qe ζ : ℝ) (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ) : Set Ω :=
  (⋃ i : Fin 4, toMeasurable P (laneA4RBad Q ξ Qe ζ P W hW n K i))ᶜ

theorem laneA4RGood_measurableSet {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams)
    (ξ Qe ζ : ℝ) (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ) :
    MeasurableSet (laneA4RGood Q ξ Qe ζ P W hW n K) :=
  (MeasurableSet.iUnion fun _ => measurableSet_toMeasurable _ _).compl

theorem laneA4RGood_subset {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams)
    (ξ Qe ζ : ℝ) (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ) :
    laneA4RGood Q ξ Qe ζ P W hW n K ⊆ laneA4Regular Q ξ Qe ζ P W hW n K := by
  intro ω hω
  simp only [laneA4RGood, mem_compl_iff, mem_iUnion, not_exists] at hω
  have h : ∀ i : Fin 4, ω ∉ laneA4RBad Q ξ Qe ζ P W hW n K i := fun i hi =>
    hω i (subset_toMeasurable _ _ hi)
  refine ⟨not_lt.mp (h 0), not_lt.mp (h 1), fun b hb => ⟨fun h2 => h 2 ⟨b, hb, h2⟩,
    fun h3 => h 3 ⟨b, hb, h3⟩⟩⟩

theorem laneA4RGood_compl_le {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams)
    (ξ Qe ζ : ℝ) (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ) :
    P (laneA4RGood Q ξ Qe ζ P W hW n K)ᶜ ≤ ∑ i : Fin 4, P (laneA4RBad Q ξ Qe ζ P W hW n K i) := by
  rw [laneA4RGood, compl_compl]
  calc P (⋃ i : Fin 4, toMeasurable P (laneA4RBad Q ξ Qe ζ P W hW n K i))
      ≤ ∑ i : Fin 4, P (toMeasurable P (laneA4RBad Q ξ Qe ζ P W hW n K i)) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ i : Fin 4, P (laneA4RBad Q ξ Qe ζ P W hW n K i) := by
        simp only [measure_toMeasurable]

 
theorem laneA4R_weight_le_of_regular {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ Qe ζ : ℝ)
    (γ : ℕ → ℕ → Ω → ℝ → ℂ) (n K : ℕ) (b : ℤ × ℤ) (hb : b ∈ laneSourceIdx Q K) (ω : Ω)
    (hE : ω ∈ laneA4Regular Q ξ Qe ζ P W hW n K) :
    laneA3HitWeight P W hW Q ξ γ n K b ω ≤
      ENNReal.ofReal (((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ))) ^ 2 * (2 : ℝ) ^ ((ζ - ξ * Qe) * K)) *
        ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) := by
  obtain ⟨-, h2, h34⟩ := hE
  have hup := (h34 b hb).2
  set τ := (2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ)) with hτ
  have hτpos : 0 < τ := by positivity
  set lam := lambdaN ξ W P (n - K)
  have hlam : 0 < lam := lambdaN_pos hW (n - K)
  set φ := phiMN W P 0 K (T20.dyCenter K b) ω
  set Lr := lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω
  set A := laneA3Around P W hW Q ξ n K b ω
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hLfin : rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) (hψ.cont ω)
  have hLr : rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) = ENNReal.ofReal Lr :=
    (ENNReal.ofReal_toReal hLfin).symm
  set lo := τ⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Qe + ζ) * (K : ℝ)) * lam
  have hlo : 0 < lo := by positivity
  have hloL : lo ≤ Lr := h2
  
  have hA : A ≤ ENNReal.ofReal (τ * ((2 : ℝ)⁻¹ ^ K * lam) * Real.exp (ξ * φ)) := by
    have h : ENNReal.ofReal (Real.exp (-ξ * φ)) * A ≤
        ENNReal.ofReal (τ * ((2 : ℝ)⁻¹ ^ K * lam)) := not_lt.mp hup
    have he : ENNReal.ofReal (Real.exp (ξ * φ)) * ENNReal.ofReal (Real.exp (-ξ * φ)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp
    calc A = (ENNReal.ofReal (Real.exp (ξ * φ)) * ENNReal.ofReal (Real.exp (-ξ * φ))) * A := by
          rw [he, one_mul]
      _ = ENNReal.ofReal (Real.exp (ξ * φ)) * (ENNReal.ofReal (Real.exp (-ξ * φ)) * A) := by ring
      _ ≤ ENNReal.ofReal (Real.exp (ξ * φ)) * ENNReal.ofReal (τ * ((2 : ℝ)⁻¹ ^ K * lam)) :=
          mul_le_mul' le_rfl h
      _ = ENNReal.ofReal (τ * ((2 : ℝ)⁻¹ ^ K * lam) * Real.exp (ξ * φ)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  have hkey : τ * ((2 : ℝ)⁻¹ ^ K * lam) * Real.exp (ξ * φ) / lo =
      τ ^ 2 * (2 : ℝ) ^ ((ζ - ξ * Qe) * K) * Real.exp (ξ * φ) := by
    have h2K : (2 : ℝ)⁻¹ ^ K = (2 : ℝ) ^ (-(K : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
    have hsplit : (2 : ℝ) ^ ((ζ - ξ * Qe) * K) =
        (2 : ℝ) ^ (-(K : ℝ)) / (2 : ℝ) ^ (-(1 - ξ * Qe + ζ) * (K : ℝ)) := by
      rw [← Real.rpow_sub (by norm_num)]; congr 1; ring
    rw [h2K, hsplit]
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(1 - ξ * Qe + ζ) * (K : ℝ)) := by positivity
    simp only [lo]
    field_simp
  calc laneA3HitWeight P W hW Q ξ γ n K b ω
      ≤ A / rectLen ξ (fun z => psiMN Q W P 0 n z ω) (rectAB 1 1) := by
        unfold laneA3HitWeight
        by_cases hF : ω ∈ laneCEventualHit γ n K (laneBCoarseIndex Q K) b
        · rw [indicator_of_mem hF]
        · rw [indicator_of_notMem hF]; exact bot_le
    _ ≤ ENNReal.ofReal (τ * ((2 : ℝ)⁻¹ ^ K * lam) * Real.exp (ξ * φ)) / ENNReal.ofReal lo := by
        rw [hLr]
        exact ENNReal.div_le_div hA (ENNReal.ofReal_le_ofReal hloL)
    _ = ENNReal.ofReal (τ ^ 2 * (2 : ℝ) ^ ((ζ - ξ * Qe) * K) * Real.exp (ξ * φ)) := by
        rw [← ENNReal.ofReal_div_of_pos hlo, hkey]
    _ = ENNReal.ofReal (τ ^ 2 * (2 : ℝ) ^ ((ζ - ξ * Qe) * K)) *
          ENNReal.ofReal (Real.exp (ξ * φ)) := ENNReal.ofReal_mul (by positivity)

 
theorem laneA4R_hitProfile_lipschitz {ξ Q β : ℝ} (hξ : 0 < ξ) (hβ : Q ≤ β) :
    (ξ * min ξ β - (min ξ β) ^ 2 / 2) - (ξ * min ξ Q - (min ξ Q) ^ 2 / 2) ≤
      (ξ + |Q|) * (β - Q) := by
  set y₁ := min ξ Q
  set y₂ := min ξ β
  have hy : y₁ ≤ y₂ := min_le_min_left ξ hβ
  have hy2 : y₂ - y₁ ≤ β - Q := by
    rcases le_total ξ Q with h | h
    · have e1 : y₁ = ξ := min_eq_left h
      have e2 : y₂ = ξ := min_eq_left (h.trans hβ)
      rw [e1, e2]; linarith
    · have e1 : y₁ = Q := min_eq_right h
      rw [e1]; linarith [min_le_right ξ β]
  have hy1 : -|Q| ≤ y₁ := by
    rcases le_total ξ Q with h | h
    · have : y₁ = ξ := min_eq_left h
      rw [this]; linarith [abs_nonneg Q]
    · have : y₁ = Q := min_eq_right h
      rw [this]; exact neg_abs_le Q
  have e : (ξ * y₂ - y₂ ^ 2 / 2) - (ξ * y₁ - y₁ ^ 2 / 2) = (y₂ - y₁) * (ξ - (y₁ + y₂) / 2) := by
    ring
  rw [e]
  have h0 : 0 ≤ y₂ - y₁ := by linarith
  calc (y₂ - y₁) * (ξ - (y₁ + y₂) / 2) ≤ (y₂ - y₁) * (ξ + |Q|) :=
        mul_le_mul_of_nonneg_left (by linarith) h0
    _ ≤ (β - Q) * (ξ + |Q|) := mul_le_mul_of_nonneg_right hy2 (by positivity)
    _ = (ξ + |Q|) * (β - Q) := by ring

 
theorem laneA4R_superexp_rate {c c' ε M : ℝ} (hc : 0 < c) (hc' : 0 < c') (hε0 : 0 < ε)
    (hε : ε < 1 / 100) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      c * (5 : ℝ) ^ K * Real.exp (-(c' * (Real.log ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ)))) ^ 2 /
        ((K : ℝ) ^ (3 * ε) * Real.log (Real.log ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ))))))) ≤
      (2 : ℝ) ^ (-(M * K)) ∧
      c * (5 : ℝ) ^ K * Real.exp (-c' * (Real.log ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ)))) ^ 2 /
        (K : ℝ) ^ (3 * ε)) ≤ (2 : ℝ) ^ (-(M * K)) := by
  set a := Real.log 2 with ha
  have ha0 : 0 < a := Real.log_pos (by norm_num)
  have ha1 : a < 1 := by
    rw [ha, Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
  obtain ⟨K₁, hK₁⟩ := laneA3R_eventually_log_le ((|Real.log c| + 2 + |M|) / (c' * a ^ 2))
    (1 / 3 - 3 * ε) (by linarith)
  obtain ⟨K₂, hK₂⟩ := laneA3R_eventually_log_le (3 / a) (2 / 3) (by norm_num)
  refine ⟨max 2 (max K₁ K₂), fun K hK => ?_⟩
  have hK2 : 2 ≤ K := (le_max_left _ _).trans hK
  have hK1' : K₁ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hK2' : K₂ ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hK0 : (0 : ℝ) < K := by linarith
  set L := Real.log K
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set x₀ := (K : ℝ) ^ (2 / 3 : ℝ)
  have hx₀pos : 0 < x₀ := Real.rpow_pos_of_pos hK0 _
  set ℓ := Real.log ((2 : ℝ) ^ x₀) with hℓ
  have hℓeq : ℓ = x₀ * a := by rw [hℓ, Real.log_rpow (by norm_num)]
  
  have hℓ3 : 3 ≤ ℓ := by
    have h := hK₂ K hK2'
    rw [hℓeq]
    have : 3 / a * (L + 1) ≥ 3 / a := le_mul_of_one_le_right (by positivity) (by linarith)
    have hx : 3 / a ≤ x₀ := le_trans this h
    rw [div_le_iff₀ ha0] at hx
    linarith
  have hlogℓ1 : 1 ≤ Real.log ℓ := by
    have := laneA3R_one_lt_log_three.le
    exact this.trans (Real.log_le_log (by norm_num) hℓ3)
  have hlogℓK : Real.log ℓ ≤ L := by
    apply Real.log_le_log (by linarith)
    rw [hℓeq]
    have hx₀K : x₀ ≤ K := by
      calc x₀ ≤ (K : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = K := Real.rpow_one _
    nlinarith
  set e₃ := (K : ℝ) ^ (3 * ε)
  have he₃ : 0 < e₃ := Real.rpow_pos_of_pos hK0 _
  
  have hℓsq : ℓ ^ 2 = K * (K : ℝ) ^ (1 / 3 - 3 * ε) * e₃ * a ^ 2 := by
    rw [hℓeq]
    have e1 : x₀ ^ 2 = (K : ℝ) ^ ((4 : ℝ) / 3) := by
      simp only [x₀]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
      norm_num
    have e2 : (K : ℝ) * (K : ℝ) ^ (1 / 3 - 3 * ε) * e₃ = (K : ℝ) ^ ((4 : ℝ) / 3) := by
      simp only [e₃]
      rw [mul_assoc, ← Real.rpow_add hK0, show (1 / 3 - 3 * ε + 3 * ε : ℝ) = 1 / 3 by ring,
        mul_comm, ← Real.rpow_add_one hK0.ne']
      norm_num
    rw [mul_pow, e1, ← e2]
  have hD : Real.log c + K * Real.log 5 + M * K * a ≤ (|Real.log c| + 2 + |M|) * K := by
    have h5 := laneA3R_log_five_lt_two
    have h1 : Real.log c ≤ |Real.log c| * K := by
      have := le_abs_self (Real.log c)
      nlinarith [abs_nonneg (Real.log c)]
    have h3 : M * K * a ≤ |M| * K := by
      have : M * a ≤ |M| := by
        calc M * a ≤ |M| * a := mul_le_mul_of_nonneg_right (le_abs_self M) ha0.le
          _ ≤ |M| := by nlinarith [abs_nonneg M]
      nlinarith
    nlinarith
  have hmain : Real.log c + K * Real.log 5 + M * K * a ≤ c' * ℓ ^ 2 / (e₃ * Real.log ℓ) := by
    rw [le_div_iff₀ (by positivity)]
    have h := hK₁ K hK1'
    have hk : (|Real.log c| + 2 + |M|) * (L + 1) ≤ c' * a ^ 2 * (K : ℝ) ^ (1 / 3 - 3 * ε) := by
      have : (|Real.log c| + 2 + |M|) / (c' * a ^ 2) * (L + 1) * (c' * a ^ 2) =
          (|Real.log c| + 2 + |M|) * (L + 1) := by field_simp
      nlinarith [mul_pos hc' (pow_pos ha0 2)]
    rw [hℓsq]
    have hpos : 0 ≤ (|Real.log c| + 2 + |M|) := by positivity
    calc (Real.log c + K * Real.log 5 + M * K * a) * (e₃ * Real.log ℓ)
        ≤ ((|Real.log c| + 2 + |M|) * K) * (e₃ * (L + 1)) := by
          rcases le_or_gt (Real.log c + K * Real.log 5 + M * K * a) 0 with hneg | hpos'
          · have : (Real.log c + K * Real.log 5 + M * K * a) * (e₃ * Real.log ℓ) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
            linarith [show 0 ≤ ((|Real.log c| + 2 + |M|) * K) * (e₃ * (L + 1)) by positivity]
          · exact mul_le_mul hD (mul_le_mul_of_nonneg_left (by linarith) he₃.le)
              (by positivity) (by positivity)
      _ = K * e₃ * ((|Real.log c| + 2 + |M|) * (L + 1)) := by ring
      _ ≤ K * e₃ * (c' * a ^ 2 * (K : ℝ) ^ (1 / 3 - 3 * ε)) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = c' * (K * (K : ℝ) ^ (1 / 3 - 3 * ε) * e₃ * a ^ 2) := by ring
  have h5 : (5 : ℝ) ^ K = Real.exp (K * Real.log 5) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have h2M : (2 : ℝ) ^ (-(M * K)) = Real.exp (-(M * K * a)) := by
    rw [Real.rpow_def_of_pos (by norm_num), ha]; ring_nf
  have hfirst : c * (5 : ℝ) ^ K * Real.exp (-(c' * ℓ ^ 2 / (e₃ * Real.log ℓ))) ≤
      (2 : ℝ) ^ (-(M * K)) := by
    rw [h5, h2M, ← Real.exp_log hc, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  refine ⟨hfirst, le_trans ?_ hfirst⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ c' * ℓ ^ 2 / e₃ := by positivity
  have h1 : c' * ℓ ^ 2 / e₃ / Real.log ℓ ≤ c' * ℓ ^ 2 / e₃ := div_le_self hq hlogℓ1
  have e1 : c' * ℓ ^ 2 / (e₃ * Real.log ℓ) = c' * ℓ ^ 2 / e₃ / Real.log ℓ := by rw [div_div]
  rw [e1, show -c' * ℓ ^ 2 / e₃ = -(c' * ℓ ^ 2 / e₃) by ring]
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
