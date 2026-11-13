/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5OneStep
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5InductionEngine
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CircuitBase
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsDGFF

 






















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

 
def qbar : ℝ := 1 - (1 / 2 : ℝ) ^ 40

theorem qbar_half : (1 / 2 : ℝ) ≤ qbar := by unfold qbar; norm_num
theorem qbar_le_one : qbar ≤ 1 := by
  unfold qbar; have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 40 := by positivity
  linarith
theorem qbar_nonneg : 0 ≤ qbar := by unfold qbar; norm_num

 
theorem exp_level_le (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-c * (Real.sqrt (a * Real.log 2 / c) + 1) ^ 2) ≤ (1 / 2 : ℝ) ^ a := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := Real.sq_sqrt (show 0 ≤ a * Real.log 2 / c by positivity)
  have hs0 := Real.sqrt_nonneg (a * Real.log 2 / c)
  have hsq : a * Real.log 2 / c ≤ (Real.sqrt (a * Real.log 2 / c) + 1) ^ 2 := by nlinarith
  have hle : -c * (Real.sqrt (a * Real.log 2 / c) + 1) ^ 2 ≤ -(a * Real.log 2) := by
    have := mul_le_mul_of_nonneg_left hsq hc.le
    rw [mul_div_cancel₀ _ hc.ne'] at this
    linarith
  calc Real.exp (-c * (Real.sqrt (a * Real.log 2 / c) + 1) ^ 2) ≤ Real.exp (-(a * Real.log 2)) :=
        Real.exp_le_exp.mpr hle
    _ = (1 / 2 : ℝ) ^ a := by
        rw [Real.rpow_def_of_pos (by norm_num), Real.log_div (by norm_num) (by norm_num),
          Real.log_one]
        ring_nf

 
theorem budget_real (j : ℕ) (hj : 2 ≤ j) :
    (25 * 4 ^ (32 * j) : ℝ) * (2 ^ (16 * j) * ((1 / 2 : ℝ) ^ 128) ^ j +
      (1 / 8 : ℝ) ^ (32 * j) + 2 ^ (16 * j) * ((1 / 2 : ℝ) ^ 40) ^ (4 * j)) ≤ (1 / 2 : ℝ) ^ 41 := by
  set t : ℝ := 2 ^ j with ht
  have ht4 : (4 : ℝ) ≤ t := by
    rw [ht]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have htpos : 0 < t := by linarith
  have e1 : (4 : ℝ) ^ (32 * j) = t ^ 64 := by
    rw [ht, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have e2 : (2 : ℝ) ^ (16 * j) = t ^ 16 := by rw [ht, ← pow_mul]; ring_nf
  have e3 : ((1 / 2 : ℝ) ^ 128) ^ j = 1 / t ^ 128 := by
    rw [ht, one_div_pow, one_div_pow, ← pow_mul, ← pow_mul]; ring_nf
  have e4 : (1 / 8 : ℝ) ^ (32 * j) = 1 / t ^ 96 := by
    rw [ht, show (1 / 8 : ℝ) = 1 / 2 ^ 3 by norm_num, one_div_pow, ← pow_mul, ← pow_mul]
    ring_nf
  have e5 : ((1 / 2 : ℝ) ^ 40) ^ (4 * j) = 1 / t ^ 160 := by
    rw [ht, one_div_pow, one_div_pow, ← pow_mul, ← pow_mul]; ring_nf
  rw [e1, e2, e3, e4, e5]
  have hrw : (25 * t ^ 64 : ℝ) * (t ^ 16 * (1 / t ^ 128) + 1 / t ^ 96 + t ^ 16 * (1 / t ^ 160)) =
      25 * (1 / t ^ 48 + 1 / t ^ 32 + 1 / t ^ 80) := by
    field_simp
  rw [hrw]
  have h32 : (2 : ℝ) ^ 64 ≤ t ^ 32 := by
    calc (2 : ℝ) ^ 64 = 4 ^ 32 := by norm_num
      _ ≤ t ^ 32 := pow_le_pow_left₀ (by norm_num) ht4 32
  have h48 : t ^ 32 ≤ t ^ 48 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h80 : t ^ 32 ≤ t ^ 80 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hp32 : 0 < t ^ 32 := by positivity
  have i1 : 1 / t ^ 48 ≤ 1 / t ^ 32 := one_div_le_one_div_of_le hp32 h48
  have i2 : 1 / t ^ 80 ≤ 1 / t ^ 32 := one_div_le_one_div_of_le hp32 h80
  have i3 : 1 / t ^ 32 ≤ 1 / (2 : ℝ) ^ 64 := one_div_le_one_div_of_le (by positivity) h32
  have : (25 : ℝ) * (1 / t ^ 48 + 1 / t ^ 32 + 1 / t ^ 80) ≤ 75 * (1 / (2 : ℝ) ^ 64) := by
    linarith
  refine this.trans ?_
  rw [one_div_pow]
  norm_num

 
theorem budget (c : ℝ) (hc : 0 < c) (j : ℕ) (hj : 2 ≤ j) (A u : ℝ)
    (hA : Real.exp (-c * A ^ 2) ≤ (1 / 2 : ℝ) ^ 41)
    (hu : Real.exp (-c * u ^ 2) ≤ (1 / 2 : ℝ) ^ 128) :
    ENNReal.ofReal (Real.exp (-c * A ^ 2)) +
        ((25 * 4 ^ (32 * j) : ℕ) : ℝ≥0∞) *
          (((Nat.choose (32 * j / 2) (32 * j / 32) : ℝ≥0∞)) *
              (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ^ (32 * j / 32) +
            ENNReal.ofReal ((1 / 8 : ℝ) ^ (32 * j)) +
            (Nat.choose (32 * j / 2) (32 * j / 8) : ℝ≥0∞) *
              (ENNReal.ofReal (1 - qbar)) ^ (32 * j / 8)) ≤
      ENNReal.ofReal (1 - qbar) := by
  have hj1 : 32 * j / 2 = 16 * j := by omega
  have hj2 : 32 * j / 32 = j := by omega
  have hj3 : 32 * j / 8 = 4 * j := by omega
  rw [hj1, hj2, hj3]
  have hq : 1 - qbar = (1 / 2 : ℝ) ^ 40 := by unfold qbar; ring
  rw [hq]
  have hc1 : ((Nat.choose (16 * j) j : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ (16 * j)) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast Nat.choose_le_two_pow (16 * j) j
  have hc2 : ((Nat.choose (16 * j) (4 * j) : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ (16 * j)) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast Nat.choose_le_two_pow (16 * j) (4 * j)
  have hu' : (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ^ j ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ 128) ^ j) := by
    rw [ENNReal.ofReal_pow (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal hu) j
  have hb' : (ENNReal.ofReal ((1 / 2 : ℝ) ^ 40)) ^ (4 * j) =
      ENNReal.ofReal (((1 / 2 : ℝ) ^ 40) ^ (4 * j)) := (ENNReal.ofReal_pow (by positivity) _).symm
  have hN : ((25 * 4 ^ (32 * j) : ℕ) : ℝ≥0∞) = ENNReal.ofReal (25 * 4 ^ (32 * j)) := by
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  have hinner : ((Nat.choose (16 * j) j : ℝ≥0∞)) * (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ^ j +
      ENNReal.ofReal ((1 / 8 : ℝ) ^ (32 * j)) +
      (Nat.choose (16 * j) (4 * j) : ℝ≥0∞) * (ENNReal.ofReal ((1 / 2 : ℝ) ^ 40)) ^ (4 * j) ≤
      ENNReal.ofReal (2 ^ (16 * j) * ((1 / 2 : ℝ) ^ 128) ^ j + (1 / 8 : ℝ) ^ (32 * j) +
        2 ^ (16 * j) * ((1 / 2 : ℝ) ^ 40) ^ (4 * j)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), hb']
    gcongr
  calc ENNReal.ofReal (Real.exp (-c * A ^ 2)) + ((25 * 4 ^ (32 * j) : ℕ) : ℝ≥0∞) * _
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ 41) + ENNReal.ofReal (25 * 4 ^ (32 * j)) *
          ENNReal.ofReal (2 ^ (16 * j) * ((1 / 2 : ℝ) ^ 128) ^ j + (1 / 8 : ℝ) ^ (32 * j) +
            2 ^ (16 * j) * ((1 / 2 : ℝ) ^ 40) ^ (4 * j)) := by
        rw [hN]
        gcongr
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ 41 + (25 * 4 ^ (32 * j)) *
          (2 ^ (16 * j) * ((1 / 2 : ℝ) ^ 128) ^ j + (1 / 8 : ℝ) ^ (32 * j) +
            2 ^ (16 * j) * ((1 / 2 : ℝ) ^ 40) ^ (4 * j))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ 40) := by
        apply ENNReal.ofReal_le_ofReal
        have := budget_real j hj
        have : (1 / 2 : ℝ) ^ 41 + (1 / 2 : ℝ) ^ 41 = (1 / 2 : ℝ) ^ 40 := by norm_num
        linarith

 

theorem dgffInductionLowerWindow_of_circuitLower (hinput : Inputs.DGFFCircuitLower) :
    Inputs.DGFFInductionLowerWindow := by
  obtain ⟨c, hc, hcirc⟩ := hinput
  have hcir : ∀ m : ℕ, 4 ≤ m → ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (1 - Real.exp (-c * u ^ 2)) ≤ boxDGFF m (highCircuit m u) :=
    fun m hm u hu => hcirc m hm u hu
  obtain ⟨C₂, hC₂, hosc⟩ := harmonic_osc_count (1 / 8) (by norm_num)
  set A : ℝ := Real.sqrt (41 * Real.log 2 / c) + 1
  set u : ℝ := Real.sqrt (128 * Real.log 2 / c) + 1
  set u₀ : ℝ := Real.sqrt (40 * Real.log 2 / c) + 1
  have hA0 : 0 < A := by positivity
  have hu0 : 0 < u := by positivity
  have hu₀0 : 0 < u₀ := by positivity
  have hAexp : Real.exp (-c * A ^ 2) ≤ (1 / 2 : ℝ) ^ 41 := by
    have := exp_level_le c hc 41 (by norm_num)
    simpa [A, Real.rpow_natCast] using this
  have huexp : Real.exp (-c * u ^ 2) ≤ (1 / 2 : ℝ) ^ 128 := by
    have := exp_level_le c hc 128 (by norm_num)
    simpa [u, Real.rpow_natCast] using this
  have hu₀exp : Real.exp (-c * u₀ ^ 2) ≤ (1 / 2 : ℝ) ^ 40 := by
    have := exp_level_le c hc 40 (by norm_num)
    simpa [u₀, Real.rpow_natCast] using this
  set C : ℝ := A + 1 + u + C₂
  intro ξ
  have hξ : (0 : ℝ) < ξ := ξ.2
  set j : ℕ := ⌈Real.exp ((ξ : ℝ) * (C + u₀))⌉₊ + 2
  set K : ℕ := 32 * j
  have hj : 2 ≤ j := by omega
  have hK8 : 8 ≤ K := by omega
  have hKj : (K : ℝ) / 4 = 8 * j := by simp only [K]; push_cast; ring
  have hjexp : Real.exp ((ξ : ℝ) * (C + u₀)) ≤ j := by
    have := Nat.le_ceil (Real.exp ((ξ : ℝ) * (C + u₀)))
    simp only [j]; push_cast; linarith
  set F : ℝ := (K / 4 : ℝ) * Real.exp (-(ξ : ℝ) * C)
  set r₀ : ℝ := Real.exp (-(ξ : ℝ) * u₀)
  have hFr : 8 ≤ F * r₀ := by
    have h1 : F * r₀ = 8 * j * Real.exp (-((ξ : ℝ) * (C + u₀))) := by
      simp only [F, r₀]; rw [hKj, mul_assoc, ← Real.exp_add]; ring_nf
    rw [h1]
    have h2 : Real.exp ((ξ : ℝ) * (C + u₀)) * Real.exp (-((ξ : ℝ) * (C + u₀))) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-((ξ : ℝ) * (C + u₀))) := Real.exp_pos _
    nlinarith
  have hF : 8 ≤ F := by
    have : F * r₀ ≤ F := by
      have hr : r₀ ≤ 1 := by
        simp only [r₀]; rw [Real.exp_le_one_iff]; nlinarith
      have hF0 : 0 ≤ F := by simp only [F]; positivity
      nlinarith
    linarith
  
  set P : ℕ → ℝ → Prop := fun m R =>
    ENNReal.ofReal qbar ≤ boxDGFF m (distEvent m (ξ : ℝ) R)
  have hmono : ∀ m R S, R ≤ S → P m S → P m R := by
    intro m R S hRS hS
    refine hS.trans (measure_mono ?_)
    intro h hh
    exact le_trans hRS hh
  have hbase : ∀ m, 4 ≤ m → P m r₀ := by
    intro m hm
    have h1 := hcir m hm u₀ hu₀0
    have hsub : highCircuit m u₀ ⊆ distEvent m (ξ : ℝ) r₀ := by
      intro h hh
      show r₀ ≤ dgffAnnulusDistance m (ξ : ℝ) h
      have := dgffCircuit_forces_distance m hm ξ u₀ h hh
      simpa [r₀, neg_mul] using this
    refine le_trans ?_ (h1.trans (measure_mono hsub))
    apply ENNReal.ofReal_le_ofReal
    unfold qbar
    linarith
  have hstep : ∀ n, K + 3 ≤ n → ∀ R, 0 < R →
      (∀ m, n - K + 1 ≤ m → m ≤ n - (K + 1) / 2 → P m R) → P n (F * R) := by
    intro n hn R hR hpred
    have := one_step c hc hcir C₂ hosc K n (by simp [K]) (by omega) hn (ξ : ℝ) R qbar A u hξ hR
      qbar_nonneg qbar_le_one hA0 hu0 (budget c hc j hj A u hAexp huexp) hpred
    simpa [P, F, C, mul_assoc] using this
  have hres := repaired_induction_engine P K hK8 F r₀ (Real.exp_pos _) hFr hF hmono hbase hstep
  refine ⟨K, hK8, fun n hn => ?_⟩
  have := hres n hn
  refine le_trans ?_ this
  rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  exact ENNReal.ofReal_le_ofReal qbar_half

end SupercriticalLQGUniqueness.B2.QPos.P5
