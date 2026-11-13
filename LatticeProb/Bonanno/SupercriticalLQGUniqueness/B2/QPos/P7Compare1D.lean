/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7Compare1D at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Spectral1D
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Gauss1D

 











set_option autoImplicit false
noncomputable section

open MeasureTheory Real Finset
open LQGMetric LQGMetric.HeatSq

namespace SupercriticalLQGUniqueness.B2.QPos.P7

 
def pc (N : ℕ) (α : ℤ → ℝ) (r : ℝ) : ℝ :=
  ∑ c ∈ sites1 N, α c * (cell1 N c).indicator (1 : ℝ → ℝ) r

lemma prof_eq_pc (N : ℕ) (s : ℝ) (a : ℤ) : prof N s a = pc N (fun c => (N : ℝ) * qker N s a c) :=
  rfl

lemma integrable_pc (N : ℕ) (α : ℤ → ℝ) : Integrable (pc N α) :=
  integrable_finset_sum _ fun c _ => integrable_indicator_cell1 N c _

lemma integral_pc {N : ℕ} (hN : 0 < N) (α : ℤ → ℝ) :
    ∫ r, pc N α r = (∑ c ∈ sites1 N, α c) / N := by
  unfold pc
  rw [integral_finset_sum _ fun c _ => integrable_indicator_cell1 N c _, sum_div]
  refine sum_congr rfl fun c _ => ?_
  rw [integral_const_mul, integral_indicator_one (measurableSet_cell1 N c), volume_cell1 hN]
  ring

lemma pc_mul_pc {N : ℕ} (hN : 0 < N) (α β : ℤ → ℝ) (r : ℝ) :
    pc N α r * pc N β r = pc N (fun c => α c * β c) r := by
  unfold pc
  rw [sum_mul_sum]
  refine sum_congr rfl fun c hc => ?_
  have : ∀ c' ∈ sites1 N, α c * (cell1 N c).indicator (1 : ℝ → ℝ) r *
      (β c' * (cell1 N c').indicator (1 : ℝ → ℝ) r) =
      α c * β c' * (if c = c' then (cell1 N c).indicator (1 : ℝ → ℝ) r else 0) := by
    intro c' _
    rw [← indicator_cell1_mul hN]; ring
  rw [sum_congr rfl this]
  simp only [mul_ite, mul_zero, sum_ite_eq, hc, if_true]

 
def cellCount (N : ℕ) (r : ℝ) : ℝ := pc N (fun _ => 1) r

lemma cellCount_sq {N : ℕ} (hN : 0 < N) (r : ℝ) : cellCount N r ^ 2 = cellCount N r := by
  unfold cellCount; rw [sq, pc_mul_pc hN]; simp

lemma cellCount_nonneg (N : ℕ) (r : ℝ) : 0 ≤ cellCount N r := by
  unfold cellCount pc
  refine sum_nonneg fun c _ => ?_
  rw [one_mul]; apply Set.indicator_nonneg; intro _ _; norm_num

lemma cellCount_le_one {N : ℕ} (hN : 0 < N) (r : ℝ) : cellCount N r ≤ 1 := by
  have h := cellCount_sq hN r
  have h0 := cellCount_nonneg N r
  nlinarith

lemma cellCount_eq_one {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : |r| < 1 - 1 / (2 * N)) :
    cellCount N r = 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℤ := ⌊(N : ℝ) * r + 1 / 2⌋
  have hc1 := Int.floor_le ((N : ℝ) * r + 1 / 2)
  have hc2 := Int.lt_floor_add_one ((N : ℝ) * r + 1 / 2)
  have hmem : r ∈ cell1 N c := by
    rw [mem_cell1 hN]; constructor <;> linarith
  have hNr : |(N : ℝ) * r| < N - 1 / 2 := by
    rw [abs_mul, abs_of_pos hN']
    calc (N : ℝ) * |r| < N * (1 - 1 / (2 * N)) := mul_lt_mul_of_pos_left hr hN'
      _ = N - 1 / 2 := by field_simp
  have hcs : c ∈ sites1 N := by
    simp only [sites1, mem_Icc]
    have h1 := (abs_lt.mp hNr).1
    have h2 := (abs_lt.mp hNr).2
    constructor
    · have h3 : (-(N : ℝ)) < c := by linarith
      have h4 : (-(N : ℤ)) < c := by exact_mod_cast h3
      omega
    · have : (c : ℝ) < N := by linarith
      have : c < (N : ℤ) := by exact_mod_cast this
      omega
  unfold cellCount pc
  rw [← add_sum_erase _ _ hcs, Set.indicator_of_mem hmem]
  have : ∀ c' ∈ (sites1 N).erase c, (1 : ℝ) * (cell1 N c').indicator (1 : ℝ → ℝ) r = 0 := by
    intro c' hc'
    have hne : c' ≠ c := (mem_erase.mp hc').1
    have : r ∉ cell1 N c' := fun h => hne (cell1_eq_of_mem hN h hmem)
    simp [this]
  rw [sum_congr rfl this, sum_const_zero]; simp

 
def cmp1Const : ℝ :=
  4 * (2 * (cS1 + cS2) + 8 * imgConst (1 / 5) 2 ^ 2 * (1250 / (2 * π)) +
    (Real.sqrt π)⁻¹ + (Real.sqrt (2 * π))⁻¹ * 80000)

lemma cmp1Const_nonneg : 0 ≤ cmp1Const := by
  unfold cmp1Const
  have := cS1_nonneg; have := cS2_nonneg
  positivity

lemma gauss1_fifth_sq_le {s : ℝ} (hs : 0 < s) : gauss1 s (1 / 5) ^ 2 ≤ 1250 / (2 * π) * s := by
  have hπ := Real.pi_pos
  have hexp5 : Real.exp (-(1 / (25 * s))) ≤ 1250 * s ^ 2 := by
    have h := exp_neg_le_two_div_sq (show 0 < 1 / (25 * s) by positivity)
    refine h.trans (le_of_eq ?_); field_simp; ring
  unfold gauss1
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  have : ((2 : ℕ) : ℝ) * (-(1 / 5 : ℝ) ^ 2 / (2 * s)) = -(1 / (25 * s)) := by
    push_cast; field_simp; ring
  rw [this]
  calc (2 * π * s)⁻¹ * Real.exp (-(1 / (25 * s))) ≤ (2 * π * s)⁻¹ * (1250 * s ^ 2) :=
        mul_le_mul_of_nonneg_left hexp5 (by positivity)
    _ = 1250 / (2 * π) * s := by field_simp

lemma gauss1_tenth_le {s : ℝ} (hs : 0 < s) :
    gauss1 s (1 / 10) ≤ (Real.sqrt (2 * π))⁻¹ * 80000 * (Real.sqrt s)⁻¹ * s ^ 2 := by
  have hπ := Real.pi_pos
  have hexp10 : Real.exp (-(1 / (200 * s))) ≤ 80000 * s ^ 2 := by
    have h := exp_neg_le_two_div_sq (show 0 < 1 / (200 * s) by positivity)
    refine h.trans (le_of_eq ?_); field_simp; ring
  unfold gauss1
  have : -(1 / 10 : ℝ) ^ 2 / (2 * s) = -(1 / (200 * s)) := by field_simp; ring
  rw [this, Real.sqrt_mul (by positivity) s]
  calc (Real.sqrt (2 * π) * Real.sqrt s)⁻¹ * Real.exp (-(1 / (200 * s)))
      ≤ (Real.sqrt (2 * π) * Real.sqrt s)⁻¹ * (80000 * s ^ 2) :=
        mul_le_mul_of_nonneg_left hexp10 (by positivity)
    _ = _ := by rw [mul_inv]; ring

lemma gauss1_eight_zero {s : ℝ} (hs : 0 < s) :
    gauss1 (2 * (4 * s)) 0 = (Real.sqrt π)⁻¹ * (Real.sqrt s)⁻¹ / 4 := by
  have hπ := Real.pi_pos
  unfold gauss1
  rw [show 2 * π * (2 * (4 * s)) = 4 ^ 2 * π * s by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  simp; field_simp

 
theorem integral_prof_sub_gauss_sq_le {N : ℕ} (hN : 10 ≤ N) {a : ℤ}
    (ha : |(a : ℝ)| ≤ 4 / 5 * N) {s : ℝ} (hs1 : 1 / (2 * (N : ℝ) ^ 2) ≤ s) (hs2 : s ≤ 1 / 2) :
    ∫ r, (prof N s a r - gauss1 s (a / N - r)) ^ 2 ≤
      cmp1Const * (Real.sqrt s)⁻¹ * (((N : ℝ) ^ 4 * s ^ 2)⁻¹ + ((N : ℝ) ^ 2 * s)⁻¹ + s) := by
  have hN0 : 0 < N := by omega
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hπ := Real.pi_pos
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hs1
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hsN : 1 / 2 ≤ s * N ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hs1; linarith
  set x : ℝ := a / N with hx
  have hx45 : |x| ≤ 4 / 5 := by
    rw [hx, abs_div, abs_of_pos hNp, div_le_iff₀ hNp]; linarith
  set K := imgConst (1 / 5) 2
  set α : ℤ → ℝ := fun c => (N : ℝ) * qker N s a c - idk s (c / N) x
  set β : ℤ → ℝ := fun c => idk s (c / N) x - gauss1 s (x - c / N)
  set g : ℤ → ℝ := fun c => gauss1 s (x - c / N)
  set B : ℝ → ℝ := fun r => gauss1 s (x - r)
  
  have hdecomp : ∀ r, prof N s a r - B r =
      pc N α r + pc N β r + (pc N g r - cellCount N r * B r) -
        (1 - cellCount N r) * B r := by
    intro r
    have h : pc N α r + pc N β r + pc N g r = prof N s a r := by
      rw [prof_eq_pc]; simp only [pc, ← sum_add_distrib]
      refine sum_congr rfl fun c _ => ?_
      simp only [α, β, g]; ring
    linear_combination (-1 : ℝ) * h
  
  have hgap : 1 / (2 * (N : ℝ)) ≤ Real.sqrt s := by
    have h1 : (1 / (2 * (N : ℝ))) ^ 2 ≤ s := by
      have e : (1 / (2 * (N : ℝ))) ^ 2 = 1 / (4 * (N : ℝ) ^ 2) := by field_simp; ring
      rw [e]
      refine le_trans ?_ hs1
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at this
  have hG : ∀ r, (pc N g r - cellCount N r * B r) ^ 2 ≤
      4 / ((N : ℝ) ^ 2 * s) * gauss1 (4 * s) (x - r) ^ 2 := by
    intro r
    have e : pc N g r - cellCount N r * B r =
        pc N (fun c => g c - B r) r := by
      simp only [pc, cellCount, sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun c _ => by ring
    rw [e, sq, pc_mul_pc hN0]
    unfold pc
    calc ∑ c ∈ sites1 N, (g c - B r) * (g c - B r) * (cell1 N c).indicator 1 r
        ≤ ∑ c ∈ sites1 N, (4 / ((N : ℝ) ^ 2 * s) * gauss1 (4 * s) (x - r) ^ 2) *
            (cell1 N c).indicator 1 r := by
          refine sum_le_sum fun c _ => ?_
          by_cases hr : r ∈ cell1 N c
          · rw [Set.indicator_of_mem hr, Pi.one_apply, mul_one, mul_one]
            have hd : |(x - c / N) - (x - r)| ≤ 1 / (2 * N) := by
              rw [mem_cell1 hN0] at hr
              have h1 : |(N : ℝ) * r - c| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
              have e : (x - c / N) - (x - r) = ((N : ℝ) * r - c) / N := by field_simp; ring
              rw [e, abs_div, abs_of_pos hNp, div_le_div_iff₀ hNp (by positivity)]
              nlinarith
            have hb := abs_gauss1_sub_le hs (hd.trans hgap)
            have hb' : |g c - B r| ≤ 4 * (Real.sqrt s)⁻¹ * gauss1 (4 * s) (x - r) *
                (1 / (2 * N)) :=
              hb.trans (mul_le_mul_of_nonneg_left hd (by
                have := gauss1_nonneg (4 * s) (x - r); positivity))
            have hsq' := pow_le_pow_left₀ (abs_nonneg _) hb' 2
            rw [sq_abs] at hsq'
            calc (g c - B r) * (g c - B r) = (g c - B r) ^ 2 := by ring
              _ ≤ (4 * (Real.sqrt s)⁻¹ * gauss1 (4 * s) (x - r) * (1 / (2 * N))) ^ 2 := hsq'
              _ = 4 / ((N : ℝ) ^ 2 * s) * gauss1 (4 * s) (x - r) ^ 2 := by
                  rw [mul_pow, mul_pow, mul_pow, inv_pow, hsq]; field_simp; ring
          · simp [hr]
      _ = 4 / ((N : ℝ) ^ 2 * s) * gauss1 (4 * s) (x - r) ^ 2 * cellCount N r := by
          rw [← mul_sum]; simp [cellCount, pc]
      _ ≤ 4 / ((N : ℝ) ^ 2 * s) * gauss1 (4 * s) (x - r) ^ 2 * 1 := by
          gcongr; exact cellCount_le_one hN0 r
      _ = _ := mul_one _
  
  have hH : ∀ r, ((1 - cellCount N r) * B r) ^ 2 ≤ gauss1 s (1 / 10) * B r := by
    intro r
    have hB0 : 0 ≤ B r := gauss1_nonneg _ _
    by_cases hr : |r| < 1 - 1 / (2 * N)
    · rw [cellCount_eq_one hN0 hr]; simp only [sub_self, zero_mul]
      rw [sq, zero_mul]; exact mul_nonneg (gauss1_nonneg _ _) hB0
    · push_neg at hr
      have hfar : 1 / 10 ≤ |x - r| := by
        have h1 : 1 / (2 * (N : ℝ)) ≤ 1 / 20 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have := abs_sub_abs_le_abs_sub r x
        rw [abs_sub_comm] at this
        linarith
      have hBle : B r ≤ gauss1 s (1 / 10) := by
        have := gauss1_le_of_le_abs hs (by linarith) (by norm_num) (le_refl 0)
          (show (1 / 10 : ℝ) + 0 ≤ |x - r| by linarith)
        simpa using this
      have hc0 := cellCount_nonneg N r
      have hc1 := cellCount_le_one hN0 r
      have hcc := cellCount_sq hN0 r
      have h01 : (1 - cellCount N r) ^ 2 ≤ 1 := by nlinarith
      calc ((1 - cellCount N r) * B r) ^ 2 = (1 - cellCount N r) ^ 2 * (B r * B r) := by ring
        _ ≤ 1 * (B r * B r) := mul_le_mul_of_nonneg_right h01 (mul_nonneg hB0 hB0)
        _ ≤ gauss1 s (1 / 10) * B r := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right hBle hB0
  
  set R : ℝ → ℝ := fun r => 4 * pc N (fun c => α c ^ 2) r + 4 * pc N (fun c => β c ^ 2) r +
    4 * (4 / ((N : ℝ) ^ 2 * s) * gauss1 (4 * s) (x - r) ^ 2) + 4 * (gauss1 s (1 / 10) * B r)
  have hpt : ∀ r, (prof N s a r - B r) ^ 2 ≤ R r := by
    intro r
    rw [hdecomp r]
    have hα : pc N α r ^ 2 = pc N (fun c => α c ^ 2) r := by
      rw [sq, pc_mul_pc hN0]; simp [sq]
    have hβ : pc N β r ^ 2 = pc N (fun c => β c ^ 2) r := by
      rw [sq, pc_mul_pc hN0]; simp [sq]
    have h4 : ∀ p q u v : ℝ, (p + q + u - v) ^ 2 ≤ 4 * p ^ 2 + 4 * q ^ 2 + 4 * u ^ 2 + 4 * v ^ 2 := by
      intro p q u v
      nlinarith [sq_nonneg (p - q), sq_nonneg (p - u), sq_nonneg (p + v), sq_nonneg (q - u),
        sq_nonneg (q + v), sq_nonneg (u + v)]
    refine (h4 _ _ _ _).trans ?_
    simp only [R]
    rw [hα, hβ]
    have := hG r
    have := hH r
    linarith
  have i1 : Integrable (fun r => 4 * pc N (fun c => α c ^ 2) r) :=
    (integrable_pc N _).const_mul 4
  have i2 : Integrable (fun r => 4 * pc N (fun c => β c ^ 2) r) :=
    (integrable_pc N _).const_mul 4
  have i3 : Integrable (fun r => 4 * (4 / ((N : ℝ) ^ 2 * s) * gauss1 (4 * s) (x - r) ^ 2)) :=
    ((integrable_gauss1_sub_sq (by positivity : (0 : ℝ) < 4 * s) x).const_mul _).const_mul 4
  have i4 : Integrable (fun r => 4 * (gauss1 s (1 / 10) * B r)) :=
    ((integrable_gauss1_sub hs x).const_mul _).const_mul 4
  have hRint : Integrable R := ((i1.add i2).add i3).add i4
  have hmain : ∫ r, (prof N s a r - B r) ^ 2 ≤ ∫ r, R r :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => sq_nonneg _) hRint
      (Filter.Eventually.of_forall hpt)
  have hRval : ∫ r, R r = 4 * ((∑ c ∈ sites1 N, α c ^ 2) / N) +
      4 * ((∑ c ∈ sites1 N, β c ^ 2) / N) +
      4 * (4 / ((N : ℝ) ^ 2 * s) * gauss1 (2 * (4 * s)) 0) + 4 * (gauss1 s (1 / 10) * 1) := by
    simp only [R]
    rw [integral_add (by exact (i1.add i2).add i3) (by exact i4),
      integral_add (by exact i1.add i2) (by exact i3), integral_add (by exact i1) (by exact i2)]
    simp only [integral_const_mul]
    rw [integral_pc hN0, integral_pc hN0, integral_gauss1_sub_sq (by positivity),
      integral_gauss1_sub hs]
  
  have hD := sum_walk_sub_idk_sq_le N hN0 hs hsN a
  have hE : (∑ c ∈ sites1 N, β c ^ 2) / N ≤ 2 * (2 * K * gauss1 s (1 / 5)) ^ 2 := by
    have hb : ∀ c ∈ sites1 N, β c ^ 2 ≤ (2 * K * gauss1 s (1 / 5)) ^ 2 := by
      intro c hc
      have hu : (c : ℝ) / N ∈ Set.Icc (-1 : ℝ) (-1 + 2) := by
        simp only [sites1, mem_Icc] at hc
        have h1 : (-((N : ℤ) - 1) : ℝ) ≤ c := by exact_mod_cast hc.1
        have h2 : (c : ℝ) ≤ (N : ℤ) - 1 := by exact_mod_cast hc.2
        push_cast at h1 h2
        constructor
        · rw [le_div_iff₀ hNp]; linarith
        · rw [div_le_iff₀ hNp]; linarith
      have hv : x ∈ Set.Icc (-1 + 1 / 5 : ℝ) (-1 + 2 - 1 / 5) := by
        constructor <;> linarith [(abs_le.mp hx45).1, (abs_le.mp hx45).2]
      have himg := abs_intervalDirKernel_sub_le hs (by linarith) (by norm_num : (0 : ℝ) < 1 / 5)
        (by norm_num : (0 : ℝ) < 2) hu hv
      have : β c = intervalDirKernel (-1) 2 s (c / N) x - gauss1 s (c / N - x) := by
        simp only [β, idk, gauss1_sub_comm s x]
      rw [this]
      exact pow_le_pow_left₀ (abs_nonneg _) himg 2 |>.trans' (by rw [sq_abs])
    have hsum : ∑ c ∈ sites1 N, β c ^ 2 ≤ (2 * N) * (2 * K * gauss1 s (1 / 5)) ^ 2 := by
      calc ∑ c ∈ sites1 N, β c ^ 2 ≤ ∑ _c ∈ sites1 N, (2 * K * gauss1 s (1 / 5)) ^ 2 :=
            sum_le_sum hb
        _ = ((sites1 N).card : ℝ) * (2 * K * gauss1 s (1 / 5)) ^ 2 := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ (2 * N) * (2 * K * gauss1 s (1 / 5)) ^ 2 := by
            gcongr
            simp only [sites1, Int.card_Icc]
            rw [show (N : ℤ) - 1 + 1 - -((N : ℤ) - 1) = ((2 * N - 1 : ℕ) : ℤ) by omega]
            simp only [Int.toNat_natCast]
            rw [Nat.cast_sub (by omega)]; push_cast; linarith
    rw [div_le_iff₀ hNp]; linarith
  have hg5 := gauss1_fifth_sq_le hs
  have hg10 := gauss1_tenth_le hs
  have hg8 := gauss1_eight_zero hs
  have hs_le : s ≤ 1 := by linarith
  have hsqs : (Real.sqrt s)⁻¹ * s ≥ s := by
    have : Real.sqrt s ≤ 1 := by rw [Real.sqrt_le_one]; linarith
    rw [ge_iff_le, le_mul_iff_one_le_left hs]
    exact one_le_inv_iff₀.mpr ⟨hss, this⟩
  rw [show (fun r => (prof N s a r - gauss1 s (a / N - r)) ^ 2) =
    fun r => (prof N s a r - B r) ^ 2 from rfl]
  refine hmain.trans ?_
  rw [hRval, hg8]
  
  have hA : 0 ≤ ((N : ℝ) ^ 4 * s ^ 2)⁻¹ := by positivity
  have hB : 0 ≤ ((N : ℝ) ^ 2 * s)⁻¹ := by positivity
  have hI : 0 ≤ (Real.sqrt s)⁻¹ := by positivity
  have hDα : (∑ c ∈ sites1 N, α c ^ 2) / N ≤
      2 * (cS1 + cS2) * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ := hD
  have hEs : 2 * (2 * K * gauss1 s (1 / 5)) ^ 2 ≤
      8 * K ^ 2 * (1250 / (2 * π)) * ((Real.sqrt s)⁻¹ * s) := by
    have : 2 * (2 * K * gauss1 s (1 / 5)) ^ 2 = 8 * K ^ 2 * gauss1 s (1 / 5) ^ 2 := by ring
    rw [this]
    have hK2 : 0 ≤ 8 * K ^ 2 := by positivity
    calc 8 * K ^ 2 * gauss1 s (1 / 5) ^ 2 ≤ 8 * K ^ 2 * (1250 / (2 * π) * s) :=
          mul_le_mul_of_nonneg_left hg5 hK2
      _ ≤ 8 * K ^ 2 * (1250 / (2 * π) * ((Real.sqrt s)⁻¹ * s)) := by
          gcongr
      _ = _ := by ring
  have hGs : 4 / ((N : ℝ) ^ 2 * s) * ((Real.sqrt π)⁻¹ * (Real.sqrt s)⁻¹ / 4) =
      (Real.sqrt π)⁻¹ * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 2 * s)⁻¹ := by
    field_simp
  have hHs : gauss1 s (1 / 10) * 1 ≤ (Real.sqrt (2 * π))⁻¹ * 80000 * ((Real.sqrt s)⁻¹ * s) := by
    rw [mul_one]
    refine hg10.trans ?_
    have : s ^ 2 ≤ s := by nlinarith
    calc (Real.sqrt (2 * π))⁻¹ * 80000 * (Real.sqrt s)⁻¹ * s ^ 2
        ≤ (Real.sqrt (2 * π))⁻¹ * 80000 * (Real.sqrt s)⁻¹ * s := by gcongr
      _ = _ := by ring
  rw [hGs]
  set I := (Real.sqrt s)⁻¹
  set A := ((N : ℝ) ^ 4 * s ^ 2)⁻¹
  set B' := ((N : ℝ) ^ 2 * s)⁻¹
  set K'' := 8 * K ^ 2 * (1250 / (2 * π))
  set p1 := (Real.sqrt π)⁻¹
  set p2 := (Real.sqrt (2 * π))⁻¹ * 80000
  have hcS := add_nonneg cS1_nonneg cS2_nonneg
  have hK0 : 0 ≤ K'' := by positivity
  have hp1 : 0 ≤ p1 := by positivity
  have hp2 : 0 ≤ p2 := by positivity
  have hkey : 4 * ((∑ c ∈ sites1 N, α c ^ 2) / N) + 4 * ((∑ c ∈ sites1 N, β c ^ 2) / N) +
      4 * (p1 * I * B') + 4 * (gauss1 s (1 / 10) * 1) ≤
      4 * (2 * (cS1 + cS2) * I * A + K'' * (I * s) + p1 * I * B' + p2 * (I * s)) := by
    have := hE.trans hEs
    linarith
  have hexpand : cmp1Const * I * (A + B' + s) =
      4 * (2 * (cS1 + cS2) * I * A + K'' * (I * s) + p1 * I * B' + p2 * (I * s)) +
      4 * (2 * (cS1 + cS2) * I * (B' + s) + K'' * I * (A + B') + p1 * I * (A + s) +
        p2 * I * (A + B')) := by
    have hcm : cmp1Const = 4 * (2 * (cS1 + cS2) + K'' + p1 + p2) := rfl
    rw [hcm]; ring
  have hextra : 0 ≤ 4 * (2 * (cS1 + cS2) * I * (B' + s) + K'' * I * (A + B') +
      p1 * I * (A + s) + p2 * I * (A + B')) := by positivity
  linarith

end SupercriticalLQGUniqueness.B2.QPos.P7
