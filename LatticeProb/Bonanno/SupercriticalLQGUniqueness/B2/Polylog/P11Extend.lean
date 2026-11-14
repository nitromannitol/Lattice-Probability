/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P11Extend at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P10DyadicRate

 














set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.Polylog

 
lemma rpow_bounds_of_half_le {δ α : ℝ} (h1 : 1 / 2 ≤ δ) (h2 : δ ≤ 1) :
    (2 : ℝ) ^ (-|α|) ≤ δ ^ α ∧ δ ^ α ≤ (2 : ℝ) ^ |α| := by
  have hδ : 0 < δ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : |Real.log δ| ≤ Real.log 2 := by
    rw [abs_le]
    constructor
    · have := Real.log_le_log (by norm_num) h1
      rw [one_div, Real.log_inv] at this
      linarith
    · have := Real.log_le_log hδ h2
      rw [Real.log_one] at this
      linarith
  have hb : |Real.log δ * α| ≤ Real.log 2 * |α| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hl (abs_nonneg _)
  rw [abs_le] at hb
  rw [Real.rpow_def_of_pos hδ, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  constructor
  · apply Real.exp_le_exp.2
    have : Real.log 2 * -|α| = -(Real.log 2 * |α|) := by ring
    rw [this]; exact hb.1
  · exact Real.exp_le_exp.2 hb.2

 
theorem normalizer_comparable_of_dyadic {α Λ k K : ℝ} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    (hΛ : 1 < Λ)
    (hrat : ∀ δ : Set.Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (hk : 0 ≤ k)
    (hdy : ∀ n : ℕ, Real.exp (-k) * (dyad n : ℝ) ^ α ≤ c (dyad n) ∧
      (c (dyad n) : ℝ) ≤ Real.exp k * (dyad n : ℝ) ^ α)
    (hK : 1 < K)
    (hsub : ∀ r s : Ioi (0 : ℝ), (K⁻¹) ^ 3 * ((c r : ℝ) * c s) ≤ c (mulI r s) ∧
      (c (mulI r s) : ℝ) ≤ K ^ 3 * ((c r : ℝ) * c s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Ioi (0 : ℝ),
      C⁻¹ * (r : ℝ) ^ α ≤ c r ∧ (c r : ℝ) ≤ C * (r : ℝ) ^ α := by
  have hΛ0 : 0 < Λ := by linarith
  set B : ℝ := (2 : ℝ) ^ |α| with hBdef
  have hB1 : 1 ≤ B := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  have hB0 : 0 < B := by linarith
  have hBinv : (2 : ℝ) ^ (-|α|) = B⁻¹ := Real.rpow_neg (by norm_num) _
  set Lr : ℝ := Λ * (2 : ℝ) ^ Λ with hLrdef
  have h2Λ : 1 ≤ (2 : ℝ) ^ Λ := Real.one_le_rpow (by norm_num) hΛ0.le
  have hLr1 : 1 ≤ Lr := by nlinarith
  have hLr0 : 0 < Lr := by linarith
  set A : ℝ := Lr * Real.exp k * B with hAdef
  have hek1 : 1 ≤ Real.exp k := Real.one_le_exp hk
  have hA0 : 0 < A := by positivity
  have hAe : Real.exp k ≤ A := by
    have : 1 ≤ Lr * B := one_le_mul_of_one_le_of_one_le hLr1 hB1
    calc Real.exp k = 1 * Real.exp k := (one_mul _).symm
      _ ≤ (Lr * B) * Real.exp k := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = A := by rw [hAdef]; ring
  
  have hsmall : ∀ r : Ioi (0 : ℝ), (r : ℝ) ≤ 1 →
      A⁻¹ * (r : ℝ) ^ α ≤ c r ∧ (c r : ℝ) ≤ A * (r : ℝ) ^ α := by
    intro r hr1
    have hr0 : (0 : ℝ) < r := r.2
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hr0 hr1 (by norm_num : (0 : ℝ) < 2⁻¹)
      (by norm_num)
    have hd0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    have hdyn : (dyad n : ℝ) = (2 : ℝ)⁻¹ ^ n := rfl
    set δ : ℝ := (r : ℝ) / (2 : ℝ)⁻¹ ^ n with hδdef
    have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hd0]; exact hn2
    have hδh : 1 / 2 < δ := by
      rw [hδdef, lt_div_iff₀ hd0]
      calc 1 / 2 * (2 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ (n + 1) := by rw [pow_succ]; ring
        _ < r := hn1
    have hrδ : (r : ℝ) = δ * (2 : ℝ)⁻¹ ^ n := by rw [hδdef, div_mul_cancel₀ _ hd0.ne']
    
    have hpow : (dyad n : ℝ) ^ α = (r : ℝ) ^ α * δ ^ (-α) := by
      rw [hdyn, hrδ, Real.mul_rpow (by linarith) hd0.le, Real.rpow_neg (by linarith)]
      field_simp [(Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < δ) α).ne']
    obtain ⟨hδl, hδu⟩ := rpow_bounds_of_half_le (α := -α) hδh.le hδ1
    rw [abs_neg, hBinv] at hδl
    rw [abs_neg] at hδu
    have hrα : 0 < (r : ℝ) ^ α := Real.rpow_pos_of_pos hr0 α
    
    have hcmp : Lr⁻¹ * (c (dyad n) : ℝ) ≤ c r ∧ (c r : ℝ) ≤ Lr * c (dyad n) := by
      have hcd : (0 : ℝ) < c (dyad n) := (c (dyad n)).2
      rcases hδ1.lt_or_eq with hlt | heq
      · let δI : Set.Ioo (0 : ℝ) 1 := ⟨δ, by linarith, hlt⟩
        have hq : (0 : ℚ) < (2 : ℚ)⁻¹ ^ n := by positivity
        have hqR : (((2 : ℚ)⁻¹ ^ n : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ n := by push_cast; ring
        obtain ⟨hlo, hhi⟩ := hrat δI ((2 : ℚ)⁻¹ ^ n) hq
        have e1 : (c ⟨(δI : ℝ) * (((2 : ℚ)⁻¹ ^ n : ℚ) : ℝ), Set.mem_Ioi.mpr (mul_pos δI.property.1
            (Rat.cast_pos.mpr hq))⟩ : ℝ) = c r := by
          congr 2; apply Subtype.ext; show δ * _ = (r : ℝ); rw [hrδ, hqR]
        have e2 : (c ⟨(((2 : ℚ)⁻¹ ^ n : ℚ) : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hq)⟩ : ℝ) =
            c (dyad n) := by
          congr 2; apply Subtype.ext; exact hqR
        rw [e1, e2] at hlo hhi
        have hδΛl : (2 : ℝ) ^ (-Λ) ≤ δ ^ Λ := by
          rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
          exact Real.rpow_le_rpow (by norm_num) (by rw [one_div] at hδh; linarith) hΛ0.le
        have hδΛu : δ ^ (-Λ) ≤ (2 : ℝ) ^ Λ := by
          rw [Real.rpow_neg (by linarith), ← Real.inv_rpow (by linarith)]
          apply Real.rpow_le_rpow (by positivity) _ hΛ0.le
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        constructor
        · have : Lr⁻¹ ≤ (c r : ℝ) / c (dyad n) := by
            refine le_trans ?_ hlo
            rw [hLrdef, mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            exact mul_le_mul_of_nonneg_left hδΛl (inv_nonneg.2 hΛ0.le)
          rwa [le_div_iff₀ hcd] at this
        · have : (c r : ℝ) / c (dyad n) ≤ Lr :=
            hhi.trans (mul_le_mul_of_nonneg_left hδΛu hΛ0.le)
          rwa [div_le_iff₀ hcd] at this
      · have hrd : r = dyad n := by
          apply Subtype.ext; rw [hrδ, heq, one_mul]; rfl
        rw [hrd]
        constructor
        · calc Lr⁻¹ * (c (dyad n) : ℝ) ≤ 1 * c (dyad n) :=
                mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hLr1) hcd.le
            _ = c (dyad n) := one_mul _
        · calc (c (dyad n) : ℝ) = 1 * c (dyad n) := (one_mul _).symm
            _ ≤ Lr * c (dyad n) := mul_le_mul_of_nonneg_right hLr1 hcd.le
    obtain ⟨hdl, hdu⟩ := hdy n
    rw [hpow] at hdl hdu
    constructor
    · calc A⁻¹ * (r : ℝ) ^ α = Lr⁻¹ * (Real.exp (-k) * ((r : ℝ) ^ α * B⁻¹)) := by
            rw [hAdef, Real.exp_neg]; field_simp
        _ ≤ Lr⁻¹ * (Real.exp (-k) * ((r : ℝ) ^ α * δ ^ (-α))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hδl hrα.le) (Real.exp_pos _).le) (inv_nonneg.2 hLr0.le)
        _ ≤ Lr⁻¹ * (c (dyad n) : ℝ) := mul_le_mul_of_nonneg_left hdl (inv_nonneg.2 hLr0.le)
        _ ≤ c r := hcmp.1
    · calc (c r : ℝ) ≤ Lr * c (dyad n) := hcmp.2
        _ ≤ Lr * (Real.exp k * ((r : ℝ) ^ α * δ ^ (-α))) := mul_le_mul_of_nonneg_left hdu hLr0.le
        _ ≤ Lr * (Real.exp k * ((r : ℝ) ^ α * B)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hδu hrα.le) (Real.exp_pos _).le) hLr0.le
        _ = A * (r : ℝ) ^ α := by rw [hAdef]; ring
  
  let one : Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  set c1 : ℝ := (c one : ℝ) with hc1def
  have hc10 : 0 < c1 := (c one).2
  have hK0 : 0 < K := by linarith
  have hK3 : 0 < K ^ 3 := by positivity
  refine ⟨max A (max (K ^ 3 * c1 * A) (K ^ 3 * A / c1)), lt_max_of_lt_left hA0, ?_⟩
  set C := max A (max (K ^ 3 * c1 * A) (K ^ 3 * A / c1)) with hCdef
  have hCA : A ≤ C := le_max_left _ _
  have hC2 : K ^ 3 * c1 * A ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC3 : K ^ 3 * A / c1 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0 : 0 < C := lt_of_lt_of_le hA0 hCA
  intro r
  have hr0 : (0 : ℝ) < r := r.2
  have hrα : 0 < (r : ℝ) ^ α := Real.rpow_pos_of_pos hr0 α
  rcases le_or_gt (r : ℝ) 1 with hr1 | hr1
  · obtain ⟨hl, hu⟩ := hsmall r hr1
    exact ⟨le_trans (mul_le_mul_of_nonneg_right ((inv_le_inv₀ hC0 hA0).2 hCA) hrα.le) hl,
      hu.trans (mul_le_mul_of_nonneg_right hCA hrα.le)⟩
  · let s : Ioi (0 : ℝ) := ⟨(r : ℝ)⁻¹, Set.mem_Ioi.mpr (inv_pos.2 hr0)⟩
    have hs1 : (s : ℝ) ≤ 1 := inv_le_one_of_one_le₀ hr1.le
    obtain ⟨hsl, hsu⟩ := hsmall s hs1
    have hsα : (s : ℝ) ^ α = ((r : ℝ) ^ α)⁻¹ := Real.inv_rpow hr0.le α
    rw [hsα] at hsl hsu
    have hmul : mulI r s = one := Subtype.ext (mul_inv_cancel₀ hr0.ne')
    obtain ⟨hml, hmu⟩ := hsub r s
    rw [hmul] at hml hmu
    have hcs0 : (0 : ℝ) < c s := (c s).2
    have hcr0 : (0 : ℝ) < c r := (c r).2
    constructor
    · 
      have h1 : c1 ≤ K ^ 3 * ((c r : ℝ) * c s) := hmu
      have h2 : (c s : ℝ) ≤ A * ((r : ℝ) ^ α)⁻¹ := hsu
      have h3 : c1 ≤ K ^ 3 * (c r : ℝ) * (A * ((r : ℝ) ^ α)⁻¹) := by
        calc c1 ≤ K ^ 3 * ((c r : ℝ) * c s) := h1
          _ = K ^ 3 * (c r : ℝ) * c s := by ring
          _ ≤ K ^ 3 * (c r : ℝ) * (A * ((r : ℝ) ^ α)⁻¹) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : c1 * (r : ℝ) ^ α ≤ K ^ 3 * A * (c r : ℝ) := by
        have := mul_le_mul_of_nonneg_right h3 hrα.le
        rw [show K ^ 3 * (c r : ℝ) * (A * ((r : ℝ) ^ α)⁻¹) * (r : ℝ) ^ α =
          K ^ 3 * A * (c r : ℝ) by field_simp] at this
        exact this
      calc C⁻¹ * (r : ℝ) ^ α ≤ (K ^ 3 * A / c1)⁻¹ * (r : ℝ) ^ α :=
            mul_le_mul_of_nonneg_right ((inv_le_inv₀ hC0 (by positivity)).2 hC3) hrα.le
        _ = c1 * (r : ℝ) ^ α / (K ^ 3 * A) := by field_simp
        _ ≤ c r := by rw [div_le_iff₀ (by positivity)]; linarith
    · 
      have h1 : (K⁻¹) ^ 3 * ((c r : ℝ) * c s) ≤ c1 := hml
      have h2 : A⁻¹ * ((r : ℝ) ^ α)⁻¹ ≤ c s := hsl
      have h3 : (c r : ℝ) * c s ≤ K ^ 3 * c1 := by
        have hKK : K ^ 3 * (K⁻¹) ^ 3 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hK0.ne', one_pow]
        calc (c r : ℝ) * c s = K ^ 3 * ((K⁻¹) ^ 3 * ((c r : ℝ) * c s)) := by
              rw [← mul_assoc, hKK, one_mul]
          _ ≤ K ^ 3 * c1 := mul_le_mul_of_nonneg_left h1 hK3.le
      have h4 : (c r : ℝ) * (A⁻¹ * ((r : ℝ) ^ α)⁻¹) ≤ K ^ 3 * c1 :=
        le_trans (mul_le_mul_of_nonneg_left h2 hcr0.le) h3
      have h5 : (c r : ℝ) ≤ K ^ 3 * c1 * A * (r : ℝ) ^ α := by
        have := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ A * (r : ℝ) ^ α)
        rw [show (c r : ℝ) * (A⁻¹ * ((r : ℝ) ^ α)⁻¹) * (A * (r : ℝ) ^ α) = c r by
          field_simp] at this
        linarith
      calc (c r : ℝ) ≤ K ^ 3 * c1 * A * (r : ℝ) ^ α := h5
        _ ≤ C * (r : ℝ) ^ α := mul_le_mul_of_nonneg_right hC2 hrα.le

end SupercriticalLQGUniqueness.B2.Polylog
