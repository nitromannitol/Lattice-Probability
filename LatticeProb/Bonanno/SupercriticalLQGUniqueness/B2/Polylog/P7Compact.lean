/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P7Compact at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7Chains

 












set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 
lemma mem_plRadiusSet_bounds {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) {r : Set.Ioi (0 : ℝ)} (hr : r ∈ plRadiusSet ζ ⟨ε, hε.1⟩) :
    ε < r ∧ (r : ℝ) < 1 := by
  unfold plRadiusSet at hr
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
  rw [Finset.mem_range] at hi
  show ε < (10 : ℝ) ^ (-((i : ℝ) + 2)) * ε ^ (1 - ζ) ∧ (10 : ℝ) ^ (-((i : ℝ) + 2)) * ε ^ (1 - ζ) < 1
  have hε0 := hε.1
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 hε)
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  set x := ζ / 2 * Real.logb 10 ε⁻¹
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) (Real.logb_nonneg (by norm_num)
    (one_le_inv_iff₀.2 ⟨hε0, hε.2.le⟩))
  have hi' : i + 11 ≤ ⌊x⌋₊ := by
    have : i < ⌊x⌋₊ - 10 := hi
    omega
  have hix : (i : ℝ) + 11 ≤ x := by
    have := Nat.floor_le hx0
    have h2 : ((i + 11 : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hi'
    push_cast at h2
    linarith
  have hxdef : x = ζ / 2 * (Real.log ε⁻¹ / Real.log 10) := rfl
  have hpow : 0 < (10 : ℝ) ^ (-((i : ℝ) + 2)) := Real.rpow_pos_of_pos (by norm_num) _
  have hεp : 0 < ε ^ (1 - ζ) := Real.rpow_pos_of_pos hε0 _
  constructor
  · rw [← Real.log_lt_log_iff hε0 (mul_pos hpow hεp), Real.log_mul hpow.ne' hεp.ne',
      Real.log_rpow (by norm_num), Real.log_rpow hε0]
    have hlog' : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
    have h3 : x * Real.log 10 = ζ / 2 * Real.log ε⁻¹ := by
      rw [hxdef]; field_simp [hl10.ne']
    have h1 : ((i : ℝ) + 2) * Real.log 10 ≤ ζ / 2 * Real.log ε⁻¹ - 9 * Real.log 10 := by
      have h4 : ((i : ℝ) + 2) ≤ x - 9 := by linarith
      have := mul_le_mul_of_nonneg_right h4 hl10.le
      linarith
    rw [hlog'] at h1 hlog
    have := mul_pos hζ0 hlog
    nlinarith
  · have h1 : (10 : ℝ) ^ (-((i : ℝ) + 2)) ≤ (10 : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    have h2 : ε ^ (1 - ζ) ≤ 1 := Real.rpow_le_one hε0.le hε.2.le (by linarith)
    have h3 : (10 : ℝ) ^ (-(2 : ℝ)) = 1 / 100 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    calc (10 : ℝ) ^ (-((i : ℝ) + 2)) * ε ^ (1 - ζ) ≤ 1 / 100 * 1 :=
          mul_le_mul (h1.trans h3.le) h2 hεp.le (by norm_num)
      _ < 1 := by norm_num

 
lemma rpow_mem_minmax {ε₀ r a : ℝ} (h0 : 0 < ε₀) (h1 : ε₀ ≤ r) (h2 : r ≤ 1) :
    min 1 (ε₀ ^ a) ≤ r ^ a ∧ r ^ a ≤ max 1 (ε₀ ^ a) := by
  have hr : 0 < r := lt_of_lt_of_le h0 h1
  rcases le_total 0 a with ha | ha
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow h0.le h1 ha),
      (Real.rpow_le_one hr.le h2 ha).trans (le_max_left _ _)⟩
  · exact ⟨(min_le_left _ _).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr h2 ha),
      (Real.rpow_le_rpow_of_nonpos h0 h1 ha).trans (le_max_right _ _)⟩

 
lemma exists_two_sided_of_bounds {L U : ℝ} (hL : 0 < L) :
    ∃ B : ℝ, 1 < B ∧ ∀ x : ℝ, L ≤ x → x ≤ U → B⁻¹ ≤ x ∧ x ≤ B := by
  refine ⟨max U L⁻¹ + 2, by linarith [le_max_right U L⁻¹, inv_pos.2 hL], fun x hx1 hx2 => ⟨?_, ?_⟩⟩
  · refine le_trans ?_ hx1
    rw [inv_le_comm₀ (by linarith [le_max_right U L⁻¹, inv_pos.2 hL]) hL]
    linarith [le_max_right U L⁻¹]
  · linarith [le_max_left U L⁻¹]

 
theorem ratioBC_bounds_compact (hS4 : Iface.DG20Section4) {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    (hQ : IsLFPPExponent ξ Q) {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) :
    ∃ B : ℝ, 1 < B ∧ ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε₀ ≤ ε →
      ∀ r ∈ plRadiusSet ζ ⟨ε, hε.1⟩,
        B⁻¹ ≤ ratioBC m c ⟨ε, hε.1⟩ r ∧ ratioBC m c ⟨ε, hε.1⟩ r ≤ B := by
  obtain ⟨Cg, hCg, hCgb⟩ := (hS4 ξ Q hQ m hm).2.1 1 one_pos
  obtain ⟨Λ, hΛ, hΛb⟩ := hD.2.2.2.2.2.1
  have hΛ0 : 0 < Λ := lt_trans one_pos hΛ
  set c₁ : ℝ := (c ⟨1, Set.mem_Ioi.mpr one_pos⟩ : ℝ)
  have hc₁ : 0 < c₁ := (c _).2
  set L := Cg⁻¹ * min 1 (ε₀ ^ ((ξ : ℝ) * Q + 1)) / (c₁ * (Λ * ε₀ ^ (-Λ)))
  set U := Cg * max 1 (ε₀ ^ ((ξ : ℝ) * Q - 1)) / (c₁ * (Λ⁻¹ * ε₀ ^ Λ))
  have hL : 0 < L := by
    have : 0 < min 1 (ε₀ ^ ((ξ : ℝ) * Q + 1)) := lt_min one_pos (Real.rpow_pos_of_pos hε₀ _)
    have : 0 < ε₀ ^ (-Λ) := Real.rpow_pos_of_pos hε₀ _
    positivity
  obtain ⟨B, hB, hBb⟩ := exists_two_sided_of_bounds (U := U) hL
  refine ⟨B, hB, fun ε hε hε₀ε r hr => hBb _ ?_ ?_⟩ <;>
  · obtain ⟨hεr, hr1⟩ := mem_plRadiusSet_bounds hζ0 hζ1 hε hr
    have hr0 : (0 : ℝ) < r := r.2
    have hε₀r : ε₀ ≤ r := hε₀ε.trans hεr.le
    have hsc := hCgb ⟨r, hr0, hr1⟩ ⟨ε, hε.1, hεr⟩
    have hcb := hΛb ⟨r, hr0, hr1⟩ 1 one_pos
    have e1 : (⟨(r : ℝ) * ((1 : ℚ) : ℝ), Set.mem_Ioi.mpr (mul_pos hr0 (Rat.cast_pos.mpr one_pos))⟩ :
        Set.Ioi (0 : ℝ)) = r := Subtype.ext (by simp)
    have e2 : (⟨((1 : ℚ) : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr one_pos)⟩ : Set.Ioi (0 : ℝ)) =
        ⟨1, Set.mem_Ioi.mpr one_pos⟩ := Subtype.ext (by simp)
    simp only at hcb
    rw [e1, e2] at hcb
    have hsc' : Cg⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + 1) ≤ lfppScaleFactor m ⟨ε, hε.1⟩ r ∧
        lfppScaleFactor m ⟨ε, hε.1⟩ r ≤ Cg * (r : ℝ) ^ ((ξ : ℝ) * Q - 1) := hsc
    have hcr : 0 < (c r : ℝ) := (c r).2
    have hcL : (c r : ℝ) ≤ c₁ * (Λ * ε₀ ^ (-Λ)) := by
      have h := hcb.2
      rw [div_le_iff₀ hc₁] at h
      have : (r : ℝ) ^ (-Λ) ≤ ε₀ ^ (-Λ) :=
        Real.rpow_le_rpow_of_nonpos hε₀ hε₀r (by linarith)
      calc (c r : ℝ) ≤ Λ * (r : ℝ) ^ (-Λ) * c₁ := h
        _ ≤ Λ * ε₀ ^ (-Λ) * c₁ := by gcongr
        _ = _ := by ring
    have hcU : c₁ * (Λ⁻¹ * ε₀ ^ Λ) ≤ (c r : ℝ) := by
      have h := hcb.1
      rw [le_div_iff₀ hc₁] at h
      have : ε₀ ^ Λ ≤ (r : ℝ) ^ Λ := Real.rpow_le_rpow hε₀.le hε₀r hΛ0.le
      calc c₁ * (Λ⁻¹ * ε₀ ^ Λ) = Λ⁻¹ * ε₀ ^ Λ * c₁ := by ring
        _ ≤ Λ⁻¹ * (r : ℝ) ^ Λ * c₁ := by gcongr
        _ ≤ _ := h
    have hmm1 := rpow_mem_minmax (a := (ξ : ℝ) * Q + 1) hε₀ hε₀r hr1.le
    have hmm2 := rpow_mem_minmax (a := (ξ : ℝ) * Q - 1) hε₀ hε₀r hr1.le
    unfold ratioBC
    first
    | (refine div_le_div₀ ?_ ?_ hcr hcL
       · exact le_trans (by positivity) hsc'.1
       · exact le_trans (mul_le_mul_of_nonneg_left hmm1.1 (inv_pos.2 hCg).le) hsc'.1)
    | (refine div_le_div₀ ?_ ?_ (by positivity) hcU
       · exact mul_nonneg hCg.le (le_trans zero_le_one (le_max_left _ _))
       · exact hsc'.2.trans (mul_le_mul_of_nonneg_left hmm2.2 hCg.le))

 
lemma exists_rpow_le {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    ∃ e : ℝ, 0 < e ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ e → ε ^ p ≤ t := by
  refine ⟨t ^ p⁻¹, Real.rpow_pos_of_pos ht _, fun ε h0 h1 => ?_⟩
  calc ε ^ p ≤ (t ^ p⁻¹) ^ p := Real.rpow_le_rpow h0 h1 hp.le
    _ = t := Real.rpow_inv_rpow ht.le hp.ne'

end SupercriticalLQGUniqueness.B2.Polylog
