/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_1Geom at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_1Chain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_5
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS (arXiv:1905.00380, "T"), proof of Proposition 3.1, T:1522–1568.

* `exists_bounded_conn`: T:1525 "We also impose the requirement that `U` is bounded" and T:1566
  (`D_h(𝕣K₁, 𝕣K₂; 𝕣U') ≤ D_h(𝕣K₁, 𝕣K₂; 𝕣U)` for `U ⊆ U'`): a bounded connected open
  `U₀ ⊆ U` containing `K₁ ∪ K₂` (a thickening of `K₁ ∪ γ₀ ∪ K₂`, `γ₀` a path in `U`); own
  elementary construction, since the paper does not say which bounded `U` to use.
* `exists_sep`: disjoint compact sets are at positive distance.
* `scaleFac_bounds`: the two estimates (3.11)/(3.12) of the scaling factor, from (1.2)
  (`eqn-scaling-constant`, part of Axiom V, `TightAcrossScales`) and the circle-average bound
  (3.10) of Lemma 3.4: for `δ ∈ [ε², ε]`,
  `Λ⁻¹ ε^{2Λ+ξq} 𝔠_𝕣 e^{ξh_𝕣(0)} ≤ 𝔠_{δ𝕣} e^{ξ h_{δ𝕣}(w)} ≤ Λ ε^{-(2Λ+ξq)} 𝔠_𝕣 e^{ξh_𝕣(0)}`.
-/

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace P31

lemma exists_bounded_conn {U K₁ K₂ : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hK₁ : IsCompact K₁) (hK₁c : IsConnected K₁) (hK₂ : IsCompact K₂) (hK₂c : IsConnected K₂)
    (h₁U : K₁ ⊆ U) (h₂U : K₂ ⊆ U) :
    ∃ U₀ : Set ℂ, ∃ R₀ : ℝ, 0 < R₀ ∧ IsOpen U₀ ∧ IsConnected U₀ ∧ U₀ ⊆ ball 0 R₀ ∧
      K₁ ⊆ U₀ ∧ K₂ ⊆ U₀ ∧ U₀ ⊆ U := by
  obtain ⟨p, hp⟩ := hK₁c.nonempty
  obtain ⟨q, hq⟩ := hK₂c.nonempty
  have hj : JoinedIn U p q :=
    ((hU.isConnected_iff_isPathConnected).1 hUc).joinedIn p (h₁U hp) q (h₂U hq)
  set γ := hj.somePath
  set S : Set ℂ := K₁ ∪ range γ ∪ K₂
  have hpr : p ∈ range γ := ⟨0, γ.source⟩
  have hqr : q ∈ range γ := ⟨1, γ.target⟩
  have hSc : IsCompact S := (hK₁.union (isCompact_range γ.continuous)).union hK₂
  have hSp : IsPreconnected S :=
    (hK₁c.isPreconnected.union p hp hpr (isPreconnected_range γ.continuous)).union q
      (Or.inr hqr) hq hK₂c.isPreconnected
  have hSU : S ⊆ U := union_subset (union_subset h₁U (by
    rintro _ ⟨t, rfl⟩; exact hj.somePath_mem t)) h₂U
  obtain ⟨δ, hδ, hδU⟩ := hSc.exists_thickening_subset_open hU hSU
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 (hSc.isBounded.thickening (δ := δ))
  have hpS : p ∈ S := Or.inl (Or.inl hp)
  have hR₀pos : 0 < R₀ := by
    have := hR₀ (self_subset_thickening hδ S hpS)
    exact (dist_nonneg).trans_lt (mem_ball.1 this)
  refine ⟨thickening δ S, R₀, hR₀pos, isOpen_thickening, ⟨⟨p, self_subset_thickening hδ S hpS⟩,
    isPreconnected_of_forall p fun y hy => ?_⟩, hR₀,
    fun x hx => self_subset_thickening hδ S (Or.inl (Or.inl hx)),
    fun x hx => self_subset_thickening hδ S (Or.inr hx), hδU⟩
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  refine ⟨S ∪ ball z δ, union_subset (self_subset_thickening hδ S) (ball_subset_thickening hz δ),
    Or.inl hpS, Or.inr (mem_ball.2 hyz), ?_⟩
  exact hSp.union z hz (mem_ball_self hδ) (convex_ball z δ).isPreconnected

lemma exists_sep {K₁ K₂ : Set ℂ} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hd : Disjoint K₁ K₂) : ∃ d : ℝ, 0 < d ∧ ∀ x ∈ K₁, ∀ y ∈ K₂, d ≤ ‖x - y‖ := by
  obtain ⟨δ, hδ, hdisj⟩ := hd.exists_thickenings hK₁ hK₂.isClosed
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 : y ∈ thickening δ K₁ := mem_thickening_iff.2 ⟨x, hx, by rwa [dist_comm, dist_eq_norm]⟩
  exact hdisj.ne_of_mem h1 (self_subset_thickening hδ K₂ hy) rfl

lemma norm_of_mem_scaleSet {𝕣 R : ℝ} (h𝕣 : 0 < 𝕣) {K : Set ℂ} (hK : K ⊆ ball 0 R) {x : ℂ}
    (hx : x ∈ scaleSet 𝕣 0 K) : ‖x‖ < 𝕣 * R := by
  obtain ⟨x', hx', rfl⟩ := hx
  have := mem_ball_zero_iff.1 (hK hx')
  simp only; rw [add_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg h𝕣.le]
  exact mul_lt_mul_of_pos_left this h𝕣

lemma sep_scaleSet {𝕣 d : ℝ} (h𝕣 : 0 < 𝕣) {K₁ K₂ : Set ℂ}
    (hd : ∀ x ∈ K₁, ∀ y ∈ K₂, d ≤ ‖x - y‖) {x y : ℂ} (hx : x ∈ scaleSet 𝕣 0 K₁)
    (hy : y ∈ scaleSet 𝕣 0 K₂) : 𝕣 * d ≤ ‖x - y‖ := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  simp only; rw [add_zero, add_zero, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg h𝕣.le]
  exact mul_le_mul_of_nonneg_left (hd x' hx' y' hy') h𝕣.le

/-- the estimates (3.11), (3.12) on `𝔠_r e^{ξ h_r(w)}` -/
lemma scaleFac_bounds {ξ Λ q ε 𝕣 δ : ℝ} {c : ℝ → ℝ} (hξ : 0 < ξ) (hΛ : 1 < Λ)
    (hc : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ))
    (hcpos : ∀ r, 0 < r → 0 < c r) (hε0 : 0 < ε) (hε1 : ε < 1) (h𝕣 : 0 < 𝕣)
    (hδ0 : ε ^ 2 ≤ δ) (hδ1 : δ ≤ ε) {g : DistC} {w : ℂ}
    (hq : |circleAvg g (δ * 𝕣) w - circleAvg g 𝕣 0| ≤ q * Real.log ε⁻¹) :
    Λ⁻¹ * ε ^ (2 * Λ + ξ * q) * scaleFac ξ c g 𝕣 0 ≤ scaleFac ξ c g (δ * 𝕣) w ∧
      scaleFac ξ c g (δ * 𝕣) w ≤ Λ * ε ^ (-(2 * Λ + ξ * q)) * scaleFac ξ c g 𝕣 0 := by
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδ0
  obtain ⟨hc1, hc2⟩ := hc δ ⟨hδpos, hδ1.trans_lt hε1⟩ 𝕣 h𝕣
  have hc𝕣 := hcpos 𝕣 h𝕣
  rw [le_div_iff₀ hc𝕣] at hc1
  rw [div_le_iff₀ hc𝕣] at hc2
  have hlog : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
  have hpow : ∀ x : ℝ, ε ^ x = Real.exp (Real.log ε * x) := fun x => Real.rpow_def_of_pos hε0 x
  rw [abs_le] at hq
  set a := circleAvg g (δ * 𝕣) w
  set b := circleAvg g 𝕣 0
  have hδΛ1 : (ε ^ 2) ^ Λ ≤ δ ^ Λ := Real.rpow_le_rpow (by positivity) hδ0 (by linarith)
  have hδΛ2 : δ ^ (-Λ) ≤ (ε ^ 2) ^ (-Λ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hδ0 (by linarith)
  have e2 : ∀ x : ℝ, (ε ^ 2) ^ x = Real.exp (Real.log ε * (2 * x)) := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le, hpow]; norm_num
  rw [e2] at hδΛ1 hδΛ2
  unfold scaleFac
  rw [hpow, hpow]
  constructor
  · have hE : Real.exp (Real.log ε * (2 * Λ + ξ * q)) * Real.exp (ξ * b) ≤
        Real.exp (Real.log ε * (2 * Λ)) * Real.exp (ξ * a) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : ξ * b - ξ * q * Real.log ε⁻¹ ≤ ξ * a := by nlinarith
      rw [hlog] at this
      nlinarith
    calc Λ⁻¹ * Real.exp (Real.log ε * (2 * Λ + ξ * q)) * (c 𝕣 * Real.exp (ξ * b))
        = Λ⁻¹ * c 𝕣 * (Real.exp (Real.log ε * (2 * Λ + ξ * q)) * Real.exp (ξ * b)) := by ring
      _ ≤ Λ⁻¹ * c 𝕣 * (Real.exp (Real.log ε * (2 * Λ)) * Real.exp (ξ * a)) := by
          gcongr
      _ = (Λ⁻¹ * Real.exp (Real.log ε * (2 * Λ)) * c 𝕣) * Real.exp (ξ * a) := by ring
      _ ≤ c (δ * 𝕣) * Real.exp (ξ * a) := by
          gcongr
          exact le_trans (by gcongr) hc1
  · have hE : Real.exp (Real.log ε * (2 * -Λ)) * Real.exp (ξ * a) ≤
        Real.exp (Real.log ε * -(2 * Λ + ξ * q)) * Real.exp (ξ * b) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : ξ * a ≤ ξ * b + ξ * q * Real.log ε⁻¹ := by nlinarith
      rw [hlog] at this
      nlinarith
    calc c (δ * 𝕣) * Real.exp (ξ * a) ≤ (Λ * Real.exp (Real.log ε * (2 * -Λ)) * c 𝕣) *
          Real.exp (ξ * a) := by
          gcongr
          exact hc2.trans (by gcongr)
      _ = Λ * c 𝕣 * (Real.exp (Real.log ε * (2 * -Λ)) * Real.exp (ξ * a)) := by ring
      _ ≤ Λ * c 𝕣 * (Real.exp (Real.log ε * -(2 * Λ + ξ * q)) * Real.exp (ξ * b)) := by
          gcongr
      _ = _ := by ring

end P31

end LQGMetric.DFGPS
