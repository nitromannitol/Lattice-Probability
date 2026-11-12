/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightA at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw

/-!
GM (arXiv:1905.00383v3) l. 449–452: Axiom V "implies the tightness of various functionals of
`D_h`", e.g. of `(𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(rK, r∂U))⁻¹` (DFGPS (1.4), T:370–374). No proof is
given. Decision D-A3 (`decisions/DEC-A.md` (c)) states the nodes proved here, for a weak γ-LQG
metric `D` with constants `𝔠 = c`, uniformly over whole-plane GFFs `h`, scales `r > 0` and
centres `z` (writing `𝔞 = 𝔠_r e^{ξ h_r(z)}`):

* `gm_S2_4a`: disjoint compacts `K₁, K₂`: `∀ ε > 0 ∃ s > 0`,
  `P[∃ u ∈ K₁, v ∈ K₂, D_h(ru + z, rv + z) ≤ s 𝔞] < ε`.
* `gm_S2_4a_sep` (separated points): compact `K`, `b > 0`: `∀ ε ∃ s > 0`,
  `P[∃ u, v ∈ K, |u − v| ≥ b, D_h(ru + z, rv + z) ≤ s 𝔞] < ε` (the inverse modulus of GM l. 1071).
* `gm_S2_4b` (uniform modulus): compact `K`, `s > 0`: `∀ ε ∃ b > 0`,
  `P[∃ u, v ∈ K, |u − v| ≤ b, D_h(ru + z, rv + z) ≥ s 𝔞] < ε`.
* `gm_S2_4b'` (diameter): compact `K`: `∀ ε ∃ S`, `P[∃ u, v ∈ K, D_h(ru + z, rv + z) ≥ S 𝔞] < ε`.

All four are instances of `Tight.tight_mapsTo` (Prokhorov + Portmanteau + the closure property of
Axiom V). Own argument (no source); DEVIATIONS DA5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM
namespace Tight

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

lemma cmetric_nonneg {d : C(ℂ × ℂ, ℝ)} (hd : IsContinuousMetric d) (p : ℂ × ℂ) : 0 ≤ d p := by
  have h1 := hd.triangle p.1 p.2 p.1
  rw [hd.self_eq_zero, hd.symm p.2 p.1] at h1
  linarith

/-- `s < 𝔠_r⁻¹ e^{−ξt} x ↔ s 𝔠_r e^{ξt} < x` -/
lemma lt_scaled_iff {C : ℝ} (hC : 0 < C) (ξ t s x : ℝ) :
    s < C⁻¹ * Real.exp (-ξ * t) * x ↔ s * C * Real.exp (ξ * t) < x := by
  have he : Real.exp (-ξ * t) = (Real.exp (ξ * t))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  have hp : 0 < C * Real.exp (ξ * t) := mul_pos hC (Real.exp_pos _)
  rw [he, ← mul_inv, mul_assoc, inv_mul_eq_div, lt_div_iff₀ hp]

lemma scaled_lt_iff {C : ℝ} (hC : 0 < C) (ξ t s x : ℝ) :
    C⁻¹ * Real.exp (-ξ * t) * x < s ↔ x < s * C * Real.exp (ξ * t) := by
  have he : Real.exp (-ξ * t) = (Real.exp (ξ * t))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  have hp : 0 < C * Real.exp (ξ * t) := mul_pos hC (Real.exp_pos _)
  rw [he, ← mul_inv, inv_mul_eq_div, div_lt_iff₀ hp, mul_assoc]

lemma one_div_succ_anti : Antitone fun n : ℕ => (1 : ℝ) / (n + 1) := fun m n hmn =>
  one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)

lemma isCompact_near_diag {K : Set ℂ} (hK : IsCompact K) (b : ℝ) :
    IsCompact {p : ℂ × ℂ | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ b} :=
  (hK.prod hK).inter_right (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const)

/-- Crossing lower bound from `tight_mapsTo` with `U n = (1/(n+1), ∞)`, on any compact `A`
avoiding the diagonal. -/
theorem tight_lower_of_offDiag (hD : IsWeakLQGMetric γ D c) {A : Set (ℂ × ℂ)}
    (hA : IsCompact A) (hAd : ∀ p ∈ A, p.1 ≠ p.2) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ ∀ p ∈ A, s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
        (D (h ω)).1 ((r : ℂ) * p.1 + z, (r : ℂ) * p.2 + z)} < ε := by
  obtain ⟨n, hn⟩ := tight_mapsTo hD (A := fun _ => A) (fun _ => hA) (fun _ _ _ => le_rfl)
    (U := fun n => Ioi ((1 : ℝ) / (n + 1))) (fun _ => isOpen_Ioi)
    (fun m n hmn => Ioi_subset_Ioi (one_div_succ_anti hmn))
    (fun d hd x hx => by
      have hx' : x ∈ A := mem_iInter.1 hx 0
      have hpos : 0 < d x := lt_of_le_of_ne (cmetric_nonneg hd x)
        (fun h0 => hAd x hx' (hd.eq_of_eq_zero x.1 x.2 h0.symm))
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact ⟨n, hn⟩) hε
  refine ⟨1 / (n + 1), by positivity, fun P _ h hh r hr z => ?_⟩
  refine lt_of_le_of_lt (measure_mono fun ω hω => ?_) (hn P h hh r hr z)
  intro hmaps
  refine hω fun p hp => ?_
  have := hmaps hp
  simp only [mem_Ioi, scaledField_apply] at this
  exact (lt_scaled_iff (hD.tightness.1 r hr) _ _ _ _).1 this

/-- **GM.S2.4a** (D-A3): crossing lower bound between disjoint compacts, uniformly in the field,
the scale and the centre. -/
theorem gm_S2_4a (hD : IsWeakLQGMetric γ D c) {K₁ K₂ : Set ℂ} (hK₁ : IsCompact K₁)
    (hK₂ : IsCompact K₂) (hdisj : Disjoint K₁ K₂) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₂, s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
        (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)} < ε := by
  obtain ⟨s, hs, H⟩ := tight_lower_of_offDiag hD (hK₁.prod hK₂)
    (fun p hp heq => hdisj.ne_of_mem hp.1 hp.2 heq) hε
  refine ⟨s, hs, fun P _ h hh r hr z => lt_of_le_of_lt (measure_mono fun ω hω => ?_)
    (H P h hh r hr z)⟩
  exact fun hall => hω fun u hu v hv => hall (u, v) ⟨hu, hv⟩

/-- **GM.S2.4b** (D-A3): uniform modulus of continuity. -/
theorem gm_S2_4b (hD : IsWeakLQGMetric γ D c) {K : Set ℂ} (hK : IsCompact K) {s : ℝ}
    (hs : 0 < s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
        (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z) <
          s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)} < ε := by
  obtain ⟨n, hn⟩ := tight_mapsTo hD
    (A := fun n => {p : ℂ × ℂ | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ 1 / (n + 1)})
    (fun n => isCompact_near_diag hK _)
    (fun m n hmn p hp => ⟨hp.1, hp.2.trans (one_div_succ_anti hmn)⟩)
    (U := fun _ => Iio s) (fun _ => isOpen_Iio) (fun _ _ _ => le_rfl)
    (fun d hd x hx => by
      have h0 : ‖x.1 - x.2‖ ≤ 0 := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        exact ((mem_iInter.1 hx n).2.trans hn.le).trans (by linarith)
      have hx12 : x.1 = x.2 := sub_eq_zero.1 (norm_le_zero_iff.1 h0)
      refine ⟨0, ?_⟩
      show d x < s
      have : d x = 0 := by
        rcases x with ⟨x1, x2⟩
        simp only at hx12
        subst hx12
        exact hd.self_eq_zero x1
      rw [this]; exact hs) hε
  refine ⟨1 / (n + 1), by positivity, fun P _ h hh r hr z => ?_⟩
  refine lt_of_le_of_lt (measure_mono fun ω hω => ?_) (hn P h hh r hr z)
  intro hmaps
  refine hω fun u hu v hv huv => ?_
  have := hmaps (show (u, v) ∈ {p : ℂ × ℂ | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ 1 / (n + 1)} from
    ⟨⟨hu, hv⟩, huv⟩)
  simp only [mem_Iio, scaledField_apply] at this
  exact (scaled_lt_iff (hD.tightness.1 r hr) _ _ _ _).1 this

end Tight
end GM
end LQGMetric
