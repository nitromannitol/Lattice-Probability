/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46STailFinite at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46STailAsymptotic
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SLogCompare

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.GMSLemma27

theorem l46s_coupling_degree_tail_card
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) (s : Finset ℤ) (n : ℕ) :
    P {ω | ∃ x ∈ s, (n : ℕ∞) < MatedCRT.lemma25Degree ε (bm ω) x} ≤
      (s.card : ℝ≥0∞) * ENNReal.ofReal
        (MatedCRT.lemma25TailC₀ * Real.exp (-(MatedCRT.lemma25TailC₁ * n))) := by
  convert l46s_coupling_degree_tail_finset D hε s n using 1
  simp

/-- A finite-region degree tail once a real cardinality bound and a tail
power have been supplied. -/
theorem l46s_coupling_degree_tail_power
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (s : Finset ℤ) (n : ℕ)
    {K b r : ℝ} (_hK : 0 ≤ K)
    (hcard : (s.card : ℝ) ≤ K * ε ^ (-b))
    (htail : Real.exp (-(MatedCRT.lemma25TailC₁ * n)) ≤ ε ^ (r + b)) :
    P {ω | ∃ x ∈ s, (n : ℕ∞) < MatedCRT.lemma25Degree ε (bm ω) x} ≤
      ENNReal.ofReal (K * MatedCRT.lemma25TailC₀ * ε ^ r) := by
  have hp := l46s_coupling_degree_tail_card D hε.1 s n
  have hc0 : 0 ≤ MatedCRT.lemma25TailC₀ := MatedCRT.lemma25TailC₀_pos.le
  have hεpos : 0 < ε := hε.1
  have hreal : (s.card : ℝ) *
      (MatedCRT.lemma25TailC₀ * Real.exp (-(MatedCRT.lemma25TailC₁ * n))) ≤
      K * MatedCRT.lemma25TailC₀ * ε ^ r := by
    have hr2 := mul_le_mul_of_nonneg_right hcard
      (mul_nonneg hc0 (Real.rpow_nonneg hεpos.le (r + b)))
    have hpow : ε ^ (-b) * ε ^ (r + b) = ε ^ r := by
      rw [← Real.rpow_add hεpos]
      congr 1
      ring
    calc
      (s.card : ℝ) * (MatedCRT.lemma25TailC₀ * Real.exp (-(MatedCRT.lemma25TailC₁ * n)))
          ≤ (s.card : ℝ) * (MatedCRT.lemma25TailC₀ * ε ^ (r + b)) := by gcongr
      _ ≤ (K * ε ^ (-b)) * (MatedCRT.lemma25TailC₀ * ε ^ (r + b)) := hr2
      _ = K * MatedCRT.lemma25TailC₀ * ε ^ r := by calc
          _ = K * MatedCRT.lemma25TailC₀ * (ε ^ (-b) * ε ^ (r + b)) := by ring
          _ = _ := by rw [hpow]
  calc
    P {ω | ∃ x ∈ s, (n : ℕ∞) < MatedCRT.lemma25Degree ε (bm ω) x} ≤
        (s.card : ℝ≥0∞) * ENNReal.ofReal
          (MatedCRT.lemma25TailC₀ * Real.exp (-(MatedCRT.lemma25TailC₁ * n))) := hp
    _ = ENNReal.ofReal ((s.card : ℝ) *
          (MatedCRT.lemma25TailC₀ * Real.exp (-(MatedCRT.lemma25TailC₁ * n)))) := by
      have hcast : (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := by simp
      rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (K * MatedCRT.lemma25TailC₀ * ε ^ r) :=
      ENNReal.ofReal_le_ofReal hreal

/-- Uniformly over a polynomially large mesh interval, the maximum
Brownian graph degree exceeds a superlinear log threshold with
superpolynomially small probability. -/
theorem l46s_coupling_degree_tail_superpoly
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {p ζ : ℝ} (hp : 0 ≤ p) (hζ : 0 < ζ) (s : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x ∈ (Finset.Icc ⌈-(ε ^ (-p)) / ε⌉
          (⌈(ε ^ (-p)) / ε⌉ + 1)),
        (⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊ : ℕ∞) <
          MatedCRT.lemma25Degree ε (bm ω) x} ≤
        ENNReal.ofReal (C * ε ^ s) := by
  have htail := l46s_exp_log_power_le_rpow MatedCRT.lemma25TailC₁_pos
    (show 0 < ζ / 2 by linarith) (s + (p + 1))
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      P {ω | ∃ x ∈ (Finset.Icc ⌈-(ε ^ (-p)) / ε⌉
          (⌈(ε ^ (-p)) / ε⌉ + 1)),
        (⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊ : ℕ∞) <
          MatedCRT.lemma25Degree ε (bm ω) x} ≤
        ENNReal.ofReal ((6 * MatedCRT.lemma25TailC₀) * ε ^ s) := by
    filter_upwards [htail, self_mem_nhdsWithin,
      eventually_lt_nhdsGT_zero one_pos] with ε htail hε0 hε1
    have hε : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, hε1⟩
    have hcard := l46s_finite_interval_card_power hε hp
    have htail' : Real.exp (-(MatedCRT.lemma25TailC₁ *
        (⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊ : ℕ))) ≤ ε ^ (s + (p + 1)) := by
      convert htail using 1 <;> ring
    convert l46s_coupling_degree_tail_power D hε
      (Finset.Icc ⌈-(ε ^ (-p)) / ε⌉ (⌈(ε ^ (-p)) / ε⌉ + 1))
      ⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊
      (K := 6) (b := p + 1) (r := s) (by norm_num) hcard htail' using 1 <;> ring
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact exists_bound_of_eventually (fun _ => prob_le_one) hev

end MatedCRTHarmonic.GMS4b
