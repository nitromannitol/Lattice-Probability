/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P10Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L9Tail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable
import LatticeProb.Bonanno.LQGMetric.LFPP.PathAnalytic

/-!
# DDDF Lemma 9 / DF Lemma 4.7 for crossing lengths in a compact set (for DDDF Prop 10)

`lemma9_tail` (L9Tail.lean) is stated for marked rectangles and globally continuous fields. DDDF
Prop 10 (arXiv:1904.08021, l. 725–736; proof DF Props. 4.5–4.6, arXiv:1809.02607, l. 534–608)
needs it for the crossing length `L(A, B; K)` of a compact `K` and a field `Ψ = φ_H` that is
only continuous on `K`. `tail_cross` is the same statement and the same proof (DDDF l. 701–722:
conditionally on `Γ` fix a near-geodesic, Jensen and Chebyshev, `moment_select_bound`), with
the near-geodesics selected from the countable family `exists_enum_family` with additive slack
`1/n` (a crossing of a general `K` may have length `0`, so the multiplicative slack of
`exists_nearGeodesic` is not available); if `K` has no admissible crossing both lengths are `∞`
and the event is empty.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- a crossing length along an admissible path of a continuous field is finite -/
lemma lfppLen_ne_top_of_adm {ξ : ℝ} {f : ℂ → ℝ} (hf : Continuous f) {K A B : Set ℂ}
    (hK : IsCompact K) {Q : ℝ → ℂ} (hQ : AdmPath K A B Q) : lfppLen ξ f Q ≠ ∞ := by
  obtain ⟨z, -, w, -, hQc, hQK⟩ := hQ
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn (continuous_abs.comp hf).continuousOn).isBounded.bddAbove
  have h1 := lfppLen_le_of_abs_sub_le (ξ := ξ) (f := f) (g := fun _ => 0) (P := Q) (c := M)
    fun t ht => by simpa using hM ⟨Q t, hQK t ht, rfl⟩
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) h1
  have : lfppLen ξ (fun _ => (0 : ℝ)) Q = ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖deriv Q t‖ := by
    simp [lfppLen]
  rw [this]; exact hQc.lintegral_norm_deriv_lt_top.ne

/-- **DDDF Lemma 9 / DF Lemma 4.7 for `L(A, B; K)`**: for independent fields `Γ` (continuous) and
`Ψ` (continuous on `K`) with `Ψ x ~ N(0, v_x)`, `v_x ≤ σ²` on `K`, `ε < e^{−ξ²σ²/2}`,
`s = √(2ξ²σ² log ε⁻¹)`: `P(e^s L(Γ) < L(Γ + Ψ)) ≤ ε`. -/
theorem tail_cross {ξ σ ε : ℝ} (hξ : 0 < ξ) (hσ : 0 < σ) (hε0 : 0 < ε)
    (hε : ε < Real.exp (-(ξ * σ) ^ 2 / 2)) {K A B : Set ℂ} (hK : IsCompact K)
    {Γ Ψ : ℂ → Ω → ℝ} (hΓc : ∀ ω, Continuous fun x => Γ x ω) (hΓm : ∀ x, Measurable (Γ x))
    (hΨc : ∀ ω, ContinuousOn (fun x => Ψ x ω) K) (hΨm : ∀ x, Measurable (Ψ x))
    (hind : IndepFun (fun ω x => Γ x ω) (fun ω x => Ψ x ω) P)
    (hgauss : ∀ x ∈ K, ∃ v : ℝ≥0, (v : ℝ) ≤ σ ^ 2 ∧ HasLaw (Ψ x) (gaussianReal 0 v) P) :
    P {ω | ENNReal.ofReal (Real.exp (Real.sqrt (2 * (ξ * σ) ^ 2 * Real.log ε⁻¹))) *
        crossLenIn ξ (fun x => Γ x ω) K A B < crossLenIn ξ (fun x => Γ x ω + Ψ x ω) K A B} ≤
      ENNReal.ofReal ε := by
  set τ := ξ * σ with hτdef
  have hτ : 0 < τ := mul_pos hξ hσ
  set s := Real.sqrt (2 * τ ^ 2 * Real.log ε⁻¹) with hsdef
  set α := s / τ ^ 2 with hαdef
  obtain ⟨hα, hval⟩ := lemma9_exponents hτ hε0 hε
  have hα0 : 0 < α := by linarith
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp s) with hcdef
  have hc0 : c ≠ 0 := by rw [hcdef]; exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  set L : Ω → ℝ≥0∞ := fun ω => crossLenIn ξ (fun x => Γ x ω) K A B with hLdef
  set L' : Ω → ℝ≥0∞ := fun ω => crossLenIn ξ (fun x => Γ x ω + Ψ x ω) K A B with hL'def
  by_cases hadm : ∃ P₀, AdmPath K A B P₀
  swap
  · have htop : ∀ f : ℂ → ℝ, crossLenIn ξ f K A B = ⊤ := fun f => by
      rw [crossLenIn_eq_biInf]
      exact iInf₂_eq_top.2 fun P hP => absurd ⟨P, hP⟩ hadm
    have : {ω | c * L ω < L' ω} = ∅ := by
      ext ω; simp only [hLdef, hL'def, htop, ENNReal.mul_top hc0, lt_self_iff_false,
        mem_ofPred_eq, mem_empty_iff_false]
    simp only [hLdef, hL'def] at this
    rw [this, measure_empty]; exact zero_le'
  obtain ⟨P₀, hP₀⟩ := hadm
  obtain ⟨Q, hQa, hQ⟩ := exists_enum_family (ξ := ξ) hK hP₀
  have hLt : ∀ ω, L ω ≠ ∞ := fun ω =>
    ne_top_of_le_ne_top (lfppLen_ne_top_of_adm (hΓc ω) hK (hQa 0))
      (crossLenIn_le_lfppLen (hQa 0))
  set M : ℝ≥0∞ := ENNReal.ofReal (Real.exp (σ ^ 2 * (α * ξ) ^ 2 / 2)) with hMdef
  have hMc : M / c ^ α = ENNReal.ofReal ε := by
    rw [hcdef, hMdef, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hα0.le,
      ← Real.exp_mul, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
    congr 1
    rw [← Real.exp_log hε0, ← hval]
    congr 1
    rw [hτdef]; ring
  have hΓle : (fieldSigma Γ) ≤ mΩ := (measurable_pi_iff.2 hΓm).comap_le
  have hΨle : (fieldSigma Ψ) ≤ mΩ := (measurable_pi_iff.2 hΨm).comap_le
  have hind' : Indep (fieldSigma Γ) (fieldSigma Ψ) P := (IndepFun_iff_Indep _ _ _).1 hind
  have hΓσ : ∀ x, Measurable[(fieldSigma Γ)] (Γ x) := fun x =>
    (measurable_pi_apply x).comp (comap_measurable (fun ω x => Γ x ω))
  have hΨσ : ∀ x, Measurable[(fieldSigma Ψ)] (Ψ x) := fun x =>
    (measurable_pi_apply x).comp (comap_measurable (fun ω x => Ψ x ω))
  set E : ℕ → Set Ω := fun n => {ω | c * (L ω + (n : ℝ≥0∞)⁻¹) < L' ω} with hEdef
  have hkey : ∀ n, P (E n) ≤ ENNReal.ofReal ε := fun n => by
    have hQm : ∀ j, Measurable[fieldSigma Γ] fun ω => lfppLen ξ (fun x => Γ x ω) (Q j) :=
      fun j => by
        obtain ⟨_, -, _, -, hPw, -⟩ := hQa j
        exact @measurable_lfppLen ξ Ω (fieldSigma Γ) Γ hΓc hΓσ _ hPw.continuousOn
    have hLm : Measurable[fieldSigma Γ] L :=
      @measurable_crossLenIn ξ K A B Ω (fieldSigma Γ) hK Γ hΓc hΓσ
    obtain ⟨J, hJm, hJ⟩ := @exists_measurable_select ξ K A B Ω (fieldSigma Γ) Q Γ
      (fun ω => hQ _ (hΓc ω)) hQm (fun ω => L ω + (n : ℝ≥0∞)⁻¹)
      (hLm.add_const _) fun ω => ENNReal.lt_add_right (hLt ω) (ENNReal.inv_ne_zero.2
        (ENNReal.natCast_ne_top n))
    set z : ℕ → ℝ → ℂ := fun j t => Q j (projIcc (0 : ℝ) 1 zero_le_one t) with hzdef
    have hz : ∀ j, Continuous (z j) := fun j => by
      obtain ⟨_, -, _, -, hPw, -⟩ := hQa j
      exact hPw.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun t => (projIcc _ _ _ t).2
    have hzK : ∀ j t, z j t ∈ K := fun j t => by
      obtain ⟨_, -, _, -, -, hU⟩ := hQa j
      exact hU _ (projIcc _ _ _ t).2
    set A' : ℕ → ℝ → Ω → ℝ≥0∞ := fun j t ω =>
      ENNReal.ofReal (Real.exp (ξ * Γ (z j t) ω) * ‖deriv (Q j) t‖) with hAdef
    set F : ℕ → ℝ → Ω → ℝ≥0∞ := fun j t ω =>
      ENNReal.ofReal (Real.exp (ξ * Ψ (z j t) ω) * (fun _ => (1 : ℝ)) t) with hFdef
    have hA : ∀ j, Measurable[@Prod.instMeasurableSpace ℝ Ω _ (fieldSigma Γ)]
        (uncurry (A' j)) := fun j =>
      measurable_expWeight (m := fieldSigma Γ) hΓc hΓσ (hz j) ((measurable_deriv (Q j)).norm) ξ
    have hF : ∀ j, Measurable[@Prod.instMeasurableSpace ℝ Ω _ (fieldSigma Ψ)]
        (uncurry (F j)) := fun j => by
      refine measurable_uncurry_of_continuous_of_measurable (m := fieldSigma Ψ)
        (u := F j) (fun ω => ?_) (fun t => ?_)
      · refine ENNReal.continuous_ofReal.comp (Continuous.mul ?_ continuous_const)
        exact Real.continuous_exp.comp (continuous_const.mul
          ((hΨc ω).comp_continuous (hz j) (hzK j)))
      · exact (((hΨσ _).const_mul ξ).exp.mul measurable_const).ennreal_ofReal
    have hM : ∀ j t, ∫⁻ ω, F j t ω ^ α ∂P ≤ M := fun j t => by
      obtain ⟨v, hv, hlaw⟩ := hgauss _ (hzK j t)
      have heq : ∀ ω, F j t ω ^ α = ENNReal.ofReal (Real.exp ((α * ξ) * Ψ (z j t) ω)) :=
        fun ω => by
          simp only [hFdef, mul_one]
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hα0.le, ← Real.exp_mul]
          congr 2; ring
      simp_rw [heq]
      exact lintegral_exp_gauss_le hlaw hv _
    have hmom :=
      moment_select_bound (fieldSigma Γ) (fieldSigma Ψ) hΓle hΨle hind' hA hF hα hM hJm hc0 hct
    rw [hMc] at hmom
    refine le_trans (measure_mono fun ω hω => ?_) hmom
    simp only [hEdef, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq]
    have hG : lfppLen ξ (fun x => Γ x ω) (Q (J ω)) = ∫⁻ t in Icc (0 : ℝ) 1, A' (J ω) t ω :=
      lfppLen_eq_projIcc _ _ _
    have hH : lfppLen ξ (fun x => Γ x ω + Ψ x ω) (Q (J ω)) =
        ∫⁻ t in Icc (0 : ℝ) 1, A' (J ω) t ω * F (J ω) t ω := by
      rw [lfppLen_eq_projIcc]
      refine lintegral_congr fun t => ?_
      simp only [hAdef, hFdef, mul_one]
      exact ofReal_exp_add_split ξ _ _ _ (norm_nonneg _)
    rw [← hG, ← hH]
    have h1 : L' ω ≤ lfppLen ξ (fun x => Γ x ω + Ψ x ω) (Q (J ω)) :=
      crossLenIn_le_lfppLen (hQa (J ω))
    calc c * lfppLen ξ (fun x => Γ x ω) (Q (J ω)) ≤ c * (L ω + (n : ℝ≥0∞)⁻¹) := by
          gcongr; exact (hJ ω).le
      _ < L' ω := hω
      _ ≤ _ := h1
  have hmono : Monotone E := fun n m hnm ω hω => by
    simp only [hEdef, mem_ofPred_eq] at hω ⊢
    refine lt_of_le_of_lt ?_ hω
    gcongr
  have hsub : {ω | c * L ω < L' ω} ⊆ ⋃ n, E n := fun ω hω => by
    simp only [mem_ofPred_eq] at hω
    have hcLt : c * L ω ≠ ∞ := ENNReal.mul_ne_top hct (hLt ω)
    refine mem_iUnion.2 ?_
    set d := L' ω - c * L ω
    have hd : d ≠ 0 := (tsub_pos_of_lt hω).ne'
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.div_pos hd hct).ne'
    refine ⟨n, ?_⟩
    simp only [hEdef, mem_ofPred_eq]
    have h2 : c * (n : ℝ≥0∞)⁻¹ < d := by
      calc c * (n : ℝ≥0∞)⁻¹ = (n : ℝ≥0∞)⁻¹ * c := mul_comm _ _
        _ < d / c * c := ENNReal.mul_lt_mul_left hc0 hct hn
        _ = d := ENNReal.div_mul_cancel hc0 hct
    calc c * (L ω + (n : ℝ≥0∞)⁻¹) = c * L ω + c * (n : ℝ≥0∞)⁻¹ := by ring
      _ < c * L ω + d := ENNReal.add_lt_add_left hcLt h2
      _ = L' ω := add_tsub_cancel_of_le hω.le
  calc P {ω | c * L ω < L' ω} ≤ P (⋃ n, E n) := measure_mono hsub
    _ = ⨆ n, P (E n) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal ε := iSup_le hkey

end DDDF
end LQGMetric
