/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3Gt1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs

/-!
# GM Theorem 4.2: reduction to `λ₄ > 1` by scaling (D75 (b))

Decision `decisions/DEC-75.md` (b) (own argument, DV-D75): GM use `λ₄ ≥ 1` (Lemma 4.22, l. 2555;
GM l. 1611 even assume `λ₃ = 1`, "the proof when `λ₃ ≠ 1` is identical"). `T4_2Gt1` is `T4_2` with
the extra hypothesis `1 < lam 3`; `gm_T4_2_of_gt1` recovers `T4_2` by an integer scaling
`s = ⌈1/λ₄⌉₊ + 1`: `λ' = sλ`, `𝕣' = 𝕣/s`, `U' = sU`, `ℛ' = {r | sr ∈ ℛ}`, `E'_r = E_{sr}`,
`𝔈'_r = 𝔈_{sr}` (all hypotheses transfer since `λ'_i r = λ_i (sr)`; the grid `ε^q𝕣ℤ²` is contained
in `ε^q𝕣'ℤ²` as `s ∈ ℕ`, `𝕣'U' = 𝕣U` and `ℓ𝕣' ≤ ℓ𝕣`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `T4_2` with the extra hypothesis `1 < lam 3` (GM l. 2555; D75 (b)); `0 < ε₀` (D95) -/
def T4_2Gt1 : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c → ∀ (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)),
  (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) →
  ∃ νs : ℝ, νs ∈ Ioo (0 : ℝ) 1 ∧ ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν ≤ νs → ∀ lam : Fin 5 → ℝ,
  0 < lam 0 → lam 0 < lam 1 → lam 1 ≤ lam 2 → lam 2 ≤ lam 3 → lam 3 < lam 4 → 1 < lam 3 →
  ∃ 𝕡 ∈ Ioo (0 : ℝ) 1, ∀ (q ℓ : ℝ) (U : Set ℂ), 0 < q → ℓ ∈ Ioo (0 : ℝ) 1 → IsOpen U →
  Bornology.IsBounded U → ∀ ε₀ Λ η : ℝ, 0 < ε₀ → 0 < η → ∃ ε₁ : ℝ, 0 < ε₁ ∧
  ∀ (R : ℝ) (Rad : Set ℝ) (E : ℝ → ℂ → Set DistC) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC), 0 < R →
    GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₁,
    P {ω | ∀ a b : ℂ, (∃ m : ℤ × ℤ, a = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      (∃ m : ℤ × ℤ, b = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      a ∈ (fun x => (R : ℂ) * x) '' U → b ∈ (fun x => (R : ℂ) * x) '' U → ℓ * R ≤ ‖a - b‖ →
      ∃ z : ℂ, ∃ r ∈ Rad, r ∈ Icc (ε ^ (1 + ν) * R) (ε * R) ∧
        (range (sel a b (h ω)) ∩ Metric.ball z (lam 1 * r)).Nonempty ∧ h ω ∈ Ef r z a b ∧
        a ∉ Metric.ball z (lam 3 * r) ∧ b ∉ Metric.ball z (lam 3 * r)}ᶜ ≤
      ENNReal.ofReal η

/-- the scaled hypotheses (D75 (b)) -/
theorem gm_geoIterateHyp_scale {D : DistC → ContMetric}
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {μ ν : ℝ} {lam : Fin 5 → ℝ} {𝕡 R ε₀ Λ : ℝ}
    {Rad : Set ℝ} {E : ℝ → ℂ → Set DistC} {Ef : ℝ → ℂ → ℂ → ℂ → Set DistC} {s : ℝ}
    (hs : 0 < s) (H : GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef) :
    GeoIterateHyp D sel μ ν (fun i => s * lam i) 𝕡 (R / s) ε₀ Λ {r | s * r ∈ Rad}
      (fun r z => E (s * r) z) (fun r z a b => Ef (s * r) z a b) := by
  obtain ⟨hRad, hΛ, hE, hEf, h1, hP⟩ := H
  have e : ∀ (i : Fin 5) (r : ℝ), s * lam i * r = lam i * (s * r) := fun i r => by ring
  refine ⟨fun r hr => ?_, hΛ, fun r z g c => hE (s * r) z g c,
    fun r z a b g c => hEf (s * r) z a b g c, fun ε hε => ?_, fun {Ω} _ P _ h hh => ?_⟩
  · obtain ⟨h0, h1'⟩ := hRad hr
    refine ⟨pos_of_mul_pos_right h0 hs.le, ?_⟩
    rw [mul_div_assoc', le_div_iff₀ hs]; linarith
  · obtain ⟨rr, hrr1, hrr2⟩ := h1 ε hε
    refine ⟨fun k => rr k / s, fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
    · obtain ⟨⟨l, u⟩, -⟩ := hrr1 k hk
      constructor
      · rw [mul_div_assoc', div_le_div_iff_of_pos_right hs]; exact l
      · rw [mul_div_assoc', div_le_div_iff_of_pos_right hs]; exact u
    · show s * (rr k / s) ∈ Rad
      rw [mul_div_cancel₀ _ hs.ne']; exact (hrr1 k hk).2
    · have := hrr2 k hk
      have e1 : s * lam 3 / (s * lam 0) = lam 3 / lam 0 := mul_div_mul_left _ _ hs.ne'
      have e2 : rr k / s / (rr (k + 1) / s) = rr k / rr (k + 1) := div_div_div_cancel_right₀
        hs.ne' _ _
      simp only [e1, e2]; exact this
  · obtain ⟨hg, h2, h2f, h3, h4⟩ := hP P h hh
    refine ⟨hg, fun z r hr => ?_, fun z r hr a b => ?_, fun z r hr => h3 z _ hr,
      fun z r hr a b hab ha hb => ?_⟩
    · simp only [e]; exact h2 z _ hr
    · simp only [e]; exact h2f z _ hr a b
    · simp only [e] at ha hb ⊢
      exact h4 z _ hr a b hab ha hb

/-- refining the grid `cℤ²` to `(c/N)ℤ²` -/
theorem gm_grid_refine (c : ℝ) (N : ℕ) (hN : (N : ℝ) ≠ 0) (m : ℤ × ℤ) :
    ((c : ℝ) : ℂ) * (m.1 + m.2 * Complex.I) =
      ((c / N : ℝ) : ℂ) * (((N * m.1 : ℤ) : ℂ) + ((N * m.2 : ℤ) : ℂ) * Complex.I) := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp

/-- **`T4_2` from `T4_2Gt1`** (D75 (b), own scaling argument, DV-D75) -/
theorem gm_T4_2_of_gt1 (H : T4_2Gt1) : T4_2 := by
  intro γ D c hγ hγ2 hD sel hsel
  obtain ⟨νs, hνs, H1⟩ := H hγ hγ2 hD sel hsel
  refine ⟨νs, hνs, fun {μ ν} hμ hμν hνs' lam h0 h01 h12 h23 h34 => ?_⟩
  have hl3 : 0 < lam 3 := by linarith
  set s : ℝ := ((⌈(lam 3)⁻¹⌉₊ + 1 : ℕ) : ℝ) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hs1 : 1 ≤ s := by rw [hsdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈(lam 3)⁻¹⌉₊]
  have hsl : 1 < s * lam 3 := by
    have : (lam 3)⁻¹ < s := by
      rw [hsdef]; push_cast; linarith [Nat.le_ceil (lam 3)⁻¹]
    calc (1 : ℝ) = (lam 3)⁻¹ * lam 3 := by field_simp
      _ < s * lam 3 := mul_lt_mul_of_pos_right this hl3
  obtain ⟨𝕡, h𝕡, H2⟩ := H1 hμ hμν hνs' (fun i => s * lam i) (mul_pos hs0 h0)
    (mul_lt_mul_of_pos_left h01 hs0) (mul_le_mul_of_nonneg_left h12 hs0.le)
    (mul_le_mul_of_nonneg_left h23 hs0.le) (mul_lt_mul_of_pos_left h34 hs0) hsl
  refine ⟨𝕡, h𝕡, fun q ℓ U hq hℓ hU hUb ε₀ Λ η hε₀ hη => ?_⟩
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  set U' : Set ℂ := (fun x : ℂ => (s : ℂ) * x) '' U with hU'def
  have hU' : IsOpen U' := (Homeomorph.mulLeft₀ (s : ℂ) hsC).isOpenMap U hU
  have hU'b : Bornology.IsBounded U' := by
    obtain ⟨C, hC⟩ := hUb.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨s * C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    exact mul_le_mul_of_nonneg_left (hC x hx) hs0.le
  obtain ⟨ε₁, hε₁, H3⟩ := H2 q ℓ U' hq hℓ hU' hU'b ε₀ Λ η hε₀ hη
  refine ⟨ε₁, hε₁, fun R Rad E Ef hR hyp Ω _ P _ h hh ε hε => ?_⟩
  refine le_trans (measure_mono ?_) (H3 (R / s) {r | s * r ∈ Rad} (fun r z => E (s * r) z)
    (fun r z a b => Ef (s * r) z a b) (div_pos hR hs0) (gm_geoIterateHyp_scale hs0 hyp) P h hh
    ε hε)
  refine compl_subset_compl.2 fun ω hω a b ha hb haU hbU hab => ?_
  have hgrid : ∀ x : ℂ, (∃ m : ℤ × ℤ, x = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      ∃ m : ℤ × ℤ, x = ((ε ^ q * (R / s) : ℝ) : ℂ) * (m.1 + m.2 * Complex.I) := by
    rintro x ⟨m, rfl⟩
    refine ⟨((⌈(lam 3)⁻¹⌉₊ + 1 : ℕ) * m.1, (⌈(lam 3)⁻¹⌉₊ + 1 : ℕ) * m.2), ?_⟩
    rw [show ε ^ q * (R / s) = ε ^ q * R / ((⌈(lam 3)⁻¹⌉₊ + 1 : ℕ) : ℝ) by rw [hsdef]; ring]
    exact gm_grid_refine _ _ (by positivity) m
  have hU1 : ∀ x : ℂ, x ∈ (fun y => (R : ℂ) * y) '' U →
      x ∈ (fun y => ((R / s : ℝ) : ℂ) * y) '' U' := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(s : ℂ) * y, ⟨y, hy, rfl⟩, ?_⟩
    simp only
    push_cast
    field_simp
  have hab' : ℓ * (R / s) ≤ ‖a - b‖ := by
    refine le_trans ?_ hab
    rw [mul_div_assoc']
    exact div_le_self (mul_pos hℓ.1 hR).le hs1
  obtain ⟨z, r', hr', ⟨hrl, hru⟩, hhit, hEf, ha', hb'⟩ :=
    hω a b (hgrid a ha) (hgrid b hb) (hU1 a haU) (hU1 b hbU) hab'
  have e : ∀ i : Fin 5, s * lam i * r' = lam i * (s * r') := fun i => by ring
  refine ⟨z, s * r', hr', ⟨?_, ?_⟩, ?_, hEf, ?_, ?_⟩
  · rw [mul_div_assoc', div_le_iff₀ hs0] at hrl; linarith
  · rw [mul_div_assoc', le_div_iff₀ hs0] at hru; linarith
  · rw [← e]; exact hhit
  · rw [← e]; exact ha'
  · rw [← e]; exact hb'

end LQGMetric.GM
