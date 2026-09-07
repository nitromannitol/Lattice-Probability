/-
The covariance form of the Efron-Stein inequality.

The variance form bounds `Var(F)` by the total resampling energy.  What the
divisible-sandpile paper needs for two odometers is the covariance of two
functions of the same independent field, bounded by the PAIRING of their
coefficient vectors, `∑_z a_z b_z`, and not by the product of their norms:
Cauchy-Schwarz applied to the two variances gives the weaker bound with
`(∑ a_z²)^{1/2} (∑ b_z²)^{1/2}` and is not enough.

The pairing comes out of the same head-tail induction, run on a pair.  Writing
`Φ_f` for the average of `f` over the first coordinate, the decomposition
`f - E f = (Φ_f - E f) + (f - Φ_f)` is orthogonal in each variable separately,
so the two cross terms of `Cov(f, g)` vanish by Fubini, the remaining product of
head fluctuations is Cauchy-Schwarz against the two resampling energies of the
first coordinate, and the covariance of the two head averages is the inductive
hypothesis.  The constant is `1` at every step, which is what the paper's
factor `2` needs, since `E|ζ - ζ'|² = 2 Var(ζ)`.
-/
import LatticeProb.Prob.LpSmooth

noncomputable section

namespace LatticeProb

open MeasureTheory

/-! ### Cauchy-Schwarz for the Bochner integral -/

/-- The product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_sq {α : Type*} [MeasurableSpace α] {P : Measure α} {A B : α → ℝ}
    (hAm : AEStronglyMeasurable A P) (hBm : AEStronglyMeasurable B P)
    (hA2 : Integrable (fun x => A x ^ 2) P) (hB2 : Integrable (fun x => B x ^ 2) P) :
    Integrable (fun x => A x * B x) P := by
  refine Integrable.mono' (hA2.add hB2) (hAm.mul hBm)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|A x| - |B x|), sq_abs (A x), sq_abs (B x),
    abs_nonneg (A x), abs_nonneg (B x)]

/-- A square-integrable function on a probability space is integrable. -/
theorem integrable_of_integrable_sq {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {h : α → ℝ} (hm : AEStronglyMeasurable h P)
    (h2 : Integrable (fun x => h x ^ 2) P) : Integrable h P := by
  refine Integrable.mono' (h2.add (integrable_const 1)) hm
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|h x| - 1), sq_abs (h x), abs_nonneg (h x)]

/-- Subtracting a constant preserves square integrability. -/
theorem integrable_sub_const_sq {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsFiniteMeasure P] {h : α → ℝ} (hm : Measurable h)
    (h2 : Integrable (fun x => h x ^ 2) P) (c : ℝ) :
    Integrable (fun x => (h x - c) ^ 2) P := by
  refine Integrable.mono' ((h2.const_mul 2).add (integrable_const (2 * c ^ 2)))
    (((hm.sub measurable_const).pow_const 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (h x + c)]

/-- **Cauchy-Schwarz.**  The integral of a product is at most the product of the
two square roots of the integrals of the squares. -/
theorem abs_integral_mul_le {α : Type*} [MeasurableSpace α] {P : Measure α} {A B : α → ℝ}
    (hAm : AEStronglyMeasurable A P) (hBm : AEStronglyMeasurable B P)
    (hA2 : Integrable (fun x => A x ^ 2) P) (hB2 : Integrable (fun x => B x ^ 2) P) :
    |∫ x, A x * B x ∂P| ≤ Real.sqrt (∫ x, A x ^ 2 ∂P) * Real.sqrt (∫ x, B x ^ 2 ∂P) := by
  set a := ∫ x, A x ^ 2 ∂P with hadef
  set b := ∫ x, B x ^ 2 ∂P with hbdef
  set c := ∫ x, A x * B x ∂P with hcdef
  have hAB := integrable_mul_of_sq hAm hBm hA2 hB2
  have ha : 0 ≤ a := integral_nonneg fun x => sq_nonneg _
  have hb : 0 ≤ b := integral_nonneg fun x => sq_nonneg _
  have hq : ∀ t : ℝ, 0 ≤ t ^ 2 * a - 2 * t * c + b := by
    intro t
    have hnn : (0 : ℝ) ≤ ∫ x, (t * A x - B x) ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
    have hpt : ∀ x, (t * A x - B x) ^ 2
        = t ^ 2 * A x ^ 2 - 2 * t * (A x * B x) + B x ^ 2 := fun x => by ring
    have hexp : ∫ x, (t * A x - B x) ^ 2 ∂P = t ^ 2 * a - 2 * t * c + b := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_add (f := fun x => t ^ 2 * A x ^ 2 - 2 * t * (A x * B x))
          (g := fun x => B x ^ 2)
          ((hA2.const_mul (t ^ 2)).sub (hAB.const_mul (2 * t))) hB2,
        integral_sub (hA2.const_mul (t ^ 2)) (hAB.const_mul (2 * t)),
        integral_const_mul, integral_const_mul]
    rw [hexp] at hnn
    exact hnn
  have hc2 : c ^ 2 ≤ a * b := by
    rcases eq_or_lt_of_le ha with h | h
    · have ha0 : a = 0 := h.symm
      have hc0 : c = 0 := by
        by_contra hc
        have h2 := hq ((b + 1) / (2 * c))
        have hcc : 2 * ((b + 1) / (2 * c)) * c = b + 1 := by field_simp
        rw [ha0, mul_zero, zero_sub] at h2
        linarith [hcc]
      rw [hc0, ha0]
      simp
    · have h2 := hq (c / a)
      have hne : a ≠ 0 := ne_of_gt h
      have h4 : 0 ≤ a * ((c / a) ^ 2 * a - 2 * (c / a) * c + b) := mul_nonneg h.le h2
      have h5 : a * ((c / a) ^ 2 * a - 2 * (c / a) * c + b) = a * b - c ^ 2 := by
        field_simp; ring
      rw [h5] at h4
      linarith
  calc |c| = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
    _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt hc2
    _ = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b

/-! ### The head average -/

/-- The average of a function over its first coordinate. -/
def headAvg {M : ℕ} (μ : Fin (M + 1) → Measure ℝ) (G : (Fin (M + 1) → ℝ) → ℝ)
    (η : Fin M → ℝ) : ℝ :=
  ∫ x, G (Fin.cons x η) ∂(μ 0)

section Head

variable {M : ℕ} {μ : Fin (M + 1) → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
  {G : (Fin (M + 1) → ℝ) → ℝ}

theorem measurable_headAvg (hGm : Measurable G) : Measurable (headAvg μ G) := by
  have hg : StronglyMeasurable (fun q : (Fin M → ℝ) × ℝ => G (Fin.cons q.2 q.1)) :=
    (hGm.comp (measurable_cons_pair.comp
      (measurable_snd.prodMk measurable_fst))).stronglyMeasurable
  exact (hg.integral_prod_right').measurable

theorem integrable_cons (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ)) :
    Integrable (fun q : ℝ × (Fin M → ℝ) => G (Fin.cons q.1 q.2))
      ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) :=
  integrable_prod_cons_fam μ G
    (integrable_of_integrable_sq _ hGm.aestronglyMeasurable hG2)

theorem integrable_cons_sq (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ)) :
    Integrable (fun q : ℝ × (Fin M → ℝ) => G (Fin.cons q.1 q.2) ^ 2)
      ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) :=
  integrable_prod_cons_fam μ (fun ξ => G ξ ^ 2) hG2

theorem integrable_headAvg_sq (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ)) :
    Integrable (fun η => headAvg μ G η ^ 2) (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) := by
  have hGc2 := integrable_cons_sq (μ := μ) hG2
  have hGc1 := integrable_cons (μ := μ) hGm hG2
  have hW : Integrable (fun η => ∫ x, G (Fin.cons x η) ^ 2 ∂(μ 0))
      (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) := (hGc2.swap).integral_prod_left
  refine Integrable.mono' hW (((measurable_headAvg hGm).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [hGc1.prod_left_ae, hGc2.prod_left_ae] with η h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_integral_le (μ 0) (fun x => G (Fin.cons x η)) h1 h2

theorem integrable_headAvg (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ)) :
    Integrable (headAvg μ G) (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) :=
  ((integrable_cons (μ := μ) hGm hG2).swap).integral_prod_left

theorem integral_headAvg (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ)) :
    ∫ η, headAvg μ G η ∂(Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) = ∫ ξ, G ξ ∂(Measure.pi μ) := by
  rw [integral_prod_cons_fam μ G,
    integral_prod_symm _ (integrable_cons (μ := μ) hGm hG2)]
  rfl

/-- The head fluctuation has mean zero in the head coordinate, for every value
of the tail, the junk value at a tail where the slice is not integrable
included. -/
theorem headAvg_fluct_integral_zero (η : Fin M → ℝ) :
    ∫ x, (G (Fin.cons x η) - headAvg μ G η) ∂(μ 0) = 0 := by
  by_cases h : Integrable (fun x => G (Fin.cons x η)) (μ 0)
  · rw [integral_sub h (integrable_const _)]
    simp [headAvg]
  · rw [integral_undef]
    intro hc
    refine h ((hc.add (integrable_const (headAvg μ G η))).congr
      (Filter.Eventually.of_forall fun x => ?_))
    show (G (Fin.cons x η) - headAvg μ G η) + headAvg μ G η = G (Fin.cons x η)
    ring

theorem integrable_headFluct_sq (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ)) :
    Integrable (fun q : ℝ × (Fin M → ℝ) => (G (Fin.cons q.1 q.2) - headAvg μ G q.2) ^ 2)
      ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) := by
  have hGc2 := integrable_cons_sq (μ := μ) hG2
  have hΦ2 := integrable_headAvg_sq (μ := μ) hGm hG2
  have hYm : Measurable
      (fun q : ℝ × (Fin M → ℝ) => G (Fin.cons q.1 q.2) - headAvg μ G q.2) :=
    (hGm.comp measurable_cons_pair).sub ((measurable_headAvg hGm).comp measurable_snd)
  refine Integrable.mono' ((hGc2.const_mul 2).add ((hΦ2.comp_snd (μ 0)).const_mul 2))
    ((hYm.pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (G (Fin.cons q.1 q.2) + headAvg μ G q.2)]

/-- The energy of the head fluctuation is at most the resampling energy of the
first coordinate. -/
theorem integral_headFluct_sq_le (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ))
    (hE0 : Integrable (fun q : (Fin (M + 1) → ℝ) × ℝ =>
      (G q.1 - G (Function.update q.1 0 q.2)) ^ 2) ((Measure.pi μ).prod (μ 0))) :
    ∫ q : ℝ × (Fin M → ℝ), (G (Fin.cons q.1 q.2) - headAvg μ G q.2) ^ 2
        ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))))
      ≤ resampleEnergy μ G 0 := by
  classical
  set κ : Measure ℝ := μ 0 with hκdef
  set ρ : Measure (Fin M → ℝ) := Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)) with hρdef
  have hMP : MeasurePreserving
      (fun q : ℝ × (Fin M → ℝ) => (Fin.cons q.1 q.2 : Fin (M + 1) → ℝ))
      (κ.prod ρ) (Measure.pi μ) := measurePreserving_cons μ
  have hMPh : MeasurePreserving
      (fun r : (ℝ × (Fin M → ℝ)) × ℝ => ((Fin.cons r.1.1 r.1.2 : Fin (M + 1) → ℝ), r.2))
      ((κ.prod ρ).prod κ) ((Measure.pi μ).prod κ) := hMP.prod (MeasurePreserving.id κ)
  have hmeas0 : Measurable (fun q : (Fin (M + 1) → ℝ) × ℝ =>
      (G q.1 - G (Function.update q.1 0 q.2)) ^ 2) :=
    (((hGm.comp measurable_fst).sub (hGm.comp (measurable_update_pair 0))).pow_const 2)
  have hHcongr : ∀ r : (ℝ × (Fin M → ℝ)) × ℝ,
      (G (Fin.cons r.1.1 r.1.2)
          - G (Function.update (Fin.cons r.1.1 r.1.2 : Fin (M + 1) → ℝ) 0 r.2)) ^ 2
        = (G (Fin.cons r.1.1 r.1.2) - G (Fin.cons r.2 r.1.2)) ^ 2 := by
    intro r
    rw [cons_update_zero]
  have hHtrans : Integrable (fun r : (ℝ × (Fin M → ℝ)) × ℝ =>
      (G (Fin.cons r.1.1 r.1.2) - G (Fin.cons r.2 r.1.2)) ^ 2) ((κ.prod ρ).prod κ) :=
    (integrable_comp_mp hMPh _ hmeas0.aestronglyMeasurable hE0).congr
      (Filter.Eventually.of_forall hHcongr)
  have hHeq : resampleEnergy μ G 0
      = ∫ r : (ℝ × (Fin M → ℝ)) × ℝ,
          (G (Fin.cons r.1.1 r.1.2) - G (Fin.cons r.2 r.1.2)) ^ 2 ∂((κ.prod ρ).prod κ) := by
    rw [resampleEnergy, integral_comp_mp hMPh _ hmeas0.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall hHcongr)
  have hGc1 := integrable_cons (μ := μ) hGm hG2
  have hGc2 := integrable_cons_sq (μ := μ) hG2
  have haeq : ∀ᵐ q ∂(κ.prod ρ),
      Integrable (fun x => G (Fin.cons x q.2)) κ ∧
        Integrable (fun x => G (Fin.cons x q.2) ^ 2) κ :=
    measurePreserving_snd.quasiMeasurePreserving.ae
      (hGc1.prod_left_ae.and hGc2.prod_left_ae)
  rw [hHeq, integral_prod _ hHtrans]
  refine integral_mono_ae (integrable_headFluct_sq (μ := μ) hGm hG2)
    hHtrans.integral_prod_left ?_
  filter_upwards [haeq] with q hq
  obtain ⟨h1, h2⟩ := hq
  set a : ℝ := G (Fin.cons q.1 q.2) with hadef
  have hh1 : Integrable (fun y => a - G (Fin.cons y q.2)) κ :=
    (integrable_const a).sub h1
  have hh2 : Integrable (fun y => (a - G (Fin.cons y q.2)) ^ 2) κ := by
    refine Integrable.mono' ((integrable_const (2 * a ^ 2)).add (h2.const_mul 2))
      ((((measurable_const.sub (hGm.comp (measurable_cons_pair.comp
        (measurable_id.prodMk measurable_const)))).pow_const 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (a + G (Fin.cons y q.2))]
  have hint : ∫ y, (a - G (Fin.cons y q.2)) ∂κ = a - headAvg μ G q.2 := by
    rw [integral_sub (integrable_const a) h1]
    simp [headAvg, hκdef]
  have hsq := sq_integral_le κ (fun y => a - G (Fin.cons y q.2)) hh1 hh2
  rw [hint] at hsq
  exact hsq

/-- The tail machinery of the induction: the resampling energy of the head
average is controlled by that of `G` in every tail coordinate, and the head
average inherits the integrability. -/
theorem headAvg_resample_aux (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ))
    (hE : ∀ i : Fin (M + 1), Integrable (fun q : (Fin (M + 1) → ℝ) × ℝ =>
      (G q.1 - G (Function.update q.1 i q.2)) ^ 2) ((Measure.pi μ).prod (μ i)))
    (j : Fin M) :
    Integrable (fun w : (Fin M → ℝ) × ℝ =>
        (headAvg μ G w.1 - headAvg μ G (Function.update w.1 j w.2)) ^ 2)
      ((Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))).prod (μ (Fin.succAbove 0 j)))
    ∧ resampleEnergy (fun j : Fin M => μ (Fin.succAbove 0 j)) (headAvg μ G) j
        ≤ resampleEnergy μ G (Fin.succAbove 0 j) := by
  classical
  set κ : Measure ℝ := μ 0 with hκdef
  set ρ : Measure (Fin M → ℝ) := Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)) with hρdef
  have hΦm : Measurable (headAvg μ G) := measurable_headAvg hGm
  have hGc1 := integrable_cons (μ := μ) hGm hG2
  have hslice1 : ∀ᵐ η ∂ρ, Integrable (fun x => G (Fin.cons x η)) κ := hGc1.prod_left_ae
  have hMP : MeasurePreserving
      (fun q : ℝ × (Fin M → ℝ) => (Fin.cons q.1 q.2 : Fin (M + 1) → ℝ))
      (κ.prod ρ) (Measure.pi μ) := measurePreserving_cons μ
  have hMPt : MeasurePreserving
      (fun r : (ℝ × (Fin M → ℝ)) × ℝ => ((Fin.cons r.1.1 r.1.2 : Fin (M + 1) → ℝ), r.2))
      ((κ.prod ρ).prod (μ (Fin.succAbove 0 j))) ((Measure.pi μ).prod (μ (Fin.succAbove 0 j))) :=
    hMP.prod (MeasurePreserving.id (μ (Fin.succAbove 0 j)))
  have hAssoc : MeasurePreserving
      (⇑(MeasurableEquiv.prodAssoc :
        ((ℝ × (Fin M → ℝ)) × ℝ) ≃ᵐ (ℝ × ((Fin M → ℝ) × ℝ))))
      ((κ.prod ρ).prod (μ (Fin.succAbove 0 j))) (κ.prod (ρ.prod (μ (Fin.succAbove 0 j)))) :=
    measurePreserving_prodAssoc κ ρ (μ (Fin.succAbove 0 j))
  have hmeasj : Measurable (fun q : (Fin (M + 1) → ℝ) × ℝ =>
      (G q.1 - G (Function.update q.1 (Fin.succAbove 0 j) q.2)) ^ 2) :=
    (((hGm.comp measurable_fst).sub
      (hGm.comp (measurable_update_pair (Fin.succAbove 0 j)))).pow_const 2)
  have hcongr : ∀ r : (ℝ × (Fin M → ℝ)) × ℝ,
      (G (Fin.cons r.1.1 r.1.2)
          - G (Function.update (Fin.cons r.1.1 r.1.2 : Fin (M + 1) → ℝ)
            (Fin.succAbove 0 j) r.2)) ^ 2
        = (G (Fin.cons r.1.1 r.1.2)
          - G (Fin.cons r.1.1 (Function.update r.1.2 j r.2))) ^ 2 := by
    intro r
    rw [Fin.zero_succAbove, ← cons_update_succ]
  have hmeass : Measurable (fun s : ℝ × ((Fin M → ℝ) × ℝ) =>
      (G (Fin.cons s.1 s.2.1)
        - G (Fin.cons s.1 (Function.update s.2.1 j s.2.2))) ^ 2) := by
    have h1 : Measurable fun s : ℝ × ((Fin M → ℝ) × ℝ) => G (Fin.cons s.1 s.2.1) :=
      hGm.comp (measurable_cons_pair.comp (measurable_fst.prodMk
        (measurable_fst.comp measurable_snd)))
    have h2 : Measurable fun s : ℝ × ((Fin M → ℝ) × ℝ) =>
        G (Fin.cons s.1 (Function.update s.2.1 j s.2.2)) :=
      hGm.comp (measurable_cons_pair.comp (measurable_fst.prodMk
        ((measurable_update_pair j).comp measurable_snd)))
    exact ((h1.sub h2).pow_const 2)
  have htrans := (integrable_comp_mp hMPt _ hmeasj.aestronglyMeasurable
    (hE (Fin.succAbove 0 j))).congr (Filter.Eventually.of_forall hcongr)
  have hkey1 : Integrable (fun s : ℝ × ((Fin M → ℝ) × ℝ) =>
      (G (Fin.cons s.1 s.2.1)
        - G (Fin.cons s.1 (Function.update s.2.1 j s.2.2))) ^ 2)
      (κ.prod (ρ.prod (μ (Fin.succAbove 0 j)))) :=
    integrable_of_comp_mp hAssoc _ hmeass.aestronglyMeasurable htrans
  have hkey2 : resampleEnergy μ G (Fin.succAbove 0 j)
      = ∫ s : ℝ × ((Fin M → ℝ) × ℝ),
          (G (Fin.cons s.1 s.2.1)
            - G (Fin.cons s.1 (Function.update s.2.1 j s.2.2))) ^ 2
          ∂(κ.prod (ρ.prod (μ (Fin.succAbove 0 j)))) := by
    rw [resampleEnergy, integral_comp_mp hMPt _ hmeasj.aestronglyMeasurable,
      integral_congr_ae (Filter.Eventually.of_forall hcongr),
      integral_comp_mp hAssoc _ hmeass.aestronglyMeasurable]
    rfl
  have hswap : Integrable (fun w : (Fin M → ℝ) × ℝ =>
      ∫ x, (G (Fin.cons x w.1)
        - G (Fin.cons x (Function.update w.1 j w.2))) ^ 2 ∂κ) (ρ.prod (μ (Fin.succAbove 0 j))) :=
    (hkey1.swap).integral_prod_left
  have hslicej : ∀ᵐ w ∂(ρ.prod (μ (Fin.succAbove 0 j))),
      Integrable (fun x => (G (Fin.cons x w.1)
        - G (Fin.cons x (Function.update w.1 j w.2))) ^ 2) κ := hkey1.prod_left_ae
  have hTail : ∀ᵐ w ∂(ρ.prod (μ (Fin.succAbove 0 j))),
      Integrable (fun x => G (Fin.cons x w.1)) κ :=
    measurePreserving_fst.quasiMeasurePreserving.ae hslice1
  have hΦcmp : ∀ᵐ w ∂(ρ.prod (μ (Fin.succAbove 0 j))),
      (headAvg μ G w.1 - headAvg μ G (Function.update w.1 j w.2)) ^ 2
        ≤ ∫ x, (G (Fin.cons x w.1)
            - G (Fin.cons x (Function.update w.1 j w.2))) ^ 2 ∂κ := by
    filter_upwards [hTail, hslicej] with w h1 h2
    set h : ℝ → ℝ := fun x => G (Fin.cons x w.1)
      - G (Fin.cons x (Function.update w.1 j w.2)) with hhdef
    have hhm : Measurable h := by
      have e1 : Measurable fun x : ℝ => G (Fin.cons x w.1) :=
        hGm.comp (measurable_cons_pair.comp (measurable_id.prodMk measurable_const))
      have e2 : Measurable fun x : ℝ => G (Fin.cons x (Function.update w.1 j w.2)) :=
        hGm.comp (measurable_cons_pair.comp (measurable_id.prodMk measurable_const))
      exact e1.sub e2
    have hhint : Integrable h κ :=
      integrable_of_integrable_sq κ hhm.aestronglyMeasurable h2
    have hupd : Integrable (fun x => G (Fin.cons x (Function.update w.1 j w.2))) κ :=
      (h1.sub hhint).congr (Filter.Eventually.of_forall fun x => by
        show G (Fin.cons x w.1) - h x = G (Fin.cons x (Function.update w.1 j w.2))
        rw [hhdef]; ring)
    have hrep : ∫ x, h x ∂κ
        = headAvg μ G w.1 - headAvg μ G (Function.update w.1 j w.2) := by
      rw [hhdef, integral_sub h1 hupd]
      simp [headAvg, hκdef]
    have hsq := sq_integral_le κ h hhint h2
    rw [hrep] at hsq
    exact hsq
  have hEΦ : Integrable (fun w : (Fin M → ℝ) × ℝ =>
      (headAvg μ G w.1 - headAvg μ G (Function.update w.1 j w.2)) ^ 2)
      (ρ.prod (μ (Fin.succAbove 0 j))) := by
    refine Integrable.mono' hswap
      ((((hΦm.comp measurable_fst).sub
        (hΦm.comp (measurable_update_pair j))).pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [hΦcmp] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hw
  refine ⟨hEΦ, ?_⟩
  rw [resampleEnergy, hkey2, integral_prod_symm _ hkey1]
  exact integral_mono_ae hEΦ hswap hΦcmp

/-- **The head fluctuation carries exactly half the resampling energy of the
first coordinate.**  This is the identity `E|ζ - ζ'|² = 2 Var(ζ)` applied in the
head coordinate for each value of the tail, and it is what makes the constant of
the Efron-Stein bound `1/2`. -/
theorem two_mul_integral_headFluct_sq (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ))
    (hE0 : Integrable (fun q : (Fin (M + 1) → ℝ) × ℝ =>
      (G q.1 - G (Function.update q.1 0 q.2)) ^ 2) ((Measure.pi μ).prod (μ 0))) :
    2 * ∫ q : ℝ × (Fin M → ℝ), (G (Fin.cons q.1 q.2) - headAvg μ G q.2) ^ 2
        ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))))
      = resampleEnergy μ G 0 := by
  classical
  have hMP : MeasurePreserving
      (fun q : ℝ × (Fin M → ℝ) => (Fin.cons q.1 q.2 : Fin (M + 1) → ℝ))
      ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) (Measure.pi μ) :=
    measurePreserving_cons μ
  have hMPh : MeasurePreserving
      (fun r : (ℝ × (Fin M → ℝ)) × ℝ => ((Fin.cons r.1.1 r.1.2 : Fin (M + 1) → ℝ), r.2))
      (((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))).prod (μ 0))
      ((Measure.pi μ).prod (μ 0)) := hMP.prod (MeasurePreserving.id (μ 0))
  have hmeas0 : Measurable (fun q : (Fin (M + 1) → ℝ) × ℝ =>
      (G q.1 - G (Function.update q.1 0 q.2)) ^ 2) :=
    (((hGm.comp measurable_fst).sub (hGm.comp (measurable_update_pair 0))).pow_const 2)
  have hHcongr : ∀ r : (ℝ × (Fin M → ℝ)) × ℝ,
      (G (Fin.cons r.1.1 r.1.2)
          - G (Function.update (Fin.cons r.1.1 r.1.2 : Fin (M + 1) → ℝ) 0 r.2)) ^ 2
        = (G (Fin.cons r.1.1 r.1.2) - G (Fin.cons r.2 r.1.2)) ^ 2 := by
    intro r
    rw [cons_update_zero]
  have hHtrans : Integrable (fun r : (ℝ × (Fin M → ℝ)) × ℝ =>
      (G (Fin.cons r.1.1 r.1.2) - G (Fin.cons r.2 r.1.2)) ^ 2)
      (((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))).prod (μ 0)) :=
    (integrable_comp_mp hMPh _ hmeas0.aestronglyMeasurable hE0).congr
      (Filter.Eventually.of_forall hHcongr)
  have hHeq : resampleEnergy μ G 0
      = ∫ r : (ℝ × (Fin M → ℝ)) × ℝ,
          (G (Fin.cons r.1.1 r.1.2) - G (Fin.cons r.2 r.1.2)) ^ 2
          ∂(((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))).prod (μ 0)) := by
    rw [resampleEnergy, integral_comp_mp hMPh _ hmeas0.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall hHcongr)
  have hGc1 := integrable_cons (μ := μ) hGm hG2
  have hGc2 := integrable_cons_sq (μ := μ) hG2
  rw [hHeq, integral_prod _ hHtrans,
    integral_prod_symm _ hHtrans.integral_prod_left,
    integral_prod_symm _ (integrable_headFluct_sq (μ := μ) hGm hG2),
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hGc1.prod_left_ae, hGc2.prod_left_ae] with η h1 h2
  exact (integral_pair_sq (μ 0) (fun x => G (Fin.cons x η)) h1 h2).symm

/-- The head average inherits the resampling integrability of `G`. -/
theorem integrable_headAvg_resample (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ))
    (hE : ∀ i : Fin (M + 1), Integrable (fun q : (Fin (M + 1) → ℝ) × ℝ =>
      (G q.1 - G (Function.update q.1 i q.2)) ^ 2) ((Measure.pi μ).prod (μ i)))
    (j : Fin M) :
    Integrable (fun w : (Fin M → ℝ) × ℝ =>
        (headAvg μ G w.1 - headAvg μ G (Function.update w.1 j w.2)) ^ 2)
      ((Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))).prod (μ (Fin.succAbove 0 j))) :=
  (headAvg_resample_aux hGm hG2 hE j).1

/-- The resampling energy of the head average is at most that of `G`. -/
theorem resampleEnergy_headAvg_le (hGm : Measurable G)
    (hG2 : Integrable (fun ξ => G ξ ^ 2) (Measure.pi μ))
    (hE : ∀ i : Fin (M + 1), Integrable (fun q : (Fin (M + 1) → ℝ) × ℝ =>
      (G q.1 - G (Function.update q.1 i q.2)) ^ 2) ((Measure.pi μ).prod (μ i)))
    (j : Fin M) :
    resampleEnergy (fun j : Fin M => μ (Fin.succAbove 0 j)) (headAvg μ G) j ≤ resampleEnergy μ G (Fin.succAbove 0 j) :=
  (headAvg_resample_aux hGm hG2 hE j).2

end Head


/-! ### The covariance bound -/

theorem sqrt_half_mul_sqrt_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a / 2) * Real.sqrt (b / 2) = Real.sqrt a * Real.sqrt b / 2 := by
  rw [show a / 2 = a * (1 / 2) by ring, show b / 2 = b * (1 / 2) by ring,
    Real.sqrt_mul ha, Real.sqrt_mul hb]
  have h2 : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 :=
    Real.mul_self_sqrt (by norm_num)
  linear_combination (Real.sqrt a * Real.sqrt b) * h2


/-- **The covariance form of the Efron-Stein inequality.**  The covariance of
two square-integrable functions of independent coordinates is at most the
PAIRING of their two vectors of resampling energies, with constant one.  For
coordinate-Lipschitz functions with constants `a_i` and `b_i` this is
`|Cov(f, g)| ≤ ∑ a_i b_i E|ζ_i - ζ_i'|²`, which is the bound the paper's
`Cov(u_n(x), u_m(y)) ≤ 2 Var(ζ) ∑_z g_n(x, z) g_m(y, z)` needs: Cauchy-Schwarz
on the two variances would give the product of the norms instead of the
pairing. -/
theorem efron_stein_cov :
    ∀ (M : ℕ) (μ : Fin M → Measure ℝ), (∀ i, IsProbabilityMeasure (μ i)) →
      ∀ f g : (Fin M → ℝ) → ℝ, Measurable f → Measurable g →
        Integrable (fun ξ => f ξ ^ 2) (Measure.pi μ) →
        Integrable (fun ξ => g ξ ^ 2) (Measure.pi μ) →
        (∀ i, Integrable (fun q : (Fin M → ℝ) × ℝ =>
          (f q.1 - f (Function.update q.1 i q.2)) ^ 2) ((Measure.pi μ).prod (μ i))) →
        (∀ i, Integrable (fun q : (Fin M → ℝ) × ℝ =>
          (g q.1 - g (Function.update q.1 i q.2)) ^ 2) ((Measure.pi μ).prod (μ i))) →
        |∫ ξ, (f ξ - ∫ η, f η ∂(Measure.pi μ)) * (g ξ - ∫ η, g η ∂(Measure.pi μ))
            ∂(Measure.pi μ)|
          ≤ (1 / 2) * ∑ i, Real.sqrt (resampleEnergy μ f i)
              * Real.sqrt (resampleEnergy μ g i) := by
  intro M
  induction M with
  | zero =>
      intro μ hμ f g hfm hgm hf2 hg2 hEf hEg
      haveI := hμ
      have hsubf : ∀ ξ : Fin 0 → ℝ, f ξ = f 0 := fun ξ => congrArg f (Subsingleton.elim _ _)
      have hsubg : ∀ ξ : Fin 0 → ℝ, g ξ = g 0 := fun ξ => congrArg g (Subsingleton.elim _ _)
      have hmf : ∫ η, f η ∂(Measure.pi μ) = f 0 := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hsubf)]; simp
      have hmg : ∫ η, g η ∂(Measure.pi μ) = g 0 := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hsubg)]; simp
      have hz : ∀ ξ : Fin 0 → ℝ,
          (f ξ - ∫ η, f η ∂(Measure.pi μ)) * (g ξ - ∫ η, g η ∂(Measure.pi μ)) = 0 := by
        intro ξ
        rw [hmf, hmg, hsubf ξ, hsubg ξ, sub_self]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hz)]
      simp
  | succ M ih =>
      intro μ hμ f g hfm hgm hf2 hg2 hEf hEg
      classical
      haveI := hμ
      haveI hκp : IsProbabilityMeasure (μ 0) := hμ 0
      haveI hρp : IsProbabilityMeasure (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) := by infer_instance
      set mf : ℝ := ∫ ξ, f ξ ∂(Measure.pi μ) with hmfdef
      set mg : ℝ := ∫ ξ, g ξ ∂(Measure.pi μ) with hmgdef
      have hΦfm : Measurable (headAvg μ f) := measurable_headAvg hfm
      have hΦgm : Measurable (headAvg μ g) := measurable_headAvg hgm
      have hΦf2 : Integrable (fun η => headAvg μ f η ^ 2) (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) :=
        integrable_headAvg_sq hfm hf2
      have hΦg2 : Integrable (fun η => headAvg μ g η ^ 2) (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) :=
        integrable_headAvg_sq hgm hg2
      have hmfeq : ∫ η, headAvg μ f η ∂(Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) = mf :=
        integral_headAvg hfm hf2
      have hmgeq : ∫ η, headAvg μ g η ∂(Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) = mg :=
        integral_headAvg hgm hg2
      have hXfm : Measurable (fun η => headAvg μ f η - mf) := hΦfm.sub measurable_const
      have hXgm : Measurable (fun η => headAvg μ g η - mg) := hΦgm.sub measurable_const
      have hYfm : Measurable
          (fun q : ℝ × (Fin M → ℝ) => f (Fin.cons q.1 q.2) - headAvg μ f q.2) :=
        (hfm.comp measurable_cons_pair).sub (hΦfm.comp measurable_snd)
      have hYgm : Measurable
          (fun q : ℝ × (Fin M → ℝ) => g (Fin.cons q.1 q.2) - headAvg μ g q.2) :=
        (hgm.comp measurable_cons_pair).sub (hΦgm.comp measurable_snd)
      have hXf2 : Integrable (fun η => (headAvg μ f η - mf) ^ 2)
          (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) := integrable_sub_const_sq hΦfm hΦf2 mf
      have hXg2 : Integrable (fun η => (headAvg μ g η - mg) ^ 2)
          (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) := integrable_sub_const_sq hΦgm hΦg2 mg
      have hYf2 := integrable_headFluct_sq (μ := μ) hfm hf2
      have hYg2 := integrable_headFluct_sq (μ := μ) hgm hg2
      have hXf2' : Integrable (fun q : ℝ × (Fin M → ℝ) => (headAvg μ f q.2 - mf) ^ 2)
          ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) := hXf2.comp_snd (μ 0)
      have hXg2' : Integrable (fun q : ℝ × (Fin M → ℝ) => (headAvg μ g q.2 - mg) ^ 2)
          ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) := hXg2.comp_snd (μ 0)
      have i1 : Integrable (fun q : ℝ × (Fin M → ℝ) =>
          (headAvg μ f q.2 - mf) * (headAvg μ g q.2 - mg))
          ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) :=
        integrable_mul_of_sq ((hXfm.comp measurable_snd).aestronglyMeasurable)
          ((hXgm.comp measurable_snd).aestronglyMeasurable) hXf2' hXg2'
      have i2 : Integrable (fun q : ℝ × (Fin M → ℝ) =>
          (headAvg μ f q.2 - mf) * (g (Fin.cons q.1 q.2) - headAvg μ g q.2))
          ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) :=
        integrable_mul_of_sq ((hXfm.comp measurable_snd).aestronglyMeasurable)
          hYgm.aestronglyMeasurable hXf2' hYg2
      have i3 : Integrable (fun q : ℝ × (Fin M → ℝ) =>
          (f (Fin.cons q.1 q.2) - headAvg μ f q.2) * (headAvg μ g q.2 - mg))
          ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) :=
        integrable_mul_of_sq hYfm.aestronglyMeasurable
          ((hXgm.comp measurable_snd).aestronglyMeasurable) hYf2 hXg2'
      have i4 : Integrable (fun q : ℝ × (Fin M → ℝ) =>
          (f (Fin.cons q.1 q.2) - headAvg μ f q.2) * (g (Fin.cons q.1 q.2) - headAvg μ g q.2))
          ((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) :=
        integrable_mul_of_sq hYfm.aestronglyMeasurable hYgm.aestronglyMeasurable hYf2 hYg2
      -- the covariance splits into four terms, two of which vanish by Fubini
      have hsplit : ∫ ξ, (f ξ - mf) * (g ξ - mg) ∂(Measure.pi μ)
          = (∫ q : ℝ × (Fin M → ℝ),
                (headAvg μ f q.2 - mf) * (headAvg μ g q.2 - mg)
                ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))))
            + (∫ q : ℝ × (Fin M → ℝ),
                (headAvg μ f q.2 - mf) * (g (Fin.cons q.1 q.2) - headAvg μ g q.2)
                ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))))
            + (∫ q : ℝ × (Fin M → ℝ),
                (f (Fin.cons q.1 q.2) - headAvg μ f q.2) * (headAvg μ g q.2 - mg)
                ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))))
            + (∫ q : ℝ × (Fin M → ℝ),
                (f (Fin.cons q.1 q.2) - headAvg μ f q.2)
                  * (g (Fin.cons q.1 q.2) - headAvg μ g q.2)
                ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))))) := by
        rw [integral_prod_cons_fam μ (fun ξ => (f ξ - mf) * (g ξ - mg))]
        have hpt : ∀ q : ℝ × (Fin M → ℝ),
            (f (Fin.cons q.1 q.2) - mf) * (g (Fin.cons q.1 q.2) - mg)
              = (headAvg μ f q.2 - mf) * (headAvg μ g q.2 - mg)
                + (headAvg μ f q.2 - mf) * (g (Fin.cons q.1 q.2) - headAvg μ g q.2)
                + (f (Fin.cons q.1 q.2) - headAvg μ f q.2) * (headAvg μ g q.2 - mg)
                + (f (Fin.cons q.1 q.2) - headAvg μ f q.2)
                  * (g (Fin.cons q.1 q.2) - headAvg μ g q.2) := fun q => by ring
        have i12 : Integrable (fun q : ℝ × (Fin M → ℝ) =>
            (headAvg μ f q.2 - mf) * (headAvg μ g q.2 - mg)
              + (headAvg μ f q.2 - mf) * (g (Fin.cons q.1 q.2) - headAvg μ g q.2))
            ((μ 0).prod (Measure.pi fun j : Fin M => μ (Fin.succAbove 0 j))) := i1.add i2
        have i123 : Integrable (fun q : ℝ × (Fin M → ℝ) =>
            (headAvg μ f q.2 - mf) * (headAvg μ g q.2 - mg)
              + (headAvg μ f q.2 - mf) * (g (Fin.cons q.1 q.2) - headAvg μ g q.2)
              + (f (Fin.cons q.1 q.2) - headAvg μ f q.2) * (headAvg μ g q.2 - mg))
            ((μ 0).prod (Measure.pi fun j : Fin M => μ (Fin.succAbove 0 j))) := i12.add i3
        rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      have hP2 : ∫ q : ℝ × (Fin M → ℝ),
          (headAvg μ f q.2 - mf) * (g (Fin.cons q.1 q.2) - headAvg μ g q.2)
          ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) = 0 := by
        rw [integral_prod_symm _ i2]
        have hz : ∀ η : Fin M → ℝ,
            ∫ x, (headAvg μ f η - mf) * (g (Fin.cons x η) - headAvg μ g η) ∂(μ 0) = 0 := by
          intro η
          rw [integral_const_mul, headAvg_fluct_integral_zero (μ := μ) η, mul_zero]
        rw [integral_congr_ae (Filter.Eventually.of_forall hz)]
        simp
      have hP3 : ∫ q : ℝ × (Fin M → ℝ),
          (f (Fin.cons q.1 q.2) - headAvg μ f q.2) * (headAvg μ g q.2 - mg)
          ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))) = 0 := by
        rw [integral_prod_symm _ i3]
        have hz : ∀ η : Fin M → ℝ,
            ∫ x, (f (Fin.cons x η) - headAvg μ f η) * (headAvg μ g η - mg) ∂(μ 0) = 0 := by
          intro η
          rw [integral_mul_const, headAvg_fluct_integral_zero (μ := μ) η, zero_mul]
        rw [integral_congr_ae (Filter.Eventually.of_forall hz)]
        simp
      have hP1 : ∫ q : ℝ × (Fin M → ℝ),
          (headAvg μ f q.2 - mf) * (headAvg μ g q.2 - mg)
          ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))))
          = ∫ η, (headAvg μ f η - mf) * (headAvg μ g η - mg)
              ∂(Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))) := by
        rw [integral_prod_symm _ i1]
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        simp
      -- the inductive hypothesis for the two head averages
      have hIH := ih (fun j : Fin M => μ (Fin.succAbove 0 j)) (fun j => hμ _) (headAvg μ f) (headAvg μ g) hΦfm hΦgm
        hΦf2 hΦg2 (fun j => integrable_headAvg_resample hfm hf2 hEf j)
        (fun j => integrable_headAvg_resample hgm hg2 hEg j)
      rw [hmfeq, hmgeq] at hIH
      have hP1le : |∫ η, (headAvg μ f η - mf) * (headAvg μ g η - mg)
            ∂(Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))|
          ≤ (1 / 2) * ∑ j : Fin M, Real.sqrt (resampleEnergy μ f (Fin.succAbove 0 j))
              * Real.sqrt (resampleEnergy μ g (Fin.succAbove 0 j)) := by
        refine le_trans hIH ?_
        have hsum : ∑ j : Fin M,
              Real.sqrt (resampleEnergy (fun j : Fin M => μ (Fin.succAbove 0 j))
                  (headAvg μ f) j)
                * Real.sqrt (resampleEnergy (fun j : Fin M => μ (Fin.succAbove 0 j))
                  (headAvg μ g) j)
            ≤ ∑ j : Fin M, Real.sqrt (resampleEnergy μ f (Fin.succAbove 0 j))
                * Real.sqrt (resampleEnergy μ g (Fin.succAbove 0 j)) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul (Real.sqrt_le_sqrt (resampleEnergy_headAvg_le hfm hf2 hEf j))
              (Real.sqrt_le_sqrt (resampleEnergy_headAvg_le hgm hg2 hEg j))
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        linarith
      have hP4le : |∫ q : ℝ × (Fin M → ℝ),
            (f (Fin.cons q.1 q.2) - headAvg μ f q.2)
              * (g (Fin.cons q.1 q.2) - headAvg μ g q.2)
            ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))))|
          ≤ (1 / 2) * (Real.sqrt (resampleEnergy μ f 0)
              * Real.sqrt (resampleEnergy μ g 0)) := by
        have hfe := two_mul_integral_headFluct_sq (μ := μ) hfm hf2 (hEf 0)
        have hge := two_mul_integral_headFluct_sq (μ := μ) hgm hg2 (hEg 0)
        have hfhalf : ∫ q : ℝ × (Fin M → ℝ),
            (f (Fin.cons q.1 q.2) - headAvg μ f q.2) ^ 2
            ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))))
              = resampleEnergy μ f 0 / 2 := by linarith
        have hghalf : ∫ q : ℝ × (Fin M → ℝ),
            (g (Fin.cons q.1 q.2) - headAvg μ g q.2) ^ 2
            ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))))
              = resampleEnergy μ g 0 / 2 := by linarith
        refine le_trans (abs_integral_mul_le hYfm.aestronglyMeasurable
          hYgm.aestronglyMeasurable hYf2 hYg2) ?_
        rw [hfhalf, hghalf,
          sqrt_half_mul_sqrt_half (resampleEnergy_nonneg μ f 0) (resampleEnergy_nonneg μ g 0)]
        ring_nf
        exact le_rfl
      rw [Fin.sum_univ_succAbove (fun i : Fin (M + 1) =>
        Real.sqrt (resampleEnergy μ f i) * Real.sqrt (resampleEnergy μ g i)) 0]
      rw [hsplit, hP2, hP3, hP1]
      have hcollapse : ∀ a b : ℝ, a + 0 + 0 + b = a + b := by intro a b; ring
      rw [hcollapse]
      have habs := abs_add_le
        (∫ η, (headAvg μ f η - mf) * (headAvg μ g η - mg)
          ∂(Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j))))
        (∫ q : ℝ × (Fin M → ℝ),
          (f (Fin.cons q.1 q.2) - headAvg μ f q.2)
            * (g (Fin.cons q.1 q.2) - headAvg μ g q.2)
          ∂((μ 0).prod (Measure.pi (fun j : Fin M => μ (Fin.succAbove 0 j)))))
      linarith [hP1le, hP4le, habs]

/-- **The Efron-Stein inequality with the sharp constant.**  The variance of a
square-integrable function of independent coordinates is at most half the total
resampling energy.  It is the covariance bound at `f = g`, where the two square
roots multiply back to the energy. -/
theorem efron_stein_var (M : ℕ) (μ : Fin M → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) (F : (Fin M → ℝ) → ℝ) (hFm : Measurable F)
    (hF2 : Integrable (fun ξ => F ξ ^ 2) (Measure.pi μ))
    (hE : ∀ i, Integrable (fun q : (Fin M → ℝ) × ℝ =>
      (F q.1 - F (Function.update q.1 i q.2)) ^ 2) ((Measure.pi μ).prod (μ i))) :
    ∫ ξ, (F ξ - ∫ η, F η ∂(Measure.pi μ)) ^ 2 ∂(Measure.pi μ)
      ≤ (1 / 2) * ∑ i, resampleEnergy μ F i := by
  have h := efron_stein_cov M μ hμ F F hFm hFm hF2 hF2 hE hE
  have hsq : ∀ i : Fin M,
      Real.sqrt (resampleEnergy μ F i) * Real.sqrt (resampleEnergy μ F i)
        = resampleEnergy μ F i :=
    fun i => Real.mul_self_sqrt (resampleEnergy_nonneg μ F i)
  rw [Finset.sum_congr rfl fun i _ => hsq i] at h
  have hpt : ∀ ξ : Fin M → ℝ,
      (F ξ - ∫ η, F η ∂(Measure.pi μ)) * (F ξ - ∫ η, F η ∂(Measure.pi μ))
        = (F ξ - ∫ η, F η ∂(Measure.pi μ)) ^ 2 := fun ξ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at h
  exact le_trans (le_abs_self _) h

end LatticeProb

end
