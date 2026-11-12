/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcL2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcL1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcI0

/-!
# D124 packet I3, part 2: DZZ's good set `𝒜` from `𝓔*` (P2-DZZI3)

Decision D124 (`decisions/DEC-124.md` §1, §5 I3). Source: DZZ (arXiv:1807.00422,
`LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1579–1594:
"there exists a set `𝒜 ⊆ 𝒜_δ` such that `P(𝓔* | 𝐗_δ) ≥ 0.9` on the event `𝒳_δ ∈ 𝒜`, which occurs
with high probability. In particular, for `𝐱_δ, 𝐱'_δ ∈ 𝒜`, `𝓔*_{𝐱_δ} ∩ 𝓔*_{𝐱'_δ}` is non-empty"
(l. 1579–1582), then Lemma 3.8 (l. 1584–1587, `ae_sandwich_wnMix`, S3ConcL1) and the chain of
l. 1588–1594 give (eq-distance-Lip).

DZZ's conditional probability given `𝐗_δ` is the Fubini slice over the fine sample `ω₂` of the
mixing white noise (DEC-124 §1, DV-D124 2): with `M = toMeasurable (P ⊗ P) 𝓔*ᶜ`,
`∫ P(M_{ω₁}) dP(ω₁) = (P ⊗ P)(𝓔*ᶜ)` (`Measure.prod_apply`) and Markov's inequality
(`mul_meas_ge_le_lintegral₀`) give `P{ω₁ : P(M_{ω₁}) > 1/10} ≤ 10 (P ⊗ P)(𝓔*ᶜ)`. No conditional
expectation and no measurability of `𝓔*` are used.

* `coreOn_of_eStar`: the abstract core, for any cell family `S` and any family of measures `μ'`
  on the mixed samples satisfying the sandwich;
* **`dzzGoodCore_of_eStar`**: `DZZGoodCore` (S3ConcH) at `μIn`;
* **`goodCoreOn_of_eStar`**: the walled form (`D'_S`, `dzzWall K (dzzMuIn ·)`), for
  `DZZConcApproxOn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `log ∘ toNat` is monotone on finite values. -/
lemma log_toNat_mono {a b : ℕ∞} (h : a ≤ b) (hb : b ≠ ⊤) :
    Real.log (a.toNat : ℝ) ≤ Real.log (b.toNat : ℝ) := by
  have hab := ENat.toNat_le_toNat h hb
  rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hab)

/-- **Fubini + Markov** (DZZ l. 1579–1580): the coarse samples whose fine slice of `toMeasurable E`
has measure `> 1/10` have probability `≤ 10 (P ⊗ P)(E)`. -/
lemma measure_slice_gt_le [IsProbabilityMeasure P] (E : Set (Ω × Ω)) :
    P {ω₁ | ENNReal.ofReal (1 / 10) < P (Prod.mk ω₁ ⁻¹' toMeasurable (P.prod P) E)} ≤
      ENNReal.ofReal 10 * (P.prod P) E := by
  set M := toMeasurable (P.prod P) E
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hf : Measurable fun ω₁ => P (Prod.mk ω₁ ⁻¹' M) := measurable_measure_prodMk_left hM
  have hint : ∫⁻ ω₁, P (Prod.mk ω₁ ⁻¹' M) ∂P = (P.prod P) E := by
    rw [← Measure.prod_apply hM, measure_toMeasurable]
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hf.aemeasurable (ENNReal.ofReal (1 / 10))
  rw [hint] at hmk
  have h10 : ENNReal.ofReal 10 * ENNReal.ofReal (1 / 10) = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc P {ω₁ | ENNReal.ofReal (1 / 10) < P (Prod.mk ω₁ ⁻¹' M)}
      ≤ P {ω₁ | ENNReal.ofReal (1 / 10) ≤ P (Prod.mk ω₁ ⁻¹' M)} :=
        measure_mono fun ω h => by simp only [mem_setOf_eq] at h ⊢; exact h.le
    _ = ENNReal.ofReal 10 * (ENNReal.ofReal (1 / 10) *
          P {ω₁ | ENNReal.ofReal (1 / 10) ≤ P (Prod.mk ω₁ ⁻¹' M)}) := by
        rw [← mul_assoc, h10, one_mul]
    _ ≤ _ := by gcongr

/-- Two sets of measure `≤ 1/10` and a full-measure property leave a common point (DZZ l. 1582:
`𝓔*_{𝐱_δ} ∩ 𝓔*_{𝐱'_δ} ≠ ∅`). -/
lemma exists_common_fine [IsProbabilityMeasure P] {T T' : Set Ω} {q : Ω → Prop}
    (hT : P T ≤ ENNReal.ofReal (1 / 10)) (hT' : P T' ≤ ENNReal.ofReal (1 / 10))
    (hq : ∀ᵐ ω ∂P, q ω) : ∃ ω, ω ∉ T ∧ ω ∉ T' ∧ q ω := by
  by_contra hne
  push Not at hne
  have hsub : (univ : Set Ω) ⊆ T ∪ T' ∪ {ω | ¬ q ω} := fun ω _ => by
    by_cases h1 : ω ∈ T
    · exact Or.inl (Or.inl h1)
    by_cases h2 : ω ∈ T'
    · exact Or.inl (Or.inr h2)
    exact Or.inr (hne ω h1 h2)
  have h0 : P {ω | ¬ q ω} = 0 := ae_iff.1 hq
  have h := ((measure_mono (μ := P) hsub).trans (measure_union_le _ _)).trans
    (add_le_add (measure_union_le T T') le_rfl)
  rw [measure_univ, h0, add_zero] at h
  have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 10 + 1 / 10) := by
    rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]; exact h.trans (add_le_add hT hT')
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
  norm_num at h2

/-- **The core of DZZ l. 1579–1594** (abstract form): from the sandwich of Lemma 3.8 on the mixed
samples (for a measure family `μ'`), `P(𝒳_δ ∉ 𝒜_δ) ≤ ε₁` and `(P ⊗ P)(𝓔*ᶜ) ≤ ε₂`, DZZ's set
`𝒜 ⊆ 𝒜_δ` with `P(𝒳_δ ∉ 𝒜) ≤ ε₁ + 10 ε₂` and (eq-distance-Lip) with constant `2τ`. -/
theorem coreOn_of_eStar (hW : IsWhiteNoise P W) (S : Set DyBox) {γ κ δ r τ ℓ ε₁ ε₂ : ℝ}
    (hδ : 0 < δ) (hγ : 0 ≤ γ) (hℓ : 0 ≤ ℓ) (hr : γ * ℓ / 2 ≤ r) {A B : Set ℂ}
    (μ' : Ω × Ω → Measure ℂ)
    (hsand : ∃ G₁ : Set Ω, P G₁ᶜ = 0 ∧ ∀ ω₁ ∈ G₁, ∀ ω₁' ∈ G₁,
      (∀ q : CoarsePt κ δ,
        |coarseField W κ δ (Sum.inr q) ω₁ - coarseField W κ δ (Sum.inr q) ω₁'| ≤ ℓ) →
      ∀ᵐ ω₂ ∂P, lgdMinSet (μ' (ω₁, ω₂)) (δ * Real.exp (γ * ℓ / 2)) A B ≤
          lgdMinSet (μ' (ω₁', ω₂)) δ A B ∧
        lgdMinSet (μ' (ω₁', ω₂)) δ A B ≤
          lgdMinSet (μ' (ω₁, ω₂)) (δ * Real.exp (-(γ * ℓ / 2))) A B)
    (hgood : P.real {ω | (fun s => coarseField W κ δ s ω) ∉ CoarseGood γ κ δ} ≤ ε₁)
    (hE : (P.prod P).real (eStarEvent S γ (wnMix W κ δ) μ' δ r τ A B)ᶜ ≤ ε₂) :
    ∃ 𝒜 : Set (CoarseIdx κ δ → ℝ), 𝒜 ⊆ CoarseGood γ κ δ ∧
      P.real {ω | (fun s => coarseField W κ δ s ω) ∉ 𝒜} ≤ ε₁ + 10 * ε₂ ∧
      ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) →
        |coarseLogDOn S γ κ δ A B x - coarseLogDOn S γ κ δ A B x'| ≤ 2 * τ := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨G₁, hG₁, hs⟩ := hsand
  set E := eStarEvent S γ (wnMix W κ δ) μ' δ r τ A B
  set M := toMeasurable (P.prod P) Eᶜ
  set X : Ω → CoarseIdx κ δ → ℝ := fun ω s => coarseField W κ δ s ω with hXdef
  set G₃ := {ω₁ | P (Prod.mk ω₁ ⁻¹' M) ≤ ENNReal.ofReal (1 / 10)}
  set G := G₁ ∩ {ω | X ω ∈ CoarseGood γ κ δ} ∩ G₃
  refine ⟨X '' G, ?_, ?_, ?_⟩
  · rintro _ ⟨ω, hω, rfl⟩; exact hω.1.2
  · have hsub : {ω | X ω ∉ X '' G} ⊆ (G₁ᶜ ∪ {ω | X ω ∉ CoarseGood γ κ δ}) ∪ G₃ᶜ := by
      intro ω hω
      by_contra h
      simp only [mem_union, mem_compl_iff, mem_setOf_eq, not_or, not_not] at h
      exact hω ⟨ω, ⟨⟨h.1.1, h.1.2⟩, h.2⟩, rfl⟩
    have h3 : P.real G₃ᶜ ≤ 10 * ε₂ := by
      have hm := measure_slice_gt_le (P := P) Eᶜ
      have e : G₃ᶜ = {ω₁ | ENNReal.ofReal (1 / 10) < P (Prod.mk ω₁ ⁻¹' M)} := by
        ext ω; simp only [G₃, mem_compl_iff, mem_setOf_eq, not_le]
      rw [measureReal_def, e]
      calc _ ≤ (ENNReal.ofReal 10 * (P.prod P) Eᶜ).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hm
        _ = 10 * (P.prod P).real Eᶜ := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), measureReal_def]
        _ ≤ 10 * ε₂ := by linarith
    have h1 : P.real G₁ᶜ = 0 := by rw [measureReal_def, hG₁, ENNReal.toReal_zero]
    calc _ ≤ P.real ((G₁ᶜ ∪ {ω | X ω ∉ CoarseGood γ κ δ}) ∪ G₃ᶜ) := measureReal_mono hsub
      _ ≤ P.real (G₁ᶜ ∪ {ω | X ω ∉ CoarseGood γ κ δ}) + P.real G₃ᶜ := measureReal_union_le _ _
      _ ≤ (P.real G₁ᶜ + P.real {ω | X ω ∉ CoarseGood γ κ δ}) + P.real G₃ᶜ := by
          gcongr; exact measureReal_union_le _ _
      _ ≤ ε₁ + 10 * ε₂ := by rw [h1]; linarith
  · rintro _ ⟨ω₁, ⟨⟨hg1, hcg⟩, hg3⟩, rfl⟩ _ ⟨ω₁', ⟨⟨hg1', hcg'⟩, hg3'⟩, rfl⟩ hxx
    have hsw := hs ω₁ hg1 ω₁' hg1' fun q => hxx (Sum.inr q)
    obtain ⟨ω₂, hn1, hn2, ⟨hsw1, hsw2⟩, hcf⟩ :=
      exists_common_fine hg3 hg3' (hsw.and (coarseField_wnMix hW hδ))
    have hm1 : (ω₁, ω₂) ∈ E := by
      by_contra h; exact hn1 (subset_toMeasurable _ _ h)
    have hm2 : (ω₁', ω₂) ∈ E := by
      by_contra h; exact hn2 (subset_toMeasurable _ _ h)
    -- `D'` is read off the coarse field (DZZ l. 1567)
    have hX : ∀ ω, (fun s => coarseField (wnMix W κ δ) κ δ s (ω, ω₂)) = X ω :=
      fun ω => funext fun s => hcf ω s
    have hL1 : logApproxLGDOn S γ (wnMix W κ δ) δ A B (ω₁, ω₂) =
        coarseLogDOn S γ κ δ A B (X ω₁) := by
      rw [logApproxLGDOn_eq_coarseLogDOn S hδ.ne' _ A B _ (by rw [hX]; exact hcg), hX]
    have hL2 : logApproxLGDOn S γ (wnMix W κ δ) δ A B (ω₁', ω₂) =
        coarseLogDOn S γ κ δ A B (X ω₁') := by
      rw [logApproxLGDOn_eq_coarseLogDOn S hδ.ne' _ A B _ (by rw [hX]; exact hcg'), hX]
    -- the window `[δe^{−r}, δe^{r}]` contains `δ`, `δe^{±γℓ/2}`
    have hr0 : 0 ≤ r := le_trans (by positivity) hr
    have hwin : ∀ t, |t| ≤ r → δ * Real.exp t ∈ Icc (δ * Real.exp (-r)) (δ * Real.exp r) :=
      fun t ht => ⟨by gcongr; linarith [(abs_le.1 ht).1], by gcongr; exact (abs_le.1 ht).2⟩
    have hg : |γ * ℓ / 2| ≤ r := by rw [abs_of_nonneg (by positivity)]; exact hr
    have hg' : |-(γ * ℓ / 2)| ≤ r := by rw [abs_neg]; exact hg
    have h0 : δ ∈ Icc (δ * Real.exp (-r)) (δ * Real.exp r) := by
      have := hwin 0 (by rw [abs_zero]; exact hr0)
      rwa [Real.exp_zero, mul_one] at this
    obtain ⟨-, -, e1⟩ := hm1
    obtain ⟨-, -, e2⟩ := hm2
    obtain ⟨-, l1⟩ := e1 _ (hwin _ hg)
    obtain ⟨f1', l1'⟩ := e1 _ (hwin _ hg')
    obtain ⟨f2, l2⟩ := e2 δ h0
    have m1 := log_toNat_mono hsw1 f2
    have m2 := log_toNat_mono hsw2 f1'
    rw [hL1] at l1 l1'
    rw [hL2] at l2
    unfold logMinLGD at l1 l1' l2
    have a1 := abs_le.1 l1
    have a1' := abs_le.1 l1'
    have a2 := abs_le.1 l2
    rw [abs_le]
    constructor <;> linarith

lemma dzzWall_univ' (μ : Measure ℂ) : dzzWall univ μ = μ := by simp [dzzWall]

lemma l3_approxDistOn_univ (m : DyBox → ℝ) (δ : ℝ) (u v : ℂ) :
    approxDistOn univ m δ u v = approxDist m δ u v := by
  have : cellGraphOn univ m δ = cellGraph m δ := by ext b b'; simp [cellGraphOn]
  simp [approxDistOn, approxDist, this]

lemma coarseLogDOn_univ (γ κ δ : ℝ) (A B : Set ℂ) (x : CoarseIdx κ δ → ℝ) :
    coarseLogDOn univ γ κ δ A B x = coarseLogD γ κ δ A B x := by
  simp only [coarseLogDOn, coarseLogD, approxDistSetOn, approxDistSet, l3_approxDistOn_univ]

/-- **DZZ l. 1579–1594 at `μIn`**: `DZZGoodCore` from `P(𝒳_δ ∉ 𝒜_δ) ≤ ε₁` and
`(P ⊗ P)(𝓔*ᶜ) ≤ ε₂` for the mixing white noise, when `γℓ/2 ≤ r`. -/
theorem dzzGoodCore_of_eStar (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {δ : ℝ} (hδ : 0 < δ) {r τ ℓ ε₁ ε₂ : ℝ} (hℓ : 0 ≤ ℓ) (hr : γ * ℓ / 2 ≤ r) {A B : Set ℂ}
    (hgood : P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉
      CoarseGood γ (dzzCmc γ) δ} ≤ ε₁)
    (hE : (P.prod P).real (eStarEvent univ γ (wnMix W (dzzCmc γ) δ)
      (dzzMuIn γ (wnMix W (dzzCmc γ) δ)) δ r τ A B)ᶜ ≤ ε₂) :
    DZZGoodCore P γ W δ A B ℓ (2 * τ) (ε₁ + 10 * ε₂) := by
  obtain ⟨G₁, hG₁, hs⟩ := ae_sandwich_wnMix hW hγ hγ2 (κ := dzzCmc γ) hδ
  obtain ⟨𝒜, h1, h2, h3⟩ := coreOn_of_eStar hW univ hδ hγ.le hℓ hr
    (dzzMuIn γ (wnMix W (dzzCmc γ) δ))
    ⟨G₁, hG₁, fun ω₁ h ω₁' h' hq => (hs ω₁ h ω₁' h' ℓ hℓ hq).mono fun ω₂ H => by
      have e := H univ δ A B
      rw [dzzWall_univ', dzzWall_univ'] at e
      exact e⟩ hgood hE
  refine ⟨𝒜, h1, h2, fun x hx x' hx' hxx => ?_⟩
  rw [← coarseLogDOn_univ, ← coarseLogDOn_univ]
  exact h3 x hx x' hx' hxx

/-- **DZZ l. 1579–1594, walled** (`D'_S`, `D = D^{dzzWall K μIn}`; for `DZZConcApproxOn`). -/
theorem goodCoreOn_of_eStar (hW : IsWhiteNoise P W) (S : Set DyBox) (K : Set ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) {r τ ℓ ε₁ ε₂ : ℝ} (hℓ : 0 ≤ ℓ)
    (hr : γ * ℓ / 2 ≤ r) {A B : Set ℂ}
    (hgood : P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉
      CoarseGood γ (dzzCmc γ) δ} ≤ ε₁)
    (hE : (P.prod P).real (eStarEvent S γ (wnMix W (dzzCmc γ) δ)
      (fun p => dzzWall K (dzzMuIn γ (wnMix W (dzzCmc γ) δ) p)) δ r τ A B)ᶜ ≤ ε₂) :
    ∃ 𝒜 : Set (CoarseIdx (dzzCmc γ) δ → ℝ), 𝒜 ⊆ CoarseGood γ (dzzCmc γ) δ ∧
      P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜} ≤ ε₁ + 10 * ε₂ ∧
      ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) →
        |coarseLogDOn S γ (dzzCmc γ) δ A B x - coarseLogDOn S γ (dzzCmc γ) δ A B x'| ≤
          2 * τ := by
  obtain ⟨G₁, hG₁, hs⟩ := ae_sandwich_wnMix hW hγ hγ2 (κ := dzzCmc γ) hδ
  exact coreOn_of_eStar hW S hδ hγ.le hℓ hr
    (fun p => dzzWall K (dzzMuIn γ (wnMix W (dzzCmc γ) δ) p))
    ⟨G₁, hG₁, fun ω₁ h ω₁' h' hq => (hs ω₁ h ω₁' h' ℓ hℓ hq).mono fun ω₂ H => H K δ A B⟩
    hgood hE

end DZZ
end LQGMetric
