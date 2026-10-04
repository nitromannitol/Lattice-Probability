import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic
import LatticeProb.Prob.AkcogluKrengelAE.BallMaximalLp
import LatticeProb.Prob.AkcogluKrengel

/-!
# The `Lᵖ` box mean ergodic theorem, and the pair-to-anchored-box reduction

Source main read: `01de1d0`.  `LatticeProb.akcoglu_krengel_mean` (`Prob/AkcogluKrengel.lean:730`) is
a *scalar* cube statement, not an `Lᵖ` norm convergence, so it does not supply the mean half.  The
library's `KrengelLpBall` (`BallMaximalLp.lean:74`) is the `ℓ¹`-ball `Lᵖ` maximal bound (the maximal
half); a box is contained in an `ℓ¹` ball, so it dominates the box maximal.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal symmDiff

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The normalized anchored-box average of `h` at scale `N`. -/
noncomputable def anchoredBoxAvgMean (h : Ω → ℝ) (τ : Site d → Ω → Ω) (c : Fin d → ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, h (τ x ω)

/-- **The anchored-box `Lᵖ` maximal inequality.**  For `c ≥ 0` and `p > 1`, the sup over `N` of the
deviation of the box average from the mean is controlled in `Lᵖ` by `‖h - ∫h‖_p`. -/
def AnchoredBoxMaximal (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Ω → ℝ), Measurable h →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      ∫⁻ ω, (⨆ N : ℕ,
          ENNReal.ofReal |anchoredBoxAvgMean h τ c N ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) ^ p ∂μ ≤
        ENNReal.ofReal C *
          ∫⁻ ω, (ENNReal.ofReal |h ω - ∫ ω, h ω ∂μ|) ^ p ∂μ

/-- **The `Lᵖ` box mean ergodic theorem**: `∫⁻ |boxAvg_N h - (∏ᵢ cᵢ) ∫h|ᵖ → 0`. -/
def AnchoredBoxMean (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      Tendsto (fun N : ℕ =>
          ∫⁻ ω, (ENNReal.ofReal
            |anchoredBoxAvgMean h τ c N ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) ^ p ∂μ)
        atTop (𝓝 0)

/-- **The dense-class input of the upgrade.**  A class of bounded measurable functions, dense in
`Lᵖ` modulo constants, on which the box averages converge a.e. to the mean. -/
def AnchoredBoxDenseClass (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∃ D : Set (Ω → ℝ),
      (∀ g ∈ D, Measurable g) ∧
      (∀ g ∈ D, ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ =>
          anchoredBoxAvgMean g τ c N ω - (∏ i, c i) * ∫ ω, g ω ∂μ) atTop (𝓝 0)) ∧
      (∀ h : Ω → ℝ, Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) → ∀ ε : ℝ, 0 < ε →
        ∃ g ∈ D, ∫⁻ ω, (ENNReal.ofReal
          |(h ω - g ω) - ∫ ω', (h ω' - g ω') ∂μ|) ^ p ∂μ < ENNReal.ofReal ε)

/-- **Step (c): the density/`limsup` upgrade.**  Given the maximal inequality and the dense class,
every bounded measurable `h` has its box averages converging a.e. to `(∏ᵢ cᵢ) ∫h`: for `g` in the
class, `limsup_N |A_N h| ≤ limsup_N |A_N g| + sup_N |A_N (h - g)| = sup_N |A_N (h - g)|` a.e., the
maximal bound controls the sup in `Lᵖ`, and the `Lᵖ` density lets `∫ |(h-g) - ∫(h-g)|ᵖ → 0`. -/
def AnchoredBoxDensityUpgrade (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) → 1 < p →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    AnchoredBoxMaximal d c p → AnchoredBoxDenseClass d c p →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => anchoredBoxAvgMean h τ c N ω) atTop
        (𝓝 ((∏ i, c i) * ∫ ω, h ω ∂μ))

/-- **The pair-to-anchored-box reduction.**  With the `Lᵖ` maximal inequality `AnchoredBoxMaximal`
(the library's `KrengelLpBall` dominates it), the `Lᵖ` box mean theorem `AnchoredBoxMean` and the
dense/`limsup` upgrade `AnchoredBoxDensityUpgrade`, the library's `AnchoredBoxErgodic` holds.  The
upgrade is the only place the density/`limsup` argument is used. -/
theorem AnchoredBoxErgodic_of_MaximalMean
    (Hmax : ∀ (c : Fin d → ℝ) (p : ℝ), 1 < p → AnchoredBoxMaximal d c p)
    (_Hmean : ∀ (c : Fin d → ℝ) (p : ℝ), 1 < p → AnchoredBoxMean d c p)
    (Hdense : ∀ (c : Fin d → ℝ) (p : ℝ), 1 < p → AnchoredBoxDenseClass d c p)
    (Hup : ∀ (c : Fin d → ℝ) (p : ℝ), 1 < p → AnchoredBoxDensityUpgrade d c p) :
    AnchoredBoxErgodic d := by
  intro Ω _ μ _ τ hτ hadd _herg h hh hb c hc
  exact (Hup c 2 (by norm_num)) hc (by norm_num) μ τ hτ hadd
    (Hmax c 2 (by norm_num)) (Hdense c 2 (by norm_num)) h hh hb

/-- The anchored-box average is measurable in the state. -/
theorem measurable_anchoredBoxAvgMean {h : Ω → ℝ} (hh : Measurable h)
    {τ : Site d → Ω → Ω} (hτ : ∀ z, Measurable (τ z)) (c : Fin d → ℝ) (N : ℕ) :
    Measurable fun ω => anchoredBoxAvgMean h τ c N ω := by
  unfold anchoredBoxAvgMean
  exact measurable_const.mul (Finset.measurable_sum _ fun x _ => hh.comp (hτ x))

/-- **Step (a): the maximal function is finite a.e.**  The sup has been rewritten as the countable
sup over `R : ℕ` of `if 1 ≤ R then |box average at R - (∏c)∫h| else 0`, a sup of measurable
functions, so it is measurable; the maximal inequality makes its `p`-th power `L¹`-finite, hence it
is finite a.e. -/
theorem anchoredBoxMaximal_ae_lt_top {c : Fin d → ℝ} {p : ℝ} (hp : 0 < p)
    {μ : Measure Ω} [IsProbabilityMeasure μ] (τ : Site d → Ω → Ω)
    (hτ : ∀ z, MeasurePreserving (τ z) μ μ) (_hadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    {h : Ω → ℝ} (hh : Measurable h) (_hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) {C : ℝ}
    (hC : ∫⁻ ω, (⨆ N : ℕ,
        ENNReal.ofReal |anchoredBoxAvgMean h τ c N ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) ^ p ∂μ ≤
      ENNReal.ofReal C * ∫⁻ ω, (ENNReal.ofReal |h ω - ∫ ω, h ω ∂μ|) ^ p ∂μ)
    (hint : ∫⁻ ω, (ENNReal.ofReal |h ω - ∫ ω, h ω ∂μ|) ^ p ∂μ ≠ ⊤) :
    ∀ᵐ ω ∂μ, (⨆ R : ℕ, ENNReal.ofReal
      (if 1 ≤ R then |anchoredBoxAvgMean h τ c R ω - (∏ i, c i) * ∫ ω, h ω ∂μ| else 0)) < ⊤ := by
  have hmN : ∀ R : ℕ, Measurable fun ω : Ω => ENNReal.ofReal
      (if 1 ≤ R then |anchoredBoxAvgMean h τ c R ω - (∏ i, c i) * ∫ ω, h ω ∂μ| else 0) := by
    intro R
    refine ENNReal.measurable_ofReal.comp ?_
    by_cases hR : 1 ≤ R
    · simp only [hR, ↓reduceIte]
      exact ((measurable_anchoredBoxAvgMean hh (fun z => (hτ z).measurable) c R).sub
        measurable_const).abs
    · simp only [hR, ↓reduceIte]
      exact measurable_const
  have hsup : Measurable fun ω : Ω => (⨆ R : ℕ, ENNReal.ofReal
      (if 1 ≤ R then |anchoredBoxAvgMean h τ c R ω - (∏ i, c i) * ∫ ω, h ω ∂μ| else 0)) :=
    Measurable.iSup hmN
  have hle : ∀ ω, (⨆ R : ℕ, ENNReal.ofReal
      (if 1 ≤ R then |anchoredBoxAvgMean h τ c R ω - (∏ i, c i) * ∫ ω, h ω ∂μ| else 0)) ≤
      (⨆ R : ℕ, ENNReal.ofReal |anchoredBoxAvgMean h τ c R ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) :=
    fun ω => iSup_le fun R => by
      by_cases hR : 1 ≤ R
      · simp only [hR, ↓reduceIte]
        exact le_iSup (fun R' => ENNReal.ofReal
          |anchoredBoxAvgMean h τ c R' ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) R
      · simp [hR]
  have hLfin : ∫⁻ ω, (⨆ R : ℕ, ENNReal.ofReal
      (if 1 ≤ R then |anchoredBoxAvgMean h τ c R ω - (∏ i, c i) * ∫ ω, h ω ∂μ| else 0)) ^ p ∂μ
      ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hint) hC)
      (lintegral_mono fun ω => ENNReal.rpow_le_rpow (hle ω) hp.le)
  have hf : Measurable fun ω : Ω => (⨆ R : ℕ, ENNReal.ofReal
      (if 1 ≤ R then |anchoredBoxAvgMean h τ c R ω - (∏ i, c i) * ∫ ω, h ω ∂μ| else 0)) ^ p :=
    ENNReal.continuous_rpow_const.measurable.comp hsup
  filter_upwards [ae_lt_top hf hLfin] with ω hω
  exact (ENNReal.rpow_lt_top_iff_of_pos hp).mp hω


omit [MeasurableSpace Ω] in
/-- **Invariant model case (algebraic part).**  For a function invariant under the action, every
box average is the value times the normalised box volume: `A_N h ω = (N^{-d} |anchoredBox c N|) h ω`.
Since `N^{-d} |anchoredBox c N| → ∏ᵢ cᵢ`, its a.e. limit is `(∏ᵢ cᵢ) h`, which equals `(∏ᵢ cᵢ) ∫h`
under ergodicity. -/
theorem anchoredBoxAvgMean_invariant {h : Ω → ℝ} (τ : Site d → Ω → Ω)
    (hinv : ∀ z ω, h (τ z ω) = h ω)
    (c : Fin d → ℝ) (N : ℕ) (ω : Ω) :
    anchoredBoxAvgMean h τ c N ω = (N : ℝ) ^ (-(d : ℝ)) * ((anchoredBox c N).card : ℝ) * h ω := by
  unfold anchoredBoxAvgMean
  rw [Finset.sum_congr rfl (fun x _ => hinv x ω), Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The two model cases of step (b)**, stated together: (i) functions invariant under the action
have box averages equal to `(N^{-d} |anchoredBox c N|) h`, converging a.e. to `(∏ᵢ cᵢ) ∫h` under
ergodicity (their a.e. value is the integral); (ii) a coboundary `h = g - g ∘ τ x` has box-sum
boundary of size `O(N^{d-1})`, so its average tends to `0 = ∫h`.  The density assembly (finite sums
plus the maximal inequality on the approximation error) is the remaining named step. -/
def AnchoredBoxDenseCases (d : ℕ) : Prop :=
  (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (τ : Site d → Ω → Ω) (h : Ω → ℝ) (c : Fin d → ℝ),
      (∀ z ω, h (τ z ω) = h ω) →
      (∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => anchoredBoxAvgMean h τ c N ω) atTop
        (𝓝 ((∏ i, c i) * ∫ ω, h ω ∂μ)))) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (τ : Site d → Ω → Ω) (x : Site d) (g : Ω → ℝ) (c : Fin d → ℝ),
      (∀ᵐ ω ∂μ, Tendsto (fun N : ℕ =>
        anchoredBoxAvgMean (fun ω => g ω - g (τ x ω)) τ c N ω) atTop (𝓝 0)))



omit [MeasurableSpace Ω] in
/-- **Coboundary model case (algebraic telescoping).**  For `h = g - g ∘ τ x`, the box sum is the
difference of the box sum of `g` and the sum of `g ∘ τ` over the shifted box (written as `x + y`):
`Σ_{y∈box} h(τ y ω) = Σ_{y∈box} g(τ y ω) - Σ_{y∈box} g(τ (x+y) ω)`.  The two overlap except on the
boundary of size `O(|x| N^{d-1})`, so dividing by `N^d` gives `O(1/N) → 0`, matching `∫h = 0`. -/
theorem anchoredBoxAvgMean_coboundary (g : Ω → ℝ) (τ : Site d → Ω → Ω)
    (hadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (x : Site d) (c : Fin d → ℝ) (N : ℕ)
    (ω : Ω) :
    anchoredBoxAvgMean (fun ω => g ω - g (τ x ω)) τ c N ω =
      (N : ℝ) ^ (-(d : ℝ)) *
        ((∑ y ∈ anchoredBox c N, g (τ y ω)) -
          ∑ y ∈ anchoredBox c N, g (τ (x + y) ω)) := by
  unfold anchoredBoxAvgMean
  rw [Finset.sum_congr rfl (fun y _ =>
    show g (τ y ω) - g (τ x (τ y ω)) = g (τ y ω) - g (τ (x + y) ω) from by
      rw [hadd x y ω])]
  rw [Finset.sum_sub_distrib]


/-- **The quantitative coboundary bound, stated.**  For `h = g - g ∘ τ (unit j)` with `|g| ≤ M`, the
box sum telescopes along coordinate `j`: for each choice of the other coordinates the inner sum
`Σ_{k<m_j} (g(τ(z + k e_j)ω) - g(τ(z + (k+1)e_j)ω))` collapses to `g(τ z ω) - g(τ(z + m_j e_j)ω)`, so
the whole sum is over the two `j`-faces and is at most `2 M ∏_{i≠j} m_i`, `m_i = ⌈N c_i⌉.toNat`.
Dividing by `N^d` gives `≤ 2M (∏_{i≠j} m_i / N^{d-1}) / N → 0` when `c_j > 0`, matching `∫h = 0`.
The telescoping/cardinality proof of this bound is the remaining formal step. -/
def CoboundaryBound (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (g : Ω → ℝ) {M : ℝ} (_hM : 0 ≤ M)
    (_hb : ∀ ω, |g ω| ≤ M) (τ : Site d → Ω → Ω)
    (_hadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (j : Fin d) (_hcj : 0 < c j) (ω : Ω) (N : ℕ),
    |∑ y ∈ anchoredBox c N, (g (τ y ω) - g (τ (unit j) (τ y ω)))| ≤
      2 * M * ∏ i ∈ Finset.univ.erase j, ((⌈(N : ℝ) * c i⌉).toNat : ℝ)


/-- **Step (iii), the `limsup` comparison.**  For every `h` and every `h'`, a.e.
`limsup_N |A_N h - (∏c)∫h| ≤ (⨆N |A_N (h - h')|) + |(∏c)∫(h - h')|`.  The invariant and coboundary
cases give `limsup_N |A_N h' - (∏c)∫h'| = 0`, and the `Lᵖ` density of the span lets
`∫ |(h - h') - ∫(h - h')|ᵖ → 0`, so the `limsup` vanishes. -/
def AnchoredBoxLimsupBound (d : ℕ) (c : Fin d → ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (h h' : Ω → ℝ),
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) → ∀ ω,
      ENNReal.ofReal (limsup (fun N : ℕ =>
          |anchoredBoxAvgMean h τ c N ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) atTop) ≤
        (⨆ N : ℕ, ENNReal.ofReal |anchoredBoxAvgMean (h - h') τ c N ω|) +
          ENNReal.ofReal |(∏ i, c i) * (∫ ω, h ω ∂μ - ∫ ω, h' ω ∂μ)|


/-- **The two-face cardinality bound.**  The symmetric difference of `anchoredBox c N` and its unit
shift in coordinate `j` is contained in the union of the two `j`-faces `{y ∈ box : y j = 0}` and
`{y ∈ box + unit j : y j = m j}`, each of cardinality `∏_{i≠j} ⌈N cᵢ⌉.toNat`, so it has at most
`2 ∏_{i≠j} ⌈N cᵢ⌉.toNat` elements.  This is the exact cardinality input of `CoboundaryBound`, and
it is the remaining formal step: the proof is `box \ box' ⊆ {y ∈ box : y j = 0}` and
`box' \ box ⊆ {y ∈ box' : y j = m j}` by membership in `Fintype.piFinset`, then
`Finset.card_le_card` with `Fintype.card_piFinset` on the slices. -/
def SymmDiffFaceBound (d : ℕ) : Prop :=
  ∀ (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (j : Fin d) (N : ℕ),
    (((anchoredBox c N) \ ((anchoredBox c N).map (Equiv.addRight (unit j)).toEmbedding)) ∪
        (((anchoredBox c N).map (Equiv.addRight (unit j)).toEmbedding) \ (anchoredBox c N))).card ≤
      2 * ∏ i ∈ Finset.univ.erase j, (⌈(N : ℝ) * c i⌉).toNat


omit [MeasurableSpace Ω] in
/-- **Containment of the first face.**  A site in the box but not in its unit-`j` translate has
`j`-coordinate `0`. -/
theorem sdiff_anchoredBox_subset_eq_zero {c : Fin d → ℝ} (N : ℕ) (j : Fin d) :
    (anchoredBox c N) \ ((anchoredBox c N).map (Equiv.addRight (unit j)).toEmbedding)
      ⊆ (anchoredBox c N).filter (fun y => y j = 0) := by
  intro y hy
  rw [Finset.mem_sdiff] at hy
  rw [Finset.mem_filter]
  refine ⟨hy.1, ?_⟩
  by_contra hne
  apply hy.2
  rw [Finset.mem_map]
  refine ⟨y - unit j, ?_, ?_⟩
  · rw [mem_anchoredBox] at hy ⊢
    intro i
    have hi := hy.1 i
    simp only [Finset.mem_Ico] at hi ⊢
    simp only [unit, Pi.sub_apply, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      constructor <;> omega
    · simp only [hij, ↓reduceIte, sub_zero]
      exact hi
  · ext i
    change ((y - unit j) + unit j) i = y i
    simp [Pi.add_apply, Pi.sub_apply]


omit [MeasurableSpace Ω] in
/-- **Containment of the second face.** -/
theorem sdiff_anchoredBox_shift_subset_eq_top {c : Fin d → ℝ} (N : ℕ) (j : Fin d) :
    ((anchoredBox c N).map (Equiv.addRight (unit j)).toEmbedding) \ (anchoredBox c N)
      ⊆ ((anchoredBox c N).map (Equiv.addRight (unit j)).toEmbedding).filter
          (fun y => y j = ⌈(N : ℝ) * c j⌉) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 (Finset.mem_sdiff.1 hy).1
  rw [mem_anchoredBox] at hx
  rw [Finset.mem_filter]
  refine ⟨(Finset.mem_sdiff.1 hy).1, ?_⟩
  have hyB : x + unit j ∉ anchoredBox c N := (Finset.mem_sdiff.1 hy).2
  change (x + unit j) j = ⌈(N : ℝ) * c j⌉
  have hxj : (x + unit j) j = x j + 1 := by simp [Pi.add_apply, unit, Pi.single_eq_same]
  rw [hxj]
  refine le_antisymm ?_ ?_
  · have := hx j
    simp only [Finset.mem_Ico] at this
    omega
  · by_contra hlt
    push Not at hlt
    apply hyB
    rw [mem_anchoredBox]
    intro i
    change (x + unit j) i ∈ Finset.Ico 0 ⌈(N : ℝ) * c i⌉
    have hi := hx i
    simp only [Finset.mem_Ico] at hi
    by_cases hij : i = j
    · rw [← hij] at hlt ⊢
      simp only [Pi.add_apply, unit, Pi.single_eq_same, Finset.mem_Ico]
      constructor <;> omega
    · have hval : (x + unit j) i = x i := by simp [Pi.add_apply, unit, Ne.symm hij]
      rw [hval]
      simpa using hi

omit [MeasurableSpace Ω] in
/-- **Slab cardinality, anchored box.**  Pinning the `j`-th coordinate of the anchored box at any
integer leaves at most `∏_{i ≠ j} m i` sites, `m i = ⌈N cᵢ⌉.toNat`. -/
theorem card_filter_anchoredBox_le {c : Fin d → ℝ} (N : ℕ) (j : Fin d) (a : ℤ) :
    ((anchoredBox c N).filter (fun y => y j = a)).card ≤
      ∏ i ∈ Finset.univ.erase j, (⌈(N : ℝ) * c i⌉).toNat := by
  rw [anchoredBox, Fintype.card_filter_piFinset_eq
    (s := fun i => Finset.Ico (0 : ℤ) ⌈(N : ℝ) * c i⌉) j a]
  split_ifs with h
  · refine le_of_eq (Finset.prod_congr rfl (fun i _ => ?_))
    rw [Int.card_Ico, sub_zero]
  · exact Nat.zero_le _

omit [MeasurableSpace Ω] in
/-- **Slab cardinality, unit-shifted box.**  The `j`-face `{y j = m j}` of the translated box
`anchoredBox c N + unit j` has at most `∏_{i ≠ j} m i` sites.  Under the right translation by
`unit j` this face is the slab `{x j = m j - 1}` of the anchored box, so it is the previous
lemma. -/
theorem card_filter_map_anchoredBox_le {c : Fin d → ℝ} (N : ℕ) (j : Fin d) :
    (((anchoredBox c N).map (Equiv.addRight (unit j)).toEmbedding).filter
        (fun y => y j = ⌈(N : ℝ) * c j⌉)).card ≤
      ∏ i ∈ Finset.univ.erase j, (⌈(N : ℝ) * c i⌉).toNat := by
  refine le_trans (le_of_eq ?_) (card_filter_anchoredBox_le (c := c) N j (⌈(N : ℝ) * c j⌉ - 1))
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  refine Finset.filter_congr (fun x _ => ?_)
  change (Equiv.addRight (unit j)).toEmbedding x j = ⌈(N : ℝ) * c j⌉ ↔
    x j = ⌈(N : ℝ) * c j⌉ - 1
  have hx : (Equiv.addRight (unit j)).toEmbedding x j = x j + 1 := by
    change (x + unit j) j = x j + 1
    simp [Pi.add_apply, unit, Pi.single_eq_same]
  rw [hx]
  omega

omit [MeasurableSpace Ω] in
/-- **The two-face cardinality bound, proved.**  The symmetric difference of the anchored box and
its unit-`j` translate lies in the union of the two slabs `{y j = 0}` and `{y j = m j}`, each of
cardinality at most `∏_{i ≠ j} m i`, so its cardinality is at most twice that product. -/
theorem symmDiffFaceBound (d : ℕ) : SymmDiffFaceBound d := by
  intro c hc j N
  have hsub1 := sdiff_anchoredBox_subset_eq_zero (c := c) N j
  have hsub2 := sdiff_anchoredBox_shift_subset_eq_top (c := c) N j
  refine le_trans (Finset.card_le_card (Finset.union_subset_union hsub1 hsub2)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := card_filter_anchoredBox_le (c := c) N j (0 : ℤ)
  have h2 := card_filter_map_anchoredBox_le (c := c) N j
  calc
    ((anchoredBox c N).filter (fun y => y j = 0)).card +
        (((anchoredBox c N).map (Equiv.addRight (unit j)).toEmbedding).filter
          (fun y => y j = ⌈(N : ℝ) * c j⌉)).card
        ≤ (∏ i ∈ Finset.univ.erase j, (⌈(N : ℝ) * c i⌉).toNat) +
            ∏ i ∈ Finset.univ.erase j, (⌈(N : ℝ) * c i⌉).toNat := Nat.add_le_add h1 h2
    _ = 2 * ∏ i ∈ Finset.univ.erase j, (⌈(N : ℝ) * c i⌉).toNat := by ring

end LatticeProb

#print axioms LatticeProb.anchoredBoxMaximal_ae_lt_top
#print axioms LatticeProb.card_filter_anchoredBox_le
#print axioms LatticeProb.card_filter_map_anchoredBox_le
#print axioms LatticeProb.symmDiffFaceBound
