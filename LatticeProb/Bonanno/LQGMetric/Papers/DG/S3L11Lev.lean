/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Lev at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11

/-!
# DG Lemma 3.11 with a random level independent of the fine field (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.13
(DG:1300–1305): after scaling by `2^{-m-n_m}`, the threshold of Lemma 3.11 involves the coarse
field `ĥ_{2^{-m-n_m}}`, which is independent of the rescaled fine field; DG conclude that "the
conditional law … given `ĥ_{2^{-m-n_m}}` is stochastically dominated by" the law of Lemma 3.11.

Here the conditioning is done for a discrete random level `κ : Ω → ℤ` (the level of the coarse
factor) independent of a σ-algebra `m` carrying the fine events `E k x` (one family per level):
`prob_level_le` (`P[ω ∈ Bad(κ ω)] ≤ sup_k P[Bad k]` by countable subadditivity and independence),
the measurability of the percolation event in the fine events (`measurableSet_of_local`: it is a
finite Boolean combination of the events of the grid sites), and the Peierls bound
`l311_bad_le` (`perc_peierls`, as in `dg_lemma311_perc`). Main result: `dg_lemma311_level`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- an event depending only on the events `F z` of finitely many sites `z ∈ A` is measurable -/
lemma measurableSet_of_local {Ω : Type*} {m : MeasurableSpace Ω} (A : Finset (ℤ × ℤ))
    (Φ : Set (ℤ × ℤ) → Prop)
    (hΦ : ∀ G G' : Set (ℤ × ℤ), (∀ z ∈ A, z ∈ G ↔ z ∈ G') → Φ G → Φ G')
    (F : ℤ × ℤ → Set Ω) (hF : ∀ z ∈ A, MeasurableSet[m] (F z)) :
    MeasurableSet[m] {ω | Φ {z | ω ∈ F z}} := by
  classical
  have e : {ω | Φ {z | ω ∈ F z}} = ⋃ S ∈ A.powerset.filter (fun S : Finset (ℤ × ℤ) => Φ (↑S : Set (ℤ × ℤ))),
      ⋂ z ∈ A, {ω | ω ∈ F z ↔ z ∈ S} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro h
      refine ⟨A.filter (fun z => ω ∈ F z), ⟨Finset.filter_subset _ _, hΦ _ _ (fun z hz => ?_) h⟩,
        fun z hz => ?_⟩
      · simp [hz]
      · simp [hz]
    · rintro ⟨S, ⟨-, hS⟩, h⟩
      exact hΦ _ _ (fun z hz => by simpa using (h z hz).symm) hS
  rw [e]
  refine Finset.measurableSet_biUnion _ fun S _ => Finset.measurableSet_biInter _ fun z hz => ?_
  by_cases hzS : z ∈ S
  · have e1 : {ω | ω ∈ F z ↔ z ∈ S} = F z := by ext; simp [hzS]
    rw [e1]; exact hF z hz
  · have e1 : {ω | ω ∈ F z ↔ z ∈ S} = (F z)ᶜ := by ext; simp [hzS]
    rw [e1]; exact (hF z hz).compl

/-- the sites of the `K × L` grid -/
def gridFin (K L : ℤ) : Finset (ℤ × ℤ) := Finset.Ico 0 K ×ˢ Finset.Ico 0 L

lemma mem_gridFin {K L : ℤ} {x : ℤ × ℤ} : x ∈ gridFin K L ↔ percInGrid K L x := by
  simp only [gridFin, Finset.mem_product, Finset.mem_Ico, percInGrid]; tauto

lemma percGoodLR_mono {K L : ℤ} {g g' : ℤ × ℤ → Prop}
    (h : ∀ x, percInGrid K L x → g x → g' x) (hg : PercGoodLR K L g) : PercGoodLR K L g' := by
  obtain ⟨a, c, ha, hc, hga, hgood, hr⟩ := hg
  refine ⟨a, c, ha, hc, hga, h a hga hgood, ?_⟩
  clear hc
  induction hr with
  | refl => exact .refl
  | tail _ hxy ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
    exact ih.tail ⟨h1, h _ h1 h2, h3, h _ h3 h4, h5⟩

lemma measurableSet_not_percGoodLR {Ω : Type*} {m : MeasurableSpace Ω} (K L : ℤ)
    (F : ℤ × ℤ → Set Ω) (hF : ∀ x, MeasurableSet[m] (F x)) :
    MeasurableSet[m] {ω | ¬ PercGoodLR K L (fun x => ω ∈ F x)} :=
  measurableSet_of_local (gridFin K L) (fun G => ¬ PercGoodLR K L (· ∈ G))
    (fun _ _ hGG' hG hG' => hG (percGoodLR_mono (fun x hx h =>
      (hGG' x (mem_gridFin.2 hx)).2 h) hG')) F (fun z _ => hF z)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **conditioning on a discrete level independent of the fine σ-algebra** (DG:1300–1305) -/
lemma prob_level_le (P : Measure Ω) [IsProbabilityMeasure P] (κ : Ω → ℤ) (hκ : Measurable κ)
    (Fg : Set (Set Ω)) (Bad : ℤ → Set Ω)
    (hBad : ∀ k, MeasurableSet[MeasurableSpace.generateFrom Fg] (Bad k))
    (hind : ∀ (k : ℤ) (A : Set Ω), MeasurableSet[MeasurableSpace.generateFrom Fg] A →
      P ({ω | κ ω = k} ∩ A) = P {ω | κ ω = k} * P A)
    {q : ℝ≥0∞} (hq : ∀ k, P (Bad k) ≤ q) : P {ω | ω ∈ Bad (κ ω)} ≤ q := by
  have e : {ω | ω ∈ Bad (κ ω)} = ⋃ k, {ω | κ ω = k} ∩ Bad k := by
    ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℤ => {ω | κ ω = k}) := by
    intro i j hij
    exact Set.disjoint_left.2 fun ω h1 h2 => hij ((show κ ω = i from h1).symm.trans h2)
  have hmeas : ∀ k, MeasurableSet {ω | κ ω = k} := fun k => hκ (measurableSet_singleton k)
  have hsum : ∑' k, P {ω | κ ω = k} = 1 := by
    rw [← measure_iUnion hdisj hmeas]
    have : (⋃ k, {ω | κ ω = k}) = univ := by ext ω; simp
    rw [this, measure_univ]
  rw [e]
  calc P (⋃ k, {ω | κ ω = k} ∩ Bad k) ≤ ∑' k, P ({ω | κ ω = k} ∩ Bad k) := measure_iUnion_le _
    _ = ∑' k, P {ω | κ ω = k} * P (Bad k) := by
        congr 1; ext k; exact hind k _ (hBad k)
    _ ≤ ∑' k, P {ω | κ ω = k} * q := ENNReal.tsum_le_tsum fun k => by gcongr; exact hq k
    _ = q := by rw [ENNReal.tsum_mul_right, hsum, one_mul]

/-- the Peierls bound of `dg_lemma311_perc` for arbitrary site events -/
lemma l311_bad_le (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (E : ℤ × ℤ → Set Ω)
    (hgood : ∀ x, percInGrid (2 * (n : ℤ)) ((n : ℤ) - 2) x → P (E x)ᶜ ≤ (32⁻¹ : ℝ≥0∞) ^ 100)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ x ∈ F, percInGrid (2 * (n : ℤ)) ((n : ℤ) - 2) x) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 9 x y) →
      P (⋂ x ∈ F, (E x)ᶜ) ≤ ∏ x ∈ F, P (E x)ᶜ) :
    P {ω | ¬ PercGoodLR (2 * (n : ℤ)) ((n : ℤ) - 2) (fun x => ω ∈ E x)} ≤
      ENNReal.ofReal (32 * (2 : ℝ)⁻¹ ^ n) := by
  rcases lt_or_ge n 3 with hn | hn
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (2 : ℝ)⁻¹ ^ 2 ≤ (2 : ℝ)⁻¹ ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by omega)
    norm_num at this ⊢
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set B : ℤ × ℤ → Set Ω := fun x => (E x)ᶜ
  have eK : (((2 * (m + 2) : ℕ) : ℤ)) = 2 * (((m + 2 : ℕ) : ℤ)) := by push_cast; ring
  have eL : ((m : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ) - 2 := by push_cast; ring
  have hgrid : ∀ x, percInGrid ((2 * (m + 2) : ℕ) : ℤ) (m : ℤ) x →
      percInGrid (2 * ((m + 2 : ℕ) : ℤ)) (((m + 2 : ℕ) : ℤ) - 2) x := by
    intro x hx; rwa [eK, eL] at hx
  have hpeier := perc_peierls P (2 * (m + 2)) m (by omega) (by omega) B 9
    (θ := (32⁻¹ : ℝ≥0∞)) (ε := (32⁻¹ : ℝ≥0∞) ^ 100)
    (by
      have h : (8 : ℝ≥0∞) * 32⁻¹ = ENNReal.ofReal (8 * 32⁻¹) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
      have h' : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
      rw [h, h']
      exact ENNReal.ofReal_le_ofReal (by norm_num))
    (le_of_eq (by norm_num))
    (fun x hx => hgood x (hgrid x hx))
    (fun F hF hfar => hind F (fun x hx => hgrid x (hF x hx)) hfar)
  have hsub : {ω | ¬ PercGoodLR (2 * ((m + 2 : ℕ) : ℤ)) (((m + 2 : ℕ) : ℤ) - 2)
        (fun x => ω ∈ E x)} ⊆
      {ω | ¬ PercGoodLR ((2 * (m + 2) : ℕ) : ℤ) (m : ℤ) (fun x => ω ∉ B x)} := by
    intro ω hω hcross
    apply hω
    rw [eK, eL] at hcross
    simpa only [B, mem_compl_iff, not_not] using hcross
  refine (measure_mono hsub).trans (hpeier.trans ?_)
  have h8 : (8 * 32⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat,
      one_div]
    rw [show (32 : ℝ≥0∞) = 8 * 4 by norm_num, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  rw [h8, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := l311_num m
  push_cast at this ⊢
  exact this

/-- **DG Lemma 3.11 at a random level** (DG:1256–1278 with DG:1300–1305): for each level
`k ∈ ℤ` let `E k x` be fine events (measurable for `m`) which, on `{κ = k}`, imply that the grid
square `x` of `sℛ_n + b` is good with threshold `Mf k`; if each `E k x` has probability
`≥ 1 − 32^{−100}`, far failures satisfy the product bound, and the level `κ` is independent of
`m`, then `P[D^ε(∂_L, ∂_R; ℛ_n') > 2n² Mf(κ)] ≤ 32 · 2^{−n}`. -/
theorem dg_lemma311_level (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure ℂ)
    {ε s : ℝ} (hs : 0 < s) (b : ℂ) (n : ℕ) (κ : Ω → ℤ) (hκ : Measurable κ) (Mf : ℤ → ℝ)
    (Fg : Set (Set Ω)) (E : ℤ → ℤ × ℤ → Set Ω) (hEm : ∀ k x, E k x ∈ Fg)
    (hindκ : ∀ (k : ℤ) (A : Set Ω), MeasurableSet[MeasurableSpace.generateFrom Fg] A →
      P ({ω | κ ω = k} ∩ A) = P {ω | κ ω = k} * P A)
    (Z : Set Ω)
    (hpath : ∀ᵐ ω ∂P, ω ∉ Z → ∀ k x, κ ω = k → ω ∈ E k x → goodSq (μ ω) ε s b (Mf k) x)
    (hgood : ∀ k x, percInGrid (2 * (n : ℤ)) ((n : ℤ) - 2) x →
      P (E k x)ᶜ ≤ (32⁻¹ : ℝ≥0∞) ^ 100)
    (hind : ∀ k (F : Finset (ℤ × ℤ)), (∀ x ∈ F, percInGrid (2 * (n : ℤ)) ((n : ℤ) - 2) x) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 9 x y) →
      P (⋂ x ∈ F, (E k x)ᶜ) ≤ ∏ x ∈ F, P (E k x)ᶜ) :
    P {ω | ¬ (dgLGDSet (μ ω) ε (rectStretch s b n) (rectLeft s b n) (rectRight s b n) : ℝ≥0∞) ≤
        (2 * n ^ 2 : ℝ≥0∞) * ENNReal.ofReal (Mf (κ ω))} ≤
      ENNReal.ofReal (32 * (2 : ℝ)⁻¹ ^ n) + P Z := by
  set Bad : ℤ → Set Ω := fun k =>
    {ω | ¬ PercGoodLR (2 * (n : ℤ)) ((n : ℤ) - 2) (fun x => ω ∈ E k x)}
  have hsub : {ω | ¬ (dgLGDSet (μ ω) ε (rectStretch s b n) (rectLeft s b n)
      (rectRight s b n) : ℝ≥0∞) ≤ (2 * n ^ 2 : ℝ≥0∞) * ENNReal.ofReal (Mf (κ ω))} ≤ᵐ[P]
      {ω | ω ∈ Bad (κ ω)} ∪ Z := by
    filter_upwards [hpath] with ω hp
    exact fun hω => by_cases (p := ω ∈ Z) (fun hZ => Or.inr hZ) fun hZ => Or.inl fun hcross =>
      hω (dgLGDSet_rect_le_of_goodLR hs b
        (percGoodLR_mono (fun x _ hx => hp hZ (κ ω) x rfl hx) hcross))
  refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans (add_le_add_left ?_ _))
  refine (prob_level_le P κ hκ Fg Bad
    (fun k => measurableSet_not_percGoodLR _ _ _
      (fun x => MeasurableSpace.measurableSet_generateFrom (hEm k x))) hindκ
    (fun k => l311_bad_le P n (E k) (hgood k) (hind k)))

end DG
end LQGMetric
