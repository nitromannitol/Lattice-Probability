/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Q1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61G1

/-!
# DZZ Lemma 5.3, part 1, node 2 in rational-ball form (P2-DZZ53Q, packet P-131D of D131)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2452–2502 ((eq-z-open)).
DEC-131 §3 (P-131D): the bad event `l53ZBad` (S5L53G1) depends on the random measure `ν ω` only
through its rational ball masses `ballMassQ (ν ω)` (`lgdDZZ_eq_lgdRat`, LGDMeas;
`ballMassQ_dzzWall`, S6L61G1). We restate it for a *mass map* `M : Ω → (ℚ × ℚ) → ℚ → ℝ≥0∞`, so
that the locality hypothesis of node 2 becomes `Measurable[wnSigma W (R i)] (fun ω => M ω c q)`
and no honestly local `Ω → Measure ℂ` is needed (the proxy chaos is only a.e. local,
`fineChaos_ball_ae_local`, P-131C).

This file: the far relation `l53FarQ` and the bad event `l53ZBadQ`, the bridge
`l53ZBad_eq_l53ZBadQ` (`l53ZBad ν = l53ZBadQ (ballMassQ ∘ ν)`), the a.e. transfer
`l53ZBadQ_ae_eq_l53ZBad`, and copies (with credit) of the G1 results `measurable_lgdTilde_q`,
`measurableSet_l53Far_q`, `measurableSet_l53ZBad`, `l53ZBad_le`, `l53_open_of_not_l53ZBad`,
`l53ZBad_mono` and of G2's `l53Far_mono_ball`, `l53_hopen_of_not_bad` for mass maps.
The G3/G4 statements are in S5L53Q2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*}

/-! ### Walled rational masses -/

/-- Copy of `dzzWall_ball_le_iff` (S5L53E6) for `wallMass` (S6L61G1). -/
lemma wallMass_le_iff {K : Set ℂ} (hK : IsClosed K) (m : ℚ × ℚ → ℚ → ℝ≥0∞) (c : ℚ × ℚ) (q : ℚ)
    (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    wallMass K m c q ≤ t ↔ m c q ≤ t ∧ Metric.ball (ratPt c) q ⊆ K := by
  have hvol : volume (Metric.ball (ratPt c) (q : ℝ) ∩ Kᶜ) = 0 ↔
      Metric.ball (ratPt c) (q : ℝ) ⊆ K := by
    constructor
    · intro h0
      by_contra hns
      obtain ⟨w, hw, hwK⟩ := not_subset.1 hns
      exact ((Metric.isOpen_ball.inter hK.isOpen_compl).measure_ne_zero volume ⟨w, hw, hwK⟩) h0
    · intro hs
      rw [show Metric.ball (ratPt c) (q : ℝ) ∩ Kᶜ = ∅ from by
        ext w; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
          not_not]; exact fun hw => hs hw]
      exact measure_empty
  rw [← hvol, wallMass]
  constructor
  · intro h
    refine ⟨le_trans le_self_add h, ?_⟩
    by_contra h0
    have : (⊤ : ℝ≥0∞) * volume (Metric.ball (ratPt c) (q : ℝ) ∩ Kᶜ) = ⊤ := ENNReal.top_mul h0
    rw [this, add_top] at h
    exact ht (top_le_iff.1 h)
  · rintro ⟨h1, h2⟩
    rw [h2, mul_zero, add_zero]; exact h1

/-- Domination of the masses of the balls inside a closed wall passes to `wallMass` (the case split
of `lgdDZZ_wall_mono_ball`, S5L53G2). -/
lemma wallMass_le_of_ball {K : Set ℂ} (hK : IsClosed K) {m m' : ℚ × ℚ → ℚ → ℝ≥0∞}
    (hb : ∀ (c : ℚ × ℚ) (q : ℚ), Metric.ball (ratPt c) q ⊆ K → m c q ≤ m' c q)
    (c : ℚ × ℚ) (q : ℚ) : wallMass K m c q ≤ wallMass K m' c q := by
  simp only [wallMass]
  by_cases hs : Metric.ball (ratPt c) (q : ℝ) ⊆ K
  · have : Metric.ball (ratPt c) (q : ℝ) ∩ Kᶜ = ∅ := by
      ext w; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
        not_not]; exact fun hw => hs hw
    rw [this, measure_empty, mul_zero, add_zero, add_zero]
    exact hb c q hs
  · obtain ⟨w, hw, hwK⟩ := not_subset.1 hs
    have h0 : volume (Metric.ball (ratPt c) (q : ℝ) ∩ Kᶜ) ≠ 0 :=
      (Metric.isOpen_ball.inter hK.isOpen_compl).measure_ne_zero volume ⟨w, hw, hwK⟩
    rw [ENNReal.top_mul h0, add_top, add_top]

/-! ### The far relation and the bad event for a mass map -/

/-- The pair `(z, z')` is far at `ω` for the mass map `M`: not
`D^{𝕍̃_{z,z'}}_δ[M ω](z, z') ≤ e^T`, with the LGD `lgdRat` of the walled rational masses
(DZZ l. 2494; `l53Far` of S5L53G1 for `M = ballMassQ ∘ ν`, `l53Far_iff_l53FarQ`). -/
def l53FarQ (M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞) (δ T : ℝ) (ω : Ω) (z z' : ℂ) : Prop :=
  ¬ (lgdRat (wallMass (tildeBox z z') (M ω)) δ {z} {z'} ≠ ⊤ ∧
    ((lgdRat (wallMass (tildeBox z z') (M ω)) δ {z} {z'}).toNat : ℝ) ≤ Real.exp T)

/-- **The bad event of (eq-z-open) for a mass map** (DZZ l. 2497–2500; `l53ZBad`, S5L53G1). -/
def l53ZBadQ (M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞) (δ T : ℝ) (Bd : Set ℂ) (a b : ℝ≥0∞) : Set Ω :=
  {ω | b ≤ ((μH[1] : Measure ℂ).restrict Bd)
    {z | a ≤ ((μH[1] : Measure ℂ).restrict Bd) {z' | l53FarQ M δ T ω z z'}}}

/-- The measure far relation is the mass-map one for the rational ball masses. -/
lemma l53Far_iff_l53FarQ (ν : Ω → Measure ℂ) (δ T : ℝ) (ω : Ω) (z z' : ℂ) :
    l53Far ν δ T ω z z' ↔ l53FarQ (fun ω => ballMassQ (ν ω)) δ T ω z z' := by
  simp only [l53Far, l53FarQ, lgdLeExp, lgdDZZ_eq_lgdRat, ballMassQ_dzzWall]

/-! ### Measurability and the counting bound (copies of S5L53G1) -/

section Meas

variable [MeasurableSpace Ω]

/-- Copy of `measurable_lgdTilde_q` (S5L53G1) for a mass map. -/
theorem measurable_lgdTildeQ {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hM : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => M ω c q) (δ : ℝ) :
    Measurable fun p : Ω × (ℂ × ℂ) =>
      lgdRat (wallMass (tildeBox p.2.1 p.2.2) (M p.1)) δ {p.2.1} {p.2.2} := by
  refine measurable_enat_of_le fun K => ?_
  simp_rw [lgdRat_le_iff, ratAdm]
  refine measurableSet_setOfPred.2 (Measurable.exists fun N => Measurable.and
    (Measurable.exists fun c => Measurable.exists fun q => Measurable.and ?_
      (Measurable.forall fun i => Measurable.and measurable_const ?_)) measurable_const)
  · have hset : {p : Ω × (ℂ × ℂ) | ratCov {p.2.1} {p.2.2} N c q} =
        Prod.snd ⁻¹' {x : ℂ × ℂ | JoinedIn (⋃ i, Metric.ball (ratPt (c i)) (q i)) x.1 x.2} := by
      ext p
      simp only [ratCov, mem_singleton_iff, exists_eq_left, mem_ofPred_eq, mem_preimage, JoinedIn,
        mem_iUnion]
    refine measurableSet_setOfPred.1 ?_
    rw [hset]
    exact measurable_snd (isOpen_setOf_joinedIn
      (isOpen_iUnion fun i => Metric.isOpen_ball)).measurableSet
  · have hset : {p : Ω × (ℂ × ℂ) |
        wallMass (tildeBox p.2.1 p.2.2) (M p.1) (c i) (q i) ≤ ENNReal.ofReal (δ ^ 2)} =
        (Prod.fst ⁻¹' {ω | M ω (c i) (q i) ≤ ENNReal.ofReal (δ ^ 2)}) ∩
        (Prod.snd ⁻¹' {x : ℂ × ℂ | Metric.ball (ratPt (c i)) (q i) ⊆ tildeBox x.1 x.2}) := by
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
      exact wallMass_le_iff (isClosed_tildeBox _ _) _ _ _ _ ENNReal.ofReal_ne_top
    refine measurableSet_setOfPred.1 ?_
    rw [hset]
    exact (measurable_fst (measurableSet_le (hM _ _) measurable_const)).inter
      (measurable_snd (isClosed_setOf_ball_subset_tildeBox _ _).measurableSet)

/-- Copy of `measurableSet_l53Far_q` (S5L53G1) for a mass map. -/
theorem measurableSet_l53FarQ {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hM : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => M ω c q) (δ T : ℝ) :
    MeasurableSet {q : (Ω × ℂ) × ℂ | l53FarQ M δ T q.1.1 q.1.2 q.2} := by
  set g : (Ω × ℂ) × ℂ → Ω × (ℂ × ℂ) := fun q => (q.1.1, (q.1.2, q.2)) with hg
  have hgm : Measurable g := by rw [hg]; fun_prop
  have hm := (measurable_lgdTildeQ hM δ).comp hgm
  have : {q : (Ω × ℂ) × ℂ | l53FarQ M δ T q.1.1 q.1.2 q.2} =
      ((fun p : Ω × (ℂ × ℂ) =>
        lgdRat (wallMass (tildeBox p.2.1 p.2.2) (M p.1)) δ {p.2.1} {p.2.2}) ∘ g) ⁻¹'
        {k : ℕ∞ | ¬ (k ≠ ⊤ ∧ (k.toNat : ℝ) ≤ Real.exp T)} := by
    ext q; simp only [hg, Function.comp_apply, mem_preimage, mem_ofPred_eq]; rfl
  rw [this]
  exact hm (Set.to_countable _).measurableSet

/-- One far event `{ω | (z, z') far}` is measurable. -/
lemma measurableSet_l53FarQ_pair {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hM : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => M ω c q) (δ T : ℝ) (z z' : ℂ) :
    MeasurableSet {ω | l53FarQ M δ T ω z z'} :=
  (Measurable.prodMk (Measurable.prodMk measurable_id measurable_const) measurable_const)
    (measurableSet_l53FarQ hM δ T)

/-- **`l53ZBadQ` is measurable** for every σ-algebra making the masses `M · c q` measurable
(copy of `measurableSet_l53ZBad`, S5L53G1). -/
theorem measurableSet_l53ZBadQ {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hM : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => M ω c q) (δ T : ℝ)
    {Bd : Set ℂ} (hBd : μH[1] Bd ≠ ⊤) (a b : ℝ≥0∞) : MeasurableSet (l53ZBadQ M δ T Bd a b) := by
  set m : Measure ℂ := (μH[1] : Measure ℂ).restrict Bd with hm
  have : IsFiniteMeasure m := ⟨by rw [hm, Measure.restrict_apply_univ]; exact hBd.lt_top⟩
  have hS := measurableSet_l53FarQ hM δ T
  have h1 : Measurable fun x : Ω × ℂ => m (Prod.mk x ⁻¹' {q : (Ω × ℂ) × ℂ |
      l53FarQ M δ T q.1.1 q.1.2 q.2}) := measurable_measure_prodMk_left hS
  have h2 : MeasurableSet {x : Ω × ℂ | a ≤ m (Prod.mk x ⁻¹' {q : (Ω × ℂ) × ℂ |
      l53FarQ M δ T q.1.1 q.1.2 q.2})} := measurableSet_le measurable_const h1
  have h3 := measurable_measure_prodMk_left (ν := m) h2
  exact measurableSet_le measurable_const h3

end Meas

/-! ### Openness off the bad event (copies of S5L53G1/G2) -/

/-- **Off the bad event the box is open** (DZZ l. 2502); copy of `l53_open_of_not_l53ZBad`. -/
theorem l53_open_of_not_l53ZBadQ {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞} {δ T : ℝ} {Bd : Set ℂ}
    (hBm : MeasurableSet Bd) {a b : ℝ≥0∞} {ω : Ω} (hω : ω ∉ l53ZBadQ M δ T Bd a b) {Λ : Set ℂ}
    (hΛ : Λ ⊆ Bd) (hb : b ≤ μH[1] Λ) :
    ∃ z ∈ Λ, μH[1] {z' ∈ Bd | l53FarQ M δ T ω z z'} < a := by
  set m : Measure ℂ := (μH[1] : Measure ℂ).restrict Bd with hm
  have hlt : m {z | a ≤ m {z' | l53FarQ M δ T ω z z'}} < b := not_le.1 hω
  have hb' : b ≤ m Λ := by
    rw [hm, Measure.restrict_apply' hBm, inter_eq_left.2 hΛ]; exact hb
  by_contra hne
  push Not at hne
  have hsub : Λ ⊆ {z | a ≤ m {z' | l53FarQ M δ T ω z z'}} := by
    intro z hz
    show a ≤ m {z' | l53FarQ M δ T ω z z'}
    rw [hm, Measure.restrict_apply' hBm]
    have : {z' | l53FarQ M δ T ω z z'} ∩ Bd = {z' ∈ Bd | l53FarQ M δ T ω z z'} := by
      ext z'; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
    rw [this]; exact hne z hz
  exact absurd (hb'.trans (measure_mono hsub)) (not_le.2 hlt)

/-- Larger masses inside `𝕍̃_{z,z'}` make more pairs far (`l53Far_mono_ball`, S5L53G2). -/
lemma l53FarQ_mono_ball {M M' : Ω → ℚ × ℚ → ℚ → ℝ≥0∞} {δ T : ℝ} {ω : Ω} {z z' : ℂ}
    (hb : ∀ (c : ℚ × ℚ) (q : ℚ), Metric.ball (ratPt c) q ⊆ tildeBox z z' → M ω c q ≤ M' ω c q)
    (h : l53FarQ M δ T ω z z') : l53FarQ M' δ T ω z z' := by
  intro h'
  apply h
  have hle' := lgdRat_mono (wallMass_le_of_ball (isClosed_tildeBox z z') hb) δ {z} {z'}
  refine ⟨ne_top_of_le_ne_top h'.1 hle', le_trans ?_ h'.2⟩
  exact_mod_cast ENat.toNat_le_toNat hle' h'.1

/-- Far pairs for a measure `ν` are far for a mass map dominating its ball masses in
`𝕍̃_{z,z'}`. -/
lemma l53FarQ_of_l53Far_ball {ν : Ω → Measure ℂ} {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞} {δ T : ℝ} {ω : Ω}
    {z z' : ℂ}
    (hb : ∀ (c : ℚ × ℚ) (q : ℚ), Metric.ball (ratPt c) q ⊆ tildeBox z z' →
      ν ω (Metric.ball (ratPt c) q) ≤ M ω c q)
    (h : l53Far ν δ T ω z z') : l53FarQ M δ T ω z z' :=
  l53FarQ_mono_ball (M := fun ω => ballMassQ (ν ω)) hb ((l53Far_iff_l53FarQ ν δ T ω z z').1 h)

/-- **Openness for `D^K[ν ω]` off the mass-map bad event** (DZZ l. 2453), copy of
`l53_hopen_of_not_bad` (S5L53G2): the domination is `ν ω (ball) ≤ M ω c q` on the balls in `Bs`. -/
theorem l53_hopen_of_not_badQ {ν : Ω → Measure ℂ} {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞} {δ T : ℝ}
    {Bd Bs K : Set ℂ} (hBm : MeasurableSet Bd) {a b : ℝ≥0∞} {ω : Ω}
    (hω : ω ∉ l53ZBadQ M δ T Bd a b)
    (hdom : ∀ (c : ℚ × ℚ) (q : ℚ), Metric.ball (ratPt c) q ⊆ Bs →
      ν ω (Metric.ball (ratPt c) q) ≤ M ω c q)
    (hBs : ∀ z ∈ Bd, ∀ z' ∈ Bd, z ≠ z' → tildeBox z z' ⊆ Bs)
    (hK : ∀ z ∈ Bd, ∀ z' ∈ Bd, z ≠ z' → tildeBox z z' ⊆ K) :
    ∀ Λ ⊆ Bd, b ≤ μH[1] Λ → ∃ z ∈ Λ,
      μH[1] {z' ∈ Bd | ¬ lgdLeExp (dzzWall K (ν ω)) δ T z z'} ≤ a := by
  intro Λ hΛ hb
  obtain ⟨z, hz, hza⟩ := l53_open_of_not_l53ZBadQ hBm hω hΛ hb
  refine ⟨z, hz, ?_⟩
  have hzB := hΛ hz
  have hsub : {z' ∈ Bd | ¬ lgdLeExp (dzzWall K (ν ω)) δ T z z'} ⊆
      {z' ∈ Bd | l53FarQ M δ T ω z z'} ∪ {z} := by
    intro z' hz'
    by_cases he : z = z'
    · exact Or.inr he.symm
    refine Or.inl ⟨hz'.1, ?_⟩
    refine l53FarQ_of_l53Far_ball
      (fun c q hcq => hdom c q (hcq.trans (hBs z hzB z' hz'.1 he))) ?_
    exact fun h => hz'.2 (lgdLeExp_wall_mono (hK z hzB z' hz'.1 he) _ h)
  calc μH[1] {z' ∈ Bd | ¬ lgdLeExp (dzzWall K (ν ω)) δ T z z'}
      ≤ μH[1] {z' ∈ Bd | l53FarQ M δ T ω z z'} + μH[1] ({z} : Set ℂ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ a := by rw [l53_hausdorff_singleton, add_zero]; exact hza.le

end DZZ
end LQGMetric
