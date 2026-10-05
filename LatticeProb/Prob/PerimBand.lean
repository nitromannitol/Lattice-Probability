import Mathlib
import LatticeProb.Prob.PerimStein
import LatticeProb.Prob.PerimInner
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeOrthantPerimeter

/-!
# Assembly of the elementary Gaussian perimeter bound for the rounded-orthant class

Packet Q9a.  Takes the output of the tilt chain and the two regimes as the named hypothesis
`PerimPsiBound K` (`Ψ(t) = E[|V|; N² < t²] ≤ K (1 + √(2 log m))² t`, a `def` Prop carried as
an explicit hypothesis) and proves the cited proposition `MvbeOrthantPerimeterQuarter`
(restated locally as `PerimQuarterStmt`), by the assembly of `MvbeOrthantPerimeter.lean` with
`m/√(2π)` replaced by `L_m = 3 C₁ + 3 + √(2 log m)`, `C₁ = K (1 + √(2 log m))²`.

* `perimB_dyadic`: generic dyadic (ratio `q`) bookkeeping for half-open bands `{s < N ≤ s'}`.
* `perimB_open_band`, `perimB_half_open_base`: from (G4) with `a = s²`, `b = s'²`:
  `μ{s < N < s'} ≤ 3 C (s' - s)` for `s' ≤ 2 s`; half-open version for `s' ≤ (3/2) s`
  (the closed right end by `ENNReal.le_of_forall_pos_le_add`).
* `perimB_band_pos`, `perimB_band`: `μ{s < N ≤ s'} ≤ 3 C (s' - s)` for all `0 < s < s'`
  (dyadic) and all `0 ≤ s < s'` (monotone limit `s ↓ 0`), `N = √(perimN2 h ·)`,
  `μ = Measure.pi (gaussianReal 0 1)`; `perimB_band_stdGaussian` is the transfer to
  `stdGaussian (EuclideanSpace ℝ (Fin m))`.
* `perimB_rho_outer_band` (`0 ≤ a`), `perimB_rho_inner_band` (`b ≤ 0`), `perimB_rho_band`
  (all `a < b`, split at `0`): the bands of `ρ_h`.
* `perimB_gammaStarOf_orthant_le`, `perimB_class_le`: band bound `⟹` class bound.
* `perimB_quarter (K) (hK : PerimPsiBound K) : PerimQuarterStmt`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-- **Dyadic (ratio `q`) bookkeeping for half-open bands.** -/
theorem perimB_dyadic {α : Type*} [MeasurableSpace α] (ν : Measure α) (N : α → ℝ)
    {q D : ℝ} (hq : 1 < q) (hD : 0 ≤ D)
    (hbase : ∀ s s' : ℝ, 0 < s → s < s' → s' ≤ q * s →
      ν {x | s < N x ∧ N x ≤ s'} ≤ ENNReal.ofReal (D * (s' - s))) :
    ∀ s s' : ℝ, 0 < s → s < s' →
      ν {x | s < N x ∧ N x ≤ s'} ≤ ENNReal.ofReal (D * (s' - s)) := by
  have key : ∀ k : ℕ, ∀ s s' : ℝ, 0 < s → s < s' → s' ≤ q ^ (k + 1) * s →
      ν {x | s < N x ∧ N x ≤ s'} ≤ ENNReal.ofReal (D * (s' - s)) := by
    intro k
    induction k with
    | zero =>
      intro s s' hs hss' h
      exact hbase s s' hs hss' (by simpa using h)
    | succ k ih =>
      intro s s' hs hss' h
      by_cases hle : s' ≤ q * s
      · exact hbase s s' hs hss' hle
      · have hle := not_le.mp hle
        have hs1 : s < q * s := by nlinarith
        have hqs : 0 < q * s := by positivity
        have h' : s' ≤ q ^ (k + 1) * (q * s) := by
          calc s' ≤ q ^ (k + 1 + 1) * s := h
            _ = q ^ (k + 1) * (q * s) := by ring
        calc ν {x | s < N x ∧ N x ≤ s'}
            ≤ ν ({x | s < N x ∧ N x ≤ q * s} ∪ {x | q * s < N x ∧ N x ≤ s'}) := by
              refine measure_mono fun x hx => ?_
              by_cases hx2 : N x ≤ q * s
              · exact Or.inl ⟨hx.1, hx2⟩
              · exact Or.inr ⟨not_le.mp hx2, hx.2⟩
          _ ≤ ν {x | s < N x ∧ N x ≤ q * s} + ν {x | q * s < N x ∧ N x ≤ s'} :=
              measure_union_le _ _
          _ ≤ ENNReal.ofReal (D * (q * s - s)) + ENNReal.ofReal (D * (s' - q * s)) :=
              add_le_add (hbase s (q * s) hs hs1 le_rfl) (ih (q * s) s' hqs hle h')
          _ = ENNReal.ofReal (D * (s' - s)) := by
              rw [← ENNReal.ofReal_add (mul_nonneg hD (by linarith))
                (mul_nonneg hD (by linarith))]
              congr 1
              ring
  intro s s' hs hss'
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s' / s) hq
  refine key n s s' hs hss' ?_
  have h1 : s' < q ^ n * s := by
    rw [div_lt_iff₀ hs] at hn
    exact hn
  have h2 : q ^ n ≤ q ^ (n + 1) := pow_le_pow_right₀ hq.le (Nat.le_succ n)
  nlinarith


/-- **Open outer band for `N = √(perimN2 h ·)` on the product measure** from (G4): for
`0 < s < s' ≤ 2 s`, `μ{s < N < s'} ≤ 3 C (s' - s)` when `Ψ(t) ≤ C t`. -/
theorem perimB_open_band {m : ℕ} (h : Fin m → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ C * t)
    {s s' : ℝ} (hs : 0 < s) (hss' : s < s') (h2 : s' ≤ 2 * s) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        {x | s < √(perimN2 h x) ∧ √(perimN2 h x) < s'}
      ≤ ENNReal.ofReal (3 * C * (s' - s)) := by
  have hset : {x : Fin m → ℝ | s < √(perimN2 h x) ∧ √(perimN2 h x) < s'}
      = {x | s ^ 2 < perimN2 h x ∧ perimN2 h x < s' ^ 2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Real.lt_sqrt hs.le, Real.sqrt_lt' (by linarith)]
  rw [hset, ← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (perim_G4 h (a := s ^ 2) (b := s' ^ 2) (by positivity) (by nlinarith)).trans ?_
  have hI := hC s' (by linarith)
  have hcoef : 0 ≤ (s' ^ 2 - s ^ 2) / (2 * s ^ 2) :=
    div_nonneg (by nlinarith) (by positivity)
  refine (mul_le_mul_of_nonneg_left hI hcoef).trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h3 : (s' + s) * s' ≤ 6 * s ^ 2 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hC0 (sub_nonneg.2 hss'.le)) (sub_nonneg.2 h3)]

/-- Half-open base band: for `0 < s < s' ≤ (3/2) s`, `μ{s < N ≤ s'} ≤ 3 C (s' - s)`. -/
theorem perimB_half_open_base {m : ℕ} (h : Fin m → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ C * t)
    {s s' : ℝ} (hs : 0 < s) (hss' : s < s') (h2 : s' ≤ 3 / 2 * s) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        {x | s < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'}
      ≤ ENNReal.ofReal (3 * C * (s' - s)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  set δ : ℝ := min (s / 2) ((ε : ℝ) / (3 * C + 1)) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (div_pos hε' (by linarith))
  have hδ1 : δ ≤ s / 2 := min_le_left _ _
  have hδ2 : δ ≤ (ε : ℝ) / (3 * C + 1) := min_le_right _ _
  have hsub : {x : Fin m → ℝ | s < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'}
      ⊆ {x | s < √(perimN2 h x) ∧ √(perimN2 h x) < s' + δ} :=
    fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hεδ : 3 * C * δ ≤ ε := by
    have := (le_div_iff₀ (by linarith : 0 < 3 * C + 1)).1 hδ2
    nlinarith
  calc (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        {x | s < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'}
      ≤ (Measure.pi fun _ : Fin m => gaussianReal 0 1)
          {x | s < √(perimN2 h x) ∧ √(perimN2 h x) < s' + δ} := measure_mono hsub
    _ ≤ ENNReal.ofReal (3 * C * (s' + δ - s)) :=
        perimB_open_band h hC0 hC hs (by linarith) (by linarith)
    _ = ENNReal.ofReal (3 * C * (s' - s) + 3 * C * δ) := by congr 1; ring
    _ ≤ ENNReal.ofReal (3 * C * (s' - s)) + ENNReal.ofReal (3 * C * δ) :=
        ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (3 * C * (s' - s)) + ε := by
        gcongr
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hεδ

/-- Half-open outer band for every `0 < s < s'`. -/
theorem perimB_band_pos {m : ℕ} (h : Fin m → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ C * t)
    {s s' : ℝ} (hs : 0 < s) (hss' : s < s') :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        {x | s < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'}
      ≤ ENNReal.ofReal (3 * C * (s' - s)) :=
  perimB_dyadic (Measure.pi fun _ : Fin m => gaussianReal 0 1) (fun x => √(perimN2 h x))
    (q := 3 / 2) (D := 3 * C) (by norm_num) (by positivity)
    (fun _ _ hs hss' h2 => perimB_half_open_base h hC0 hC hs hss' h2) s s' hs hss'

/-- Half-open outer band, with no ordering hypothesis (empty set when `s' ≤ s`). -/
theorem perimB_band_pos_all {m : ℕ} (h : Fin m → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ C * t)
    {s : ℝ} (hs : 0 < s) (s' : ℝ) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        {x | s < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'}
      ≤ ENNReal.ofReal (3 * C * (s' - s)) := by
  by_cases hss' : s < s'
  · exact perimB_band_pos h hC0 hC hs hss'
  · have : {x : Fin m → ℝ | s < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro h1
      exact lt_of_le_of_lt (not_lt.mp hss') h1
    rw [this]
    simp

/-- **Outer band for `N = √(perimN2 h ·)` on the product Gaussian measure**, `0 ≤ s < s'`:
`μ{s < N ≤ s'} ≤ 3 C (s' - s)` from `Ψ(t) ≤ C t`. -/
theorem perimB_band {m : ℕ} (h : Fin m → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ C * t)
    {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        {x | s < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'}
      ≤ ENNReal.ofReal (3 * C * (s' - s)) := by
  rcases hs.lt_or_eq with hs0 | hs0
  · exact perimB_band_pos h hC0 hC hs0 hss'
  · subst hs0
    set μ : Measure (Fin m → ℝ) := Measure.pi fun _ : Fin m => gaussianReal 0 1 with hμ
    set A : ℕ → Set (Fin m → ℝ) := fun n =>
      {x | (1 : ℝ) / ((n : ℝ) + 1) < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'} with hA
    have hmono : Monotone A := by
      intro n n' hnn' x hx
      refine ⟨lt_of_le_of_lt ?_ hx.1, hx.2⟩
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn' 1)
    have hU : {x : Fin m → ℝ | 0 < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'} = ⋃ n, A n := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, hA]
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt h1
        exact ⟨n, hn, h2⟩
      · rintro ⟨n, hn, h2⟩
        exact ⟨lt_trans (by positivity) hn, h2⟩
    rw [hU, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine (perimB_band_pos_all h hC0 hC hn0 s').trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ 3 * C * (1 / ((n : ℝ) + 1)) := by positivity
    nlinarith

/-! ### Transfer to `ρ_h` on the standard Gaussian of `EuclideanSpace ℝ (Fin m)` -/

/-- The standard Gaussian of `EuclideanSpace ℝ (Fin m)` of a coordinate-measurable set equals the
product Gaussian measure of the set. -/
theorem perimB_stdGaussian_preimage {m : ℕ} {T : Set (Fin m → ℝ)} (hT : MeasurableSet T) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {y | y.ofLp ∈ T}
      = (Measure.pi fun _ : Fin m => gaussianReal 0 1) T := by
  have hmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin m) | y.ofLp ∈ T} :=
    (PiLp.continuous_ofLp 2 _).measurable hT
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (PiLp.continuous_toLp 2 _).measurable hmeas]
  rfl

section Rho

variable {m : ℕ} [NeZero m]

theorem perimB_rho_eq_sqrt (h : Fin m → ℝ) {x : EuclideanSpace ℝ (Fin m)}
    (hx : 0 < mvbeRho h x) : mvbeRho h x = √(perimN2 h x.ofLp) := by
  rw [mvbeRho_of_exists ((mvbeRho_pos_iff h x).1 hx)]
  rfl

theorem perimB_rho_pos_of_sqrt_pos (h : Fin m → ℝ) {x : EuclideanSpace ℝ (Fin m)}
    (hx : 0 < √(perimN2 h x.ofLp)) : 0 < mvbeRho h x := by
  rw [mvbeRho_pos_iff]
  by_contra hne
  have h0 : perimN2 h x.ofLp = 0 := by
    unfold perimN2 perimP
    refine Finset.sum_eq_zero fun j _ => ?_
    have : x.ofLp j - h j ≤ 0 := by
      have := not_exists.1 hne j
      exact sub_nonpos.2 (not_lt.1 this)
    rw [max_eq_right this]
    norm_num
  rw [h0, Real.sqrt_zero] at hx
  exact lt_irrefl _ hx

theorem perimB_rho_band_set (h : Fin m → ℝ) {a b : ℝ} (ha : 0 ≤ a) :
    {x : EuclideanSpace ℝ (Fin m) | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
      = {y | y.ofLp ∈ {x : Fin m → ℝ | a < √(perimN2 h x) ∧ √(perimN2 h x) ≤ b}} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < mvbeRho h x := lt_of_le_of_lt ha h1
    rw [perimB_rho_eq_sqrt h hpos] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hpos : 0 < mvbeRho h x := perimB_rho_pos_of_sqrt_pos h (lt_of_le_of_lt ha h1)
    rw [perimB_rho_eq_sqrt h hpos]
    exact ⟨h1, h2⟩

omit [NeZero m] in
theorem perimB_band_set_measurable (h : Fin m → ℝ) (a b : ℝ) :
    MeasurableSet {x : Fin m → ℝ | a < √(perimN2 h x) ∧ √(perimN2 h x) ≤ b} :=
  (measurableSet_lt measurable_const (perimN2_measurable h).sqrt).inter
    (measurableSet_le (perimN2_measurable h).sqrt measurable_const)

/-- **Outer band of `ρ_h`** (`0 ≤ a < b`): `γ{a < ρ_h ≤ b} ≤ 3 C (b - a)`. -/
theorem perimB_rho_outer_band (h : Fin m → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ C * t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
      ≤ ENNReal.ofReal (3 * C * (b - a)) := by
  rw [perimB_rho_band_set h ha, perimB_stdGaussian_preimage (perimB_band_set_measurable h a b)]
  exact perimB_band h hC0 hC ha hab

omit [NeZero m] in
/-- **Outer band of `N = √(perimN2 h ·)` on `stdGaussian (EuclideanSpace ℝ (Fin m))`**,
`0 ≤ s < s'`: `γ{s < N ≤ s'} ≤ 3 C (s' - s)`. -/
theorem perimB_band_stdGaussian (h : Fin m → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ C * t)
    {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') :
    stdGaussian (EuclideanSpace ℝ (Fin m))
        {y | s < √(perimN2 h y.ofLp) ∧ √(perimN2 h y.ofLp) ≤ s'}
      ≤ ENNReal.ofReal (3 * C * (s' - s)) := by
  have : {y : EuclideanSpace ℝ (Fin m) | s < √(perimN2 h y.ofLp) ∧ √(perimN2 h y.ofLp) ≤ s'}
      = {y | y.ofLp ∈ {x : Fin m → ℝ | s < √(perimN2 h x) ∧ √(perimN2 h x) ≤ s'}} := rfl
  rw [this, perimB_stdGaussian_preimage (perimB_band_set_measurable h s s')]
  exact perimB_band h hC0 hC hs hss'

/-- **Inner band of `ρ_h`** (`a < b ≤ 0`): `γ{a < ρ_h ≤ b} ≤ (3 + √(2 log m)) (b - a)`. -/
theorem perimB_rho_inner_band (h : Fin m → ℝ) {a b : ℝ} (hb : b ≤ 0) (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
      ≤ ENNReal.ofReal ((3 + √(2 * Real.log m)) * (b - a)) := by
  have hset : {x : EuclideanSpace ℝ (Fin m) | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
      = {x | ∀ j, x j ≤ h j + b} \ {x | ∀ j, x j ≤ h j + a} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    rw [mvbeRho_le_iff_of_nonpos hb, ← mvbeRho_le_iff_of_nonpos (by linarith : a ≤ 0), not_le]
    exact and_comm
  rw [hset]
  exact perim_stdGaussian_inner_layer_le h hab

/-- **Band bound for `ρ_h`** (all `a < b`, `m ≥ 1` implicit in `NeZero`):
`γ{a < ρ_h ≤ b} ≤ (3 C + 3 + √(2 log m)) (b - a)` when `Ψ(t) ≤ C t`. -/
theorem perimB_rho_band (h : Fin m → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ C * t)
    {a b : ℝ} (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
      ≤ ENNReal.ofReal ((3 * C + (3 + √(2 * Real.log m))) * (b - a)) := by
  have hLin : 0 ≤ 3 + √(2 * Real.log m) := by positivity
  have hba : 0 < b - a := sub_pos.2 hab
  by_cases hb : b ≤ 0
  · refine (perimB_rho_inner_band h hb hab).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hC0 hba.le]
  · have hb' := not_le.mp hb
    by_cases ha : 0 ≤ a
    · refine (perimB_rho_outer_band h hC0 hC ha hab).trans (ENNReal.ofReal_le_ofReal ?_)
      nlinarith [mul_nonneg hLin hba.le]
    · have ha' := not_le.mp ha
      have hsub : {x : EuclideanSpace ℝ (Fin m) | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
          ⊆ {x | a < mvbeRho h x ∧ mvbeRho h x ≤ 0} ∪ {x | 0 < mvbeRho h x ∧ mvbeRho h x ≤ b} := by
        intro x hx
        by_cases hx0 : mvbeRho h x ≤ 0
        · exact Or.inl ⟨hx.1, hx0⟩
        · exact Or.inr ⟨not_le.mp hx0, hx.2⟩
      calc stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
          ≤ stdGaussian (EuclideanSpace ℝ (Fin m))
              ({x | a < mvbeRho h x ∧ mvbeRho h x ≤ 0} ∪ {x | 0 < mvbeRho h x ∧ mvbeRho h x ≤ b}) :=
            measure_mono hsub
        _ ≤ stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ 0}
              + stdGaussian (EuclideanSpace ℝ (Fin m)) {x | 0 < mvbeRho h x ∧ mvbeRho h x ≤ b} :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal ((3 + √(2 * Real.log m)) * (0 - a))
              + ENNReal.ofReal (3 * C * (b - 0)) :=
            add_le_add (perimB_rho_inner_band h le_rfl ha')
              (perimB_rho_outer_band h hC0 hC le_rfl hb')
        _ = ENNReal.ofReal ((3 + √(2 * Real.log m)) * (0 - a) + 3 * C * (b - 0)) :=
            (ENNReal.ofReal_add (mul_nonneg hLin (by linarith))
              (mul_nonneg (by positivity) (by linarith))).symm
        _ ≤ ENNReal.ofReal ((3 * C + (3 + √(2 * Real.log m))) * (b - a)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            nlinarith [mul_nonneg hC0 (neg_nonneg.2 ha'.le), mul_nonneg hLin hb'.le]

/-! ### Assembly: from a band bound to the class bound -/

/-- **Perimeter of one rounded orthant from a band bound.**  If every band of every `ρ_h` has
Gaussian mass at most `L (b - a)`, then `γ*(O_{h,s} | δ) ≤ L` for `s ≥ 0`. -/
theorem perimB_gammaStarOf_orthant_le {L : ℝ} (hL : 0 ≤ L)
    (hband : ∀ (h : Fin m → ℝ) {a b : ℝ}, a < b →
      stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
        ≤ ENNReal.ofReal (L * (b - a)))
    (h : Fin m → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    mvbeGammaStarOf (stdGaussian (EuclideanSpace ℝ (Fin m)))
        (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) ≤ ENNReal.ofReal L := by
  refine iSup₂_le fun ε hε => ?_
  have hε0 : ENNReal.ofReal ε ≠ 0 := by simpa using hε
  rw [ENNReal.div_le_iff' hε0 ENNReal.ofReal_ne_top]
  have key : ENNReal.ofReal (L * ε) = ENNReal.ofReal ε * ENNReal.ofReal L := by
    rw [ENNReal.ofReal_mul hL, mul_comm]
  refine max_le ?_ ?_
  · rw [← key, mvbe_outer_layer_orthant h hs]
    have := hband h (a := s) (b := s + ε) (by linarith)
    rwa [add_sub_cancel_left] at this
  · rw [← key, mvbe_inner_layer_orthant h hs]
    have := hband h (a := s - ε) (b := s) (by linarith)
    rwa [sub_sub_cancel] at this

/-- **Class bound from a band bound**: `γ*(rounded orthants) ≤ L`. -/
theorem perimB_class_le {L : ℝ} (hL : 0 ≤ L)
    (hband : ∀ (h : Fin m → ℝ) {a b : ℝ}, a < b →
      stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
        ≤ ENNReal.ofReal (L * (b - a))) :
    (mvbeRoundedRegularClass m).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
      ≤ ENNReal.ofReal L := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨h, s, hs, rfl⟩ := hA
  exact perimB_gammaStarOf_orthant_le hL hband h hs

end Rho

/-! ### The hypothesis, the cited statement, and the final theorem -/

/-- **The output of the tilt chain and the two regimes** (carried as a hypothesis):
`Ψ(t) = E[|V|; N² < t²] ≤ C₁ t` with `C₁ = K (1 + √(2 log m))²`. -/
def PerimPsiBound (K : ℝ) : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (h : Fin m → ℝ) (t : ℝ), 0 < t →
    ∫ x in {x : Fin m → ℝ | perimN2 h x < t ^ 2}, |perimV h x|
      ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤ K * (1 + √(2 * Real.log m)) ^ 2 * t

/-- The cited proposition `MvbeOrthantPerimeterQuarter` (restated locally, textually the
definition in `MvbeOrthantBerryEsseen.lean`). -/
def PerimQuarterStmt : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) [NeZero m],
    (mvbeRoundedRegularClass m).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
      ≤ ENNReal.ofReal (c * (m : ℝ) ^ ((1 : ℝ) / 4))

/-- The constant `C₁ = K (1 + √(2 log m))²` is nonnegative (take `h = 0`, `t = 1`). -/
theorem perimB_C1_nonneg {K : ℝ} (hK : PerimPsiBound K) {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ K * (1 + √(2 * Real.log m)) ^ 2 := by
  have h1 := hK m hm (fun _ => 0) 1 one_pos
  have h2 : 0 ≤ ∫ x in {x : Fin m → ℝ | perimN2 (fun _ => (0 : ℝ)) x < 1 ^ 2},
      |perimV (fun _ => (0 : ℝ)) x| ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
    integral_nonneg fun _ => abs_nonneg _
  linarith

/-- The final band constant `L_m = 3 C₁ + 3 + √(2 log m)`. -/
noncomputable def perimBL (K : ℝ) (m : ℕ) : ℝ :=
  3 * (K * (1 + √(2 * Real.log m)) ^ 2) + (3 + √(2 * Real.log m))

theorem perimBL_nonneg {K : ℝ} (hK : PerimPsiBound K) {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ perimBL K m := by
  have := perimB_C1_nonneg hK hm
  unfold perimBL
  positivity

/-- **Band bound for `ρ_h` with the final constant.**  For `m ≥ 2` and all `a < b`,
`γ{a < ρ_h ≤ b} ≤ L_m (b - a)`. -/
theorem perimB_rho_band_le {K : ℝ} (hK : PerimPsiBound K) {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (h : Fin m → ℝ) {a b : ℝ} (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ b}
      ≤ ENNReal.ofReal (perimBL K m * (b - a)) :=
  perimB_rho_band h (perimB_C1_nonneg hK hm) (fun t ht => hK m hm h t ht) hab

/-- **The class bound `γ*(rounded orthants) ≤ L_m`** for `m ≥ 2`. -/
theorem perimB_class_le_of_psi {K : ℝ} (hK : PerimPsiBound K) {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    (mvbeRoundedRegularClass m).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
      ≤ ENNReal.ofReal (perimBL K m) :=
  perimB_class_le (perimBL_nonneg hK hm) fun h _ _ hab => perimB_rho_band_le hK hm h hab

/-- **Arithmetic**: `L_m ≤ (54 K + 8) m^{1/4}` for `m ≥ 2`, `K ≥ 0`. -/
theorem perimBL_le {K : ℝ} (hK0 : 0 ≤ K) {m : ℕ} (hm : 2 ≤ m) :
    perimBL K m ≤ (54 * K + 8) * (m : ℝ) ^ ((1 : ℝ) / 4) := by
  unfold perimBL
  have hlog0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  set H : ℝ := √(2 * Real.log m) with hH
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hH2 : H ^ 2 = 2 * Real.log m := Real.sq_sqrt (by positivity)
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set M : ℝ := (m : ℝ) ^ ((1 : ℝ) / 4) with hM
  have hM1 : 1 ≤ M :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ m)) (by norm_num)
  have hlogM : Real.log m ≤ 4 * M := by
    have h1 : Real.log M = 1 / 4 * Real.log m := Real.log_rpow hm0 _
    have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < M)
    linarith
  have h3 : (1 + H) ^ 2 ≤ 2 + 2 * H ^ 2 := by nlinarith [sq_nonneg (1 - H)]
  have h4 : H ≤ 1 / 2 + Real.log m := by nlinarith [sq_nonneg (H - 1)]
  have e : K * H ^ 2 = 2 * K * Real.log m := by rw [hH2]; ring
  nlinarith [mul_le_mul_of_nonneg_left h3 hK0, mul_le_mul_of_nonneg_left hlogM hK0,
    mul_le_mul_of_nonneg_left hM1 hK0]

/-- **The cited proposition `MvbeOrthantPerimeterQuarter`, from the tilt-chain hypothesis.**
Given `Ψ(t) ≤ K (1 + √(2 log m))² t` (`PerimPsiBound K`), the rounded-orthant Gaussian perimeter
is at most `c m^{1/4}`. -/
theorem perimB_quarter (K : ℝ) (hK : PerimPsiBound K) : PerimQuarterStmt := by
  have hK0 : 0 ≤ K := by
    have h2 := perimB_C1_nonneg hK (m := 2) le_rfl
    have hpos : 0 < (1 + √(2 * Real.log (2 : ℕ))) ^ 2 := by positivity
    by_contra hneg
    nlinarith [not_le.mp hneg]
  refine ⟨54 * K + 8, by positivity, fun m _ => ?_⟩
  have hm1 : m = 1 ∨ 2 ≤ m := by
    have := NeZero.ne m
    omega
  rcases hm1 with rfl | hm
  · refine mvbeRoundedRegularClass_gammaStar_le.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 := perim_two_le_sqrt
    rw [Nat.cast_one, Real.one_rpow, mul_one, div_le_iff₀ (by linarith)]
    nlinarith
  · exact (perimB_class_le_of_psi hK hm).trans (ENNReal.ofReal_le_ofReal (perimBL_le hK0 hm))

end LatticeProb
