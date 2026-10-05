import Mathlib
import LatticeProb.Prob.MvbeGaussConv
import LatticeProb.Prob.PittStatements
import LatticeProb.Gauss.MultivariateDensity
import LatticeProb.Prob.GaussDensity

/-!
# Pitt's Gaussian association theorem: the singular covariance

`pitt_full k hnd : PittFullStmt k` from `hnd : PittNondegStmt k`.

A positive semidefinite `S` with nonnegative entries may be singular and `f`, `g` are only bounded
Borel monotone, so one cannot let `ε → 0` in `S + ε 1` directly.  The route:

* Let `A = √S`, `u = S 1 = A w` with `w = A 1`.  Then `u ≥ 0`, and `u i = 0` forces `S i i = 0`,
  hence the `i`-th row of `A` vanishes, hence `(A z) i = 0` for every `z`.  Put
  `F = f ∘ pittProj u` (coordinates with `u i = 0` zeroed).  Then `F (A z) = f (A z)` for all `z`,
  and `F` is nondecreasing in the coordinates where `u i > 0` and ignores the others
  (`PittDirMono u F`).
* Envelopes `F^* (x) = inf_n F (x + (n+1)⁻¹ u)`, `F_* (x) = sup_n F (x - (n+1)⁻¹ u)`:
  `F_* ≤ F ≤ F^*`, `F^*` upper semicontinuous, `F_*` lower semicontinuous, both coordinatewise
  monotone (part (a)).
* Null jumps (part (b), `pitt_stdGaussian_null_jumps`): for `γ`-a.e. `z`, `F^* (A z) = F_* (A z)`.
  Along the line `z + ℝ w` the function `t ↦ F (A z + t u)` is monotone, hence has at most
  countably many discontinuities; Tonelli over `(z, t) ↦ z + t w` and `γ ≪ volume`.
* Coupling (part (c)): `X_ε = A z + √ε z'` on `γ ⊗ γ` has law `N(0, S + ε 1)`, which is positive
  definite with nonnegative entries.
* Limit (part (d)): `hnd` at `S + ε 1` for `F^*, G^*`; sandwich `F_* ≤ F^*`; Fatou for the lower
  semicontinuous `F_*, G_*` and reverse Fatou for the upper semicontinuous `F^* G^*`
  (`pitt_limit_ineq`); then replace `F_*, F^*` by `f` almost everywhere.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder ENNReal

namespace LatticeProb


/-! ### (a) One-sided envelopes along a nonnegative direction -/

section Envelopes

variable {k : ℕ}

/-- `F` is nondecreasing in the coordinates `i` where `u i > 0`, and ignores the others. -/
def PittDirMono (u : EuclideanSpace ℝ (Fin k)) (F : EuclideanSpace ℝ (Fin k) → ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin k), (∀ i, 0 < u i → x i ≤ y i) → F x ≤ F y

/-- Upper envelope `F^*(x) = inf_n F(x + (n+1)⁻¹ u)`. -/
noncomputable def pittUp (u : EuclideanSpace ℝ (Fin k)) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ⨅ n : ℕ, F (x + (1 / ((n : ℝ) + 1)) • u)

/-- Lower envelope `F_*(x) = sup_n F(x - (n+1)⁻¹ u)`. -/
noncomputable def pittDown (u : EuclideanSpace ℝ (Fin k)) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ⨆ n : ℕ, F (x - (1 / ((n : ℝ) + 1)) • u)

variable {u : EuclideanSpace ℝ (Fin k)} {F : EuclideanSpace ℝ (Fin k) → ℝ} {M : ℝ}

lemma pitt_shift_le (hu : ∀ i, 0 ≤ u i) (hF : PittDirMono u F) (x : EuclideanSpace ℝ (Fin k))
    {t s : ℝ} (hts : t ≤ s) : F (x + t • u) ≤ F (x + s • u) := by
  refine hF _ _ fun i _ => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have := mul_le_mul_of_nonneg_right hts (hu i)
  linarith

lemma pittUp_bddBelow (hM : ∀ x, |F x| ≤ M) (x : EuclideanSpace ℝ (Fin k)) :
    BddBelow (Set.range fun n : ℕ => F (x + (1 / ((n : ℝ) + 1)) • u)) :=
  ⟨-M, by rintro _ ⟨n, rfl⟩; exact (abs_le.1 (hM _)).1⟩

lemma pittDown_bddAbove (hM : ∀ x, |F x| ≤ M) (x : EuclideanSpace ℝ (Fin k)) :
    BddAbove (Set.range fun n : ℕ => F (x - (1 / ((n : ℝ) + 1)) • u)) :=
  ⟨M, by rintro _ ⟨n, rfl⟩; exact (abs_le.1 (hM _)).2⟩

lemma pittUp_le (hM : ∀ x, |F x| ≤ M) (x : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    pittUp u F x ≤ F (x + (1 / ((n : ℝ) + 1)) • u) :=
  ciInf_le (pittUp_bddBelow hM x) n

lemma pitt_le_pittDown (hM : ∀ x, |F x| ≤ M) (x : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    F (x - (1 / ((n : ℝ) + 1)) • u) ≤ pittDown u F x :=
  le_ciSup (pittDown_bddAbove hM x) n

lemma pitt_le_pittUp (hu : ∀ i, 0 ≤ u i) (hF : PittDirMono u F) (x : EuclideanSpace ℝ (Fin k)) :
    F x ≤ pittUp u F x := by
  refine le_ciInf fun n => ?_
  have := pitt_shift_le hu hF x (t := 0) (s := 1 / ((n : ℝ) + 1)) (by positivity)
  simpa using this

lemma pittDown_le (hu : ∀ i, 0 ≤ u i) (hF : PittDirMono u F) (x : EuclideanSpace ℝ (Fin k)) :
    pittDown u F x ≤ F x := by
  refine ciSup_le fun n => ?_
  have := pitt_shift_le hu hF x (t := -(1 / ((n : ℝ) + 1))) (s := 0) (by
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith)
  simpa [sub_eq_add_neg] using this

lemma pitt_abs_pittUp_le (hu : ∀ i, 0 ≤ u i) (hF : PittDirMono u F) (hM : ∀ x, |F x| ≤ M)
    (x : EuclideanSpace ℝ (Fin k)) : |pittUp u F x| ≤ M := by
  rw [abs_le]
  exact ⟨(abs_le.1 (hM x)).1.trans (pitt_le_pittUp hu hF x),
    (pittUp_le hM x 0).trans (abs_le.1 (hM _)).2⟩

lemma pitt_abs_pittDown_le (hu : ∀ i, 0 ≤ u i) (hF : PittDirMono u F) (hM : ∀ x, |F x| ≤ M)
    (x : EuclideanSpace ℝ (Fin k)) : |pittDown u F x| ≤ M := by
  rw [abs_le]
  exact ⟨(abs_le.1 (hM _)).1.trans (pitt_le_pittDown hM x 0),
    (pittDown_le hu hF x).trans (abs_le.1 (hM x)).2⟩

lemma pittUp_nonneg (hu : ∀ i, 0 ≤ u i) (hF : PittDirMono u F) (h0 : ∀ x, 0 ≤ F x)
    (x : EuclideanSpace ℝ (Fin k)) : 0 ≤ pittUp u F x :=
  (h0 x).trans (pitt_le_pittUp hu hF x)

lemma pittDown_nonneg (hM : ∀ x, |F x| ≤ M) (h0 : ∀ x, 0 ≤ F x)
    (x : EuclideanSpace ℝ (Fin k)) : 0 ≤ pittDown u F x :=
  (h0 _).trans (pitt_le_pittDown hM x 0)

lemma pittUp_dirMono (hF : PittDirMono u F) (hM : ∀ x, |F x| ≤ M) :
    PittDirMono u (pittUp u F) := by
  intro x y hxy
  refine ciInf_mono (pittUp_bddBelow hM x) fun n => hF _ _ fun i hi => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linarith [hxy i hi]

lemma pittDown_dirMono (hF : PittDirMono u F) (hM : ∀ x, |F x| ≤ M) :
    PittDirMono u (pittDown u F) := by
  intro x y hxy
  refine ciSup_mono (pittDown_bddAbove hM y) fun n => hF _ _ fun i hi => ?_
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  linarith [hxy i hi]

lemma pittUp_usc (hF : PittDirMono u F) (hM : ∀ x, |F x| ≤ M) :
    UpperSemicontinuous (pittUp u F) := by
  intro x c hc
  obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt hc
  have hδ : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have hev : ∀ᶠ y in 𝓝 x, ∀ i, 0 < u i → y i < x i + 1 / (2 * ((n : ℝ) + 1)) * u i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : 0 < u i
    · have hc1 : Continuous fun y : EuclideanSpace ℝ (Fin k) => y i := by fun_prop
      have hlt : x i < x i + 1 / (2 * ((n : ℝ) + 1)) * u i := by
        have := mul_pos hδ hi
        linarith
      filter_upwards [(hc1.tendsto x).eventually_lt tendsto_const_nhds hlt] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun y h => absurd h hi
  filter_upwards [hev] with y hy
  have hle := pittUp_le (u := u) hM y (2 * n + 1)
  have hcast : (1 : ℝ) / (((2 * n + 1 : ℕ) : ℝ) + 1) = 1 / (2 * ((n : ℝ) + 1)) := by
    push_cast; ring_nf
  rw [hcast] at hle
  refine lt_of_le_of_lt hle (lt_of_le_of_lt (hF _ _ fun i hi => ?_) hn)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have h1 := hy i hi
  have h2 : 1 / ((n : ℝ) + 1) * u i = 2 * (1 / (2 * ((n : ℝ) + 1)) * u i) := by
    field_simp
  linarith

lemma pittDown_lsc (hF : PittDirMono u F) (hM : ∀ x, |F x| ≤ M) :
    LowerSemicontinuous (pittDown u F) := by
  intro x c hc
  obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hc
  have hδ : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have hev : ∀ᶠ y in 𝓝 x, ∀ i, 0 < u i → x i - 1 / (2 * ((n : ℝ) + 1)) * u i < y i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : 0 < u i
    · have hc1 : Continuous fun y : EuclideanSpace ℝ (Fin k) => y i := by fun_prop
      have hlt : x i - 1 / (2 * ((n : ℝ) + 1)) * u i < x i := by
        have := mul_pos hδ hi
        linarith
      filter_upwards [(hc1.tendsto x).eventually_const_lt hlt] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun y h => absurd h hi
  filter_upwards [hev] with y hy
  have hle := pitt_le_pittDown (u := u) hM y (2 * n + 1)
  have hcast : (1 : ℝ) / (((2 * n + 1 : ℕ) : ℝ) + 1) = 1 / (2 * ((n : ℝ) + 1)) := by
    push_cast; ring_nf
  rw [hcast] at hle
  refine lt_of_lt_of_le (lt_of_lt_of_le hn (hF _ _ fun i hi => ?_)) hle
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have h1 := hy i hi
  have h2 : 1 / ((n : ℝ) + 1) * u i = 2 * (1 / (2 * ((n : ℝ) + 1)) * u i) := by
    field_simp
  linarith

/-- The product of two nonnegative upper semicontinuous functions is upper semicontinuous. -/
lemma pitt_usc_mul {α : Type*} [TopologicalSpace α] {a b : α → ℝ} (ha : UpperSemicontinuous a)
    (hb : UpperSemicontinuous b) (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) :
    UpperSemicontinuous (fun x => a x * b x) := by
  intro x c hc
  have hcont : Tendsto (fun η : ℝ => (a x + η) * (b x + η)) (𝓝 0) (𝓝 (a x * b x)) := by
    have : Continuous fun η : ℝ => (a x + η) * (b x + η) := by fun_prop
    simpa using this.tendsto 0
  obtain ⟨η, hη, hlt⟩ : ∃ η : ℝ, 0 < η ∧ (a x + η) * (b x + η) < c := by
    have h1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), (a x + η) * (b x + η) < c :=
      (hcont.eventually (gt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds
    obtain ⟨η, h2, h3⟩ := (h1.and self_mem_nhdsWithin).exists
    exact ⟨η, h3, h2⟩
  filter_upwards [ha x (a x + η) (by linarith), hb x (b x + η) (by linarith)] with y hya hyb
  calc a y * b y ≤ (a x + η) * (b x + η) :=
        mul_le_mul hya.le hyb.le (hb0 y) (by linarith [ha0 x])
    _ < c := hlt

end Envelopes

/-! ### (b) The envelopes agree off a null set of jumps -/

section NullJumps

variable {k : ℕ} {u : EuclideanSpace ℝ (Fin k)} {F : EuclideanSpace ℝ (Fin k) → ℝ} {M : ℝ}

/-- If the line `t ↦ F (x + t u)` is continuous at `0`, the two envelopes at `x` coincide. -/
lemma pittUp_eq_pittDown_of_continuousAt (hu : ∀ i, 0 ≤ u i) (hF : PittDirMono u F)
    (hM : ∀ x, |F x| ≤ M) (x : EuclideanSpace ℝ (Fin k))
    (hcont : ContinuousAt (fun t : ℝ => F (x + t • u)) 0) : pittUp u F x = pittDown u F x := by
  set h : ℝ → ℝ := fun t => F (x + t • u) with hh
  have hmono : Monotone h := fun t s hts => pitt_shift_le hu hF x hts
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h0 : h 0 = F x := by simp [hh]
  have hlim : Tendsto (fun n : ℕ => h (1 / ((n : ℝ) + 1))) atTop (𝓝 (F x)) := by
    rw [← h0]; exact hcont.tendsto.comp hseq
  have hlim' : Tendsto (fun n : ℕ => h (-(1 / ((n : ℝ) + 1)))) atTop (𝓝 (F x)) := by
    have hneg : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hseq.neg
    rw [← h0]; exact hcont.tendsto.comp hneg
  have hanti : Antitone fun n : ℕ => h (1 / ((n : ℝ) + 1)) := by
    intro n m hnm
    refine hmono ?_
    have : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact one_div_le_one_div_of_le (by positivity) this
  have hmono' : Monotone fun n : ℕ => h (-(1 / ((n : ℝ) + 1))) := by
    intro n m hnm
    refine hmono ?_
    have : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    have := one_div_le_one_div_of_le (by positivity) this
    linarith
  have hup : pittUp u F x = F x := by
    have h1 := tendsto_atTop_ciInf hanti (pittUp_bddBelow hM x)
    exact tendsto_nhds_unique h1 hlim
  have hdown : pittDown u F x = F x := by
    have hb : BddAbove (Set.range fun n : ℕ => h (-(1 / ((n : ℝ) + 1)))) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (abs_le.1 (hM _)).2
    have h1 := tendsto_atTop_ciSup hmono' hb
    have h2 : pittDown u F x = ⨆ n : ℕ, h (-(1 / ((n : ℝ) + 1))) := by
      simp [pittDown, hh, sub_eq_add_neg]
    rw [h2]
    exact tendsto_nhds_unique h1 hlim'
  rw [hup, hdown]

/-- A measurable set that meets every line `z + ℝ w` in a countable set is Lebesgue-null
(Tonelli over the shift `(z, t) ↦ z + t w`, using translation invariance of Lebesgue measure). -/
lemma pitt_volume_null_of_countable_lines {N : Set (EuclideanSpace ℝ (Fin k))}
    (hN : MeasurableSet N) (w : EuclideanSpace ℝ (Fin k))
    (hcount : ∀ z, {t : ℝ | z + t • w ∈ N}.Countable) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) N = 0 := by
  set Q : Set (EuclideanSpace ℝ (Fin k) × ℝ) := {p | p.1 + p.2 • w ∈ N} with hQ
  have hQm : MeasurableSet Q := hN.preimage (by fun_prop)
  have h1 : ((volume : Measure (EuclideanSpace ℝ (Fin k))).prod (volume : Measure ℝ)) Q = 0 := by
    rw [Measure.prod_apply hQm]
    have : ∀ z : EuclideanSpace ℝ (Fin k), (volume : Measure ℝ) (Prod.mk z ⁻¹' Q) = 0 :=
      fun z => (hcount z).measure_zero _
    simp [this]
  have h2 : ((volume : Measure (EuclideanSpace ℝ (Fin k))).prod (volume : Measure ℝ)) Q
      = (volume : Measure (EuclideanSpace ℝ (Fin k))) N * ⊤ := by
    rw [Measure.prod_apply_symm hQm]
    have : ∀ t : ℝ, (volume : Measure (EuclideanSpace ℝ (Fin k)))
        ((fun z => (z, t)) ⁻¹' Q) = (volume : Measure (EuclideanSpace ℝ (Fin k))) N :=
      fun t => measure_preimage_add_right volume (t • w) N
    simp [this, lintegral_const]
  rw [h2] at h1
  simpa using h1

/-- **Null jumps (iii).**  Let `A w = u` with `u ≥ 0`, and `F` bounded and nondecreasing in the
coordinates where `u > 0`.  Then the two envelopes of `F` along `u` agree at `A z` for
`γ`-a.e. `z`: along each line `z + ℝ w` the monotone function `t ↦ F (A z + t u)` has only
countably many discontinuities, hence the exceptional set is Lebesgue-null (Tonelli) and
`γ ≪ volume`. -/
lemma pitt_stdGaussian_null_jumps (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (w : EuclideanSpace ℝ (Fin k)) (hAw : A w = u) (hu : ∀ i, 0 ≤ u i) (hF : PittDirMono u F)
    (hM : ∀ x, |F x| ≤ M) :
    stdGaussian (EuclideanSpace ℝ (Fin k)) {z | pittUp u F (A z) ≠ pittDown u F (A z)} = 0 := by
  set N : Set (EuclideanSpace ℝ (Fin k)) := {z | pittUp u F (A z) ≠ pittDown u F (A z)} with hN
  have hup : Measurable fun z => pittUp u F (A z) :=
    (pittUp_usc hF hM).measurable.comp A.continuous.measurable
  have hdown : Measurable fun z => pittDown u F (A z) :=
    (pittDown_lsc hF hM).measurable.comp A.continuous.measurable
  have hNm : MeasurableSet N := (measurableSet_eq_fun hup hdown).compl
  have hcount : ∀ z, {t : ℝ | z + t • w ∈ N}.Countable := by
    intro z
    have hmono : Monotone fun s : ℝ => F (A z + s • u) :=
      fun s t hst => pitt_shift_le hu hF (A z) hst
    have hsub : {t : ℝ | z + t • w ∈ N}
        ⊆ {t : ℝ | ¬ ContinuousAt (fun s : ℝ => F (A z + s • u)) t} := by
      intro t ht hcont
      refine ht (pittUp_eq_pittDown_of_continuousAt hu hF hM _ ?_)
      have hfun : (fun s : ℝ => F (A (z + t • w) + s • u))
          = (fun s : ℝ => F (A z + s • u)) ∘ (fun s : ℝ => t + s) := by
        funext s
        simp [Function.comp, hAw, add_smul, add_assoc]
      rw [hfun]
      exact ContinuousAt.comp_of_eq hcont (continuousAt_const.add continuousAt_id) (by simp)
    exact Set.Countable.mono hsub hmono.countable_not_continuousAt
  have hvol := pitt_volume_null_of_countable_lines hNm w hcount
  rw [stdGaussian_euclidean_eq_withDensity (Fin k)]
  exact withDensity_absolutelyContinuous _ _ hvol

end NullJumps



/-! ### (d) Fatou-type limit inequalities -/

section Limit

variable {Ω : Type*} [MeasurableSpace Ω]

lemma pitt_integrable_of_bound {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ ω, |f ω| ≤ M) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using hM ω)

lemma pitt_integral_nonneg_le {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) {M : ℝ} (h0 : ∀ ω, 0 ≤ f ω) (hM : ∀ ω, f ω ≤ M) :
    0 ≤ ∫ ω, f ω ∂P ∧ ∫ ω, f ω ∂P ≤ M := by
  have hint : Integrable f P := pitt_integrable_of_bound hf (M := M) fun ω => by
    rw [abs_of_nonneg (h0 ω)]; exact hM ω
  refine ⟨integral_nonneg h0, ?_⟩
  calc ∫ ω, f ω ∂P ≤ ∫ _ω, M ∂P := integral_mono hint (integrable_const M) hM
    _ = M := by simp

/-- If every `c < a` is eventually below `s n`, then `ofReal a ≤ liminf (ofReal ∘ s)`. -/
lemma pitt_ofReal_le_liminf {s : ℕ → ℝ} {a : ℝ} (h : ∀ c < a, ∀ᶠ n in atTop, c < s n) :
    ENNReal.ofReal a ≤ liminf (fun n => ENNReal.ofReal (s n)) atTop := by
  refine le_of_forall_lt fun d hd => ?_
  obtain ⟨d', hdd', hd'⟩ := exists_between hd
  have hd'top : d' ≠ ∞ := ne_top_of_lt hd'
  have hlt : d'.toReal < a := (ENNReal.lt_ofReal_iff_toReal_lt hd'top).1 hd'
  have hev : ∀ᶠ n in atTop, d' ≤ ENNReal.ofReal (s n) := by
    filter_upwards [h _ hlt] with n hn
    calc d' = ENNReal.ofReal d'.toReal := (ENNReal.ofReal_toReal hd'top).symm
      _ ≤ ENNReal.ofReal (s n) := ENNReal.ofReal_le_ofReal hn.le
  exact lt_of_lt_of_le hdd' (le_liminf_of_le (by isBoundedDefault) hev)

/-- **Fatou, lower form** for bounded nonnegative functions on a probability space. -/
lemma pitt_fatou_lower (P : Measure Ω) [IsProbabilityMeasure P] {M : ℝ}
    (a : ℕ → Ω → ℝ) (a' : Ω → ℝ) (hm : ∀ n, Measurable (a n)) (hm' : Measurable a')
    (h0 : ∀ n ω, 0 ≤ a n ω) (hM : ∀ n ω, a n ω ≤ M) (h0' : ∀ ω, 0 ≤ a' ω) (hM' : ∀ ω, a' ω ≤ M)
    (hlim : ∀ ω, ∀ c < a' ω, ∀ᶠ n in atTop, c < a n ω) :
    ∀ c < ∫ ω, a' ω ∂P, ∀ᶠ n in atTop, c < ∫ ω, a n ω ∂P := by
  intro c hc
  by_cases hc0 : c < 0
  · exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le hc0 (integral_nonneg (h0 n))
  have hc0 : 0 ≤ c := not_lt.1 hc0
  have hint : ∀ n, Integrable (a n) P := fun n =>
    pitt_integrable_of_bound (hm n) (M := M) fun ω => by
      rw [abs_of_nonneg (h0 n ω)]; exact hM n ω
  have hint' : Integrable a' P := pitt_integrable_of_bound hm' (M := M) fun ω => by
    rw [abs_of_nonneg (h0' ω)]; exact hM' ω
  have key : ENNReal.ofReal (∫ ω, a' ω ∂P)
      ≤ liminf (fun n => ENNReal.ofReal (∫ ω, a n ω ∂P)) atTop := by
    rw [ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall h0')]
    calc ∫⁻ ω, ENNReal.ofReal (a' ω) ∂P
        ≤ ∫⁻ ω, liminf (fun n => ENNReal.ofReal (a n ω)) atTop ∂P :=
          lintegral_mono fun ω => pitt_ofReal_le_liminf (hlim ω)
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (a n ω) ∂P) atTop :=
          lintegral_liminf_le fun n => (hm n).ennreal_ofReal
      _ = liminf (fun n => ENNReal.ofReal (∫ ω, a n ω ∂P)) atTop := by
          congr 1
          funext n
          exact (ofReal_integral_eq_lintegral_ofReal (hint n)
            (Filter.Eventually.of_forall (h0 n))).symm
  have hlt : ENNReal.ofReal c < ENNReal.ofReal (∫ ω, a' ω ∂P) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).2 hc
  filter_upwards [eventually_lt_of_lt_liminf (lt_of_lt_of_le hlt key)] with n hn
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 hn).1

/-- **Fatou, upper form** for bounded nonnegative functions on a probability space. -/
lemma pitt_fatou_upper (P : Measure Ω) [IsProbabilityMeasure P] {M : ℝ}
    (b : ℕ → Ω → ℝ) (b' : Ω → ℝ) (hm : ∀ n, Measurable (b n)) (hm' : Measurable b')
    (h0 : ∀ n ω, 0 ≤ b n ω) (hM : ∀ n ω, b n ω ≤ M) (h0' : ∀ ω, 0 ≤ b' ω) (hM' : ∀ ω, b' ω ≤ M)
    (hlim : ∀ ω, ∀ c, b' ω < c → ∀ᶠ n in atTop, b n ω < c) :
    ∀ c, ∫ ω, b' ω ∂P < c → ∀ᶠ n in atTop, ∫ ω, b n ω ∂P < c := by
  intro c hc
  have hint : ∀ n, Integrable (b n) P := fun n =>
    pitt_integrable_of_bound (hm n) (M := M) fun ω => by
      rw [abs_of_nonneg (h0 n ω)]; exact hM n ω
  have hint' : Integrable b' P := pitt_integrable_of_bound hm' (M := M) fun ω => by
    rw [abs_of_nonneg (h0' ω)]; exact hM' ω
  have := pitt_fatou_lower P (M := M) (fun n ω => M - b n ω) (fun ω => M - b' ω)
    (fun n => measurable_const.sub (hm n)) (measurable_const.sub hm')
    (fun n ω => sub_nonneg.2 (hM n ω)) (fun n ω => by linarith [h0 n ω])
    (fun ω => sub_nonneg.2 (hM' ω)) (fun ω => by linarith [h0' ω])
    (fun ω d hd => by
      filter_upwards [hlim ω (M - d) (by linarith)] with n hn using by linarith) (M - c)
    (by
      rw [integral_sub (integrable_const M) hint']
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      linarith)
  filter_upwards [this] with n hn
  rw [integral_sub (integrable_const M) (hint n)] at hn
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hn
  linarith

/-- **The limit inequality.**  A product inequality `(∫ a n)(∫ b n) ≤ ∫ c n` for all `n` passes to
the limit when `a, b` are asymptotically lower semicontinuous and `c` asymptotically upper
semicontinuous, all nonnegative and bounded. -/
lemma pitt_limit_ineq (P : Measure Ω) [IsProbabilityMeasure P] {M : ℝ} (hM0 : 0 ≤ M)
    (a b c : ℕ → Ω → ℝ) (a' b' c' : Ω → ℝ)
    (hma : ∀ n, Measurable (a n)) (hmb : ∀ n, Measurable (b n)) (hmc : ∀ n, Measurable (c n))
    (hma' : Measurable a') (hmb' : Measurable b') (hmc' : Measurable c')
    (ha0 : ∀ n ω, 0 ≤ a n ω) (haM : ∀ n ω, a n ω ≤ M)
    (hb0 : ∀ n ω, 0 ≤ b n ω) (hbM : ∀ n ω, b n ω ≤ M)
    (hc0 : ∀ n ω, 0 ≤ c n ω) (hcM : ∀ n ω, c n ω ≤ M * M)
    (ha0' : ∀ ω, 0 ≤ a' ω) (haM' : ∀ ω, a' ω ≤ M)
    (hb0' : ∀ ω, 0 ≤ b' ω) (hbM' : ∀ ω, b' ω ≤ M)
    (hc0' : ∀ ω, 0 ≤ c' ω) (hcM' : ∀ ω, c' ω ≤ M * M)
    (hla : ∀ ω, ∀ x < a' ω, ∀ᶠ n in atTop, x < a n ω)
    (hlb : ∀ ω, ∀ x < b' ω, ∀ᶠ n in atTop, x < b n ω)
    (hlc : ∀ ω, ∀ x, c' ω < x → ∀ᶠ n in atTop, c n ω < x)
    (H : ∀ n, (∫ ω, a n ω ∂P) * (∫ ω, b n ω ∂P) ≤ ∫ ω, c n ω ∂P) :
    (∫ ω, a' ω ∂P) * (∫ ω, b' ω ∂P) ≤ ∫ ω, c' ω ∂P := by
  have FA := pitt_fatou_lower P a a' hma hma' ha0 haM ha0' haM' hla
  have FB := pitt_fatou_lower P b b' hmb hmb' hb0 hbM hb0' hbM' hlb
  have FC := pitt_fatou_upper P c c' hmc hmc' hc0 hcM hc0' hcM' hlc
  obtain ⟨hI0, hIM⟩ := pitt_integral_nonneg_le (P := P) hma' ha0' haM'
  obtain ⟨hJ0, hJM⟩ := pitt_integral_nonneg_le (P := P) hmb' hb0' hbM'
  set I := ∫ ω, a' ω ∂P
  set J := ∫ ω, b' ω ∂P
  set K := ∫ ω, c' ω ∂P
  have hη : ∀ η : ℝ, 0 < η → η ≤ 1 → I * J ≤ K + η * (2 + 2 * M) := by
    intro η hη0 hη1
    obtain ⟨n, hn1, hn2, hn3⟩ := ((FA (I - η) (by linarith)).and
      ((FB (J - η) (by linarith)).and (FC (K + η) (by linarith)))).exists
    obtain ⟨hA0, hAM⟩ := pitt_integral_nonneg_le (P := P) (hma n) (ha0 n) (haM n)
    obtain ⟨hB0, hBM⟩ := pitt_integral_nonneg_le (P := P) (hmb n) (hb0 n) (hbM n)
    have h1 := H n
    have h2 : I * J ≤ ((∫ ω, a n ω ∂P) + η) * ((∫ ω, b n ω ∂P) + η) :=
      mul_le_mul (by linarith) (by linarith) hJ0 (by linarith)
    nlinarith [mul_nonneg hA0 hB0, mul_nonneg hη0.le hA0, mul_nonneg hη0.le hB0, hη1,
      mul_le_mul_of_nonneg_left hAM hη0.le, mul_le_mul_of_nonneg_left hBM hη0.le]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hpos : 0 < 2 + 2 * M := by linarith
  have hmin : min 1 (ε / (2 + 2 * M)) * (2 + 2 * M) ≤ ε := by
    calc min 1 (ε / (2 + 2 * M)) * (2 + 2 * M) ≤ ε / (2 + 2 * M) * (2 + 2 * M) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
      _ = ε := by field_simp
  have := hη (min 1 (ε / (2 + 2 * M))) (lt_min one_pos (div_pos hε hpos)) (min_le_left _ _)
  linarith

end Limit



/-! ### (c) The coupling and the matrix facts -/

section MatrixFacts

variable {k : ℕ}

/-- The regularisation direction `u = S 1`, i.e. `u i = ∑ j, S i j`. -/
noncomputable def pittDir (S : Matrix (Fin k) (Fin k) ℝ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i => ∑ j, S i j

/-- Zero out the coordinates `i` where `u i` is not positive. -/
noncomputable def pittProj (u x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i => if 0 < u i then x i else 0

lemma pittDir_apply (S : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) : pittDir S i = ∑ j, S i j := rfl

lemma pittDir_nonneg {S : Matrix (Fin k) (Fin k) ℝ} (hSnn : ∀ i j, 0 ≤ S i j) (i : Fin k) :
    0 ≤ pittDir S i := by
  rw [pittDir_apply]
  exact Finset.sum_nonneg fun j _ => hSnn i j

lemma pittProj_apply (u x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    pittProj u x i = if 0 < u i then x i else 0 := rfl

lemma pittProj_continuous (u : EuclideanSpace ℝ (Fin k)) : Continuous (pittProj u) := by
  unfold pittProj
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : 0 < u i
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    exact continuous_const

lemma pittProj_eq_self {u x : EuclideanSpace ℝ (Fin k)} (h : ∀ i, ¬ 0 < u i → x i = 0) :
    pittProj u x = x := by
  ext i
  rw [pittProj_apply]
  by_cases hi : 0 < u i
  · simp [hi]
  · simp [hi, h i hi]

lemma pittProj_mono {u x y : EuclideanSpace ℝ (Fin k)} (h : ∀ i, 0 < u i → x i ≤ y i) (i : Fin k) :
    pittProj u x i ≤ pittProj u y i := by
  rw [pittProj_apply, pittProj_apply]
  by_cases hi : 0 < u i
  · simp [hi, h i hi]
  · simp [hi]

/-- `A (A 1) = S 1` for `A = √S`. -/
lemma pitt_sqrt_sqrt_one {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) (WithLp.toLp 2 fun _ => (1 : ℝ)))
      = pittDir S := by
  ext i
  simp only [Matrix.toEuclideanCLM_toLp, Matrix.mulVec_mulVec,
    CFC.sqrt_mul_sqrt_self S hS.nonneg]
  simp [pittDir_apply, Matrix.mulVec, dotProduct]

lemma pitt_sqrt_symm {S : Matrix (Fin k) (Fin k) ℝ} (a b : Fin k) :
    CFC.sqrt S a b = CFC.sqrt S b a := by
  have hher : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint.isHermitian
  have h := congr_fun (congr_fun hher a) b
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using h.symm

/-- A coordinate whose direction entry vanishes is identically zero on the range of `√S`. -/
lemma pitt_sqrt_apply_eq_zero {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef)
    (hSnn : ∀ i j, 0 ≤ S i j) {i : Fin k} (hi : ¬ 0 < pittDir S i)
    (z : EuclideanSpace ℝ (Fin k)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) z) i = 0 := by
  have hu0 : pittDir S i = 0 := le_antisymm (not_lt.1 hi) (pittDir_nonneg hSnn i)
  have hSi : ∀ j, S i j = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hSnn i j)).1
      (by simpa [pittDir_apply] using hu0)
    exact fun j => this j (Finset.mem_univ j)
  have hSii : S i i = 0 := hSi i
  have hrow : ∀ j, CFC.sqrt S i j = 0 := by
    have hmul : (CFC.sqrt S * CFC.sqrt S) i i = ∑ j, (CFC.sqrt S i j) ^ 2 := by
      simp only [Matrix.mul_apply, sq]
      exact Finset.sum_congr rfl fun j _ => by rw [pitt_sqrt_symm (S := S) j i]
    rw [CFC.sqrt_mul_sqrt_self S hS.nonneg, hSii] at hmul
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (CFC.sqrt S i j))).1 hmul.symm
    exact fun j => pow_eq_zero_iff (two_ne_zero) |>.1 (this j (Finset.mem_univ j))
  simp [Matrix.mulVec, dotProduct, hrow]

end MatrixFacts

section Coupling

variable {k : ℕ}

lemma pitt_coupling_law_zero {S : Matrix (Fin k) (Fin k) ℝ} :
    ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))).map
      (fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) p.1)
      = multivariateGaussian 0 S := by
  rw [multivariateGaussian_eq_map]
  have : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) p.1)
      = (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod]
  simp

/-- **The coupling `X_ε = A z + √ε z'` has law `N(0, S + ε 1)`.** -/
lemma pitt_coupling_law {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))).map
      (fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) p.1 + Real.sqrt ε • p.2)
      = multivariateGaussian 0 (S + ε • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  have hX : Measurable fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) p.1 := by fun_prop
  have hY : Measurable fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      Real.sqrt ε • p.2 := by fun_prop
  have hind := indepFun_prod (μ := γ) (ν := γ)
    (X := fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
    (Y := fun z => Real.sqrt ε • z) (by fun_prop) (by fun_prop)
  have hYlaw : (γ.prod γ).map (fun p => Real.sqrt ε • p.2)
      = multivariateGaussian 0 (ε • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    have : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) => Real.sqrt ε • p.2)
        = (fun z => Real.sqrt ε • z) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
    rw [mvbe_stdGaussian_map_smul (Real.sqrt_nonneg ε), Real.sq_sqrt hε]
  have := mvbe_law_add_multivariateGaussian hX hY hind 0 0 hS
    (Matrix.PosSemidef.one.smul hε) pitt_coupling_law_zero hYlaw
  have h2 : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) p.1 + Real.sqrt ε • p.2)
      = (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
          Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) p.1) + (fun p => Real.sqrt ε • p.2) := rfl
  rw [h2]
  simpa using this

lemma pitt_posDef_add {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (S + ε • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef :=
  Matrix.PosDef.posSemidef_add hS (Matrix.PosDef.one.smul hε)

lemma pitt_entries_add {S : Matrix (Fin k) (Fin k) ℝ} (hSnn : ∀ i j, 0 ≤ S i j) {ε : ℝ}
    (hε : 0 ≤ ε) (i j : Fin k) : 0 ≤ (S + ε • (1 : Matrix (Fin k) (Fin k) ℝ)) i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have := hSnn i j
  split_ifs <;> nlinarith

end Coupling


/-! ### (e) The theorem -/

section Main

variable {k : ℕ}

/-- The nonnegative case of Pitt's theorem for an arbitrary positive semidefinite covariance with
nonnegative entries, assuming the nondegenerate case `hnd`. -/
theorem pitt_full_nonneg (hnd : PittNondegStmt k) {S : Matrix (Fin k) (Fin k) ℝ}
    (hS : S.PosSemidef) (hSnn : ∀ i j, 0 ≤ S i j)
    {f g : EuclideanSpace ℝ (Fin k) → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {M : ℝ} (hfM : ∀ x, |f x| ≤ M) (hgM : ∀ x, |g x| ≤ M)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfmono : PittMono f) (hgmono : PittMono g) :
    (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
        * (∫ x, g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
      ≤ ∫ x, f x * g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S) := by
  classical
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  set γ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  set P : Measure (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) := γ.prod γ with hP
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hA
  set u : EuclideanSpace ℝ (Fin k) := pittDir S with hudef
  set w : EuclideanSpace ℝ (Fin k) := A (WithLp.toLp 2 fun _ => (1 : ℝ)) with hwdef
  have hu : ∀ i, 0 ≤ u i := pittDir_nonneg hSnn
  have hAw : A w = u := pitt_sqrt_sqrt_one hS
  -- the functions `F = f ∘ pittProj u`, `G = g ∘ pittProj u`
  set F : EuclideanSpace ℝ (Fin k) → ℝ := fun x => f (pittProj u x) with hFdef
  set G : EuclideanSpace ℝ (Fin k) → ℝ := fun x => g (pittProj u x) with hGdef
  have hFmono : PittDirMono u F := fun x y hxy => hfmono _ _ (pittProj_mono hxy)
  have hGmono : PittDirMono u G := fun x y hxy => hgmono _ _ (pittProj_mono hxy)
  have hFM : ∀ x, |F x| ≤ M := fun x => hfM _
  have hGM : ∀ x, |G x| ≤ M := fun x => hgM _
  have hF0 : ∀ x, 0 ≤ F x := fun x => hf0 _
  have hG0 : ∀ x, 0 ≤ G x := fun x => hg0 _
  have hFA : ∀ z, F (A z) = f (A z) := fun z => by
    simp only [hFdef]
    rw [pittProj_eq_self fun i hi => pitt_sqrt_apply_eq_zero hS hSnn hi z]
  have hGA : ∀ z, G (A z) = g (A z) := fun z => by
    simp only [hGdef]
    rw [pittProj_eq_self fun i hi => pitt_sqrt_apply_eq_zero hS hSnn hi z]
  -- the envelopes
  have hFuM := pitt_abs_pittUp_le hu hFmono hFM
  have hGuM := pitt_abs_pittUp_le hu hGmono hGM
  have hFlM := pitt_abs_pittDown_le hu hFmono hFM
  have hGlM := pitt_abs_pittDown_le hu hGmono hGM
  have hFu0 := pittUp_nonneg hu hFmono hF0
  have hGu0 := pittUp_nonneg hu hGmono hG0
  have hFl0 := pittDown_nonneg (u := u) hFM hF0
  have hGl0 := pittDown_nonneg (u := u) hGM hG0
  have hFuusc := pittUp_usc hFmono hFM
  have hGuusc := pittUp_usc hGmono hGM
  have hFllsc := pittDown_lsc hFmono hFM
  have hGllsc := pittDown_lsc hGmono hGM
  have hFum : Measurable (pittUp u F) := hFuusc.measurable
  have hGum : Measurable (pittUp u G) := hGuusc.measurable
  have hFlm : Measurable (pittDown u F) := hFllsc.measurable
  have hGlm : Measurable (pittDown u G) := hGllsc.measurable
  have hFGusc : UpperSemicontinuous fun x => pittUp u F x * pittUp u G x :=
    pitt_usc_mul hFuusc hGuusc hFu0 hGu0
  have hFumono : PittMono (pittUp u F) := fun x y h =>
    pittUp_dirMono hFmono hFM x y fun i _ => h i
  have hGumono : PittMono (pittUp u G) := fun x y h =>
    pittUp_dirMono hGmono hGM x y fun i _ => h i
  -- the coupling
  set Y : ℕ → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
    fun n p => A p.1 + Real.sqrt (1 / ((n : ℝ) + 1)) • p.2 with hYdef
  set Y0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
    fun p => A p.1 with hY0def
  have hYm : ∀ n, Measurable (Y n) := fun n => by simp only [hYdef]; fun_prop
  have hY0m : Measurable Y0 := by simp only [hY0def]; fun_prop
  have hYlim : ∀ p, Tendsto (fun n => Y n p) atTop (𝓝 (Y0 p)) := by
    intro p
    have h1 : Tendsto (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [Real.sqrt_zero] at this
    have h2 := (h1.smul_const p.2).const_add (A p.1)
    simpa only [zero_smul, add_zero] using h2
  have hlaw : ∀ n, P.map (Y n)
      = multivariateGaussian 0 (S + (1 / ((n : ℝ) + 1)) • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    intro n
    have hε : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    exact pitt_coupling_law hS hε
  have hlaw0 : P.map Y0 = multivariateGaussian 0 S := pitt_coupling_law_zero
  -- the inequality for each `n`
  have hH : ∀ n, (∫ ω, pittDown u F (Y n ω) ∂P) * (∫ ω, pittDown u G (Y n ω) ∂P)
      ≤ ∫ ω, pittUp u F (Y n ω) * pittUp u G (Y n ω) ∂P := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hn := hnd _ (pitt_posDef_add hS hε) (pitt_entries_add hSnn hε.le) (pittUp u F)
      (pittUp u G) hFum hGum ⟨M, hFuM⟩ ⟨M, hGuM⟩ hFumono hGumono
    rw [← hlaw n, integral_map (hYm n).aemeasurable hFum.aestronglyMeasurable,
      integral_map (hYm n).aemeasurable hGum.aestronglyMeasurable,
      integral_map (f := fun x => pittUp u F x * pittUp u G x) (hYm n).aemeasurable
        (hFum.mul hGum).aestronglyMeasurable] at hn
    have hint : ∀ {h : EuclideanSpace ℝ (Fin k) → ℝ}, Measurable h → (∀ x, |h x| ≤ M) →
        Integrable (fun ω => h (Y n ω)) P := fun hm hb =>
      pitt_integrable_of_bound (hm.comp (hYm n)) (M := M) fun ω => hb _
    have hFle : ∫ ω, pittDown u F (Y n ω) ∂P ≤ ∫ ω, pittUp u F (Y n ω) ∂P :=
      integral_mono (hint hFlm hFlM) (hint hFum hFuM) fun ω =>
        (pittDown_le hu hFmono _).trans (pitt_le_pittUp hu hFmono _)
    have hGle : ∫ ω, pittDown u G (Y n ω) ∂P ≤ ∫ ω, pittUp u G (Y n ω) ∂P :=
      integral_mono (hint hGlm hGlM) (hint hGum hGuM) fun ω =>
        (pittDown_le hu hGmono _).trans (pitt_le_pittUp hu hGmono _)
    calc (∫ ω, pittDown u F (Y n ω) ∂P) * (∫ ω, pittDown u G (Y n ω) ∂P)
        ≤ (∫ ω, pittUp u F (Y n ω) ∂P) * (∫ ω, pittUp u G (Y n ω) ∂P) :=
          mul_le_mul hFle hGle (integral_nonneg fun ω => hGl0 _)
            (integral_nonneg fun ω => hFu0 _)
      _ ≤ _ := hn
  -- pass to the limit
  have hlim := pitt_limit_ineq P hM0
    (fun n ω => pittDown u F (Y n ω)) (fun n ω => pittDown u G (Y n ω))
    (fun n ω => pittUp u F (Y n ω) * pittUp u G (Y n ω))
    (fun ω => pittDown u F (Y0 ω)) (fun ω => pittDown u G (Y0 ω))
    (fun ω => pittUp u F (Y0 ω) * pittUp u G (Y0 ω))
    (fun n => hFlm.comp (hYm n)) (fun n => hGlm.comp (hYm n))
    (fun n => (hFum.mul hGum).comp (hYm n))
    (hFlm.comp hY0m) (hGlm.comp hY0m) ((hFum.mul hGum).comp hY0m)
    (fun n ω => hFl0 _) (fun n ω => (le_abs_self _).trans (hFlM _))
    (fun n ω => hGl0 _) (fun n ω => (le_abs_self _).trans (hGlM _))
    (fun n ω => mul_nonneg (hFu0 _) (hGu0 _))
    (fun n ω => mul_le_mul ((le_abs_self _).trans (hFuM _)) ((le_abs_self _).trans (hGuM _))
      (hGu0 _) hM0)
    (fun ω => hFl0 _) (fun ω => (le_abs_self _).trans (hFlM _))
    (fun ω => hGl0 _) (fun ω => (le_abs_self _).trans (hGlM _))
    (fun ω => mul_nonneg (hFu0 _) (hGu0 _))
    (fun ω => mul_le_mul ((le_abs_self _).trans (hFuM _)) ((le_abs_self _).trans (hGuM _))
      (hGu0 _) hM0)
    (fun ω x hx => (hYlim ω).eventually (hFllsc (Y0 ω) x hx))
    (fun ω x hx => (hYlim ω).eventually (hGllsc (Y0 ω) x hx))
    (fun ω x hx => (hYlim ω).eventually (hFGusc (Y0 ω) x hx))
    hH
  -- replace the envelopes by `f`, `g` almost everywhere
  have hNF := pitt_stdGaussian_null_jumps A w hAw hu hFmono hFM
  have hNG := pitt_stdGaussian_null_jumps A w hAw hu hGmono hGM
  have hae : ∀ᵐ ω ∂P, pittUp u F (A ω.1) = pittDown u F (A ω.1)
      ∧ pittUp u G (A ω.1) = pittDown u G (A ω.1) := by
    rw [ae_iff]
    have hsub : {ω : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) | ¬ (pittUp u F (A ω.1)
          = pittDown u F (A ω.1) ∧ pittUp u G (A ω.1) = pittDown u G (A ω.1))}
        ⊆ ({z | pittUp u F (A z) ≠ pittDown u F (A z)}
            ∪ {z | pittUp u G (A z) ≠ pittDown u G (A z)}) ×ˢ (Set.univ : Set _) := by
      intro ω hω
      simp only [Set.mem_setOf_eq, not_and_or] at hω
      simp only [Set.mem_prod, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, and_true]
      exact hω
    refine measure_mono_null hsub ?_
    rw [hP, Measure.prod_prod, measure_union_null hNF hNG, zero_mul]
  have hFeq : ∀ᵐ ω ∂P, pittDown u F (Y0 ω) = f (Y0 ω) := by
    filter_upwards [hae] with ω hω
    exact le_antisymm ((pittDown_le hu hFmono (A ω.1)).trans (hFA _).le)
      ((hFA _).symm.le.trans ((pitt_le_pittUp hu hFmono _).trans hω.1.le))
  have hGeq : ∀ᵐ ω ∂P, pittDown u G (Y0 ω) = g (Y0 ω) := by
    filter_upwards [hae] with ω hω
    exact le_antisymm ((pittDown_le hu hGmono (A ω.1)).trans (hGA _).le)
      ((hGA _).symm.le.trans ((pitt_le_pittUp hu hGmono _).trans hω.2.le))
  have hFGeq : ∀ᵐ ω ∂P, pittUp u F (Y0 ω) * pittUp u G (Y0 ω) = f (Y0 ω) * g (Y0 ω) := by
    filter_upwards [hae] with ω hω
    have h1 : pittUp u F (A ω.1) = f (A ω.1) :=
      le_antisymm (hω.1.le.trans ((pittDown_le hu hFmono _).trans (hFA _).le))
        ((hFA _).symm.le.trans (pitt_le_pittUp hu hFmono _))
    have h2 : pittUp u G (A ω.1) = g (A ω.1) :=
      le_antisymm (hω.2.le.trans ((pittDown_le hu hGmono _).trans (hGA _).le))
        ((hGA _).symm.le.trans (pitt_le_pittUp hu hGmono _))
    show pittUp u F (A ω.1) * pittUp u G (A ω.1) = f (A ω.1) * g (A ω.1)
    rw [h1, h2]
  have e1 : ∫ ω, pittDown u F (Y0 ω) ∂P = ∫ ω, f (Y0 ω) ∂P := integral_congr_ae hFeq
  have e2 : ∫ ω, pittDown u G (Y0 ω) ∂P = ∫ ω, g (Y0 ω) ∂P := integral_congr_ae hGeq
  have e3 : ∫ ω, pittUp u F (Y0 ω) * pittUp u G (Y0 ω) ∂P = ∫ ω, f (Y0 ω) * g (Y0 ω) ∂P :=
    integral_congr_ae hFGeq
  beta_reduce at hlim
  rw [e1, e2, e3] at hlim
  rw [← hlaw0, integral_map hY0m.aemeasurable hfm.aestronglyMeasurable,
    integral_map hY0m.aemeasurable hgm.aestronglyMeasurable,
    integral_map (f := fun x => f x * g x) hY0m.aemeasurable (hfm.mul hgm).aestronglyMeasurable]
  exact hlim

/-- **Pitt's Gaussian association theorem** for an arbitrary positive semidefinite covariance with
nonnegative entries and bounded Borel nondecreasing functions, from the nondegenerate case.
The reduction to nonnegative functions adds the (constant) bounds. -/
theorem pitt_full (k : ℕ) (hnd : PittNondegStmt k) : PittFullStmt k := by
  intro S hS hSnn f g hfm hgm hfb hgb hfmono hgmono
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨Mg, hMg⟩ := hgb
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  set ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S with hν
  have hfi : Integrable f ν := pitt_integrable_of_bound hfm hMf
  have hgi : Integrable g ν := pitt_integrable_of_bound hgm hMg
  have hfgi : Integrable (fun x => f x * g x) ν :=
    pitt_integrable_of_bound (hfm.mul hgm) (M := Mf * Mg) fun x => by
      rw [abs_mul]; exact mul_le_mul (hMf x) (hMg x) (abs_nonneg _) hMf0
  have hmain := pitt_full_nonneg hnd hS hSnn (f := fun x => f x + Mf) (g := fun x => g x + Mg)
    (hfm.add_const Mf) (hgm.add_const Mg) (M := 2 * Mf + 2 * Mg)
    (fun x => by
      have := abs_le.1 (hMf x)
      rw [abs_le]; constructor <;> linarith)
    (fun x => by
      have := abs_le.1 (hMg x)
      rw [abs_le]; constructor <;> linarith)
    (fun x => by linarith [(abs_le.1 (hMf x)).1])
    (fun x => by linarith [(abs_le.1 (hMg x)).1])
    (fun x y h => by have := hfmono x y h; simp only; linarith)
    (fun x y h => by have := hgmono x y h; simp only; linarith)
  have e1 : ∫ x, (f x + Mf) ∂ν = (∫ x, f x ∂ν) + Mf := by
    rw [integral_add hfi (integrable_const Mf)]; simp
  have e2 : ∫ x, (g x + Mg) ∂ν = (∫ x, g x ∂ν) + Mg := by
    rw [integral_add hgi (integrable_const Mg)]; simp
  have e3 : ∫ x, (f x + Mf) * (g x + Mg) ∂ν
      = (∫ x, f x * g x ∂ν) + Mg * (∫ x, f x ∂ν) + (Mf * (∫ x, g x ∂ν) + Mf * Mg) := by
    have : (fun x => (f x + Mf) * (g x + Mg))
        = fun x => (f x * g x + Mg * f x) + (Mf * g x + Mf * Mg) := by
      funext x; ring
    have i1 : Integrable (fun x => f x * g x + Mg * f x) ν := hfgi.add (hfi.const_mul Mg)
    have i2 : Integrable (fun x => Mf * g x + Mf * Mg) ν :=
      (hgi.const_mul Mf).add (integrable_const _)
    rw [this, integral_add i1 i2, integral_add hfgi (hfi.const_mul Mg),
      integral_add (hgi.const_mul Mf) (integrable_const _), integral_const_mul,
      integral_const_mul]
    simp
  rw [e1, e2, e3] at hmain
  nlinarith [hmain]

end Main

end LatticeProb
