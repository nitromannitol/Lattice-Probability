/-
Doob's maximal inequality for the partial-sum process of an i.i.d. sequence of bounded,
mean-zero real-valued steps read off an arbitrary infinite product measure `Measure.infinitePi
(fun _ : ℕ => ν)` on `ℕ → S`, for an arbitrary measurable space `S` and reading function
`g : S → ℝ`.  This is the abstract content behind the walk's maximal-displacement tail bound: the
partial sum `S_k = ∑_{j<k} g (p j)` exits a window of half-width proportional to `√n` before time
`n` with probability at most `1/(16A²)`, uniformly in the horizon `n`.

The bridge from an abstract i.i.d. sequence to Mathlib's `MeasureTheory.Filtration`/
`Submartingale` framework goes through `Filtration.natural S hSm` (the smallest filtration making
`S` adapted): the increment `S_{k+1} - S_k = g (p k)` is independent of the coordinates before `k`
(`ProbabilityTheory.indep_iSup_of_disjoint`, fed by `iIndepFun_infinitePi`), hence independent of
`Filtration.natural S hSm k` (a coarser σ-algebra), hence has conditional mean zero
(`MeasureTheory.condExp_indep_eq`), which gives both the martingale property of `S` and the exact
conditional increment identity `E[(S_{k+1})² - (S_k)² | 𝒢_k] = ∫ g² dν` that makes `S²` a
submartingale with `E[(S_n)²] ≤ n·B²` when `|g| ≤ B` everywhere.
-/
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb.DoobMaximal

variable {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (g : S → ℝ)

/-- **The i.i.d. product law of the step sequence.** -/
def stepsLaw : Measure (ℕ → S) := Measure.infinitePi fun _ : ℕ => ν

instance : IsProbabilityMeasure (stepsLaw ν) := by unfold stepsLaw; infer_instance

/-- **The explicit partial sum** of the reading function `g` along the step sequence. -/
def partialSum (k : ℕ) (p : ℕ → S) : ℝ := ∑ j ∈ Finset.range k, g (p j)

theorem measurable_partialSum (hg : Measurable g) (k : ℕ) : Measurable (partialSum g k) :=
  Finset.measurable_sum _ fun j _ => hg.comp (measurable_pi_apply j)

theorem stronglyMeasurable_partialSum (hg : Measurable g) (k : ℕ) :
    StronglyMeasurable (partialSum g k) :=
  (measurable_partialSum g hg k).stronglyMeasurable

omit [MeasurableSpace S] in
theorem abs_partialSum_le {B : ℝ} (hB : ∀ s, |g s| ≤ B) (k : ℕ) (p : ℕ → S) :
    |partialSum g k p| ≤ k * B := by
  calc |partialSum g k p| ≤ ∑ j ∈ Finset.range k, |g (p j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, B := Finset.sum_le_sum fun j _ => hB (p j)
    _ = k * B := by rw [Finset.sum_const, Finset.card_range]; ring

/-- **The coordinate σ-algebras of the step sequence are jointly independent.** -/
theorem iIndep_coord :
    iIndep (fun j : ℕ => MeasurableSpace.comap (fun p : ℕ → S => p j) inferInstance)
      (stepsLaw ν) := by
  exact (iIndepFun_infinitePi (Ω := fun _ : ℕ => S) (P := fun _ : ℕ => ν)
    (X := fun (_ : ℕ) (s : S) => s) (fun _ => measurable_id)).iIndep

/-- **The natural filtration of `partialSum`.** -/
def filtration (hg : Measurable g) : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) :=
  Filtration.natural (partialSum g) (stronglyMeasurable_partialSum g hg)

theorem stronglyAdapted_filtration (hg : Measurable g) :
    StronglyAdapted (filtration g hg) (partialSum g) :=
  Filtration.stronglyAdapted_natural (stronglyMeasurable_partialSum g hg)

/-- **`filtration g hg k` sits inside the σ-algebra of the coordinates below `k`**: every
`partialSum g j` for `j ≤ k` is a finite sum of terms reading coordinates `< j ≤ k`. -/
theorem filtration_le_iSup_coord (hg : Measurable g) (k : ℕ) :
    filtration g hg k ≤ ⨆ i ∈ Set.Iio k,
      MeasurableSpace.comap (fun p : ℕ → S => p i) inferInstance := by
  set M : MeasurableSpace (ℕ → S) :=
    ⨆ i ∈ Set.Iio k, MeasurableSpace.comap (fun p : ℕ → S => p i) inferInstance
    with hMdef
  show (⨆ j ≤ k, MeasurableSpace.comap (partialSum g j) inferInstance) ≤ M
  refine iSup₂_le fun j hjk => ?_
  rw [← measurable_iff_comap_le]
  show Measurable[M] (fun p => ∑ i ∈ Finset.range j, g (p i))
  refine Finset.measurable_sum (Finset.range j) fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hik : i ∈ Set.Iio k := lt_of_lt_of_le hi hjk
  have heval : Measurable[M] (fun p : ℕ → S => p i) := by
    rw [hMdef]
    exact measurable_iff_comap_le.mpr
      (le_biSup (fun i => MeasurableSpace.comap (fun p : ℕ → S => p i) inferInstance) hik)
  exact hg.comp heval

/-- **The `k`-th coordinate is independent of `filtration g hg k`.** -/
theorem indep_coord_filtration (hg : Measurable g) (k : ℕ) :
    Indep (MeasurableSpace.comap (fun p : ℕ → S => p k) inferInstance)
      (filtration g hg k) (stepsLaw ν) := by
  have h_le : ∀ j : ℕ, MeasurableSpace.comap (fun p : ℕ → S => p j) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → S)) :=
    fun j => measurable_iff_comap_le.mp (measurable_pi_apply j)
  have hST : Disjoint (Set.Iio k) ({k} : Set ℕ) := by
    simp [Set.disjoint_singleton_right]
  have h1 := indep_iSup_of_disjoint h_le (iIndep_coord ν) hST
  rw [_root_.iSup_singleton] at h1
  exact indep_of_indep_of_le h1.symm le_rfl (filtration_le_iSup_coord g hg k)

/-- **A single reading has mean `∫ g dν`.** -/
theorem integral_g_eval (hg : Measurable g) (k : ℕ) :
    ∫ p : ℕ → S, g (p k) ∂(stepsLaw ν) = ∫ s, g s ∂ν := by
  have hmap : (stepsLaw ν).map (fun p : ℕ → S => p k) = ν := by
    unfold stepsLaw; exact Measure.infinitePi_map_eval _ _
  have hpull : ∫ s, g s ∂((stepsLaw ν).map (fun p : ℕ → S => p k))
      = ∫ p : ℕ → S, g (p k) ∂(stepsLaw ν) :=
    integral_map (measurable_pi_apply k).aemeasurable hg.aestronglyMeasurable
  rw [hmap] at hpull
  exact hpull.symm

/-- **A single reading, squared, has mean `∫ g² dν`.** -/
theorem integral_sq_g_eval (hg : Measurable g) (k : ℕ) :
    ∫ p : ℕ → S, (g (p k)) ^ 2 ∂(stepsLaw ν) = ∫ s, (g s) ^ 2 ∂ν := by
  have hmap : (stepsLaw ν).map (fun p : ℕ → S => p k) = ν := by
    unfold stepsLaw; exact Measure.infinitePi_map_eval _ _
  have hpull : ∫ s, (g s) ^ 2 ∂((stepsLaw ν).map (fun p : ℕ → S => p k))
      = ∫ p : ℕ → S, (g (p k)) ^ 2 ∂(stepsLaw ν) :=
    integral_map (measurable_pi_apply k).aemeasurable (hg.pow_const 2).aestronglyMeasurable
  rw [hmap] at hpull
  exact hpull.symm

/-- **If `g` has mean zero, the increment of `partialSum` has conditional mean zero.** -/
theorem condExp_g_filtration (hg : Measurable g) (_hInt : Integrable g ν)
    (hmean : ∫ s, g s ∂ν = 0) (k : ℕ) :
    (stepsLaw ν)[fun p => g (p k) | filtration g hg k] =ᵐ[stepsLaw ν] 0 := by
  have hSM : StronglyMeasurable[MeasurableSpace.comap
      (fun p : ℕ → S => p k) inferInstance] (fun p : ℕ → S => g (p k)) := by
    have heval : Measurable[MeasurableSpace.comap (fun p : ℕ → S => p k)
        inferInstance] (fun p : ℕ → S => p k) :=
      measurable_iff_comap_le.mpr le_rfl
    exact (hg.comp heval).stronglyMeasurable
  have hle₁ : MeasurableSpace.comap (fun p : ℕ → S => p k) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → S)) :=
    measurable_iff_comap_le.mp (measurable_pi_apply k)
  have h := condExp_indep_eq (μ := stepsLaw ν) (m₁ := MeasurableSpace.comap
      (fun p : ℕ → S => p k) inferInstance) (m₂ := filtration g hg k)
    hle₁ ((filtration g hg).le k) hSM (indep_coord_filtration ν g hg k)
  filter_upwards [h] with p hp
  simp only [Pi.zero_apply]
  rw [hp, integral_g_eval ν g hg k]
  exact hmean

theorem integrable_partialSum {B : ℝ} (hg : Measurable g) (hB : ∀ s, |g s| ≤ B) (k : ℕ) :
    Integrable (partialSum g k) (stepsLaw ν) :=
  Integrable.mono' (integrable_const (k * B : ℝ))
    (measurable_partialSum g hg k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact abs_partialSum_le g hB k p)

theorem integrable_partialSum_sq {B : ℝ} (hg : Measurable g) (hB : ∀ s, |g s| ≤ B) (k : ℕ) :
    Integrable (fun p => (partialSum g k p) ^ 2) (stepsLaw ν) := by
  refine Integrable.mono' (integrable_const ((k * B : ℝ) ^ 2))
    ((measurable_partialSum g hg k).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (partialSum g k p) ^ 2 = |partialSum g k p| ^ 2 := (sq_abs _).symm
    _ ≤ (k * B : ℝ) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_partialSum_le g hB k p) 2

/-- **`partialSum` is a martingale for its own natural filtration, provided `g` has mean
zero.** -/
theorem martingale_partialSum {B : ℝ} (hg : Measurable g) (hB : ∀ s, |g s| ≤ B)
    (hInt : Integrable g ν) (hmean : ∫ s, g s ∂ν = 0) :
    Martingale (partialSum g) (filtration g hg) (stepsLaw ν) := by
  refine martingale_of_condExp_sub_eq_zero_nat (stronglyAdapted_filtration g hg)
    (integrable_partialSum ν g hg hB) fun i => ?_
  have heq : (partialSum g (i + 1) - partialSum g i) = fun p => g (p i) := by
    funext p
    simp only [Pi.sub_apply]
    show (∑ j ∈ Finset.range (i + 1), g (p j))
        - (∑ j ∈ Finset.range i, g (p j)) = g (p i)
    rw [Finset.sum_range_succ]
    ring
  rw [heq]
  exact condExp_g_filtration ν g hg hInt hmean i

/-- **The conditional increment of the squared partial sum is the constant `∫ g² dν`.** -/
theorem condExp_sq_partialSum_sub {B : ℝ} (hg : Measurable g) (hB : ∀ s, |g s| ≤ B)
    (hInt : Integrable g ν) (hmean : ∫ s, g s ∂ν = 0)
    (_hInt2 : Integrable (fun s => (g s) ^ 2) ν) (i : ℕ) :
    (stepsLaw ν)[fun p => (partialSum g (i + 1) p) ^ 2 - (partialSum g i p) ^ 2 |
        filtration g hg i] =ᵐ[stepsLaw ν] fun _ => ∫ s, (g s) ^ 2 ∂ν := by
  have hstepMeas : Measurable (fun p : ℕ → S => g (p i)) := hg.comp (measurable_pi_apply i)
  have hpt : ∀ p : ℕ → S, (partialSum g (i + 1) p) ^ 2 - (partialSum g i p) ^ 2
      = (2 * partialSum g i p) * g (p i) + (g (p i)) ^ 2 := by
    intro p
    have hsucc : partialSum g (i + 1) p = partialSum g i p + g (p i) := by
      show (∑ j ∈ Finset.range (i + 1), g (p j))
          = (∑ j ∈ Finset.range i, g (p j)) + g (p i)
      rw [Finset.sum_range_succ]
    rw [hsucc]; ring
  have heq : (fun p => (partialSum g (i + 1) p) ^ 2 - (partialSum g i p) ^ 2)
      = (fun p => (2 * partialSum g i p) * g (p i)) + fun p => (g (p i)) ^ 2 := by
    funext p
    rw [Pi.add_apply]
    exact hpt p
  rw [heq]
  have hle : filtration g hg i ≤ (inferInstance : MeasurableSpace (ℕ → S)) :=
    (filtration g hg).le i
  have hSMf : StronglyMeasurable[filtration g hg i] (fun p => 2 * partialSum g i p) :=
    stronglyMeasurable_const.mul (stronglyAdapted_filtration g hg i)
  have hfbound : ∀ᵐ p ∂(stepsLaw ν), ‖2 * partialSum g i p‖ ≤ (2 * i * B : ℝ) := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    have := abs_partialSum_le g hB i p
    nlinarith [abs_nonneg (partialSum g i p)]
  have hgint : Integrable (fun p => g (p i)) (stepsLaw ν) :=
    Integrable.mono' (integrable_const B) hstepMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact hB (p i))
  have hmul := condExp_stronglyMeasurable_mul_of_bound hle hSMf hgint (2 * i * B) hfbound
  have hmulEq : (fun p => 2 * partialSum g i p) * (fun p => g (p i))
      = fun p => 2 * partialSum g i p * g (p i) := by
    funext p; rw [Pi.mul_apply]
  rw [hmulEq] at hmul
  have hint1 : Integrable (fun p => (2 * partialSum g i p) * g (p i)) (stepsLaw ν) := by
    refine Integrable.mono' (integrable_const (2 * i * B * B : ℝ)) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact (((measurable_partialSum g hg i).const_mul 2).mul hstepMeas).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |2 * partialSum g i p| ≤ (2 * i * B : ℝ) := by
        rw [abs_mul, abs_two]
        have := abs_partialSum_le g hB i p
        nlinarith [abs_nonneg (partialSum g i p)]
      have h2 : |g (p i)| ≤ B := hB (p i)
      have h2' : (0:ℝ) ≤ B := le_trans (abs_nonneg _) h2
      calc |2 * partialSum g i p| * |g (p i)| ≤ (2 * i * B : ℝ) * B :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 2 * i * B * B := by ring
  have hint2 : Integrable (fun p => (g (p i)) ^ 2) (stepsLaw ν) := by
    refine Integrable.mono' (integrable_const (B ^ 2 : ℝ)) (hstepMeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (g (p i)) ^ 2 = |g (p i)| ^ 2 := (sq_abs _).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB (p i)) 2
  have hcombine := condExp_add hint1 hint2 (filtration g hg i)
  have hsqEval : (stepsLaw ν)[fun p => (g (p i)) ^ 2 | filtration g hg i]
      =ᵐ[stepsLaw ν] fun _ => ∫ s, (g s) ^ 2 ∂ν := by
    have hSM2 : StronglyMeasurable[MeasurableSpace.comap
        (fun p : ℕ → S => p i) inferInstance] (fun p : ℕ → S => (g (p i)) ^ 2) := by
      have heval : Measurable[MeasurableSpace.comap (fun p : ℕ → S => p i)
          inferInstance] (fun p : ℕ → S => p i) :=
        measurable_iff_comap_le.mpr le_rfl
      exact ((hg.comp heval).pow_const 2).stronglyMeasurable
    have hle₁ : MeasurableSpace.comap (fun p : ℕ → S => p i) inferInstance ≤
        (inferInstance : MeasurableSpace (ℕ → S)) :=
      measurable_iff_comap_le.mp (measurable_pi_apply i)
    have h := condExp_indep_eq (μ := stepsLaw ν) (m₁ := MeasurableSpace.comap
        (fun p : ℕ → S => p i) inferInstance) (m₂ := filtration g hg i)
      hle₁ ((filtration g hg).le i) hSM2 (indep_coord_filtration ν g hg i)
    filter_upwards [h] with p hp
    rw [hp]
    exact integral_sq_g_eval ν g hg i
  filter_upwards [hcombine, hmul, condExp_g_filtration ν g hg hInt hmean i, hsqEval]
    with p hp1 hp2 hp3 hp4
  rw [hp1]
  simp only [Pi.add_apply]
  rw [hp2]
  simp only [Pi.mul_apply, Pi.zero_apply] at hp3 ⊢
  rw [hp3, mul_zero, zero_add, hp4]

/-- **`(partialSum g)²` is a submartingale for `filtration g hg`, provided `g` has mean
zero.** -/
theorem submartingale_partialSum_sq {B : ℝ} (hg : Measurable g) (hB : ∀ s, |g s| ≤ B)
    (hInt : Integrable g ν) (hmean : ∫ s, g s ∂ν = 0)
    (hInt2 : Integrable (fun s => (g s) ^ 2) ν) :
    Submartingale (fun k p => (partialSum g k p) ^ 2) (filtration g hg) (stepsLaw ν) := by
  refine submartingale_of_condExp_sub_nonneg_nat
    (fun i => ((stronglyAdapted_filtration g hg i)).pow 2) (integrable_partialSum_sq ν g hg hB)
    fun i => ?_
  have heq : ((fun p => (partialSum g (i + 1) p) ^ 2) - fun p => (partialSum g i p) ^ 2)
      = fun p => (partialSum g (i + 1) p) ^ 2 - (partialSum g i p) ^ 2 := by
    funext p; simp only [Pi.sub_apply]
  rw [heq]
  have hnonneg : (0:ℝ) ≤ ∫ s, (g s) ^ 2 ∂ν := integral_nonneg fun s => sq_nonneg _
  filter_upwards [condExp_sq_partialSum_sub ν g hg hB hInt hmean hInt2 i] with p hp
  rw [hp]; exact hnonneg

/-- **`E[(S_n)²] ≤ n·B²`**: the second moment of the partial sum, uniform in the mean-zero
step's law, by induction using the exact conditional increment and the tower property. -/
theorem integral_partialSum_sq_le {B : ℝ} (hg : Measurable g) (hB : ∀ s, |g s| ≤ B)
    (hInt : Integrable g ν) (hmean : ∫ s, g s ∂ν = 0)
    (hInt2 : Integrable (fun s => (g s) ^ 2) ν) (n : ℕ) :
    ∫ p, (partialSum g n p) ^ 2 ∂(stepsLaw ν) ≤ n * B ^ 2 := by
  have hgsqB : ∫ s, (g s) ^ 2 ∂ν ≤ B ^ 2 := by
    have hmono : ∫ s, (g s) ^ 2 ∂ν ≤ ∫ _s : S, B ^ 2 ∂ν :=
      integral_mono hInt2 (integrable_const _) fun s => by
        calc (g s) ^ 2 = |g s| ^ 2 := (sq_abs _).symm
          _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB s) 2
    rwa [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul] at hmono
  induction n with
  | zero =>
    have : (fun p : ℕ → S => (partialSum g 0 p) ^ 2) = fun _ => (0 : ℝ) := by
      funext p; show (partialSum g 0 p) ^ 2 = 0
      show (∑ _j ∈ Finset.range 0, g (p _j)) ^ 2 = 0
      simp
    rw [this]; simp
  | succ i ih =>
    have htower := integral_condExp (μ := stepsLaw ν)
      (f := fun p => (partialSum g (i + 1) p) ^ 2 - (partialSum g i p) ^ 2)
      ((filtration g hg).le i)
    have hrhs : (∫ p, (stepsLaw ν)[fun p => (partialSum g (i + 1) p) ^ 2 -
        (partialSum g i p) ^ 2 | filtration g hg i] p ∂(stepsLaw ν))
        = ∫ _p : ℕ → S, (∫ s, (g s) ^ 2 ∂ν) ∂(stepsLaw ν) :=
      integral_congr_ae (condExp_sq_partialSum_sub ν g hg hB hInt hmean hInt2 i)
    rw [hrhs] at htower
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul] at htower
    have hsub : (∫ p, ((partialSum g (i + 1) p) ^ 2 - (partialSum g i p) ^ 2) ∂(stepsLaw ν))
        = (∫ p, (partialSum g (i + 1) p) ^ 2 ∂(stepsLaw ν))
          - ∫ p, (partialSum g i p) ^ 2 ∂(stepsLaw ν) :=
      integral_sub (integrable_partialSum_sq ν g hg hB (i + 1)) (integrable_partialSum_sq ν g hg hB i)
    rw [hsub] at htower
    have heqn : (∫ p, (partialSum g (i + 1) p) ^ 2 ∂(stepsLaw ν))
        = (∫ s, (g s) ^ 2 ∂ν) + ∫ p, (partialSum g i p) ^ 2 ∂(stepsLaw ν) := by linarith
    rw [heqn]
    push_cast
    nlinarith [ih]

/-- **Doob's maximal inequality for the partial sum of a mean-zero, bounded-step i.i.d.
sequence, uniform in `n`.** The event that the partial sum ever exits a window of half-width
`4AB√n` before time `n` has probability at most `1/(16A²)`. -/
theorem measureReal_sup_partialSum_sq_le {B : ℝ} (hg : Measurable g) (hB : ∀ s, |g s| ≤ B)
    (hBpos : 0 < B) (hInt : Integrable g ν) (hmean : ∫ s, g s ∂ν = 0)
    (hInt2 : Integrable (fun s => (g s) ^ 2) ν) (n : ℕ) (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A) :
    (stepsLaw ν).real {p | ∃ k ≤ n, (4 * A * B * Real.sqrt n) ≤ |partialSum g k p|} ≤
      1 / (16 * A ^ 2) := by
  set ε : ℝ≥0 := (16 * A ^ 2 * B ^ 2 * n : ℝ).toNNReal with hεdef
  have hεcoe : (ε : ℝ) = 16 * A ^ 2 * B ^ 2 * n := by
    rw [hεdef, Real.coe_toNNReal]
    positivity
  have hmax := maximal_ineq (ε := ε)
    (submartingale_partialSum_sq ν g hg hB hInt hmean hInt2)
    (fun k => fun p => sq_nonneg (partialSum g k p)) n
  have hn2 : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsq : (4 * A * B * Real.sqrt n) ^ 2 = 16 * A ^ 2 * B ^ 2 * n := by
    have hring : (4 * A * B * Real.sqrt n) ^ 2 = 16 * A ^ 2 * B ^ 2 * (Real.sqrt n) ^ 2 := by
      ring
    rw [hring, hn2]
  have hynn : (0:ℝ) ≤ 4 * A * B * Real.sqrt n := by positivity
  have hset_eq : {ω : ℕ → S | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (partialSum g k ω) ^ 2}
      = {p | ∃ k ≤ n, (4 * A * B * Real.sqrt n) ≤ |partialSum g k p|} := by
    ext p
    simp only [Set.mem_setOf_eq]
    rw [Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hkle⟩
      rw [Finset.mem_range] at hk
      refine ⟨k, by omega, ?_⟩
      rw [hεcoe] at hkle
      have h1 : (4 * A * B * Real.sqrt n) ^ 2 ≤ (partialSum g k p) ^ 2 := by
        rw [hsq]; exact hkle
      have h2 : (4 * A * B * Real.sqrt n) ^ 2 ≤ |partialSum g k p| ^ 2 := by
        rwa [sq_abs]
      have := abs_le_of_sq_le_sq h2 (abs_nonneg _)
      rwa [abs_of_nonneg hynn] at this
    · rintro ⟨k, hk, hkle⟩
      refine ⟨k, by rw [Finset.mem_range]; omega, ?_⟩
      rw [hεcoe, ← hsq]
      calc (4 * A * B * Real.sqrt n) ^ 2 ≤ |partialSum g k p| ^ 2 :=
            pow_le_pow_left₀ hynn hkle 2
        _ = partialSum g k p ^ 2 := sq_abs _
  rw [hset_eq] at hmax
  have hbound : (∫ p in {p | ∃ k ≤ n, (4 * A * B * Real.sqrt n) ≤ |partialSum g k p|},
      (partialSum g n p) ^ 2 ∂(stepsLaw ν)) ≤ (n : ℝ) * B ^ 2 := by
    calc (∫ p in {p | ∃ k ≤ n, (4 * A * B * Real.sqrt n) ≤ |partialSum g k p|},
          (partialSum g n p) ^ 2 ∂(stepsLaw ν))
        ≤ ∫ p, (partialSum g n p) ^ 2 ∂(stepsLaw ν) :=
          setIntegral_le_integral (integrable_partialSum_sq ν g hg hB n)
            (Filter.Eventually.of_forall fun p => sq_nonneg _)
      _ ≤ (n : ℝ) * B ^ 2 := integral_partialSum_sq_le ν g hg hB hInt hmean hInt2 n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hεpos : (0 : ℝ) < ε := by rw [hεcoe]; positivity
  have h1 : (ε : ℝ≥0∞) * (stepsLaw ν) {p | ∃ k ≤ n, (4 * A * B * Real.sqrt n) ≤ |partialSum g k p|}
      ≤ ENNReal.ofReal ((n:ℝ) * B ^ 2) := hmax.trans (ENNReal.ofReal_le_ofReal hbound)
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity)] at h2
  rw [hεcoe] at h2
  rw [MeasureTheory.measureReal_def]
  have hA2 : (0 : ℝ) < 16 * A ^ 2 := by positivity
  rw [le_div_iff₀ hA2]
  have hB2 : (0:ℝ) < B ^ 2 := by positivity
  nlinarith [h2, hnpos, hB2]

end LatticeProb.DoobMaximal

end
