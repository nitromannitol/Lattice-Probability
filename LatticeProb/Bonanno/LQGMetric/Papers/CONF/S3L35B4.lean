/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L32
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3EMeas

/-!
# CONF Lemma 3.5 from the D110 leaves (task P2-CONF35b)

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`confluence-final.tex` C:1169–1172 (proof of Lemma 3.2: "the collection of open sets
`𝒰_r(z;δ)` is finite, and is equal to `r𝒰_1(0;δ) + z`"; a bound for each fixed `U`, then a union
over the finitely many `U`).

* `confHarmBound_of_U : CONFHarmBoundU → CONFHarmBound`: the finite union over `T` (C:1169).
  The index set `confSqIdx (δr) z 𝔸_{3r,4r}(z)` lies in the box `sqBox δ`, independent of `z, r`.
* `CONFHarmBoundU` (proved in S3L35B6/B9): the bound for one `T`, uniform
  in `z, r` and in the field (C:1170–1172: a.s. finiteness of `sup_{U_{δ/4}} |𝔥^U|` plus scale
  and translation invariance of the law of `h` modulo constants).
* `confLem3_5_of_B : CONFHarmExists → CONFHarmBoundU → Blueprint.CONFLem3_5`, with
  `CONFHarmLocN` from `confHarmLocN_of_exists` (S3L35B1) and CONF L2.12 (1) from
  `confLem2_12aP` (S3L35B3, proved from LM L3.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **the harmonic-part bound for one `U = confU r δ z T`** (CONF C:1170–1172), uniform in the
scale `r`, the centre `z` and the field. -/
def CONFHarmBoundU : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ T : Finset (ℤ × ℤ), ∀ β : ℝ, 0 < β → ∃ A : ℝ, 0 < A ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
        P {ω | ∃ u ∈ innerPart (confU r δ z T) (δ * r / 4),
          A < |harmPart P h (confU r δ z T) ω u - circleAvg (h ω) r z|} ≤ ENNReal.ofReal β

/-- the box of square indices `[-⌈4/δ⌉-1, ⌈4/δ⌉]²` -/
def sqBox (δ : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-⌈4 / δ⌉ - 1) ⌈4 / δ⌉ ×ˢ Finset.Icc (-⌈4 / δ⌉ - 1) ⌈4 / δ⌉

theorem int_mem_box {δ r x : ℝ} (hδ : 0 < δ) (hr : 0 < r) {k : ℤ} (hx : |x| < 4 * r)
    (h1 : k * (δ * r) ≤ x) (h2 : x ≤ (k + 1) * (δ * r)) :
    k ∈ Finset.Icc (-⌈4 / δ⌉ - 1) ⌈4 / δ⌉ := by
  rw [abs_lt] at hx
  have hc := Int.le_ceil (4 / δ)
  have hk1 : (k : ℝ) * δ < 4 := by nlinarith
  have hk2 : -4 < ((k : ℝ) + 1) * δ := by nlinarith
  have e1 : (k : ℝ) < 4 / δ := by rw [lt_div_iff₀ hδ]; linarith
  have e2 : -(4 / δ) < (k : ℝ) + 1 := by
    rw [neg_lt, lt_div_iff₀ hδ]; linarith
  rw [Finset.mem_Icc]
  constructor
  · have : ((-⌈4 / δ⌉ - 1 : ℤ) : ℝ) < k + 1 := by push_cast; linarith
    have : (-⌈4 / δ⌉ - 1 : ℤ) < k + 1 := by exact_mod_cast this
    omega
  · have : (k : ℝ) < ⌈4 / δ⌉ := by linarith
    have : k < ⌈4 / δ⌉ := by exact_mod_cast this
    omega

theorem confSqIdx_subset_sqBox {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (z : ℂ) {k : ℤ × ℤ}
    (hk : k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r))) : k ∈ sqBox δ := by
  obtain ⟨w, ⟨h1, h2, h3, h4⟩, -, hw⟩ := hk
  have hre : |w.re - z.re| < 4 * r :=
    lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hw
  have him : |w.im - z.im| < 4 * r :=
    lt_of_le_of_lt (by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _) hw
  exact Finset.mem_product.2 ⟨int_mem_box hδ hr hre (by linarith) (by linarith),
    int_mem_box hδ hr him (by linarith) (by linarith)⟩

/-- **`CONFHarmBound` from the one-`U` bound** (CONF C:1169: `𝒰_r(z;δ)` is finite). -/
theorem confHarmBound_of_U (HU : CONFHarmBoundU) : CONFHarmBound := by
  intro δ hδ hδ1 β hβ
  set I := sqBox δ
  set N := I.powerset.card with hN
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := Finset.card_pos.2 ⟨∅, Finset.empty_mem_powerset I⟩
    exact_mod_cast this
  choose A hA HA using fun T : Finset (ℤ × ℤ) => HU δ hδ hδ1 T (β / N) (by positivity)
  set A₀ := ∑ T ∈ I.powerset, A T with hA₀
  have hAle : ∀ T ∈ I.powerset, A T ≤ A₀ := fun T hT =>
    Finset.single_le_sum (f := A) (fun T _ => (hA T).le) hT
  have hA₀pos : 0 < A₀ :=
    lt_of_lt_of_le (hA ∅) (hAle ∅ (Finset.empty_mem_powerset I))
  refine ⟨A₀, hA₀pos, ?_⟩
  intro Ω _ P _ h hh z r hr
  have hsub : {ω | ∀ T : Finset (ℤ × ℤ),
      (∀ k ∈ T, k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r))) →
      ∀ u ∈ innerPart (confU r δ z T) (δ * r / 4),
        |harmPart P h (confU r δ z T) ω u - circleAvg (h ω) r z| ≤ A₀}ᶜ ⊆
      ⋃ T ∈ I.powerset, {ω | ∃ u ∈ innerPart (confU r δ z T) (δ * r / 4),
        A T < |harmPart P h (confU r δ z T) ω u - circleAvg (h ω) r z|} := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨T, hT, u, hu, hlt⟩ := hω
    have hTI : T ∈ I.powerset :=
      Finset.mem_powerset.2 fun k hk => confSqIdx_subset_sqBox hδ hr z (hT k hk)
    exact mem_biUnion hTI ⟨u, hu, lt_of_le_of_lt (hAle T hTI) hlt⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun T _ => HA T P h hh z r hr).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← hN, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp

end LQGMetric.CONF
