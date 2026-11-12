/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L13Cross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L13Approx
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L13Limit
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import LatticeProb.Bonanno.LQGMetric.Gaussian.AssociationSqrt
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.GaussFdd
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable

/-!
# DDDF Lemma 13 for general crossings `(K, A, B)` (task P2-DDDFRSW2)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 771–780 (`Lem:FKG`),
used in Step 2 of Prop 14 (l. 799–806) for the crossings of the ellipse `E_p` between marked
sub-arcs (DDDF apply Lemma 13 to these crossings, not only to rectangles). The proof is the one
of `L13.lean` (DF arXiv:1809.02607 §2.3, DF:226–252, with Pitt's theorem), with the rectangle
`R` replaced by a compact `K` with arcs `A, B ⊆ K`; the only new input is the finiteness of
`crossLenIn ξ 0 K A B` (some admissible path exists), which DDDF use implicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DDDF

variable {ξ : ℝ}

theorem crossLenIn_congr' {K A B : Set ℂ} {f g : ℂ → ℝ} (h : ∀ x ∈ K, f x = g x) :
    crossLenIn ξ f K A B = crossLenIn ξ g K A B := by
  have h1 := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := A) (B := B) (c := 0)
    (U := K) (f := f) (g := g) fun x hx => by rw [h x hx, sub_self, abs_zero]
  have h2 := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := A) (B := B) (c := 0)
    (U := K) (f := g) (g := f) fun x hx => by rw [h x hx, sub_self, abs_zero]
  simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h1 h2
  exact le_antisymm h1 h2

theorem crossLenIn_mono' (hξ : 0 ≤ ξ) (K A B : Set ℂ) {f g : ℂ → ℝ} (h : ∀ x, f x ≤ g x) :
    crossLenIn ξ f K A B ≤ crossLenIn ξ g K A B := by
  rw [crossLenIn_eq_biInf, crossLenIn_eq_biInf]
  refine iInf₂_mono fun P _ => ?_
  unfold lfppLen
  refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h _) hξ))
    (norm_nonneg _)

/-- a field bounded by `M` on `K` has finite crossing length when `crossLenIn ξ 0 K A B < ∞` -/
theorem crossLenIn_ne_top_of_bdd {K A B : Set ℂ} (hfin : crossLenIn ξ 0 K A B ≠ ⊤) {f : ℂ → ℝ}
    {M : ℝ} (hM : ∀ x ∈ K, |f x| ≤ M) : crossLenIn ξ f K A B ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    (crossLenIn_le_of_abs_sub_le (g := 0) fun x hx => by simpa using hM x hx)

/-- a continuous field on a compact `K` has finite crossing length when `crossLenIn ξ 0 K A B < ∞` -/
theorem crossLenIn_ne_top_of_cont {K A B : Set ℂ} (hK : IsCompact K)
    (hfin : crossLenIn ξ 0 K A B ≠ ⊤) {f : ℂ → ℝ} (hf : Continuous f) :
    crossLenIn ξ f K A B ≠ ⊤ := by
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn (continuous_abs.comp hf).continuousOn).isBounded
    |>.bddAbove
  exact crossLenIn_ne_top_of_bdd hfin fun x hx => hM ⟨x, hx, rfl⟩

/-- conversely, `crossLenIn ξ 0 K A B = ⊤` forces `crossLenIn ξ f K A B = ⊤` for bounded `f` -/
theorem crossLenIn_zero_ne_top {K A B : Set ℂ} {f : ℂ → ℝ} {M : ℝ} (hM : ∀ x ∈ K, |f x| ≤ M)
    (hf : crossLenIn ξ f K A B ≠ ⊤) : crossLenIn ξ 0 K A B ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf)
    (crossLenIn_le_of_abs_sub_le (f := 0) (g := f) fun x hx => by simpa using hM x hx)

theorem isUpperSet_crossUpper (hξ : 0 ≤ ξ) (k : ℕ) (D : Finset ℂ) {K A B : Set ℂ}
    (hfin : crossLenIn ξ 0 K A B ≠ ⊤) (a : ℝ) :
    IsUpperSet {v : D → ℝ | a < (crossLenIn ξ (blockField k D v) K A B).toReal} :=
  fun _ v' hvv' hv =>
  hv.trans_le (ENNReal.toReal_mono
    (crossLenIn_ne_top_of_bdd hfin fun x _ => abs_blockField_le k D v' x)
    (crossLenIn_mono' hξ K A B (blockField_mono k D hvv')))

theorem isOpen_crossUpper (k : ℕ) (D : Finset ℂ) {K A B : Set ℂ}
    (hfin : crossLenIn ξ 0 K A B ≠ ⊤) (a : ℝ) :
    IsOpen {v : D → ℝ | a < (crossLenIn ξ (blockField k D v) K A B).toReal} := by
  rw [Metric.isOpen_iff]
  intro v hv
  simp only [mem_ofPred_eq] at hv
  set b := (crossLenIn ξ (blockField k D v) K A B).toReal
  have hcont : Tendsto (fun η : ℝ => Real.exp (-(|ξ| * η)) * b) (𝓝 0) (𝓝 b) := by
    have : Continuous fun η : ℝ => Real.exp (-(|ξ| * η)) * b := by fun_prop
    simpa using this.tendsto 0
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds hv))
  refine ⟨δ, hδ, fun v' hv' => ?_⟩
  simp only [mem_ofPred_eq]
  rw [Metric.mem_ball, dist_eq_norm] at hv'
  have h1 : crossLenIn ξ (blockField k D v) K A B ≤
      ENNReal.ofReal (Real.exp (|ξ| * ‖v' - v‖)) * crossLenIn ξ (blockField k D v') K A B :=
    crossLenIn_le_of_abs_sub_le fun x _ => by
      rw [abs_sub_comm, ← norm_neg (v' - v), neg_sub]
      exact abs_blockField_sub_le k D v' v x |>.trans_eq (by rw [← norm_neg, neg_sub])
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (crossLenIn_ne_top_of_bdd hfin fun x _ => abs_blockField_le k D v' x)) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h2
  have h3 : Real.exp (-(|ξ| * ‖v' - v‖)) * b ≤
      (crossLenIn ξ (blockField k D v') K A B).toReal := by
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]; exact h2
  have h4 := hδb (show dist ‖v' - v‖ 0 < δ by simpa using hv')
  linarith

/-- `L(K, A, B; Y ∘ dyRound k) → L(K, A, B; Y)` for continuous `Y` (DF:229–233). -/
theorem tendsto_crossLenIn_dyRound {K A B : Set ℂ} (hK : IsCompact K)
    (hfin0 : crossLenIn ξ 0 K A B ≠ ⊤) {Y : ℂ → ℝ} (hY : Continuous Y) :
    Tendsto (fun k => (crossLenIn ξ (fun x => Y (dyRound k x)) K A B).toReal) atTop
      (𝓝 (crossLenIn ξ Y K A B).toReal) := by
  set b := (crossLenIn ξ Y K A B).toReal
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hK' : IsCompact (cthickening 2 K) := hK.cthickening
  have huc := (hK'.uniformContinuousOn_of_continuous hY.continuousOn)
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  set φ : ℝ → ℝ := fun η => (Real.exp (|ξ| * η) - 1) * Real.exp (|ξ| * η) * b
  have hφ : Tendsto φ (𝓝 0) (𝓝 0) := by
    have : Continuous φ := by fun_prop
    simpa [φ] using this.tendsto 0
  obtain ⟨δ0, hδ0, hδ0φ⟩ := Metric.eventually_nhds_iff.1 (hφ.eventually (gt_mem_nhds hε))
  set η := δ0 / 2
  have hη : 0 < η := by positivity
  have hηδ : η < δ0 := by simp only [η]; linarith
  have hφη : φ η < ε := hδ0φ (by rw [Real.dist_eq, sub_zero, abs_of_pos hη]; exact hηδ)
  obtain ⟨δ, hδ, hδY⟩ := huc η hη
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, fun k hk => ?_⟩
  have hclose : ∀ x ∈ K, |Y (dyRound k x) - Y x| ≤ η := fun x hx => by
    have hd := dist_dyRound_le k x
    have hpow : ((2 : ℝ) ^ k)⁻¹ ≤ (1 / 2) ^ N := by
      rw [← inv_pow, ← one_div]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have hle1 : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h1 : dyRound k x ∈ cthickening 2 K :=
      mem_cthickening_of_dist_le _ x _ _ hx (by linarith)
    have h2 : x ∈ cthickening 2 K := self_subset_cthickening _ hx
    have := hδY _ h1 _ h2 (by linarith)
    rw [Real.dist_eq] at this
    exact this.le
  have hfin : crossLenIn ξ Y K A B ≠ ∞ := crossLenIn_ne_top_of_cont hK hfin0 hY
  have h1 : crossLenIn ξ (fun x => Y (dyRound k x)) K A B ≤
      ENNReal.ofReal (Real.exp (|ξ| * η)) * crossLenIn ξ Y K A B :=
    crossLenIn_le_of_abs_sub_le hclose
  have h2 : crossLenIn ξ Y K A B ≤
      ENNReal.ofReal (Real.exp (|ξ| * η)) * crossLenIn ξ (fun x => Y (dyRound k x)) K A B :=
    crossLenIn_le_of_abs_sub_le fun x hx => by rw [abs_sub_comm]; exact hclose x hx
  have hfin' : crossLenIn ξ (fun x => Y (dyRound k x)) K A B ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
  have h1' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
  have h2' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin') h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h1' h2'
  set a := (crossLenIn ξ (fun x => Y (dyRound k x)) K A B).toReal
  set E := Real.exp (|ξ| * η)
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hφ' : φ η = (E - 1) * E * b := rfl
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1' (show 0 ≤ E - 1 by linarith)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **DDDF Lemma 13, positive association, for crossings of `(K, A, B)`** (DDDF l. 771–776, as
used at l. 803): `∏ P(L_i > a_i) ≤ P(⋂ {L_i > a_i})`. -/
theorem lemma13_cross (hξ : 0 ≤ ξ) {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x))
    (hG : ∀ D : Finset ℂ, HasGaussianLaw (fun ω (s : D) => Y s ω) P)
    (hcov : ∀ x y, 0 ≤ cov[Y x, Y y; P])
    {κ : Type*} [Fintype κ] (K A B : κ → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hfin : ∀ i, crossLenIn ξ 0 (K i) (A i) (B i) ≠ ⊤) (a : κ → ℝ) :
    ∏ i, P.real {ω | a i < (crossLenIn ξ (fun x => Y x ω) (K i) (A i) (B i)).toReal} ≤
      P.real (⋂ i, {ω | a i < (crossLenIn ξ (fun x => Y x ω) (K i) (A i) (B i)).toReal}) := by
  classical
  have hKb : Bornology.IsBounded (⋃ i, K i) := (isCompact_iUnion hK).isBounded
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Finset ℂ, ∀ k i, ∀ x ∈ K i, dyRound k x ∈ D k :=
    ⟨fun k => (finite_dyRound_image k hKb).toFinset, fun k i x hx =>
      (finite_dyRound_image k hKb).mem_toFinset.2 ⟨x, mem_iUnion.2 ⟨i, hx⟩, rfl⟩⟩
  have hXm : ∀ k, Measurable (fun ω (s : D k) => Y s ω) := fun k =>
    measurable_pi_iff.2 fun s => hYm s
  set Z : ℕ → κ → Ω → ℝ := fun k i ω =>
    (crossLenIn ξ (fun x => Y (dyRound k x) ω) (K i) (A i) (B i)).toReal with hZdef
  have hZU : ∀ k i b, {ω | b < Z k i ω} = (fun ω (s : D k) => Y s ω) ⁻¹'
      {v | b < (crossLenIn ξ (blockField k (D k) v) (K i) (A i) (B i)).toReal} := fun k i b => by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, hZdef]
    rw [crossLenIn_congr' fun x hx =>
      (blockField_eq k (D k) (fun s => Y s ω) (hD k i x hx)).symm]
  have hUo : ∀ k i b, IsOpen
      {v : D k → ℝ | b < (crossLenIn ξ (blockField k (D k) v) (K i) (A i) (B i)).toReal} :=
    fun k i b => isOpen_crossUpper k (D k) (hfin i) b
  have hZm : ∀ k i, Measurable (Z k i) := fun k i => measurable_of_Ioi fun b => by
    have : Z k i ⁻¹' Ioi b = {ω | b < Z k i ω} := rfl
    rw [this, hZU]
    exact hXm k (hUo k i b).measurableSet
  have hass : ∀ k (b : κ → ℝ), ∏ i, P.real {ω | b i < Z k i ω} ≤
      P.real (⋂ i, {ω | b i < Z k i ω}) := fun k b => by
    have h := Pitt.prod_prob_le_biInter (hG (D k)) (fun s t => hcov s t)
      (U := fun i =>
        {v : D k → ℝ | b i < (crossLenIn ξ (blockField k (D k) v) (K i) (A i) (B i)).toReal})
      (fun i => (hUo k i (b i)).measurableSet)
      (fun i => isUpperSet_crossUpper hξ k (D k) (hfin i) (b i)) Finset.univ
    simp only [Finset.mem_univ, iInter_true] at h
    simp only [hZU]
    exact h
  have hlim : ∀ i ω, Tendsto (fun k => Z k i ω) atTop
      (𝓝 ((crossLenIn ξ (fun x => Y x ω) (K i) (A i) (B i)).toReal)) := fun i ω =>
    tendsto_crossLenIn_dyRound (Y := fun x => Y x ω) (hK i) (hfin i) (hYc ω)
  exact assoc_of_tendsto (Z := Z)
    (Zl := fun i ω => (crossLenIn ξ (fun x => Y x ω) (K i) (A i) (B i)).toReal)
    hZm (fun i => (measurable_crossLenIn (hK i) hYc hYm).ennreal_toReal) hlim hass a

/-- **DDDF Lemma 13 for crossings, square-root trick** (DDDF l. 777–779, as used at l. 801–803). -/
theorem lemma13_cross_sqrt (hξ : 0 ≤ ξ) {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x))
    (hG : ∀ D : Finset ℂ, HasGaussianLaw (fun ω (s : D) => Y s ω) P)
    (hcov : ∀ x y, 0 ≤ cov[Y x, Y y; P])
    {κ : Type*} [Fintype κ] [Nonempty κ] (K A B : κ → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hfin : ∀ i, crossLenIn ξ 0 (K i) (A i) (B i) ≠ ⊤) (a : κ → ℝ) :
    ∃ i, 1 - (1 - P.real (⋃ i, {ω | (crossLenIn ξ (fun x => Y x ω) (K i) (A i) (B i)).toReal ≤
        a i})) ^ (1 / (Fintype.card κ : ℝ)) ≤
      P.real {ω | (crossLenIn ξ (fun x => Y x ω) (K i) (A i) (B i)).toReal ≤ a i} := by
  have h := Pitt.sqrt_trick (P := P)
    (A := fun i => {ω | a i < (crossLenIn ξ (fun x => Y x ω) (K i) (A i) (B i)).toReal})
    (fun i => (measurableSet_lt measurable_const
      (measurable_crossLenIn (hK i) hYc hYm).ennreal_toReal).nullMeasurableSet)
    (lemma13_cross hξ hYc hYm hG hcov K A B hK hfin a)
  simpa only [compl_ofPred, not_lt] using h

end DDDF
end LQGMetric
