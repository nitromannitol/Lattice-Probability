/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.LenCountable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Prod

/-!
# DDDF crossing lengths: a countable family of paths, measurability, near-geodesics
(task P2-DDDFLEN; blueprint DDDF.D2.len, DDDF.S2.b with deviation D-DDDF-5, decision D31)

DDDF (arXiv:1904.08021, `tightness.tex` l. 462–463) uses a geodesic of `e^{ξφ_{0,n}} ds`
("exists by the Hopf–Rinow theorem and a compactness argument") and later the "uppermost
geodesic" as a measurable function of the field (l. 950). Following D-DDDF-5 / D31 we use
measurably chosen near-geodesics from a countable family instead:

* `exists_countable_family`: for `U` compact there is a countable set `S` of admissible paths
  with `crossLenIn ξ f U A B = ⨅_{P ∈ S} lfppLen ξ f P` for **every** continuous `f`.
  Own soft argument (no source needed beyond mathlib): `C(ℂ, ℝ)` is separable
  (`ContinuousMap.instSeparableSpace`); for `g` in a dense sequence and `k ∈ ℕ` pick a path that
  is `1/(k+1)`-optimal for `g`; for general `f` use `crossLenIn_le_of_abs_sub_le` with `g`
  uniformly close to `f` on `U` (compact-open = compact convergence,
  `ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn`).
* `measurable_crossLenIn`: for a random field `Y` continuous in `x` and measurable in `ω`,
  `ω ↦ crossLenIn ξ (Y · ω) U A B` is measurable (countable infimum of measurable lengths).
* `exists_measurable_select`: for a measurable bound `Bd ω > L(ω)`, a measurable index
  `J : Ω → ℕ` with `lfppLen (Q (J ω)) < Bd ω`; specializations `exists_nearGeodesic_add`
  (`≤ L + η`) and `exists_nearGeodesic_mul` (`< (1+η) L`) for marked rectangles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace LQGMetric
namespace DDDF

variable {ξ : ℝ} {U A B : Set ℂ}

/-- Uniform approximation on a compact set by the dense sequence of `C(ℂ, ℝ)`. -/
theorem exists_denseSeq_close {K : Set ℂ} (hK : IsCompact K) (f : C(ℂ, ℝ)) {δ : ℝ}
    (hδ : 0 < δ) : ∃ n, ∀ x ∈ K, |f x - denseSeq C(ℂ, ℝ) n x| < δ := by
  have hU := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
    (tendsto_id (x := 𝓝 f)) K hK
  have hev := Metric.tendstoUniformlyOn_iff.mp hU δ hδ
  obtain ⟨g, hg, n, rfl⟩ := mem_closure_iff_nhds.mp (denseRange_denseSeq C(ℂ, ℝ) f) _ hev
  exact ⟨n, fun x hx => by simpa [Real.dist_eq] using hg x hx⟩

/-- the `1/(k+1)`-optimal admissible paths for the weight `g` -/
def optSet (ξ : ℝ) (U A B : Set ℂ) (g : ℂ → ℝ) (k : ℕ) : Set (ℝ → ℂ) :=
  {P | AdmPath U A B P ∧
    lfppLen ξ g P < crossLenIn ξ g U A B + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹}

open Classical in
/-- the countable family: one `1/(k+1)`-optimal path for each element of a dense sequence -/
def ctblFamily (ξ : ℝ) (U A B : Set ℂ) : Set (ℝ → ℂ) :=
  ⋃ n : ℕ, ⋃ k : ℕ,
    if h : (optSet ξ U A B (denseSeq C(ℂ, ℝ) n) k).Nonempty then {h.some} else ∅

theorem ctblFamily_countable : (ctblFamily ξ U A B).Countable :=
  countable_iUnion fun _ => countable_iUnion fun _ => by split_ifs <;> simp

theorem ctblFamily_subset : ctblFamily ξ U A B ⊆ {P | AdmPath U A B P} := by
  intro P hP
  simp only [ctblFamily, mem_iUnion] at hP
  obtain ⟨n, k, hP⟩ := hP
  split_ifs at hP with h
  · rw [mem_singleton_iff.1 hP]; exact h.some_mem.1
  · exact absurd hP (notMem_empty _)

theorem mem_ctblFamily_of_nonempty {n k : ℕ}
    (h : (optSet ξ U A B (denseSeq C(ℂ, ℝ) n) k).Nonempty) :
    h.some ∈ ctblFamily ξ U A B := by
  simp only [ctblFamily, mem_iUnion]
  exact ⟨n, k, by simp [h]⟩

/-- **The countable family** (DDDF.S2.b via D-DDDF-5): for `U` compact the crossing length of
every continuous weight is the infimum over the countable family `ctblFamily`. -/
theorem crossLenIn_eq_ctblFamily (hU : IsCompact U) {f : ℂ → ℝ} (hf : Continuous f) :
    crossLenIn ξ f U A B = ⨅ P ∈ ctblFamily ξ U A B, lfppLen ξ f P := by
  refine le_antisymm (le_iInf₂ fun P hP => crossLenIn_le_lfppLen (ctblFamily_subset hP)) ?_
  set L := crossLenIn ξ f U A B with hL
  rcases eq_or_ne L ∞ with hLt | hLt
  · rw [hLt]; exact le_top
  set c : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (Real.exp (|ξ| * (1 / ((m : ℝ) + 1))))
  set ε : ℕ → ℝ≥0∞ := fun m => ((m + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hbound : ∀ m, ⨅ P ∈ ctblFamily ξ U A B, lfppLen ξ f P ≤ c m * (c m * L + ε m) := by
    intro m
    obtain ⟨n, hn⟩ := exists_denseSeq_close hU ⟨f, hf⟩
      (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))
    set g := denseSeq C(ℂ, ℝ) n
    have hgf : crossLenIn ξ g U A B ≤ c m * L :=
      crossLenIn_le_of_abs_sub_le fun x hx => by
        rw [abs_sub_comm]; exact (hn x hx).le
    have hgt : crossLenIn ξ g U A B ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLt) hgf
    have hne : (optSet ξ U A B g m).Nonempty := by
      have hlt : crossLenIn ξ g U A B < crossLenIn ξ g U A B + ε m :=
        ENNReal.lt_add_right hgt (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
      conv_lhs at hlt => rw [crossLenIn_eq_biInf]
      obtain ⟨P, hlt1⟩ := iInf_lt_iff.1 hlt
      obtain ⟨hP, hlt'⟩ := iInf_lt_iff.1 hlt1
      exact ⟨P, hP, hlt'⟩
    have hmem := mem_ctblFamily_of_nonempty hne
    obtain ⟨⟨z, -, w, -, -, hPU⟩, hlt⟩ := hne.some_mem
    calc ⨅ P ∈ ctblFamily ξ U A B, lfppLen ξ f P ≤ lfppLen ξ f hne.some := iInf₂_le _ hmem
      _ ≤ c m * lfppLen ξ g hne.some :=
          lfppLen_le_of_abs_sub_le fun t ht => (hn _ (hPU t ht)).le
      _ ≤ c m * (c m * L + ε m) := by
          gcongr
          exact hlt.le.trans (add_le_add hgf le_rfl)
  have hc : Tendsto c atTop (𝓝 1) := by
    have h0 : Tendsto (fun m : ℕ => Real.exp (|ξ| * (1 / ((m : ℝ) + 1)))) atTop
        (𝓝 (Real.exp (|ξ| * 0))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto 0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    rw [mul_zero, Real.exp_zero] at h0
    have := ENNReal.tendsto_ofReal h0
    rwa [ENNReal.ofReal_one] at this
  have hε : Tendsto ε atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun m => c m * (c m * L + ε m)) atTop (𝓝 (1 * (1 * L + 0))) :=
    ENNReal.Tendsto.mul hc (Or.inl one_ne_zero)
      ((ENNReal.Tendsto.mul_const hc (Or.inr hLt)).add hε) (Or.inr ENNReal.one_ne_top)
  rw [one_mul, one_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim hbound

/-! ### Measurability -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For a random continuous field `Y`, the length of a fixed path is measurable in `ω`. -/
theorem measurable_lfppLen {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) {P : ℝ → ℂ} (hP : ContinuousOn P (Icc 0 1)) :
    Measurable fun ω => lfppLen ξ (fun x => Y x ω) P := by
  set P' : ℝ → ℂ := fun t => P (projIcc (0 : ℝ) 1 zero_le_one t)
  have hP' : Continuous P' :=
    hP.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t => (projIcc _ _ _ t).2
  have heq : ∀ ω, lfppLen ξ (fun x => Y x ω) P = ∫⁻ t in Icc (0 : ℝ) 1,
      ENNReal.ofReal (Real.exp (ξ * Y (P' t) ω) * ‖deriv P t‖) := fun ω =>
    setLIntegral_congr_fun measurableSet_Icc fun t ht => by
      simp only [P', projIcc_of_mem zero_le_one ht]
  simp_rw [heq]
  have hY : Measurable (Function.uncurry Y) :=
    measurable_uncurry_of_continuous_of_measurable hYc hYm
  have hY' : Measurable fun p : Ω × ℝ => Y (P' p.2) p.1 :=
    hY.comp ((hP'.measurable.comp measurable_snd).prodMk measurable_fst)
  refine Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ =>
    ENNReal.ofReal (Real.exp (ξ * Y (P' p.2) p.1) * ‖deriv P p.2‖)) ?_
  exact (((hY'.const_mul ξ).exp).mul ((measurable_deriv P).comp measurable_snd).norm).ennreal_ofReal

/-- **Measurability of crossing lengths** in the field (DDDF.D2.len; D31). -/
theorem measurable_crossLenIn (hU : IsCompact U) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) :
    Measurable fun ω => crossLenIn ξ (fun x => Y x ω) U A B := by
  simp_rw [crossLenIn_eq_ctblFamily (ξ := ξ) (A := A) (B := B) hU (hYc _)]
  refine Measurable.biInf _ ctblFamily_countable fun P hP => ?_
  obtain ⟨z, -, w, -, hPw, -⟩ := ctblFamily_subset hP
  exact measurable_lfppLen hYc hYm hPw.continuousOn

/-- An enumerated countable family of admissible paths realizing every crossing length. -/
theorem exists_enum_family (hU : IsCompact U) {P₀ : ℝ → ℂ} (hP₀ : AdmPath U A B P₀) :
    ∃ Q : ℕ → ℝ → ℂ, (∀ j, AdmPath U A B (Q j)) ∧
      ∀ f : ℂ → ℝ, Continuous f → crossLenIn ξ f U A B = ⨅ j, lfppLen ξ f (Q j) := by
  have hc : (insert P₀ (ctblFamily ξ U A B)).Countable := ctblFamily_countable.insert P₀
  obtain ⟨Q, hQ⟩ := hc.exists_eq_range (insert_nonempty _ _)
  have hsub : ∀ j, AdmPath U A B (Q j) := fun j => by
    have : Q j ∈ insert P₀ (ctblFamily ξ U A B) := hQ ▸ mem_range_self j
    rcases this with h | h
    · rw [h]; exact hP₀
    · exact ctblFamily_subset h
  refine ⟨Q, hsub, fun f hf =>
    le_antisymm (le_iInf fun j => crossLenIn_le_lfppLen (hsub j)) ?_⟩
  rw [crossLenIn_eq_ctblFamily hU hf]
  refine le_iInf₂ fun P hP => ?_
  obtain ⟨j, rfl⟩ : P ∈ range Q := hQ ▸ mem_insert_of_mem _ hP
  exact iInf_le _ j

/-- **Measurable selection** (D-DDDF-5): given a measurable bound `Bd > L`, a measurable index
`J` of the enumerated family with `lfppLen (Q (J ω)) < Bd ω`. -/
theorem exists_measurable_select {Q : ℕ → ℝ → ℂ} {Y : ℂ → Ω → ℝ}
    (hQ : ∀ ω, crossLenIn ξ (fun x => Y x ω) U A B = ⨅ j, lfppLen ξ (fun x => Y x ω) (Q j))
    (hQm : ∀ j, Measurable fun ω => lfppLen ξ (fun x => Y x ω) (Q j))
    {Bd : Ω → ℝ≥0∞} (hBd : Measurable Bd)
    (hlt : ∀ ω, crossLenIn ξ (fun x => Y x ω) U A B < Bd ω) :
    ∃ J : Ω → ℕ, Measurable J ∧ ∀ ω, lfppLen ξ (fun x => Y x ω) (Q (J ω)) < Bd ω := by
  have hex : ∀ ω, ∃ j, lfppLen ξ (fun x => Y x ω) (Q j) < Bd ω := fun ω =>
    iInf_lt_iff.1 ((hQ ω) ▸ hlt ω)
  classical
  refine ⟨fun ω => Nat.find (hex ω), measurable_to_countable' fun j => ?_,
    fun ω => Nat.find_spec (hex ω)⟩
  have hset : (fun ω => Nat.find (hex ω)) ⁻¹' {j} =
      {ω | lfppLen ξ (fun x => Y x ω) (Q j) < Bd ω} ∩
        ⋂ i, ⋂ (_ : i < j), {ω | lfppLen ξ (fun x => Y x ω) (Q i) < Bd ω}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, Nat.find_eq_iff, mem_inter_iff, mem_ofPred_eq,
      mem_iInter, mem_compl_iff]
  rw [hset]
  exact (measurableSet_lt (hQm j) hBd).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (measurableSet_lt (hQm i) hBd).compl)

/-- **Measurable near-geodesics of a marked rectangle** (DDDF.S2.b, D-DDDF-5): for a random
continuous field and `η > 0` there are a countable enumerated family `Q` of admissible crossings
of `R` and measurable indices `J`, `J'` with `lfppLen (Q (J ω)) ≤ L(ω) + η` and, if
`crossWidth R > 0`, `lfppLen (Q (J' ω)) < (1 + η) L(ω)`. -/
theorem exists_nearGeodesic (R : MarkedRect) (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) {η : ℝ≥0∞}
    (hη : 0 < η) :
    ∃ Q : ℕ → ℝ → ℂ, (∀ j, AdmPath R.toSet R.side₁ R.side₂ (Q j)) ∧
      (∀ ω, rectLen ξ (fun x => Y x ω) R = ⨅ j, lfppLen ξ (fun x => Y x ω) (Q j)) ∧
      (∀ j, Measurable fun ω => lfppLen ξ (fun x => Y x ω) (Q j)) ∧
      (∃ J : Ω → ℕ, Measurable J ∧
        ∀ ω, lfppLen ξ (fun x => Y x ω) (Q (J ω)) < rectLen ξ (fun x => Y x ω) R + η) ∧
      (0 < R.crossWidth → ∃ J : Ω → ℕ, Measurable J ∧
        ∀ ω, lfppLen ξ (fun x => Y x ω) (Q (J ω)) < (1 + η) * rectLen ξ (fun x => Y x ω) R) := by
  obtain ⟨Q, hQa, hQ⟩ := exists_enum_family (ξ := ξ) R.isCompact_toSet (R.admPath_seg hw hh)
  have hQ' : ∀ ω, rectLen ξ (fun x => Y x ω) R = ⨅ j, lfppLen ξ (fun x => Y x ω) (Q j) :=
    fun ω => hQ _ (hYc ω)
  have hQm : ∀ j, Measurable fun ω => lfppLen ξ (fun x => Y x ω) (Q j) := fun j => by
    obtain ⟨z, -, w, -, hPw, -⟩ := hQa j
    exact measurable_lfppLen hYc hYm hPw.continuousOn
  have hLm : Measurable fun ω => rectLen ξ (fun x => Y x ω) R :=
    measurable_crossLenIn R.isCompact_toSet hYc hYm
  have hfin : ∀ ω, rectLen ξ (fun x => Y x ω) R ≠ ∞ := fun ω => rectLen_ne_top R hw hh (hYc ω)
  refine ⟨Q, hQa, hQ', hQm, exists_measurable_select hQ' hQm (hLm.add_const η)
    fun ω => ENNReal.lt_add_right (hfin ω) hη.ne', fun hc => ?_⟩
  refine exists_measurable_select hQ' hQm (hLm.const_mul _) fun ω => ?_
  have h0 : rectLen ξ (fun x => Y x ω) R ≠ 0 := (rectLen_pos R hc (hYc ω)).ne'
  calc rectLen ξ (fun x => Y x ω) R = 1 * rectLen ξ (fun x => Y x ω) R := (one_mul _).symm
    _ < (1 + η) * rectLen ξ (fun x => Y x ω) R :=
        ENNReal.mul_lt_mul_left h0 (hfin ω) (ENNReal.lt_add_right ENNReal.one_ne_top hη.ne')

end DDDF
end LQGMetric
