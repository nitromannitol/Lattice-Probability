/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.WedgeMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurable
import LatticeProb.Bonanno.QuantumZipper.LQG.Wedge
import Mathlib.Probability.BrownianMotion.Basic

/-!
# WEDGE-MEAS (AUDIT-2, M1): measurability of the reference wedge data map

The reference map of `IsQuantumWedge` is
`ω ↦ canonical γ (wedgeField (lateralPart (X ω)) (A · ω) Q)`, read through `fieldLawFull`
(`coordsFull` jointly with raw test pairings).

* `measurable_dataFull_resc`: the data of `rescale (reconstruct c) Q s` is a *measurable* function
  of `(c, s) ∈ (ℕ → ℝ) × ℝ`.
* `dataFull_canonical`: the data of `canonical γ x` is that function at `(coords x, scaleParam γ x)`,
  and on good samples `scaleParam γ x = scaleG γ (coords x)` with `scaleG` measurable
  (`measurable_scaleParam_global`).
* `aemeasurable_coords_wedgeField`: under `IsWedgeProcess` and measurable coordinates of `X`,
  `ω ↦ coords (wedgeField (lateralPart (X ω)) (A · ω) Q)` is a.e.-measurable. This needs a
  jointly measurable version of the wedge radial process, hence the measurability of `lastZero`
  of a continuous path (`measurable_lastZero`).
* `isProbabilityMeasure_fieldLawFull_wedgeRef`: consequently the reference law is a probability
  measure **provided the reference wedge field is a.s. good** (`IsLQGGood`). This a.s. goodness
  is not available (M4-A5 and the area/boundary existence for wedge fields); it is the only
  missing input.
-/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology NNReal

namespace QuantumZipper

namespace WedgeMeas

open Factorization CoordsFull

/-! ## 1. The data of a rescaled reconstruction is measurable -/

/-- The data map read by `fieldLawFull U`. -/
def dataFull (U : Set ℂ) (y : FieldSample) : (ℕ → ℝ) × (TestFun U → ℝ) :=
  (coordsFull y, fun ρ => pairRaw y ρ.1)

/-- The sample `rescale (reconstruct c) Q s`. -/
def resc (Q : ℝ) (p : (ℕ → ℝ) × ℝ) : FieldSample := rescale (reconstruct p.1) Q p.2

theorem deriv_mul_left' (a : ℝ) (z : ℂ) : deriv (fun w : ℂ => (a : ℂ) * w) z = a := by
  simp

theorem measurable_resc_apply (Q : ℝ) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun p : (ℕ → ℝ) × ℝ => resc Q p μ := by
  have e : ∀ p : (ℕ → ℝ) × ℝ, resc Q p μ =
      limUnder atTop (fun k => ∫ z, avgReg (reconstruct p.1) k ((p.2 : ℂ) * z) ∂μ) +
        Q * (μ.real univ * Real.log |p.2|) := by
    intro p
    have h1 : evalReg (reconstruct p.1) (μ.map fun z => (p.2 : ℂ) * z) =
        limUnder atTop (fun k => ∫ z, avgReg (reconstruct p.1) k ((p.2 : ℂ) * z) ∂μ) := by
      unfold evalReg
      congr 1
      funext k
      have hm : Measurable (avgReg (reconstruct p.1) k) :=
        RegClosure.measurable_avgReg_slice (reconstruct p.1) k
      exact integral_map (measurable_const_mul (p.2 : ℂ)).aemeasurable hm.aestronglyMeasurable
    have h2 : ∫ z, Real.log ‖deriv (fun w : ℂ => (p.2 : ℂ) * w) z‖ ∂μ =
        μ.real univ * Real.log |p.2| := by
      have hd : ∀ z, Real.log ‖deriv (fun w : ℂ => (p.2 : ℂ) * w) z‖ = Real.log |p.2| :=
        fun z => by rw [deriv_mul_left', Complex.norm_real, Real.norm_eq_abs]
      rw [integral_congr_ae (ae_of_all _ hd), integral_const, smul_eq_mul]
    show evalReg (reconstruct p.1) (μ.map fun z => (p.2 : ℂ) * z) +
      Q * ∫ z, Real.log ‖deriv (fun w : ℂ => (p.2 : ℂ) * w) z‖ ∂μ = _
    rw [h1, h2]
  rw [show (fun p : (ℕ → ℝ) × ℝ => resc Q p μ) = fun p =>
      limUnder atTop (fun k => ∫ z, avgReg (reconstruct p.1) k ((p.2 : ℂ) * z) ∂μ) +
        Q * (μ.real univ * Real.log |p.2|) from funext e]
  have hk : ∀ k : ℕ, StronglyMeasurable
      (fun p : (ℕ → ℝ) × ℝ => ∫ z, avgReg (reconstruct p.1) k ((p.2 : ℂ) * z) ∂μ) := fun k =>
    StronglyMeasurable.integral_prod_right'
      (f := fun q : ((ℕ → ℝ) × ℝ) × ℂ => avgReg (reconstruct q.1.1) k ((q.1.2 : ℂ) * q.2))
      ((measurable_avgReg k).comp ((measurable_reconstruct.comp measurable_fst.fst).prodMk
        ((Complex.continuous_ofReal.measurable.comp measurable_fst.snd).mul
          measurable_snd))).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hk).measurable.add (measurable_const.mul
    (measurable_const.mul (Real.measurable_log.comp (continuous_abs.measurable.comp
      measurable_snd))))

theorem measurable_dataFull_resc (U : Set ℂ) (Q : ℝ) :
    Measurable fun p : (ℕ → ℝ) × ℝ => dataFull U (resc Q p) :=
  (measurable_pi_iff.2 fun _ => measurable_resc_apply Q _).prodMk
    (measurable_pi_iff.2 fun _ => (measurable_resc_apply Q _).sub (measurable_resc_apply Q _))

/-! ## 2. `canonical` through coordinates and the scale on good samples -/

theorem canonical_eq_resc (γ : ℝ) (x : FieldSample) :
    canonical γ x = resc (Qc γ) (coords x, scaleParam γ x) := by
  funext μ
  simp only [canonical, resc, rescale, coordChange]
  rw [evalReg_congr (avgReg_reconstruct_coords x)]

open Classical in
/-- The scale parameter of the reconstruction, on the good set (junk `0` elsewhere). -/
def scaleG (γ : ℝ) (c : ℕ → ℝ) : ℝ :=
  if IsLQGGood γ (reconstruct c) then scaleParam γ (reconstruct c) else 0

theorem measurable_scaleG (γ : ℝ) : Measurable (scaleG γ) :=
  (GoodMeas.measurable_scaleParam_global γ).comp measurable_reconstruct

theorem scaleG_coords {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    scaleG γ (coords x) = scaleParam γ x := by
  have hx' : IsLQGGood γ (reconstruct (coords x)) := (GoodSample.isLQGGood_iff_reconstruct γ x).2 hx
  simp only [scaleG, if_pos hx']
  exact scaleParam_congr (avgReg_reconstruct_coords x) γ

/-- **Conditional measurability of canonical data.** -/
theorem aemeasurable_dataFull_canonical {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {W : Ω → FieldSample} (hc : AEMeasurable (fun ω => coords (W ω)) P)
    (hg : ∀ᵐ ω ∂P, IsLQGGood γ (W ω)) (U : Set ℂ) :
    AEMeasurable (fun ω => dataFull U (canonical γ (W ω))) P := by
  have hm := (measurable_dataFull_resc U (Qc γ)).comp_aemeasurable
    (hc.prodMk ((measurable_scaleG γ).comp_aemeasurable hc))
  refine hm.congr ?_
  filter_upwards [hg] with ω hω
  simp only [Function.comp, canonical_eq_resc, scaleG_coords hω]

/-! ## 3. `lastZero` of a continuous path is measurable -/

/-- `g` has a zero in `[a, b]`. -/
def ZeroIn (g : ℝ → ℝ) (a b : ℝ) : Prop := ∃ s ∈ Icc a b, g s = 0

theorem zeroIn_iff {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b) :
    ZeroIn g a b ↔ ∀ m : ℕ, ∃ q : ℚ, a ≤ q ∧ (q : ℝ) ≤ b ∧ |g q| < 1 / ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨s, ⟨hs1, hs2⟩, hs0⟩ m
    have hc := Metric.continuous_iff.1 hg s (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨δ, hδ, hδ'⟩ := hc
    have hlt : max a (s - δ) < min b (s + δ) :=
      max_lt (lt_min hab (by linarith)) (lt_min (by linarith) (by linarith))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    refine ⟨q, (le_max_left _ _).trans hq1.le, hq2.le.trans (min_le_left _ _), ?_⟩
    have hd : dist (q : ℝ) s < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [le_max_right a (s - δ)]
      · linarith [min_le_right b (s + δ)]
    have := hδ' _ hd
    rwa [Real.dist_eq, hs0, sub_zero] at this
  · intro h
    by_contra hno
    obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le)
      (continuous_abs.comp hg).continuousOn
    have hpos : 0 < |g s0| := abs_pos.2 fun h0 => hno ⟨s0, hs0, h0⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    obtain ⟨q, hq1, hq2, hq3⟩ := h m
    have := hmin (show (q : ℝ) ∈ Icc a b from ⟨hq1, hq2⟩)
    simp only [mem_setOf_eq, Function.comp] at this
    linarith

theorem measurable_zeroIn {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hc : ∀ ω, Continuous (f ω)) (hm : ∀ s, Measurable fun ω => f ω s) {a b : ℝ} (hab : a < b) :
    Measurable fun ω => ZeroIn (f ω) a b := by
  have e : (fun ω => ZeroIn (f ω) a b) = fun ω => ∀ m : ℕ, ∃ q : ℚ, a ≤ q ∧ (q : ℝ) ≤ b ∧
      |f ω q| < 1 / ((m : ℝ) + 1) := funext fun ω => propext (zeroIn_iff (hc ω) hab)
  rw [e]
  exact Measurable.forall fun m => Measurable.exists fun q => measurable_const.and
    (measurable_const.and (measurableSet_setOfPred.1 (measurableSet_lt
      (continuous_abs.measurable.comp (hm q)) measurable_const)))

theorem bddAbove_zeros_iff {g : ℝ → ℝ} :
    BddAbove {s | 0 ≤ s ∧ g s = 0} ↔ ∃ N : ℕ, ∀ n : ℕ, ¬ ZeroIn g N (N + n + 1) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨⌈M⌉₊ + 1, fun n => ?_⟩
    rintro ⟨s, ⟨hs1, -⟩, hs0⟩
    have h1 := hM ⟨le_trans (by positivity) hs1, hs0⟩
    have h2 := Nat.le_ceil M
    push_cast at hs1
    linarith
  · rintro ⟨N, hN⟩
    refine ⟨N, fun s hs => ?_⟩
    by_contra h
    push_neg at h
    refine hN ⌈s⌉₊ ⟨s, ⟨h.le, ?_⟩, hs.2⟩
    have := Nat.le_ceil s
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    linarith

theorem exists_zero_gt_iff {g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    (∃ s ∈ {s | 0 ≤ s ∧ g s = 0}, c < s) ↔
      ∃ n : ℕ, ZeroIn g (c + 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1) + n + 1) := by
  constructor
  · rintro ⟨s, ⟨-, hs0⟩, hcs⟩
    obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt (sub_pos.2 hcs)
    obtain ⟨n2, hn2⟩ := exists_nat_ge s
    refine ⟨max n1 n2, s, ⟨?_, ?_⟩, hs0⟩
    · have h0 : (n1 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_left n1 n2
      have : 1 / ((max n1 n2 : ℕ) + 1 : ℝ) ≤ 1 / ((n1 : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    · have h1 : (n2 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_right n1 n2
      have h2 : 0 < 1 / ((max n1 n2 : ℕ) + 1 : ℝ) := by positivity
      linarith
  · rintro ⟨n, s, ⟨hs1, -⟩, hs0⟩
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨s, ⟨by linarith, hs0⟩, by linarith⟩

theorem lt_lastZero_iff {g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    c < lastZero g ↔ BddAbove {s | 0 ≤ s ∧ g s = 0} ∧ ∃ s ∈ {s | 0 ≤ s ∧ g s = 0}, c < s := by
  unfold lastZero
  constructor
  · intro h
    by_cases hb : BddAbove {s | 0 ≤ s ∧ g s = 0}
    · by_cases hne : ({s | 0 ≤ s ∧ g s = 0} : Set ℝ).Nonempty
      · exact ⟨hb, exists_lt_of_lt_csSup hne h⟩
      · rw [not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty] at h; linarith
    · rw [Real.sSup_of_not_bddAbove hb] at h; linarith
  · rintro ⟨hb, s, hs, hcs⟩
    exact lt_csSup_of_lt hb hs hcs

theorem measurable_lastZero {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hc : ∀ ω, Continuous (f ω)) (hm : ∀ s, Measurable fun ω => f ω s) :
    Measurable fun ω => lastZero (f ω) := by
  refine measurable_of_Ioi fun c => ?_
  by_cases hc0 : c < 0
  · have e : (fun ω => lastZero (f ω)) ⁻¹' Ioi c = univ := by
      ext ω
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact hc0.trans_le (Real.sSup_nonneg fun s hs => hs.1)
    rw [e]; exact MeasurableSet.univ
  · push_neg at hc0
    have e : (fun ω => lastZero (f ω)) ⁻¹' Ioi c =
        {ω | (∃ N : ℕ, ∀ n : ℕ, ¬ ZeroIn (f ω) N (N + n + 1)) ∧
          ∃ n : ℕ, ZeroIn (f ω) (c + 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1) + n + 1)} := by
      ext ω
      simp only [mem_preimage, mem_Ioi, mem_setOf_eq]
      rw [lt_lastZero_iff hc0, bddAbove_zeros_iff, exists_zero_gt_iff hc0]
    rw [e]
    refine measurableSet_setOfPred.2 ((Measurable.exists fun N => Measurable.forall fun n =>
      (measurable_zeroIn hc hm ?_).not).and (Measurable.exists fun n => measurable_zeroIn hc hm ?_))
    · linarith
    · linarith

/-! ## 4. A jointly measurable version of the wedge radial process -/

/-- Joint measurability of the wedge path built from paths that are continuous for every `ω`
and measurable for every time. -/
theorem measurable_wedgePath_joint {Ω : Type*} [MeasurableSpace Ω] (α Q : ℝ)
    {B B' : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous fun t => B t ω)
    (hB'c : ∀ ω, Continuous fun t => B' t ω) (hBm : ∀ t, Measurable (B t))
    (hB'm : ∀ t, Measurable (B' t)) :
    Measurable fun q : Ω × ℝ => wedgePath α Q (fun s => B s q.1) (fun s => B' s q.1) q.2 := by
  have hJ : ∀ {C : ℝ≥0 → Ω → ℝ}, (∀ ω, Continuous fun t => C t ω) → (∀ t, Measurable (C t)) →
      Measurable fun q : Ω × ℝ => C q.2.toNNReal q.1 := fun hc hm =>
    (measurable_uncurry_of_continuous_of_measurable hc hm).comp
      ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  set f : Ω → ℝ → ℝ := fun ω s => Real.sqrt 2 * B' s.toNNReal ω - (α - Q) * s with hf
  have hfc : ∀ ω, Continuous (f ω) := fun ω =>
    (continuous_const.mul ((hB'c ω).comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hfm : ∀ s, Measurable fun ω => f ω s := fun s =>
    ((hB'm _).const_mul _).sub measurable_const
  have hF : Measurable fun q : Ω × ℝ => f q.1 q.2 :=
    ((hJ hB'c hB'm).const_mul _).sub (measurable_snd.const_mul _)
  have hL := measurable_lastZero hfc hfm
  have e : (fun q : Ω × ℝ => wedgePath α Q (fun s => B s q.1) (fun s => B' s q.1) q.2) =
      fun q => if 0 ≤ q.2 then Real.sqrt 2 * B q.2.toNNReal q.1 + (α - Q) * q.2
        else f q.1 (-q.2 + lastZero (f q.1)) := rfl
  rw [e]
  refine Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (((hJ hBc hBm).const_mul _).add (measurable_snd.const_mul _)) ?_
  exact hF.comp (measurable_fst.prodMk (measurable_snd.neg.add (hL.comp measurable_fst)))

/-- A version of an a.s. continuous, a.e.-measurable process, continuous and measurable
everywhere, equal to it on a measurable conull set. -/
theorem exists_good_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, AEMeasurable (B t) P) (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ (∀ ω ∈ G, Continuous (B · ω)) ∧
      ∀ t, Measurable (G.indicator (B t)) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  set S : Set Ω := {ω | Continuous (B · ω) ∧ ∀ q : D, B q ω = (hm q).mk (B q) ω} with hS
  have hSae : ∀ᵐ ω ∂P, ω ∈ S :=
    hc.and (ae_all_iff.2 fun q => (hm q).ae_eq_mk)
  refine ⟨(toMeasurable P Sᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hSae
  · intro ω hω
    exact (not_not.1 fun h => hω (subset_toMeasurable _ _ h)).1
  · have hsub : (toMeasurable P Sᶜ)ᶜ ⊆ S := fun ω hω =>
      not_not.1 fun h => hω (subset_toMeasurable _ _ h)
    have hq : ∀ q : D, Measurable ((toMeasurable P Sᶜ)ᶜ.indicator (B q)) := by
      intro q
      have e : (toMeasurable P Sᶜ)ᶜ.indicator (B q) =
          (toMeasurable P Sᶜ)ᶜ.indicator ((hm q).mk (B q)) := by
        funext ω
        by_cases hω : ω ∈ (toMeasurable P Sᶜ)ᶜ
        · simp only [indicator_of_mem hω]; exact (hsub hω).2 q
        · simp only [indicator_of_notMem hω]
      rw [e]
      exact (hm q).measurable_mk.indicator (measurableSet_toMeasurable _ _).compl
    intro t
    obtain ⟨u, huD, hut⟩ := mem_closure_iff_seq_limit.1 (hDd.closure_eq ▸ mem_univ t)
    refine measurable_of_tendsto_metrizable (f := fun n => (toMeasurable P Sᶜ)ᶜ.indicator
      (B (u n))) (fun n => hq ⟨u n, huD n⟩) (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ (toMeasurable P Sᶜ)ᶜ
    · simp only [indicator_of_mem hω]
      exact ((hsub hω).1.tendsto t).comp hut
    · simp only [indicator_of_notMem hω]
      exact tendsto_const_nhds

/-! ## 5. Coordinates of the wedge field -/

theorem measurable_radAvgReg_joint :
    Measurable (fun p : FieldSample × ℝ => radAvgReg p.1 p.2) := by
  have hround : ∀ n : ℕ, Measurable (fun p : FieldSample × ℝ =>
      p.1 (foldedCircle 0 (dyadicRound n p.2 + radius n))) := by
    intro n
    set g : ℝ → ℝ := fun r => dyadicRound n r + radius n with hg
    have hgm : Measurable g := (((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const
      ((2 : ℝ) ^ n)).comp (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))).add_const _
    have hcount : (Set.range g).Countable := by
      have hsub : Set.range g ⊆ Set.range (fun m : ℤ => (m : ℝ) / (2 : ℝ) ^ n + radius n) := by
        rintro _ ⟨r, rfl⟩
        exact ⟨⌊(2 : ℝ) ^ n * r⌋, rfl⟩
      exact (Set.countable_range _).mono hsub
    have : Countable (Set.range g) := hcount.to_subtype
    intro T hT
    have key : (fun p : FieldSample × ℝ => p.1 (foldedCircle 0 (g p.2))) ⁻¹' T
        = ⋃ d : Set.range g,
            {x : FieldSample | x (foldedCircle 0 (d : ℝ)) ∈ T} ×ˢ (g ⁻¹' ({(d : ℝ)} : Set ℝ)) := by
      ext ⟨x, r⟩
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq,
        Set.mem_singleton_iff]
      constructor
      · intro hmem
        exact ⟨⟨g r, Set.mem_range_self r⟩, hmem, rfl⟩
      · rintro ⟨d, hmem, hdz⟩
        rwa [hdz]
    show MeasurableSet ((fun p : FieldSample × ℝ => p.1 (foldedCircle 0 (g p.2))) ⁻¹' T)
    rw [key]
    exact MeasurableSet.iUnion fun d => MeasurableSet.prod
      (measurable_pi_apply (foldedCircle 0 (d : ℝ)) hT) (hgm (measurableSet_singleton _))
  unfold radAvgReg
  exact (StronglyMeasurable.limUnder fun n => (hround n).stronglyMeasurable).measurable

theorem measurable_lateralPart_apply' (μ : Measure ℂ) [SFinite μ] :
    Measurable fun x : FieldSample => lateralPart x μ :=
  (measurable_evalReg μ).sub (StronglyMeasurable.integral_prod_right' (ν := μ)
    (measurable_radAvgReg_joint.comp (measurable_fst.prodMk
      (measurable_norm.comp measurable_snd))).stronglyMeasurable).measurable

theorem measurable_wedgeField_apply {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) {A : Ω × ℝ → ℝ} (hA : Measurable A)
    (Q : ℝ) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun ω => wedgeField (lateralPart (X ω)) (fun t => A (ω, t)) Q ν := by
  have hXm : Measurable X := measurable_pi_iff.2 hX
  refine ((measurable_lateralPart_apply' ν).comp hXm).add ?_
  have hf : Measurable fun q : Ω × ℂ => Q * (-Real.log ‖q.2‖) + A (q.1, -Real.log ‖q.2‖) :=
    (measurable_const.mul (Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg).add
      (hA.comp (measurable_fst.prodMk
        (Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg))
  exact (StronglyMeasurable.integral_prod_right' (ν := ν)
    (f := fun q : Ω × ℂ => Q * (-Real.log ‖q.2‖) + A (q.1, -Real.log ‖q.2‖))
    hf.stronglyMeasurable).measurable

/-- **Coordinates of the reference wedge field are a.e.-measurable.** -/
theorem aemeasurable_coords_wedgeField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {α Q : ℝ}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) (hA : IsWedgeProcess α Q A P) :
    AEMeasurable (fun ω => coords (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)) P := by
  obtain ⟨B, B', hB, hB', -, hAB⟩ := hA
  obtain ⟨G, hGm, hG0, hGc, hGmeas⟩ :=
    exists_good_version (P := P) (fun t => hB.aemeasurable t) hB.cont
  obtain ⟨G', hG'm, hG'0, hG'c, hG'meas⟩ :=
    exists_good_version (P := P) (fun t => hB'.aemeasurable t) hB'.cont
  set Bt : ℝ≥0 → Ω → ℝ := fun t => G.indicator (B t) with hBt
  set Bt' : ℝ≥0 → Ω → ℝ := fun t => G'.indicator (B' t) with hBt'
  have hcont : ∀ {C : ℝ≥0 → Ω → ℝ} {K : Set Ω}, (∀ ω ∈ K, Continuous (C · ω)) →
      ∀ ω, Continuous fun t => K.indicator (C t) ω := by
    intro C K hK ω
    by_cases hω : ω ∈ K
    · simp only [indicator_of_mem hω]; exact hK ω hω
    · simp only [indicator_of_notMem hω]; exact continuous_const
  have hÂ := measurable_wedgePath_joint α Q (B := Bt) (B' := Bt') (hcont hGc) (hcont hG'c)
    hGmeas hG'meas
  set Â : Ω × ℝ → ℝ := fun q => wedgePath α Q (fun s => Bt s q.1) (fun s => Bt' s q.1) q.2
  have hmeas : Measurable fun ω => coords (wedgeField (lateralPart (X ω)) (fun t => Â (ω, t)) Q) :=
    measurable_pi_iff.2 fun i => measurable_wedgeField_apply hX hÂ Q _
  refine hmeas.aemeasurable.congr ?_
  have hae : ∀ᵐ ω ∂P, ω ∈ G ∩ G' := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) (measure_union_null hG0 hG'0)
    simp only [mem_setOf_eq, mem_inter_iff, not_and_or] at hω
    rcases hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  filter_upwards [hae] with ω hω
  have e : (fun t => Â (ω, t)) = fun t => A t ω := by
    funext t
    rw [hAB ω t]
    simp only [Â, hBt, hBt', indicator_of_mem hω.1, indicator_of_mem hω.2]
  simp only [e]

/-! ## 6. The reference law -/

/-- The reference field of `IsQuantumWedge`. -/
def wedgeRef (γ : ℝ) {Ω : Type*} (X : Ω → FieldSample) (A : ℝ → Ω → ℝ) : Ω → FieldSample :=
  fun ω => canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))

/-- **WEDGE-MEAS, conditional form.** If the reference wedge field is a.s. good, the reference
data map is a.e.-measurable, so the reference law is a probability measure. -/
theorem aemeasurable_wedgeRefData {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {γ α : ℝ} (hX : IsFreeGFFModConstH X P)
    (hA : IsWedgeProcess α (Qc γ) A P)
    (hgood : ∀ᵐ ω ∂P, IsLQGGood γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))
    (U : Set ℂ) : AEMeasurable (fun ω => dataFull U (wedgeRef γ X A ω)) P :=
  aemeasurable_dataFull_canonical (aemeasurable_coords_wedgeField hX.measurable_coord hA) hgood U

theorem isProbabilityMeasure_fieldLawFull_wedgeRef {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {γ α : ℝ}
    (hX : IsFreeGFFModConstH X P) (hA : IsWedgeProcess α (Qc γ) A P)
    (hgood : ∀ᵐ ω ∂P, IsLQGGood γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))
    (U : Set ℂ) : IsProbabilityMeasure (fieldLawFull U (wedgeRef γ X A) P) :=
  (Measure.isProbabilityMeasure_map_iff (aemeasurable_wedgeRefData hX hA hgood U)).2 inferInstance

end WedgeMeas

end QuantumZipper
