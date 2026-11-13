/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm14.WeldingData at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.Determination
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseFlow
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardFlow
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Theorem 1.4(b): the driver side (welding data of the reverse SLE hull)

Sheffield, *Conformal weldings of random surfaces*, §1.4, proof of Theorem 1.4 (blueprint node
C1, with A3 and A4).

For a driving function `W` and a time `T`, the *welding data* is
`weldingData W T = (0₋, q ↦ weldingHom W T q for rational q ∈ [0₋, 0], junk 0 elsewhere)`,
an element of the standard Borel space `ℝ × (ℚ → ℝ)`.

Main results (paths on `[0,T]` are elements of `C([0,T], ℝ)`, a Polish space):

* `measurable_weldingDataC`, `weldingDataC_eq_of_car`: an everywhere-defined Borel map
  `weldingDataC` on `C([0,T], ℝ)` agrees with the welding data at every path whose reverse hull
  has a Carathéodory extension (so at every path with a simple reverse hull, under
  `Blueprint.RevMapCaratheodory`). The boundary values are read along the heights `1/(n+1)`,
  `0₋` and the welding homeomorphism through rational infima and suprema.
* `continuousOn_weldingHom_of_car`, `weldingHom_eqOn_of_weldingData_eq`: the welding
  homeomorphism is continuous on `[0₋,0]`, so it is determined by its rational values.
* `revMap_eq_of_weldingData_eq`: equal welding data of two simple hulls, one of them removable,
  give equal reverse maps at time `T` and equal terminal driver values (welding uniqueness A3).
* `injective_sampleC`, `exists_partialGraph_of_injOn` (Lusin–Souslin): a Borel map that is
  injective on a Borel set of paths yields a Borel partial graph in
  (welding data) × (driver at rational times).
* `exists_weldingGraph_of_goodSet`: the resulting a.s. statement for a random driver.
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace Thm14WeldingData

open Thm14Determination

/-! ### Rational suprema and infima -/

section RatBounds

variable {α : Type*} [MeasurableSpace α]

theorem measurable_sSup_rat (p : ℚ → α → Prop) (hp : ∀ q, MeasurableSet {a | p q a})
    (hb : ∀ a, BddAbove (((↑) : ℚ → ℝ) '' {q | p q a})) :
    Measurable fun a => sSup (((↑) : ℚ → ℝ) '' {q | p q a}) := by
  refine measurable_of_Ioi fun c => ?_
  have hset : (fun a => sSup (((↑) : ℚ → ℝ) '' {q | p q a})) ⁻¹' Ioi c =
      (⋃ q : ℚ, {a | p q a} ∩ {_a | c < (q : ℝ)}) ∪
        ((⋂ q : ℚ, {a | p q a}ᶜ) ∩ {_a | c < 0}) := by
    ext a
    simp only [mem_preimage, mem_Ioi, mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq,
      mem_iInter, mem_compl_iff]
    by_cases hne : ∃ q, p q a
    · obtain ⟨q₀, hq₀⟩ := hne
      rw [lt_csSup_iff (hb a) ⟨_, q₀, hq₀, rfl⟩]
      constructor
      · rintro ⟨_, ⟨q, hq, rfl⟩, h⟩
        exact Or.inl ⟨q, hq, h⟩
      · rintro (⟨q, hq, h⟩ | ⟨h, -⟩)
        · exact ⟨_, ⟨q, hq, rfl⟩, h⟩
        · exact absurd hq₀ (h q₀)
    · push Not at hne
      have hempty : ((↑) : ℚ → ℝ) '' {q | p q a} = ∅ := by
        ext x
        simp only [mem_image, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
        intro q hq
        exact absurd hq (hne q)
      rw [hempty, Real.sSup_empty]
      constructor
      · intro h
        exact Or.inr ⟨hne, h⟩
      · rintro (⟨q, hq, -⟩ | ⟨-, h⟩)
        · exact absurd hq (hne q)
        · exact h
  rw [hset]
  exact (MeasurableSet.iUnion fun q => (hp q).inter (MeasurableSet.const _)).union
    ((MeasurableSet.iInter fun q => (hp q).compl).inter (MeasurableSet.const _))

theorem measurable_sInf_rat (p : ℚ → α → Prop) (hp : ∀ q, MeasurableSet {a | p q a})
    (hb : ∀ a, BddBelow (((↑) : ℚ → ℝ) '' {q | p q a})) :
    Measurable fun a => sInf (((↑) : ℚ → ℝ) '' {q | p q a}) := by
  refine measurable_of_Iio fun c => ?_
  have hset : (fun a => sInf (((↑) : ℚ → ℝ) '' {q | p q a})) ⁻¹' Iio c =
      (⋃ q : ℚ, {a | p q a} ∩ {_a | (q : ℝ) < c}) ∪
        ((⋂ q : ℚ, {a | p q a}ᶜ) ∩ {_a | (0 : ℝ) < c}) := by
    ext a
    simp only [mem_preimage, mem_Iio, mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq,
      mem_iInter, mem_compl_iff]
    by_cases hne : ∃ q, p q a
    · obtain ⟨q₀, hq₀⟩ := hne
      rw [csInf_lt_iff (hb a) ⟨_, q₀, hq₀, rfl⟩]
      constructor
      · rintro ⟨_, ⟨q, hq, rfl⟩, h⟩
        exact Or.inl ⟨q, hq, h⟩
      · rintro (⟨q, hq, h⟩ | ⟨h, -⟩)
        · exact ⟨_, ⟨q, hq, rfl⟩, h⟩
        · exact absurd hq₀ (h q₀)
    · push Not at hne
      have hempty : ((↑) : ℚ → ℝ) '' {q | p q a} = ∅ := by
        ext x
        simp only [mem_image, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
        intro q hq
        exact absurd hq (hne q)
      rw [hempty, Real.sInf_empty]
      constructor
      · intro h
        exact Or.inr ⟨hne, h⟩
      · rintro (⟨q, hq, -⟩ | ⟨-, h⟩)
        · exact absurd hq (hne q)
        · exact h
  rw [hset]
  exact (MeasurableSet.iUnion fun q => (hp q).inter (MeasurableSet.const _)).union
    ((MeasurableSet.iInter fun q => (hp q).compl).inter (MeasurableSet.const _))

end RatBounds

/-- The heights `1/(n+1)` along which boundary values are read. -/
def height (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem height_pos (n : ℕ) : 0 < height n := by
  unfold height
  positivity

theorem tendsto_height : Tendsto height atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall height_pos⟩

/-- For a continuous `G` on `ℝ` whose level set `{y ≥ 0 : G y = c}` has minimum `m`, the
rational description of `m` used by `whSeq`. -/
theorem sInf_rat_cond_eq {G : ℝ → ℂ} (hG : Continuous G) (c : ℂ) {m : ℝ} (hm0 : 0 ≤ m)
    (hmG : G m = c) (hmin : ∀ y, 0 ≤ y → G y = c → m ≤ y) :
    sInf (((↑) : ℚ → ℝ) '' {r : ℚ | 0 ≤ (r : ℝ) ∧ ∀ n : ℕ, ∃ y : ℚ, 0 ≤ (y : ℝ) ∧
      (y : ℝ) ≤ r ∧ ‖G y - c‖ < height n}) = m := by
  have key : ∀ r : ℚ, r ∈ {r : ℚ | 0 ≤ (r : ℝ) ∧ ∀ n : ℕ, ∃ y : ℚ, 0 ≤ (y : ℝ) ∧
      (y : ℝ) ≤ r ∧ ‖G y - c‖ < height n} ↔ r ∈ {r : ℚ | 0 ≤ (r : ℝ) ∧ m ≤ r} := by
    intro r
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hr, hn⟩
      refine ⟨hr, ?_⟩
      choose y hy0 hyr hyn using hn
      obtain ⟨y', hy', φ, hφ, hlim⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) r)).tendsto_subseq
        (x := fun n => (y n : ℝ)) (fun n => ⟨hy0 n, hyr n⟩)
      have h1 : Tendsto (fun n => ‖G ((y (φ n) : ℚ) : ℝ) - c‖) atTop (𝓝 ‖G y' - c‖) :=
        (((hG.tendsto y').comp hlim).sub_const c).norm
      have h2 : Tendsto (fun n => height (φ n)) atTop (𝓝 0) :=
        (tendsto_nhdsWithin_iff.1 tendsto_height).1.comp hφ.tendsto_atTop
      have hzero : ‖G y' - c‖ = 0 :=
        le_antisymm (le_of_tendsto_of_tendsto' h1 h2 fun n => (hyn (φ n)).le) (norm_nonneg _)
      exact (hmin y' hy'.1 (sub_eq_zero.1 (norm_eq_zero.1 hzero))).trans hy'.2
    · rintro ⟨hr, hmr⟩
      refine ⟨hr, fun n => ?_⟩
      have hc : ContinuousAt (fun y : ℝ => ‖G y - c‖) m :=
        ((hG.sub continuous_const).norm).continuousAt
      obtain ⟨δ, hδ, hδP⟩ := Metric.continuousAt_iff.1 hc (height n) (height_pos n)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show m < m + δ by linarith)
      have hcast : ((min q r : ℚ) : ℝ) = min (q : ℝ) (r : ℝ) := Rat.cast_min q r
      refine ⟨min q r, ?_, ?_, ?_⟩
      · rw [hcast]
        exact le_min (by linarith) hr
      · rw [hcast]
        exact min_le_right _ _
      · have hd : dist ((min q r : ℚ) : ℝ) m < δ := by
          rw [hcast, Real.dist_eq, abs_lt]
          constructor
          · have := le_min hq1.le hmr
            linarith
          · have := min_le_left (q : ℝ) r
            linarith
        have := hδP hd
        rw [Real.dist_eq, hmG, sub_self, norm_zero, sub_zero, abs_of_nonneg (norm_nonneg _)]
          at this
        exact this
  rw [Set.ext key]
  obtain ⟨q₀, hq₀⟩ := exists_rat_gt m
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, q₀, ⟨by linarith, hq₀.le⟩, rfl⟩ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact hr.2
  · intro w hw
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hw
    exact ⟨_, ⟨q, ⟨by linarith, hq1.le⟩, rfl⟩, hq2⟩

/-! ### The Carathéodory extension and the welding homeomorphism -/

section Car

variable {W : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ}

theorem hbar_ofReal (x : ℝ) : (x : ℂ) ∈ Hbar := by
  show (0 : ℝ) ≤ (x : ℂ).im
  simp

theorem tendsto_revMap_of_car (hF : Blueprint.IsCaratheodoryRevExt W T F) (x : ℝ) :
    Tendsto (fun y : ℝ => revMap W T (x + y * Complex.I)) (𝓝[>] 0) (𝓝 (F x)) := by
  obtain ⟨hFeq, hFc, -⟩ := hF
  have hpath : Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0) (𝓝[Hbar] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun y : ℝ => (x : ℂ) + y * Complex.I := by fun_prop
      have h := this.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      show (0 : ℝ) ≤ ((x : ℂ) + y * Complex.I).im
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
      linarith [show (0 : ℝ) < y from hy]
  have hc := ((hFc x (hbar_ofReal x)).tendsto).comp hpath
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  apply hFeq
  show (0 : ℝ) < ((x : ℂ) + y * Complex.I).im
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
  linarith [show (0 : ℝ) < y from hy]

theorem revMapBdry_eq_of_car (hF : Blueprint.IsCaratheodoryRevExt W T F) (x : ℝ) :
    revMapBdry W T x = F x :=
  (tendsto_revMap_of_car hF x).limUnder_eq

theorem continuous_car_real (hF : Blueprint.IsCaratheodoryRevExt W T F) :
    Continuous fun x : ℝ => F x :=
  hF.2.1.comp_continuous Complex.continuous_ofReal hbar_ofReal

theorem weldingHom_zero (W : ℝ → ℝ) (T : ℝ) : weldingHom W T 0 = 0 :=
  le_antisymm (csInf_le ⟨0, fun _ hy => hy.1⟩ ⟨le_rfl, rfl⟩)
    (Real.sInf_nonneg fun _ hy => hy.1)

theorem zeroPlus_nonneg (W : ℝ → ℝ) (T : ℝ) : 0 ≤ zeroPlus W T :=
  Real.sInf_nonneg fun _ hy => hy.1.le

theorem weldingHom_mem_of_car (hF : Blueprint.IsCaratheodoryRevExt W T F) {s : ℝ}
    (hs : s ∈ Icc (zeroMinus W T) 0) :
    0 ≤ weldingHom W T s ∧ F (weldingHom W T s) = F s :=
  ⟨Real.sInf_nonneg fun _ hy => hy.1,
    (hF.2.2.2.2.2.2 _ (hbar_ofReal _) _ (hbar_ofReal _)).2 (Or.inr ⟨s, hs, Or.inr ⟨rfl, rfl⟩⟩)⟩

/-- On `[0₋,0]`, the welding partner is the only nonnegative point with the same image. -/
theorem eq_weldingHom_of_car (hF : Blueprint.IsCaratheodoryRevExt W T F) {s y : ℝ}
    (hs : s ∈ Icc (zeroMinus W T) 0) (hy : 0 ≤ y) (h : F y = F s) : y = weldingHom W T s := by
  have hφ0 := weldingHom_zero W T
  rcases (hF.2.2.2.2.2.2 _ (hbar_ofReal y) _ (hbar_ofReal s)).1 h with
    h' | ⟨t, ht, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · have hys : y = s := Complex.ofReal_injective h'
    have hy0 : s = 0 := le_antisymm hs.2 (hys ▸ hy)
    rw [hys, hy0, hφ0]
  · have hyt : y = t := Complex.ofReal_injective h1
    have hst : s = weldingHom W T t := Complex.ofReal_injective h2
    have ht0 : t = 0 := le_antisymm ht.2 (hyt ▸ hy)
    rw [ht0, hφ0] at hst
    rw [hyt, ht0, hst, hφ0]
  · rw [Complex.ofReal_injective h1, Complex.ofReal_injective h2]

theorem weldingHom_le_zeroPlus_of_car (hF : Blueprint.IsCaratheodoryRevExt W T F) {s : ℝ}
    (hs : s ∈ Icc (zeroMinus W T) 0) : weldingHom W T s ≤ zeroPlus W T := by
  obtain ⟨-, hFs⟩ := weldingHom_mem_of_car hF hs
  by_contra hlt
  push Not at hlt
  have hre : (F (weldingHom W T s)).im = 0 := (hF.2.2.2.2.2.1 _).2 (Or.inr hlt.le)
  rw [hFs] at hre
  rcases (hF.2.2.2.2.2.1 s).1 hre with h | h
  · have hsa : s = zeroMinus W T := le_antisymm h hs.1
    rw [hsa, hF.2.2.2.2.1] at hlt
    exact lt_irrefl _ hlt
  · have hs0 : s = 0 := le_antisymm hs.2 ((zeroPlus_nonneg W T).trans h)
    rw [hs0, weldingHom_zero] at hlt
    linarith [zeroPlus_nonneg W T]

/-- The welding homeomorphism is continuous on `[0₋,0]`: its graph is closed (it is cut out by
`F y = F s`) and it takes values in the compact interval `[0,0₊]`. -/
theorem continuousOn_weldingHom_of_car (hF : Blueprint.IsCaratheodoryRevExt W T F) :
    ContinuousOn (weldingHom W T) (Icc (zeroMinus W T) 0) := by
  intro s₀ hs₀
  have hFr := continuous_car_real hF
  refine (isCompact_Icc (a := (0 : ℝ)) (b := zeroPlus W T)).tendsto_nhds_of_unique_mapClusterPt
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨(weldingHom_mem_of_car hF hs).1, weldingHom_le_zeroPlus_of_car hF hs⟩
  · intro y hy hcl
    have h1 : MapClusterPt (F y) (𝓝[Icc (zeroMinus W T) 0] s₀)
        ((fun x : ℝ => F x) ∘ weldingHom W T) :=
      hcl.continuousAt_comp (f := fun x : ℝ => F x) hFr.continuousAt
    have heq : ((fun x : ℝ => F x) ∘ weldingHom W T) =ᶠ[𝓝[Icc (zeroMinus W T) 0] s₀]
        (fun x : ℝ => F x) := by
      filter_upwards [self_mem_nhdsWithin] with s hs using (weldingHom_mem_of_car hF hs).2
    have h2 : Tendsto (fun x : ℝ => F x) (𝓝[Icc (zeroMinus W T) 0] s₀) (𝓝 (F s₀)) :=
      hFr.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h3 : ClusterPt (F y) (𝓝 (F s₀)) := by
      have h1' : ClusterPt (F y) (map ((fun x : ℝ => F x) ∘ weldingHom W T)
          (𝓝[Icc (zeroMinus W T) 0] s₀)) := h1
      rw [Filter.map_congr heq] at h1'
      exact h1'.mono h2
    exact eq_weldingHom_of_car hF hs₀ hy.1 (eq_of_nhds_neBot h3)

end Car

/-- Two functions continuous on `[a,0]` that agree at the rationals of `[a,0]` agree on it. -/
theorem eqOn_of_eqOn_rat {a : ℝ} (ha : a ≤ 0) {φ φ' : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a 0))
    (hφ' : ContinuousOn φ' (Icc a 0)) (h : ∀ q : ℚ, (q : ℝ) ∈ Icc a 0 → φ q = φ' q) :
    EqOn φ φ' (Icc a 0) := by
  refine Set.EqOn.of_subset_closure (s := Icc a 0 ∩ range ((↑) : ℚ → ℝ)) ?_ hφ hφ'
    inter_subset_left ?_
  · rintro _ ⟨hx, q, rfl⟩
    exact h q hx
  · rcases eq_or_lt_of_le ha with rfl | ha'
    · intro x hx
      have hx0 : x = 0 := le_antisymm hx.2 hx.1
      exact subset_closure ⟨hx, 0, by simp [hx0]⟩
    · calc Icc a 0 = closure (Ioo a 0) := (closure_Ioo ha'.ne).symm
        _ ⊆ closure (Ioo a 0 ∩ range ((↑) : ℚ → ℝ)) :=
          closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
            isClosed_closure
        _ ⊆ closure (Icc a 0 ∩ range ((↑) : ℚ → ℝ)) :=
          closure_mono (inter_subset_inter_left _ Ioo_subset_Icc_self)

/-! ### The welding data -/

/-- **Welding data** of the reverse Loewner flow driven by `W` at time `T`: the point `0₋` and
the welding homeomorphism at the rationals of `[0₋, 0]` (junk `0` at other rationals). -/
def weldingData (W : ℝ → ℝ) (T : ℝ) : ℝ × (ℚ → ℝ) :=
  (zeroMinus W T, fun q => if zeroMinus W T ≤ (q : ℝ) ∧ (q : ℝ) ≤ 0 then weldingHom W T q else 0)

theorem weldingData_congr {W W' : ℝ → ℝ} {T : ℝ} (h : EqOn W W' (Icc 0 T)) :
    weldingData W T = weldingData W' T := by
  have hr : revMap W T = revMap W' T := funext fun z => ReverseFlow.revMap_congr_drive z h
  unfold weldingData weldingHom zeroMinus revMapBdry
  rw [hr]

theorem weldingHom_eqOn_of_weldingData_eq {W W' : ℝ → ℝ} {T T' : ℝ} {F F' : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt W T F) (hF' : Blueprint.IsCaratheodoryRevExt W' T' F')
    (h : weldingData W T = weldingData W' T') :
    zeroMinus W T = zeroMinus W' T' ∧
      EqOn (weldingHom W T) (weldingHom W' T') (Icc (zeroMinus W T) 0) := by
  have h1 : zeroMinus W T = zeroMinus W' T' := congrArg Prod.fst h
  refine ⟨h1, eqOn_of_eqOn_rat (WeldingUniqueness.zeroMinus_nonpos W T)
    (continuousOn_weldingHom_of_car hF) (by rw [h1]; exact continuousOn_weldingHom_of_car hF')
    fun q hq => ?_⟩
  have h2 := congrFun (congrArg Prod.snd h) q
  simp only [weldingData] at h2
  rw [if_pos (show zeroMinus W T ≤ (q : ℝ) ∧ (q : ℝ) ≤ 0 from hq),
    if_pos (show zeroMinus W' T' ≤ (q : ℝ) ∧ (q : ℝ) ≤ 0 by rw [← h1]; exact hq)] at h2
  exact h2

/-- **Injectivity up to the reverse map (A3).** Equal welding data of two simple reverse hulls,
the first one removable, give equal reverse maps and equal terminal driver values. -/
theorem revMap_eq_of_weldingData_eq (hCar : Blueprint.RevMapCaratheodory) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T : ℝ}
    (hT : 0 < T) (hK : IsSimpleCurveHull (revHull W T)) (hK' : IsSimpleCurveHull (revHull W' T))
    (hrem : IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T)))
    (h : weldingData W T = weldingData W' T) :
    EqOn (revMap W' T) (revMap W T) H ∧ W T = W' T := by
  obtain ⟨F, hF⟩ := hCar W hW hW0 T hT hK
  obtain ⟨F', hF'⟩ := hCar W' hW' hW'0 T hT hK'
  obtain ⟨h1, h2⟩ := weldingHom_eqOn_of_weldingData_eq hF hF' h
  have hr := revMap_eq_of_welding_eq hCar hW hW' hW0 hW'0 hT hT hK hK' h1 h2 hrem
  exact ⟨hr, (WeldingUniqueness.drive_and_time_eq_of_revMap_eq hW hW' hT.le hT.le hr).1⟩

/-! ### A Borel version on the path space `C([0,T], ℝ)` -/

section Paths

variable {T : ℝ} (hT : 0 ≤ T)

theorem continuous_revMap_extIccPath {z : ℂ} (hz : 0 < z.im) :
    Continuous fun f : C(Icc (0 : ℝ) T, ℝ) => revMap (extIccPath hT f) T z := by
  refine (LipschitzWith.of_dist_le_mul
    (K := ⟨Real.exp (2 * T / z.im ^ 2), (Real.exp_pos _).le⟩) fun f f' => ?_).continuous
  rw [dist_eq_norm]
  have h := ReverseFlow.norm_revMap_sub_revMap_le _ _ (continuous_extIccPath hT f)
    (continuous_extIccPath hT f') z hz hT (ε := dist f f') fun r hr => by
      rw [extIccPath_of_mem hT f hr, extIccPath_of_mem hT f' hr, ← Real.dist_eq]
      exact ContinuousMap.dist_apply_le_dist _
  calc _ ≤ _ := h
    _ = _ := mul_comm _ _

theorem im_add_height (x : ℝ) (n : ℕ) : 0 < ((x : ℂ) + (height n : ℂ) * Complex.I).im := by
  simpa using height_pos n

/-- Boundary values read along the heights `1/(n+1)`. -/
def bdrySeq (f : C(Icc (0 : ℝ) T, ℝ)) (x : ℝ) : ℂ :=
  limUnder atTop fun n : ℕ => revMap (extIccPath hT f) T (x + (height n : ℂ) * Complex.I)

theorem measurable_bdrySeq (x : ℝ) : Measurable fun f => bdrySeq hT f x :=
  (StronglyMeasurable.limUnder (l := atTop)
    (f := fun (n : ℕ) (f : C(Icc (0 : ℝ) T, ℝ)) =>
      revMap (extIccPath hT f) T (x + (height n : ℂ) * Complex.I))
    fun n => (continuous_revMap_extIccPath hT (im_add_height x n)).measurable.stronglyMeasurable
    ).measurable

theorem bdrySeq_eq_of_car {f : C(Icc (0 : ℝ) T, ℝ)} {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt (extIccPath hT f) T F) (x : ℝ) :
    bdrySeq hT f x = F x :=
  ((tendsto_revMap_of_car hF x).comp tendsto_height).limUnder_eq

/-- Borel version of `0₋`: the supremum of the negative rationals with real boundary value. -/
def zmSeq (f : C(Icc (0 : ℝ) T, ℝ)) : ℝ :=
  sSup (((↑) : ℚ → ℝ) '' {q : ℚ | (q : ℝ) < 0 ∧ (bdrySeq hT f q).im = 0})

theorem measurable_zmSeq : Measurable (zmSeq hT) :=
  measurable_sSup_rat _
    (fun q => measurableSet_setOfPred.2 (measurable_const.and (measurableSet_setOfPred.1
      (measurableSet_eq_fun (Complex.measurable_im.comp (measurable_bdrySeq hT q))
        measurable_const))))
    (fun _ => ⟨0, by rintro _ ⟨q, hq, rfl⟩; exact hq.1.le⟩)

theorem zmSeq_eq_of_car {f : C(Icc (0 : ℝ) T, ℝ)} {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt (extIccPath hT f) T F) :
    zmSeq hT f = zeroMinus (extIccPath hT f) T := by
  have ha := WeldingUniqueness.zeroMinus_nonpos (extIccPath hT f) T
  have hb := zeroPlus_nonneg (extIccPath hT f) T
  have hset : {q : ℚ | (q : ℝ) < 0 ∧ (bdrySeq hT f q).im = 0} =
      {q : ℚ | (q : ℝ) < 0 ∧ (q : ℝ) ≤ zeroMinus (extIccPath hT f) T} := by
    ext q
    simp only [mem_ofPred_eq, bdrySeq_eq_of_car hT hF]
    constructor
    · rintro ⟨hq, h⟩
      refine ⟨hq, ?_⟩
      rcases (hF.2.2.2.2.2.1 q).1 h with h' | h'
      · exact h'
      · linarith
    · rintro ⟨hq, h⟩
      exact ⟨hq, (hF.2.2.2.2.2.1 q).2 (Or.inl h)⟩
  unfold zmSeq
  rw [hset]
  obtain ⟨q₀, hq₀⟩ := exists_rat_lt (zeroMinus (extIccPath hT f) T - 1)
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨_, q₀, ⟨by linarith, by linarith⟩, rfl⟩ ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact hq.2
  · intro c hc
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hc
    exact ⟨_, ⟨q, ⟨by linarith, hq2.le⟩, rfl⟩, hq1⟩

/-- Borel version of the welding homeomorphism. -/
def whSeq (f : C(Icc (0 : ℝ) T, ℝ)) (x : ℝ) : ℝ :=
  sInf (((↑) : ℚ → ℝ) '' {r : ℚ | 0 ≤ (r : ℝ) ∧ ∀ n : ℕ, ∃ y : ℚ, 0 ≤ (y : ℝ) ∧
    (y : ℝ) ≤ r ∧ ‖bdrySeq hT f y - bdrySeq hT f x‖ < height n})

theorem measurable_whSeq (x : ℝ) : Measurable fun f => whSeq hT f x :=
  measurable_sInf_rat _
    (fun r => measurableSet_setOfPred.2 (measurable_const.and (Measurable.forall fun n =>
      Measurable.exists fun y => measurable_const.and (measurable_const.and
        (measurableSet_setOfPred.1 (measurableSet_lt
          ((measurable_bdrySeq hT y).sub (measurable_bdrySeq hT x)).norm measurable_const))))))
    (fun _ => ⟨0, by rintro _ ⟨r, hr, rfl⟩; exact hr.1⟩)

theorem whSeq_eq_of_car {f : C(Icc (0 : ℝ) T, ℝ)} {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt (extIccPath hT f) T F) {s : ℝ}
    (hs : s ∈ Icc (zeroMinus (extIccPath hT f) T) 0) :
    whSeq hT f s = weldingHom (extIccPath hT f) T s := by
  obtain ⟨hm0, hmF⟩ := weldingHom_mem_of_car hF hs
  unfold whSeq
  simp only [bdrySeq_eq_of_car hT hF]
  exact sInf_rat_cond_eq (G := fun y : ℝ => F y) (continuous_car_real hF) (F s) hm0 hmF
    fun y hy hyF => (eq_weldingHom_of_car hF hs hy hyF).ge

/-- Borel version of the welding data. -/
def weldingDataC (f : C(Icc (0 : ℝ) T, ℝ)) : ℝ × (ℚ → ℝ) :=
  (zmSeq hT f, fun q => if zmSeq hT f ≤ (q : ℝ) ∧ (q : ℝ) ≤ 0 then whSeq hT f q else 0)

theorem measurable_weldingDataC : Measurable (weldingDataC hT) := by
  refine (measurable_zmSeq hT).prodMk (measurable_pi_iff.2 fun q => ?_)
  refine Measurable.ite ?_ (measurable_whSeq hT q) measurable_const
  exact (measurableSet_le (measurable_zmSeq hT) measurable_const).inter
    (MeasurableSet.const _)

theorem weldingDataC_eq_of_car {f : C(Icc (0 : ℝ) T, ℝ)} {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt (extIccPath hT f) T F) :
    weldingDataC hT f = weldingData (extIccPath hT f) T := by
  have hz := zmSeq_eq_of_car hT hF
  simp only [weldingDataC, weldingData, hz, Prod.mk.injEq, true_and]
  funext q
  split_ifs with hq
  · exact whSeq_eq_of_car hT hF hq
  · rfl

theorem weldingDataC_eq (hCar : Blueprint.RevMapCaratheodory) (hT' : 0 < T)
    {f : C(Icc (0 : ℝ) T, ℝ)} (hf0 : extIccPath hT f 0 = 0)
    (hK : IsSimpleCurveHull (revHull (extIccPath hT f) T)) :
    weldingDataC hT f = weldingData (extIccPath hT f) T := by
  obtain ⟨F, hF⟩ := hCar _ (continuous_extIccPath hT f) hf0 T hT' hK
  exact weldingDataC_eq_of_car hT hF

/-- Driver values at (clamped) rational times, as a function of the path. -/
def sampleC (f : C(Icc (0 : ℝ) T, ℝ)) : ℚ → ℝ := sampleDrive T (extIccPath hT f)

theorem measurable_sampleC : Measurable (sampleC hT) :=
  measurable_pi_iff.2 fun q =>
    (continuous_eval_const (projIcc 0 T hT (max 0 (min (q : ℝ) T)))).measurable

theorem injective_sampleC : Function.Injective (sampleC hT) := by
  intro f f' h
  ext ⟨t, ht⟩
  have e1 := recoverDrive_sampleDrive (continuous_extIccPath hT f) ht
  have e2 := recoverDrive_sampleDrive (continuous_extIccPath hT f') ht
  have : extIccPath hT f t = extIccPath hT f' t := by
    rw [← e1, ← e2]
    exact congrArg (fun z => recoverDrive z t) h
  rwa [extIccPath_of_mem hT f ht, extIccPath_of_mem hT f' ht] at this

/-- **Lusin–Souslin assembly.** A Borel map of paths that is injective on a Borel set `G` gives
a Borel partial graph in (its values) × (driver at rational times) containing the pairs coming
from `G`. -/
theorem exists_partialGraph_of_injOn {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (Φ : C(Icc (0 : ℝ) T, ℝ) → S) (hΦ : Measurable Φ) {G : Set C(Icc (0 : ℝ) T, ℝ)}
    (hG : MeasurableSet G) (hinj : InjOn Φ G) :
    ∃ G' : Set (S × (ℚ → ℝ)), MeasurableSet G' ∧ IsPartialGraph G' ∧
      ∀ f ∈ G, (Φ f, sampleC hT f) ∈ G' := by
  refine ⟨(fun f => (Φ f, sampleC hT f)) '' G,
    hG.image_of_measurable_injOn (hΦ.prodMk (measurable_sampleC hT))
      (fun f _ f' _ h => injective_sampleC hT (congrArg Prod.snd h)), ?_,
    fun f hf => ⟨f, hf, rfl⟩⟩
  rintro d z z' ⟨f, hf, hfe⟩ ⟨f', hf', hfe'⟩
  simp only [Prod.mk.injEq] at hfe hfe'
  rw [← hfe.2, ← hfe'.2, hinj hf hf' (hfe.1.trans hfe'.1.symm)]

/-- Injectivity of the Borel welding data on a set of good paths, reduced to the statement that
the reverse map at time `T` determines the path. -/
theorem injOn_weldingDataC (hCar : Blueprint.RevMapCaratheodory) (hT' : 0 < T)
    {G : Set C(Icc (0 : ℝ) T, ℝ)}
    (hgood : ∀ f ∈ G, extIccPath hT f 0 = 0 ∧ IsSimpleCurveHull (revHull (extIccPath hT f) T) ∧
      IsConformallyRemovable (closure (revHull (extIccPath hT f) T) ∪
        conj '' closure (revHull (extIccPath hT f) T)))
    (hdet : ∀ f ∈ G, ∀ f' ∈ G,
      EqOn (revMap (extIccPath hT f') T) (revMap (extIccPath hT f) T) H → f = f') :
    InjOn (weldingDataC hT) G := by
  intro f hf f' hf' h
  obtain ⟨h0, hK, hrem⟩ := hgood f hf
  obtain ⟨h0', hK', -⟩ := hgood f' hf'
  rw [weldingDataC_eq hT hCar hT' h0 hK, weldingDataC_eq hT hCar hT' h0' hK'] at h
  exact hdet f hf f' hf' (revMap_eq_of_weldingData_eq hCar (continuous_extIccPath hT f)
    (continuous_extIccPath hT f') h0 h0' hT' hK hK' hrem h).1

end Paths

/-! ### The random driver -/

open Classical in
/-- The restriction of a driver to `[0,T]`, as an element of `C([0,T], ℝ)` (junk `0` if the
driver is not continuous). -/
def pathC (T : ℝ) (W : ℝ → ℝ) : C(Icc (0 : ℝ) T, ℝ) :=
  if h : Continuous W then ⟨fun x => W x, h.comp continuous_subtype_val⟩ else 0

theorem extIccPath_pathC {T : ℝ} (hT : 0 ≤ T) {W : ℝ → ℝ} (hW : Continuous W) :
    EqOn (extIccPath hT (pathC T W)) W (Icc 0 T) := by
  intro t ht
  rw [extIccPath_of_mem hT _ ht]
  simp [pathC, hW]

/-- **Welding data determines the driver, given a good Borel set.** Let `V` be a random driver
and `G` a Borel set of paths on `[0,T]` containing the restriction of `V` almost surely, on
which the reverse hulls are simple (so the Borel welding data is the welding data) and the
Borel welding data is injective. Then there is a Borel partial graph in
(welding data) × (driver at rational times) containing `(weldingData V T, V|ℚ)` almost
surely. -/
theorem exists_weldingGraph_of_goodSet (hCar : Blueprint.RevMapCaratheodory) {T : ℝ}
    (hT : 0 < T) {G : Set C(Icc (0 : ℝ) T, ℝ)} (hG : MeasurableSet G)
    (hgood : ∀ f ∈ G, extIccPath hT.le f 0 = 0 ∧
      IsSimpleCurveHull (revHull (extIccPath hT.le f) T))
    (hinj : InjOn (weldingDataC hT.le) G) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : Ω → ℝ → ℝ) (hV : ∀ᵐ ω ∂P, Continuous (V ω) ∧ pathC T (V ω) ∈ G) :
    ∃ G' : Set ((ℝ × (ℚ → ℝ)) × (ℚ → ℝ)), MeasurableSet G' ∧ IsPartialGraph G' ∧
      ∀ᵐ ω ∂P, (weldingData (V ω) T, sampleDrive T (V ω)) ∈ G' := by
  obtain ⟨G', hG'm, hG'g, hG'mem⟩ :=
    exists_partialGraph_of_injOn hT.le (weldingDataC hT.le) (measurable_weldingDataC hT.le) hG
      hinj
  refine ⟨G', hG'm, hG'g, ?_⟩
  filter_upwards [hV] with ω ⟨hc, hmem⟩
  have hagree := extIccPath_pathC hT.le hc
  obtain ⟨h0, hK⟩ := hgood _ hmem
  have h1 : weldingData (V ω) T = weldingDataC hT.le (pathC T (V ω)) := by
    rw [weldingDataC_eq hT.le hCar hT h0 hK]
    exact weldingData_congr fun t ht => (hagree ht).symm
  have h2 : sampleDrive T (V ω) = sampleC hT.le (pathC T (V ω)) := by
    funext q
    have hq : max 0 (min (q : ℝ) T) ∈ Icc (0 : ℝ) T :=
      ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
    exact (hagree hq).symm
  rw [h1, h2]
  exact hG'mem _ hmem

end Thm14WeldingData

end QuantumZipper
