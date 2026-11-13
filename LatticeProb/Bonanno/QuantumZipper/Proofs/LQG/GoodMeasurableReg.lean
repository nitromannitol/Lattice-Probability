/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.GoodMeasurableReg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# M4-R5(a), part 1: regularity is a measurable property of field samples

We prove `MeasurableSet {x : FieldSample | IsRegularSample x}` by characterizing regularity
through countably many conditions on measurable functions of `x`
(`isRegularSample_iff_cert`):

* `C1`: at each dyadic radius `2^{-k}`, the raw values `x (fc(d, 2^{-k}))` at dyadic centres
  `d ∈ Hbar` are uniformly continuous on bounded sets (so `avgReg x k` is their continuous
  extension to `Hbar`);
* `C2`: the smoothings `Φ_i(q) = ∫ avgReg x i d(fc q)` are uniformly Cauchy on the countable dense
  set of dyadic points `qpt j` of each box (hence converge locally uniformly on `Hbar × (0,∞)`
  to the canonical witness `canon x q = evalReg x (fc q)`);
* `C3`: `canon x (d, 2^{-k}) = x (fc(d, 2^{-k}))` at dyadic centres;
* `C4`: clause (ii) of regularity at dyadic smoothing radii and dyadic points.

The tool for `C4` is the joint measurability of `(x, u) ↦ evalReg x (fc(u, ρ))`
(`measurable_evalReg_fc_joint`), from the circle kernel.
-/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace QuantumZipper

namespace GoodMeas

open RegClosure (tendsto_dyadicRoundC fc_ae_mem_Hbar continuousOn_slice tluo_comp_tendsto
  tendsto_radius_nhdsGT continuousOn_integral_fc)
open CircleCont (lpt dyadicRoundC_eq_lpt abs_dyadicRound_sub_le)

/-! ## Measurability tools -/

/-- Joint measurability of `(x, u) ↦ evalReg x (fc(u, ρ))` at a fixed radius. -/
theorem measurable_evalReg_fc_joint (ρ : ℝ) :
    Measurable fun p : FieldSample × ℂ => evalReg p.1 (foldedCircle p.2 ρ) := by
  unfold evalReg
  have hk : ∀ k : ℕ, StronglyMeasurable
      (fun p : FieldSample × ℂ => ∫ w, avgReg p.1 k w ∂foldedCircle p.2 ρ) := fun k =>
    StronglyMeasurable.integral_kernel_prod_right'
      (κ := (CircleFubini.circleKernel ρ).comap Prod.snd measurable_snd)
      (f := fun q : (FieldSample × ℂ) × ℂ => avgReg q.1.1 k q.2)
      ((measurable_avgReg k).comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hk).measurable

theorem measurable_integral_avgReg (k : ℕ) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun x : FieldSample => ∫ w, avgReg x k w ∂ν :=
  (StronglyMeasurable.integral_prod_right' (f := fun p : FieldSample × ℂ => avgReg p.1 k p.2)
    (measurable_avgReg k).stronglyMeasurable).measurable

theorem measurable_integral_evalReg_fc (ρ : ℝ) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun x : FieldSample => ∫ u, evalReg x (foldedCircle u ρ) ∂ν :=
  (StronglyMeasurable.integral_prod_right'
    (f := fun p : FieldSample × ℂ => evalReg p.1 (foldedCircle p.2 ρ))
    (measurable_evalReg_fc_joint ρ).stronglyMeasurable).measurable

theorem mprop_abs_le {X : Type*} [MeasurableSpace X] {f g : X → ℝ} (hf : Measurable f)
    (hg : Measurable g) (c : ℝ) : Measurable fun x => |f x - g x| ≤ c := by
  have h : MeasurableSet {x | |f x - g x| ≤ c} :=
    measurableSet_le (continuous_abs.measurable.comp (hf.sub hg) :
      Measurable fun x => |f x - g x|) measurable_const
  exact measurableSet_setOfPred.1 h

/-! ## Dyadic points -/

theorem dyadicRoundC_lpt {n m : ℕ} (h : n ≤ m) (a b : ℤ) :
    dyadicRoundC m (lpt n a b) = lpt n a b := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  have key : ∀ c : ℤ, dyadicRound (n + j) ((c : ℝ) / 2 ^ n) = (c : ℝ) / 2 ^ n := by
    intro c
    have e : (2 : ℝ) ^ (n + j) * ((c : ℝ) / 2 ^ n) = ((c * 2 ^ j : ℤ) : ℝ) := by
      push_cast; rw [pow_add]; field_simp
    rw [dyadicRound, e, Int.floor_intCast]; push_cast; rw [pow_add]; field_simp
  unfold dyadicRoundC lpt
  dsimp only
  rw [key, key]

theorem dyadicRound_le' (n : ℕ) (r : ℝ) : dyadicRound n r ≤ r := by
  unfold dyadicRound
  rw [div_le_iff₀ (by positivity)]
  linarith [Int.floor_le ((2 : ℝ) ^ n * r)]

theorem tendsto_dyadicRound' (r : ℝ) : Tendsto (fun n => dyadicRound n r) atTop (𝓝 r) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ => 1 / (2 : ℝ) ^ n) (fun n => norm_nonneg _) (fun n => by
    rw [Real.norm_eq_abs]; exact abs_dyadicRound_sub_le n r) ?_
  have : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa [one_div, inv_pow] using this

/-- The parameter domain `Hbar × (0,∞)`. -/
abbrev Sd : Set (ℂ × ℝ) := Hbar ×ˢ Ioi 0

/-- Open boxes exhausting `Hbar × (0,∞)`. -/
def box (m : ℕ) : Set (ℂ × ℝ) := {q | ‖q.1‖ < m ∧ q.2 < m ∧ 1 < (m : ℝ) * q.2}

/-- Compact boxes containing `box m ∩ Sd`. -/
def kbox (m : ℕ) : Set (ℂ × ℝ) :=
  (Metric.closedBall (0 : ℂ) m ∩ Hbar) ×ˢ Icc (1 / ((m : ℝ) + 1)) m

theorem isOpen_box (m : ℕ) : IsOpen (box m) :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    ((isOpen_lt continuous_snd continuous_const).inter
      (isOpen_lt continuous_const (continuous_const.mul continuous_snd)))

theorem exists_box {p : ℂ × ℝ} (hp : 0 < p.2) : ∃ m : ℕ, p ∈ box m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (‖p.1‖ + p.2 + 1 / p.2)
  have h0 : 0 < 1 / p.2 := by positivity
  have hn := norm_nonneg p.1
  refine ⟨m, show _ ∧ _ ∧ _ from ⟨by linarith, by linarith, ?_⟩⟩
  have h1 : 1 / p.2 < m := by linarith
  rw [div_lt_iff₀ hp] at h1
  linarith

theorem isCompact_kbox (m : ℕ) : IsCompact (kbox m) :=
  ((isCompact_closedBall _ _).inter_right isClosed_Hbar).prod isCompact_Icc

theorem kbox_subset (m : ℕ) : kbox m ⊆ Sd := fun q hq =>
  ⟨hq.1.2, lt_of_lt_of_le (by positivity) hq.2.1⟩

theorem box_inter_subset (m : ℕ) : box m ∩ Sd ⊆ kbox m := by
  rintro q ⟨⟨h1, h2, h3⟩, hH, hr⟩
  have hr : 0 < q.2 := hr
  refine ⟨⟨by simpa using h1.le, hH⟩, ?_, h2.le⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Dyadic points of `ℂ × ℝ`. -/
def qpt (j : ℕ × ℤ × ℤ × ℤ) : ℂ × ℝ := (lpt j.1 j.2.1 j.2.2.1, (j.2.2.2 : ℝ) / 2 ^ j.1)

/-- The index of the dyadic rounding of `p` at level `n`. -/
def qIdx (n : ℕ) (p : ℂ × ℝ) : ℕ × ℤ × ℤ × ℤ :=
  (n, ⌊(2 : ℝ) ^ n * p.1.re⌋, ⌊(2 : ℝ) ^ n * p.1.im⌋, ⌊(2 : ℝ) ^ n * p.2⌋)

theorem qpt_qIdx (n : ℕ) (p : ℂ × ℝ) :
    qpt (qIdx n p) = (dyadicRoundC n p.1, dyadicRound n p.2) := rfl

theorem tendsto_qpt (p : ℂ × ℝ) : Tendsto (fun n => qpt (qIdx n p)) atTop (𝓝 p) := by
  simp only [qpt_qIdx]
  exact (tendsto_dyadicRoundC p.1).prodMk_nhds (tendsto_dyadicRound' p.2)

theorem eventually_qpt_mem {p : ℂ × ℝ} (hp : p ∈ Sd) {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    (hpU : p ∈ U) : ∀ᶠ n in atTop, qpt (qIdx n p) ∈ Sd ∩ U := by
  have h1 : ∀ᶠ n in atTop, qpt (qIdx n p) ∈ U := tendsto_qpt p (hU.mem_nhds hpU)
  have h2 : ∀ᶠ n in atTop, 0 < dyadicRound n p.2 :=
    (tendsto_dyadicRound' p.2).eventually (Ioi_mem_nhds hp.2)
  filter_upwards [h1, h2] with n hn1 hn2
  rw [qpt_qIdx] at hn1 ⊢
  exact ⟨⟨CircleCont.dyadicRoundC_mem_Hbar hp.1 n, hn2⟩, hn1⟩

/-- Density: a bound at the dyadic points of a box extends to the box. -/
theorem le_of_qpt {φ : ℂ × ℝ → ℝ} {p : ℂ × ℝ} (hp : p ∈ Sd) {m : ℕ} (hpm : p ∈ box m)
    (hφ : ContinuousWithinAt φ Sd p) {c : ℝ}
    (h : ∀ j, qpt j ∈ Sd → qpt j ∈ box m → φ (qpt j) ≤ c) : φ p ≤ c := by
  have hq := eventually_qpt_mem hp (isOpen_box m) hpm
  have ht : Tendsto (fun n => qpt (qIdx n p)) atTop (𝓝[Sd] p) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_qpt p, hq.mono fun n hn => hn.1⟩
  exact le_of_tendsto (hφ.tendsto.comp ht) (hq.mono fun n hn => h _ hn.1 hn.2)

/-- Density with an extra dyadic radius parameter. -/
theorem le_of_qpt₂ {φ : ℝ × (ℂ × ℝ) → ℝ} {ρ δ : ℝ} {p : ℂ × ℝ} (hρ : 0 < ρ) (hρδ : ρ < δ)
    (hp : p ∈ Sd) {m : ℕ} (hpm : p ∈ box m) (hφ : ContinuousWithinAt φ (Ioi 0 ×ˢ Sd) (ρ, p))
    {c : ℝ} (h : ∀ (n : ℕ) (b : ℤ) j, 0 < (b : ℝ) / 2 ^ n → (b : ℝ) / 2 ^ n < δ →
      qpt j ∈ Sd → qpt j ∈ box m → φ ((b : ℝ) / 2 ^ n, qpt j) ≤ c) : φ (ρ, p) ≤ c := by
  have hρn : ∀ᶠ n in atTop, 0 < dyadicRound n ρ :=
    (tendsto_dyadicRound' ρ).eventually (Ioi_mem_nhds hρ)
  have hq := eventually_qpt_mem hp (isOpen_box m) hpm
  have ht : Tendsto (fun n => (dyadicRound n ρ, qpt (qIdx n p))) atTop
      (𝓝[Ioi 0 ×ˢ Sd] (ρ, p)) :=
    tendsto_nhdsWithin_iff.2 ⟨(tendsto_dyadicRound' ρ).prodMk_nhds (tendsto_qpt p),
      (hρn.and hq).mono fun n hn => ⟨hn.1, hn.2.1⟩⟩
  refine le_of_tendsto (hφ.tendsto.comp ht) ((hρn.and hq).mono fun n hn => ?_)
  exact h n ⌊(2 : ℝ) ^ n * ρ⌋ (qIdx n p) hn.1 ((dyadicRound_le' n ρ).trans_lt hρδ) hn.2.1 hn.2.2

/-! ## The countable certificate -/

/-- Raw folded-circle value at a dyadic radius. -/
def raw (x : FieldSample) (d : ℂ) (k : ℕ) : ℝ := x (foldedCircle d (radius k))

/-- The canonical regularity witness. -/
def canon (x : FieldSample) (q : ℂ × ℝ) : ℝ := evalReg x (foldedCircle q.1 q.2)

/-- Smoothing of `avgReg x i` along folded circles. -/
def Phi (x : FieldSample) (i : ℕ) (q : ℂ × ℝ) : ℝ := ∫ w, avgReg x i w ∂foldedCircle q.1 q.2

/-- Smoothing of the canonical witness at radius `ρ`. -/
def smoothC (x : FieldSample) (ρ : ℝ) (q : ℂ × ℝ) : ℝ :=
  ∫ u, canon x (u, ρ) ∂foldedCircle q.1 q.2

/-- Uniform continuity of the raw dyadic values on bounded sets. -/
def C1 (x : FieldSample) : Prop :=
  ∀ k M e : ℕ, ∃ j : ℕ, ∀ (n : ℕ) (a b : ℤ) (n' : ℕ) (a' b' : ℤ),
    lpt n a b ∈ Hbar → lpt n' a' b' ∈ Hbar → ‖lpt n a b‖ ≤ M → ‖lpt n' a' b'‖ ≤ M →
    ‖lpt n a b - lpt n' a' b'‖ < 1 / ((j : ℝ) + 1) →
    |raw x (lpt n a b) k - raw x (lpt n' a' b') k| ≤ 1 / ((e : ℝ) + 1)

/-- Uniform Cauchy property of the smoothings `Phi x i` at dyadic points of the boxes. -/
def C2 (x : FieldSample) : Prop :=
  ∀ m e : ℕ, ∃ J : ℕ, ∀ i : ℕ, J ≤ i → ∀ i' : ℕ, J ≤ i' → ∀ j : ℕ × ℤ × ℤ × ℤ,
    qpt j ∈ Sd → qpt j ∈ box m → |Phi x i (qpt j) - Phi x i' (qpt j)| ≤ 1 / ((e : ℝ) + 1)

/-- The canonical witness matches the raw values at dyadic centres and radii. -/
def C3 (x : FieldSample) : Prop :=
  ∀ (k n : ℕ) (a b : ℤ), lpt n a b ∈ Hbar → canon x (lpt n a b, radius k) = raw x (lpt n a b) k

/-- Clause (ii) of regularity at dyadic smoothing radii and dyadic points. -/
def C4 (x : FieldSample) : Prop :=
  ∀ m e : ℕ, ∃ J : ℕ, ∀ (n : ℕ) (b : ℤ), 0 < (b : ℝ) / 2 ^ n → (b : ℝ) / 2 ^ n < 1 / ((J : ℝ) + 1) →
    ∀ j : ℕ × ℤ × ℤ × ℤ, qpt j ∈ Sd → qpt j ∈ box m →
      |smoothC x ((b : ℝ) / 2 ^ n) (qpt j) - canon x (qpt j)| ≤ 1 / ((e : ℝ) + 1)

/-! ### Measurability of the certificate -/

theorem measurable_raw (d : ℂ) (k : ℕ) : Measurable fun x : FieldSample => raw x d k :=
  measurable_pi_apply _

theorem measurable_canon (q : ℂ × ℝ) : Measurable fun x : FieldSample => canon x q :=
  measurable_evalReg _

theorem measurable_Phi (i : ℕ) (q : ℂ × ℝ) : Measurable fun x : FieldSample => Phi x i q :=
  measurable_integral_avgReg i _

theorem measurable_smoothC (ρ : ℝ) (q : ℂ × ℝ) : Measurable fun x : FieldSample => smoothC x ρ q :=
  measurable_integral_evalReg_fc ρ _

theorem measurable_C1 : Measurable C1 := by
  unfold C1
  refine Measurable.forall fun k => Measurable.forall fun M => Measurable.forall fun e =>
    Measurable.exists fun j => ?_
  refine Measurable.forall fun n => Measurable.forall fun a => Measurable.forall fun b =>
    Measurable.forall fun n' => Measurable.forall fun a' => Measurable.forall fun b' => ?_
  refine measurable_const.imp (measurable_const.imp (measurable_const.imp
    (measurable_const.imp (measurable_const.imp ?_))))
  exact mprop_abs_le (measurable_raw _ _) (measurable_raw _ _) _

theorem measurable_C2 : Measurable C2 := by
  unfold C2
  refine Measurable.forall fun m => Measurable.forall fun e => Measurable.exists fun J => ?_
  refine Measurable.forall fun i => measurable_const.imp (Measurable.forall fun i' =>
    measurable_const.imp (Measurable.forall fun j => measurable_const.imp
      (measurable_const.imp ?_)))
  exact mprop_abs_le (measurable_Phi _ _) (measurable_Phi _ _) _

theorem measurable_C3 : Measurable C3 := by
  unfold C3
  refine Measurable.forall fun k => Measurable.forall fun n => Measurable.forall fun a =>
    Measurable.forall fun b => measurable_const.imp ?_
  exact measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_canon _) (measurable_raw _ _))

theorem measurable_C4 : Measurable C4 := by
  unfold C4
  refine Measurable.forall fun m => Measurable.forall fun e => Measurable.exists fun J => ?_
  refine Measurable.forall fun n => Measurable.forall fun b => measurable_const.imp
    (measurable_const.imp (Measurable.forall fun j => measurable_const.imp
      (measurable_const.imp ?_)))
  exact mprop_abs_le (measurable_smoothC _ _) (measurable_canon _) _

/-! ### Regular samples satisfy the certificate -/

theorem raw_eq_of_regular {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F) (k : ℕ)
    {n : ℕ} {a b : ℤ} (hd : lpt n a b ∈ Hbar) : raw x (lpt n a b) k = F (lpt n a b, radius k) := by
  refine tendsto_nhds_unique ?_ (h.2.1 k _ hd)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [dyadicRoundC_lpt hm]; rfl

theorem C1_of_regular {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F) : C1 x := by
  intro k M e
  have hK : IsCompact (Metric.closedBall (0 : ℂ) M ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have huc := hK.uniformContinuousOn_of_continuous
    ((continuousOn_slice h.1 (radius_pos k)).mono inter_subset_right)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (1 / ((e : ℝ) + 1)) (by positivity)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  refine ⟨j, fun n a b n' a' b' h1 h2 h3 h4 h5 => ?_⟩
  rw [raw_eq_of_regular h k h1, raw_eq_of_regular h k h2]
  have := hδ' _ ⟨by simpa using h3, h1⟩ _ ⟨by simpa using h4, h2⟩
    (by rw [dist_eq_norm]; exact h5.trans hj)
  rw [Real.dist_eq] at this
  exact this.le

theorem tluo_Phi {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F) :
    TendstoLocallyUniformlyOn (Phi x) F atTop Sd := by
  have e : Phi x = fun i q => ∫ u, F (u, radius i) ∂foldedCircle q.1 q.2 :=
    funext fun i => funext fun q =>
      integral_congr_ae ((fc_ae_mem_Hbar _ _).mono fun u hu => h.avgReg_eq i hu)
  rw [e]
  exact tluo_comp_tendsto h.2.2 tendsto_radius_nhdsGT

theorem C2_of_regular {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F) : C2 x := by
  intro m e
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_kbox m)).1
    ((tluo_Phi h).mono (kbox_subset m))
  rw [Metric.tendstoUniformlyOn_iff] at hu
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hu (1 / ((e : ℝ) + 1) / 2) (by positivity))
  refine ⟨J, fun i hi i' hi' j hj1 hj2 => ?_⟩
  have h1 := hJ i hi _ (box_inter_subset m ⟨hj2, hj1⟩)
  have h2 := hJ i' hi' _ (box_inter_subset m ⟨hj2, hj1⟩)
  rw [Real.dist_eq, abs_lt] at h1 h2
  rw [abs_le]
  constructor <;> linarith

theorem C3_of_regular {x : FieldSample} (h : IsRegularWith x (canon x)) : C3 x :=
  fun k _ _ _ hd => (raw_eq_of_regular h k hd).symm

theorem C4_of_regular {x : FieldSample} (h : IsRegularWith x (canon x)) : C4 x := by
  intro m e
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_kbox m)).1
    (h.2.2.mono (kbox_subset m))
  rw [Metric.tendstoUniformlyOn_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (hu (1 / ((e : ℝ) + 1)) (by positivity)))
  obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hδ
  refine ⟨J, fun n b hb1 hb2 j hj1 hj2 => ?_⟩
  have := hδ' (y := (b : ℝ) / 2 ^ n) (by rw [Real.dist_eq, sub_zero, abs_of_pos hb1]; linarith)
    hb1 _ (box_inter_subset m ⟨hj2, hj1⟩)
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this.le

/-! ### The certificate implies regularity -/

theorem hj_dyadic {x : FieldSample} {k M e j : ℕ}
    (hj : ∀ (n : ℕ) (a b : ℤ) (n' : ℕ) (a' b' : ℤ),
      lpt n a b ∈ Hbar → lpt n' a' b' ∈ Hbar → ‖lpt n a b‖ ≤ M → ‖lpt n' a' b'‖ ≤ M →
      ‖lpt n a b - lpt n' a' b'‖ < 1 / ((j : ℝ) + 1) →
      |raw x (lpt n a b) k - raw x (lpt n' a' b') k| ≤ 1 / ((e : ℝ) + 1))
    (n n' : ℕ) (z z' : ℂ) (h1 : dyadicRoundC n z ∈ Hbar) (h2 : dyadicRoundC n' z' ∈ Hbar)
    (h3 : ‖dyadicRoundC n z‖ ≤ M) (h4 : ‖dyadicRoundC n' z'‖ ≤ M)
    (h5 : ‖dyadicRoundC n z - dyadicRoundC n' z'‖ < 1 / ((j : ℝ) + 1)) :
    |raw x (dyadicRoundC n z) k - raw x (dyadicRoundC n' z') k| ≤ 1 / ((e : ℝ) + 1) :=
  hj n ⌊(2 : ℝ) ^ n * z.re⌋ ⌊(2 : ℝ) ^ n * z.im⌋ n' ⌊(2 : ℝ) ^ n' * z'.re⌋
    ⌊(2 : ℝ) ^ n' * z'.im⌋ h1 h2 h3 h4 h5

theorem raw_close {x : FieldSample} {k M e j : ℕ}
    (hj : ∀ (n : ℕ) (a b : ℤ) (n' : ℕ) (a' b' : ℤ),
      lpt n a b ∈ Hbar → lpt n' a' b' ∈ Hbar → ‖lpt n a b‖ ≤ M → ‖lpt n' a' b'‖ ≤ M →
      ‖lpt n a b - lpt n' a' b'‖ < 1 / ((j : ℝ) + 1) →
      |raw x (lpt n a b) k - raw x (lpt n' a' b') k| ≤ 1 / ((e : ℝ) + 1))
    {z z' : ℂ} (hz : z ∈ Hbar) (hz' : z' ∈ Hbar) (hzM : ‖z‖ < M) (hz'M : ‖z'‖ < M)
    (hzz : ‖z - z'‖ < 1 / ((j : ℝ) + 1)) :
    ∃ N, ∀ n ≥ N, ∀ n' ≥ N,
      |raw x (dyadicRoundC n z) k - raw x (dyadicRoundC n' z') k| ≤ 1 / ((e : ℝ) + 1) := by
  set η := min (min ((M : ℝ) - ‖z‖) (M - ‖z'‖)) ((1 / ((j : ℝ) + 1) - ‖z - z'‖) / 2) with hη
  have hη0 : 0 < η := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hη1 : η ≤ M - ‖z‖ := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ M - ‖z'‖ := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η ≤ (1 / ((j : ℝ) + 1) - ‖z - z'‖) / 2 := min_le_right _ _
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 (tendsto_dyadicRoundC z) η hη0
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 (tendsto_dyadicRoundC z') η hη0
  refine ⟨max N1 N2, fun n hn n' hn' => ?_⟩
  have h1 : ‖dyadicRoundC n z - z‖ < η := by
    rw [← dist_eq_norm]; exact hN1 n (le_of_max_le_left hn)
  have h2 : ‖dyadicRoundC n' z' - z'‖ < η := by
    rw [← dist_eq_norm]; exact hN2 n' (le_of_max_le_right hn')
  have n1 := norm_sub_norm_le (dyadicRoundC n z) z
  have n2 := norm_sub_norm_le (dyadicRoundC n' z') z'
  have hdiff : ‖dyadicRoundC n z - dyadicRoundC n' z'‖ < 1 / ((j : ℝ) + 1) := by
    calc ‖dyadicRoundC n z - dyadicRoundC n' z'‖
        = ‖(dyadicRoundC n z - z) + (z - z') - (dyadicRoundC n' z' - z')‖ := by
          congr 1; ring
      _ ≤ ‖dyadicRoundC n z - z‖ + ‖z - z'‖ + ‖dyadicRoundC n' z' - z'‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ < 1 / ((j : ℝ) + 1) := by linarith
  exact hj_dyadic hj n n' z z' (CircleCont.dyadicRoundC_mem_Hbar hz n)
    (CircleCont.dyadicRoundC_mem_Hbar hz' n') (by linarith) (by linarith) hdiff

theorem tendsto_raw_of_C1 {x : FieldSample} (h : C1 x) (k : ℕ) {z : ℂ} (hz : z ∈ Hbar) :
    Tendsto (fun n => raw x (dyadicRoundC n z) k) atTop (𝓝 (avgReg x k z)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
    (Metric.cauchySeq_iff.2 fun ε hε => ?_))
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
  obtain ⟨j, hj⟩ := h k (⌈‖z‖⌉₊ + 1) e
  have hc := Nat.le_ceil ‖z‖
  have hzM : ‖z‖ < ((⌈‖z‖⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨N, hN⟩ := raw_close hj hz hz hzM hzM (by rw [sub_self, norm_zero]; positivity)
  exact ⟨N, fun n hn n' hn' => by rw [Real.dist_eq]; exact (hN n hn n' hn').trans_lt he⟩

theorem continuousOn_avgReg_of_C1 {x : FieldSample} (h : C1 x) (k : ℕ) :
    ContinuousOn (avgReg x k) Hbar := by
  rw [Metric.continuousOn_iff]
  intro z0 hz0 ε hε
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
  obtain ⟨j, hj⟩ := h k (⌈‖z0‖⌉₊ + 2) e
  refine ⟨min 1 (1 / ((j : ℝ) + 1)), lt_min one_pos (by positivity), fun z hz hzz0 => ?_⟩
  have hd : ‖z - z0‖ < min 1 (1 / ((j : ℝ) + 1)) := by rwa [← dist_eq_norm]
  have hc := Nat.le_ceil ‖z0‖
  have hzM : ‖z‖ < ((⌈‖z0‖⌉₊ + 2 : ℕ) : ℝ) := by
    push_cast
    have := norm_sub_norm_le z z0
    linarith [min_le_left 1 (1 / ((j : ℝ) + 1))]
  have hz0M : ‖z0‖ < ((⌈‖z0‖⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨N, hN⟩ := raw_close hj hz hz0 hzM hz0M (hd.trans_le (min_le_right _ _))
  have hlim := ((tendsto_raw_of_C1 h k hz).sub (tendsto_raw_of_C1 h k hz0)).abs
  have hle : |avgReg x k z - avgReg x k z0| ≤ 1 / ((e : ℝ) + 1) :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun n hn => hN n hn n hn⟩)
  rw [Real.dist_eq]; linarith

theorem regular_of_cert {x : FieldSample} (h1 : C1 x) (h2 : C2 x) (h3 : C3 x) (h4 : C4 x) :
    IsRegularWith x (canon x) := by
  have hPc : ∀ i, Continuous (Phi x i) := fun i =>
    continuousOn_univ.1 (GoodSample.gs_continuousOn_integral_fc_fun (continuousOn_avgReg_of_C1 h1 i))
  -- uniform Cauchy bound on whole boxes
  have hU : ∀ m e : ℕ, ∃ J : ℕ, ∀ i ≥ J, ∀ i' ≥ J, ∀ p ∈ Sd, p ∈ box m →
      |Phi x i p - Phi x i' p| ≤ 1 / ((e : ℝ) + 1) := by
    intro m e
    obtain ⟨J, hJ⟩ := h2 m e
    refine ⟨J, fun i hi i' hi' p hp hpm => ?_⟩
    exact le_of_qpt (φ := fun q => |Phi x i q - Phi x i' q|) hp hpm
      (continuous_abs.comp ((hPc i).sub (hPc i'))).continuousWithinAt
      (fun j hj1 hj2 => hJ i hi i' hi' j hj1 hj2)
  have hT : ∀ p ∈ Sd, Tendsto (fun i => Phi x i p) atTop (𝓝 (canon x p)) := by
    intro p hp
    obtain ⟨m, hm⟩ := exists_box hp.2
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      (Metric.cauchySeq_iff.2 fun ε hε => ?_))
    obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
    obtain ⟨J, hJ⟩ := hU m e
    exact ⟨J, fun i hi i' hi' => by
      rw [Real.dist_eq]; exact (hJ i hi i' hi' p hp hm).trans_lt he⟩
  have hU' : ∀ m e : ℕ, ∃ J : ℕ, ∀ i ≥ J, ∀ p ∈ Sd, p ∈ box m →
      |Phi x i p - canon x p| ≤ 1 / ((e : ℝ) + 1) := by
    intro m e
    obtain ⟨J, hJ⟩ := hU m e
    refine ⟨J, fun i hi p hp hpm => ?_⟩
    exact le_of_tendsto ((tendsto_const_nhds.sub (hT p hp)).abs :
      Tendsto (fun i' => |Phi x i p - Phi x i' p|) atTop _)
      (eventually_atTop.2 ⟨J, fun i' hi' => hJ i hi i' hi' p hp hpm⟩)
  have hL : TendstoLocallyUniformlyOn (Phi x) (canon x) atTop Sd := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε p hp
    obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hm⟩ := exists_box hp.2
    obtain ⟨J, hJ⟩ := hU' m e
    refine ⟨box m ∩ Sd, inter_mem (mem_nhdsWithin_of_mem_nhds ((isOpen_box m).mem_nhds hm))
      self_mem_nhdsWithin, eventually_atTop.2 ⟨J, fun i hi q hq => ?_⟩⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact (hJ i hi q hq.2 hq.1).trans_lt he
  have hGc : ContinuousOn (canon x) Sd :=
    hL.continuousOn (Eventually.frequently (Eventually.of_forall fun i => (hPc i).continuousOn))
  refine ⟨hGc, fun k z hz => ?_, ?_⟩
  · have hcont : Tendsto (canon x) (𝓝[Sd] (z, radius k)) (𝓝 (canon x (z, radius k))) :=
      hGc _ ⟨hz, radius_pos k⟩
    have hseq : Tendsto (fun n => (dyadicRoundC n z, radius k)) atTop (𝓝[Sd] (z, radius k)) :=
      tendsto_nhdsWithin_iff.2 ⟨(tendsto_dyadicRoundC z).prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun n => ⟨CircleCont.dyadicRoundC_mem_Hbar hz n, radius_pos k⟩⟩
    refine (hcont.comp hseq).congr fun n => ?_
    exact h3 k n ⌊(2 : ℝ) ^ n * z.re⌋ ⌊(2 : ℝ) ^ n * z.im⌋ (CircleCont.dyadicRoundC_mem_Hbar hz n)
  · have hΨ : ContinuousOn (fun P : ℝ × (ℂ × ℝ) => smoothC x P.1 P.2) (Ioi 0 ×ˢ univ) := by
      refine continuousOn_integral_fc (P := ℝ × (ℂ × ℝ)) (S := Ioi 0 ×ˢ univ)
        (H := fun P u => canon x (u, P.1)) (c := fun P => P.2.1) (r := fun P => P.2.2) ?_
        (by fun_prop) (by fun_prop)
      exact hGc.comp (by fun_prop : Continuous fun q : (ℝ × (ℂ × ℝ)) × ℂ => (q.2, q.1.1)).continuousOn
        (fun q hq => ⟨hq.2, hq.1.1⟩)
    have hV : ∀ m e : ℕ, ∃ J : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ < 1 / ((J : ℝ) + 1) → ∀ p ∈ Sd, p ∈ box m →
        |smoothC x ρ p - canon x p| ≤ 1 / ((e : ℝ) + 1) := by
      intro m e
      obtain ⟨J, hJ⟩ := h4 m e
      refine ⟨J, fun ρ hρ hρJ p hp hpm => ?_⟩
      have c1 : ContinuousWithinAt (fun P : ℝ × (ℂ × ℝ) => smoothC x P.1 P.2) (Ioi 0 ×ˢ Sd) (ρ, p) :=
        (hΨ.mono (prod_mono subset_rfl (subset_univ _))) _ ⟨hρ, hp⟩
      have c2 : ContinuousWithinAt (fun P : ℝ × (ℂ × ℝ) => canon x P.2) (Ioi 0 ×ˢ Sd) (ρ, p) :=
        (hGc.comp continuousOn_snd (fun P hP => hP.2)) _ ⟨hρ, hp⟩
      exact le_of_qpt₂ (φ := fun P => |smoothC x P.1 P.2 - canon x P.2|) hρ hρJ hp hpm
        (continuous_abs.continuousAt.comp_continuousWithinAt (c1.sub c2))
        (fun n b j hb1 hb2 hj1 hj2 => hJ n b hb1 hb2 j hj1 hj2)
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε p hp
    obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hm⟩ := exists_box hp.2
    obtain ⟨J, hJ⟩ := hV m e
    refine ⟨box m ∩ Sd, inter_mem (mem_nhdsWithin_of_mem_nhds ((isOpen_box m).mem_nhds hm))
      self_mem_nhdsWithin, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((J : ℝ) + 1) by positivity)] with ρ hρ q hq
    rw [Real.dist_eq, abs_sub_comm]
    exact (hJ ρ hρ.1 hρ.2 q hq.2 hq.1).trans_lt he

/-! ## Main result of part 1 -/

theorem isRegularSample_iff_cert (x : FieldSample) :
    IsRegularSample x ↔ C1 x ∧ C2 x ∧ C3 x ∧ C4 x := by
  constructor
  · rintro ⟨F, hF⟩
    have hG : IsRegularWith x (canon x) := hF.congr_evalReg
    exact ⟨C1_of_regular hG, C2_of_regular hG, C3_of_regular hG, C4_of_regular hG⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨_, regular_of_cert h1 h2 h3 h4⟩

/-- **M4-R5(a), regularity.** Regularity of a field sample is a measurable event. -/
theorem measurableSet_isRegularSample : MeasurableSet {x : FieldSample | IsRegularSample x} := by
  have e : {x : FieldSample | IsRegularSample x} = {x | C1 x ∧ C2 x ∧ C3 x ∧ C4 x} := by
    ext x; exact isRegularSample_iff_cert x
  rw [e]
  exact measurableSet_setOfPred.2 (measurable_C1.and (measurable_C2.and (measurable_C3.and
    measurable_C4)))

end GoodMeas

end QuantumZipper
