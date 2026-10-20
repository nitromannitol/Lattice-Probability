/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/CurveLength.lean.
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Finset.Sort
import Mathlib.Order.LiminfLimsup
import LatticeProb.Topology.Length.VariationCompat

/-!
# Length of a curve

For a pseudo-extended-metric space `X` and a map `P : ℝ → X`, the length of `P` on `[a, b]` is

  `curveLength P a b = eVariationOn P (Icc a b) ∈ [0, ∞]`

(mathlib's variation, a sup over monotone finite sequences in `[a, b]`).
We prove that it agrees with the partition definition of length: the sup over partitions `a = t₀ < t₁ < … < t_n = b` of
`∑ d(P(t_i), P(t_{i-1}))` (`curveLength_eq_partitionLengthSup`).

Basic properties: `edist (P a) (P b) ≤ curveLength P a b`, additivity over subintervals,
invariance under monotone and antitone reparametrizations, lower semicontinuity under pointwise
(hence uniform) convergence.

Sources: Petrunin, *Pure metric geometry* (arXiv:2007.09846), §1 "Length" (the definition of length
and lower semicontinuity of length); Burago–Burago–Ivanov, *A course in metric geometry*,
Prop. 2.3.4 (additivity, lower semicontinuity). The proofs are thin wrappers around mathlib's
`eVariationOn` API (`eVariationOn.union`, `eVariationOn.comp_eq_of_monotoneOn`,
`eVariationOn.lowerSemicontinuous_aux`) and around `LatticeProb.eVariationOn_image_range_of_monotone`
from `LatticeProb.Topology.Length.VariationCompat`.
-/

open Set Filter Topology
open scoped ENNReal

namespace LatticeProb.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-- The length of `P : ℝ → X` on `[a, b]`, as an element of `[0, ∞]`. -/
noncomputable def curveLength (P : ℝ → X) (a b : ℝ) : ℝ≥0∞ :=
  eVariationOn P (Icc a b)

/-- The partition definition of length: the supremum over partitions `a = t₀ < … < t_n = b` of
`∑_{i=1}^n d(P(t_i), P(t_{i-1}))`. -/
noncomputable def partitionLengthSup (P : ℝ → X) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (t : ℕ → ℝ) (_ : StrictMonoOn t (Iic n)) (_ : t 0 = a) (_ : t n = b),
    ∑ i ∈ Finset.range n, edist (P (t (i + 1))) (P (t i))

/-- The partition length is at most the variation length. -/
theorem partitionLengthSup_le_curveLength (P : ℝ → X) (a b : ℝ) :
    partitionLengthSup P a b ≤ curveLength P a b := by
  refine iSup_le fun n => iSup_le fun t => iSup_le fun ht => iSup_le fun h0 => iSup_le fun hn => ?_
  have hmono : Monotone (fun i => t (min i n)) := fun i j hij =>
    ht.monotoneOn (Set.mem_Iic.2 (min_le_right _ _)) (Set.mem_Iic.2 (min_le_right _ _))
      (min_le_min_right n hij)
  have hmem : ∀ i, t (min i n) ∈ Icc a b := fun i =>
    ⟨h0 ▸ ht.monotoneOn (Set.mem_Iic.2 (Nat.zero_le _)) (Set.mem_Iic.2 (min_le_right _ _))
        (Nat.zero_le _),
      hn ▸ ht.monotoneOn (Set.mem_Iic.2 (min_le_right _ _)) (Set.mem_Iic.2 le_rfl)
        (min_le_right _ _)⟩
  calc ∑ i ∈ Finset.range n, edist (P (t (i + 1))) (P (t i))
      = ∑ i ∈ Finset.range n, edist (P (t (min (i + 1) n))) (P (t (min i n))) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [min_eq_left (by omega), min_eq_left (by omega)]
    _ ≤ curveLength P a b := eVariationOn.sum_le (f := P) hmono hmem

/-- The variation on a finite set `S ⊆ [a, b]` containing `a` and `b` is a partition sum. -/
theorem eVariationOn_finite_le_partitionLengthSup (P : ℝ → X) {a b : ℝ} {S : Set ℝ}
    (hS : S.Finite) (ha : a ∈ S) (hb : b ∈ S) (hSab : S ⊆ Icc a b) :
    eVariationOn P S ≤ partitionLengthSup P a b := by
  set F := hS.toFinset with hF
  set k := F.card with hk
  have hkpos : 0 < k := Finset.card_pos.2 ⟨a, by simpa [hF] using ha⟩
  let e := F.orderEmbOfFin hk.symm
  let t : ℕ → ℝ := fun i => e ⟨min i (k - 1), by omega⟩
  have htmono : Monotone t := fun i j hij => e.monotone (Fin.mk_le_mk.2 (min_le_min_right _ hij))
  have htstrict : StrictMonoOn t (Iic (k - 1)) := by
    intro i hi j hj hij
    simp only [Set.mem_Iic] at hi hj
    refine e.strictMono (Fin.mk_lt_mk.2 ?_)
    rw [min_eq_left hi, min_eq_left hj]; exact hij
  have himg : t '' Iic (k - 1) = S := by
    have hrange : Set.range e = (F : Set ℝ) := Finset.range_orderEmbOfFin F hk.symm
    rw [hF, Set.Finite.coe_toFinset] at hrange
    rw [← hrange]
    ext x; constructor
    · rintro ⟨i, -, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, Set.mem_Iic.2 (by omega), by simp only [t]; congr; omega⟩
  have hmin : ∀ x ∈ F, a ≤ x := fun x hx => (hSab (by simpa [hF] using hx)).1
  have hmax : ∀ x ∈ F, x ≤ b := fun x hx => (hSab (by simpa [hF] using hx)).2
  have haF : a ∈ F := by simpa [hF] using ha
  have hbF : b ∈ F := by simpa [hF] using hb
  have ht0 : t 0 = a := by
    have h1 : t 0 = F.min' ⟨a, haF⟩ := by
      simp only [t, Nat.zero_min]
      exact Finset.orderEmbOfFin_zero hk.symm hkpos
    rw [h1]
    exact le_antisymm (Finset.min'_le _ _ haF) (Finset.le_min' _ _ _ hmin)
  have htk : t (k - 1) = b := by
    have h1 : t (k - 1) = F.max' ⟨a, haF⟩ := by
      simp only [t, min_self]
      exact Finset.orderEmbOfFin_last hk.symm hkpos
    rw [h1]
    exact le_antisymm (Finset.max'_le _ _ _ hmax) (Finset.le_max' _ _ hbF)
  rw [← himg, LatticeProb.eVariationOn_image_range_of_monotone P htmono]
  refine le_iSup_of_le (k - 1) <| le_iSup_of_le t <| le_iSup_of_le htstrict <|
    le_iSup_of_le ht0 <| le_iSup_of_le htk ?_
  exact le_of_eq (Finset.sum_congr rfl fun i _ => edist_comm _ _)

/-- **The partition definition of length agrees with `curveLength`.** -/
theorem curveLength_eq_partitionLengthSup (P : ℝ → X) (a b : ℝ) :
    curveLength P a b = partitionLengthSup P a b := by
  refine le_antisymm ?_ (partitionLengthSup_le_curveLength P a b)
  rcases lt_or_ge b a with hba | hab
  · unfold curveLength
    rw [Set.Icc_eq_empty (not_le.2 hba), eVariationOn.subsingleton P Set.subsingleton_empty]
    exact bot_le
  refine iSup_le fun ⟨n, u, hu, us⟩ => ?_
  have h1 : ∑ i ∈ Finset.range n, edist (P (u (i + 1))) (P (u i)) = eVariationOn P (u '' Iic n) := by
    rw [LatticeProb.eVariationOn_image_range_of_monotone P hu]
    exact Finset.sum_congr rfl fun i _ => edist_comm _ _
  dsimp only
  rw [h1]
  set S : Set ℝ := insert a (insert b (u '' Iic n))
  have hSfin : S.Finite := ((Set.finite_Iic n).image u).insert b |>.insert a
  have hSsub : S ⊆ Icc a b := by
    rintro x (rfl | rfl | ⟨i, -, rfl⟩)
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
    · exact us i
  calc eVariationOn P (u '' Iic n) ≤ eVariationOn P S :=
        eVariationOn.mono P (Set.subset_insert _ _ |>.trans (Set.subset_insert _ _))
    _ ≤ partitionLengthSup P a b :=
        eVariationOn_finite_le_partitionLengthSup P hSfin (Set.mem_insert _ _)
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hSsub

/-- The distance between the endpoints is at most the length. -/
theorem edist_le_curveLength (P : ℝ → X) {a b : ℝ} (hab : a ≤ b) :
    edist (P a) (P b) ≤ curveLength P a b :=
  eVariationOn.edist_le P ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩

/-- The length on `[a, b]` vanishes when `b ≤ a`. -/
theorem curveLength_of_ge (P : ℝ → X) {a b : ℝ} (hba : b ≤ a) : curveLength P a b = 0 :=
  eVariationOn.subsingleton P (Set.subsingleton_Icc_of_ge hba)

/-- The length on a degenerate interval vanishes. -/
theorem curveLength_self (P : ℝ → X) (a : ℝ) : curveLength P a a = 0 :=
  curveLength_of_ge P le_rfl

/-- **Additivity** of length over subintervals. -/
theorem curveLength_add (P : ℝ → X) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    curveLength P a b + curveLength P b c = curveLength P a c := by
  unfold curveLength
  rw [← eVariationOn.union P (isGreatest_Icc hab) (isLeast_Icc hbc), Icc_union_Icc_eq_Icc hab hbc]

/-- Length is monotone in the interval. -/
theorem curveLength_mono (P : ℝ → X) {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    curveLength P a b ≤ curveLength P c d :=
  eVariationOn.mono P (Icc_subset_Icc hca hbd)

/-- Curves that agree on `[a, b]` have the same length there. -/
theorem curveLength_congr {P Q : ℝ → X} {a b : ℝ} (h : EqOn P Q (Icc a b)) :
    curveLength P a b = curveLength Q a b :=
  eVariationOn.eq_of_eqOn h

/-- Invariance of length under a monotone reparametrization `φ` of `[c, d]` onto `[a, b]`. -/
theorem curveLength_comp_of_monotoneOn (P : ℝ → X) {φ : ℝ → ℝ} {a b c d : ℝ}
    (hφ : MonotoneOn φ (Icc c d)) (himg : φ '' Icc c d = Icc a b) :
    curveLength (P ∘ φ) c d = curveLength P a b := by
  unfold curveLength; rw [eVariationOn.comp_eq_of_monotoneOn P φ hφ, himg]

/-- Invariance of length under an antitone reparametrization `φ` of `[c, d]` onto `[a, b]`. -/
theorem curveLength_comp_of_antitoneOn (P : ℝ → X) {φ : ℝ → ℝ} {a b c d : ℝ}
    (hφ : AntitoneOn φ (Icc c d)) (himg : φ '' Icc c d = Icc a b) :
    curveLength (P ∘ φ) c d = curveLength P a b := by
  unfold curveLength; rw [eVariationOn.comp_eq_of_antitoneOn P φ hφ, himg]

/-- Continuous monotone reparametrization. -/
theorem curveLength_comp_of_continuousOn_monotoneOn (P : ℝ → X) {φ : ℝ → ℝ} {c d : ℝ}
    (hcd : c ≤ d) (hφc : ContinuousOn φ (Icc c d)) (hφ : MonotoneOn φ (Icc c d)) :
    curveLength (P ∘ φ) c d = curveLength P (φ c) (φ d) :=
  curveLength_comp_of_monotoneOn P hφ (hφc.image_Icc_of_monotoneOn hcd hφ)

/-- Continuous antitone reparametrization (reverses the orientation). -/
theorem curveLength_comp_of_continuousOn_antitoneOn (P : ℝ → X) {φ : ℝ → ℝ} {c d : ℝ}
    (hcd : c ≤ d) (hφc : ContinuousOn φ (Icc c d)) (hφ : AntitoneOn φ (Icc c d)) :
    curveLength (P ∘ φ) c d = curveLength P (φ d) (φ c) :=
  curveLength_comp_of_antitoneOn P hφ (hφc.image_Icc_of_antitoneOn hcd hφ)

/-- Length of the reversed curve `t ↦ P (a + b - t)`. -/
theorem curveLength_reverse (P : ℝ → X) {a b : ℝ} (hab : a ≤ b) :
    curveLength (fun t => P (a + b - t)) a b = curveLength P a b := by
  have := curveLength_comp_of_continuousOn_antitoneOn P (φ := fun t => a + b - t) hab
    (by fun_prop) (fun x _ y _ hxy => by simp only; linarith)
  simpa [Function.comp_def] using this

/-- **Lower semicontinuity of length** (Petrunin, *Pure metric geometry*, Thm. on lower
semicontinuity of length; Burago–Burago–Ivanov, Prop. 2.3.4(iv)), eventual form. -/
theorem eventually_lt_curveLength {ι : Type*} {l : Filter ι} {F : ι → ℝ → X} {P : ℝ → X}
    {a b : ℝ} (h : ∀ t ∈ Icc a b, Tendsto (fun i => F i t) l (𝓝 (P t))) {v : ℝ≥0∞}
    (hv : v < curveLength P a b) : ∀ᶠ i in l, v < curveLength (F i) a b :=
  eVariationOn.lowerSemicontinuous_aux h hv

/-- **Lower semicontinuity of length** under pointwise convergence on `[a, b]`. -/
theorem curveLength_le_liminf {ι : Type*} {l : Filter ι} {F : ι → ℝ → X} {P : ℝ → X}
    {a b : ℝ} (h : ∀ t ∈ Icc a b, Tendsto (fun i => F i t) l (𝓝 (P t))) :
    curveLength P a b ≤ liminf (fun i => curveLength (F i) a b) l := by
  refine le_of_forall_lt fun v hv => ?_
  obtain ⟨w, hvw, hw⟩ := exists_between hv
  exact hvw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault)
    ((eventually_lt_curveLength h hw).mono fun i hi => hi.le))

/-- **Lower semicontinuity of length** under uniform convergence on `[a, b]`. -/
theorem curveLength_le_liminf_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι} {F : ι → ℝ → X}
    {P : ℝ → X} {a b : ℝ} (h : TendstoUniformlyOn F P l (Icc a b)) :
    curveLength P a b ≤ liminf (fun i => curveLength (F i) a b) l :=
  curveLength_le_liminf fun _ ht => h.tendsto_at ht

/-! ### Nonvacuity examples

The reparametrization hypotheses of `curveLength_comp_of_monotoneOn` and
`curveLength_comp_of_antitoneOn` are satisfied by the identity and by `t ↦ 1 - t` on `[0, 1]`. -/

namespace CurveLengthExample

/-- The identity map of `[0, 1]` satisfies the monotone reparametrization hypotheses. -/
example (P : ℝ → X) : curveLength (P ∘ id) 0 1 = curveLength P 0 1 :=
  curveLength_comp_of_monotoneOn P (monotone_id.monotoneOn _) (by simp)

/-- The map `t ↦ 1 - t` maps `[0, 1]` onto itself and satisfies the antitone hypotheses. -/
example (P : ℝ → X) : curveLength (P ∘ fun t => 1 - t) 0 1 = curveLength P 0 1 := by
  refine curveLength_comp_of_antitoneOn P (fun x _ y _ hxy => by show 1 - y ≤ 1 - x; linarith) ?_
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    exact ⟨1 - x, ⟨by linarith, by linarith⟩, by ring⟩

end CurveLengthExample

end LatticeProb.MetricGeometry
