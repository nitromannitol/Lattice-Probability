/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53G3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G1
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseIndep
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentWN

/-!
# DZZ Lemma 5.3, part 1, node 2: finite-range independence of the openness events (P2-DZZ53G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2452–2453: "there is an event
`𝓔_{𝖡,open}` which is measurable with respect to the field `η̌^𝖡` so that
`P(𝓔_{𝖡,open} | 𝓕*) ≥ 1 − O(K⁻²)`"; used (l. 2510–2514, "similar to (eq-par)") in a Peierls
argument over the `K × K` sub-boxes, which needs that the events of sub-boxes with disjoint
white-noise regions are independent, also conditionally on `𝓕*` (the cell chain).

The conditioning on `𝓕*` is built in the way DZZ L3.13 is formalized (`dzz_lemma313_of_geom`,
S3L13Main): on `{chain = c₀}` every `𝓕*`-event is an event of the white noise off the fine region
of `c₀`. So we condition on an event `A₀` of the white noise in a region `R₀` disjoint from the
regions `R i` of the sub-box fields.

* **`l53_measure_inter_biInter`**: `P(A₀ ∩ ⋂_{i∈F} E_i) = P(A₀) ∏_{i∈F} P(E_i)` for `A₀` an event of
  `W|_{R₀}` and `E_i` events of `W|_{R_i}`, the regions `R₀, R_i (i ∈ F)` pairwise disjoint
  (`IsWhiteNoise.iIndepFun_of_pairwise_disjoint`, Field/WhiteNoiseIndep).
* **`l53_cond_biInter`**, `l53_cond_eq`: the same for `P[·|A₀]` (the `hind` input of
  `perc_annulus_peierls`, Perc/AnnulusPeierls, holds with equality), and `P[E_i|A₀] = P(E_i)`.
* **`l53_zopen_local`**: the interface for node 3. For sub-box boundaries `Bd i` with *local*
  proxy measures `νB i` (rational ball masses measurable for `W|_{R i}`), and the per-pair far
  bound `P(far_{νB i}(z,z')) ≤ p`, the openness events `𝓔_i = (l53ZBad (νB i) δ T (Bd i) a b)ᶜ`
  are `W|_{R i}`-measurable, `a b P[𝓔_iᶜ | A₀] ≤ p 𝓛₁(Bd i)²`, and the `𝓔_iᶜ` of sub-boxes with
  pairwise disjoint regions are independent under `P[·|A₀]`.
Own elementary proofs (standard independence calculus; DZZ give no details).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- Independence of an event of `W|_{R₀}` and events of `W|_{R i}`, all regions disjoint, for a
family indexed by a type. -/
lemma l53_measure_inter_biInter_aux (hW : IsWhiteNoise P W) {ι : Type} {R₀ : Set (ℝ × ℂ)}
    {R : ι → Set (ℝ × ℂ)} (hR : Pairwise fun i j => Disjoint (R i) (R j))
    (hR₀ : ∀ i, Disjoint R₀ (R i)) {A₀ : Set Ω} (hA₀ : MeasurableSet[wnSigma W R₀] A₀)
    {E : ι → Set Ω} (hE : ∀ i, MeasurableSet[wnSigma W (R i)] (E i)) (F : Finset ι) :
    P (A₀ ∩ ⋂ i ∈ F, E i) = P A₀ * ∏ i ∈ F, P (E i) := by
  classical
  set A : Option ι → Set (ℝ × ℂ) := fun o => o.elim R₀ R with hAdef
  have hA : Pairwise fun i j => Disjoint (A i) (A j) := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact hR₀ j
    · exact (hR₀ i).symm
    · exact hR fun h => hij (congrArg some h)
  have h := hW.iIndepFun_of_pairwise_disjoint hA
  set s : Option ι → Set Ω := fun o => o.elim A₀ E with hs
  have key := h.meas_biInter (S := insert none (F.map Function.Embedding.some)) (s := s)
    (fun o _ => by
      cases o with
      | none => exact hA₀
      | some i => exact hE i)
  have hnone : none ∉ F.map Function.Embedding.some := by simp
  rw [Finset.prod_insert hnone, Finset.prod_map] at key
  have hset : (⋂ o ∈ insert none (F.map Function.Embedding.some), s o) = A₀ ∩ ⋂ i ∈ F, E i := by
    ext ω
    simp only [Finset.mem_insert, Finset.mem_map, Function.Embedding.some_apply, mem_iInter,
      mem_inter_iff]
    constructor
    · intro hω
      exact ⟨hω none (Or.inl rfl), fun i hi => hω (some i) (Or.inr ⟨i, hi, rfl⟩)⟩
    · rintro ⟨h0, h1⟩ o ho
      rcases ho with rfl | ⟨i, hi, rfl⟩
      · exact h0
      · exact h1 i hi
  rw [hset] at key
  exact key

/-- **Independence of an `𝓕*`-type event and sub-box events with disjoint regions.** -/
theorem l53_measure_inter_biInter (hW : IsWhiteNoise P W) {ι : Type} {R₀ : Set (ℝ × ℂ)}
    {R : ι → Set (ℝ × ℂ)} (F : Finset ι)
    (hR : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (R i) (R j))
    (hR₀ : ∀ i ∈ F, Disjoint R₀ (R i)) {A₀ : Set Ω} (hA₀ : MeasurableSet[wnSigma W R₀] A₀)
    {E : ι → Set Ω} (hE : ∀ i ∈ F, MeasurableSet[wnSigma W (R i)] (E i)) :
    P (A₀ ∩ ⋂ i ∈ F, E i) = P A₀ * ∏ i ∈ F, P (E i) := by
  classical
  have h := l53_measure_inter_biInter_aux (P := P) (W := W) (ι := ↥F) hW
    (R := fun x => R x.1) (fun x y hxy => hR x.1 x.2 y.1 y.2 fun h => hxy (Subtype.ext h))
    (fun x => hR₀ x.1 x.2) hA₀ (E := fun x => E x.1) (fun x => hE x.1 x.2) Finset.univ
  have hset : (⋂ x ∈ (Finset.univ : Finset ↥F), E x.1) = ⋂ i ∈ F, E i := by
    ext ω
    simp only [Finset.mem_univ, iInter_true, mem_iInter, Subtype.forall]
  rw [hset, Finset.prod_coe_sort F (fun i => P (E i))] at h
  exact h

/-- Under `P[·|A₀]` a sub-box event has its unconditional probability. -/
theorem l53_cond_eq (hW : IsWhiteNoise P W) {R₀ R : Set (ℝ × ℂ)} (hR₀ : Disjoint R₀ R)
    {A₀ : Set Ω} (hA₀ : MeasurableSet[wnSigma W R₀] A₀) (h0 : P A₀ ≠ 0) {E : Set Ω}
    (hE : MeasurableSet[wnSigma W R] E) : P[E | A₀] = P E := by
  have := hW.isProbabilityMeasure
  have h := l53_measure_inter_biInter (P := P) (W := W) (ι := Unit) (R₀ := R₀)
    (R := fun _ => R) hW {()} (by simp) (fun _ _ => hR₀) hA₀ (E := fun _ => E) (fun _ _ => hE)
  simp only [Finset.mem_singleton, Finset.prod_singleton, iInter_const] at h
  rw [cond_apply (wnSigma_le hW R₀ _ hA₀), h, ← mul_assoc,
    ENNReal.inv_mul_cancel h0 (measure_ne_top P A₀), one_mul]

/-- **The `hind` input of the Peierls argument under `P[·|A₀]`** (with equality). -/
theorem l53_cond_biInter (hW : IsWhiteNoise P W) {ι : Type} {R₀ : Set (ℝ × ℂ)}
    {R : ι → Set (ℝ × ℂ)} (F : Finset ι)
    (hR : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (R i) (R j))
    (hR₀ : ∀ i ∈ F, Disjoint R₀ (R i)) {A₀ : Set Ω} (hA₀ : MeasurableSet[wnSigma W R₀] A₀)
    (h0 : P A₀ ≠ 0) {E : ι → Set Ω} (hE : ∀ i ∈ F, MeasurableSet[wnSigma W (R i)] (E i)) :
    P[⋂ i ∈ F, E i | A₀] = ∏ i ∈ F, P[E i | A₀] := by
  have := hW.isProbabilityMeasure
  rw [cond_apply (wnSigma_le hW R₀ _ hA₀), l53_measure_inter_biInter hW F hR hR₀ hA₀ hE,
    ← mul_assoc, ENNReal.inv_mul_cancel h0 (measure_ne_top P A₀), one_mul]
  exact Finset.prod_congr rfl fun i hi => (l53_cond_eq hW (hR₀ i hi) hA₀ h0 (hE i hi)).symm

/-- DZZ's numbers in (eq-z-open) (l. 2497–2500): with `a = b = K⁻¹ 𝓛₁(∂𝖡)`, the counting bound
`a b X ≤ p 𝓛₁(∂𝖡)²` gives `X ≤ p K²` (so `p = O(K⁻⁴)` gives `O(K⁻²)`). -/
lemma l53_K_cancel {K m p X : ℝ≥0∞} (hK0 : K ≠ 0) (hKt : K ≠ ⊤) (hm0 : m ≠ 0) (hmt : m ≠ ⊤)
    (h : K⁻¹ * m * (K⁻¹ * m) * X ≤ p * m ^ 2) : X ≤ p * K ^ 2 := by
  have e1 : K⁻¹ * m * (K⁻¹ * m) * X = m ^ 2 * ((K ^ 2)⁻¹ * X) := by
    rw [ENNReal.inv_pow]; ring
  rw [e1, mul_comm p] at h
  have h2 : (K ^ 2)⁻¹ * X ≤ p :=
    (ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hm0) (ENNReal.pow_ne_top hmt)).1 h
  have hK2 : K ^ 2 * (K ^ 2)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (pow_ne_zero 2 hK0) (ENNReal.pow_ne_top hKt)
  calc X = K ^ 2 * (K ^ 2)⁻¹ * X := by rw [hK2, one_mul]
    _ = K ^ 2 * ((K ^ 2)⁻¹ * X) := by ring
    _ ≤ K ^ 2 * p := by gcongr
    _ = p * K ^ 2 := mul_comm _ _

end DZZ
end LQGMetric
