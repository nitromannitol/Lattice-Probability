/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11In3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentTilde
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseIndep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Open node 2 (b), (c) of P2-DG105g: independence of local white-noise events (P2-DG105l)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`:
* DG:1267: "By the definition (eqn-wn-truncate) of `ĥ^tr`, the event `E_S^ε` is a.s. determined
  by the restriction of the white noise `W` to `S(2) × ℝ_+`. In particular, `E_S^ε` and
  `E_{S̃}^ε` are independent whenever `S(2) ∩ S̃(2) = ∅`."
* DG:1302–1305: the fine field `(ĥ − ĥ_{2^{-m-n_m}})(2^{-m-n_m}· + u_R)` "is independent from
  `ĥ_{2^{-m-n_m}}`" (white noise at times `< δ²` vs `≥ δ²`).

The events of the formalization are only *a.s.* determined by the local white noise (they are
built from chosen modifications), so the σ-algebra `generateFrom Fg` of `L311LevelInput` is
handled by passing to a.s.-equal versions (`exists_ae_eq_of_generateFrom`: the sets a.s. equal to
an `m`-measurable set form a σ-algebra). With `𝓖_R = σ(W f : supp f ⊆ R)` (`GMCIdent.wnSigma`):

* **`prob_inter_eq_mul_of_ae`** (node 2(c)): if `T` is a.s. a `𝓖_C`-measurable variable and every
  `A ∈ Fg` is a.s. a `𝓖_M`-event with `C ∩ M = ∅`, then `T ⊥ generateFrom Fg`;
* **`prob_iInter_compl_eq_prod`** (node 2(b)): events a.s. determined by `W` on regions that are
  pairwise disjoint along a finite family `F` satisfy `P(⋂_F E_iᶜ) = ∏_F P(E_iᶜ)`;
* **`l311_indep_of_local`**: both conjuncts of `L311LevelInput` (S3L11Sc) in the form needed,
  from the locality of `E` and `T`.

White-noise independence over disjoint sets: `IsWhiteNoise.indepFun_of_disjoint`,
`IsWhiteNoise.iIndepFun_of_pairwise_disjoint` (Field/WhiteNoise*). Own elementary glue.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise GMCIdent

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- sets a.s. equal to `m`-measurable sets are closed under the σ-algebra operations -/
lemma exists_ae_eq_of_generateFrom {m : MeasurableSpace Ω} {Fg : Set (Set Ω)}
    (hF : ∀ A ∈ Fg, ∃ A', MeasurableSet[m] A' ∧ A =ᵐ[P] A') {A : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.generateFrom Fg] A) :
    ∃ A', MeasurableSet[m] A' ∧ A =ᵐ[P] A' := by
  induction A, hA using MeasurableSpace.generateFrom_induction with
  | hC t ht _ => exact hF t ht
  | empty => exact ⟨∅, @MeasurableSet.empty _ m, ae_eq_refl _⟩
  | compl t _ ih =>
      obtain ⟨A', h1, h2⟩ := ih
      exact ⟨A'ᶜ, h1.compl, h2.compl⟩
  | iUnion s _ ih =>
      choose A' h1 h2 using ih
      exact ⟨⋃ i, A' i, MeasurableSet.iUnion h1, EventuallyEqSet.countable_iUnion h2⟩

/-- **Node 2(c)**: independence of `T` from `generateFrom Fg` via a.s.-equal versions -/
theorem prob_inter_eq_mul_of_ae {mC mM : MeasurableSpace Ω} (hind : Indep mC mM P)
    {T T' : Ω → ℝ} (hT' : Measurable[mC] T') (hTT : T =ᵐ[P] T') {Fg : Set (Set Ω)}
    (hF : ∀ A ∈ Fg, ∃ A', MeasurableSet[mM] A' ∧ A =ᵐ[P] A') :
    ∀ B : Set ℝ, MeasurableSet B → ∀ A : Set Ω,
      MeasurableSet[MeasurableSpace.generateFrom Fg] A →
      P (T ⁻¹' B ∩ A) = P (T ⁻¹' B) * P A := by
  intro B hB A hA
  obtain ⟨A', hA'm, hAA⟩ := exists_ae_eq_of_generateFrom (mΩ := mΩ) (m := mM) hF hA
  have hTB : T ⁻¹' B =ᵐ[P] T' ⁻¹' B := by
    filter_upwards [hTT] with ω hω
    change (T ω ∈ B) = (T' ω ∈ B)
    rw [hω]
  rw [measure_congr (hTB.inter hAA), measure_congr hTB, measure_congr hAA]
  exact (Indep_iff _ _ _).1 hind _ _ (hT' hB) hA'm

/-- **Node 2(b)**: events a.s. determined by the white noise on regions pairwise disjoint along
`F` are independent along `F` -/
theorem prob_iInter_compl_eq_prod {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ι : Type}
    [DecidableEq ι] {R : ι → Set (ℝ × ℂ)} {E : ι → Set Ω}
    (hE : ∀ i, ∃ A', MeasurableSet[wnSigma W (R i)] A' ∧ E i =ᵐ[P] A') (F : Finset ι)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (R i) (R j)) :
    P (⋂ i ∈ F, (E i)ᶜ) = ∏ i ∈ F, P (E i)ᶜ := by
  classical
  choose E' hE'm hEE using hE
  set R' : ι → Set (ℝ × ℂ) := fun i => if i ∈ F then R i else ∅ with hR'
  have hpair : Pairwise fun i j => Disjoint (R' i) (R' j) := by
    intro i j hij
    simp only [hR']
    split_ifs with hi hj hj
    · exact hdisj i hi j hj hij
    · exact disjoint_empty _
    · exact empty_disjoint _
    · exact disjoint_empty _
  have hind : iIndep (fun i => wnSigma W (R' i)) P :=
    (iIndepFun_iff_iIndep _ _ _).1 (hW.iIndepFun_of_pairwise_disjoint hpair)
  have hmeas : ∀ i ∈ F, MeasurableSet[wnSigma W (R' i)] (E' i)ᶜ := by
    intro i hi
    have : R' i = R i := by simp [hR', hi]
    rw [this]; exact (hE'm i).compl
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ F, (ω ∈ E i ↔ ω ∈ E' i) := by
    have : ∀ᵐ ω ∂P, ∀ i : F, (E i ω = E' i ω) := ae_all_iff.2 fun i => hEE i
    filter_upwards [this] with ω hω i hi
    exact Iff.of_eq (hω ⟨i, hi⟩)
  have hset : (⋂ i ∈ F, (E i)ᶜ) =ᵐ[P] ⋂ i ∈ F, (E' i)ᶜ := by
    filter_upwards [hall] with ω hω
    simp only [eq_iff_iff, mem_iInter, mem_compl_iff]
    exact ⟨fun h i hi => (hω i hi).not.1 (h i hi), fun h i hi => (hω i hi).not.2 (h i hi)⟩
  rw [measure_congr hset, hind.meas_biInter hmeas]
  exact Finset.prod_congr rfl fun i _ => measure_congr (hEE i).compl.symm

/-- **The independence conjuncts of `L311LevelInput`** (DG:1267, 1302–1305) from locality:
`E k x` is a.s. determined by `W` on `R x`, `T` a.s. by `W` on `C`, `C` is disjoint from every
`R x`, and `R x`, `R y` are disjoint for `x ≠ y` in the admissible families. -/
theorem l311_indep_of_local {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {R : ℤ × ℤ → Set (ℝ × ℂ)} {C : Set (ℝ × ℂ)} (hRC : ∀ x, Disjoint (R x) C)
    {E : ℤ → ℤ × ℤ → Set Ω}
    (hE : ∀ k x, ∃ A', MeasurableSet[wnSigma W (R x)] A' ∧ E k x =ᵐ[P] A')
    {T T' : Ω → ℝ} (hT' : Measurable[wnSigma W C] T') (hTT : T =ᵐ[P] T')
    (Adm : Finset (ℤ × ℤ) → Prop)
    (hdisj : ∀ F, Adm F → ∀ x ∈ F, ∀ y ∈ F, x ≠ y → Disjoint (R x) (R y)) :
    (∀ k x, E k x ∈ {A | ∃ k x, A = E k x}) ∧
      (∀ B : Set ℝ, MeasurableSet B → ∀ A : Set Ω,
        MeasurableSet[MeasurableSpace.generateFrom {A | ∃ k x, A = E k x}] A →
        P (T ⁻¹' B ∩ A) = P (T ⁻¹' B) * P A) ∧
      (∀ k F, Adm F → P (⋂ x ∈ F, (E k x)ᶜ) ≤ ∏ x ∈ F, P (E k x)ᶜ) := by
  refine ⟨fun k x => ⟨k, x, rfl⟩, ?_, fun k F hF =>
    (prob_iInter_compl_eq_prod hW (hE k) F (hdisj F hF)).le⟩
  have hind : Indep (wnSigma W C) (wnSigma W (⋃ x, R x)) P :=
    hW.indepFun_of_disjoint (disjoint_iUnion_right.2 fun x => (hRC x).symm)
  refine prob_inter_eq_mul_of_ae hind hT' hTT ?_
  rintro A ⟨k, x, rfl⟩
  obtain ⟨A', h1, h2⟩ := hE k x
  exact ⟨A', wnSigma_mono (subset_iUnion R x) A' h1, h2⟩

end DG
end LQGMetric
