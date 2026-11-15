/-
Copied from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: SupercriticalLQGUniqueness/Uniqueness/Objects/Shadow/Planar.lean,
commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82, lines 746–825.
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set Metric

namespace LatticeProb

theorem finite_of_compact_separated {X : Type*} [PseudoEMetricSpace X]
    {K S : Set X} (hK : IsCompact K) (hSK : S ⊆ K)
    {ε : NNReal} (hε : ε ≠ 0)
    (hsep : Metric.IsSeparated (↑(2 * ε) : ENNReal) S) : S.Finite := by
  obtain ⟨N, _, hNfinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hε hK
  have hS : S.encard ≤ N.encard :=
    (Metric.IsSeparated.encard_le_packingNumber hSK hsep).trans
      ((Metric.packingNumber_two_mul_le_externalCoveringNumber ε K).trans
        hcover.externalCoveringNumber_le_encard)
  exact Set.encard_lt_top_iff.mp
    (lt_of_le_of_lt hS (Set.encard_lt_top_iff.mpr hNfinite))

 


theorem finite_charged_excursions {S : Set (ℝ × ℝ)} {a b δ : ℝ}
    (hδ : 0 < δ)
    (hspan : ∀ e ∈ S, a ≤ e.1 ∧ δ ≤ e.2 - e.1 ∧ e.2 ≤ b)
    (hdisj : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
      Disjoint (Ioo e.1 e.2) (Ioo f.1 f.2)) : S.Finite := by
  let starts : Set ℝ := Prod.fst '' S
  have hstarts : starts ⊆ Icc a b := by
    rintro x ⟨e, he, rfl⟩
    obtain ⟨ha, hlen, hb⟩ := hspan e he
    exact ⟨ha, by linarith⟩
  have hseparated : ∀ x ∈ starts, ∀ y ∈ starts,
      x ≠ y → δ ≤ dist x y := by
    rintro x ⟨e, he, rfl⟩ y ⟨f, hf, rfl⟩ hxy
    have hef : e ≠ f := fun h => hxy (congrArg Prod.fst h)
    have hsep := (Ioo_disjoint_Ioo).1 (hdisj e he f hf hef)
    obtain ⟨_, heδ, _⟩ := hspan e he
    obtain ⟨_, hfδ, _⟩ := hspan f hf
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have hfe : f.1 < f.2 := by linarith
      have horder : e.2 ≤ f.1 := by
        have hmax : max e.1 f.1 = f.1 := max_eq_right hlt.le
        rw [hmax] at hsep
        rcases le_total e.2 f.2 with h | h
        · rw [min_eq_left h] at hsep; exact hsep
        · rw [min_eq_right h] at hsep; linarith
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlt.le)]
      linarith
    · have hee : e.1 < e.2 := by linarith
      have horder : f.2 ≤ e.1 := by
        have hmax : max e.1 f.1 = e.1 := max_eq_left hgt.le
        rw [hmax] at hsep
        rcases le_total e.2 f.2 with h | h
        · rw [min_eq_left h] at hsep; linarith
        · rw [min_eq_right h] at hsep; exact hsep
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hgt.le)]
      linarith
  let ε : NNReal := ⟨δ / 4, by positivity⟩
  have hε : ε ≠ 0 := by
    apply ne_of_gt
    change 0 < δ / 4
    positivity
  have hsep : Metric.IsSeparated (↑(2 * ε) : ENNReal) starts := by
    intro x hx y hy hxy
    have hδxy := hseparated x hx y hy hxy
    have hsmall : 2 * (ε : ℝ) < dist x y := by
      change 2 * (δ / 4) < dist x y
      linarith
    have hεeq : (↑(2 * ε) : ENNReal) = ENNReal.ofReal (2 * (ε : ℝ)) := by
      rw [ENNReal.coe_nnreal_eq]
      congr 1
    rw [hεeq, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_lt_of_le (by positivity) hδxy)).mpr hsmall
  have hfinite : starts.Finite := finite_of_compact_separated isCompact_Icc hstarts hε hsep
  apply hfinite.of_finite_image
  intro e he f hf heq
  by_contra hne
  have hd := hdisj e he f hf hne
  have heδ := (hspan e he).2.1
  have hfδ := (hspan f hf).2.1
  have hm : e.1 + δ / 2 ∈ Ioo e.1 e.2 := by constructor <;> linarith
  have hm' : e.1 + δ / 2 ∈ Ioo f.1 f.2 := by
    rw [← heq]
    constructor <;> linarith
  exact (Set.disjoint_left.mp hd) hm hm'

end LatticeProb
