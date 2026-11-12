/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E5

/-!
# DZZ Lemma 5.3, node 3: a desirable cell from the good cluster (deterministic)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2504–2514, via (eq-par) l. 1927–1966). The boxes
of a cell `𝖢_i` are the sites of a grid; the boundary positions `ι` carry their outer
segments `seg p ⊆ Bd (site p)`. `Prev` lists the positions whose segment lies in `Λ_{i-1}`,
`Next` those in `Λ_i`, and every position of `Prev ∪ Next` outside the exceptional set `Exc`
has its box in the good cluster `C` (the conclusion of `l53_perc_cluster`).

`l53_desirable_of_cluster`: under the covering inequalities
* `0.2 𝓛₁(Λ_{i-1}) + #Exc σ ≤ 𝓛₁(⋃_{Prev} seg)` and `#Prev a ≤ 0.1 𝓛₁(Λ_{i-1})`,
* `𝓛₁(Λ_i \ ⋃_{Next} seg) + #Next b + #Exc σ < 0.1 𝓛₁(Λ_i)`
(`σ` bounds the length of a segment), every `Λ_end ⊆ Λ_i` with `𝓛₁ ≥ 0.1 𝓛₁(Λ_i)` meets some
good segment of `Λ_i` in mass `≥ b` (pigeonhole, DZZ's `𝕃_Λ ≠ ∅`, l. 1906–1909), and from the
chains of `l53_cluster_chain` and `l53_desirable_of_chains` we get `Λ_start ⊆ Λ_{i-1}` with
`𝓛₁ ≥ 0.1 𝓛₁(Λ_{i-1})` whose points are within `e^{T + log(#Box+1)}` of `Λ_end`: exactly
the `𝖢_i`-clause of `L53ChainDesirable` (S5L53F4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric

/-- **A desirable cell from the good cluster** (DZZ l. 1927–1966 and l. 2504–2514). -/
theorem l53_desirable_of_cluster (ν μ : Measure ℂ) {δ T : ℝ} (Box : Finset (ℤ × ℤ))
    (C : Set (ℤ × ℤ)) (hCbox : ∀ z ∈ C, z ∈ Box)
    (hCc : ∀ x ∈ C, ∀ y ∈ C, Relation.ReflTransGen (PercStepIn C PercAdj4) x y)
    (Bd : ℤ × ℤ → Set ℂ) (I : ℤ × ℤ → ℤ × ℤ → Set ℂ) {a b c : ℝ≥0∞} (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) (hc : b + a ≤ c)
    (hI : ∀ x ∈ C, ∀ y ∈ C, PercAdj4 x y → I x y ⊆ Bd x ∩ Bd y)
    (hIc : ∀ x ∈ C, ∀ y ∈ C, PercAdj4 x y → c ≤ ν (I x y))
    (hBdc : ∀ x ∈ C, c ≤ ν (Bd x))
    (hopen : ∀ x ∈ C, ∀ Λ ⊆ Bd x, b ≤ ν Λ →
      ∃ z ∈ Λ, ν {z' ∈ Bd x | ¬ lgdLeExp μ δ T z z'} ≤ a)
    {ι : Type*} (site : ι → ℤ × ℤ) (seg : ι → Set ℂ) (hseg : ∀ p, seg p ⊆ Bd (site p))
    (Prev Next Exc : Finset ι) (hsite : ∀ p, p ∉ Exc → (p ∈ Prev ∨ p ∈ Next) → site p ∈ C)
    {Λprev Λnext : Set ℂ} (hΛp : ν Λprev ≠ ⊤) (hΛn : ν Λnext ≠ ⊤)
    (hPrev : ∀ p ∈ Prev, seg p ⊆ Λprev) (hNext : ∀ p ∈ Next, seg p ⊆ Λnext)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : ∀ p, ν.real (seg p) ≤ σ)
    (hcovP : 0.2 * ν.real Λprev + Exc.card * σ ≤ ν.real (⋃ p ∈ Prev, seg p))
    (hcardP : (Prev.card : ℝ) * a.toReal ≤ 0.1 * ν.real Λprev)
    (hcovN : ν.real (Λnext \ ⋃ p ∈ Next, seg p) + Next.card * b.toReal + Exc.card * σ <
      0.1 * ν.real Λnext) :
    ∀ E ⊆ Λnext, 0.1 * ν.real Λnext ≤ ν.real E → ∃ S ⊆ Λprev,
      0.1 * ν.real Λprev ≤ ν.real S ∧
      ∀ x ∈ S, ∃ x' ∈ E, lgdLeExp μ δ (T + Real.log ((Box.card : ℝ) + 1)) x x' := by
  classical
  intro E hE hEm
  -- Step 1 (pigeonhole): a good segment of `Λ_i` meets `E` in mass `≥ b`
  obtain ⟨q, hqN, hqE, hqb⟩ : ∃ q ∈ Next, q ∉ Exc ∧ b ≤ ν (E ∩ seg q) := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    set G := Next.filter (fun p => p ∉ Exc) with hG
    set X := Next.filter (fun p => p ∈ Exc) with hX
    have hsub : E ⊆ (Λnext \ ⋃ p ∈ Next, seg p) ∪
        ((⋃ p ∈ G, E ∩ seg p) ∪ ⋃ p ∈ X, seg p) := by
      intro x hx
      by_cases hU : x ∈ ⋃ p ∈ Next, seg p
      · simp only [mem_iUnion] at hU
        obtain ⟨p, hp, hxp⟩ := hU
        by_cases hpE : p ∈ Exc
        · exact Or.inr (Or.inr (mem_biUnion (Finset.mem_filter.mpr ⟨hp, hpE⟩) hxp))
        · exact Or.inr (Or.inl (mem_biUnion (Finset.mem_filter.mpr ⟨hp, hpE⟩) ⟨hx, hxp⟩))
      · exact Or.inl ⟨hE hx, hU⟩
    have hbig : (Λnext \ ⋃ p ∈ Next, seg p) ∪ ((⋃ p ∈ G, E ∩ seg p) ∪ ⋃ p ∈ X, seg p) ⊆
        Λnext := by
      refine union_subset sdiff_subset (union_subset ?_ ?_) <;> intro x hx <;>
        simp only [mem_iUnion] at hx
      · obtain ⟨p, -, hxp⟩ := hx
        exact hE hxp.1
      · obtain ⟨p, hp, hxp⟩ := hx
        exact hNext p (Finset.mem_filter.mp hp).1 hxp
    have h1 : ν.real E ≤ ν.real (Λnext \ ⋃ p ∈ Next, seg p) +
        (ν.real (⋃ p ∈ G, E ∩ seg p) + ν.real (⋃ p ∈ X, seg p)) :=
      (measureReal_mono hsub (ne_top_of_le_ne_top hΛn (measure_mono hbig))).trans
        ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _)))
    have h2 : ν.real (⋃ p ∈ G, E ∩ seg p) ≤ Next.card * b.toReal := by
      refine (measureReal_biUnion_finset_le G _).trans ?_
      calc ∑ p ∈ G, ν.real (E ∩ seg p) ≤ ∑ _p ∈ G, b.toReal := by
            refine Finset.sum_le_sum fun p hp => ?_
            exact ENNReal.toReal_mono hb (hcon p (Finset.mem_filter.mp hp).1
              (Finset.mem_filter.mp hp).2).le
        _ = G.card * b.toReal := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Next.card * b.toReal := by
            gcongr
            exact Finset.filter_subset _ _
    have h3 : ν.real (⋃ p ∈ X, seg p) ≤ Exc.card * σ := by
      refine (measureReal_biUnion_finset_le X _).trans ?_
      calc ∑ p ∈ X, ν.real (seg p) ≤ ∑ _p ∈ X, σ := Finset.sum_le_sum fun p _ => hσ p
        _ = X.card * σ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Exc.card * σ := by
            gcongr
            exact fun p hp => (Finset.mem_filter.mp hp).2
    linarith
  have hqC : site q ∈ C := hsite q hqE (Or.inr hqN)
  set Λend : Set ℂ := E ∩ seg q with hΛend
  have hΛendBd : Λend ⊆ Bd (site q) := fun x hx => hseg q hx.2
  -- Step 2: chains from every good segment of `Λ_{i-1}`
  set F := Prev.filter (fun p => p ∉ Exc) with hF
  have hch : ∀ p ∈ F, ∃ z₀ ∈ Bd (site p), ν {z' ∈ Bd (site p) | ¬ lgdLeExp μ δ T z₀ z'} ≤ a ∧
      ∃ n < Box.card, ∃ y : ℕ → ℂ, y 0 = z₀ ∧ y n ∈ Λend ∧
        ∀ k < n, lgdLeExp μ δ T (y (k + 1)) (y k) := by
    intro p hp
    have hpC : site p ∈ C := hsite p (Finset.mem_filter.mp hp).2
      (Or.inl (Finset.mem_filter.mp hp).1)
    exact l53_cluster_chain ν (fun z z' => lgdLeExp μ δ T z z') Box C hCbox hCc Bd I ha hc hI hIc
      hBdc hopen (site p) hpC (site q) hqC Λend hΛendBd hqb
  choose! z₀ hz₀ hz₀a hz₀ch using hch
  have hU : ν.real (⋃ p ∈ Prev, seg p) ≤ ν.real (⋃ p ∈ F, seg p) + Exc.card * σ := by
    have hsub : (⋃ p ∈ Prev, seg p) ⊆
        (⋃ p ∈ F, seg p) ∪ ⋃ p ∈ Prev.filter (fun p => p ∈ Exc), seg p := by
      intro x hx
      simp only [mem_iUnion] at hx
      obtain ⟨p, hp, hxp⟩ := hx
      by_cases hpE : p ∈ Exc
      · exact Or.inr (mem_biUnion (Finset.mem_filter.mpr ⟨hp, hpE⟩) hxp)
      · exact Or.inl (mem_biUnion (Finset.mem_filter.mpr ⟨hp, hpE⟩) hxp)
    have hfin : ν (⋃ p ∈ Prev, seg p) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hΛp (measure_mono ?_)
      intro x hx
      simp only [mem_iUnion] at hx
      obtain ⟨p, hp, hxp⟩ := hx
      exact hPrev p hp hxp
    refine (measureReal_mono hsub ?_).trans ((measureReal_union_le _ _).trans ?_)
    · refine ne_top_of_le_ne_top hΛp (measure_mono (union_subset ?_ ?_)) <;> intro x hx <;>
        simp only [mem_iUnion] at hx <;> obtain ⟨p, hp, hxp⟩ := hx
      · exact hPrev p (Finset.mem_filter.mp hp).1 hxp
      · exact hPrev p (Finset.mem_filter.mp hp).1 hxp
    · gcongr
      refine (measureReal_biUnion_finset_le _ _).trans ?_
      calc ∑ p ∈ Prev.filter (fun p => p ∈ Exc), ν.real (seg p)
          ≤ ∑ _p ∈ Prev.filter (fun p => p ∈ Exc), σ := Finset.sum_le_sum fun p _ => hσ p
        _ = (Prev.filter (fun p => p ∈ Exc)).card * σ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Exc.card * σ := by
            gcongr
            exact fun p hp => (Finset.mem_filter.mp hp).2
  obtain ⟨S, hSΛ, hSm, hS⟩ := l53_desirable_of_chains ν μ (N := Box.card) (Λend := Λend)
    hΛp F seg z₀
    (fun p hp => hPrev p (Finset.mem_filter.mp hp).1)
    (fun p hp => by
      have h := hz₀a p hp
      have hsub : {x ∈ seg p | ¬ lgdLeExp μ δ T (z₀ p) x} ⊆
          {z' ∈ Bd (site p) | ¬ lgdLeExp μ δ T (z₀ p) z'} := fun x hx => ⟨hseg p hx.1, hx.2⟩
      exact ENNReal.toReal_mono ha ((measure_mono hsub).trans h))
    (fun p hp => by
      obtain ⟨n, hn, y, hy0, hyn, hyR⟩ := hz₀ch p hp
      exact ⟨n, hn.le, y, hy0, hyn, hyR⟩)
    (by linarith)
    (by
      have hFc : (F.card : ℝ) ≤ Prev.card := by exact_mod_cast Finset.card_filter_le _ _
      have ha0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
      nlinarith)
  exact ⟨S, hSΛ, hSm, fun x hx => by
    obtain ⟨x', hx', hxx'⟩ := hS x hx
    exact ⟨x', hx'.1, hxx'⟩⟩

end LQGMetric.DZZ
