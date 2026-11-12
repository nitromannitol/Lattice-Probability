/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J2

/-!
# DZZ Lemma 5.3, node 3: the percolation bound for the good cluster of a box grid

The probabilistic part of the percolation step of DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`
l. 2504–2514, "similar to (eq-par)", proof of (eq-par) l. 1953–2000). Sites of the grid
(the `K × K` sub-boxes of a cell) are bad on events `B z` with `μ (B z) ≤ ε`, and
families of sites at pairwise `ℓ^∞`-distance `> r` satisfy the product bound (the form of
`l53_cond_biInter`, with `μ = P[· | A₀]`); the same holds on the set `Box ⊇ annBox N` of all
boxes (see S5L53J2 for the boundary depths `tb d`). Then, outside an event of probability

  `4 (2N+1) (8θ)^{N-n+1} + 4 (r+1) C(2N+1, j) ((N-n+2) ε)^j`   (`ε ≤ θ^{(r+1)²}`, `8θ ≤ 1/2`),

there is a `4`-connected cluster `C` of good boxes containing, on each of the four sides, the
boundary box `l53Col n N d a (tb d)` of every non-corner position `a` (`|a - N| < n`) except
fewer than `(r+1) j` of them.

The first term is the Peierls bound for a good enclosure of the annulus `n ≤ ‖z‖_∞ ≤ N`
(`perc_annulus_peierls`), the second the union bound for `j` bad columns in one class
(`l53_count_bad`), over the `4 (r+1)` classes (side, residue of `a` mod `r+1`). Off both,
`l53_cluster` gives `C`. This
replaces DZZ's duality-and-enumeration bound (eq-enumeration) by the existing enclosure Peierls
bound; it gives the conclusion (eq-connectivity-percolation) in the stronger form that one
cluster serves all `Λ ⊆ Λ_i` at once.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric

/-- **Percolation bound for the good cluster of a box grid** (DZZ l. 1953–2000, abstract
form). -/
theorem l53_perc_cluster {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n N : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (Box : Set (ℤ × ℤ)) (hBox : ∀ z, annBox N z → z ∈ Box)
    (tb : PercDir → ℤ) (htb : ∀ d, (N : ℤ) - n ≤ tb d ∧ tb d ≤ N - n + 1)
    (hcolB : ∀ d a, (N : ℤ) - n < a → a < N + n → ∀ t, 0 ≤ t → t ≤ tb d →
      l53Col n N d a t ∈ Box)
    (B : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹)
    (hεθ : ε ≤ θ ^ ((r + 1) ^ 2)) (hε : ∀ z, z ∈ Box → μ (B z) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, z ∈ Box) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x))
    (j : ℕ) :
    μ {ω | ¬ ∃ C : Set (ℤ × ℤ), (∀ z ∈ C, z ∈ Box ∧ ω ∉ B z) ∧
        (∀ x ∈ C, ∀ y ∈ C, Relation.ReflTransGen (PercStepIn C PercAdj4) x y) ∧
        ∀ d, ∃ E : Finset ℤ, E.card < (r + 1) * j ∧ ∀ a : ℤ, (N : ℤ) - n < a → a < N + n → a ∉ E →
          l53Col n N d a (tb d) ∈ C} ≤
      4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) +
        4 * (r + 1) * (((2 * N + 1).choose j : ℝ≥0∞) * (((N - n + 2 : ℕ) : ℝ≥0∞) * ε) ^ j) := by
  classical
  set m : ℕ := N - n + 2 with hm
  set q : ℤ := (r : ℤ) + 1 with hq
  have hq0 : 0 < q := by omega
  set cls : Finset ℤ := Finset.Ico 0 q with hcls
  have hclsc : cls.card = r + 1 := by rw [hcls, Int.card_Ico]; omega
  set I : ℤ → Finset ℤ := fun c => (Finset.Ioo ((N : ℤ) - n) (N + n)).filter (fun a => a % q = c)
    with hI
  set Y : PercDir → ℤ → Finset (ℤ × ℤ) := fun d a =>
    (Finset.range (tb d + 1).toNat).image (fun t : ℕ => l53Col n N d a t) with hY
  set Cnt : PercDir → ℤ → Set Ω := fun d c =>
    {ω | ∃ S ⊆ I c, S.card = j ∧ ∀ a ∈ S, ∃ y ∈ Y d a, ω ∈ B y} with hCnt
  set b : ℝ≥0∞ := ((2 * N + 1).choose j : ℝ≥0∞) * ((m : ℝ≥0∞) * ε) ^ j with hb
  have hYmem : ∀ d a x, x ∈ Y d a ↔ ∃ t : ℕ, t < (tb d + 1).toNat ∧ l53Col n N d a t = x := by
    intro d a x
    simp only [hY, Finset.mem_image, Finset.mem_range]
  have hcnt : ∀ d c, μ (Cnt d c) ≤ b := by
    intro d c
    refine (l53_count_bad μ (I c) (Y d) B (ε := ε) (m := m) (fun a _ => ?_) ?_ ?_ j).trans ?_
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_range]
      have := htb d
      omega
    · intro a _ a' _ x hx hx'
      obtain ⟨t, -, rfl⟩ := (hYmem d a x).1 hx
      obtain ⟨t', -, ht'⟩ := (hYmem d a' _).1 hx'
      have := annFromStd_inj n N d ht'
      simp only [Prod.mk.injEq] at this
      exact this.1.symm
    · intro F hF hF1
      have hFbox : ∀ x ∈ F, x ∈ Box := by
        intro x hx
        obtain ⟨a, ha, hxa⟩ := hF x hx
        obtain ⟨t, ht, rfl⟩ := (hYmem d a x).1 hxa
        simp only [hI, Finset.mem_filter, Finset.mem_Ioo] at ha
        exact hcolB d a ha.1.1 ha.1.2 t (by omega) (by omega)
      refine (hind F hFbox ?_).trans (Finset.prod_le_pow_card F _ ε fun x hx => hε x (hFbox x hx))
      intro x hx y hy hxy
      obtain ⟨a, ha, hxa⟩ := hF x hx
      obtain ⟨a', ha', hya⟩ := hF y hy
      obtain ⟨t, -, rfl⟩ := (hYmem d a x).1 hxa
      obtain ⟨t', -, rfl⟩ := (hYmem d a' _).1 hya
      have hne : a ≠ a' := by
        rintro rfl
        exact hxy (hF1 a ha _ hx _ hy hxa hya)
      simp only [hI, Finset.mem_filter] at ha ha'
      have e1 := Int.mul_ediv_add_emod a q
      have e2 := Int.mul_ediv_add_emod a' q
      set k : ℤ := a / q - a' / q with hkdef
      have hk : a - a' = q * k := by rw [hkdef, mul_sub]; linarith [ha.2, ha'.2]
      have hk0 : k ≠ 0 := by
        intro h0; apply hne; rw [h0, mul_zero] at hk; linarith
      refine annFromStd_far n N d r ?_
      simp only [PercFar]
      rcases lt_or_gt_of_ne hk0 with hk1 | hk1
      · right; left; nlinarith
      · left; nlinarith
    · rw [hb]
      gcongr
      have hc : (I c).card ≤ 2 * N + 1 := by
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Int.card_Ioo]
        omega
      exact hc
  have hpei := perc_annulus_peierls μ n N hn hnN B r hθ hεθ
    (fun z ⟨d, hz⟩ => hε z (hBox z hz.1)) (fun F hF hfar => hind F (fun z hz => by
      obtain ⟨d, hd⟩ := hF z hz
      exact hBox z hd.1) hfar)
  set Bad : PercDir → Set Ω := fun d => ⋃ c ∈ cls, Cnt d c with hBad
  have hBadle : ∀ d, μ (Bad d) ≤ (r + 1) * b := by
    intro d
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ c ∈ cls, μ (Cnt d c) ≤ ∑ _c ∈ cls, b := Finset.sum_le_sum fun c _ => hcnt d c
      _ = (r + 1) * b := by rw [Finset.sum_const, nsmul_eq_mul, hclsc]; push_cast; ring
  have hsub : {ω | ¬ ∃ C : Set (ℤ × ℤ), (∀ z ∈ C, z ∈ Box ∧ ω ∉ B z) ∧
        (∀ x ∈ C, ∀ y ∈ C, Relation.ReflTransGen (PercStepIn C PercAdj4) x y) ∧
        ∀ d, ∃ E : Finset ℤ, E.card < (r + 1) * j ∧ ∀ a : ℤ, (N : ℤ) - n < a → a < N + n → a ∉ E →
          l53Col n N d a (tb d) ∈ C} ⊆
      {ω | ¬ PercEnclosure n N {z | ω ∉ B z}} ∪ ((Bad .T ∪ Bad .B) ∪ (Bad .R ∪ Bad .L)) := by
    intro ω hω
    by_contra hc
    simp only [mem_union, not_or, mem_ofPred_eq, not_not] at hc
    obtain ⟨henc, ⟨hT, hB⟩, ⟨hR, hL⟩⟩ := hc
    have hgood : ∀ d, ∀ c ∈ cls, ω ∉ Cnt d c := by
      intro d c hc' hω'
      have hd : ω ∈ Bad d := mem_biUnion hc' hω'
      cases d
      · exact hT hd
      · exact hB hd
      · exact hR hd
      · exact hL hd
    apply hω
    obtain ⟨C, hC, hCc, hCcol⟩ := l53_cluster n N (by exact_mod_cast hn) (by exact_mod_cast hnN)
      {z | ω ∉ B z} Box hBox tb htb hcolB henc
    refine ⟨C, hC, hCc, fun d => ?_⟩
    set E : Finset ℤ := (Finset.Ioo ((N : ℤ) - n) (N + n)).filter
      (fun a => ∃ y ∈ Y d a, ω ∈ B y) with hE
    have hpart : ∀ c ∈ cls, (E.filter (fun a => a % q = c)).card < j := by
      intro c hc'
      by_contra hj
      obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (not_lt.mp hj)
      refine hgood d c hc' ⟨S, fun a ha => ?_, hSc, fun a ha => ?_⟩
      · have := hS ha
        simp only [hE, hI, Finset.mem_filter] at this ⊢
        exact ⟨this.1.1, this.2⟩
      · have := hS ha
        simp only [hE, Finset.mem_filter] at this
        exact this.1.2
    refine ⟨E, ?_, fun a ha₁ ha₂ haE => hCcol d a ha₁ ha₂ fun t ht₁ ht₂ => ?_⟩
    · rw [Finset.card_eq_sum_card_fiberwise (f := fun a => a % q) (t := cls) (fun a _ =>
        Finset.mem_Ico.2 ⟨Int.emod_nonneg a hq0.ne', Int.emod_lt_of_pos a hq0⟩)]
      calc ∑ c ∈ cls, (E.filter (fun a => a % q = c)).card < ∑ _c ∈ cls, j :=
            Finset.sum_lt_sum_of_nonempty ⟨0, by simp [hcls, hq0]⟩ hpart
        _ = (r + 1) * j := by rw [Finset.sum_const, hclsc, smul_eq_mul]
    · intro hbad
      apply haE
      simp only [hE, Finset.mem_filter, Finset.mem_Ioo]
      refine ⟨⟨ha₁, ha₂⟩, l53Col n N d a t, (hYmem d a _).2 ⟨t.toNat, by omega, ?_⟩, hbad⟩
      rw [Int.toNat_of_nonneg ht₁]
  calc _ ≤ μ {ω | ¬ PercEnclosure n N {z | ω ∉ B z}} +
        ((μ (Bad .T) + μ (Bad .B)) + (μ (Bad .R) + μ (Bad .L))) := by
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr <;> exact measure_union_le _ _
    _ ≤ 4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) +
        (((r + 1) * b + (r + 1) * b) + ((r + 1) * b + (r + 1) * b)) := by
        gcongr
        · exact hBadle _
        · exact hBadle _
        · exact hBadle _
        · exact hBadle _
    _ = 4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) +
        4 * (r + 1) * (((2 * N + 1).choose j : ℝ≥0∞) * (((N - n + 2 : ℕ) : ℝ≥0∞) * ε) ^ j) := by
        rw [hb]; ring

end LQGMetric.DZZ
