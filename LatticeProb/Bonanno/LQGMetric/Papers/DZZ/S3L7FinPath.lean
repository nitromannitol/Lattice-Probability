/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7FinPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinGeom

/-!
# DZZ Lemma 3.7: the enclosure of Definition 3.6 from a percolation enclosure (P2-DZZ3F)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1005–1015, Def 3.6 l. 935–940).

* `exists_path_sites`: a continuous path in `𝕍` visits a `*`-chain of level-`L` box sites
  (uniform continuity; points at distance `< 2^{-L}` lie in equal or `*`-adjacent boxes).
* `boxSite_hole`, `boxSite_out`: the start of a path in `B` lies in the hole
  `‖z‖_∞ < h + 2`, its end on `∂B_large` outside `annBox (2h - 2)`.
* `hasEnclosure_of_sites`: a `4`-connected set of good grid sites in the annulus meeting every
  `*`-path of grid sites from the hole to the outside gives `HasEnclosure B k good`
  (the list of boxes is a `Neighbour`-chain through the whole set, `exists_isChain_cover`).

Own elementary arguments (DZZ only say the enclosure "separates `B` from `𝕍 ∩ ∂B_large`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

lemma scale_lo {a x : ℝ} (L : ℕ) (h : a ≤ x * 2 ^ L) : a * (2 : ℝ)⁻¹ ^ L ≤ x := by
  have hs : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ L := by positivity
  calc a * (2 : ℝ)⁻¹ ^ L ≤ x * 2 ^ L * (2 : ℝ)⁻¹ ^ L := mul_le_mul_of_nonneg_right h hs
    _ = x := by rw [mul_assoc, mul_comm ((2 : ℝ) ^ L), pow_inv_mul_pow, mul_one]

lemma scale_hi {a x : ℝ} (L : ℕ) (h : x * 2 ^ L ≤ a) : x ≤ a * (2 : ℝ)⁻¹ ^ L := by
  have hs : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ L := by positivity
  calc x = x * 2 ^ L * (2 : ℝ)⁻¹ ^ L := by
        rw [mul_assoc, mul_comm ((2 : ℝ) ^ L), pow_inv_mul_pow, mul_one]
    _ ≤ a * (2 : ℝ)⁻¹ ^ L := mul_le_mul_of_nonneg_right h hs

lemma mem_closedBox_boxAt {L : ℕ} {v : ℂ} (hv : v ∈ dzzV) : v ∈ (DyBox.boxAt L v).closedBox := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  obtain ⟨a1, a2⟩ := idx_bounds (n := L) h0 h1
  obtain ⟨b1, b2⟩ := idx_bounds (n := L) h2 h3
  exact ⟨scale_lo L a1, scale_hi L a2, scale_lo L b1, scale_hi L b2⟩

lemma idx_step {L : ℕ} {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hxy : |x - y| < (2 : ℝ)⁻¹ ^ L) : (DyBox.idx L x : ℤ) ≤ DyBox.idx L y + 1 := by
  obtain ⟨a1, -⟩ := idx_bounds (n := L) hx0 hx1
  obtain ⟨-, b2⟩ := idx_bounds (n := L) hy0 hy1
  have ht : (0 : ℝ) < 2 ^ L := by positivity
  have h1 : (x - y) * 2 ^ L < 1 := by
    have := mul_lt_mul_of_pos_right (lt_of_le_of_lt (le_abs_self _) hxy) ht
    rwa [pow_inv_mul_pow] at this
  have h2 : (DyBox.idx L x : ℝ) < DyBox.idx L y + 2 := by linarith
  have h3 : DyBox.idx L x < DyBox.idx L y + 2 := by exact_mod_cast h2
  omega

/-- Points at distance `< 2^{-L}` lie in equal or `*`-adjacent boxes of level `L`. -/
lemma boxSite_step (c : ℤ × ℤ) {L : ℕ} {u v : ℂ} (hu : u ∈ dzzV) (hv : v ∈ dzzV)
    (huv : ‖u - v‖ < (2 : ℝ)⁻¹ ^ L) :
    boxSite c (DyBox.boxAt L u) = boxSite c (DyBox.boxAt L v) ∨
      PercAdjK (boxSite c (DyBox.boxAt L u)) (boxSite c (DyBox.boxAt L v)) := by
  obtain ⟨u0, u1, u2, u3⟩ := hu
  obtain ⟨v0, v1, v2, v3⟩ := hv
  have are : |u.re - v.re| ≤ ‖u - v‖ := by simpa using Complex.abs_re_le_norm (u - v)
  have aim : |u.im - v.im| ≤ ‖u - v‖ := by simpa using Complex.abs_im_le_norm (u - v)
  have hre : |u.re - v.re| < (2 : ℝ)⁻¹ ^ L := are.trans_lt huv
  have him : |u.im - v.im| < (2 : ℝ)⁻¹ ^ L := aim.trans_lt huv
  have hre' : |v.re - u.re| < (2 : ℝ)⁻¹ ^ L := by rwa [abs_sub_comm]
  have him' : |v.im - u.im| < (2 : ℝ)⁻¹ ^ L := by rwa [abs_sub_comm]
  have r1 := idx_step u0 u1 v0 v1 hre
  have r2 := idx_step v0 v1 u0 u1 hre'
  have i1 := idx_step u2 u3 v2 v3 him
  have i2 := idx_step v2 v3 u2 u3 him'
  by_cases he : boxSite c (DyBox.boxAt L u) = boxSite c (DyBox.boxAt L v)
  · exact Or.inl he
  · right
    simp only [boxSite, DyBox.boxAt, Prod.ext_iff, not_and_or] at he ⊢
    refine ⟨he, by omega, by omega, by omega, by omega⟩

/-- The times `i / M` (clamped into `[0, 1]`). -/
def ttM (M i : ℕ) : unitInterval := Set.projIcc 0 1 zero_le_one ((i : ℝ) / M)

lemma ttM_zero (M : ℕ) : ttM M 0 = 0 := by
  apply Subtype.ext; simp [ttM]

lemma ttM_self {M : ℕ} (hM : M ≠ 0) : ttM M M = 1 := by
  apply Subtype.ext; simp [ttM, hM]

lemma dist_ttM (M i : ℕ) : dist (ttM M i) (ttM M (i + 1)) ≤ 1 / M := by
  rw [Subtype.dist_eq, Real.dist_eq]
  refine (Set.abs_projIcc_sub_projIcc zero_le_one).trans (le_of_eq ?_)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  rw [abs_sub_comm]; push_cast
  rw [show ((i : ℝ) + 1) / M - i / M = 1 / M by ring]
  exact abs_of_nonneg (by positivity)

/-- A continuous path in `𝕍` visits a `*`-chain of level-`L` box sites. -/
theorem exists_path_sites (c : ℤ × ℤ) (L : ℕ) (p : C(unitInterval, ℂ)) (hp : ∀ t, p t ∈ dzzV) :
    ∃ Γ : Set (ℤ × ℤ), (∀ z ∈ Γ, ∃ t, z = boxSite c (DyBox.boxAt L (p t))) ∧
      Relation.ReflTransGen (PercStepIn Γ PercAdjK) (boxSite c (DyBox.boxAt L (p 0)))
        (boxSite c (DyBox.boxAt L (p 1))) := by
  have hu := CompactSpace.uniformContinuous_of_continuous p.continuous
  obtain ⟨δ, hδ, hδp⟩ := Metric.uniformContinuous_iff.1 hu ((2 : ℝ)⁻¹ ^ L) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  set M := m + 1 with hMdef
  have hM : 1 / (M : ℝ) < δ := by rw [hMdef]; push_cast; exact hm
  set σ : ℕ → ℤ × ℤ := fun i => boxSite c (DyBox.boxAt L (p (ttM M i))) with hσ
  refine ⟨{z | ∃ i ≤ M, σ i = z}, fun z ⟨i, _, hi⟩ => ⟨ttM M i, hi.symm⟩, ?_⟩
  have key : ∀ i ≤ M,
      Relation.ReflTransGen (PercStepIn {z | ∃ i ≤ M, σ i = z} PercAdjK) (σ 0) (σ i) := by
    intro i
    induction i with
    | zero => intro _; exact .refl
    | succ i ih =>
      intro hi
      have hd : dist (p (ttM M i)) (p (ttM M (i + 1))) < (2 : ℝ)⁻¹ ^ L :=
        hδp ((dist_ttM M i).trans_lt hM)
      rw [dist_eq_norm] at hd
      rcases boxSite_step c (hp _) (hp _) hd with h | h
      · have h' : σ i = σ (i + 1) := h
        rw [← h']
        exact ih (by omega)
      · exact (ih (by omega)).tail ⟨⟨i, by omega, rfl⟩, ⟨i + 1, hi, rfl⟩, h⟩
  have := key M le_rfl
  have e0 : σ 0 = boxSite c (DyBox.boxAt L (p 0)) := by simp only [σ, ttM_zero]
  have eM : σ M = boxSite c (DyBox.boxAt L (p 1)) := by
    simp only [σ]; rw [ttM_self (show M ≠ 0 by omega)]
  rw [e0, eM] at this
  exact this

lemma frontier_largeBox_sub (B : DyBox) {z : ℂ} (hz : z ∈ frontier B.largeBox) :
    |z.re - B.center.re| = B.side ∨ |z.im - B.center.im| = B.side := by
  have cr : Continuous fun w : ℂ => |w.re - B.center.re| :=
    continuous_abs.comp (Complex.continuous_re.sub continuous_const)
  have ci : Continuous fun w : ℂ => |w.im - B.center.im| :=
    continuous_abs.comp (Complex.continuous_im.sub continuous_const)
  have hcl : IsClosed B.largeBox :=
    (isClosed_le cr continuous_const).inter (isClosed_le ci continuous_const)
  have hzc : z ∈ B.largeBox := hcl.frontier_subset hz
  by_contra hne
  push_neg at hne
  set O : Set ℂ := {w | |w.re - B.center.re| < B.side ∧ |w.im - B.center.im| < B.side}
  have hO : IsOpen O := (isOpen_lt cr continuous_const).inter (isOpen_lt ci continuous_const)
  have hOs : O ⊆ B.largeBox := fun w hw => ⟨hw.1.le, hw.2.le⟩
  exact hz.2 (interior_maximal hOs hO ⟨lt_of_le_of_ne hzc.1 hne.1, lt_of_le_of_ne hzc.2 hne.2⟩)

/-- A point of `B` lies in a box of the hole `‖z‖_∞ < h + 2`. -/
lemma boxSite_hole (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) {v : ℂ} (hv : v ∈ dzzV)
    (hB : v ∈ B.closedBox) :
    -((h : ℤ) + 2) < (boxSite (l37c B h) (DyBox.boxAt (B.n + k) v)).1 ∧
      (boxSite (l37c B h) (DyBox.boxAt (B.n + k) v)).1 < (h : ℤ) + 2 ∧
      -((h : ℤ) + 2) < (boxSite (l37c B h) (DyBox.boxAt (B.n + k) v)).2 ∧
      (boxSite (l37c B h) (DyBox.boxAt (B.n + k) v)).2 < (h : ℤ) + 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  obtain ⟨a1, a2⟩ := idx_bounds (n := B.n + k) h0 h1
  obtain ⟨b1, b2⟩ := idx_bounds (n := B.n + k) h2 h3
  obtain ⟨d1, d2, d3, d4⟩ := hB
  have ht : (0 : ℝ) ≤ 2 ^ (B.n + k) := by positivity
  have e := side_mul_pow B hK
  have m1 := mul_le_mul_of_nonneg_right d1 ht
  have m2 := mul_le_mul_of_nonneg_right d2 ht
  have m3 := mul_le_mul_of_nonneg_right d3 ht
  have m4 := mul_le_mul_of_nonneg_right d4 ht
  rw [mul_assoc, e] at m1 m2 m3 m4
  simp only [boxSite, DyBox.boxAt, l37c]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ((-((h : ℤ) + 2) : ℤ) : ℝ) <
        (((DyBox.idx (B.n + k) v.re : ℤ) - (2 * h * B.j + h) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (((DyBox.idx (B.n + k) v.re : ℤ) - (2 * h * B.j + h) : ℤ) : ℝ) <
        (((h : ℤ) + 2 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : ((-((h : ℤ) + 2) : ℤ) : ℝ) <
        (((DyBox.idx (B.n + k) v.im : ℤ) - (2 * h * B.k + h) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (((DyBox.idx (B.n + k) v.im : ℤ) - (2 * h * B.k + h) : ℤ) : ℝ) <
        (((h : ℤ) + 2 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- A point of `∂B_large` in `𝕍` lies in a box outside `annBox (2h - 2)`. -/
lemma boxSite_out (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) {v : ℂ} (hv : v ∈ dzzV)
    (hB : v ∈ frontier B.largeBox) :
    ¬ annBox (2 * (h : ℤ) - 2) (boxSite (l37c B h) (DyBox.boxAt (B.n + k) v)) := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  obtain ⟨a1, a2⟩ := idx_bounds (n := B.n + k) h0 h1
  obtain ⟨b1, b2⟩ := idx_bounds (n := B.n + k) h2 h3
  have e := side_mul_pow B hK
  have ej : (B.j : ℝ) * B.side * 2 ^ (B.n + k) = B.j * (2 * h) := by rw [mul_assoc, e]
  have ek : (B.k : ℝ) * B.side * 2 ^ (B.n + k) = B.k * (2 * h) := by rw [mul_assoc, e]
  have hs0 := (side_pos' B).le
  intro hA
  obtain ⟨c1, c2, c3, c4⟩ := hA
  simp only [boxSite, DyBox.boxAt, l37c] at c1 c2 c3 c4
  have r1 : (-(2 * (h : ℝ) - 2)) ≤ (DyBox.idx (B.n + k) v.re : ℝ) - (2 * h * B.j + h) := by
    have := Int.cast_le (R := ℝ).2 c1; push_cast at this; linarith
  have r2 : (DyBox.idx (B.n + k) v.re : ℝ) - (2 * h * B.j + h) ≤ 2 * h - 2 := by
    have := Int.cast_le (R := ℝ).2 c2; push_cast at this; linarith
  have r3 : (-(2 * (h : ℝ) - 2)) ≤ (DyBox.idx (B.n + k) v.im : ℝ) - (2 * h * B.k + h) := by
    have := Int.cast_le (R := ℝ).2 c3; push_cast at this; linarith
  have r4 : (DyBox.idx (B.n + k) v.im : ℝ) - (2 * h * B.k + h) ≤ 2 * h - 2 := by
    have := Int.cast_le (R := ℝ).2 c4; push_cast at this; linarith
  rcases frontier_largeBox_sub B hB with hr | hr
  · rcases (abs_eq hs0).1 hr with q | q
    · have := congrArg (· * (2 : ℝ) ^ (B.n + k)) q
      simp only [DyBox.center, sub_mul, add_mul] at this
      linarith
    · have := congrArg (· * (2 : ℝ) ^ (B.n + k)) q
      simp only [DyBox.center, sub_mul, add_mul, neg_mul] at this
      linarith
  · rcases (abs_eq hs0).1 hr with q | q
    · have := congrArg (· * (2 : ℝ) ^ (B.n + k)) q
      simp only [DyBox.center, sub_mul, add_mul] at this
      linarith
    · have := congrArg (· * (2 : ℝ) ^ (B.n + k)) q
      simp only [DyBox.center, sub_mul, add_mul, neg_mul] at this
      linarith

lemma chain_mem_of_stepIn {S : Set (ℤ × ℤ)} {adj : ℤ × ℤ → ℤ × ℤ → Prop} :
    ∀ {x0 : ℤ × ℤ} {l : List (ℤ × ℤ)}, List.IsChain (PercStepIn S adj) (x0 :: l) → x0 ∈ S →
      ∀ y ∈ x0 :: l, y ∈ S
  | x0, [], _, hx, y, hy => by
    rw [List.mem_singleton] at hy; subst hy; exact hx
  | x0, x1 :: l, hch, hx, y, hy => by
    rw [List.isChain_cons_cons] at hch
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact chain_mem_of_stepIn hch.2 hch.1.2.1 y hy

/-- **Encoding of DZZ Def 3.6** (l. 935–940, 1005–1015): a `4`-connected set `U` of good grid
sites in the annulus `h + 2 ≤ ‖z‖_∞ ≤ 2h - 2` around `B` (in units of `2^{-(n_B + k)}`,
`2^k = 2h`) meeting every `*`-path of grid sites from the hole to the outside of the annulus
gives an enclosure of `B` by good neighbouring boxes of `𝓑(B, 2^{-k})`. -/
theorem hasEnclosure_of_sites (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) (good : DyBox → Prop)
    (U : Set (ℤ × ℤ)) (hgrid : ∀ z ∈ U, InGrid (B.n + k) (l37c B h) z)
    (hann : ∀ z ∈ U, ∃ d, z ∈ annRect ((h : ℤ) + 2) (2 * (h : ℤ) - 2) d)
    (hgood : ∀ z ∈ U, good (siteBox (B.n + k) (l37c B h) z)) (hne : U.Nonempty)
    (hconn : ∀ x ∈ U, ∀ y ∈ U, Relation.ReflTransGen (PercStepIn U PercAdj4) x y)
    (hsep : ∀ (Γ : Set (ℤ × ℤ)) (s e : ℤ × ℤ), (∀ z ∈ Γ, InGrid (B.n + k) (l37c B h) z) →
      (-((h : ℤ) + 2) < s.1 ∧ s.1 < (h : ℤ) + 2 ∧ -((h : ℤ) + 2) < s.2 ∧ s.2 < (h : ℤ) + 2) →
      ¬ annBox (2 * (h : ℤ) - 2) e →
      Relation.ReflTransGen (PercStepIn Γ PercAdjK) s e → ∃ z ∈ U, z ∈ Γ) :
    HasEnclosure B k good := by
  set N : ℤ := 2 * (h : ℤ) - 2
  have hfin : U.Finite := by
    refine (Finset.finite_toSet (Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N)).subset fun z hz => ?_
    obtain ⟨d, ⟨a1, a2, a3, a4⟩, -⟩ := hann z hz
    simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨a1, a2⟩, a3, a4⟩
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨l, hch, hcov⟩ := exists_isChain_cover hconn hfin.toFinset.toList
    (fun x hx => by simpa using hx) x0 hx0
  have hmemU : ∀ y ∈ x0 :: l, y ∈ U := chain_mem_of_stepIn hch hx0
  refine ⟨(x0 :: l).map (siteBox (B.n + k) (l37c B h)), by simp, ?_, ?_, ?_⟩
  · exact List.isChain_map_of_isChain _
      (fun a b hab => neighbour_siteBox (hgrid a hab.1) (hgrid b hab.2.1) hab.2.2) hch
  · intro b' hb'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb'
    have hzU := hmemU z hz
    obtain ⟨d, hd1, hd2⟩ := hann z hzU
    exact ⟨siteBox_mem_boxColl B hK (hgrid z hzU) hd1, disjoint_siteBox B hK (hgrid z hzU) hd2,
      hgood z hzU⟩
  · intro p hpV hp0 hp1
    obtain ⟨Γ, hΓ, hrt⟩ := exists_path_sites (l37c B h) (B.n + k) p hpV
    obtain ⟨z, hzU, hzΓ⟩ := hsep Γ _ _
      (fun z hz => by obtain ⟨t, rfl⟩ := hΓ z hz; exact inGrid_boxSite _ _)
      (boxSite_hole B hK (hpV 0) hp0) (boxSite_out B hK (hpV 1) hp1) hrt
    obtain ⟨t, rfl⟩ := hΓ z hzΓ
    refine ⟨t, siteBox (B.n + k) (l37c B h) (boxSite (l37c B h) (DyBox.boxAt (B.n + k) (p t))),
      ?_, ?_⟩
    · exact List.mem_map.2 ⟨_, hcov _ (by simpa using hzU), rfl⟩
    · rw [siteBox_boxSite (L := B.n + k) (l37c B h) (DyBox.boxAt (B.n + k) (p t)) rfl]
      exact mem_closedBox_boxAt (hpV t)

end DZZ
end LQGMetric
