/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510C1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56Cond3

/-!
# GM Lemma 5.10, conditions (5) and (9): deterministic part (task P2-M2M6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`,
l. 3313–3320 (condition (5)) and l. 3329 (condition (9)): the internal diameter of a connected
union of squares is bounded by chaining the internal-diameter bounds (5.33) of the squares.
GM chain through the squares of the tube; here, as in `geom56_cond3` (GM Lemma 5.6 condition 3),
the chain runs through the centres of the squares inside the *open* tube, with the Whitney chain
`geom56_whitney_tube` from a point to the centre of its square (decision of P2-M2L3-2).

* `l510_conn_tube`: a preconnected tube `tubeOf s F` has internal diameter
  `≤ (2 + 2 #F) · whitC χ · t` when all dyadic sub-squares near it satisfy the bound (5.33).
* `refineF`, `tubeOf_refineF`: a tube of side `s` is a tube of side `s / N` (subdivision).
* `card_le_of_meet_ball`: at most `(2⌈R/s⌉ + 3)²` squares of side `s` meet `cl B_R(0)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **Chaining through a connected square tube** (GM l. 3313–3320; graph walk as in
`geom56_cond3`) -/
theorem l510_conn_tube (d : ContMetric) {s : ℝ} (hs : 0 < s) (F : Finset (ℤ × ℤ))
    (hconn : IsPreconnected (tubeOf s F)) {χ t : ℝ} (hχ : 0 < χ) (ht : 0 ≤ t) {W : Set ℂ}
    (hWF : ∀ m ∈ F, gridSquare s m ⊆ W)
    (hB : ∀ (j : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m ∩ W).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m) (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m) ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t)) :
    ∀ u ∈ tubeOf s F, ∀ w ∈ tubeOf s F,
      d.internal (tubeOf s F) u w ≤ ENNReal.ofReal ((2 + 2 * F.card) * whitC χ * t) := by
  intro u huV w hw
  set V := tubeOf s F with hVdef
  have hW : ∀ m ∈ sqMeet s F V, gridSquare s m ⊆ W := fun m hm => hWF m (mem_sqMeet.1 hm).1
  obtain ⟨mu, hmuF, humu⟩ := mem_tubeOf_exists huV
  have hmuG : mu ∈ sqMeet s F V := mem_sqMeet.2 ⟨hmuF, u, humu, huV⟩
  set G := sqGraph s F V
  set R : Set (ℤ × ℤ) := {m | ∃ h : m ∈ sqMeet s F V, G.Reachable ⟨mu, hmuG⟩ ⟨m, h⟩} with hR
  have hcl : ∀ P : ℤ × ℤ → Prop,
      IsClosed (⋃ m ∈ {m | m ∈ sqMeet s F V ∧ P m}, gridSquare s m) := fun P =>
    ((Finset.finite_toSet (sqMeet s F V)).subset fun m hm => hm.1).isClosed_biUnion
      fun m _ => isClosed_gridSquare56 s m
  have hcov : V ⊆ (⋃ m ∈ {m | m ∈ sqMeet s F V ∧ m ∈ R}, gridSquare s m) ∪
      (⋃ m ∈ {m | m ∈ sqMeet s F V ∧ m ∉ R}, gridSquare s m) := by
    intro x hx
    obtain ⟨m, hmF, hxm⟩ := mem_tubeOf_exists hx
    have hmG : m ∈ sqMeet s F V := mem_sqMeet.2 ⟨hmF, x, hxm, hx⟩
    by_cases hmR : m ∈ R
    · exact Or.inl (mem_biUnion (x := m) ⟨hmG, hmR⟩ hxm)
    · exact Or.inr (mem_biUnion (x := m) ⟨hmG, hmR⟩ hxm)
  have hdisj : ¬ (V ∩ ((⋃ m ∈ {m | m ∈ sqMeet s F V ∧ m ∈ R}, gridSquare s m) ∩
      (⋃ m ∈ {m | m ∈ sqMeet s F V ∧ m ∉ R}, gridSquare s m))).Nonempty := by
    rintro ⟨x, hxO, hx1, hx2⟩
    obtain ⟨a, ⟨haG, haR⟩, hxa⟩ := mem_iUnion₂.1 hx1
    obtain ⟨b, ⟨hbG, hbR⟩, hxb⟩ := mem_iUnion₂.1 hx2
    apply hbR
    by_cases hab : a = b
    · subst hab; exact haR
    obtain ⟨_, hreach⟩ := haR
    have hadj : G.Adj ⟨a, haG⟩ ⟨b, hbG⟩ :=
      (SimpleGraph.fromRel_adj _ _ _).2
        ⟨fun h => hab (congrArg Subtype.val h), Or.inl ⟨x, ⟨hxa, hxb⟩, hxO⟩⟩
    exact ⟨hbG, hreach.trans hadj.reachable⟩
  have hw1 : w ∈ ⋃ m ∈ {m | m ∈ sqMeet s F V ∧ m ∈ R}, gridSquare s m := by
    rcases hcov hw with h | h
    · exact h
    · exact absurd (isPreconnected_closed_iff.1 hconn _ _ (hcl _) (hcl _) hcov
        ⟨u, huV, mem_biUnion (x := mu) ⟨hmuG, hmuG, SimpleGraph.Reachable.refl _⟩ humu⟩
        ⟨w, hw, h⟩) hdisj
  obtain ⟨b, ⟨hbG, hbG', ⟨p⟩⟩, hwb⟩ := mem_iUnion₂.1 hw1
  have hlen : p.bypass.length ≤ F.card := by
    have := p.bypass_isPath.length_lt
    rw [Fintype.card_coe] at this
    have h2 : (sqMeet s F V).card ≤ F.card := by
      classical
      unfold sqMeet
      exact Finset.card_filter_le _ _
    omega
  have hK : 0 ≤ whitC χ * t := mul_nonneg (whitC_pos hχ).le ht
  have hwalk := geom56_walk d hs (fun x hx => hx) hW hχ ht hB p.bypass
  have hwalk' : d.internal V (sqCenter s mu) (sqCenter s b) ≤
      ENNReal.ofReal ((F.card : ℝ) * (2 * (whitC χ * t))) := by
    refine hwalk.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity)))
    exact_mod_cast hlen
  calc d.internal V u w
      ≤ d.internal V u (sqCenter s mu) + d.internal V (sqCenter s mu) w :=
        DFGPS.internal_triangle d _ _ _ _
    _ ≤ d.internal V u (sqCenter s mu) + (d.internal V (sqCenter s mu) (sqCenter s b) +
          d.internal V (sqCenter s b) w) := add_le_add le_rfl (DFGPS.internal_triangle d _ _ _ _)
    _ ≤ ENNReal.ofReal (whitC χ * t) + (ENNReal.ofReal ((F.card : ℝ) * (2 * (whitC χ * t))) +
          ENNReal.ofReal (whitC χ * t)) := by
        refine add_le_add (geom56_whitney_tube d hs hmuF humu huV hχ ht (hW _ hmuG) hB)
          (add_le_add hwalk' ?_)
        exact (MetricGeometry.internalEDist_comm _ _ _).trans_le <|
          geom56_whitney_tube d hs (mem_sqMeet.1 hbG).1 hwb hw hχ ht (hW _ hbG) hB
    _ = ENNReal.ofReal ((2 + 2 * F.card) * whitC χ * t) := by
        rw [← ENNReal.ofReal_add (by positivity) hK, ← ENNReal.ofReal_add hK (by positivity)]
        congr 1; ring

/-- the internal-diameter form of `l510_conn_tube` -/
theorem l510_conn_tube_diam (d : ContMetric) {s : ℝ} (hs : 0 < s) (F : Finset (ℤ × ℤ))
    (hconn : IsPreconnected (tubeOf s F)) {χ t : ℝ} (hχ : 0 < χ) (ht : 0 ≤ t) {W : Set ℂ}
    (hWF : ∀ m ∈ F, gridSquare s m ⊆ W)
    (hB : ∀ (j : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m ∩ W).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m) (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m) ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t)) :
    internalDiam d (tubeOf s F) (tubeOf s F) ≤
      ENNReal.ofReal ((2 + 2 * F.card) * whitC χ * t) :=
  iSup₂_le fun u hu => iSup₂_le fun w hw => l510_conn_tube d hs F hconn hχ ht hWF hB u hu w hw

/-! ## Subdividing the squares -/

/-- the squares of side `s / N` subdividing the squares of `F` (side `s`) -/
def refineF (N : ℕ) (F : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  F.biUnion fun m => Finset.Icc ((N : ℤ) * m.1) (N * m.1 + N - 1) ×ˢ
    Finset.Icc ((N : ℤ) * m.2) (N * m.2 + N - 1)

lemma refine_1d {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) {M : ℤ} {a : ℝ}
    (h1 : M * s ≤ a) (h2 : a ≤ (M + 1) * s) :
    ∃ i : ℤ, (N : ℤ) * M ≤ i ∧ i ≤ N * M + N - 1 ∧ i * (s / N) ≤ a ∧ a ≤ (i + 1) * (s / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set σ := s / N with hσ
  have hσ0 : 0 < σ := div_pos hs hN'
  have hsσ : s = N * σ := by rw [hσ]; field_simp
  have f1 : (⌊a / σ⌋ : ℝ) * σ ≤ a := by
    have := Int.floor_le (a / σ); rwa [le_div_iff₀ hσ0] at this
  have f2 : a < ((⌊a / σ⌋ : ℝ) + 1) * σ := by
    have := Int.lt_floor_add_one (a / σ); rwa [div_lt_iff₀ hσ0] at this
  have g1 : (N : ℤ) * M ≤ ⌊a / σ⌋ := by
    apply Int.le_floor.2
    rw [le_div_iff₀ hσ0]; push_cast; rw [hsσ] at h1; linarith
  by_cases hc : ⌊a / σ⌋ ≤ N * M + N - 1
  · exact ⟨⌊a / σ⌋, g1, hc, f1, f2.le⟩
  · rw [not_le] at hc
    refine ⟨N * M + N - 1, by omega, le_rfl, ?_, ?_⟩
    · have : ((N * M + N - 1 : ℤ) : ℝ) ≤ ⌊a / σ⌋ := by exact_mod_cast hc.le
      nlinarith
    · push_cast; rw [hsσ] at h2; nlinarith

lemma mem_refineF_sub {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) {F : Finset (ℤ × ℤ)}
    {m' : ℤ × ℤ} (hm' : m' ∈ refineF N F) :
    ∃ m ∈ F, gridSquare (s / N) m' ⊆ gridSquare s m := by
  obtain ⟨m, hmF, hm⟩ := Finset.mem_biUnion.1 hm'
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hm
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsσ : s = N * (s / N) := by field_simp
  have hσ0 : 0 < s / N := div_pos hs hN'
  have c1 : ((N : ℤ) * m.1 : ℤ) ≤ (m'.1 : ℝ) := by exact_mod_cast a1
  have c2 : (m'.1 : ℝ) + 1 ≤ ((N * m.1 + N : ℤ) : ℝ) := by
    have : m'.1 + 1 ≤ N * m.1 + N := by omega
    exact_mod_cast this
  have c3 : ((N : ℤ) * m.2 : ℤ) ≤ (m'.2 : ℝ) := by exact_mod_cast b1
  have c4 : (m'.2 : ℝ) + 1 ≤ ((N * m.2 + N : ℤ) : ℝ) := by
    have : m'.2 + 1 ≤ N * m.2 + N := by omega
    exact_mod_cast this
  push_cast at c1 c2 c3 c4
  refine ⟨m, hmF, fun x ⟨x1, x2, x3, x4⟩ => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hsσ]; nlinarith
  · rw [hsσ]; nlinarith
  · rw [hsσ]; nlinarith
  · rw [hsσ]; nlinarith

lemma iUnion_refineF {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (F : Finset (ℤ × ℤ)) :
    (⋃ m' ∈ refineF N F, gridSquare (s / N) m') = ⋃ m ∈ F, gridSquare s m := by
  apply Subset.antisymm
  · refine iUnion₂_subset fun m' hm' => ?_
    obtain ⟨m, hmF, hsub⟩ := mem_refineF_sub hs hN hm'
    exact hsub.trans (subset_biUnion_of_mem (u := fun m => gridSquare s m) hmF)
  · refine iUnion₂_subset fun m hmF x ⟨x1, x2, x3, x4⟩ => ?_
    obtain ⟨i, i1, i2, i3, i4⟩ := refine_1d hs hN x1 x2
    obtain ⟨k, k1, k2, k3, k4⟩ := refine_1d hs hN x3 x4
    refine mem_iUnion₂.2 ⟨(i, k), ?_, i3, i4, k3, k4⟩
    exact Finset.mem_biUnion.2 ⟨m, hmF, Finset.mem_product.2
      ⟨Finset.mem_Icc.2 ⟨i1, i2⟩, Finset.mem_Icc.2 ⟨k1, k2⟩⟩⟩

lemma tubeOf_refineF {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (F : Finset (ℤ × ℤ)) :
    tubeOf (s / N) (refineF N F) = tubeOf s F := by
  unfold tubeOf; rw [iUnion_refineF hs hN F]

/-! ## Counting squares -/

lemma l510_coord_bound {s R y : ℝ} (hs : 0 < s) {k : ℤ} (h1 : k * s ≤ y) (h2 : y ≤ (k + 1) * s)
    (hy : |y| ≤ R) : -((⌈R / s⌉₊ : ℤ) + 1) ≤ k ∧ k ≤ (⌈R / s⌉₊ : ℤ) + 1 := by
  have hc : R / s ≤ (⌈R / s⌉₊ : ℝ) := Nat.le_ceil _
  have hy' := abs_le.1 hy
  have e1 : (k : ℝ) ≤ R / s := by rw [le_div_iff₀ hs]; linarith
  have e2 : -(R / s) ≤ (k : ℝ) + 1 := by
    rw [neg_le, le_div_iff₀ hs]; linarith
  constructor
  · have : (-((⌈R / s⌉₊ : ℤ) + 1) : ℝ) ≤ k := by push_cast; linarith
    exact_mod_cast this
  · have : (k : ℝ) ≤ ((⌈R / s⌉₊ : ℤ) + 1 : ℤ) := by push_cast; linarith
    exact_mod_cast this

/-- at most `(2⌈R/s⌉ + 3)²` grid squares of side `s` meet `cl B_R(0)` -/
lemma card_le_of_meet_ball {s R : ℝ} (hs : 0 < s) (F : Finset (ℤ × ℤ))
    (hF : ∀ m ∈ F, (gridSquare s m ∩ closedBall 0 R).Nonempty) :
    F.card ≤ (2 * ⌈R / s⌉₊ + 3) ^ 2 := by
  set n : ℤ := (⌈R / s⌉₊ : ℤ) + 1
  have hsub : F ⊆ Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n := by
    intro m hm
    obtain ⟨x, ⟨h1, h2, h3, h4⟩, hx⟩ := hF m hm
    rw [mem_closedBall, dist_zero_right] at hx
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨l510_coord_bound hs h1 h2 ((Complex.abs_re_le_norm x).trans hx),
      l510_coord_bound hs h3 h4 ((Complex.abs_im_le_norm x).trans hx)⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Int.card_Icc, sq]
  have e : (n + 1 - -n).toNat = 2 * ⌈R / s⌉₊ + 3 := by omega
  rw [e]

end LQGMetric.GM
