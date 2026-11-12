/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56Cond3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56Whit
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# GM Lemma 5.6, condition 3 for an arbitrary square tube (task P2-M2L56)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, condition 3
(l. 2991–2994): "Each point of `O_u` is contained in a square of `𝒦_r(z)` which lies at graph
distance at most 40 from a square which contains `u` in the adjacency graph of squares of
`𝒦_r(z)` … It therefore follows from (5.17) …".

`geom56_cond3`: for every finite set `F` of grid squares of side `s`, `V = tubeOf s F`, and every
`w ∈ O_u` (component of `V ∩ B_{20s}(u)` containing `u`), `d(u, w; V) ≤ κ t` with
`κ = (2 + 2·43²)·whitC χ`, if all dyadic squares of side `2^{-j} s` meeting `B_{25s}(u)` have
internal diameter `≤ 2^{-jχ} t`. This is GM's argument: the squares of `F` meeting `O_u` (at most
`43²` of them) form a graph, connected through common points of `O_u` (because `O_u` is
connected), and consecutive square centres are joined through the common point by the Whitney
chains of `Geom56Whit.lean` (needed because the closed squares may leave `V`, deviation
P2-M2L3-2). The graph-distance bound `43²` replaces GM's `40` (any bound independent of `ε₁` works).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the constant of the Whitney chain -/
def whitC (χ : ℝ) : ℝ := 2 + 32 / (1 - (2 : ℝ)⁻¹ ^ χ)

lemma whitC_pos {χ : ℝ} (hχ : 0 < χ) : 0 < whitC χ := by
  have : (2 : ℝ)⁻¹ ^ χ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hχ
  have : 0 < 1 - (2 : ℝ)⁻¹ ^ χ := by linarith
  unfold whitC; positivity

lemma isClosed_gridSquare56 (s : ℝ) (m : ℤ × ℤ) : IsClosed (gridSquare s m) := by
  show IsClosed ({x : ℂ | (m.1 : ℝ) * s ≤ x.re} ∩ ({x : ℂ | x.re ≤ ((m.1 : ℝ) + 1) * s} ∩
    ({x : ℂ | (m.2 : ℝ) * s ≤ x.im} ∩ {x : ℂ | x.im ≤ ((m.2 : ℝ) + 1) * s})))
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)))

lemma isOpen_tubeOf56 (s : ℝ) (F : Finset (ℤ × ℤ)) : IsOpen (tubeOf s F) := isOpen_interior

lemma interior_gridSquare_subset_tubeOf {s : ℝ} {F : Finset (ℤ × ℤ)} {m : ℤ × ℤ} (hm : m ∈ F) :
    interior (gridSquare s m) ⊆ tubeOf s F :=
  interior_mono (subset_biUnion_of_mem (u := fun m => gridSquare s m) hm)

lemma mem_tubeOf_exists {s : ℝ} {F : Finset (ℤ × ℤ)} {x : ℂ} (hx : x ∈ tubeOf s F) :
    ∃ m ∈ F, x ∈ gridSquare s m := by
  have := interior_subset hx
  simpa only [mem_iUnion, exists_prop] using this

lemma sqCenter_mem_tubeOf {s : ℝ} (hs : 0 < s) {F : Finset (ℤ × ℤ)} {m : ℤ × ℤ} (hm : m ∈ F) :
    sqCenter s m ∈ tubeOf s F := by
  apply interior_gridSquare_subset_tubeOf hm
  apply openBox_subset_interior
  simp only [sqCenter, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- the Whitney chain inside a square tube -/
lemma geom56_whitney_tube (d : ContMetric) {s : ℝ} (hs : 0 < s) {F : Finset (ℤ × ℤ)}
    {m : ℤ × ℤ} (hm : m ∈ F) {p : ℂ} (hp : p ∈ gridSquare s m) (hpV : p ∈ tubeOf s F)
    {χ t : ℝ} (hχ : 0 < χ) (ht : 0 ≤ t) {W : Set ℂ} (hW : gridSquare s m ⊆ W)
    (hB : ∀ (j : ℕ) (m' : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m' ∩ W).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t)) :
    d.internal (tubeOf s F) p (sqCenter s m) ≤ ENNReal.ofReal (whitC χ * t) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (isOpen_tubeOf56 s F) p hpV
  exact geom56_whitney d hs (interior_gridSquare_subset_tubeOf hm) hp hρ hball hχ ht
    (fun j m' ⟨x, hx1, hx2⟩ => hB j m' ⟨x, hx1, hW hx2⟩)

/-- two squares of the tube with a common point in the tube: their centres are close -/
lemma geom56_adj (d : ContMetric) {s : ℝ} (hs : 0 < s) {F : Finset (ℤ × ℤ)}
    {a b : ℤ × ℤ} (ha : a ∈ F) (hb : b ∈ F) {q : ℂ} (hqa : q ∈ gridSquare s a)
    (hqb : q ∈ gridSquare s b) (hqV : q ∈ tubeOf s F)
    {χ t : ℝ} (hχ : 0 < χ) (ht : 0 ≤ t) {W : Set ℂ} (hWa : gridSquare s a ⊆ W)
    (hWb : gridSquare s b ⊆ W)
    (hB : ∀ (j : ℕ) (m' : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m' ∩ W).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t)) :
    d.internal (tubeOf s F) (sqCenter s a) (sqCenter s b) ≤
      ENNReal.ofReal (2 * (whitC χ * t)) := by
  have h0 : 0 ≤ whitC χ * t := mul_nonneg (whitC_pos hχ).le ht
  calc d.internal (tubeOf s F) (sqCenter s a) (sqCenter s b)
      ≤ d.internal (tubeOf s F) (sqCenter s a) q + d.internal (tubeOf s F) q (sqCenter s b) :=
        DFGPS.internal_triangle d _ _ _ _
    _ ≤ ENNReal.ofReal (whitC χ * t) + ENNReal.ofReal (whitC χ * t) :=
        add_le_add ((MetricGeometry.internalEDist_comm _ _ _).trans_le
          (geom56_whitney_tube d hs ha hqa hqV hχ ht hWa hB))
          (geom56_whitney_tube d hs hb hqb hqV hχ ht hWb hB)
    _ = ENNReal.ofReal (2 * (whitC χ * t)) := by
        rw [← ENNReal.ofReal_add h0 h0]; congr 1; ring

/-- the squares of `F` meeting `O` -/
def sqMeet (s : ℝ) (F : Finset (ℤ × ℤ)) (O : Set ℂ) : Finset (ℤ × ℤ) := by
  classical exact F.filter fun m => (gridSquare s m ∩ O).Nonempty

lemma mem_sqMeet {s : ℝ} {F : Finset (ℤ × ℤ)} {O : Set ℂ} {m : ℤ × ℤ} :
    m ∈ sqMeet s F O ↔ m ∈ F ∧ (gridSquare s m ∩ O).Nonempty := by
  classical
  unfold sqMeet
  convert Finset.mem_filter

/-- the adjacency graph: two squares are adjacent if they share a point of `O` -/
def sqGraph (s : ℝ) (F : Finset (ℤ × ℤ)) (O : Set ℂ) : SimpleGraph (sqMeet s F O) :=
  SimpleGraph.fromRel fun a b => (gridSquare s a ∩ gridSquare s b ∩ O).Nonempty

/-- the cost of a walk in the adjacency graph -/
lemma geom56_walk (d : ContMetric) {s : ℝ} (hs : 0 < s) {F : Finset (ℤ × ℤ)} {O W : Set ℂ}
    (hOV : O ⊆ tubeOf s F) (hW : ∀ m ∈ sqMeet s F O, gridSquare s m ⊆ W)
    {χ t : ℝ} (hχ : 0 < χ) (ht : 0 ≤ t)
    (hB : ∀ (j : ℕ) (m' : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m' ∩ W).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t))
    {a b : sqMeet s F O} (p : (sqGraph s F O).Walk a b) :
    d.internal (tubeOf s F) (sqCenter s a) (sqCenter s b) ≤
      ENNReal.ofReal (p.length * (2 * (whitC χ * t))) := by
  have h0 : 0 ≤ 2 * (whitC χ * t) := by have := (whitC_pos hχ).le; positivity
  induction p with
  | @nil a =>
    rw [SimpleGraph.Walk.length_nil]
    simp only [Nat.cast_zero, zero_mul, ENNReal.ofReal_zero, nonpos_iff_eq_zero]
    exact MetricGeometry.internalEDist_self (mem_image_of_mem _ (sqCenter_mem_tubeOf hs (mem_sqMeet.1 a.2).1))
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    have hadj := (SimpleGraph.fromRel_adj _ _ _).1 h
    obtain ⟨q, ⟨hqa, hqb⟩, hqO⟩ : (gridSquare s a ∩ gridSquare s b ∩ O).Nonempty := by
      rcases hadj.2 with h' | ⟨q, ⟨h1, h2⟩, h3⟩
      · exact h'
      · exact ⟨q, ⟨h2, h1⟩, h3⟩
    calc d.internal (tubeOf s F) (sqCenter s a) (sqCenter s c)
        ≤ d.internal (tubeOf s F) (sqCenter s a) (sqCenter s b) +
            d.internal (tubeOf s F) (sqCenter s b) (sqCenter s c) :=
          DFGPS.internal_triangle d _ _ _ _
      _ ≤ ENNReal.ofReal (2 * (whitC χ * t)) + ENNReal.ofReal (p.length * (2 * (whitC χ * t))) :=
          add_le_add (geom56_adj d hs (mem_sqMeet.1 a.2).1 (mem_sqMeet.1 b.2).1 hqa hqb (hOV hqO)
            hχ ht (hW _ a.2) (hW _ b.2) hB) ih
      _ = ENNReal.ofReal (((p.length + 1 : ℕ) : ℝ) * (2 * (whitC χ * t))) := by
          rw [← ENNReal.ofReal_add h0 (by positivity)]; congr 1; push_cast; ring

/-- at most `43²` squares of side `s` meet a set inside `B_{20s}(u)` -/
lemma card_sqMeet_le {s : ℝ} (hs : 0 < s) (F : Finset (ℤ × ℤ)) {O : Set ℂ} {u : ℂ}
    (hO : O ⊆ ball u (20 * s)) : (sqMeet s F O).card ≤ 43 ^ 2 := by
  have key : ∀ (k : ℤ) (y v : ℝ), (k : ℝ) * s ≤ y → y ≤ (k + 1) * s → |y - v| < 20 * s →
      ⌊v / s⌋ - 21 ≤ k ∧ k ≤ ⌊v / s⌋ + 21 := by
    intro k y v hk1 hk2 hyv
    rw [abs_lt] at hyv
    have e : v / s * s = v := div_mul_cancel₀ v hs.ne'
    have g1 : (⌊v / s⌋ : ℝ) * s ≤ v := by
      have := mul_le_mul_of_nonneg_right (Int.floor_le (v / s)) hs.le; rwa [e] at this
    have g2 : v < ((⌊v / s⌋ : ℝ) + 1) * s := by
      have := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (v / s)) hs; rwa [e] at this
    constructor
    · have h1 : (⌊v / s⌋ : ℝ) * s < ((k : ℝ) + 21) * s := by linarith
      have h2 : (⌊v / s⌋ : ℝ) < (k : ℝ) + 21 := lt_of_mul_lt_mul_right h1 hs.le
      have h3 : ⌊v / s⌋ < k + 21 := by exact_mod_cast h2
      omega
    · have h1 : (k : ℝ) * s < ((⌊v / s⌋ : ℝ) + 21) * s := by linarith
      have h2 : (k : ℝ) < (⌊v / s⌋ : ℝ) + 21 := lt_of_mul_lt_mul_right h1 hs.le
      have h3 : k < ⌊v / s⌋ + 21 := by exact_mod_cast h2
      omega
  have hsub : sqMeet s F O ⊆ Finset.Icc (⌊u.re / s⌋ - 21) (⌊u.re / s⌋ + 21) ×ˢ
      Finset.Icc (⌊u.im / s⌋ - 21) (⌊u.im / s⌋ + 21) := by
    intro m hm
    obtain ⟨-, x, hxS, hxO⟩ := mem_sqMeet.1 hm
    have hx := hO hxO
    rw [mem_ball, dist_eq_norm] at hx
    have hre : |x.re - u.re| < 20 * s := by
      rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans_lt hx
    have him : |x.im - u.im| < 20 * s := by
      rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans_lt hx
    obtain ⟨h1, h2, h3, h4⟩ := hxS
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨key _ _ _ h1 h2 hre, key _ _ _ h3 h4 him⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have e1 : (⌊u.re / s⌋ + 21 + 1 - (⌊u.re / s⌋ - 21)).toNat = 43 := by omega
  have e2 : (⌊u.im / s⌋ + 21 + 1 - (⌊u.im / s⌋ - 21)).toNat = 43 := by omega
  rw [e1, e2]; norm_num

/-- **GM Lemma 5.6, condition 3, for any square tube** (GM l. 2991–2994) -/
theorem geom56_cond3 (d : ContMetric) {s : ℝ} (hs : 0 < s) (F : Finset (ℤ × ℤ)) (u : ℂ)
    {χ t : ℝ} (hχ : 0 < χ) (ht : 0 ≤ t)
    (hB : ∀ (j : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m ∩ ball u (25 * s)).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m) (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m) ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t)) :
    ∀ w ∈ nearComp (tubeOf s F) (20 * s) u,
      d.internal (tubeOf s F) u w ≤ ENNReal.ofReal ((2 + 2 * 43 ^ 2) * whitC χ * t) := by
  intro w hw
  set V := tubeOf s F with hVdef
  set O := nearComp V (20 * s) u with hOdef
  have hOsub : O ⊆ V ∩ ball u (20 * s) := connectedComponentIn_subset _ _
  have huV : u ∈ V := by
    by_contra h
    have hO : O = ∅ := connectedComponentIn_eq_empty (fun h' => h h'.1)
    rw [hO] at hw; exact hw
  have huO : u ∈ O := mem_connectedComponentIn ⟨huV, mem_ball_self (by positivity)⟩
  have hW : ∀ m ∈ sqMeet s F O, gridSquare s m ⊆ ball u (25 * s) := by
    intro m hm
    obtain ⟨-, x, hxS, hxO⟩ := mem_sqMeet.1 hm
    refine (gridSquare_subset_ball hs hxS).trans (ball_subset_ball' ?_)
    have := (hOsub hxO).2; rw [mem_ball] at this; linarith
  obtain ⟨mu, hmuF, humu⟩ := mem_tubeOf_exists huV
  have hmuG : mu ∈ sqMeet s F O := mem_sqMeet.2 ⟨hmuF, u, humu, huO⟩
  set G := sqGraph s F O
  set R : Set (ℤ × ℤ) := {m | ∃ h : m ∈ sqMeet s F O, G.Reachable ⟨mu, hmuG⟩ ⟨m, h⟩} with hR
  have hcl : ∀ P : ℤ × ℤ → Prop,
      IsClosed (⋃ m ∈ {m | m ∈ sqMeet s F O ∧ P m}, gridSquare s m) := fun P =>
    ((Finset.finite_toSet (sqMeet s F O)).subset fun m hm => hm.1).isClosed_biUnion
      fun m _ => isClosed_gridSquare56 s m
  have hcov : O ⊆ (⋃ m ∈ {m | m ∈ sqMeet s F O ∧ m ∈ R}, gridSquare s m) ∪
      (⋃ m ∈ {m | m ∈ sqMeet s F O ∧ m ∉ R}, gridSquare s m) := by
    intro x hx
    obtain ⟨m, hmF, hxm⟩ := mem_tubeOf_exists (hOsub hx).1
    have hmG : m ∈ sqMeet s F O := mem_sqMeet.2 ⟨hmF, x, hxm, hx⟩
    by_cases hmR : m ∈ R
    · exact Or.inl (mem_biUnion (x := m) ⟨hmG, hmR⟩ hxm)
    · exact Or.inr (mem_biUnion (x := m) ⟨hmG, hmR⟩ hxm)
  have hdisj : ¬ (O ∩ ((⋃ m ∈ {m | m ∈ sqMeet s F O ∧ m ∈ R}, gridSquare s m) ∩
      (⋃ m ∈ {m | m ∈ sqMeet s F O ∧ m ∉ R}, gridSquare s m))).Nonempty := by
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
  have hw1 : w ∈ ⋃ m ∈ {m | m ∈ sqMeet s F O ∧ m ∈ R}, gridSquare s m := by
    rcases hcov hw with h | h
    · exact h
    · exact absurd (isPreconnected_closed_iff.1 isPreconnected_connectedComponentIn _ _
        (hcl _) (hcl _) hcov ⟨u, huO, mem_biUnion (x := mu) ⟨hmuG, hmuG, SimpleGraph.Reachable.refl _⟩
          humu⟩ ⟨w, hw, h⟩) hdisj
  obtain ⟨b, ⟨hbG, hbG', ⟨p⟩⟩, hwb⟩ := mem_iUnion₂.1 hw1
  have hlen : p.bypass.length < 43 ^ 2 + 1 := by
    have := p.bypass_isPath.length_lt
    rw [Fintype.card_coe] at this
    have := card_sqMeet_le hs F (fun x hx => (hOsub hx).2) (O := O)
    omega
  have hK : 0 ≤ whitC χ * t := mul_nonneg (whitC_pos hχ).le ht
  have hwalk := geom56_walk d hs (fun x hx => (hOsub hx).1) hW hχ ht hB p.bypass
  have hwalk' : d.internal V (sqCenter s mu) (sqCenter s b) ≤
      ENNReal.ofReal ((43 ^ 2 : ℝ) * (2 * (whitC χ * t))) := by
    refine hwalk.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity)))
    have : p.bypass.length ≤ 43 ^ 2 := by omega
    exact_mod_cast this
  calc d.internal V u w
      ≤ d.internal V u (sqCenter s mu) + d.internal V (sqCenter s mu) w :=
        DFGPS.internal_triangle d _ _ _ _
    _ ≤ d.internal V u (sqCenter s mu) + (d.internal V (sqCenter s mu) (sqCenter s b) +
          d.internal V (sqCenter s b) w) := add_le_add le_rfl (DFGPS.internal_triangle d _ _ _ _)
    _ ≤ ENNReal.ofReal (whitC χ * t) + (ENNReal.ofReal ((43 ^ 2 : ℝ) * (2 * (whitC χ * t))) +
          ENNReal.ofReal (whitC χ * t)) := by
        refine add_le_add (geom56_whitney_tube d hs hmuF humu huV hχ ht (hW _ hmuG) hB)
          (add_le_add hwalk' ?_)
        exact (MetricGeometry.internalEDist_comm _ _ _).trans_le <| geom56_whitney_tube d hs (mem_sqMeet.1 hbG).1 hwb (hOsub hw).1 hχ ht (hW _ hbG) hB
    _ = ENNReal.ofReal ((2 + 2 * 43 ^ 2) * whitC χ * t) := by
        rw [← ENNReal.ofReal_add (by positivity) hK, ← ENNReal.ofReal_add hK (by positivity)]
        congr 1; ring

end LQGMetric.GM
