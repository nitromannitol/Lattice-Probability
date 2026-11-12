/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Det
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L20
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusPeierls
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinPath
import Mathlib.Algebra.Order.Floor.Extended

/-!
# DG Lemma 3.19, deterministic part: a good enclosure of squares bounds the LGD below (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.19
(`lem-annulus-perc`, DG:1614–1660), at an arbitrary scale `s > 0` and offset `b` (D105 item 1,
DV-D105-3): DG's annulus `𝒜_n = [−n,2n]² ∖ (0,n)²` becomes `s𝒜_n + b`, with inner square
`annIn s b n = b + [0,sn]²` and outer square `annOut s b n = b + [−sn,2sn]²` (the sets
`l321In`/`l321Out` of Papers/DG/S3L21R, verbatim).

* The squares of `𝒮(𝒜_n)` (DG:1641) are the squares of the grid `b + sℤ²`; the site `z ∈ ℤ²` is
  the square with lower left corner `b + s (c₀ + z)`, `c₀ = ⌊n/2⌋` (`annSq`), so that the hole
  `‖z‖_∞ < c₀ + 2` of `Perc.AnnulusPeierls` contains the sites of the inner square and the sites
  of `∂ annOut` lie outside `annBox (n − 2 + c₀)`; `annSqHalf` is `S(1/2)` (side `2s`).
* `goodAnn` is condition 1 of DG's event `E_S^ε` (DG:1642): `D^ε(S, ∂S(1/2)) ≥ M`.
* `dgLGDSet_ann_ge_of_enc` is DG:1650–1652: "each Euclidean path from `∂_in 𝒜_n` to `∂_out 𝒜_n`
  must pass through one of the squares `S ∈ 𝒫` … must cross one of the annuli `S(1/2) ∖ S`".
  The planar input is `PercEnclosure` (every `*`-path of sites from the hole to the outside
  meets the enclosure); a continuous path visits a `*`-chain of sites (`exists_path_annSites`,
  the whole-plane version of DZZ's `exists_path_sites`, Papers/DZZ/S3L7FinPath); the crossing of
  `S(1/2) ∖ S` is `exists_cross_subpath` (Papers/DG/S3L20).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- the inner square `b + [0, sn]²` of `s𝒜_n + b` -/
def annIn (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  Icc b.re (b.re + s * n) ×ℂ Icc b.im (b.im + s * n)

/-- the outer square `b + [−sn, 2sn]²` of `s𝒜_n + b` -/
def annOut (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  Icc (b.re - s * n) (b.re + 2 * (s * n)) ×ℂ Icc (b.im - s * n) (b.im + 2 * (s * n))

/-- the site of a point in the grid `b + sℤ²`, recentred at `c₀` -/
def annSite (s : ℝ) (b : ℂ) (c₀ : ℤ) (v : ℂ) : ℤ × ℤ :=
  (⌊(v.re - b.re) / s⌋ - c₀, ⌊(v.im - b.im) / s⌋ - c₀)

/-- the closed square `S` of the site `z` -/
def annSq (s : ℝ) (b : ℂ) (c₀ : ℤ) (z : ℤ × ℤ) : Set ℂ :=
  Icc (b.re + s * ((c₀ + z.1 : ℤ) : ℝ)) (b.re + s * ((c₀ + z.1 : ℤ) : ℝ) + s) ×ℂ
    Icc (b.im + s * ((c₀ + z.2 : ℤ) : ℝ)) (b.im + s * ((c₀ + z.2 : ℤ) : ℝ) + s)

/-- `S(1/2)`: the square of side `2s` with the same centre -/
def annSqHalf (s : ℝ) (b : ℂ) (c₀ : ℤ) (z : ℤ × ℤ) : Set ℂ :=
  Icc (b.re + s * ((c₀ + z.1 : ℤ) : ℝ) - s / 2) (b.re + s * ((c₀ + z.1 : ℤ) : ℝ) + s + s / 2) ×ℂ
    Icc (b.im + s * ((c₀ + z.2 : ℤ) : ℝ) - s / 2) (b.im + s * ((c₀ + z.2 : ℤ) : ℝ) + s + s / 2)

/-- **condition 1 of DG's event `E_S^ε`** (DG:1642): `D^ε(S, ∂S(1/2)) ≥ M` -/
def goodAnn (μ : Measure ℂ) (ε s : ℝ) (b : ℂ) (c₀ : ℤ) (M : ℝ) (z : ℤ × ℤ) : Prop :=
  ENNReal.ofReal M ≤
    (dgLGDSet μ ε univ (annSq s b c₀ z) (frontier (annSqHalf s b c₀ z)) : ℝ≥0∞)

/-! ### Sites of points -/

lemma floor_div_bounds {s : ℝ} (hs : 0 < s) (x : ℝ) :
    s * (⌊x / s⌋ : ℝ) ≤ x ∧ x ≤ s * (⌊x / s⌋ : ℝ) + s := by
  have h1 := Int.floor_le (x / s)
  have h2 := Int.lt_floor_add_one (x / s)
  have e : s * (x / s) = x := mul_div_cancel₀ x hs.ne'
  constructor
  · calc s * (⌊x / s⌋ : ℝ) ≤ s * (x / s) := mul_le_mul_of_nonneg_left h1 hs.le
      _ = x := e
  · calc x = s * (x / s) := e.symm
      _ ≤ s * ((⌊x / s⌋ : ℝ) + 1) := mul_le_mul_of_nonneg_left h2.le hs.le
      _ = _ := by ring

lemma mem_annSq_annSite {s : ℝ} (hs : 0 < s) (b : ℂ) (c₀ : ℤ) (v : ℂ) :
    v ∈ annSq s b c₀ (annSite s b c₀ v) := by
  obtain ⟨a1, a2⟩ := floor_div_bounds hs (v.re - b.re)
  obtain ⟨b1, b2⟩ := floor_div_bounds hs (v.im - b.im)
  simp only [annSq, annSite, add_sub_cancel, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma floor_div_step {s x y : ℝ} (hs : 0 < s) (h : |x - y| < s) : ⌊x / s⌋ ≤ ⌊y / s⌋ + 1 := by
  have h1 : (x - y) / s < 1 := (div_lt_one hs).2 (lt_of_le_of_lt (le_abs_self _) h)
  have h2 : x / s ≤ y / s + 1 := by rw [sub_div] at h1; linarith
  have := Int.floor_mono h2
  rwa [Int.floor_add_one] at this

/-- points at distance `< s` lie in equal or `*`-adjacent sites -/
lemma annSite_step {s : ℝ} (hs : 0 < s) (b : ℂ) (c₀ : ℤ) {u v : ℂ} (huv : ‖u - v‖ < s) :
    annSite s b c₀ u = annSite s b c₀ v ∨ PercAdjK (annSite s b c₀ u) (annSite s b c₀ v) := by
  have are : |u.re - v.re| ≤ ‖u - v‖ := by simpa using Complex.abs_re_le_norm (u - v)
  have aim : |u.im - v.im| ≤ ‖u - v‖ := by simpa using Complex.abs_im_le_norm (u - v)
  have hre : |(u.re - b.re) - (v.re - b.re)| < s := by
    rw [sub_sub_sub_cancel_right]; exact are.trans_lt huv
  have him : |(u.im - b.im) - (v.im - b.im)| < s := by
    rw [sub_sub_sub_cancel_right]; exact aim.trans_lt huv
  have hre' : |(v.re - b.re) - (u.re - b.re)| < s := by rwa [abs_sub_comm]
  have him' : |(v.im - b.im) - (u.im - b.im)| < s := by rwa [abs_sub_comm]
  have r1 := floor_div_step hs hre
  have r2 := floor_div_step hs hre'
  have i1 := floor_div_step hs him
  have i2 := floor_div_step hs him'
  by_cases he : annSite s b c₀ u = annSite s b c₀ v
  · exact Or.inl he
  · right
    simp only [annSite, Prod.ext_iff, not_and_or] at he ⊢
    refine ⟨he, by omega, by omega, by omega, by omega⟩

/-- A continuous path visits a `*`-chain of sites (whole-plane version of DZZ's
`exists_path_sites`, Papers/DZZ/S3L7FinPath). -/
theorem exists_path_annSites {s : ℝ} (hs : 0 < s) (b : ℂ) (c₀ : ℤ) {z w : ℂ} (p : Path z w) :
    ∃ Γ : Set (ℤ × ℤ), (∀ x ∈ Γ, ∃ t, x = annSite s b c₀ (p t)) ∧
      Relation.ReflTransGen (PercStepIn Γ PercAdjK) (annSite s b c₀ z) (annSite s b c₀ w) := by
  have hu := CompactSpace.uniformContinuous_of_continuous p.continuous
  obtain ⟨δ, hδ, hδp⟩ := Metric.uniformContinuous_iff.1 hu s hs
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  set M := m + 1 with hMdef
  have hM : 1 / (M : ℝ) < δ := by rw [hMdef]; push_cast; exact hm
  set σ : ℕ → ℤ × ℤ := fun i => annSite s b c₀ (p (DZZ.ttM M i)) with hσ
  refine ⟨{x | ∃ i ≤ M, σ i = x}, fun x ⟨i, _, hi⟩ => ⟨DZZ.ttM M i, hi.symm⟩, ?_⟩
  have key : ∀ i ≤ M,
      Relation.ReflTransGen (PercStepIn {x | ∃ i ≤ M, σ i = x} PercAdjK) (σ 0) (σ i) := by
    intro i
    induction i with
    | zero => intro _; exact .refl
    | succ i ih =>
      intro hi
      have hd : dist (p (DZZ.ttM M i)) (p (DZZ.ttM M (i + 1))) < s :=
        hδp ((DZZ.dist_ttM M i).trans_lt hM)
      rw [dist_eq_norm] at hd
      rcases annSite_step hs b c₀ hd with h | h
      · have h' : σ i = σ (i + 1) := h
        rw [← h']
        exact ih (by omega)
      · exact (ih (by omega)).tail ⟨⟨i, by omega, rfl⟩, ⟨i + 1, hi, rfl⟩, h⟩
  have := key M le_rfl
  have e0 : σ 0 = annSite s b c₀ z := by simp only [σ, DZZ.ttM_zero, Path.source]
  have eM : σ M = annSite s b c₀ w := by
    simp only [σ]; rw [DZZ.ttM_self (show M ≠ 0 by omega), Path.target]
  rw [e0, eM] at this
  exact this

/-! ### The hole and the outside -/

lemma annSite_hole {s : ℝ} (hs : 0 < s) (b : ℂ) (n : ℕ) {v : ℂ} (hv : v ∈ annIn s b n) :
    -(((n / 2 : ℕ) : ℤ) + 2) < (annSite s b (n / 2 : ℕ) v).1 ∧
      (annSite s b (n / 2 : ℕ) v).1 < ((n / 2 : ℕ) : ℤ) + 2 ∧
      -(((n / 2 : ℕ) : ℤ) + 2) < (annSite s b (n / 2 : ℕ) v).2 ∧
      (annSite s b (n / 2 : ℕ) v).2 < ((n / 2 : ℕ) : ℤ) + 2 := by
  simp only [annIn, Complex.mem_reProdIm, mem_Icc] at hv
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hv
  have f : ∀ x : ℝ, 0 ≤ x → x ≤ s * n → 0 ≤ ⌊x / s⌋ ∧ ⌊x / s⌋ ≤ n := by
    intro x h0 h1
    refine ⟨Int.floor_nonneg.2 (div_nonneg h0 hs.le), ?_⟩
    have : x / s ≤ n := by rw [div_le_iff₀ hs]; linarith
    have := Int.floor_mono this
    rwa [Int.floor_natCast] at this
  obtain ⟨r1, r2⟩ := f (v.re - b.re) (by linarith) (by linarith)
  obtain ⟨i1, i2⟩ := f (v.im - b.im) (by linarith) (by linarith)
  have hn : (n : ℤ) ≤ 2 * ((n / 2 : ℕ) : ℤ) + 1 := by omega
  simp only [annSite]
  refine ⟨by omega, by omega, by omega, by omega⟩

lemma floor_div_eq_of_eq {s : ℝ} (hs : 0 < s) (k : ℤ) {x : ℝ} (hx : x = s * k) :
    ⌊x / s⌋ = k := by
  rw [hx, mul_div_cancel_left₀ _ hs.ne', Int.floor_intCast]

lemma annSite_out {s : ℝ} (hs : 0 < s) (b : ℂ) (n : ℕ) {v : ℂ} (hv : v ∈ frontier (annOut s b n)) :
    ¬ annBox ((n : ℤ) - 2 + ((n / 2 : ℕ) : ℤ)) (annSite s b (n / 2 : ℕ) v) := by
  have hle : b.re - s * n ≤ b.re + 2 * (s * n) := by
    have : 0 ≤ s * n := by positivity
    linarith
  have hle' : b.im - s * n ≤ b.im + 2 * (s * n) := by
    have : 0 ≤ s * n := by positivity
    linarith
  have h2 : 2 * ((n / 2 : ℕ) : ℤ) ≤ n := by omega
  simp only [annOut, Complex.frontier_reProdIm, frontier_Icc hle, frontier_Icc hle', closure_Icc,
    mem_union, Complex.mem_reProdIm, mem_insert_iff, mem_singleton_iff] at hv
  simp only [annBox, annSite, not_and_or, not_le]
  rcases hv with ⟨-, h | h⟩ | ⟨h | h, -⟩
  · have := floor_div_eq_of_eq hs (-(n : ℤ)) (x := v.im - b.im) (by rw [h]; push_cast; ring)
    omega
  · have := floor_div_eq_of_eq hs (2 * (n : ℤ)) (x := v.im - b.im) (by rw [h]; push_cast; ring)
    omega
  · have := floor_div_eq_of_eq hs (-(n : ℤ)) (x := v.re - b.re) (by rw [h]; push_cast; ring)
    omega
  · have := floor_div_eq_of_eq hs (2 * (n : ℤ)) (x := v.re - b.re) (by rw [h]; push_cast; ring)
    omega

/-- the squares `S(1/2)` of the sites of `annBox (n − 2 + c₀)` lie in the interior of the outer
square (DG:1651: "`S(1/2) ⊂ 𝒜_n`") -/
lemma annSqHalf_subset_interior {s : ℝ} (hs : 0 < s) (b : ℂ) (n : ℕ) {z : ℤ × ℤ}
    (hz : annBox ((n : ℤ) - 2 + ((n / 2 : ℕ) : ℤ)) z) :
    annSqHalf s b (n / 2 : ℕ) z ⊆ interior (annOut s b n) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have h2' : 2 * ((n / 2 : ℕ) : ℤ) ≤ n := by omega
  have k1 : (2 : ℝ) ≤ (((n / 2 : ℕ) + z.1 : ℤ) : ℝ) + n := by
    have : (2 : ℤ) ≤ ((n / 2 : ℕ) + z.1 : ℤ) + n := by omega
    exact_mod_cast this
  have k2 : (((n / 2 : ℕ) + z.1 : ℤ) : ℝ) + 2 ≤ 2 * n := by
    have : ((n / 2 : ℕ) + z.1 : ℤ) + 2 ≤ 2 * n := by omega
    exact_mod_cast this
  have k3 : (2 : ℝ) ≤ (((n / 2 : ℕ) + z.2 : ℤ) : ℝ) + n := by
    have : (2 : ℤ) ≤ ((n / 2 : ℕ) + z.2 : ℤ) + n := by omega
    exact_mod_cast this
  have k4 : (((n / 2 : ℕ) + z.2 : ℤ) : ℝ) + 2 ≤ 2 * n := by
    have : ((n / 2 : ℕ) + z.2 : ℤ) + 2 ≤ 2 * n := by omega
    exact_mod_cast this
  intro v hv
  rw [annOut, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  simp only [annSqHalf, Complex.mem_reProdIm, mem_Icc] at hv
  simp only [Complex.mem_reProdIm, mem_Ioo]
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hv
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left k1 hs.le]
  · nlinarith [mul_le_mul_of_nonneg_left k2 hs.le]
  · nlinarith [mul_le_mul_of_nonneg_left k3 hs.le]
  · nlinarith [mul_le_mul_of_nonneg_left k4 hs.le]

lemma annSq_subset_interior_half {s : ℝ} (hs : 0 < s) (b : ℂ) (c₀ : ℤ) (z : ℤ × ℤ) :
    annSq s b c₀ z ⊆ interior (annSqHalf s b c₀ z) := by
  intro v hv
  rw [annSqHalf, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  simp only [annSq, Complex.mem_reProdIm, mem_Icc] at hv
  simp only [Complex.mem_reProdIm, mem_Ioo]
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hv
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma isClosed_annSq (s : ℝ) (b : ℂ) (c₀ : ℤ) (z : ℤ × ℤ) : IsClosed (annSq s b c₀ z) :=
  isClosed_Icc.reProdIm isClosed_Icc

/-! ### Crossing a square annulus -/

/-- the reparametrized piece `r ↦ P(t₀ + r (t₁ − t₀))` of a path -/
def subPathE {z w : ℂ} (P : Path z w) (t₀ t₁ : ℝ) : Path (P.extend t₀) (P.extend t₁) where
  toFun r := P.extend (t₀ + r * (t₁ - t₀))
  continuous_toFun := P.continuous_extend.comp (by fun_prop)
  source' := by simp
  target' := by simp

lemma range_subPathE {z w : ℂ} (P : Path z w) (t₀ t₁ : ℝ) :
    range (subPathE P t₀ t₁) ⊆ range P := by
  rintro _ ⟨r, rfl⟩
  rw [← Path.extend_range]
  exact ⟨_, rfl⟩

/-- a path covered by `N` balls of mass `≤ ε`, from a point of `S` to a point outside
`int S(1/2)`, gives `D^ε(S, ∂S(1/2)) ≤ N` (DG:1651–1652) -/
lemma dgLGDSet_half_le {μ : Measure ℂ} {ε : ℝ} {S T : Set ℂ} (hS : IsClosed S)
    (hST : S ⊆ interior T) {z w : ℂ} (P : Path z w) {N : ℕ} {x : Fin N → ℂ} {ρ : Fin N → ℝ}
    (hb : ∀ i, 0 < ρ i ∧ Metric.ball (x i) (ρ i) ⊆ closure (univ : Set ℂ) ∧
      μ (Metric.ball (x i) (ρ i)) ≤ ENNReal.ofReal ε)
    (hc : ∀ t, ∃ i, P t ∈ Metric.ball (x i) (ρ i)) {t : ℝ} (ht : P.extend t ∈ S)
    (hw : w ∉ interior T) : dgLGDSet μ ε univ S (frontier T) ≤ N := by
  set Q := subPathE P t 1
  have hw' : P.extend 1 ∉ interior T := by rwa [Path.extend_one]
  obtain ⟨t₀, t₁, -, -, -, h0, h1, -⟩ :=
    exists_cross_subpath Q hS isOpen_interior hST ht hw'
  have hR : LGDWit μ ε univ (Q.extend t₀) (Q.extend t₁) N := by
    refine ⟨x, ρ, subPathE Q t₀ t₁, hb, fun r => ?_⟩
    have h1 : (subPathE Q t₀ t₁) r ∈ range P :=
      range_subPathE P t 1 (range_subPathE Q t₀ t₁ ⟨r, rfl⟩)
    obtain ⟨t', ht'⟩ := h1
    obtain ⟨i, hi⟩ := hc t'
    exact ⟨i, ht' ▸ hi⟩
  have hA : Q.extend t₀ ∈ S := by
    have := frontier_subset_closure h0
    rwa [hS.closure_eq] at this
  have hB : Q.extend t₁ ∈ frontier T := frontier_interior_subset h1
  exact (dgLGDSet_le hA hB).trans (dgLGD_le_of_wit hR)

/-- **DG:1650–1652**: a good enclosure of the annulus `c₀ + 2 ≤ ‖z‖_∞ ≤ n − 2 + c₀`
(`c₀ = ⌊n/2⌋`) gives `D^ε(∂_in, ∂_out) ≥ M` for the annulus `s𝒜_n + b` (unrestricted
distance, as in DG). -/
theorem dgLGDSet_ann_ge_of_enc {μ : Measure ℂ} {ε s M : ℝ} (hs : 0 < s) (b : ℂ) (n : ℕ)
    {G : Set (ℤ × ℤ)} (hG : ∀ z ∈ G, goodAnn μ ε s b (n / 2 : ℕ) M z)
    (henc : PercEnclosure (((n / 2 : ℕ) : ℤ) + 2) ((n : ℤ) - 2 + ((n / 2 : ℕ) : ℤ)) G) :
    ENNReal.ofReal M ≤ (dgLGDSet μ ε univ (annIn s b n) (frontier (annOut s b n)) : ℝ≥0∞) := by
  obtain ⟨U, hU, -, -, hsep⟩ := henc
  unfold dgLGDSet
  simp only [ENat.toENNReal_iInf]
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
  unfold dgLGD
  simp only [ENat.toENNReal_iInf]
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, hb, hc⟩ := hN
  obtain ⟨Γ, hΓ, hch⟩ := exists_path_annSites hs b (n / 2 : ℕ) P
  obtain ⟨z₀, hz₀U, hz₀Γ⟩ := hsep Γ _ _ (annSite_hole hs b n hz) (annSite_out hs b n hw) hch
  obtain ⟨hz₀G, d, hz₀d⟩ := hU z₀ hz₀U
  obtain ⟨t, rfl⟩ := hΓ z₀ hz₀Γ
  have hbox : annBox ((n : ℤ) - 2 + ((n / 2 : ℕ) : ℤ)) (annSite s b (n / 2 : ℕ) (P t)) :=
    hz₀d.1
  have hwT : w ∉ interior (annSqHalf s b (n / 2 : ℕ) (annSite s b (n / 2 : ℕ) (P t))) := by
    intro hwi
    have h1 := annSqHalf_subset_interior hs b n hbox (interior_subset hwi)
    exact hw.2 h1
  have hPt : P.extend t ∈ annSq s b (n / 2 : ℕ) (annSite s b (n / 2 : ℕ) (P t)) := by
    rw [Path.extend_extends']; exact mem_annSq_annSite hs b _ _
  have hle := dgLGDSet_half_le (isClosed_annSq s b _ _) (annSq_subset_interior_half hs b _ _)
    P hb hc hPt hwT
  exact (hG _ hz₀G).trans (by exact_mod_cast hle)

end DG
end LQGMetric
