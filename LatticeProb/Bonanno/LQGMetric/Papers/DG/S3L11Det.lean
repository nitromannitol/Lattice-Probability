/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L2
import LatticeProb.Bonanno.LQGMetric.Perc.Basic
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# DG Lemma 3.11, deterministic part: a good crossing of squares bounds the LGD (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.11
(`lem-rectangle-perc`, DG:1189–1278), at an arbitrary scale `s > 0` and offset `b` (D105 item 1:
DG's unit rectangles `ℛ_n` become `s ℛ_n + b`, DV-D105-3):

* the squares `𝒮(ℛ_n)` are the unit squares of `[0,2n] × [1,n−1]` with corners in `ℤ²`
  (DG:1236, footnote); the site `x ∈ [0,2n) × [0,n−2)` of `Perc.Basic` is the square with lower
  left corner `b + s (x.1, x.2 + 1)` (`sqX`, `sqY`); `sqOne` is its expansion `S(1)` (side `3s`);
  `sqMids` are the midpoints of its four sides (DG:1206, DEC-105 N9);
* `goodSq` is DG's event `E_S^ε` (DG:1240): `D^ε(u_S^i, u_S^j; S(1)) ≤ M` for all `i, j`;
* `dgLGDSet μ ε U A B = inf_{z ∈ A, w ∈ B} D^ε(z, w; U)` (DG's set-to-set distance);
* `dgLGDSet_rect_le_of_goodLR`: DG:1256–1259, "the definition of `E_S^ε` and the triangle
  inequality show that if a path as in the claim exists then the distance between the left and
  right boundaries of `ℛ_n` along paths of disks contained in `ℛ_n'` is at most `2n² M`".
  The triangle inequality is `LGDWit.trans` (concatenation of ball collections and paths).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-! ### Witnesses of `dgLGD` and the triangle inequality -/

/-- a collection of `N` balls of mass `≤ ε` in `Ū` covering a path from `z` to `w` -/
def LGDWit (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (z w : ℂ) (N : ℕ) : Prop :=
  ∃ (x : Fin N → ℂ) (ρ : Fin N → ℝ) (P : Path z w),
    (∀ i, 0 < ρ i ∧ Metric.ball (x i) (ρ i) ⊆ closure U ∧
      μ (Metric.ball (x i) (ρ i)) ≤ ENNReal.ofReal ε) ∧
    ∀ t, ∃ i, P t ∈ Metric.ball (x i) (ρ i)

variable {μ : Measure ℂ} {ε : ℝ} {U : Set ℂ}

lemma dgLGD_le_of_wit {z w : ℂ} {N : ℕ} (h : LGDWit μ ε U z w N) : dgLGD μ ε U z w ≤ N :=
  iInf₂_le N h

lemma exists_wit_of_dgLGD_ne_top {z w : ℂ} (h : dgLGD μ ε U z w ≠ ⊤) :
    ∃ N, LGDWit μ ε U z w N ∧ dgLGD μ ε U z w = N := by
  classical
  have hex : ∃ N, LGDWit μ ε U z w N := by
    by_contra hne
    push Not at hne
    apply h
    unfold dgLGD
    exact iInf₂_eq_top.2 fun N hN => absurd hN (hne N)
  refine ⟨Nat.find hex, Nat.find_spec hex,
    le_antisymm (dgLGD_le_of_wit (Nat.find_spec hex)) ?_⟩
  unfold dgLGD
  exact le_iInf₂ fun N hN => by exact_mod_cast Nat.find_min' hex hN

lemma exists_wit_of_le {z w : ℂ} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : (dgLGD μ ε U z w : ℝ≥0∞) ≤ M) : ∃ N : ℕ, LGDWit μ ε U z w N ∧ (N : ℝ≥0∞) ≤ M := by
  have hne : dgLGD μ ε U z w ≠ ⊤ := by
    intro e
    rw [e, ENat.toENNReal_top] at h
    exact hM (top_le_iff.1 h)
  obtain ⟨N, hw, e⟩ := exists_wit_of_dgLGD_ne_top hne
  refine ⟨N, hw, ?_⟩
  rw [e, ENat.toENNReal_coe] at h
  exact h

/-- **triangle inequality** for witnesses: concatenate the paths and the ball collections -/
lemma LGDWit.trans {z x w : ℂ} {N₁ N₂ : ℕ} (h₁ : LGDWit μ ε U z x N₁)
    (h₂ : LGDWit μ ε U x w N₂) : LGDWit μ ε U z w (N₁ + N₂) := by
  obtain ⟨x₁, ρ₁, P₁, hb₁, hc₁⟩ := h₁
  obtain ⟨x₂, ρ₂, P₂, hb₂, hc₂⟩ := h₂
  refine ⟨Fin.append x₁ x₂, Fin.append ρ₁ ρ₂, P₁.trans P₂, fun i => ?_, fun t => ?_⟩
  · induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using hb₁ i
    | right i => simpa only [Fin.append_right] using hb₂ i
  · have ht : (P₁.trans P₂) t ∈ Set.range (P₁.trans P₂) := ⟨t, rfl⟩
    rw [Path.trans_range] at ht
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · obtain ⟨i, hi⟩ := hc₁ s
      exact ⟨Fin.castAdd N₂ i, by rw [Fin.append_left, Fin.append_left, ← hs]; exact hi⟩
    · obtain ⟨i, hi⟩ := hc₂ s
      exact ⟨Fin.natAdd N₁ i, by rw [Fin.append_right, Fin.append_right, ← hs]; exact hi⟩

lemma LGDWit.mono {U' : Set ℂ} (hU : closure U ⊆ closure U') {z w : ℂ} {N : ℕ}
    (h : LGDWit μ ε U z w N) : LGDWit μ ε U' z w N := by
  obtain ⟨x, ρ, P, hb, hc⟩ := h
  exact ⟨x, ρ, P, fun i => ⟨(hb i).1, (hb i).2.1.trans hU, (hb i).2.2⟩, hc⟩

/-- DG's set-to-set Liouville graph distance `D^ε(A, B; U)` -/
def dgLGDSet (μ : Measure ℂ) (ε : ℝ) (U A B : Set ℂ) : ℕ∞ :=
  ⨅ z ∈ A, ⨅ w ∈ B, dgLGD μ ε U z w

lemma dgLGDSet_le {A B : Set ℂ} {z w : ℂ} (hz : z ∈ A) (hw : w ∈ B) :
    dgLGDSet μ ε U A B ≤ dgLGD μ ε U z w :=
  (iInf₂_le z hz).trans (iInf₂_le w hw)

/-! ### Squares, rectangles -/

/-- abscissa of the lower left corner of the square of site `x` -/
def sqX (s : ℝ) (b : ℂ) (x : ℤ × ℤ) : ℝ := b.re + s * x.1

/-- ordinate of the lower left corner of the square of site `x` (row offset `1`, DG:1236) -/
def sqY (s : ℝ) (b : ℂ) (x : ℤ × ℤ) : ℝ := b.im + s * (x.2 + 1)

/-- the expanded square `S(1)` (side `3s`, same centre) -/
def sqOne (s : ℝ) (b : ℂ) (x : ℤ × ℤ) : Set ℂ :=
  Icc (sqX s b x - s) (sqX s b x + 2 * s) ×ℂ Icc (sqY s b x - s) (sqY s b x + 2 * s)

/-- the midpoints of the four sides of the square of site `x` (left, right, bottom, top) -/
def sqMids (s : ℝ) (b : ℂ) (x : ℤ × ℤ) : Set ℂ :=
  {⟨sqX s b x, sqY s b x + s / 2⟩, ⟨sqX s b x + s, sqY s b x + s / 2⟩,
    ⟨sqX s b x + s / 2, sqY s b x⟩, ⟨sqX s b x + s / 2, sqY s b x + s⟩}

/-- DG's stretched rectangle `ℛ_n' = [−n, 3n] × [0, n]`, scaled by `s` and moved by `b` -/
def rectStretch (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  Icc (b.re - s * n) (b.re + 3 * s * n) ×ℂ Icc b.im (b.im + s * n)

/-- the left side `∂_L ℛ_n` of `ℛ_n = [0,2n] × [0,n]`, scaled -/
def rectLeft (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  {z | z.re = b.re ∧ b.im ≤ z.im ∧ z.im ≤ b.im + s * n}

/-- the right side `∂_R ℛ_n`, scaled -/
def rectRight (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  {z | z.re = b.re + 2 * s * n ∧ b.im ≤ z.im ∧ z.im ≤ b.im + s * n}

/-- **DG's event `E_S^ε`** (DG:1240): `D^ε(u_S^i, u_S^j; S(1)) ≤ M` between the side midpoints -/
def goodSq (μ : Measure ℂ) (ε s : ℝ) (b : ℂ) (M : ℝ) (x : ℤ × ℤ) : Prop :=
  ∀ u ∈ sqMids s b x, ∀ v ∈ sqMids s b x,
    (dgLGD μ ε (sqOne s b x) u v : ℝ≥0∞) ≤ ENNReal.ofReal M

lemma isClosed_sqOne (s : ℝ) (b : ℂ) (x : ℤ × ℤ) : IsClosed (sqOne s b x) :=
  isClosed_Icc.reProdIm isClosed_Icc

/-- `4`-adjacent squares share a side midpoint -/
lemma exists_common_mid {s : ℝ} {b : ℂ} {x y : ℤ × ℤ} (h : PercAdj4 x y) :
    ∃ m ∈ sqMids s b x, m ∈ sqMids s b y := by
  simp only [sqMids, sqX, sqY, mem_insert_iff, mem_singleton_iff]
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · refine ⟨_, Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr (Complex.ext ?_ ?_)))⟩ <;>
      (simp only [h1, h2]; try (push_cast; ring))
  · refine ⟨_, Or.inr (Or.inr (Or.inr rfl)), Or.inr (Or.inr (Or.inl (Complex.ext ?_ ?_)))⟩ <;>
      (simp only [h1, h2]; try (push_cast; ring))
  · refine ⟨_, Or.inl rfl, Or.inr (Or.inl (Complex.ext ?_ ?_))⟩ <;>
      (simp only [h1, h2]; try (push_cast; ring))
  · refine ⟨_, Or.inr (Or.inl rfl), Or.inl (Complex.ext ?_ ?_)⟩ <;>
      (simp only [h1, h2]; try (push_cast; ring))

/-- the expanded squares of the sites of `[0,2n) × [0,n−2)` lie in `ℛ_n'` (DG:1236, footnote) -/
lemma sqOne_subset_rectStretch {s : ℝ} (hs : 0 < s) (b : ℂ) {n : ℕ} {x : ℤ × ℤ}
    (hx : percInGrid (2 * (n : ℤ)) ((n : ℤ) - 2) x) : sqOne s b x ⊆ rectStretch s b n := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have e1 : (-(n : ℝ)) ≤ (x.1 : ℝ) - 1 := by
    have : (-(n : ℤ)) ≤ x.1 - 1 := by omega
    exact_mod_cast this
  have e2 : (x.1 : ℝ) + 2 ≤ 3 * n := by
    have : x.1 + 2 ≤ 3 * (n : ℤ) := by omega
    exact_mod_cast this
  have e3 : (0 : ℝ) ≤ x.2 := by exact_mod_cast h3
  have e4 : (x.2 : ℝ) + 3 ≤ n := by
    have : x.2 + 3 ≤ (n : ℤ) := by omega
    exact_mod_cast this
  intro z hz
  simp only [sqOne, sqX, sqY, Complex.mem_reProdIm, mem_Icc] at hz
  simp only [rectStretch, Complex.mem_reProdIm, mem_Icc]
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hz
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left e1 hs.le]
  · nlinarith [mul_le_mul_of_nonneg_left e2 hs.le]
  · nlinarith [mul_le_mul_of_nonneg_left e3 hs.le]
  · nlinarith [mul_le_mul_of_nonneg_left e4 hs.le]

/-! ### The chain argument -/

lemma wit_of_goodSq {s M : ℝ} {b : ℂ} {x : ℤ × ℤ} (hg : goodSq μ ε s b M x) {u v : ℂ}
    (hu : u ∈ sqMids s b x) (hv : v ∈ sqMids s b x) :
    ∃ N : ℕ, LGDWit μ ε (sqOne s b x) u v N ∧ (N : ℝ≥0∞) ≤ ENNReal.ofReal M :=
  exists_wit_of_le ENNReal.ofReal_ne_top (hg u hu v hv)

/-- the graph of `4`-adjacent good sites -/
def goodGraph (K L : ℤ) (good : ℤ × ℤ → Prop) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromRel (PercGoodStep K L good)

lemma goodGraph_adj {K L : ℤ} {good : ℤ × ℤ → Prop} {x y : ℤ × ℤ}
    (h : (goodGraph K L good).Adj x y) : PercGoodStep K L good x y := by
  obtain ⟨-, h | h⟩ := h
  · exact h
  · obtain ⟨a, b, c, d, e⟩ := h
    refine ⟨c, d, a, b, ?_⟩
    rcases e with ⟨e1, e2 | e2⟩ | ⟨e1, e2 | e2⟩
    · exact Or.inl ⟨e1.symm, Or.inr e2⟩
    · exact Or.inl ⟨e1.symm, Or.inl e2⟩
    · exact Or.inr ⟨e1.symm, Or.inr e2⟩
    · exact Or.inr ⟨e1.symm, Or.inl e2⟩

/-- along a walk of good squares, consecutive midpoints are joined inside `U ⊇ ⋃ S(1)` with
`≤ (length + 1) M` balls (DG:1256–1258) -/
theorem wit_of_walk {s M : ℝ} {b : ℂ} {K L : ℤ}
    (hsub : ∀ x, percInGrid K L x → sqOne s b x ⊆ closure U) {a c : ℤ × ℤ}
    (q : (goodGraph K L (goodSq μ ε s b M)).Walk a c) (ha : percInGrid K L a)
    (hga : goodSq μ ε s b M a) :
    ∀ u ∈ sqMids s b a, ∀ v ∈ sqMids s b c,
      ∃ N : ℕ, LGDWit μ ε U u v N ∧ (N : ℝ≥0∞) ≤ (q.length + 1) * ENNReal.ofReal M := by
  have hcl : ∀ x, percInGrid K L x → closure (sqOne s b x) ⊆ closure U := fun x hx => by
    rw [(isClosed_sqOne s b x).closure_eq]; exact hsub x hx
  induction q with
  | nil =>
    intro u hu v hv
    obtain ⟨N, hw, hN⟩ := wit_of_goodSq hga hu hv
    exact ⟨N, hw.mono (hcl _ ha), by simpa using hN⟩
  | @cons a a' c h q ih =>
    intro u hu v hv
    have hst := goodGraph_adj h
    obtain ⟨m, hma, hma'⟩ := exists_common_mid (s := s) (b := b) hst.2.2.2.2
    obtain ⟨N₁, hw₁, hN₁⟩ := wit_of_goodSq hga hu hma
    obtain ⟨N₂, hw₂, hN₂⟩ := ih hst.2.2.1 hst.2.2.2.1 m hma' v hv
    refine ⟨N₁ + N₂, (hw₁.mono (hcl _ ha)).trans hw₂, ?_⟩
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    calc (N₁ : ℝ≥0∞) + N₂ ≤ ENNReal.ofReal M + (q.length + 1) * ENNReal.ofReal M :=
          add_le_add hN₁ hN₂
      _ = (q.length + 1 + 1) * ENNReal.ofReal M := by ring

lemma goodGraph_walk_mem {K L : ℤ} {good : ℤ × ℤ → Prop} {u v : ℤ × ℤ}
    (q : (goodGraph K L good).Walk u v) (hu : percInGrid K L u) :
    ∀ y ∈ q.support, percInGrid K L y := by
  induction q with
  | nil => intro y hy; simp at hy; exact hy ▸ hu
  | @cons a b c h q ih =>
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hu
    · exact ih (goodGraph_adj h).2.2.1 y hy

/-- **DG:1256–1259**: a left–right crossing of `[0,2n) × [0,n−2)` by `4`-connected good squares
gives `D^ε(∂_L ℛ_n, ∂_R ℛ_n; ℛ_n') ≤ 2n² M` (scaled by `s`, moved by `b`). -/
theorem dgLGDSet_rect_le_of_goodLR {s M : ℝ} (hs : 0 < s) (b : ℂ) {n : ℕ}
    (h : PercGoodLR (2 * (n : ℤ)) ((n : ℤ) - 2) (goodSq μ ε s b M)) :
    (dgLGDSet μ ε (rectStretch s b n) (rectLeft s b n) (rectRight s b n) : ℝ≥0∞) ≤
      (2 * n ^ 2 : ℝ≥0∞) * ENNReal.ofReal M := by
  classical
  obtain ⟨a, c, ha1, hc1, hagrid, hga, hac⟩ := h
  set G := goodGraph (2 * (n : ℤ)) ((n : ℤ) - 2) (goodSq μ ε s b M)
  have hr : G.Reachable a c := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    clear hc1
    induction hac with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y _ hxy ih =>
      by_cases e : x = y
      · rw [← e]; exact ih
      · exact ih.tail ⟨e, Or.inl hxy⟩
  obtain ⟨p⟩ := hr
  set q := p.bypass
  have hcgrid : percInGrid (2 * (n : ℤ)) ((n : ℤ) - 2) c :=
    goodGraph_walk_mem q hagrid c q.end_mem_support
  obtain ⟨-, -, hc3, hc4⟩ := id hcgrid
  obtain ⟨-, -, ha3, ha4⟩ := id hagrid
  -- the endpoints
  set u : ℂ := ⟨sqX s b a, sqY s b a + s / 2⟩
  set v : ℂ := ⟨sqX s b c + s, sqY s b c + s / 2⟩
  have hu : u ∈ sqMids s b a := by simp [sqMids, u]
  have hv : v ∈ sqMids s b c := by simp [sqMids, v]
  have hsub : ∀ x, percInGrid (2 * (n : ℤ)) ((n : ℤ) - 2) x →
      sqOne s b x ⊆ closure (rectStretch s b n) :=
    fun x hx => (sqOne_subset_rectStretch hs b hx).trans subset_closure
  obtain ⟨N, hw, hN⟩ := wit_of_walk hsub q hagrid hga u hu v hv
  -- the endpoints lie on the sides
  have ea3 : (0 : ℝ) ≤ a.2 := by exact_mod_cast ha3
  have ea4 : (a.2 : ℝ) + 3 ≤ n := by
    have : a.2 + 3 ≤ (n : ℤ) := by omega
    exact_mod_cast this
  have ec3 : (0 : ℝ) ≤ c.2 := by exact_mod_cast hc3
  have ec4 : (c.2 : ℝ) + 3 ≤ n := by
    have : c.2 + 3 ≤ (n : ℤ) := by omega
    exact_mod_cast this
  have hul : u ∈ rectLeft s b n := by
    simp only [rectLeft, mem_ofPred_eq, u, sqX, sqY, ha1]
    refine ⟨by simp, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left ea3 hs.le]
    · nlinarith [mul_le_mul_of_nonneg_left ea4 hs.le]
  have hvr : v ∈ rectRight s b n := by
    simp only [rectRight, mem_ofPred_eq, v, sqX, sqY, hc1]
    refine ⟨by push_cast; ring, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left ec3 hs.le]
    · nlinarith [mul_le_mul_of_nonneg_left ec4 hs.le]
  -- the length of a simple path is at most the number of sites
  have hlen : (q.length + 1 : ℝ≥0∞) ≤ 2 * n ^ 2 := by
    have hnd := (p.bypass_isPath).support_nodup
    have hs' : q.support.toFinset ⊆
        Finset.Ico (0 : ℤ) (2 * n) ×ˢ Finset.Ico (0 : ℤ) ((n : ℤ) - 2) := by
      intro y hy
      have := goodGraph_walk_mem q ⟨by omega, by omega, ha3, ha4⟩ y (List.mem_toFinset.mp hy)
      simp only [percInGrid] at this
      simp only [Finset.mem_product, Finset.mem_Ico]
      omega
    have hc := Finset.card_le_card hs'
    rw [List.toFinset_card_of_nodup hnd, Finset.card_product, Int.card_Ico, Int.card_Ico,
      SimpleGraph.Walk.length_support] at hc
    have hnat : q.length + 1 ≤ 2 * n ^ 2 := by
      have h1 : (2 * (n : ℤ) - 0).toNat = 2 * n := by omega
      have h2 : ((n : ℤ) - 2 - 0).toNat ≤ n := by omega
      rw [h1] at hc
      nlinarith [Nat.mul_le_mul_left (2 * n) h2]
    exact_mod_cast hnat
  calc (dgLGDSet μ ε (rectStretch s b n) (rectLeft s b n) (rectRight s b n) : ℝ≥0∞)
      ≤ (dgLGD μ ε (rectStretch s b n) u v : ℝ≥0∞) :=
        ENat.toENNReal_le.2 (dgLGDSet_le hul hvr)
    _ ≤ N := by
        have := dgLGD_le_of_wit hw
        exact (ENat.toENNReal_le.2 this).trans_eq (ENat.toENNReal_coe N)
    _ ≤ (q.length + 1) * ENNReal.ofReal M := hN
    _ ≤ (2 * n ^ 2 : ℝ≥0∞) * ENNReal.ofReal M := by gcongr

end DG
end LQGMetric
