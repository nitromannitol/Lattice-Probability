/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T1_5Disc at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Defs
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*
(arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Theorem 1.5, Step 3
(T:1693–1716): a path `P` crossing `𝕣𝕊` from left to right is turned into a path `π` of the
graph `(𝕣𝕊) ∩ (δ𝕣ℤ²)` from `∂^{δ𝕣}_L` to `∂^{δ𝕣}_R` by following the cells `S_{z_j}` visited at
the successive exit times `τ_j` of `P` from neighbourhoods of `S_{z_{j-1}}`; each step costs a
crossing of an annulus around `z_{j-1}`, whence `Σ_j a(π(j)) ≤ len(P)` if `a(z)` lower-bounds the
distance across the annulus around `z` ((eqn-square-across), T:1667–1670).

Implementation choices (recorded in the report as proposed DEVIATIONS entries):
* the neighbourhood of `S_z` is the sup-norm box of half-side `3s/2` (`s = δ𝕣`), and the next
  vertex is `P(τ_j)` rounded towards `z_{j-1}`, so successive vertices are `8`-neighbours (the
  paper's Euclidean `B_{δ𝕣}(S_z)` makes the rounding ambiguous on the boundary);
* the annulus crossed is the Euclidean one `B̄_{3s/4}(z) → ∂B_{3s/2}(z)` inside `B_{2s}(z)`
  (it lies inside the box, so the crossing still happens before `τ_j`);
* the path `P` is required to run from the line `Re = s` (the leftmost column) to `Re ≥ 𝕣 + 2s`
  inside the strip `s ≤ Re`, `s ≤ Im ≤ 𝕣 - s`; then every vertex, including the last one, is
  followed by a full annulus crossing (the paper's sum `Σ_{j=0}^J` has one more term than
  crossings, T:1712–1714).
-/

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

/-- the sup norm `max(|Re u|, |Im u|)` -/
def supN (u : ℂ) : ℝ := max |u.re| |u.im|

lemma continuous_supN : Continuous supN :=
  (Complex.continuous_re.abs).max (Complex.continuous_im.abs)

lemma supN_le_norm (u : ℂ) : supN u ≤ ‖u‖ :=
  max_le (Complex.abs_re_le_norm u) (Complex.abs_im_le_norm u)

lemma supN_add_le (u v : ℂ) : supN (u + v) ≤ supN u + supN v := by
  unfold supN
  refine max_le ?_ ?_
  · rw [Complex.add_re]
    exact (abs_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · rw [Complex.add_im]
    exact (abs_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- rounding of an offset in `[-3/2, 3/2]` (in grid units) towards `0` -/
def rnd1 (o : ℝ) : ℤ := if 1 / 2 < o then 1 else if o < -1 / 2 then -1 else 0

lemma abs_sub_rnd1 {o : ℝ} (h : |o| ≤ 3 / 2) : |o - rnd1 o| ≤ 1 / 2 := by
  rw [abs_le] at h
  unfold rnd1
  split_ifs with h1 h2
  · rw [abs_le]; push_cast; constructor <;> linarith
  · rw [abs_le]; push_cast; constructor <;> linarith
  · rw [abs_le]; push_cast; constructor <;> linarith

lemma rnd1_sq_le (o : ℝ) : ((rnd1 o : ℝ)) ^ 2 = 0 ∨ ((rnd1 o : ℝ)) ^ 2 = 1 := by
  unfold rnd1; split_ifs <;> norm_num

lemma rnd1_sq_of_eq {o : ℝ} (h : |o| = 3 / 2) : ((rnd1 o : ℝ)) ^ 2 = 1 := by
  unfold rnd1
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 3 / 2) |>.1 h with h | h <;> split_ifs <;> norm_num <;>
    linarith

/-- membership in `𝕣𝕊` -/
lemma mem_rS_iff {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) {z : ℂ} :
    z ∈ rS 𝕣 ↔ 0 < z.re ∧ z.re < 𝕣 ∧ 0 < z.im ∧ z.im < 𝕣 := by
  unfold rS scaleSet
  constructor
  · rintro ⟨x, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [add_zero, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    refine ⟨by positivity, ?_, by positivity, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨z / 𝕣, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Complex.div_ofReal_re]; positivity
    · rw [Complex.div_ofReal_re, div_lt_one h𝕣]; exact h2
    · rw [Complex.div_ofReal_im]; positivity
    · rw [Complex.div_ofReal_im, div_lt_one h𝕣]; exact h4
    · have : (𝕣 : ℂ) ≠ 0 := by exact_mod_cast h𝕣.ne'
      field_simp; ring

lemma mem_leftVerts_of {s 𝕣 : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ rS 𝕣 ∩ gridPts s)
    (hre : z.re = s) (h𝕣 : 0 < 𝕣) : z ∈ leftVerts s 𝕣 := by
  refine ⟨hz, fun y hy => ?_⟩
  obtain ⟨a, b, rfl⟩ := hy.2
  have hpos := ((mem_rS_iff h𝕣).1 hy.1).1
  simp only at hpos ⊢
  have ha : (0 : ℝ) < a := by
    by_contra hc; push Not at hc; nlinarith
  have ha1 : (1 : ℝ) ≤ a := by
    have : (0 : ℤ) < a := by exact_mod_cast ha
    exact_mod_cast this
  rw [hre]; nlinarith

lemma mem_rightVerts_of {s 𝕣 : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ rS 𝕣 ∩ gridPts s)
    (hre : 𝕣 ≤ z.re + s) (h𝕣 : 0 < 𝕣) : z ∈ rightVerts s 𝕣 := by
  refine ⟨hz, fun y hy => ?_⟩
  obtain ⟨a, b, rfl⟩ := hy.2
  obtain ⟨a', b', hz'⟩ := hz.2
  have hlt := ((mem_rS_iff h𝕣).1 hy.1).2.1
  simp only at hlt ⊢
  rw [hz'] at hre ⊢
  simp only at hre ⊢
  have h1 : (a : ℝ) < a' + 1 := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : a < a' + 1 := by exact_mod_cast h1
  have h3 : (a : ℝ) ≤ a' := by exact_mod_cast (Int.lt_add_one_iff.1 h2)
  nlinarith

/-- the norm of a nonzero offset in `{-1,0,1}²` -/
lemma norm_offset {s : ℝ} (hs : 0 < s) {r₁ r₂ : ℝ} (h₁ : r₁ ^ 2 = 0 ∨ r₁ ^ 2 = 1)
    (h₂ : r₂ ^ 2 = 0 ∨ r₂ ^ 2 = 1) (hne : r₁ ^ 2 = 1 ∨ r₂ ^ 2 = 1) :
    ‖(⟨r₁ * s, r₂ * s⟩ : ℂ)‖ = s ∨ ‖(⟨r₁ * s, r₂ * s⟩ : ℂ)‖ = Real.sqrt 2 * s := by
  have e : ‖(⟨r₁ * s, r₂ * s⟩ : ℂ)‖ = Real.sqrt (r₁ ^ 2 + r₂ ^ 2) * s := by
    rw [Complex.norm_def, Complex.normSq_mk,
      show r₁ * s * (r₁ * s) + r₂ * s * (r₂ * s) = (r₁ ^ 2 + r₂ ^ 2) * s ^ 2 by ring,
      Real.sqrt_mul' _ (by positivity), Real.sqrt_sq hs.le]
  rw [e]
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂]
  · rcases hne with h | h <;> linarith
  · left; simp
  · left; simp
  · right; norm_num

/-- the next vertex: `p` at sup-distance `3s/2` from the grid point `z`, rounded towards `z` -/
lemma exists_next_vertex {s : ℝ} (hs : 0 < s) {z p : ℂ} (hz : z ∈ gridPts s)
    (hp : supN (p - z) = 3 / 2 * s) :
    ∃ z' ∈ gridPts s, supN (p - z') ≤ s / 2 ∧
      (‖z - z'‖ = s ∨ ‖z - z'‖ = Real.sqrt 2 * s) ∧ z'.re ≤ z.re + s := by
  obtain ⟨a, b, rfl⟩ := hz
  set o₁ := (p - ⟨a * s, b * s⟩).re / s with ho₁
  set o₂ := (p - ⟨a * s, b * s⟩).im / s with ho₂
  have hmax : max |o₁| |o₂| = 3 / 2 := by
    rw [ho₁, ho₂, abs_div, abs_div, abs_of_pos hs, max_div_div_right hs.le]
    unfold supN at hp; rw [hp]; field_simp
  have hb₁ : |o₁| ≤ 3 / 2 := hmax ▸ le_max_left _ _
  have hb₂ : |o₂| ≤ 3 / 2 := hmax ▸ le_max_right _ _
  refine ⟨⟨(a + rnd1 o₁ : ℤ) * s, (b + rnd1 o₂ : ℤ) * s⟩, ⟨_, _, rfl⟩, ?_, ?_, ?_⟩
  · have k₁ := abs_sub_rnd1 hb₁
    have k₂ := abs_sub_rnd1 hb₂
    have e₁ : (p - ⟨((a + rnd1 o₁ : ℤ) : ℝ) * s, ((b + rnd1 o₂ : ℤ) : ℝ) * s⟩).re =
        s * (o₁ - rnd1 o₁) := by
      rw [ho₁]; simp only [Complex.sub_re]; push_cast; field_simp; ring
    have e₂ : (p - ⟨((a + rnd1 o₁ : ℤ) : ℝ) * s, ((b + rnd1 o₂ : ℤ) : ℝ) * s⟩).im =
        s * (o₂ - rnd1 o₂) := by
      rw [ho₂]; simp only [Complex.sub_im]; push_cast; field_simp; ring
    unfold supN
    rw [e₁, e₂, abs_mul, abs_mul, abs_of_pos hs]
    refine max_le ?_ ?_ <;> nlinarith
  · have e : (⟨(a : ℝ) * s, (b : ℝ) * s⟩ : ℂ) -
        ⟨((a + rnd1 o₁ : ℤ) : ℝ) * s, ((b + rnd1 o₂ : ℤ) : ℝ) * s⟩ =
        -⟨(rnd1 o₁ : ℝ) * s, (rnd1 o₂ : ℝ) * s⟩ := by
      apply Complex.ext <;> simp <;> ring
    rw [e, norm_neg]
    refine norm_offset hs (rnd1_sq_le _) (rnd1_sq_le _) ?_
    rcases max_choice |o₁| |o₂| with h | h <;> rw [h] at hmax
    · exact Or.inl (rnd1_sq_of_eq hmax)
    · exact Or.inr (rnd1_sq_of_eq hmax)
  · have : (rnd1 o₁ : ℝ) ≤ 1 := by unfold rnd1; split_ifs <;> norm_num
    simp only; push_cast; nlinarith

/-- **One annulus crossing** ((eqn-square-across), T:1667–1670 and T:1703–1708): if `P` runs
from the cell of `z` (sup-distance `≤ s/2`) to sup-distance `≥ 3s/2`, its `D`-length is at
least the distance across the annulus `B̄_{3s/4}(z) → ∂B_{3s/2}(z)` inside `B_{2s}(z)`. -/
lemma setDistIn_le_len (D : ContMetric) {s : ℝ} (hs : 0 < s) {z : ℂ} {P : ℝ → ℂ} {t₀ τ : ℝ}
    (hτ : t₀ ≤ τ) (hP : ContinuousOn P (Icc t₀ τ)) (h0 : supN (P t₀ - z) ≤ s / 2)
    (h1 : 3 / 2 * s ≤ supN (P τ - z)) :
    setDistIn D (closedBall z (3 / 4 * s)) (sphere z (3 / 2 * s)) (ball z (2 * s)) ≤
      D.len P t₀ τ := by
  set g : ℝ → ℝ := fun t => dist (P t) z with hg
  have hgc : ContinuousOn g (Icc t₀ τ) := (continuous_id.dist continuous_const).comp_continuousOn hP
  have hg0 : g t₀ ≤ 3 / 4 * s := by
    have h := Complex.norm_le_sqrt_two_mul_max (P t₀ - z)
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have : max |(P t₀ - z).re| |(P t₀ - z).im| ≤ s / 2 := h0
    simp only [hg, Complex.dist_eq]
    nlinarith [Real.sqrt_nonneg 2, abs_nonneg (P t₀ - z).re]
  have hg1 : 3 / 2 * s ≤ g τ := by
    simp only [hg, Complex.dist_eq]; exact h1.trans (supN_le_norm _)
  obtain ⟨a, b, hta, hab, hbτ, hga, hgb, hgm⟩ :=
    RectCross.exists_sub_crossing hτ hgc (by linarith) hg0 hg1
  have hPab : ContinuousOn P (Icc a b) := hP.mono (Icc_subset_Icc hta hbτ)
  calc setDistIn D (closedBall z (3 / 4 * s)) (sphere z (3 / 2 * s)) (ball z (2 * s))
      ≤ D.internal (ball z (2 * s)) (P a) (P b) := by
        refine iInf₂_le_of_le (P a) (mem_closedBall.2 (le_of_eq hga)) ?_
        exact iInf₂_le_of_le (P b) (mem_sphere.2 hgb) le_rfl
    _ ≤ curveLength (D.pt ∘ P) a b := by
        refine internalEDist_le_curveLength hab (D.continuous_pt.comp_continuousOn hPab) ?_
        intro u hu
        refine ⟨P u, mem_ball.2 ?_, rfl⟩
        have := (hgm u hu).2
        simp only [hg] at this; linarith
    _ ≤ D.len P t₀ τ := curveLength_mono _ hta hbτ

/-- **Step 3 induction** (T:1693–1716): from a vertex `z` whose cell contains `P(t₀)`, there is
a graph path from `z` to `∂^{s}_R(𝕣𝕊)` whose `a`-cost is at most `len(P|[t₀, t_b])`. -/
lemma disc_aux (D : ContMetric) {s 𝕣 : ℝ} (hs : 0 < s) (h𝕣 : 0 < 𝕣) (a : ℂ → ℝ)
    (ha : ∀ z ∈ rS 𝕣 ∩ gridPts s, ENNReal.ofReal (a z) ≤
      setDistIn D (closedBall z (3 / 4 * s)) (sphere z (3 / 2 * s)) (ball z (2 * s)))
    {P : ℝ → ℂ} {ta tb : ℝ} (hP : ContinuousOn P (Icc ta tb))
    (hre : ∀ t ∈ Icc ta tb, s ≤ (P t).re)
    (him : ∀ t ∈ Icc ta tb, s ≤ (P t).im ∧ (P t).im ≤ 𝕣 - s) (h1 : 𝕣 + 2 * s ≤ (P tb).re)
    {η : ℝ}
    (hunif : ∀ u ∈ Icc ta tb, ∀ v ∈ Icc ta tb, dist u v < η → dist (P u) (P v) < s) :
    ∀ n : ℕ, ∀ t₀ ∈ Icc ta tb, tb - t₀ < n * η → ∀ z ∈ rS 𝕣 ∩ gridPts s,
      supN (P t₀ - z) ≤ s / 2 →
      ∃ L : List ℂ, IsGraphPath s (rS 𝕣) L ∧ L.head? = some z ∧
        (∃ y ∈ L.getLast?, y ∈ rightVerts s 𝕣) ∧
        ENNReal.ofReal (L.map a).sum ≤ D.len P t₀ tb := by
  intro n
  induction n with
  | zero =>
    intro t₀ ht₀ hlt
    simp only [CharP.cast_eq_zero, zero_mul] at hlt
    linarith [ht₀.2]
  | succ n ih =>
    intro t₀ ht₀ hlt z hz hz0
    have hzS := (mem_rS_iff h𝕣).1 hz.1
    have hPt : ContinuousOn P (Icc t₀ tb) := hP.mono (Icc_subset_Icc ht₀.1 le_rfl)
    have hfc : ContinuousOn (fun t => supN (P t - z)) (Icc t₀ tb) :=
      continuous_supN.comp_continuousOn (hPt.sub continuousOn_const)
    have hfb : 3 / 2 * s ≤ supN (P tb - z) := by
      refine le_trans ?_ (le_max_left _ _)
      rw [Complex.sub_re, abs_of_pos (by linarith)]; linarith
    obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Icc ht₀.2 hfc
      ⟨hz0.trans (by linarith), hfb⟩
    have hτab : τ ∈ Icc ta tb := ⟨ht₀.1.trans hτ.1, hτ.2⟩
    have hcross : ENNReal.ofReal (a z) ≤ D.len P t₀ τ :=
      (ha z hz).trans (setDistIn_le_len D hs hτ.1 (hP.mono (Icc_subset_Icc ht₀.1 hτ.2)) hz0
        hfτ.ge)
    by_cases hR : 𝕣 ≤ z.re + s
    · refine ⟨[z], ⟨by simp, by simpa using hz.symm.symm, by simp⟩, rfl,
        ⟨z, rfl, mem_rightVerts_of hs hz hR h𝕣⟩, ?_⟩
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact hcross.trans (curveLength_mono _ le_rfl hτ.2)
    · push Not at hR
      obtain ⟨z', hz'g, hz'P, hadj, hstep⟩ := exists_next_vertex hs hz.2 hfτ
      -- the new vertex lies in `𝕣𝕊`
      have hre' : |(P τ - z').re| ≤ s / 2 := (le_max_left _ _).trans hz'P
      have him' : |(P τ - z').im| ≤ s / 2 := (le_max_right _ _).trans hz'P
      rw [abs_le, Complex.sub_re] at hre'
      rw [abs_le, Complex.sub_im] at him'
      have hz'S : z' ∈ rS 𝕣 := by
        rw [mem_rS_iff h𝕣]
        have := hre τ hτab; have := him τ hτab
        refine ⟨by linarith, by linarith, by linarith, by linarith⟩
      -- the exit took time at least `η`
      have hτη : t₀ + η ≤ τ := by
        by_contra hc
        push Not at hc
        have hd : dist (P τ) (P t₀) < s := hunif τ hτab t₀ ht₀ (by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hτ.1])]; linarith)
        have : supN (P τ - z) ≤ supN (P τ - P t₀) + supN (P t₀ - z) := by
          have := supN_add_le (P τ - P t₀) (P t₀ - z); rwa [sub_add_sub_cancel] at this
        have := supN_le_norm (P τ - P t₀)
        rw [← Complex.dist_eq] at this
        linarith
      obtain ⟨L', hL', hhead, hlast, hcost⟩ := ih τ hτab (by push_cast at hlt; linarith) z'
        ⟨hz'S, hz'g⟩ hz'P
      obtain ⟨rest, rfl⟩ : ∃ rest, L' = z' :: rest := by
        cases L' with
        | nil => simp at hhead
        | cons x rest => simp only [List.head?_cons, Option.some.injEq] at hhead; exact ⟨rest, by rw [hhead]⟩
      refine ⟨z :: z' :: rest, ⟨by simp, ?_, ?_⟩, rfl, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hz
        · exact hL'.2.1 x hx
      · exact List.isChain_cons_cons.2 ⟨hadj, hL'.2.2⟩
      · simpa [List.getLast?_cons_cons] using hlast
      · simp only [List.map_cons, List.sum_cons] at hcost ⊢
        calc ENNReal.ofReal (a z + (a z' + (rest.map a).sum))
            ≤ ENNReal.ofReal (a z) + ENNReal.ofReal (a z' + (rest.map a).sum) :=
              ENNReal.ofReal_add_le
          _ ≤ D.len P t₀ τ + D.len P τ tb := add_le_add hcross hcost
          _ = D.len P t₀ tb := curveLength_add _ hτ.1 hτ.2

/-- **DFGPS Thm 1.5, Step 3, deterministic part** (T:1693–1716): a path `P` from the line
`Re = s` to `Re ≥ 𝕣 + 2s` inside the strip `Re ≥ s`, `s ≤ Im ≤ 𝕣 - s` yields a path of the graph
`(𝕣𝕊) ∩ sℤ²` from `∂^s_L(𝕣𝕊)` to `∂^s_R(𝕣𝕊)` of `a`-cost at most `len(P; D)`, whenever `a(z)`
lower-bounds the distance across the annulus around each vertex `z`. -/
theorem exists_graphPath_le_len (D : ContMetric) {s 𝕣 : ℝ} (hs : 0 < s) (h𝕣 : 2 * s ≤ 𝕣)
    (a : ℂ → ℝ)
    (ha : ∀ z ∈ rS 𝕣 ∩ gridPts s, ENNReal.ofReal (a z) ≤
      setDistIn D (closedBall z (3 / 4 * s)) (sphere z (3 / 2 * s)) (ball z (2 * s)))
    {P : ℝ → ℂ} {ta tb : ℝ} (hab : ta ≤ tb) (hP : ContinuousOn P (Icc ta tb))
    (hre : ∀ t ∈ Icc ta tb, s ≤ (P t).re)
    (him : ∀ t ∈ Icc ta tb, s ≤ (P t).im ∧ (P t).im ≤ 𝕣 - s)
    (h0 : (P ta).re = s) (h1 : 𝕣 + 2 * s ≤ (P tb).re) :
    ∃ L : List ℂ, IsGraphPath s (rS 𝕣) L ∧ (∃ x ∈ L.head?, x ∈ leftVerts s 𝕣) ∧
      (∃ y ∈ L.getLast?, y ∈ rightVerts s 𝕣) ∧
      ENNReal.ofReal (L.map a).sum ≤ D.len P ta tb := by
  have h𝕣0 : 0 < 𝕣 := by linarith
  obtain ⟨η, hη, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP) s hs
  obtain ⟨n, hn⟩ := exists_nat_gt ((tb - ta) / η)
  have hn' : tb - ta < n * η := by rwa [div_lt_iff₀ hη] at hn
  -- the starting vertex, in the leftmost column
  set m : ℤ := round ((P ta).im / s) with hm
  set z₀ : ℂ := ⟨(1 : ℤ) * s, m * s⟩ with hz₀
  have hta : ta ∈ Icc ta tb := ⟨le_rfl, hab⟩
  have hround : |(P ta).im - m * s| ≤ s / 2 := by
    have h := abs_sub_round ((P ta).im / s)
    rw [← hm] at h
    have e : (P ta).im - m * s = s * ((P ta).im / s - m) := by field_simp
    rw [e, abs_mul, abs_of_pos hs]; nlinarith
  have hz₀g : z₀ ∈ gridPts s := ⟨1, m, rfl⟩
  have hz₀S : z₀ ∈ rS 𝕣 := by
    rw [mem_rS_iff h𝕣0]
    have := him ta hta
    rw [abs_le] at hround
    simp only [hz₀, Int.cast_one, one_mul]
    refine ⟨hs, by linarith, by linarith, by linarith⟩
  have hz₀P : supN (P ta - z₀) ≤ s / 2 := by
    unfold supN
    refine max_le ?_ ?_
    · rw [Complex.sub_re, h0]; simp [hz₀]; linarith
    · rw [Complex.sub_im]; simpa [hz₀] using hround
  obtain ⟨L, hL, hhead, hlast, hcost⟩ :=
    disc_aux D hs h𝕣0 a ha hP hre him h1 hunif n ta hta hn' z₀ ⟨hz₀S, hz₀g⟩ hz₀P
  refine ⟨L, hL, ⟨z₀, hhead, mem_leftVerts_of hs ⟨hz₀S, hz₀g⟩ (by simp [hz₀]) h𝕣0⟩, hlast, hcost⟩

end LQGMetric.DFGPS
