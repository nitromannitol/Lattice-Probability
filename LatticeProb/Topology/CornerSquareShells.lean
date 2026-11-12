import Mathlib

/-!
# Corner shells of a closed square

Let `S = [a, a + s] × [b, b + s]` be a closed square with a corner at the origin, i.e. `a ∈ {0, -s}` and
`b ∈ {0, -s}`, and put `tₖ = s / 2^(k+1)`. The corner square of `S` of side `2 tₖ = s / 2^k` at the origin is the
union of four closed squares of side `tₖ`; the three of them which do not contain the origin form the `k`-th
*corner shell*. The shells cover `S \ {0}`, consecutive shells meet, each shell is preconnected, and every point `w`
of the `k`-th shell satisfies `tₖ ≤ |w| ≤ 3 tₖ`. This is the deterministic geometry behind chaining estimates for
random metrics towards a boundary point of a square, where the shells are used at all scales simultaneously.

## Main results

* `LatticeProb.Topology.convex_reProdIm`: a product `s ×ℂ t` of convex sets of reals is convex.
* `LatticeProb.Topology.norm_le_three_mul_of_abs_le`: `|Re w|, |Im w| ≤ 2 t` gives `|w| ≤ 3 t`.
* `LatticeProb.Topology.exists_cornerIntervalCoeffs`: the one-dimensional corner intervals.
* `LatticeProb.Topology.exists_cornerSquareShells`: the corner shells of a square with a corner at the origin.
-/

open Set

namespace LatticeProb.Topology

/-- A product `s ×ℂ t` of convex sets of reals is convex. -/
theorem convex_reProdIm {s t : Set ℝ} (hs : Convex ℝ s) (ht : Convex ℝ t) : Convex ℝ (s ×ℂ t) := by
  intro x hx y hy p q hp hq hpq
  rw [Complex.mem_reProdIm] at hx hy ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  exact ⟨hs hx.1 hy.1 hp hq hpq, ht hx.2 hy.2 hp hq hpq⟩

/-- If both coordinates of `w` are at most `2 t` in absolute value, then `|w| ≤ 3 t` (indeed `|w| ≤ 2 √2 t`). -/
theorem norm_le_three_mul_of_abs_le {w : ℂ} {t : ℝ} (hre : |w.re| ≤ 2 * t) (him : |w.im| ≤ 2 * t) :
    ‖w‖ ≤ 3 * t := by
  have ht : 0 ≤ t := by linarith [abs_nonneg w.re]
  have h1 : w.re * w.re ≤ (2 * t) * (2 * t) := by
    rw [← abs_mul_abs_self w.re]; exact mul_le_mul hre hre (abs_nonneg _) (by linarith)
  have h2 : w.im * w.im ≤ (2 * t) * (2 * t) := by
    rw [← abs_mul_abs_self w.im]; exact mul_le_mul him him (abs_nonneg _) (by linarith)
  have hsq : ‖w‖ ^ 2 ≤ (3 * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  nlinarith [norm_nonneg w]

/-- A point of `[a, a + s]` with `a ∈ {0, -s}` has absolute value at most `s`. -/
theorem abs_le_of_mem_Icc_of_corner {a s u : ℝ} (ha : a = 0 ∨ a = -s) (hu : u ∈ Icc a (a + s)) : |u| ≤ s := by
  rw [abs_le]; rcases ha with rfl | rfl <;> constructor <;> linarith [hu.1, hu.2]

/-- **Corner intervals in one dimension.** Let `0 < s` and `a ∈ {0, -s}`, so that `0` is an endpoint of
`[a, a + s]`. There are coefficients `α, β, γ` such that for every `0 < t` with `2 t ≤ s`, the interval
`[α t, α t + t]` (next to `0`) and `[β t, β t + t]` (away from `0`) lie in `[a, a + s]`, the points `u` of the first
satisfy `|u| ≤ t` and those of the second `t ≤ |u| ≤ 2 t`, every `u ∈ [a, a + s]` with `|u| ≤ t` lies in the first
and every one with `t < |u| ≤ 2 t` in the second, and `γ t` lies in both and in the far interval
`[β t / 2, β t / 2 + t / 2]` at scale `t / 2`. -/
theorem exists_cornerIntervalCoeffs {a s : ℝ} (ha : a = 0 ∨ a = -s) :
    ∃ α β γ : ℝ, ∀ t : ℝ, 0 < t → 2 * t ≤ s →
      Icc (α * t) (α * t + t) ⊆ Icc a (a + s) ∧ Icc (β * t) (β * t + t) ⊆ Icc a (a + s) ∧
      (∀ u ∈ Icc (α * t) (α * t + t), |u| ≤ t) ∧
      (∀ u ∈ Icc (β * t) (β * t + t), t ≤ |u| ∧ |u| ≤ 2 * t) ∧
      (∀ u ∈ Icc a (a + s), |u| ≤ t → u ∈ Icc (α * t) (α * t + t)) ∧
      (∀ u ∈ Icc a (a + s), t < |u| → |u| ≤ 2 * t → u ∈ Icc (β * t) (β * t + t)) ∧
      γ * t ∈ Icc (α * t) (α * t + t) ∧ γ * t ∈ Icc (β * t) (β * t + t) ∧
      γ * t ∈ Icc (β * (t / 2)) (β * (t / 2) + t / 2) := by
  rcases ha with rfl | rfl
  · refine ⟨0, 1, 1, fun t ht hts => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · intro u hu; rw [abs_le]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · intro u hu
      rw [abs_of_nonneg (a := u) (by linarith [hu.1])]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · intro u hu h
      rw [abs_of_nonneg (a := u) (by linarith [hu.1])] at h; exact ⟨by linarith [hu.1], by linarith⟩
    · intro u hu h h'
      rw [abs_of_nonneg (a := u) (by linarith [hu.1])] at h h'; exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  · refine ⟨-1, -2, -1, fun t ht hts => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · intro u hu; rw [abs_le]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · intro u hu
      rw [abs_of_nonpos (a := u) (by linarith [hu.2])]; exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    · intro u hu h
      rw [abs_of_nonpos (a := u) (by linarith [hu.2])] at h; exact ⟨by linarith, by linarith [hu.2]⟩
    · intro u hu h h'
      rw [abs_of_nonpos (a := u) (by linarith [hu.2])] at h h'; exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩

/-- **Corner shells of a square.** Let `S = [a, a + s] × [b, b + s]` with `0 < s`, `a ∈ {0, -s}` and `b ∈ {0, -s}`,
so that `0` is a corner of `S`, and put `tₖ = s / 2^(k+1)`. There are closed squares
`Q k i = [x k i, x k i + tₖ] × [y k i, y k i + tₖ]` (`k ∈ ℕ`, `i ∈ Fin 3`) of side `tₖ` such that

* `Q k i ⊆ S`;
* every `w ∈ Q k i` satisfies `tₖ ≤ |w| ≤ 3 tₖ`, and the corner `x k i + i y k i` has absolute value at most `3 tₖ`;
* `S ⊆ {0} ∪ ⋃ₖ ⋃ᵢ Q k i`;
* each shell `⋃ᵢ Q k i` is preconnected, and consecutive shells meet.

The shell `⋃ᵢ Q k i` consists of the three dyadic children of side `tₖ` of the corner square of side `2 tₖ` at the
origin which do not contain the origin. -/
theorem exists_cornerSquareShells {a b s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) (hb : b = 0 ∨ b = -s) :
    ∃ (x y : ℕ → Fin 3 → ℝ) (Q : ℕ → Fin 3 → Set ℂ),
      (∀ k i, Q k i = Icc (x k i) (x k i + s / 2 ^ (k + 1)) ×ℂ Icc (y k i) (y k i + s / 2 ^ (k + 1))) ∧
      (∀ k i, Q k i ⊆ Icc a (a + s) ×ℂ Icc b (b + s)) ∧
      (∀ k i, ∀ w ∈ Q k i, s / 2 ^ (k + 1) ≤ ‖w‖ ∧ ‖w‖ ≤ 3 * (s / 2 ^ (k + 1))) ∧
      (∀ k i, ‖(⟨x k i, y k i⟩ : ℂ)‖ ≤ 3 * (s / 2 ^ (k + 1))) ∧
      Icc a (a + s) ×ℂ Icc b (b + s) ⊆ insert 0 (⋃ k, ⋃ i, Q k i) ∧
      (∀ k, IsPreconnected (⋃ i, Q k i)) ∧
      (∀ k, ((⋃ i, Q k i) ∩ ⋃ i, Q (k + 1) i).Nonempty) := by
  obtain ⟨α, β, γ, hA⟩ := exists_cornerIntervalCoeffs (s := s) ha
  obtain ⟨α', β', γ', hB⟩ := exists_cornerIntervalCoeffs (s := s) hb
  let t : ℕ → ℝ := fun k => s / 2 ^ (k + 1)
  have htpos : ∀ k, 0 < t k := fun k => div_pos hs (pow_pos two_pos _)
  have hts : ∀ k, 2 * t k ≤ s := fun k => by
    have h : 2 * t k = s / 2 ^ k := by show 2 * (s / 2 ^ (k + 1)) = s / 2 ^ k; ring
    rw [h]; exact div_le_self hs.le (one_le_pow₀ (by norm_num))
  have hhalf : ∀ k, t (k + 1) = t k / 2 := fun k => by
    show s / 2 ^ (k + 1 + 1) = s / 2 ^ (k + 1) / 2; ring
  let x : ℕ → Fin 3 → ℝ := fun k => ![β * t k, β * t k, α * t k]
  let y : ℕ → Fin 3 → ℝ := fun k => ![α' * t k, β' * t k, β' * t k]
  have hxy : ∀ k i, (x k i = α * t k ∨ x k i = β * t k) ∧ (y k i = α' * t k ∨ y k i = β' * t k) ∧
      (x k i = β * t k ∨ y k i = β' * t k) := by
    intro k i; fin_cases i <;> simp [x, y]
  -- one-coordinate facts about the intervals of `Q k i`
  have hcoord : ∀ k i,
      (Icc (x k i) (x k i + t k) ⊆ Icc a (a + s) ∧ (∀ u ∈ Icc (x k i) (x k i + t k), |u| ≤ 2 * t k) ∧
        γ * t k ∈ Icc (x k i) (x k i + t k)) ∧
      (Icc (y k i) (y k i + t k) ⊆ Icc b (b + s) ∧ (∀ u ∈ Icc (y k i) (y k i + t k), |u| ≤ 2 * t k) ∧
        γ' * t k ∈ Icc (y k i) (y k i + t k)) ∧
      ((∀ u ∈ Icc (x k i) (x k i + t k), t k ≤ |u|) ∨ (∀ u ∈ Icc (y k i) (y k i + t k), t k ≤ |u|)) := by
    intro k i
    obtain ⟨hA1, hA2, hA3, hA4, -, -, hA7, hA8, -⟩ := hA (t k) (htpos k) (hts k)
    obtain ⟨hB1, hB2, hB3, hB4, -, -, hB7, hB8, -⟩ := hB (t k) (htpos k) (hts k)
    have ht0 := htpos k
    obtain ⟨hx, hy, hf⟩ := hxy k i
    refine ⟨?_, ?_, ?_⟩
    · rcases hx with hx | hx <;> rw [hx]
      · exact ⟨hA1, fun u hu => (hA3 u hu).trans (by linarith), hA7⟩
      · exact ⟨hA2, fun u hu => (hA4 u hu).2, hA8⟩
    · rcases hy with hy | hy <;> rw [hy]
      · exact ⟨hB1, fun u hu => (hB3 u hu).trans (by linarith), hB7⟩
      · exact ⟨hB2, fun u hu => (hB4 u hu).2, hB8⟩
    · rcases hf with hf | hf <;> rw [hf]
      · exact Or.inl fun u hu => (hA4 u hu).1
      · exact Or.inr fun u hu => (hB4 u hu).1
  have hnorm : ∀ k i, ∀ w ∈ Icc (x k i) (x k i + t k) ×ℂ Icc (y k i) (y k i + t k),
      t k ≤ ‖w‖ ∧ ‖w‖ ≤ 3 * t k := by
    intro k i w hw
    rw [Complex.mem_reProdIm] at hw
    obtain ⟨⟨-, hx2, -⟩, ⟨-, hy2, -⟩, hf⟩ := hcoord k i
    refine ⟨?_, norm_le_three_mul_of_abs_le (hx2 _ hw.1) (hy2 _ hw.2)⟩
    rcases hf with hf | hf
    · exact (hf _ hw.1).trans (Complex.abs_re_le_norm w)
    · exact (hf _ hw.2).trans (Complex.abs_im_le_norm w)
  -- the point `γ t + i γ' t` lies in every square of the `k`-th shell
  have hγ : ∀ k i, (⟨γ * t k, γ' * t k⟩ : ℂ) ∈ Icc (x k i) (x k i + t k) ×ℂ Icc (y k i) (y k i + t k) :=
    fun k i => Complex.mem_reProdIm.2 ⟨(hcoord k i).1.2.2, (hcoord k i).2.1.2.2⟩
  refine ⟨x, y, fun k i => Icc (x k i) (x k i + t k) ×ℂ Icc (y k i) (y k i + t k), fun k i => rfl,
    ?_, hnorm, ?_, ?_, ?_, ?_⟩
  · intro k i w hw
    rw [Complex.mem_reProdIm] at hw ⊢
    exact ⟨(hcoord k i).1.1 hw.1, (hcoord k i).2.1.1 hw.2⟩
  · intro k i
    have ht0 := htpos k
    exact (hnorm k i ⟨x k i, y k i⟩ (Complex.mem_reProdIm.2
      ⟨left_mem_Icc.2 (by linarith), left_mem_Icc.2 (by linarith)⟩)).2
  · intro w hw
    rw [Complex.mem_reProdIm] at hw
    rw [mem_insert_iff]
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    right
    set m := max |w.re| |w.im| with hm
    have hm0 : 0 < m := by
      rcases (abs_nonneg w.re).lt_or_eq with h | h
      · exact lt_of_lt_of_le h (le_max_left _ _)
      rcases (abs_nonneg w.im).lt_or_eq with h' | h'
      · exact lt_of_lt_of_le h' (le_max_right _ _)
      exact absurd (Complex.ext (by simpa using (abs_eq_zero.1 h.symm))
        (by simpa using (abs_eq_zero.1 h'.symm))) hw0
    have hms : m ≤ s :=
      max_le (abs_le_of_mem_Icc_of_corner ha hw.1) (abs_le_of_mem_Icc_of_corner hb hw.2)
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ((one_le_div hm0).2 hms) (one_lt_two : (1 : ℝ) < 2)
    have hp : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
    have hlt : t n < m := by
      have h := (div_lt_iff₀ hm0).1 hn2
      show s / 2 ^ (n + 1) < m
      rw [div_lt_iff₀ (pow_pos two_pos _)]; linarith [mul_comm m (2 ^ (n + 1) : ℝ)]
    have hle : m ≤ 2 * t n := by
      have h := (le_div_iff₀ hm0).1 hn1
      have h2 : 2 * t n = s / 2 ^ n := by show 2 * (s / 2 ^ (n + 1)) = s / 2 ^ n; ring
      rw [h2, le_div_iff₀ hp]; linarith [mul_comm m (2 ^ n : ℝ)]
    have hre_le : |w.re| ≤ 2 * t n := (le_max_left _ _).trans hle
    have him_le : |w.im| ≤ 2 * t n := (le_max_right _ _).trans hle
    obtain ⟨-, -, -, -, hA5, hA6, -, -, -⟩ := hA (t n) (htpos n) (hts n)
    obtain ⟨-, -, -, -, hB5, hB6, -, -, -⟩ := hB (t n) (htpos n) (hts n)
    refine mem_iUnion.2 ⟨n, mem_iUnion.2 ?_⟩
    by_cases hre : t n < |w.re|
    · by_cases him : t n < |w.im|
      · exact ⟨1, Complex.mem_reProdIm.2 ⟨hA6 _ hw.1 hre hre_le, hB6 _ hw.2 him him_le⟩⟩
      · exact ⟨0, Complex.mem_reProdIm.2 ⟨hA6 _ hw.1 hre hre_le, hB5 _ hw.2 (not_lt.1 him)⟩⟩
    · have him : t n < |w.im| := by
        rcases lt_max_iff.1 hlt with h | h
        · exact absurd h hre
        · exact h
      exact ⟨2, Complex.mem_reProdIm.2 ⟨hA5 _ hw.1 (not_lt.1 hre), hB6 _ hw.2 him him_le⟩⟩
  · intro k
    exact isPreconnected_iUnion ⟨_, mem_iInter.2 fun i => hγ k i⟩
      fun i => (convex_reProdIm (convex_Icc _ _) (convex_Icc _ _)).isPreconnected
  · intro k
    refine ⟨⟨γ * t k, γ' * t k⟩, mem_iUnion.2 ⟨0, hγ k 0⟩, mem_iUnion.2 ⟨1, ?_⟩⟩
    obtain ⟨-, -, -, -, -, -, -, -, hA9⟩ := hA (t k) (htpos k) (hts k)
    obtain ⟨-, -, -, -, -, -, -, -, hB9⟩ := hB (t k) (htpos k) (hts k)
    refine Complex.mem_reProdIm.2 ⟨?_, ?_⟩
    · show γ * t k ∈ Icc (β * t (k + 1)) (β * t (k + 1) + t (k + 1))
      rw [hhalf]; exact hA9
    · show γ' * t k ∈ Icc (β' * t (k + 1)) (β' * t (k + 1) + t (k + 1))
      rw [hhalf]; exact hB9

end LatticeProb.Topology
