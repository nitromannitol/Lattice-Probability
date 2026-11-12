/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.DualityMain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Perc.Duality
import Mathlib.Basic.Finite.Prod

/-!
`percGoodLR_or_percBadTB`: in the `K × L` rectangle of sites (`K, L ≥ 1`), for every colouring
there is a left–right `4`-crossing of good sites or a top–bottom `*`-crossing of bad sites.
`percBadTB_of_not_percGoodLR` is the form used in the Peierls argument (Ding–Gwynne,
arXiv:1807.01072, proof of Lemma 3.11, `metric-comparison-final.tex` line 1267: "By planar
duality, it suffices to show … there does not exist a simple path in `𝒮*(ℛ_n)` from the top
boundary to the bottom boundary … consisting of squares for which `E_S^ε` does not occur").

Proof: the exploration walk of `LQGMetric.Perc.Duality` (Gale 1979, Hex theorem; Kesten 1982
§2.4) started at the top-left corner terminates, by injectivity of the step map and finiteness
of the frame, at an edge whose good site lies in column `K` or whose bad site lies in row `-1`;
the connectivity invariants of the walk give the crossing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

namespace PercDual

variable {K L : ℤ} {good : ℤ × ℤ → Prop}

variable (K L good) in
/-- The exploration walk started at the top-left corner. -/
noncomputable def orbit (n : ℕ) : (ℤ × ℤ) × (ℤ × ℤ) := (step K L good)^[n] (start L)

lemma orbit_succ (n : ℕ) : orbit K L good (n + 1) = step K L good (orbit K L good n) :=
  Function.iterate_succ_apply' _ _ _

/-- The exploration walk reaches column `K` (good side) or row `-1` (bad side) while keeping
its invariant. -/
lemma exists_terminal (hK : 0 ≤ K) (hL : 1 ≤ L) :
    ∃ n, Inv K L good (orbit K L good n) ∧
      ((orbit K L good n).1.1 = K ∨ (orbit K L good n).2.2 = -1) := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ n, Inv K L good (orbit K L good n) := by
    intro n
    induction n with
    | zero => exact inv_start hK hL
    | succ n ih =>
      rw [orbit_succ]
      obtain ⟨h1, h2⟩ := hcon n ih
      exact inv_step ih h1 h2
  set T : Set ((ℤ × ℤ) × (ℤ × ℤ)) :=
    (Set.Icc (-1) K ×ˢ Set.Icc (-1) L) ×ˢ (Set.Icc (-1) K ×ˢ Set.Icc (-1) L) with hTdef
  have hT : T.Finite :=
    Set.Finite.prod (Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_Icc _ _))
      (Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_Icc _ _))
  have hmem : ∀ n, orbit K L good n ∈ T := by
    intro n
    obtain ⟨⟨hg, hb, -⟩, -, -⟩ := hall n
    have h1 := goodE_bounds hg
    have h2 := hb.1
    simp only [inE] at h2
    simp only [hTdef, Set.mem_prod, Set.mem_Icc]
    omega
  obtain ⟨a, b, hab, he⟩ := hT.exists_lt_map_eq_of_forall_mem hmem
  have key : ∀ a k : ℕ, orbit K L good a ≠ orbit K L good (a + k + 1) := by
    intro a
    induction a with
    | zero =>
      intro k h
      have hp : pred K L good (orbit K L good (k + 1)) = orbit K L good k := by
        rw [orbit_succ]; exact pred_step (hall k).1
      rw [zero_add] at h
      rw [← h] at hp
      apply not_iface_pred_start (K := K) (L := L) (good := good)
      rw [show start L = orbit K L good 0 from rfl, hp]
      exact (hall k).1
    | succ a ih =>
      intro k h
      apply ih k
      rw [show a + 1 + k + 1 = (a + k + 1) + 1 by omega, orbit_succ, orbit_succ] at h
      have := congrArg (pred K L good) h
      rwa [pred_step (hall _).1, pred_step (hall _).1] at this
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k + 1 := ⟨b - a - 1, by omega⟩
  exact key a k he

/-- What a `4`-path of good frame sites from the left column gives. -/
lemma GR_extract (hK : 1 ≤ K) {g : ℤ × ℤ} (h : GR K L good g) :
    g.1 = -1 ∨ (percInGrid K L g ∧ good g ∧ ∃ a : ℤ × ℤ, a.1 = 0 ∧ percInGrid K L a ∧ good a ∧
      Relation.ReflTransGen (PercGoodStep K L good) a g) ∨ PercGoodLR K L good := by
  obtain ⟨w, hw1, -, -, hwg⟩ := h
  induction hwg with
  | refl => exact Or.inl hw1
  | @tail c g' _ hcg ih =>
    obtain ⟨hc, hg, hadj⟩ := hcg
    have bc := goodE_bounds hc
    have bg := goodE_bounds hg
    rcases ih with h1 | ⟨hcgrid, hcgood, a, ha0, hagrid, hagood, hac⟩ | h3
    · by_cases hg1 : g'.1 = -1
      · exact Or.inl hg1
      · have hg0 : g'.1 = 0 := by simp only [PercAdj4] at hadj; omega
        have := goodE_mid hg hg1 (by omega)
        exact Or.inr (Or.inl ⟨this.1, this.2, g', hg0, this.1, this.2, .refl⟩)
    · by_cases hg1 : g'.1 = -1
      · exact Or.inl hg1
      by_cases hgK : g'.1 = K
      · refine Or.inr (Or.inr ⟨a, c, ha0, ?_, hagrid, hagood, hac⟩)
        simp only [PercAdj4] at hadj
        simp only [percInGrid] at hcgrid
        omega
      · have := goodE_mid hg hg1 hgK
        exact Or.inr (Or.inl ⟨this.1, this.2, a, ha0, hagrid, hagood,
          hac.tail ⟨hcgrid, hcgood, this.1, this.2, hadj⟩⟩)
    · exact Or.inr (Or.inr h3)

/-- What a `*`-path of bad frame sites from the top row gives. -/
lemma BR_extract (hL : 1 ≤ L) {b : ℤ × ℤ} (h : BR K L good b) :
    b.2 = L ∨ (percInGrid K L b ∧ ¬ good b ∧ ∃ a : ℤ × ℤ, a.2 = L - 1 ∧ percInGrid K L a ∧
      ¬ good a ∧ Relation.ReflTransGen (PercBadStep K L good) a b) ∨ PercBadTB K L good := by
  obtain ⟨w, hw1, -, -, hwb⟩ := h
  induction hwb with
  | refl => exact Or.inl hw1
  | @tail c b' _ hcb ih =>
    obtain ⟨hc, hb, hadj⟩ := hcb
    have bc := hc.1
    have bb := hb.1
    simp only [inE] at bc bb
    simp only [PercAdjK] at hadj
    rcases ih with h1 | ⟨hcgrid, hcbad, a, haL, hagrid, habad, hac⟩ | h3
    · by_cases hb1 : b'.2 = L
      · exact Or.inl hb1
      · have hbL : b'.2 = L - 1 := by omega
        have := badE_mid hb (by omega) (by omega)
        exact Or.inr (Or.inl ⟨this.1, this.2, b', hbL, this.1, this.2, .refl⟩)
    · by_cases hb1 : b'.2 = L
      · exact Or.inl hb1
      simp only [percInGrid] at hcgrid
      by_cases hb0 : b'.2 = -1
      · exact Or.inr (Or.inr ⟨a, c, haL, by omega, hagrid, habad, hac⟩)
      · have := badE_mid hb (by omega) (by omega)
        exact Or.inr (Or.inl ⟨this.1, this.2, a, haL, hagrid, habad,
          hac.tail ⟨hcgrid, hcbad, this.1, this.2, hadj⟩⟩)
    · exact Or.inr (Or.inr h3)

end PercDual

/-- **Planar duality** in a `K × L` rectangle of sites: a left–right crossing by a `4`-path of
good sites or a top–bottom crossing by a `*`-path of bad sites. -/
theorem percGoodLR_or_percBadTB (K L : ℤ) (good : ℤ × ℤ → Prop) (hK : 1 ≤ K) (hL : 1 ≤ L) :
    PercGoodLR K L good ∨ PercBadTB K L good := by
  obtain ⟨n, ⟨⟨-, -, -⟩, hGR, hBR⟩, hterm⟩ :=
    PercDual.exists_terminal (K := K) (L := L) (good := good) (by omega) hL
  rcases hterm with h | h
  · left
    rcases PercDual.GR_extract hK hGR with h1 | ⟨h2, -⟩ | h3
    · omega
    · have := h2.2.1; omega
    · exact h3
  · right
    rcases PercDual.BR_extract hL hBR with h1 | ⟨h2, -⟩ | h3
    · omega
    · have := h2.2.2.1; omega
    · exact h3

end LQGMetric
