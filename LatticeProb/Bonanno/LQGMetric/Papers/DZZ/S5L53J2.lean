/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusPeierls
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusMain

/-!
# DZZ Lemma 5.3, node 3: the good cluster of a box grid (deterministic part)

Part of the percolation step of DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2504–2514, an
argument "similar to (eq-par)", l. 1927–2000). DZZ show by planar duality and a Peierls count
that any `ℓ` boundary boxes of `Λ_i` are joined by open boxes to all but few boundary boxes of
`Λ_{i-1}` ((eq-connectivity-percolation), l. 1968–1975). We reach the same conclusion through
the existing enclosure tools: a good enclosure of the thin annulus `n ≤ ‖z‖_∞ ≤ N` next to the
boundary of the grid `annBox N` (`PercEnclosure`, `perc_annulus_peierls`) is met by every
straight column from a boundary site to the hole, so every boundary site whose column is
good is joined to the enclosure (`l53_col_reach`). `l53_cluster`: the good cluster `C` of the
enclosure contains all these boundary sites and is `4`-connected inside itself.

The boxes form a set `Box ⊇ annBox N`, and the boundary depth `tb d` of side `d` is `N - n` (the
boundary row of `annBox N`) or `N - n + 1` (one row outside it): a cell with an even number
`K = 2N + 2` of boxes per side is `Box = [-N, N+1]²`, with `tb = N - n + 1` on the sides `T`, `R`.

Here `l53Col n N d a t = annFromStd n N d (a, t)` is the site of side `d` at position `a` along
the side (`0 ≤ a ≤ 2N`) and depth `t` (`annDir d = n + t`); `t = N - n` is the boundary row.
Own combinatorial argument replacing DZZ's duality (the enclosure is the existing tool).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric.DZZ

open LQGMetric PercAnn

/-- The site of side `d` at position `a` along the side and depth `t`
(`annLong d = a - N`, `annDir d = n + t`). -/
def l53Col (n N : ℤ) (d : PercDir) (a t : ℤ) : ℤ × ℤ := annFromStd n N d (a, t)

lemma l53Col_adj4 (n N : ℤ) (d : PercDir) (a t : ℤ) :
    PercAdj4 (l53Col n N d a t) (l53Col n N d a (t + 1)) :=
  annFromStd_adj4 n N d (Or.inl ⟨rfl, Or.inr rfl⟩)

/-- A straight column of sites of `S` is a `4`-path in `S`. -/
lemma l53_col_path (n N : ℤ) (d : PercDir) (a : ℤ) (S : Set (ℤ × ℤ)) (t₀ : ℤ) :
    ∀ k : ℕ, (∀ i : ℕ, i ≤ k → l53Col n N d a (t₀ + i) ∈ S) →
      Relation.ReflTransGen (PercStepIn S PercAdj4) (l53Col n N d a t₀)
        (l53Col n N d a (t₀ + k)) := by
  intro k
  induction k with
  | zero => intro _; simp only [Nat.cast_zero, add_zero]; exact .refl
  | succ k ih =>
    intro hS
    refine (ih fun i hi => hS i (by omega)).tail ⟨hS k (by omega), ?_, ?_⟩
    · have := hS (k + 1) le_rfl
      push_cast at this ⊢
      exact this
    · have := l53Col_adj4 n N d a (t₀ + k)
      push_cast
      rwa [add_assoc] at this

/-- **A good column joins its boundary site to the enclosure.** Let `U` be a good enclosure of
the annulus `n ≤ ‖z‖_∞ ≤ N` (in the form of `PercEnclosure`) and `Box ⊇ annBox N` the set of all
boxes. If the column of side `d` at a non-corner position `a` (`|a - N| < n`), from depth `0` to
the boundary depth `tb ∈ [N - n, N - n + 1]`, consists of good boxes of `Box`, then its boundary
site `l53Col n N d a tb` is reached from `U` by a `4`-path of good boxes of `Box`. (`tb = N - n`:
the boundary row of `annBox N`; `tb = N - n + 1`: one more row outside `annBox N`.) -/
lemma l53_col_reach (n N : ℤ) (hn : 1 ≤ n) (hnN : n ≤ N) (G U Box : Set (ℤ × ℤ))
    (hU : ∀ z ∈ U, z ∈ G ∧ ∃ d, z ∈ annRect n N d)
    (hsep : ∀ (Γ : Set (ℤ × ℤ)) (s e : ℤ × ℤ), (-n < s.1 ∧ s.1 < n ∧ -n < s.2 ∧ s.2 < n) →
      ¬ annBox N e → Relation.ReflTransGen (PercStepIn Γ PercAdjK) s e → ∃ z ∈ U, z ∈ Γ)
    (d : PercDir) (a : ℤ) (ha₁ : N - n < a) (ha₂ : a < N + n) (tb : ℤ) (htb₁ : N - n ≤ tb)
    (htb₂ : tb ≤ N - n + 1)
    (hcolB : ∀ t, 0 ≤ t → t ≤ tb → l53Col n N d a t ∈ Box)
    (hcol : ∀ t, 0 ≤ t → t ≤ tb → l53Col n N d a t ∈ G) :
    ∃ u ∈ U, Relation.ReflTransGen (PercStepIn {z | z ∈ Box ∧ z ∈ G} PercAdj4) u
      (l53Col n N d a tb) := by
  set Γ : Set (ℤ × ℤ) := {z | ∃ t, -1 ≤ t ∧ t ≤ N - n + 1 ∧ z = l53Col n N d a t} with hΓ
  have hk : (((N - n + 2).toNat : ℕ) : ℤ) = N - n + 2 := Int.toNat_of_nonneg (by omega)
  have hpath := l53_col_path n N d a Γ (-1) (N - n + 2).toNat (fun i hi =>
    ⟨-1 + i, by omega, by omega, rfl⟩)
  rw [hk, show (-1 : ℤ) + (N - n + 2) = N - n + 1 by ring] at hpath
  obtain ⟨z, hzU, t, ht₁, ht₂, rfl⟩ := hsep Γ (l53Col n N d a (-1)) (l53Col n N d a (N - n + 1))
    (by cases d <;> simp only [l53Col, annFromStd] <;> omega)
    (by cases d <;> simp only [l53Col, annFromStd, annBox] <;> omega)
    (percStepIn_mono (fun _ h => h) (fun _ _ h => percAdjK_of_adj4 h) hpath)
  obtain ⟨-, d', hd'⟩ := hU _ hzU
  have ht : 0 ≤ t ∧ t ≤ N - n := by
    obtain ⟨hb, hdir⟩ := hd'
    cases d <;> cases d' <;> simp only [l53Col, annFromStd, annBox, annDir] at hb hdir <;> omega
  refine ⟨_, hzU, ?_⟩
  have hk' : (((tb - t).toNat : ℕ) : ℤ) = tb - t := Int.toNat_of_nonneg (by omega)
  have h := l53_col_path n N d a {z | z ∈ Box ∧ z ∈ G} t (tb - t).toNat (fun i hi => by
    have hi' : (i : ℤ) ≤ tb - t := by rw [← hk']; exact_mod_cast hi
    exact ⟨hcolB _ (by omega) (by omega), hcol _ (by omega) (by omega)⟩)
  rwa [hk', show t + (tb - t) = tb by ring] at h

/-- **The good cluster of a grid with a good enclosure.** If the annulus `n ≤ ‖z‖_∞ ≤ N` has a
good enclosure, there is a set `C` of good boxes of `Box ⊇ annBox N`, `4`-connected inside
itself, containing the boundary site `l53Col n N d a (tb d)` of every good column at a
non-corner position. -/
theorem l53_cluster (n N : ℤ) (hn : 1 ≤ n) (hnN : n ≤ N) (G Box : Set (ℤ × ℤ))
    (hBox : ∀ z, annBox N z → z ∈ Box) (tb : PercDir → ℤ)
    (htb : ∀ d, N - n ≤ tb d ∧ tb d ≤ N - n + 1)
    (hcolB : ∀ d a, N - n < a → a < N + n → ∀ t, 0 ≤ t → t ≤ tb d → l53Col n N d a t ∈ Box)
    (henc : PercEnclosure n N G) :
    ∃ C : Set (ℤ × ℤ), (∀ z ∈ C, z ∈ Box ∧ z ∈ G) ∧
      (∀ x ∈ C, ∀ y ∈ C, Relation.ReflTransGen (PercStepIn C PercAdj4) x y) ∧
      ∀ d a, N - n < a → a < N + n → (∀ t, 0 ≤ t → t ≤ tb d → l53Col n N d a t ∈ G) →
        l53Col n N d a (tb d) ∈ C := by
  obtain ⟨U, hU, ⟨u₀, hu₀⟩, hUc, hsep⟩ := henc
  set W : Set (ℤ × ℤ) := {z | z ∈ Box ∧ z ∈ G} with hW
  have hUW : ∀ z ∈ U, z ∈ W := fun z hz => by
    obtain ⟨hG, d, hd⟩ := hU z hz
    exact ⟨hBox z hd.1, hG⟩
  set C : Set (ℤ × ℤ) := {z | ∃ u ∈ U, Relation.ReflTransGen (PercStepIn W PercAdj4) u z}
    with hC
  have hCW : ∀ z ∈ C, z ∈ W := fun z ⟨u, hu, h⟩ => rtg_end_mem h (hUW u hu)
  have hsymm : ∀ x y, PercAdj4 x y → PercAdj4 y x := fun _ _ h => percAdj4_symm h
  have hfrom : ∀ z ∈ C, Relation.ReflTransGen (PercStepIn C PercAdj4) u₀ z := by
    intro z ⟨u, hu, huz⟩
    have h1 : Relation.ReflTransGen (PercStepIn C PercAdj4) u₀ u :=
      percStepIn_mono (S' := C) (fun y hy => by
        simp only [hC, Set.mem_ofPred_eq]; exact ⟨y, hy, .refl⟩) (fun _ _ h => h) (hUc u₀ hu₀ u hu)
    have h2 := rtg_reach (S := W) (W := W) (fun _ h => h) huz
    exact h1.trans (percStepIn_mono (S' := C) (fun y hy => by
      simp only [hC, Set.mem_ofPred_eq]; exact ⟨u, hu, hy.2⟩) (fun _ _ h => h) h2)
  refine ⟨C, fun z hz => hCW z hz, fun x hx y hy =>
    (percStepIn_rev hsymm (hfrom x hx)).trans (hfrom y hy), ?_⟩
  intro d a ha₁ ha₂ hcol
  obtain ⟨u, hu, h⟩ := l53_col_reach n N hn hnN G U Box hU hsep d a ha₁ ha₂ (tb d)
    (htb d).1 (htb d).2 (hcolB d a ha₁ ha₂) hcol
  exact ⟨u, hu, h⟩

end LQGMetric.DZZ
