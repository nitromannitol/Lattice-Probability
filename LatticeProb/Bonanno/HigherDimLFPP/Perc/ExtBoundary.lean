/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Perc.ExtBoundary at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Poincare

/-!
# Exterior-boundary connectivity in `ℤ^d` (HA5 D7(ii))

Let `F ⊆ [-R, R]^d` be finite, nonempty and `*`-connected, `Ext R F` its exterior (the sites joined
to `(R+1, …, R+1)` by an L-path avoiding `F`) and `B = {y ∈ Ext R F : y is *-adjacent to F}` its
exterior boundary. Then `B` is L-connected (`extBoundaryConn`). No hypothesis on `d` is needed
(for `d = 0` the set `B` is empty).

Proof (HA5 D7(ii)). Fix `y₁ ∈ B` and let `Γ` be its L-component in `B`. Put `ω({a, b}) = 1` iff one
of `a, b` is in `F` and the other in `Γ` (`bdryEdge`).

* Edge identity (`bdryEdge_eq_of_near`): on an L-edge `{a, b}` both of whose endpoints are within
  `ℓ^∞`-distance `1` of a site of `F`, `ω({a, b}) = 1_Γ(a) + 1_Γ(b)`. (Every endpoint outside `F` is
  then in `B`, and an L-neighbour in `B` of a site of `Γ` is in `Γ`.) This replaces HA5's counting
  of maximal runs of exterior sites around a plaquette or along a short path: both arguments say
  that `φ + 1_Γ` is constant along such edges.
* Plaquettes: a unit square with a vertex in `F` has all four edges of this kind, so its
  `ω`-sum is `2 ∑ 1_Γ = 0`; a square without a vertex in `F` has `ω = 0` on all its edges.
* By the Poincaré lemma (`poincareMod2`) take `φ` with `dφ = ω`.
* `φ` is constant on `F`: for `*`-adjacent `f, f' ∈ F` the coordinate path from `f` to `f'` stays in
  the unit cube of `f` and `f'`, so `φ + 1_Γ` is constant along it; `1_Γ = 0` on `F`, and `F` is
  `*`-connected.
* `φ` is constant on `Ext R F` (edges outside `F` have `ω = 0`; every exterior site is joined to the
  base point outside `F`).
* Every `y ∈ B` is joined inside `B` to a site L-adjacent to `F` (first site of `F` on the
  coordinate path from `y` to a `*`-neighbour in `F`). If some `y₂ ∈ B` is not in `Γ`, this gives
  `y₀ ∈ Γ`, `y₀' ∈ B ∖ Γ` and `f₀, f₀' ∈ F` with `y₀ ~ f₀`, `y₀' ~ f₀'`, hence
  `φ(y₀) = φ(f₀) + 1 ≠ φ(f₀') = φ(y₀')`, contradicting the constancy of `φ` on `Ext R F`.
-/

set_option autoImplicit false

open Relation

namespace HigherDimLFPP

namespace Perc

variable {d : ℕ}

/-! ### The boundary cochain -/

open Classical in
/-- The indicator of `Γ` with values in `ℤ/2`. -/
noncomputable def indZ2 (Γ : Set (Zd d)) (y : Zd d) : ZMod 2 := if y ∈ Γ then 1 else 0

open Classical in
/-- The edge weight `ω({a, b}) = 1` iff one endpoint is in `F` and the other in `Γ`. -/
noncomputable def bdryEdge (F Γ : Set (Zd d)) (a b : Zd d) : ZMod 2 :=
  if (a ∈ F ∧ b ∈ Γ) ∨ (a ∈ Γ ∧ b ∈ F) then 1 else 0

lemma bdryEdge_comm (F Γ : Set (Zd d)) (a b : Zd d) : bdryEdge F Γ a b = bdryEdge F Γ b a := by
  unfold bdryEdge
  congr 1
  exact propext ⟨fun h => h.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩),
    fun h => h.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩

lemma bdryEdge_of_notMem {F Γ : Set (Zd d)} {a b : Zd d} (ha : a ∉ F) (hb : b ∉ F) :
    bdryEdge F Γ a b = 0 := by
  unfold bdryEdge
  split_ifs with h
  · rcases h with h | h
    · exact absurd h.1 ha
    · exact absurd h.2 hb
  · rfl

lemma bdryEdge_eq_one {F Γ : Set (Zd d)} {a b : Zd d} (ha : a ∈ F) (hb : b ∈ Γ) :
    bdryEdge F Γ a b = 1 := by
  unfold bdryEdge
  split_ifs with h
  · rfl
  · exact absurd (Or.inl ⟨ha, hb⟩) h

lemma bdryEdge_eq_zero {F Γ : Set (Zd d)} {a b : Zd d} (haΓ : a ∉ Γ) (hbΓ : b ∉ Γ) :
    bdryEdge F Γ a b = 0 := by
  unfold bdryEdge
  split_ifs with h
  · rcases h with h | h
    · exact absurd h.2 hbΓ
    · exact absurd h.1 haΓ
  · rfl

/-- On a "good" edge the weight is the coboundary of the indicator of `Γ`. -/
lemma bdryEdge_eq_ind {F Γ : Set (Zd d)} (hΓF : ∀ y ∈ Γ, y ∉ F) {a b : Zd d}
    (h1 : a ∈ Γ → b ∈ F ∨ b ∈ Γ) (h2 : b ∈ Γ → a ∈ F ∨ a ∈ Γ) :
    bdryEdge F Γ a b = indZ2 Γ a + indZ2 Γ b := by
  classical
  unfold bdryEdge indZ2
  by_cases ha : a ∈ Γ <;> by_cases hb : b ∈ Γ
  · have haF := hΓF a ha
    have hbF := hΓF b hb
    simp only [ha, hb, haF, hbF, and_true, and_false, or_self, ↓reduceIte]
    decide
  · have haF := hΓF a ha
    rcases h1 ha with hbF | hbΓ
    · simp only [ha, hb, haF, hbF, and_true, and_false, or_true, ↓reduceIte]
      decide
    · exact absurd hbΓ hb
  · have hbF := hΓF b hb
    rcases h2 hb with haF | haΓ
    · simp only [ha, hb, haF, hbF, and_true, and_false, true_or, ↓reduceIte]
      decide
    · exact absurd haΓ ha
  · simp only [ha, hb, and_false, false_and, or_self, ↓reduceIte]
    decide

/-! ### Unit cells -/

/-- `v` lies in the unit cell `x + [0, 1]^d`. -/
def InCell (x v : Zd d) : Prop := ∀ k, x k ≤ v k ∧ v k ≤ x k + 1

lemma InCell.withinInf {x v w : Zd d} (hv : InCell x v) (hw : InCell x w) : WithinInf 1 v w := by
  intro k
  have h1 := hv k
  have h2 := hw k
  rw [abs_le]
  constructor <;> omega

lemma inCell_self (x : Zd d) : InCell x x := fun _ => ⟨le_rfl, by omega⟩

lemma inCell_add_single (x : Zd d) (i : Fin d) : InCell x (x + Pi.single i 1) := by
  intro k
  rw [add_single_apply]
  split_ifs <;> omega

lemma inCell_add_single_add_single (x : Zd d) {i j : Fin d} (hij : i ≠ j) :
    InCell x (x + Pi.single i 1 + Pi.single j 1) := by
  intro k
  rw [add_single_apply, add_single_apply]
  by_cases hkj : k = j
  · subst hkj
    have hki : k ≠ i := Ne.symm hij
    simp only [hki, ↓reduceIte]
    omega
  · simp only [hkj, ↓reduceIte]
    split_ifs <;> omega

/-! ### The theorem -/

/-- A site of the exterior boundary is not in `F`. -/
lemma notMem_of_mem_extBdry {R : ℤ} {F : Set (Zd d)} (hF : ∀ x ∈ F, WithinInf R x 0) {y : Zd d}
    (hy : y ∈ {y | y ∈ Ext R F ∧ ∃ f ∈ F, SAdj y f}) : y ∉ F := by
  obtain ⟨hyE, f, -, hyf⟩ := hy
  obtain ⟨i, -⟩ := Function.ne_iff.mp hyf.ne
  exact notMem_of_mem_ext hF i hyE

/-- **D7(ii): exterior-boundary connectivity** (for every `d`). -/
theorem extBoundaryConn (d : ℕ) : ExtBoundaryConn d := by
  intro R F _ _ hFbox hFconn
  classical
  set B : Set (Zd d) := {y | y ∈ Ext R F ∧ ∃ f ∈ F, SAdj y f} with hBdef
  intro y₁ hy₁ y₂ hy₂
  set Γ : Set (Zd d) := {y | ReflTransGen (StepIn B LAdj) y₁ y} with hΓdef
  -- basic facts
  obtain ⟨i₀, -⟩ := Function.ne_iff.mp hy₁.2.choose_spec.2.ne
  have hExtF : ∀ y ∈ Ext R F, y ∉ F := fun y hy => notMem_of_mem_ext hFbox i₀ hy
  have hBF : ∀ y ∈ B, y ∉ F := fun y hy => hExtF y hy.1
  have hΓB : ∀ y ∈ Γ, y ∈ B := fun y hy => mem_of_reflTransGen_stepIn hy hy₁
  have hΓF : ∀ y ∈ Γ, y ∉ F := fun y hy => hBF y (hΓB y hy)
  have hΓclos : ∀ y ∈ Γ, ∀ z ∈ B, LAdj y z → z ∈ Γ := fun y hy z hz hyz =>
    ReflTransGen.tail hy ⟨hΓB y hy, hz, hyz⟩
  have hExtStep : ∀ a b, a ∈ Ext R F → b ∉ F → LAdj a b → b ∈ Ext R F := fun a b ha hb hab =>
    mem_ext_of_lAdj hb (hExtF a ha) hab.symm ha
  -- the edge identity near `F`
  have hnear : ∀ f ∈ F, ∀ a b, WithinInf 1 a f → WithinInf 1 b f → LAdj a b →
      bdryEdge F Γ a b = indZ2 Γ a + indZ2 Γ b := by
    intro f hf a b ha hb hab
    have hgood : ∀ u v, WithinInf 1 v f → LAdj u v → u ∈ Γ → v ∈ F ∨ v ∈ Γ := by
      intro u v hv huv hu
      by_cases hvF : v ∈ F
      · exact Or.inl hvF
      · right
        have hvE : v ∈ Ext R F := hExtStep u v (hΓB u hu).1 hvF huv
        have hvB : v ∈ B := ⟨hvE, f, hf, sAdj_of_withinInf (fun h => hvF (h ▸ hf)) hv⟩
        exact hΓclos u hu v hvB huv
    exact bdryEdge_eq_ind hΓF (hgood a b hb hab) (hgood b a ha hab.symm)
  -- the cochain and the plaquette condition
  set ω : Zd d → Fin d → ZMod 2 := fun x i => bdryEdge F Γ x (x + Pi.single i 1) with hωdef
  have hplaq : ∀ x i j, ω x i + ω (x + Pi.single i 1) j + ω (x + Pi.single j 1) i + ω x j = 0 := by
    intro x i j
    simp only [hωdef]
    by_cases hij : i = j
    · subst hij
      generalize bdryEdge F Γ x (x + Pi.single i 1) = A
      generalize bdryEdge F Γ (x + Pi.single i 1) (x + Pi.single i 1 + Pi.single i 1) = A'
      revert A A'; decide
    · rw [show x + Pi.single j 1 + Pi.single i 1 = x + Pi.single i 1 + Pi.single j 1 from
        add_right_comm _ _ _]
      set v₀ := x
      set v₁ := x + Pi.single i 1
      set v₂ := x + Pi.single i 1 + Pi.single j 1
      set v₃ := x + Pi.single j 1
      have c₀ : InCell x v₀ := inCell_self x
      have c₁ : InCell x v₁ := inCell_add_single x i
      have c₂ : InCell x v₂ := inCell_add_single_add_single x hij
      have c₃ : InCell x v₃ := inCell_add_single x j
      have l₀₁ : LAdj v₀ v₁ := lAdj_add_single x i
      have l₁₂ : LAdj v₁ v₂ := lAdj_add_single _ j
      have l₃₂ : LAdj v₃ v₂ := by
        have := lAdj_add_single (x + Pi.single j 1) i
        rwa [add_right_comm] at this
      have l₀₃ : LAdj v₀ v₃ := lAdj_add_single x j
      by_cases hF : ∃ f ∈ F, InCell x f
      · obtain ⟨f, hf, cf⟩ := hF
        rw [hnear f hf v₀ v₁ (c₀.withinInf cf) (c₁.withinInf cf) l₀₁,
          hnear f hf v₁ v₂ (c₁.withinInf cf) (c₂.withinInf cf) l₁₂,
          hnear f hf v₃ v₂ (c₃.withinInf cf) (c₂.withinInf cf) l₃₂,
          hnear f hf v₀ v₃ (c₀.withinInf cf) (c₃.withinInf cf) l₀₃]
        generalize indZ2 Γ v₀ = a₀
        generalize indZ2 Γ v₁ = a₁
        generalize indZ2 Γ v₂ = a₂
        generalize indZ2 Γ v₃ = a₃
        revert a₀ a₁ a₂ a₃; decide
      · push Not at hF
        have n₀ : v₀ ∉ F := fun h => hF v₀ h c₀
        have n₁ : v₁ ∉ F := fun h => hF v₁ h c₁
        have n₂ : v₂ ∉ F := fun h => hF v₂ h c₂
        have n₃ : v₃ ∉ F := fun h => hF v₃ h c₃
        rw [bdryEdge_of_notMem n₀ n₁, bdryEdge_of_notMem n₁ n₂, bdryEdge_of_notMem n₃ n₂,
          bdryEdge_of_notMem n₀ n₃]
        decide
  obtain ⟨φ, hφ⟩ := poincareMod2 d ω hplaq
  -- `φ` along an L-edge
  have hedge : ∀ a b, LAdj a b → φ b = φ a + bdryEdge F Γ a b := by
    intro a b hab
    obtain ⟨i, hi | hi⟩ := hab.exists_eq_add_single
    · subst hi
      have := hφ a i
      simp only [hωdef] at this
      rw [← this]
      ring
    · subst hi
      have := hφ b i
      simp only [hωdef] at this
      rw [bdryEdge_comm, ← this]
      generalize φ b = P
      generalize φ (b + Pi.single i 1) = Q
      revert P Q; decide
  -- `φ` is constant on `Ext R F`
  have hφExt : ∀ y ∈ Ext R F, φ y = φ (fun _ => R + 1) := by
    intro y hy
    induction hy using ReflTransGen.head_induction_on with
    | refl => rfl
    | head hac _ ih =>
      rw [← ih, hedge _ _ hac.2.2, bdryEdge_of_notMem hac.1 hac.2.1, add_zero]
  -- `φ` is constant on `F`
  have hφF1 : ∀ f ∈ F, ∀ f' ∈ F, SAdj f f' → φ f = φ f' := by
    intro f hf f' hf' hff'
    have hpath := reflTransGen_cube hff'.withinInf
    have key : ∀ z, ReflTransGen (StepIn (cube f f') LAdj) f z →
        φ z + indZ2 Γ z = φ f + indZ2 Γ f := by
      intro z hz
      induction hz with
      | refl => rfl
      | @tail b c _ hbc ih =>
        rw [← ih, hedge b c hbc.2.2,
          hnear f hf b c (withinInf_of_mem_cube hff'.withinInf hbc.1).1
            (withinInf_of_mem_cube hff'.withinInf hbc.2.1).1 hbc.2.2]
        generalize φ b = P
        generalize indZ2 Γ b = Q
        generalize indZ2 Γ c = U
        revert P Q U; decide
    have := key f' hpath
    have h1 : indZ2 Γ f = 0 := by
      unfold indZ2
      simp only [show f ∉ Γ from fun h => hΓF f h hf, ↓reduceIte]
    have h2 : indZ2 Γ f' = 0 := by
      unfold indZ2
      simp only [show f' ∉ Γ from fun h => hΓF f' h hf', ↓reduceIte]
    rw [h1, h2, add_zero, add_zero] at this
    exact this.symm
  have hφF : ∀ f ∈ F, ∀ f' ∈ F, φ f = φ f' := by
    intro f hf f' hf'
    have hp := hFconn f hf f' hf'
    induction hp with
    | refl => rfl
    | tail _ hbc ih => exact (ih hbc.1).trans (hφF1 _ hbc.1 _ hbc.2.1 hbc.2.2)
  -- every site of `B` is joined inside `B` to a site L-adjacent to `F`
  have hstep0 : ∀ y ∈ B, ∃ y₀, ReflTransGen (StepIn B LAdj) y y₀ ∧ ∃ f₀ ∈ F, LAdj y₀ f₀ := by
    intro y hy
    obtain ⟨f, hf, hyf⟩ := hy.2
    have hpath := reflTransGen_cube hyf.withinInf
    have key : ∀ z, ReflTransGen (StepIn (cube y f) LAdj) z f → z ∈ B →
        ∃ y₀, ReflTransGen (StepIn B LAdj) z y₀ ∧ ∃ f₀ ∈ F, LAdj y₀ f₀ := by
      intro z hz
      induction hz using ReflTransGen.head_induction_on with
      | refl => intro hfB; exact absurd hf (hBF f hfB)
      | @head a c hac _ ih =>
        intro haB
        by_cases hcF : c ∈ F
        · exact ⟨a, ReflTransGen.refl, c, hcF, hac.2.2⟩
        · have hcE : c ∈ Ext R F := hExtStep a c haB.1 hcF hac.2.2
          have hcB : c ∈ B := ⟨hcE, f, hf, sAdj_of_withinInf (fun h => hcF (h ▸ hf))
            (withinInf_of_mem_cube hyf.withinInf hac.2.1).2⟩
          obtain ⟨y₀, hcy₀, hy₀⟩ := ih hcB
          exact ⟨y₀, ReflTransGen.head ⟨haB, hcB, hac.2.2⟩ hcy₀, hy₀⟩
    exact key y hpath hy
  -- conclusion
  show y₂ ∈ Γ
  by_contra hy₂Γ
  obtain ⟨y₀, h₁₀, f₀, hf₀, hy₀f₀⟩ := hstep0 y₁ hy₁
  obtain ⟨y₀', h₂₀, f₀', hf₀', hy₀f₀'⟩ := hstep0 y₂ hy₂
  have hy₀Γ : y₀ ∈ Γ := h₁₀
  have hy₀'B : y₀' ∈ B := mem_of_reflTransGen_stepIn h₂₀ hy₂
  have hy₀'Γ : y₀' ∉ Γ := by
    intro h
    exact hy₂Γ (ReflTransGen.trans h (reflTransGen_lAdj_symm h₂₀))
  have e1 : φ y₀ = φ f₀ + 1 := by
    rw [hedge f₀ y₀ hy₀f₀.symm, bdryEdge_eq_one hf₀ hy₀Γ]
  have e2 : φ y₀' = φ f₀' := by
    rw [hedge f₀' y₀' hy₀f₀'.symm, bdryEdge_eq_zero (fun h => hΓF f₀' h hf₀') hy₀'Γ, add_zero]
  have e3 : φ y₀ = φ y₀' := by
    rw [hφExt y₀ (hΓB y₀ hy₀Γ).1, hφExt y₀' hy₀'B.1]
  have e4 : φ f₀ = φ f₀' := hφF f₀ hf₀ f₀' hf₀'
  rw [e1, e2, ← e4] at e3
  generalize φ f₀ = P at e3
  revert P; decide

end Perc

end HigherDimLFPP
