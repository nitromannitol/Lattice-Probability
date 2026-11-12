/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.Annulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.ExclusiveMain

/-!
# Square annuli of boxes: the four rectangles and crossings that must meet

The annulus of sites `{z : n ≤ ‖z‖_∞ ≤ N}` is the union of four rectangles `annRect n N d`
(`d = T, B, R, L`: top `n ≤ y`, bottom `n ≤ -y`, right `n ≤ x`, left `n ≤ -x`, inside the
box `‖z‖_∞ ≤ N`), each of size `(2N+1) × (N-n+1)`. `annRect_meet`: in each of them a
long-way `4`-crossing of sites of `A` and a short-way `*`-crossing of sites of `C` share a site.
It is `percGoodLR_meets_percBadTB` transported by the affine isometry
`annStd d : z ↦ (annLong d z + N, annDir d z - n)` onto the standard rectangle.
`perc_first_reach`: a path whose coordinate `h` goes from `≥ m` to `≤ m` in unit steps has an
initial segment staying in `{h ≥ m}` and ending on `{h = m}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

/-- Steps of a path inside `S` for the adjacency `adj`. -/
def PercStepIn (S : Set (ℤ × ℤ)) (adj : ℤ × ℤ → ℤ × ℤ → Prop) (x y : ℤ × ℤ) : Prop :=
  x ∈ S ∧ y ∈ S ∧ adj x y

lemma percStepIn_rev {S : Set (ℤ × ℤ)} {adj : ℤ × ℤ → ℤ × ℤ → Prop}
    (hs : ∀ x y, adj x y → adj y x) {a b : ℤ × ℤ}
    (h : Relation.ReflTransGen (PercStepIn S adj) a b) :
    Relation.ReflTransGen (PercStepIn S adj) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact Relation.ReflTransGen.head ⟨hst.2.1, hst.1, hs _ _ hst.2.2⟩ ih

lemma percStepIn_mono {S S' : Set (ℤ × ℤ)} {adj adj' : ℤ × ℤ → ℤ × ℤ → Prop}
    (hS : ∀ z, z ∈ S → z ∈ S') (ha : ∀ x y, adj x y → adj' x y) {a b : ℤ × ℤ}
    (h : Relation.ReflTransGen (PercStepIn S adj) a b) :
    Relation.ReflTransGen (PercStepIn S' adj') a b :=
  Relation.ReflTransGen.mono (r := PercStepIn S adj)
    (fun x y (hxy : PercStepIn S adj x y) =>
      (⟨hS x hxy.1, hS y hxy.2.1, ha x y hxy.2.2⟩ : PercStepIn S' adj' x y)) a b h

lemma percAdj4_symm {x y : ℤ × ℤ} (h : PercAdj4 x y) : PercAdj4 y x := by
  simp only [PercAdj4] at h ⊢; omega

lemma percAdjK_of_adj4 {x y : ℤ × ℤ} (h : PercAdj4 x y) : PercAdjK x y := by
  simp only [PercAdj4, PercAdjK] at h ⊢; omega

/-- First reach of the level `{h = m}` from `{h ≥ m}`. -/
lemma perc_first_reach {S : Set (ℤ × ℤ)} {adj : ℤ × ℤ → ℤ × ℤ → Prop} (h : ℤ × ℤ → ℤ)
    (hadj : ∀ x y, adj x y → h y ≤ h x + 1 ∧ h x ≤ h y + 1) (m : ℤ) {a b : ℤ × ℤ}
    (hab : Relation.ReflTransGen (PercStepIn S adj) a b) (ham : m ≤ h a) (hbm : h b ≤ m) :
    ∃ c, h c = m ∧ Relation.ReflTransGen (PercStepIn {z | z ∈ S ∧ m ≤ h z} adj) a c := by
  have key : (m ≤ h b ∧ Relation.ReflTransGen (PercStepIn {z | z ∈ S ∧ m ≤ h z} adj) a b) ∨
      ∃ c, h c = m ∧ Relation.ReflTransGen (PercStepIn {z | z ∈ S ∧ m ≤ h z} adj) a c := by
    clear hbm
    induction hab with
    | refl => exact Or.inl ⟨ham, .refl⟩
    | @tail z z' _ hst ih =>
      rcases ih with ⟨hz, hp⟩ | hr
      · have := hadj z z' hst.2.2
        by_cases hz' : m ≤ h z'
        · exact Or.inl ⟨hz', hp.tail ⟨⟨hst.1, hz⟩, ⟨hst.2.1, hz'⟩, hst.2.2⟩⟩
        · exact Or.inr ⟨z, by omega, hp⟩
      · exact Or.inr hr
  rcases key with ⟨hb, hp⟩ | hr
  · exact ⟨b, by omega, hp⟩
  · exact hr

/-- The four sides of a square annulus. -/
inductive PercDir
  | T
  | B
  | R
  | L

/-- The coordinate across side `d` (distance from the centre towards side `d`). -/
def annDir : PercDir → ℤ × ℤ → ℤ
  | .T, z => z.2
  | .B, z => -z.2
  | .R, z => z.1
  | .L, z => -z.1

/-- The coordinate along side `d`. -/
def annLong : PercDir → ℤ × ℤ → ℤ
  | .T, z => z.1
  | .B, z => z.1
  | .R, z => z.2
  | .L, z => z.2

/-- The box `‖z‖_∞ ≤ N`. -/
def annBox (N : ℤ) (z : ℤ × ℤ) : Prop := -N ≤ z.1 ∧ z.1 ≤ N ∧ -N ≤ z.2 ∧ z.2 ≤ N

/-- The rectangle of the annulus `n ≤ ‖z‖_∞ ≤ N` on side `d`. -/
def annRect (n N : ℤ) (d : PercDir) : Set (ℤ × ℤ) := {z | annBox N z ∧ n ≤ annDir d z}

/-- The affine isometry carrying `annRect n N d` onto the standard rectangle
`[0, 2N] × [0, N - n]`. -/
def annStd (n N : ℤ) (d : PercDir) (z : ℤ × ℤ) : ℤ × ℤ := (annLong d z + N, annDir d z - n)

lemma annStd_adj4 (n N : ℤ) (d : PercDir) {x y : ℤ × ℤ} (h : PercAdj4 x y) :
    PercAdj4 (annStd n N d x) (annStd n N d y) := by
  cases d <;> simp only [annStd, annLong, annDir, PercAdj4] at h ⊢ <;> omega

lemma annStd_adjK (n N : ℤ) (d : PercDir) {x y : ℤ × ℤ} (h : PercAdjK x y) :
    PercAdjK (annStd n N d x) (annStd n N d y) := by
  cases d <;> simp only [annStd, annLong, annDir, PercAdjK] at h ⊢ <;> omega

lemma annStd_inj (n N : ℤ) (d : PercDir) {x y : ℤ × ℤ}
    (h : annStd n N d x = annStd n N d y) : x = y := by
  rw [Prod.ext_iff] at h ⊢
  cases d <;> simp only [annStd, annLong, annDir] at h <;> omega

lemma annStd_grid (n N : ℤ) (d : PercDir) {z : ℤ × ℤ} (hz : z ∈ annRect n N d) :
    percInGrid (2 * N + 1) (N - n + 1) (annStd n N d z) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hz
  cases d <;> simp only [annStd, annLong, annDir, percInGrid] at h5 ⊢ <;> omega

lemma annDir_adjK (d : PercDir) {x y : ℤ × ℤ} (h : PercAdjK x y) :
    annDir d y ≤ annDir d x + 1 ∧ annDir d x ≤ annDir d y + 1 := by
  cases d <;> simp only [annDir, PercAdjK] at h ⊢ <;> omega

/-- In a rectangle of the annulus, a long-way `4`-crossing of sites of `A` and a short-way
`*`-crossing of sites of `C` share a site. -/
theorem annRect_meet (n N : ℤ) (d : PercDir) (A C : Set (ℤ × ℤ))
    (hA : ∃ a b, annLong d a = -N ∧ annLong d b = N ∧ a ∈ annRect n N d ∧ a ∈ A ∧
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ A} PercAdj4) a b)
    (hC : ∃ c e, annDir d c = N ∧ annDir d e = n ∧ c ∈ annRect n N d ∧ c ∈ C ∧
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ C} PercAdjK) c e) :
    ∃ z, z ∈ annRect n N d ∧ z ∈ A ∧ z ∈ C := by
  classical
  set φ := annStd n N d
  obtain ⟨a, b, ha, hb, haX, haA, hab⟩ := hA
  obtain ⟨c, e, hc, he, hcX, hcC, hce⟩ := hC
  set A' : Set (ℤ × ℤ) := φ '' {z | z ∈ annRect n N d ∧ z ∈ A}
  set C' : Set (ℤ × ℤ) := φ '' {z | z ∈ annRect n N d ∧ z ∈ C}
  obtain ⟨z', hz'g, ⟨z1, ⟨hz1X, hz1A⟩, hz1⟩, ⟨z2, ⟨hz2X, hz2C⟩, hz2⟩⟩ :=
    percGoodLR_meets_percBadTB (K := 2 * N + 1) (L := N - n + 1) A' C' (by
      refine ⟨φ a, φ b, ?_, ?_, annStd_grid n N d haX, ⟨a, ⟨haX, haA⟩, rfl⟩, ?_⟩
      · simp only [φ, annStd, ha]; omega
      · simp only [φ, annStd, hb]; omega
      · refine Relation.ReflTransGen.lift φ (fun x y hxy => ?_) _ _ hab
        obtain ⟨hx, hy, hxy⟩ := hxy
        exact ⟨annStd_grid n N d hx.1, ⟨x, hx, rfl⟩, annStd_grid n N d hy.1, ⟨y, hy, rfl⟩,
          annStd_adj4 n N d hxy⟩) (by
      refine ⟨φ c, φ e, ?_, ?_, annStd_grid n N d hcX, not_not.mpr ⟨c, ⟨hcX, hcC⟩, rfl⟩, ?_⟩
      · simp only [φ, annStd, hc]; omega
      · simp only [φ, annStd, he]; omega
      · refine Relation.ReflTransGen.lift φ (fun x y hxy => ?_) _ _ hce
        obtain ⟨hx, hy, hxy⟩ := hxy
        exact ⟨annStd_grid n N d hx.1, not_not.mpr ⟨x, hx, rfl⟩, annStd_grid n N d hy.1,
          not_not.mpr ⟨y, hy, rfl⟩, annStd_adjK n N d hxy⟩)
  have : z1 = z2 := annStd_inj n N d (hz1.trans hz2.symm)
  subst this
  exact ⟨z1, hz1X, hz1A, hz2C⟩

end LQGMetric
