/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR3Defs
import Mathlib.Topology.Order.IntermediateValue

/-!
# EXT-CA node R6: structure of the boundary map on the swallowed interval

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R6** (simplified route of task CA-R/C1).
Let `F` be a boundary extension `RevExt W T γ F` of a simple reverse hull `γ '' Ioc 0 1`, with
`F 0 = γ 1` (the tip), and `a < 0 < b` the two real zeros of `F` bounding the interval where `F`
leaves `ℝ`. Then `F` maps `(a,b)` into `γ (0,1]`, is injective on `[a,0]` and on `[0,b]`, and the
two branches have the same image (`F '' [a,0] ⊆ F '' [0,b]`).

This is pure topology on `ℝ`, using only the fields of `RevExt` (the fold lemma and the
injectivity facts, Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Prop. 2.5 and
Thm 2.6, pp. 23–24, packaged in `RevExt`), the intermediate value theorem and connectedness of
intervals. The combinatorial argument is an own elementary proof (following the task plan; the
blueprint's R6 uses `γ⁻¹ ∘ F`, here replaced by a closed-cover connectedness argument).
-/

noncomputable section

open Set Filter Topology

namespace QuantumZipper

namespace CaraR

lemma r6_cont {W : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} {F : ℂ → ℂ} (hF : RevExt W T γ F) :
    Continuous (fun x : ℝ => F x) :=
  hF.cont.comp_continuous Complex.continuous_ofReal (fun x => by simp [Hbar])

lemma r6_exists_pos {F : ℂ → ℂ} (hc : Continuous (fun x : ℝ => F x)) {b : ℝ} (hb : F b = 0)
    (hright : ∀ x : ℝ, b < x → (F x).im = 0 ∧ 0 < (F x).re)
    (htop : Tendsto (fun x : ℝ => (F x).re) atTop atTop) {p : ℝ} (hp : 0 < p) :
    ∃ x : ℝ, b < x ∧ F x = p := by
  obtain ⟨X, hX⟩ := ((htop.eventually (eventually_ge_atTop p)).and (eventually_ge_atTop b)).exists
  have hsub := intermediate_value_Icc hX.2 (Complex.continuous_re.comp hc).continuousOn
  have hmem : p ∈ Icc ((fun x : ℝ => (F x).re) b) ((fun x : ℝ => (F x).re) X) :=
    ⟨by simp only [hb, Complex.zero_re]; exact hp.le, hX.1⟩
  obtain ⟨x, hx, hxp⟩ := hsub hmem
  simp only [Function.comp_apply] at hxp
  have hxb : b < x := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; rw [hb, Complex.zero_re] at hxp; linarith
    · exact h
  exact ⟨x, hxb, Complex.ext (by simpa using hxp) (by simp [(hright x hxb).1])⟩

lemma r6_exists_neg {F : ℂ → ℂ} (hc : Continuous (fun x : ℝ => F x)) {a : ℝ} (ha : F a = 0)
    (hleft : ∀ x : ℝ, x < a → (F x).im = 0 ∧ (F x).re < 0)
    (hbot : Tendsto (fun x : ℝ => (F x).re) atBot atBot) {p : ℝ} (hp : p < 0) :
    ∃ x : ℝ, x < a ∧ F x = p := by
  obtain ⟨X, hX⟩ := ((hbot.eventually (eventually_le_atBot p)).and (eventually_le_atBot a)).exists
  have hsub := intermediate_value_Icc hX.2 (Complex.continuous_re.comp hc).continuousOn
  have hmem : p ∈ Icc ((fun x : ℝ => (F x).re) X) ((fun x : ℝ => (F x).re) a) :=
    ⟨hX.1, by simp only [ha, Complex.zero_re]; exact hp.le⟩
  obtain ⟨x, hx, hxp⟩ := hsub hmem
  simp only [Function.comp_apply] at hxp
  have hxa : x < a := by
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h; rw [ha, Complex.zero_re] at hxp; linarith
    · exact h
  exact ⟨x, hxa, Complex.ext (by simpa using hxp) (by simp [(hleft x hxa).1])⟩

/-- Step 2: on `[a,b]`, `F` takes values in the arc `γ [0,1]`. -/
lemma r6_mem_arc {W : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} {F : ℂ → ℂ} (hF : RevExt W T γ F)
    (hγ0 : γ 0 = 0) {a b : ℝ} (ha : F a = 0) (hb : F b = 0)
    (hleft : ∀ x : ℝ, x < a → (F x).im = 0 ∧ (F x).re < 0)
    (hright : ∀ x : ℝ, b < x → (F x).im = 0 ∧ 0 < (F x).re)
    (htop : Tendsto (fun x : ℝ => (F x).re) atTop atTop)
    (hbot : Tendsto (fun x : ℝ => (F x).re) atBot atBot) {y : ℝ} (hy : y ∈ Icc a b) :
    F y ∈ γ '' Icc 0 1 := by
  rcases hF.bdry y with h | h
  · by_cases h0 : F y = 0
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hγ0, h0]⟩
    · exfalso
      have hre : F y = ((F y).re : ℂ) := Complex.ext (by simp) (by simp [h])
      have hre0 : (F y).re ≠ 0 := fun h' => h0 (by rw [hre, h', Complex.ofReal_zero])
      have hq : F y ≠ γ 0 := by rw [hγ0]; exact h0
      rcases lt_or_gt_of_ne hre0 with hn | hp
      · obtain ⟨x, hxa, hx⟩ := r6_exists_neg (r6_cont hF) ha hleft hbot hn
        have := hF.inj_real (F y) h hq x y (by rw [hx, ← hre]) rfl
        subst this; linarith [hy.1]
      · obtain ⟨x, hxb, hx⟩ := r6_exists_pos (r6_cont hF) hb hright htop hp
        have := hF.inj_real (F y) h hq x y (by rw [hx, ← hre]) rfl
        subst this; linarith [hy.2]
  · exact h

lemma r6_fold_excl {W : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} {F : ℂ → ℂ} (hF : RevExt W T γ F)
    {x y : ℝ} (hxy : x < y) {q : ℂ} (hx : F x = q) (hy : F y = q) {Z : Set ℂ}
    (hZ : Z ⊆ {p : ℂ | p.im = 0 ∨ p ∈ γ '' Icc 0 1} \ {q}) (hZc : IsPreconnected Z) {s : ℝ}
    (hs : s ∉ Icc x y) (hsZ : F s ∈ Z) : ∀ t ∈ Ioo x y, F t ∉ Z :=
  (hF.fold x y hxy q hx hy Z hZ hZc).resolve_right (fun h => h s hs hsZ)

lemma r6_gamma_ne_zero {γ : ℝ → ℂ} (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) {u : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) 1) : γ u ≠ 0 := by
  intro h
  have := (hγH u hu : 0 < (γ u).im)
  rw [h] at this; simp [H] at this

/-- Step 3: `F` has no zeros in `(a,b)`. -/
lemma r6_no_zero {W : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1))
    (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) {F : ℂ → ℂ}
    (hF : RevExt W T γ F) (hγ0 : γ 0 = 0) (htip : F 0 = γ 1) {a b : ℝ}
    (ha : F a = 0) (hb : F b = 0)
    (hleft : ∀ x : ℝ, x < a → (F x).im = 0 ∧ (F x).re < 0)
    (hright : ∀ x : ℝ, b < x → (F x).im = 0 ∧ 0 < (F x).re)
    (htop : Tendsto (fun x : ℝ => (F x).re) atTop atTop)
    (hbot : Tendsto (fun x : ℝ => (F x).re) atBot atBot) {y : ℝ} (hy : y ∈ Ioo a b) :
    F y ≠ 0 := by
  intro hFy
  have hZc : IsPreconnected (γ '' Ioc 0 1) :=
    isPreconnected_Ioc.image _ (hγc.mono Ioc_subset_Icc_self)
  have hZ : γ '' Ioc 0 1 ⊆ {p : ℂ | p.im = 0 ∨ p ∈ γ '' Icc 0 1} \ {0} := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨Or.inr ⟨u, Ioc_subset_Icc_self hu, rfl⟩,
      fun h => r6_gamma_ne_zero hγH hu (Set.mem_singleton_iff.mp h)⟩
  have h0Z : F ((0 : ℝ) : ℂ) ∈ γ '' Ioc 0 1 := by
    rw [Complex.ofReal_zero, htip]; exact ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩
  have harc := fun t (ht : t ∈ Icc a b) =>
    r6_mem_arc hF hγ0 ha hb hleft hright htop hbot ht
  rcases lt_trichotomy y 0 with hneg | hzero | hpos
  · have hex := r6_fold_excl hF hy.1 ha hFy hZ hZc (s := 0) (fun h => by linarith [h.2]) h0Z
    apply hF.noConst a y hy.1 0
    intro t ht
    obtain ⟨u, hu, hut⟩ := harc t ⟨ht.1.le, by linarith [ht.2, hy.2]⟩
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← hut, ← h, hγ0]
    · exact absurd ⟨u, ⟨h, hu.2⟩, hut⟩ (hex t ht)
  · subst hzero
    rw [Complex.ofReal_zero, htip] at hFy
    exact r6_gamma_ne_zero hγH ⟨one_pos, le_rfl⟩ hFy
  · have hex := r6_fold_excl hF hy.2 hFy hb hZ hZc (s := 0) (fun h => by linarith [h.1]) h0Z
    apply hF.noConst y b hy.2 0
    intro t ht
    obtain ⟨u, hu, hut⟩ := harc t ⟨by linarith [ht.1, hy.1], ht.2.le⟩
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← hut, ← h, hγ0]
    · exact absurd ⟨u, ⟨h, hu.2⟩, hut⟩ (hex t ht)

/-- Step 4, core: two points of `[a,b]` with a common value `q ∉ {0, γ 1}` cannot bound an
interval avoiding `0` (fold lemma applied to `γ (t,1]` and to `γ [0,t) ∪ ℝ`). -/
lemma r6_no_pair_core {W : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) {F : ℂ → ℂ}
    (hF : RevExt W T γ F) (hγ0 : γ 0 = 0) (htip : F 0 = γ 1) {a b : ℝ}
    (ha : F a = 0) (hb : F b = 0)
    (hleft : ∀ x : ℝ, x < a → (F x).im = 0 ∧ (F x).re < 0)
    (hright : ∀ x : ℝ, b < x → (F x).im = 0 ∧ 0 < (F x).re)
    (htop : Tendsto (fun x : ℝ => (F x).re) atTop atTop)
    (hbot : Tendsto (fun x : ℝ => (F x).re) atBot atBot) {x y : ℝ} (hxy : x < y)
    (hxI : x ∈ Icc a b) (hyI : y ∈ Icc a b) (hFxy : F x = F y) (hq0 : F x ≠ 0)
    (hq1 : F x ≠ γ 1) (h0 : (0 : ℝ) ∉ Icc x y) : False := by
  obtain ⟨t, ht, hqt⟩ := r6_mem_arc hF hγ0 ha hb hleft hright htop hbot hxI
  have ht0 : t ≠ 0 := fun h => hq0 (by rw [← hqt, h, hγ0])
  have ht1 : t ≠ 1 := fun h => hq1 (by rw [← hqt, h])
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  -- the upper part `γ (t,1]`
  have hsubU : γ '' Ioc t 1 ⊆ {p : ℂ | p.im = 0 ∨ p ∈ γ '' Icc 0 1} \ {F x} := by
    rintro _ ⟨u, hu, rfl⟩
    have huI : u ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hu.1.le, hu.2⟩
    exact ⟨Or.inr ⟨u, huI, rfl⟩, fun h =>
      hu.1.ne' (hγi huI ht ((Set.mem_singleton_iff.mp h).trans hqt.symm))⟩
  have hpreU : IsPreconnected (γ '' Ioc t 1) :=
    isPreconnected_Ioc.image _ (hγc.mono fun u hu => ⟨ht.1.trans hu.1.le, hu.2⟩)
  have hmemU : F ((0 : ℝ) : ℂ) ∈ γ '' Ioc t 1 := by
    rw [Complex.ofReal_zero, htip]; exact ⟨1, ⟨ht'.2, le_rfl⟩, rfl⟩
  have hup := r6_fold_excl hF hxy rfl hFxy.symm hsubU hpreU h0 hmemU
  -- the lower part `γ [0,t) ∪ ℝ`
  have hsubD : γ '' Ico 0 t ∪ range (fun r : ℝ => (r : ℂ)) ⊆
      {p : ℂ | p.im = 0 ∨ p ∈ γ '' Icc 0 1} \ {F x} := by
    rintro p (⟨u, hu, rfl⟩ | ⟨r, rfl⟩)
    · have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.le.trans ht.2⟩
      exact ⟨Or.inr ⟨u, huI, rfl⟩, fun h =>
        hu.2.ne (hγi huI ht ((Set.mem_singleton_iff.mp h).trans hqt.symm))⟩
    · refine ⟨Or.inl (Complex.ofReal_im r), fun h => ?_⟩
      have him := (hγH t ⟨ht'.1, ht.2⟩ : 0 < (γ t).im)
      rw [hqt, ← Set.mem_singleton_iff.mp h] at him
      simp [H] at him
  have hpreD : IsPreconnected (γ '' Ico 0 t ∪ range (fun r : ℝ => (r : ℂ))) :=
    IsPreconnected.union 0 ⟨0, ⟨le_rfl, ht'.1⟩, hγ0⟩ ⟨0, Complex.ofReal_zero⟩
      (isPreconnected_Ico.image _ (hγc.mono fun u hu => ⟨hu.1, hu.2.le.trans ht.2⟩))
      (isPreconnected_range Complex.continuous_ofReal)
  obtain ⟨v, hvb, hvy⟩ : ∃ v : ℝ, b < v ∧ y < v := ⟨b + 1, by linarith, by linarith [hyI.2]⟩
  have hvre := (hright v hvb).1
  have hmemD : F v ∈ γ '' Ico 0 t ∪ range (fun r : ℝ => (r : ℂ)) :=
    Or.inr ⟨(F v).re, Complex.ext (by simp) (by simp [hvre])⟩
  have hdown := r6_fold_excl hF hxy rfl hFxy.symm hsubD hpreD
    (fun h => by linarith [h.2]) hmemD
  apply hF.noConst x y hxy (F x)
  intro s hs
  rcases hF.bdry s with hr | ⟨u, hu, hus⟩
  · exact absurd (Or.inr ⟨(F s).re, Complex.ext (by simp) (by simp [hr])⟩) (hdown s hs)
  · rcases lt_trichotomy u t with h | h | h
    · exact absurd (Or.inl ⟨u, ⟨hu.1, h⟩, hus⟩) (hdown s hs)
    · rw [← hus, h, hqt]
    · exact absurd ⟨u, ⟨h, hu.2⟩, hus⟩ (hup s hs)

/-- Step 5: every point of the arc `γ [0,1]` is attained on `[0,b]`. -/
lemma r6_surj_right {W : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) {F : ℂ → ℂ}
    (hF : RevExt W T γ F) (hγ0 : γ 0 = 0) (htip : F 0 = γ 1) {a b : ℝ} (ha0 : a < 0)
    (hb0 : 0 < b) (ha : F a = 0) (hb : F b = 0)
    (hleft : ∀ x : ℝ, x < a → (F x).im = 0 ∧ (F x).re < 0)
    (hright : ∀ x : ℝ, b < x → (F x).im = 0 ∧ 0 < (F x).re)
    (htop : Tendsto (fun x : ℝ => (F x).re) atTop atTop)
    (hbot : Tendsto (fun x : ℝ => (F x).re) atBot atBot) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ∃ y ∈ Icc 0 b, F y = γ u := by
  have hcl : ∀ c d : ℝ, 0 ≤ c → d ≤ 1 →
      IsClosed ((fun y : ℝ => F y) ⁻¹' (γ '' Icc c d)) := fun c d hc hd =>
    ((isCompact_Icc.image_of_continuousOn
      (hγc.mono (Icc_subset_Icc hc hd))).isClosed).preimage (r6_cont hF)
  obtain ⟨y, hy, ⟨w1, hw1, h1⟩, ⟨w2, hw2, h2⟩⟩ :=
    isPreconnected_closed_iff.mp isPreconnected_Icc _ _ (hcl u 1 hu.1 le_rfl)
      (hcl 0 u le_rfl hu.2)
      (by
        intro z hz
        obtain ⟨w, hw, hwz⟩ := r6_mem_arc hF hγ0 ha hb hleft hright htop hbot
          (⟨ha0.le.trans hz.1, hz.2⟩ : z ∈ Icc a b)
        rcases le_total u w with h | h
        · exact Or.inl ⟨w, ⟨h, hw.2⟩, hwz⟩
        · exact Or.inr ⟨w, ⟨hw.1, h⟩, hwz⟩)
      ⟨0, ⟨le_rfl, hb0.le⟩, show F ((0 : ℝ) : ℂ) ∈ γ '' Icc u 1 by
        rw [Complex.ofReal_zero, htip]; exact ⟨1, ⟨hu.2, le_rfl⟩, rfl⟩⟩
      ⟨b, ⟨hb0.le, le_rfl⟩, show F (b : ℂ) ∈ γ '' Icc 0 u by
        rw [hb]; exact ⟨0, ⟨le_rfl, hu.1⟩, hγ0⟩⟩
  have hw1I : w1 ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans hw1.1, hw1.2⟩
  have hw2I : w2 ∈ Icc (0 : ℝ) 1 := ⟨hw2.1, hw2.2.trans hu.2⟩
  have h12 : w1 = w2 := hγi hw1I hw2I (h1.trans h2.symm)
  have hw1u : w1 = u := le_antisymm (h12 ▸ hw2.2) hw1.1
  exact ⟨y, hy, by rw [← hw1u]; exact h1.symm⟩

/-- **R6, structure on the swallowed interval.** -/
theorem revExt_structure_S {W : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) {F : ℂ → ℂ}
    (hF : RevExt W T γ F) (hγ0 : γ 0 = 0) (htip : F 0 = γ 1) {a b : ℝ} (ha0 : a < 0) (hb0 : 0 < b)
    (ha : F a = 0) (hb : F b = 0)
    (hleft : ∀ x : ℝ, x < a → (F x).im = 0 ∧ (F x).re < 0)
    (hright : ∀ x : ℝ, b < x → (F x).im = 0 ∧ 0 < (F x).re)
    (htop : Tendsto (fun x : ℝ => (F x).re) atTop atTop)
    (hbot : Tendsto (fun x : ℝ => (F x).re) atBot atBot) :
    (∀ x ∈ Ioo a b, F x ∈ γ '' Ioc 0 1) ∧ InjOn (fun x : ℝ => F x) (Icc a 0) ∧
      InjOn (fun x : ℝ => F x) (Icc 0 b) ∧ ∀ s ∈ Icc a 0, ∃ y ∈ Icc 0 b, F y = F s := by
  have harc := fun t (ht : t ∈ Icc a b) =>
    r6_mem_arc hF hγ0 ha hb hleft hright htop hbot ht
  have hnz := fun y (hy : y ∈ Ioo a b) =>
    r6_no_zero hγc hγH hF hγ0 htip ha hb hleft hright htop hbot hy
  have hcore := fun {x y : ℝ} => r6_no_pair_core hγc hγi hγH hF hγ0 htip ha hb hleft hright
    htop hbot (x := x) (y := y)
  have htip' : F ((0 : ℝ) : ℂ) = γ 1 := by rw [Complex.ofReal_zero, htip]
  -- symmetric injectivity from the strict version
  have inj_of : ∀ S : Set ℝ, (∀ x ∈ S, ∀ y ∈ S, x < y → F x = F y → False) →
      InjOn (fun x : ℝ => F x) S := by
    intro S key x hx y hy hxy
    rcases lt_trichotomy x y with h | h | h
    · exact (key x hx y hy h hxy).elim
    · exact h
    · exact (key y hy x hx h hxy.symm).elim
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, hux⟩ := harc x ⟨hx.1.le, hx.2.le⟩
    refine ⟨u, ⟨lt_of_le_of_ne hu.1 ?_, hu.2⟩, hux⟩
    rintro rfl
    exact hnz x hx (by rw [← hux, hγ0])
  · refine inj_of _ fun x hx y hy hxy hFxy => ?_
    by_cases h1 : F x = γ 1
    · exact hxy.ne (hF.inj_tip x y h1 (hFxy.symm.trans h1))
    by_cases h0 : F x = 0
    · have hyz : F y = 0 := hFxy ▸ h0
      have hya : y = a := by
        by_contra hne
        exact hnz y ⟨lt_of_le_of_ne hy.1 (Ne.symm hne), by linarith [hy.2]⟩ hyz
      linarith [hx.1]
    · refine hcore hxy ⟨hx.1, by linarith [hx.2]⟩ ⟨hy.1, by linarith [hy.2]⟩ hFxy h0 h1 ?_
      intro hm
      have : y = 0 := le_antisymm hy.2 hm.2
      subst this
      exact h1 (hFxy.trans htip')
  · refine inj_of _ fun x hx y hy hxy hFxy => ?_
    by_cases h1 : F x = γ 1
    · exact hxy.ne (hF.inj_tip x y h1 (hFxy.symm.trans h1))
    by_cases h0 : F x = 0
    · have hxb : x = b := by
        by_contra hne
        exact hnz x ⟨by linarith [hx.1], lt_of_le_of_ne hx.2 hne⟩ h0
      linarith [hy.2]
    · refine hcore hxy ⟨by linarith [hx.1], hx.2⟩ ⟨by linarith [hy.1], hy.2⟩ hFxy h0 h1 ?_
      intro hm
      have : x = 0 := le_antisymm hm.1 hx.1
      subst this
      exact h1 htip'
  · intro s hs
    obtain ⟨u, hu, hus⟩ := harc s ⟨hs.1, by linarith [hs.2]⟩
    obtain ⟨y, hy, hyu⟩ := r6_surj_right hγc hγi hF hγ0 htip ha0 hb0 ha hb hleft hright htop
      hbot hu
    exact ⟨y, hy, hyu.trans hus⟩

end CaraR

end QuantumZipper
