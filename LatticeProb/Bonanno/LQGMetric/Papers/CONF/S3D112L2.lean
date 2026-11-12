/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112L2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L1b
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2D

/-!
# D112 packet L1, part 2: Step 2 of CONF Lemma 3.3 for the family `(K_C, W_C)`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.3, Step 2 (C:1217–1234): "Since
`𝒰_r(z) = r𝒰_1(0) + z` and `#𝒰_1(0)` depends only on `δ` … taking the minimum over all such
possibilities we get (3.11)". Decision D112 (`decisions/DEC-112.md` §2, §4 packet L1): the
family is `ι = confFree δ 0 1 T` (unit scale, finite), `K₀ = confCtrs δ 0 C`,
`W₀ = confFatW δ 0 C`, `V₀ = innerPart U₀ (δ/8)`, `U₀ = confU 1 δ 0 T`.

* `CONFHarmLowZB` : the harmonic lower bound for the zero-boundary decomposition (CONF
  C:1169–1172, "since `𝔥^U` is continuous away from `∂U` … by translation and scale invariance of
  the law of `h` modulo additive constant"), stated verbatim as in `handoff/P2-CONF33W.md`; an
  open input (the input `HH` of `zb_step2_of_tight`).
* `conf33G_step2_T` : Step 2 for one unit configuration `T` (`zb_step2_of_tight` +
  `exists_tight_family`).
* `conf33G_step2` : the bound uniform over the finitely many admissible `T` (C:1233–1234).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **Harmonic lower bound for the zero-boundary decomposition** (CONF C:1169–1172; the input
`HH` of `zb_step2_of_tight`, statement of `handoff/P2-CONF33W.md`). -/
def CONFHarmLowZB : Prop :=
  ∀ (U₀ V₀ : Opens ℂ), Bornology.IsBounded (U₀ : Set ℂ) → closure (V₀ : Set ℂ) ⊆ U₀ →
  ∀ β : ℝ, 0 < β → ∃ A' : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (ρ : ℝ) (w : ℂ) (r : ℝ),
    0 < r → ∀ (z : ℂ) (X : Ω → DistC),
    IsL33ZBPart P h ρ w (affOpens r z U₀) (affOpens r z U₀).isOpen X →
    P {ω | ∃ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 (affOpens r z U₀) ∧
      (∀ φ : TestOn (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen),
        restrictTo (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen)
          (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) ∧
      ∀ u ∈ (affOpens r z V₀ : Set ℂ), circleAvg (recField h ρ w ω) r z - A' ≤ 𝔥 u}ᶜ ≤
      ENNReal.ofReal β

/-- the unit domain `U₀ = confU 1 δ 0 T` -/
def u33G (δ : ℝ) (T : Finset (ℤ × ℤ)) : Opens ℂ := ⟨confU 1 δ 0 T, isOpen_confU 1 δ 0 T⟩

/-- `V₀ = (U₀)_{δ/8}` -/
def v33G (δ : ℝ) (T : Finset (ℤ × ℤ)) : Opens ℂ :=
  ⟨innerPart (confU 1 δ 0 T) (δ / 8), isOpen_innerPart (isOpen_confU 1 δ 0 T) _⟩

/-- `W₀ = confFatW δ 0 C` -/
def w33G (δ : ℝ) (C : Set (ℤ × ℤ)) : Opens ℂ := ⟨confFatW δ 0 C, isOpen_thickening⟩

lemma isBounded_confU (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    Bornology.IsBounded (confU r δ z T) :=
  (isBounded_ball (x := z) (r := 4 * r)).subset fun p hp => by
    rw [mem_ball, dist_eq_norm]; exact hp.1.2

lemma confFatW_unit_subset_v33G {δ : ℝ} (hδ : 0 < δ) {T : Finset (ℤ × ℤ)} {C : Set (ℤ × ℤ)}
    (hC : C ⊆ confFree δ 0 1 T) : confFatW δ 0 C ⊆ v33G δ T := by
  have h := confFatW_subset_innerPart (δ := δ) (r := 1) (by simpa using hδ) 0
    (T := T) (C := C) (by simpa using hC)
  simp only [mul_one] at h
  intro x hx
  obtain ⟨h1, h2⟩ := h hx
  exact ⟨h1, by linarith⟩

lemma affOpens_coe (r : ℝ) (hr : 0 < r) (z : ℂ) (S : Opens ℂ) :
    (affOpens r z S : Set ℂ) = affFwd r z '' (S : Set ℂ) :=
  (image_affFwd_eq hr.ne' _).symm

lemma affOpens_u33G {r : ℝ} (hr : 0 < r) (z : ℂ) (δ : ℝ) (T : Finset (ℤ × ℤ)) :
    (affOpens r z (u33G δ T) : Set ℂ) = confU r δ z T := by
  rw [affOpens_coe r hr, confU_scale hr]; rfl

lemma affOpens_w33G {r : ℝ} (hr : 0 < r) (z : ℂ) (δ : ℝ) (C : Set (ℤ × ℤ)) :
    (affOpens r z (w33G δ C) : Set ℂ) = confFatW (δ * r) z C := by
  rw [affOpens_coe r hr, confFatW_scale hr]; rfl

lemma isL33ZBPart_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {ρ : ℝ}
    {w : ℂ} {U U' : Set ℂ} (e : U = U') {hU : IsOpen U} {hU' : IsOpen U'} {X : Ω → DistC}
    (hX : IsL33ZBPart P h ρ w U hU X) : IsL33ZBPart P h ρ w U' hU' X := by
  subst e; exact hX

/-- the conclusion of Step 2 for the unit configuration `T` with lower bound `𝔭` -/
def Conf33GStep2At (D : DistC → ContMetric) (c : ℝ → ℝ) (δ s : ℝ) (T : Finset (ℤ × ℤ))
    (𝔭 : ℝ) : Prop :=
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (ρ : ℝ) (w : ℂ) (r : ℝ), 0 < r → ∀ (z : ℂ) (X : Ω → DistC),
        IsL33ZBPart P h ρ w (affOpens r z (u33G δ T)) (affOpens r z (u33G δ T)).isOpen X →
        ∃ Y : Ω → DistC, IsGFFPlusCont Y P ∧
          (∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 (affOpens r z (u33G δ T)) →
            (∀ φ : TestOn (toOpens (affOpens r z (u33G δ T)) (affOpens r z (u33G δ T)).isOpen),
              restrictTo (toOpens (affOpens r z (u33G δ T)) (affOpens r z (u33G δ T)).isOpen)
                (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
            ∀ W' : Set ℂ, IsOpen W' → W' ⊆ affOpens r z (v33G δ T) → ∀ f' : C(ℂ, ℝ),
            EqOn ⇑f' 𝔥 W' →
            ∀ u v : ℂ, (D (addFun (recField h ρ w ω) (-f'))).internal W' u v =
              (D (Y ω)).internal W' u v) ∧
          ENNReal.ofReal 𝔭 ≤ P {ω | ∀ k ∈ confFree δ 0 1 T, internalDiam (D (Y ω))
              (affFwd r z '' confCtrs δ 0 (confComp (confFree δ 0 1 T) k))
              (affOpens r z (w33G δ (confComp (confFree δ 0 1 T) k))) ≤
                ENNReal.ofReal (s * c r)}

/-- **CONF Lemma 3.3, Step 2, for one unit configuration `T`** (C:1217–1234): for `δ ≤ 1/8`
and `confFree δ 0 1 T ≠ ∅`, there is `𝔭 > 0` such that for every scale, centre and version `X`
of `h̊^{rU₀+z}` a field `Y` (`= D_{h̊}` on open subsets of `rV₀ + z`) has
`P[∀ C, diam(K_C; D_Y(·,·;W_C)) ≤ s 𝔠_r] ≥ 𝔭`. -/
theorem conf33G_step2_T {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) (HH : CONFHarmLowZB) {δ : ℝ} (hδ : 0 < δ)
    (hδ8 : δ ≤ 1 / 8) {s : ℝ} (hs : 0 < s) (T : Finset (ℤ × ℤ))
    (hne : (confFree δ 0 1 T).Nonempty) :
    ∃ 𝔭 : ℝ, 0 < 𝔭 ∧ Conf33GStep2At D c δ s T 𝔭 := by
  set F := confFree δ 0 1 T with hF
  have hFfin : F.Finite := by
    have := finite_confFree (ε := δ * 1) (r := 1) (by simpa using hδ) 0 T
    simpa using this
  haveI : Fintype F := hFfin.fintype
  set ι := F
  have hCsub : ∀ i : ι, confComp F i.1 ⊆ F := fun i => confComp_subset i.2
  set W₀ : ι → Opens ℂ := fun i => w33G δ (confComp F i.1)
  set K₀ : ι → Set ℂ := fun i => confCtrs δ 0 (confComp F i.1)
  have hCfin : ∀ i : ι, (confComp F i.1).Finite := fun i => hFfin.subset (hCsub i)
  have hKne : ∀ i : ι, (K₀ i).Nonempty := fun i =>
    ⟨confCtr δ 0 i.1, ⟨i.1, Relation.ReflTransGen.refl, rfl⟩⟩
  have ha := fun i => ((finite_confCtrs (ε := δ) 0 (hCfin i)).countable).exists_eq_range (hKne i)
  choose a₀ ha₀ using ha
  have hK₀W₀ : ∀ i, K₀ i ⊆ W₀ i := fun i => confCtrs_subset_confFatW hδ 0 _
  have hW₀V₀ : ∀ i, W₀ i ≤ v33G δ T := fun i => confFatW_unit_subset_v33G hδ (hCsub i)
  have hU₀b : Bornology.IsBounded (u33G δ T : Set ℂ) := isBounded_confU 1 δ 0 T
  obtain ⟨k₀, hk₀⟩ := hne
  have hU₀ne : (u33G δ T : Set ℂ).Nonempty :=
    ⟨confCtr δ 0 k₀, (hW₀V₀ ⟨k₀, hk₀⟩ (hK₀W₀ ⟨k₀, hk₀⟩ ⟨k₀, Relation.ReflTransGen.refl, rfl⟩)).1⟩
  have hV₀U₀ : closure (v33G δ T : Set ℂ) ⊆ u33G δ T :=
    closure_innerPart_subset (isOpen_confU 1 δ 0 T) (by linarith)
  have hFull : ∀ i : ι, confComp F i.1 ⊆ confFull δ 0 1 := fun i =>
    (hCsub i).trans confFree_subset_full
  set β : ℝ := 1 / (4 * (Fintype.card ι + 1)) with hβ
  have hβ0 : 0 < β := by positivity
  obtain ⟨S, hS, HT⟩ := exists_tight_family hγ hγ2 hD (W₀ := W₀)
    (fun i => isBounded_confFatW hδ (by linarith) 0 (hFull i))
    (fun i => isPreconnected_confFatW δ 0 F i.2)
    (fun i => (finite_confCtrs (ε := δ) 0 (hCfin i)).isCompact) hK₀W₀ hβ0
  obtain ⟨A', HA⟩ := HH (u33G δ T) (v33G δ T) hU₀b hV₀U₀ β hβ0
  have hc : ∀ r, 0 < r → 0 < c r := fun r hr => hD.tightness.1 r hr
  obtain ⟨𝔭, h𝔭, H⟩ := zb_step2_of_tight hγ hD hU₀b hU₀ne hV₀U₀ hW₀V₀ hK₀W₀
    (a₀ := a₀) (fun i n => by show a₀ i n ∈ confCtrs δ 0 _; rw [ha₀ i]; exact mem_range_self n)
    (fun i => by show confCtrs δ 0 _ ⊆ _; rw [ha₀ i]; exact subset_closure) hS hs hc HT HA
  refine ⟨𝔭, h𝔭, ?_⟩
  intro Ω _ P _ h hh ρ w r hr z X hX
  obtain ⟨Y, hY, hcl, hP⟩ := H P h hh ρ w r hr z X hX
  refine ⟨Y, hY, hcl, hP.trans (measure_mono fun ω hω k hk => hω ⟨k, hk⟩)⟩

lemma conf33GStep2At_mono {D : DistC → ContMetric} {c : ℝ → ℝ} {δ s : ℝ} {T : Finset (ℤ × ℤ)}
    {𝔭 𝔭' : ℝ} (hle : 𝔭' ≤ 𝔭) (H : Conf33GStep2At D c δ s T 𝔭) :
    Conf33GStep2At D c δ s T 𝔭' := by
  intro Ω _ P _ h hh ρ w r hr z X hX
  obtain ⟨Y, hY, hcl, hP⟩ := H P h hh ρ w r hr z X hX
  exact ⟨Y, hY, hcl, (ENNReal.ofReal_le_ofReal hle).trans hP⟩

/-- **CONF Lemma 3.3, Step 2, uniformly over `𝒰_1(0;δ)`** (C:1233–1234: "Since the number of
possibilities for `U⁰` depends only on `δ`, by taking the minimum over all such possibilities"). -/
theorem conf33G_step2 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) (HH : CONFHarmLowZB) {δ : ℝ} (hδ : 0 < δ)
    (hδ8 : δ ≤ 1 / 8) {s : ℝ} (hs : 0 < s) :
    ∃ 𝔭 : ℝ, 0 < 𝔭 ∧ 𝔭 ≤ 1 ∧ ∀ T : Finset (ℤ × ℤ),
      (∀ k ∈ T, k ∈ confSqIdx δ 0 (annulus 0 3 4)) → (confFree δ 0 1 T).Nonempty →
      Conf33GStep2At D c δ s T 𝔭 := by
  classical
  set I := (finite_confSqIdx_annulus hδ 0 3 4).toFinset
  have H := fun T (hT : (confFree δ 0 1 T).Nonempty) =>
    conf33G_step2_T hγ hγ2 hD HH hδ hδ8 hs T hT
  set g : Finset (ℤ × ℤ) → ℝ := fun T =>
    if hT : (confFree δ 0 1 T).Nonempty then (H T hT).choose else 1
  have hg : ∀ T, 0 < g T := by
    intro T; simp only [g]; split_ifs with hT
    · exact (H T hT).choose_spec.1
    · exact one_pos
  have hne : I.powerset.Nonempty := ⟨∅, Finset.empty_mem_powerset _⟩
  set m := I.powerset.inf' hne g
  have hm : 0 < m := (Finset.lt_inf'_iff hne).2 fun T _ => hg T
  refine ⟨min 1 m, lt_min one_pos hm, min_le_left _ _, fun T hT hTne => ?_⟩
  have hTI : T ∈ I.powerset := Finset.mem_powerset.2 fun k hk => by
    simpa [I] using hT k hk
  have h1 : min 1 m ≤ g T := (min_le_right _ _).trans (Finset.inf'_le _ hTI)
  have h2 : g T = (H T hTne).choose := by simp only [g, dif_pos hTne]
  rw [h2] at h1
  exact @conf33GStep2At_mono D c δ s T _ _ h1 (H T hTne).choose_spec.2

end LQGMetric.CONF
