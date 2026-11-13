/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.SpatialMaximalInequality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MarkedBlockAveraging
import LatticeProb.Bonanno.ReflectedGMS.Limit.ReverseRationalMaximal
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicGridLaw
import Mathlib.Probability.Independence.Basic

/-!
# The spatial maximal inequality

This module proves the manuscript proposition "Spatial maximal inequality"
(`s:prop:maximal`, manuscript lines 311-339): for a nonnegative integrable
functional `F` of the marked configuration, the density `ρ_ω(z) = F(ω - z)` is
locally integrable almost surely,

`P[M(ρ) > λ] ≤ 512 E[F] / λ`,   `M(ρ) = sup_{R > 0} R⁻² ∫_{B̄_R} ρ(z) dz`,

and in particular `M(ρ) < ∞` almost surely.

All three clauses are proved here (`spatial_maximal_inequality`), in the
manuscript's order of ideas and with the manuscript's constants:

* `measure_exists_originAverage_gt_le` is `s:eq:dyadicmax` extended to the
  *complete* origin dyadic chain.  Doob's reverse weak-`L¹` inequality is not
  redone: the checked `ReverseConditional.measure_exists_rat_lt_abs_condExp_le`
  is applied to the decreasing family `𝒢_{param q}` of block-invariant
  sigma-fields, and the conditional expectations are replaced by the actual
  block averages through the checked
  `MarkedBlockAveraging.blockAverage_ae_eq_condExp`.  The passage from the
  countable parameter family to *every* origin dyadic square is the manuscript's
  "every origin dyadic square occurs for an interval of parameters containing a
  rational" (`exists_param_originSelected`): the selection threshold
  `κ(S) ≤ m < κ(parent S)` is an interval in `m`, and the parametrisation
  `param q = exp q` is monotone with dense range in `(0, ∞)`.
* `measure_ballMaximal_gt_le` is `s:eq:maximal`.  Following the manuscript, a
  *rational* radius is chosen measurably from the unmarked environment **before**
  the independent dyadic system `𝔻'` is used (`exists_rat_ballAverage`, which
  replaces the manuscript's continuity of `R ↦ ∫_{B̄_R} ρ` by passing to a
  slightly larger rational radius, so that no local integrability is needed
  yet).  Only then is `𝔻'` used: conditionally on its phase, its level of side
  length `ℓ ∈ [8R, 16R)` has its origin square containing `B̄_R` with probability
  at least `(3/4)² > 1/2` (`half_le_measure_goodGrid`), and on that event the
  origin square average exceeds `λ/256` (`originAverage_gt_of_ball`).  The
  countable decomposition over the rational radii turns the conditioning into an
  honest product formula, so no conditional-expectation machinery and no
  translation stationarity of the environment law is used: the auxiliary grid is
  independent of the environment sigma-field and carries the uniform dyadic law
  `DyadicApproximation.UniformGridLaw`.
* `ballMaximal_lt_top_ae` and `integrableOn_density_ae` are the finiteness and
  the local integrability, obtained *from* the tail bound; this is the reason the
  rational radius is produced without assuming local integrability.

Everything about the selected blocks is reused from
`ReflectedGMS.Spatial.MarkedBlockAveraging`.  Three producer dependencies remain
explicit hypotheses, exactly as in that module:

* `BlockData` collects, for every positive parameter, the selected-block
  measurability data and the mark-averaged mass transport
  `MarkedReRooting.MarkedBlockTransport`.  This is where the manuscript's
  *scale invariance* of the integrand enters: the transport identity
  `E[A_m U] = E[U]` is the marked mass transport applied to a scale-invariant
  integrand, and it is not reproved here.
* `OriginChainRegular` is the geometric regularity of the origin ancestor chain
  (finiteness of `κ`, divergence of the inverse ratios, and arbitrarily small
  `κ` at fine levels) which makes the selected origin block `S_m(0)` exist and be
  unique at *every* positive parameter.  Strict monotonicity of `κ` along the
  chain is not assumed: it is derived from these through the checked
  `MarkedBlockAveraging.strictMono_blockIndex_originIndex`.
  Its third clause is **false** under the singular-set manuscript's covering clause
  `μH[1] (uncoveredSet F) = 0`, and the manuscript does not claim it; `OriginChainRegularOn`
  below is the manuscript's own form, with that clause asked only on an invariant domain, and
  `blockSigmaOn` is the sigma-field that goes with it.  The two forms agree at the full
  domain, so nothing proved here is weakened under full covering.
* `EnvironmentGrid` is the independence of `𝔻'` from the unmarked environment
  sigma-field together with its uniform dyadic law.  No trivial invariant
  sigma-field and no translation stationarity is assumed anywhere.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter
open scoped ENNReal

namespace ReflectedGMS.SpatialMaximalInequality

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Nesting of the origin dyadic squares -/

/-- The side length doubles from one dyadic level to the next. -/
theorem side_succ (D : Grid) (k : ℤ) : side D (k + 1) = 2 * side D k := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hexp : D.phase + ((k + 1 : ℤ) : ℝ) = (D.phase + (k : ℝ)) + 1 := by push_cast; ring
  simp only [side, hexp, Real.rpow_add h2, Real.rpow_one]
  ring

/-- The level-`k` origin square sits inside the level-`k+1` one: the origin
chain is the ancestor chain, and the half-open squares are nested along it. -/
theorem halfOpenSquare_originIndex_subset_succ (D : Grid) (k : ℤ) :
    halfOpenSquare D (originIndex k) ⊆ halfOpenSquare D (originIndex (k + 1)) := by
  intro z hz i
  have hk := hz i
  have hlowk : (square D (originIndex k)).lower i
      = D.origin k i + side D k * ((0 : ℤ) : ℝ) := rfl
  have huppk : (square D (originIndex k)).upper i
      = D.origin k i + side D k * ((0 : ℤ) : ℝ) + side D k := rfl
  have hlows : (square D (originIndex (k + 1))).lower i
      = D.origin (k + 1) i + side D (k + 1) * ((0 : ℤ) : ℝ) := rfl
  have hupps : (square D (originIndex (k + 1))).upper i
      = D.origin (k + 1) i + side D (k + 1) * ((0 : ℤ) : ℝ) + side D (k + 1) := rfl
  rw [hlowk, huppk] at hk
  rw [hlows, hupps]
  have hcomp : D.origin k i
      = D.origin (k + 1) i + side D k * ((D.digit k i).val : ℝ) := D.compatible k i
  have hpos : 0 < side D k := side_pos D k
  have hd0 : (0 : ℝ) ≤ ((D.digit k i).val : ℝ) := by positivity
  have hd1 : ((D.digit k i).val : ℝ) ≤ 1 := by
    have h2 : (D.digit k i).val < 2 := (D.digit k i).isLt
    have h3 : (D.digit k i).val ≤ 1 := by omega
    exact_mod_cast h3
  have hprod0 : 0 ≤ side D k * ((D.digit k i).val : ℝ) := mul_nonneg hpos.le hd0
  have hprod1 : side D k * ((D.digit k i).val : ℝ) ≤ side D k := by nlinarith
  have hside2 : side D (k + 1) = 2 * side D k := side_succ D k
  push_cast at hk ⊢
  rw [hside2]
  exact ⟨by linarith [hk.1], by linarith [hk.2]⟩

/-- Nesting of the origin squares `j` levels up. -/
theorem halfOpenSquare_originIndex_subset_add (D : Grid) (k : ℤ) (j : ℕ) :
    halfOpenSquare D (originIndex k) ⊆ halfOpenSquare D (originIndex (k + (j : ℤ))) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hcast : k + ((j + 1 : ℕ) : ℤ) = (k + (j : ℤ)) + 1 := by push_cast; ring
      rw [hcast]
      exact ih.trans (halfOpenSquare_originIndex_subset_succ D (k + (j : ℤ)))

/-- The origin squares increase with the level. -/
theorem halfOpenSquare_originIndex_mono (D : Grid) {k l : ℤ} (h : k ≤ l) :
    halfOpenSquare D (originIndex k) ⊆ halfOpenSquare D (originIndex l) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, l = k + (j : ℤ) := ⟨(l - k).toNat, by omega⟩
  subst hj
  exact halfOpenSquare_originIndex_subset_add D k j

/-! ### The origin chain of a marked configuration -/

/-- The manuscript's `κ` along the origin ancestor chain of a marked
configuration. -/
noncomputable def originBlockIndex (R : MarkedReRooting Ω) (ω : Ω) (k : ℤ) : ℝ≥0∞ :=
  blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k)

/-- Regularity of the origin ancestor chain.  These are the manuscript's
standing geometric hypotheses on the selection index `κ`: it is finite at every
origin square, the inverse ratios along every ancestor chain diverge (so `κ`
increases strictly and diverges upward), and it is arbitrarily small at fine
levels.  Together they make the selected origin block `S_m(0)` exist and be
unique at every positive parameter `m`. -/
structure OriginChainRegular (R : MarkedReRooting Ω) : Prop where
  /-- `κ` is finite at every origin square. -/
  index_ne_top : ∀ (ω : Ω) (k : ℤ), originBlockIndex R ω k ≠ ∞
  /-- The inverse ratios diverge along every ancestor chain. -/
  inverseRatio_tendsto : ∀ (ω : Ω) (k : ℤ), Filter.Tendsto
    (fun j : ℕ => inverseRatio (decode (R.env ω)) (R.grid ω)
      (ancestor (R.grid ω) (originIndex k) j)) Filter.atTop (nhds ∞)
  /-- `κ` drops below every positive level at sufficiently fine origin squares. -/
  index_small : ∀ (ω : Ω) (m : ℝ), 0 < m →
    ∃ k : ℤ, originBlockIndex R ω k ≤ ENNReal.ofReal m

/-- Strict monotonicity of `κ` along the origin chain, from the checked
`MarkedBlockAveraging.strictMono_blockIndex_originIndex`. -/
theorem OriginChainRegular.strictMono {R : MarkedReRooting Ω} (h : OriginChainRegular R)
    (ω : Ω) :
    StrictMono fun k : ℤ => blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k) :=
  strictMono_blockIndex_originIndex _ _ (h.index_ne_top ω) (h.inverseRatio_tendsto ω)

/-- `κ` exceeds every finite level at sufficiently coarse origin squares, from the divergence
of the inverse ratios along the origin chain alone. -/
theorem exists_index_gt_of_tendsto {R : MarkedReRooting Ω} (ω : Ω)
    (hten : Filter.Tendsto
      (fun j : ℕ => inverseRatio (decode (R.env ω)) (R.grid ω)
        (ancestor (R.grid ω) (originIndex 0) j)) Filter.atTop (nhds ∞))
    (m : ℝ) : ∃ k : ℤ, ENNReal.ofReal m < originBlockIndex R ω k := by
  have hev : ∀ᶠ j : ℕ in Filter.atTop,
      ENNReal.ofReal m < inverseRatio (decode (R.env ω)) (R.grid ω)
        (ancestor (R.grid ω) (originIndex 0) j) :=
    hten.eventually (eventually_gt_nhds ENNReal.ofReal_lt_top)
  obtain ⟨j, hj⟩ := hev.exists
  refine ⟨(j : ℤ), lt_of_lt_of_le hj ?_⟩
  have hanc : ancestor (R.grid ω) (originIndex 0) j = originIndex ((j : ℤ)) := by
    rw [ancestor_originIndex]
    congr 1
    omega
  rw [hanc]
  exact inverseRatio_le_blockIndex _ _ _

/-- `κ` exceeds every finite level at sufficiently coarse origin squares. -/
theorem OriginChainRegular.exists_index_gt {R : MarkedReRooting Ω} (h : OriginChainRegular R)
    (ω : Ω) (m : ℝ) : ∃ k : ℤ, ENNReal.ofReal m < originBlockIndex R ω k :=
  exists_index_gt_of_tendsto ω (h.inverseRatio_tendsto ω 0) m

/-- The selected origin block exists at a parameter which `κ` both undershoots somewhere and
overshoots somewhere along the origin chain, by the checked
`MarkedBlockAveraging.exists_originSelected`.  This is the content of
`OriginChainRegular.exists_originSelected'` with the two existence facts isolated, so that the
almost-sure form `OriginChainRegularOn.exists_originSelected'` can reuse it. -/
theorem exists_originSelected_of_bounds {R : MarkedReRooting Ω} {ω : Ω}
    (hmono : StrictMono fun k : ℤ => blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k))
    {m : ℝ} (hm : 0 < m) (hsmall : ∃ k : ℤ, originBlockIndex R ω k ≤ ENNReal.ofReal m)
    (hgt : ∃ k : ℤ, ENNReal.ofReal m < originBlockIndex R ω k) :
    ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k := by
  obtain ⟨k₀, hk₀⟩ := hsmall
  obtain ⟨k₁, hk₁⟩ := hgt
  have hle : k₀ ≤ k₁ := by
    by_contra hcon
    push_neg at hcon
    exact absurd hk₀ (not_le.2 (lt_of_lt_of_le hk₁ (hmono.monotone hcon.le)))
  exact exists_originSelected _ _ _ hm hle hk₀ hk₁

/-- The selected origin block exists at every positive parameter, by the checked
`MarkedBlockAveraging.exists_originSelected`. -/
theorem OriginChainRegular.exists_originSelected' {R : MarkedReRooting Ω}
    (h : OriginChainRegular R) (ω : Ω) {m : ℝ} (hm : 0 < m) :
    ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k :=
  exists_originSelected_of_bounds (h.strictMono ω) hm (h.index_small ω m hm)
    (h.exists_index_gt ω m)

/-! ### The rational parametrisation of the block scale -/

/-- The strictly increasing rational parametrisation of the block scale.  Its
range is dense in `(0, ∞)`, which is what makes every origin dyadic square occur
at one of these parameters. -/
noncomputable def param (q : ℚ) : ℝ := Real.exp (q : ℝ)

theorem param_pos (q : ℚ) : 0 < param q := Real.exp_pos _

theorem param_mono : Monotone param := by
  intro a b hab
  exact Real.exp_le_exp.2 (by exact_mod_cast hab)

/-- **Every origin dyadic square occurs for an interval of parameters containing
a rational.**  The selection threshold `κ(S) ≤ m < κ(parent S)` is an interval in
`m`, and `param` has dense range in `(0, ∞)`. -/
theorem exists_param_originSelected_of {R : MarkedReRooting Ω} {ω : Ω}
    (hfin : ∀ k : ℤ, originBlockIndex R ω k ≠ ∞)
    (hmono : StrictMono fun k : ℤ => blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k))
    (k : ℤ) :
    ∃ q : ℚ, OriginSelected (decode (R.env ω)) (R.grid ω) (param q) k := by
  obtain ⟨a, ha0, hka⟩ : ∃ a : ℝ, 0 ≤ a ∧ originBlockIndex R ω k = ENNReal.ofReal a :=
    ⟨(originBlockIndex R ω k).toReal, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (hfin k)).symm⟩
  obtain ⟨b, hb0', hkb⟩ : ∃ b : ℝ, 0 ≤ b ∧ originBlockIndex R ω (k + 1) = ENNReal.ofReal b :=
    ⟨(originBlockIndex R ω (k + 1)).toReal, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (hfin (k + 1))).symm⟩
  have hlt : originBlockIndex R ω k < originBlockIndex R ω (k + 1) :=
    hmono (by omega)
  have hab : a < b := by
    rw [hka, hkb] at hlt
    by_contra hcon
    push_neg at hcon
    exact absurd (ENNReal.ofReal_le_ofReal hcon) (not_le.2 hlt)
  have hb0 : 0 < b := lt_of_le_of_lt ha0 hab
  have hlolt : (if 0 < a then Real.log a else Real.log b - 1) < Real.log b := by
    by_cases hpos : 0 < a
    · simp only [hpos, ite_true]
      exact Real.log_lt_log hpos hab
    · simp only [hpos, ite_false]
      linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlolt
  have hexplt : Real.exp (q : ℝ) < b := by
    have hstep := Real.exp_lt_exp.2 hq2
    rwa [Real.exp_log hb0] at hstep
  have hexpge : a ≤ Real.exp (q : ℝ) := by
    by_cases hpos : 0 < a
    · have hq1' : Real.log a < (q : ℝ) := by simpa [hpos] using hq1
      have hstep := Real.exp_lt_exp.2 hq1'
      rw [Real.exp_log hpos] at hstep
      exact hstep.le
    · push_neg at hpos
      exact le_trans hpos (Real.exp_pos _).le
  refine ⟨q, param_pos q, ?_, ?_⟩
  · show blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k) ≤ ENNReal.ofReal (param q)
    rw [show blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k)
        = ENNReal.ofReal a from hka]
    exact ENNReal.ofReal_le_ofReal hexpge
  · rw [parent_originIndex]
    show ENNReal.ofReal (param q)
      < blockIndex (decode (R.env ω)) (R.grid ω) (originIndex (k + 1))
    rw [show blockIndex (decode (R.env ω)) (R.grid ω) (originIndex (k + 1))
        = ENNReal.ofReal b from hkb]
    exact (ENNReal.ofReal_lt_ofReal_iff hb0).2 hexplt

/-- **Every origin dyadic square occurs for an interval of parameters containing
a rational.** -/
theorem exists_param_originSelected {R : MarkedReRooting Ω} (h : OriginChainRegular R)
    (ω : Ω) (k : ℤ) :
    ∃ q : ℚ, OriginSelected (decode (R.env ω)) (R.grid ω) (param q) k :=
  exists_param_originSelected_of (h.index_ne_top ω) (h.strictMono ω) k

/-! ### Monotonicity of the selected block and of the block sigma-fields -/

/-- The selected level increases with the parameter, at a configuration where the selected
origin block exists at both parameters.  The two existence facts are isolated so that the
almost-sure form `blockLevel_monoOn` can reuse the argument. -/
theorem blockLevel_mono_of_exists {R : MarkedReRooting Ω} {ω : Ω}
    (hmono : StrictMono fun k : ℤ => blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k))
    {m m' : ℝ} (hmm : m ≤ m')
    (hex : ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k)
    (hex' : ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m' k) :
    blockLevel (decode (R.env ω)) (R.grid ω) m
      ≤ blockLevel (decode (R.env ω)) (R.grid ω) m' := by
  obtain ⟨k, hk⟩ := hex
  obtain ⟨k', hk'⟩ := hex'
  rw [blockLevel_eq hmono hk, blockLevel_eq hmono hk']
  by_contra hcon
  push_neg at hcon
  have hstep : blockIndex (decode (R.env ω)) (R.grid ω) (originIndex (k' + 1))
      ≤ blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k) :=
    hmono.monotone (by omega)
  have h1 : ENNReal.ofReal m'
      < blockIndex (decode (R.env ω)) (R.grid ω) (originIndex (k' + 1)) := by
    have hp := hk'.2.2
    rwa [parent_originIndex] at hp
  have h2 : ENNReal.ofReal m' < ENNReal.ofReal m :=
    lt_of_lt_of_le (lt_of_lt_of_le h1 hstep) hk.2.1
  exact absurd (ENNReal.ofReal_le_ofReal hmm) (not_le.2 h2)

/-- The selected level increases with the parameter. -/
theorem blockLevel_mono {R : MarkedReRooting Ω} (h : OriginChainRegular R) (ω : Ω)
    {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') :
    blockLevel (decode (R.env ω)) (R.grid ω) m
      ≤ blockLevel (decode (R.env ω)) (R.grid ω) m' :=
  blockLevel_mono_of_exists (h.strictMono ω) hmm (h.exists_originSelected' ω hm)
    (h.exists_originSelected' ω (lt_of_lt_of_le hm hmm))

/-- The selected origin block increases with the parameter. -/
theorem blockSetAt_mono {R : MarkedReRooting Ω} (h : OriginChainRegular R) (ω : Ω)
    {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') :
    R.blockSetAt m ω ⊆ R.blockSetAt m' ω :=
  halfOpenSquare_originIndex_mono _ (blockLevel_mono h ω hm hmm)

/-- **The sigma-fields `𝒢_m` decrease with `m`.**  An event invariant under
re-rooting inside the larger block is invariant inside its smaller subblock. -/
theorem blockSigma_antitone {R : MarkedReRooting Ω} (h : OriginChainRegular R)
    {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') : R.blockSigma m' ≤ R.blockSigma m := by
  intro A hA
  exact ⟨hA.1, fun ω w hw => hA.2 ω w (blockSetAt_mono h ω hm hmm hw)⟩

/-! ### The manuscript's form: origin-chain regularity on an invariant domain

`OriginChainRegular.index_small` — `κ` drops below every positive level along the origin chain
of **every** configuration — is *false* under the singular-set manuscript's covering clause
`μH[1] (uncoveredSet F) = 0`.  The manuscript asks for `κ(S) ≤ 2 ℓ(S)/d_H` along a chain
containing a point `z ∈ H` of a cell, and says explicitly that *"no claim is needed about an
uncovered singular point"*; `GoodEnvironmentSet.exists_blockIndex_originIndex_le` records an
explicit configuration — the annuli `2^{-n-1} ≤ ‖x‖_∞ ≤ 2^{-n}` tiled by squares of side
`2^{-n²}` — that satisfies every clause of `Geometry`, has uncovered set `{0}`, and along whose
origin chain `κ` stays bounded below.

The manuscript's own form of §3.1 is *"the closures of the blocks cover every point belonging to
a cell, and hence Lebesgue-almost every point of the plane … undefined constructions are set to
zero off their invariant domain"*.  `OriginChainRegularOn R G` is that statement: the two chain
clauses at **every** configuration — both survive the weakened covering clause unaided, since
`NonmacroscopicSelectedBlocks.maxCellDiameter_pos` needs a covered point merely *somewhere* in
the square and the covered points are dense — and `index_small` only on the domain `G`.

Nothing here needs `G` measurable; the consumers use it with `G` conull, through the
almost-sure block sigma-field `blockSigmaOn` below.

**No regression.**  `OriginChainRegular.on` turns the everywhere form into the gated one at any
`G`, and `OriginChainRegularOn.toOriginChainRegular` turns the gated form at `G = univ` back;
`blockSigmaOn_univ` identifies the gated sigma-field with `blockSigma` there.  So under the
earlier manuscript's covering clause `⋃ v, cell v = univ`, where `uncoveredSet F = ∅`, every
conclusion below is exactly as strong as the ungated one. -/

/-- **Regularity of the origin ancestor chain on an invariant domain `G`** — the manuscript's
own form of the standing geometric hypotheses on `κ`.  Identical to `OriginChainRegular` except
that `index_small` is asked only at the configurations of `G`. -/
structure OriginChainRegularOn (R : MarkedReRooting Ω) (G : Set Ω) : Prop where
  /-- `κ` is finite at every origin square. -/
  index_ne_top : ∀ (ω : Ω) (k : ℤ), originBlockIndex R ω k ≠ ∞
  /-- The inverse ratios diverge along every ancestor chain. -/
  inverseRatio_tendsto : ∀ (ω : Ω) (k : ℤ), Filter.Tendsto
    (fun j : ℕ => inverseRatio (decode (R.env ω)) (R.grid ω)
      (ancestor (R.grid ω) (originIndex k) j)) Filter.atTop (nhds ∞)
  /-- `κ` drops below every positive level at sufficiently fine origin squares, **on `G`**. -/
  index_small : ∀ ω ∈ G, ∀ m : ℝ, 0 < m →
    ∃ k : ℤ, originBlockIndex R ω k ≤ ENNReal.ofReal m

/-- **No regression**: the everywhere form implies the gated form at every domain. -/
theorem OriginChainRegular.on {R : MarkedReRooting Ω} (h : OriginChainRegular R) (G : Set Ω) :
    OriginChainRegularOn R G where
  index_ne_top := h.index_ne_top
  inverseRatio_tendsto := h.inverseRatio_tendsto
  index_small ω _ m hm := h.index_small ω m hm

/-- **No regression, converse**: at the full domain the gated form is the everywhere form.  So
under the earlier manuscript's covering clause, where the origin of every configuration lies in
a cell, the gated theory delivers exactly the ungated statements. -/
theorem OriginChainRegularOn.toOriginChainRegular {R : MarkedReRooting Ω}
    (h : OriginChainRegularOn R Set.univ) : OriginChainRegular R where
  index_ne_top := h.index_ne_top
  inverseRatio_tendsto := h.inverseRatio_tendsto
  index_small ω m hm := h.index_small ω (Set.mem_univ ω) m hm

/-- Shrinking the domain. -/
theorem OriginChainRegularOn.mono {R : MarkedReRooting Ω} {G G' : Set Ω}
    (h : OriginChainRegularOn R G) (hsub : G' ⊆ G) : OriginChainRegularOn R G' where
  index_ne_top := h.index_ne_top
  inverseRatio_tendsto := h.inverseRatio_tendsto
  index_small ω hω m hm := h.index_small ω (hsub hω) m hm

/-- Strict monotonicity of `κ` along the origin chain.  This needs no domain: it comes from the
two ungated clauses. -/
theorem OriginChainRegularOn.strictMono {R : MarkedReRooting Ω} {G : Set Ω}
    (h : OriginChainRegularOn R G) (ω : Ω) :
    StrictMono fun k : ℤ => blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k) :=
  strictMono_blockIndex_originIndex _ _ (h.index_ne_top ω) (h.inverseRatio_tendsto ω)

/-- `κ` exceeds every finite level at sufficiently coarse origin squares.  This needs no
domain either. -/
theorem OriginChainRegularOn.exists_index_gt {R : MarkedReRooting Ω} {G : Set Ω}
    (h : OriginChainRegularOn R G) (ω : Ω) (m : ℝ) :
    ∃ k : ℤ, ENNReal.ofReal m < originBlockIndex R ω k :=
  exists_index_gt_of_tendsto ω (h.inverseRatio_tendsto ω 0) m

/-- The selected origin block exists at every positive parameter, **at a configuration of the
domain**. -/
theorem OriginChainRegularOn.exists_originSelected' {R : MarkedReRooting Ω} {G : Set Ω}
    (h : OriginChainRegularOn R G) {ω : Ω} (hω : ω ∈ G) {m : ℝ} (hm : 0 < m) :
    ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k :=
  exists_originSelected_of_bounds (h.strictMono ω) hm (h.index_small ω hω m hm)
    (h.exists_index_gt ω m)

/-- The selected level increases with the parameter, on the domain. -/
theorem blockLevel_monoOn {R : MarkedReRooting Ω} {G : Set Ω} (h : OriginChainRegularOn R G)
    {ω : Ω} (hω : ω ∈ G) {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') :
    blockLevel (decode (R.env ω)) (R.grid ω) m
      ≤ blockLevel (decode (R.env ω)) (R.grid ω) m' :=
  blockLevel_mono_of_exists (h.strictMono ω) hmm (h.exists_originSelected' hω hm)
    (h.exists_originSelected' hω (lt_of_lt_of_le hm hmm))

/-- The selected origin block increases with the parameter, on the domain. -/
theorem blockSetAt_monoOn {R : MarkedReRooting Ω} {G : Set Ω} (h : OriginChainRegularOn R G)
    {ω : Ω} (hω : ω ∈ G) {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') :
    R.blockSetAt m ω ⊆ R.blockSetAt m' ω :=
  halfOpenSquare_originIndex_mono _ (blockLevel_monoOn h hω hm hmm)

/-! ### The block sigma-field on an invariant domain -/

/-- **The manuscript's `𝒢_m` on an invariant domain `G`**: the measurable events unchanged by
every allowed re-rooting inside the selected origin block, **at the configurations of `G`**.

It is *larger* than `blockSigma m` (`blockSigma_le_blockSigmaOn`) and equal to it at
`G = univ` (`blockSigmaOn_univ`), so replacing `blockSigma` by it never weakens a conclusion
under full covering.  Being larger is exactly what the consumers need: the block average has to
be measurable for it (easier), while the transport identity it is tested against holds for every
measurable scale-invariant test function and does not see the gate at all. -/
def blockSigmaOn (R : MarkedReRooting Ω) (G : Set Ω) (m : ℝ) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧
    ∀ ω ∈ G, ∀ w : Plane, w ∈ R.blockSetAt m ω → (R.shift w ω ∈ A ↔ ω ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun ω hω w hw => not_congr (hA.2 ω hω w hw)⟩
  measurableSet_iUnion f hf :=
    ⟨MeasurableSet.iUnion fun i => (hf i).1, fun ω hω w hw => by
      simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2 ω hω w hw⟩

theorem blockSigmaOn_le (R : MarkedReRooting Ω) (G : Set Ω) (m : ℝ) :
    blockSigmaOn R G m ≤ ‹MeasurableSpace Ω› := fun _ hA => hA.1

theorem measurableSet_blockSigmaOn_iff {R : MarkedReRooting Ω} {G : Set Ω} {m : ℝ}
    {A : Set Ω} : MeasurableSet[blockSigmaOn R G m] A ↔ MeasurableSet A ∧
      ∀ ω ∈ G, ∀ w : Plane, w ∈ R.blockSetAt m ω → (R.shift w ω ∈ A ↔ ω ∈ A) := Iff.rfl

/-- The everywhere-invariant sigma-field is contained in the gated one. -/
theorem blockSigma_le_blockSigmaOn (R : MarkedReRooting Ω) (G : Set Ω) (m : ℝ) :
    R.blockSigma m ≤ blockSigmaOn R G m := fun _ hA => ⟨hA.1, fun ω _ w hw => hA.2 ω w hw⟩

/-- **No regression**: at the full domain the gated sigma-field is the manuscript's `𝒢_m`. -/
theorem blockSigmaOn_univ (R : MarkedReRooting Ω) (m : ℝ) :
    blockSigmaOn R Set.univ m = R.blockSigma m :=
  le_antisymm (fun _ hA => ⟨hA.1, fun ω w hw => hA.2 ω (Set.mem_univ ω) w hw⟩)
    (blockSigma_le_blockSigmaOn R Set.univ m)

/-- Shrinking the domain enlarges the sigma-field. -/
theorem blockSigmaOn_mono_domain (R : MarkedReRooting Ω) {G G' : Set Ω} (hsub : G' ⊆ G)
    (m : ℝ) : blockSigmaOn R G m ≤ blockSigmaOn R G' m :=
  fun _ hA => ⟨hA.1, fun ω hω w hw => hA.2 ω (hsub hω) w hw⟩

/-- **The sigma-fields `𝒢_m` decrease with `m`**, on the domain.  This is the one clause of the
maximal-inequality chain that is not an almost-sure statement and therefore could not simply be
relativised at the end: the reverse maximal inequality needs an antitone *family of
sigma-fields*.  Gating the invariance requirement is what restores it, and
`blockSetAt_monoOn` is the only input. -/
theorem blockSigmaOn_antitone {R : MarkedReRooting Ω} {G : Set Ω}
    (h : OriginChainRegularOn R G) {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') :
    blockSigmaOn R G m' ≤ blockSigmaOn R G m := by
  intro A hA
  exact ⟨hA.1, fun ω hω w hw => hA.2 ω hω w (blockSetAt_monoOn h hω hm hmm hw)⟩

/-! ### Block equivariance on an invariant domain -/

/-- **Re-rooting inside the selected origin block translates it, on the domain `G`.**  This is
`MarkedReRooting.BlockEquivariant` relativised in the same way and for the same reason: its
proof needs the selected origin block at `ω` to exist, which under the weakened covering clause
happens only at a covered origin.  Nothing is asked at `R.shift w ω`: the selected block there
is produced by transporting the one at `ω`. -/
def BlockEquivariantOn (R : MarkedReRooting Ω) (G : Set Ω) (m : ℝ) : Prop :=
  ∀ ω ∈ G, ∀ w : Plane, w ∈ R.blockSetAt m ω →
    R.blockSetAt m (R.shift w ω) = (fun y => w + y) ⁻¹' R.blockSetAt m ω ∧
      R.blockSideAt m (R.shift w ω) = R.blockSideAt m ω

/-- **No regression**: the everywhere form implies the gated form at every domain. -/
theorem blockEquivariantOn_of_blockEquivariant {R : MarkedReRooting Ω} {m : ℝ}
    (h : R.BlockEquivariant m) (G : Set Ω) : BlockEquivariantOn R G m :=
  fun ω _ w hw => h ω w hw

/-- **No regression, converse**: at the full domain the gated form is the everywhere form. -/
theorem blockEquivariant_of_blockEquivariantOn {R : MarkedReRooting Ω} {m : ℝ}
    (h : BlockEquivariantOn R Set.univ m) : R.BlockEquivariant m :=
  fun ω w hw => h ω (Set.mem_univ ω) w hw

/-- The block average is measurable for the gated block-invariant sigma-field. -/
theorem measurable_blockSigmaOn_blockAverageLint {R : MarkedReRooting Ω} {G : Set Ω} {m : ℝ}
    (hequi : BlockEquivariantOn R G m) (hgraph : R.MeasurableBlockGraph m)
    (hside : Measurable (R.blockSideAt m)) {U : Ω → ℝ≥0∞} (hU : Measurable U) :
    Measurable[blockSigmaOn R G m] (R.blockAverageLint m U) := by
  intro s hs
  refine ⟨MarkedReRooting.measurable_blockAverageLint hgraph hside hU hs, fun ω hω w hw => ?_⟩
  simp only [Set.mem_preimage]
  rw [MarkedReRooting.blockAverageLint_shift_at
    (MarkedReRooting.measurableSet_blockSetAt hgraph) U ω (hequi ω hω w hw).1
    (hequi ω hω w hw).2]

/-! ### Origin square averages -/

/-- The average of the density `ρ_ω(z) = F(ω - z)` over the level-`k` origin
dyadic square. -/
noncomputable def originAverage (R : MarkedReRooting Ω) (F : Ω → ℝ) (k : ℤ) (ω : Ω) : ℝ≥0∞ :=
  (ENNReal.ofReal (side (R.grid ω) k ^ 2))⁻¹ *
    ∫⁻ z in halfOpenSquare (R.grid ω) (originIndex k),
      ENNReal.ofReal (F (R.shift z ω)) ∂volume

/-- At a parameter selecting the level-`k` origin square, the block average of
the manuscript is the level-`k` origin square average. -/
theorem blockAverageLint_eq_originAverage (R : MarkedReRooting Ω) (F : Ω → ℝ) {ω : Ω}
    {m : ℝ} {k : ℤ} (hk : blockLevel (decode (R.env ω)) (R.grid ω) m = k) :
    R.blockAverageLint m (fun x => ENNReal.ofReal (F x)) ω = originAverage R F k ω := by
  have hside : R.blockSideAt m ω = side (R.grid ω) k := by
    simp only [MarkedReRooting.blockSideAt, blockSide, hk]
  have hset : R.blockSetAt m ω = halfOpenSquare (R.grid ω) (originIndex k) := by
    simp only [MarkedReRooting.blockSetAt, blockSet, blockSquareIndex, hk]
  simp only [MarkedReRooting.blockAverageLint, originAverage, hside, hset]

/-! ### The selected-block producer data -/

/-! ### The complete origin-chain weak-`L¹` estimate -/

/-- **The maximal average over the complete origin dyadic chain obeys the
weak-`L¹` bound `E[F]/t`.**  This is `s:eq:dyadicmax` together with the passage
from the countable parameter family to every origin square.  Doob's reverse
maximal inequality is not redone: the checked rational-parameter reverse
estimate is applied to the decreasing family `𝒢_{param q}`. -/
theorem measure_exists_originAverage_gt_le_of_chain (R : MarkedReRooting Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hcfin : ∀ (ω : Ω) (k : ℤ), originBlockIndex R ω k ≠ ∞)
    (hcmono : ∀ ω : Ω,
      StrictMono fun k : ℤ => blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k))
    {F : Ω → ℝ} (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (𝒢 : ℚ → MeasurableSpace Ω) (hanti : Antitone 𝒢)
    (hle : ∀ q : ℚ, 𝒢 q ≤ ‹MeasurableSpace Ω›)
    (hcond : ∀ q : ℚ, R.blockAverage (param q) F =ᵐ[μ] μ[F|𝒢 q])
    (hfin : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      R.blockAverageLint (param q) (fun x => ENNReal.ofReal (F x)) ω < ∞)
    {t : ℝ} (ht : 0 < t) :
    μ {ω | ∃ k : ℤ, ENNReal.ofReal t < originAverage R F k ω}
      ≤ ENNReal.ofReal ((∫ ω, F ω ∂μ) / t) := by
  classical
  have habs : (∫ ω, |F ω| ∂μ) = ∫ ω, F ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => abs_of_nonneg (hF0 ω))
  have hmain := ReverseConditional.measure_exists_rat_lt_abs_condExp_le (P := μ) hanti hle F ht
  rw [habs] at hmain
  refine le_trans (measure_mono_ae ?_) hmain
  have hid : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      R.blockAverageLint (param q) (fun x => ENNReal.ofReal (F x)) ω
        = ENNReal.ofReal (μ[F|𝒢 q] ω) := by
    intro q
    filter_upwards [hcond q, hfin q] with ω hω1 hω2
    rw [← hω1, MarkedReRooting.blockAverage_eq_toReal hF hF0 ω, ENNReal.ofReal_toReal hω2.ne]
  have hall : ∀ᵐ ω ∂μ, ∀ q : ℚ,
      R.blockAverageLint (param q) (fun x => ENNReal.ofReal (F x)) ω
        = ENNReal.ofReal (μ[F|𝒢 q] ω) := ae_all_iff.2 hid
  filter_upwards [hall] with ω hω hmem
  obtain ⟨k, hk⟩ := hmem
  obtain ⟨q, hq⟩ := exists_param_originSelected_of (hcfin ω) (hcmono ω) k
  have hlevel : blockLevel (decode (R.env ω)) (R.grid ω) (param q) = k :=
    blockLevel_eq (hcmono ω) hq
  have hrewrite : ENNReal.ofReal t < ENNReal.ofReal (μ[F|𝒢 q] ω) := by
    rw [← hω q, blockAverageLint_eq_originAverage R F hlevel]
    exact hk
  refine ⟨q, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hle' : ENNReal.ofReal |μ[F|𝒢 q] ω| ≤ ENNReal.ofReal t :=
    ENNReal.ofReal_le_ofReal hcon
  have hle'' : ENNReal.ofReal (μ[F|𝒢 q] ω) ≤ ENNReal.ofReal |μ[F|𝒢 q] ω| :=
    ENNReal.ofReal_le_ofReal (le_abs_self _)
  exact absurd (le_trans hle'' hle') (not_le.2 hrewrite)

/-- **The maximal average over the complete origin dyadic chain obeys the weak-`L¹` bound
`E[F]/t`**, from the everywhere origin-chain regularity.  Only its two ungated clauses are
used: the passage from the countable parameter family to every origin square needs finiteness
and strict monotonicity of `κ`, never `index_small`. -/
theorem measure_exists_originAverage_gt_le_of_condExp (R : MarkedReRooting Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hchain : OriginChainRegular R)
    {F : Ω → ℝ} (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (𝒢 : ℚ → MeasurableSpace Ω) (hanti : Antitone 𝒢)
    (hle : ∀ q : ℚ, 𝒢 q ≤ ‹MeasurableSpace Ω›)
    (hcond : ∀ q : ℚ, R.blockAverage (param q) F =ᵐ[μ] μ[F|𝒢 q])
    (hfin : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      R.blockAverageLint (param q) (fun x => ENNReal.ofReal (F x)) ω < ∞)
    {t : ℝ} (ht : 0 < t) :
    μ {ω | ∃ k : ℤ, ENNReal.ofReal t < originAverage R F k ω}
      ≤ ENNReal.ofReal ((∫ ω, F ω ∂μ) / t) :=
  measure_exists_originAverage_gt_le_of_chain R hchain.index_ne_top hchain.strictMono hF hF0
    hFint 𝒢 hanti hle hcond hfin ht

/-- The same bound from the manuscript's gated origin-chain regularity.  **The estimate costs
nothing on the domain**: `index_small` never enters it. -/
theorem measure_exists_originAverage_gt_le_of_condExpOn (R : MarkedReRooting Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Set Ω} (hchain : OriginChainRegularOn R G)
    {F : Ω → ℝ} (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (𝒢 : ℚ → MeasurableSpace Ω) (hanti : Antitone 𝒢)
    (hle : ∀ q : ℚ, 𝒢 q ≤ ‹MeasurableSpace Ω›)
    (hcond : ∀ q : ℚ, R.blockAverage (param q) F =ᵐ[μ] μ[F|𝒢 q])
    (hfin : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      R.blockAverageLint (param q) (fun x => ENNReal.ofReal (F x)) ω < ∞)
    {t : ℝ} (ht : 0 < t) :
    μ {ω | ∃ k : ℤ, ENNReal.ofReal t < originAverage R F k ω}
      ≤ ENNReal.ofReal ((∫ ω, F ω ∂μ) / t) :=
  measure_exists_originAverage_gt_le_of_chain R hchain.index_ne_top hchain.strictMono hF hF0
    hFint 𝒢 hanti hle hcond hfin ht

/-! ### The ball maximal function -/

/-- The normalised ball average `R⁻² ∫_{B̄_R} ρ` of the density
`ρ_ω(z) = F(ω - z)`. -/
noncomputable def ballAverage (R : MarkedReRooting Ω) (F : Ω → ℝ) (r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  (ENNReal.ofReal (r ^ 2))⁻¹ *
    ∫⁻ z in Metric.closedBall (0 : Plane) r, ENNReal.ofReal (F (R.shift z ω)) ∂volume

/-- The manuscript's `M(ρ) = sup_{R>0} R⁻² ∫_{B̄_R} ρ`. -/
noncomputable def ballMaximal (R : MarkedReRooting Ω) (F : Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ _ : 0 < r, ballAverage R F r ω

theorem ballAverage_le_ballMaximal (R : MarkedReRooting Ω) (F : Ω → ℝ) {r : ℝ} (hr : 0 < r)
    (ω : Ω) : ballAverage R F r ω ≤ ballMaximal R F ω :=
  le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) => ballAverage R F r ω) r hr

/-- The ball average exceeds `λ` exactly when the ball integral exceeds
`λ r²`. -/
theorem lt_lintegral_of_lt_ballAverage (R : MarkedReRooting Ω) (F : Ω → ℝ) (ω : Ω)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s)
    (h : ENNReal.ofReal lam < ballAverage R F s ω) :
    ENNReal.ofReal (lam * s ^ 2)
      < ∫⁻ z in Metric.closedBall (0 : Plane) s, ENNReal.ofReal (F (R.shift z ω)) ∂volume := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hnz : ENNReal.ofReal (s ^ 2) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.2 hs2]
  have h1 := ENNReal.mul_lt_mul_left hnz ENNReal.ofReal_ne_top h
  rw [ENNReal.ofReal_mul hlam.le]
  refine lt_of_lt_of_le h1 (le_of_eq ?_)
  simp only [ballAverage]
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hnz ENNReal.ofReal_ne_top, one_mul]

/-- Converse of `lt_lintegral_of_lt_ballAverage`. -/
theorem lt_ballAverage_of_lt_lintegral (R : MarkedReRooting Ω) (F : Ω → ℝ) (ω : Ω)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s)
    (h : ENNReal.ofReal (lam * s ^ 2)
      < ∫⁻ z in Metric.closedBall (0 : Plane) s, ENNReal.ofReal (F (R.shift z ω)) ∂volume) :
    ENNReal.ofReal lam < ballAverage R F s ω := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hnz : ENNReal.ofReal (s ^ 2) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.2 hs2]
  have hinv0 : (ENNReal.ofReal (s ^ 2))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hinvtop : (ENNReal.ofReal (s ^ 2))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hnz
  have hstep := ENNReal.mul_lt_mul_right hinv0 hinvtop h
  simp only [ballAverage]
  refine lt_of_le_of_lt (le_of_eq ?_) hstep
  rw [ENNReal.ofReal_mul hlam.le,
    mul_comm (ENNReal.ofReal lam) (ENNReal.ofReal (s ^ 2)), ← mul_assoc,
    ENNReal.inv_mul_cancel hnz ENNReal.ofReal_ne_top, one_mul]

/-- **A rational radius already realises the maximal function.**  This replaces
the manuscript's continuity of `R ↦ ∫_{B̄_R} ρ`: passing to a slightly larger
rational radius only increases the ball integral, and the normalisation is
continuous.  No local integrability is used. -/
theorem exists_rat_ballAverage (R : MarkedReRooting Ω) (F : Ω → ℝ) (ω : Ω) {lam : ℝ}
    (hlam : 0 < lam) (h : ENNReal.ofReal lam < ballMaximal R F ω) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ ENNReal.ofReal lam < ballAverage R F (q : ℝ) ω := by
  rw [ballMaximal, lt_iSup_iff] at h
  obtain ⟨r, hr⟩ := h
  rw [lt_iSup_iff] at hr
  obtain ⟨hrpos, hrlt⟩ := hr
  have hmono : ∀ s s' : ℝ, s ≤ s' →
      (∫⁻ z in Metric.closedBall (0 : Plane) s, ENNReal.ofReal (F (R.shift z ω)) ∂volume)
        ≤ ∫⁻ z in Metric.closedBall (0 : Plane) s',
            ENNReal.ofReal (F (R.shift z ω)) ∂volume :=
    fun s s' hss => lintegral_mono_set (Metric.closedBall_subset_closedBall hss)
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  by_cases htop : (∫⁻ z in Metric.closedBall (0 : Plane) r,
      ENNReal.ofReal (F (R.shift z ω)) ∂volume) = ∞
  · obtain ⟨p, hp1, -⟩ := exists_rat_btwn (show r < r + 1 by linarith)
    have hppos : 0 < (p : ℝ) := lt_trans hrpos hp1
    refine ⟨p, hppos, lt_ballAverage_of_lt_lintegral R F ω hlam hppos ?_⟩
    have hIq : (∫⁻ z in Metric.closedBall (0 : Plane) ((p : ℝ)),
        ENNReal.ofReal (F (R.shift z ω)) ∂volume) = ∞ := by
      refine top_unique ?_
      rw [← htop]
      exact hmono r (p : ℝ) hp1.le
    rw [hIq]
    exact ENNReal.ofReal_lt_top
  · obtain ⟨c, -, hIc⟩ : ∃ c : ℝ, 0 ≤ c ∧ (∫⁻ z in Metric.closedBall (0 : Plane) r,
        ENNReal.ofReal (F (R.shift z ω)) ∂volume) = ENNReal.ofReal c :=
      ⟨(∫⁻ z in Metric.closedBall (0 : Plane) r,
        ENNReal.ofReal (F (R.shift z ω)) ∂volume).toReal, ENNReal.toReal_nonneg,
        (ENNReal.ofReal_toReal htop).symm⟩
    have hkey := lt_lintegral_of_lt_ballAverage R F ω hlam hrpos hrlt
    rw [hIc] at hkey
    have hlt : lam * r ^ 2 < c := by
      by_contra hcon
      push_neg at hcon
      exact absurd (ENNReal.ofReal_le_ofReal hcon) (not_le.2 hkey)
    have hcpos : 0 < c := lt_of_le_of_lt (by positivity) hlt
    have hc0 : 0 ≤ c / lam := by positivity
    have hrs : r < Real.sqrt (c / lam) := by
      have hsq : r ^ 2 < c / lam := by
        rw [lt_div_iff₀ hlam]
        nlinarith
      have hstep := Real.sqrt_lt_sqrt (by positivity) hsq
      rwa [Real.sqrt_sq hrpos.le] at hstep
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hrs
    have hppos : 0 < (p : ℝ) := lt_trans hrpos hp1
    have hp2sq : (p : ℝ) ^ 2 < c / lam := by
      nlinarith [Real.sq_sqrt hc0, Real.sqrt_nonneg (c / lam)]
    have hlamq : lam * (p : ℝ) ^ 2 < c := by
      rw [lt_div_iff₀ hlam] at hp2sq
      nlinarith
    refine ⟨p, hppos, lt_ballAverage_of_lt_lintegral R F ω hlam hppos ?_⟩
    refine lt_of_lt_of_le ?_ (hmono r (p : ℝ) hp1.le)
    rw [hIc]
    exact (ENNReal.ofReal_lt_ofReal_iff hcpos).2 hlamq

/-! ### The independent uniform dyadic system -/

/-- A sub-sigma-field of `Ω` carried as data.  Wrapping it keeps it from being
picked up as an ambient `MeasurableSpace` instance on `Ω`. -/
structure EnvSigma (Ω : Type*) where
  /-- The underlying sigma-field of unmarked-environment events. -/
  sigma : MeasurableSpace Ω

/-- The unmarked-environment data.  `𝒜.sigma` is a sub-sigma-field for which the
density `ρ_ω(z) = F(ω - z)` is jointly measurable — this is the manuscript's
"this conclusion concerns `ω` alone" — the auxiliary dyadic system `𝔻'` is
independent of it, and `𝔻'` carries the uniform dyadic law.  No translation
stationarity and no triviality of any invariant sigma-field is assumed. -/
structure EnvironmentGrid (R : MarkedReRooting Ω) (μ : Measure Ω) (F : Ω → ℝ)
    (𝒜 : EnvSigma Ω) : Prop where
  /-- The environment sigma-field is a sub-sigma-field. -/
  le : 𝒜.sigma ≤ ‹MeasurableSpace Ω›
  /-- The auxiliary dyadic system is measurable. -/
  measurable_grid : Measurable R.grid
  /-- The density is an unmarked-environment observable. -/
  measurable_density :
    @Measurable (Ω × Plane) ℝ (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _
      fun p => F (R.shift p.2 p.1)
  /-- The auxiliary dyadic system is independent of the environment. -/
  indep : ProbabilityTheory.Indep 𝒜.sigma (MeasurableSpace.comap R.grid inferInstance) μ
  /-- The auxiliary dyadic system is a uniform dyadic grid. -/
  law : UniformGridLaw (μ.map R.grid)

/-- Tonelli measurability of a normalised partial integral, stated over an
arbitrary measurable space so that it can be instantiated at the environment
sigma-field. -/
theorem measurable_const_mul_setLIntegral {α : Type*} [MeasurableSpace α]
    {g : α × Plane → ℝ≥0∞} (hg : Measurable g) (c : ℝ≥0∞) (s : Set Plane) :
    Measurable fun x : α => c * ∫⁻ z in s, g (x, z) ∂volume :=
  (Measurable.lintegral_prod_right' (ν := (volume : Measure Plane).restrict s) hg).const_mul c

theorem measurable_ballAverage {R : MarkedReRooting Ω} {μ : Measure Ω} {F : Ω → ℝ}
    {𝒜 : EnvSigma Ω} (henv : EnvironmentGrid R μ F 𝒜) (r : ℝ) :
    Measurable[𝒜.sigma] (ballAverage R F r) :=
  @measurable_const_mul_setLIntegral Ω 𝒜.sigma
    (fun p : Ω × Plane => ENNReal.ofReal (F (R.shift p.2 p.1)))
    henv.measurable_density.ennreal_ofReal (ENNReal.ofReal (r ^ 2))⁻¹
    (Metric.closedBall (0 : Plane) r)

/-! ### The good grid event -/

/-- The logarithmic level at which the origin square has side exactly `8r`. -/
noncomputable def scaleLog (r : ℝ) : ℝ := Real.log (8 * r) / Real.log 2

theorem two_rpow_scaleLog {r : ℝ} (hr : 0 < r) : (2 : ℝ) ^ (scaleLog r) = 8 * r := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hcancel : Real.log 2 * (Real.log (8 * r) / Real.log 2) = Real.log (8 * r) := by
    field_simp
  rw [Real.rpow_def_of_pos h2, scaleLog, hcancel, Real.exp_log (by linarith)]

/-- The cylinder rectangle prescribing a phase window of length one at level `k`
and a relative origin well inside its square. -/
def goodCyl (r : ℝ) (k : ℤ) : Set (ℝ × ((Fin 2 → ℝ) × (Fin 0 → Fin 2 → Fin 2))) :=
  Set.Ico (scaleLog r - (k : ℝ)) (scaleLog r - (k : ℝ) + 1) ×ˢ
    ((Set.univ.pi fun _ : Fin 2 => Set.Ico (1 / 8 : ℝ) (7 / 8)) ×ˢ Set.univ)

theorem measurableSet_goodCyl (r : ℝ) (k : ℤ) : MeasurableSet (goodCyl r k) :=
  measurableSet_Ico.prod
    ((MeasurableSet.univ_pi fun _ => measurableSet_Ico).prod MeasurableSet.univ)

/-- The good grid event at level `k` for radius `r`: the level-`k` origin square
has side in `[8r, 16r)` and contains `B̄_r`. -/
def goodGridAt (r : ℝ) (k : ℤ) : Set Grid := gridCylinder k 0 ⁻¹' goodCyl r k

theorem measurableSet_goodGridAt (r : ℝ) (k : ℤ) : MeasurableSet (goodGridAt r k) :=
  ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k 0 (measurableSet_goodCyl r k)

/-- **On the good grid event the origin square has side in `[8r, 16r)` and
contains the closed ball of radius `r`.** -/
theorem closedBall_subset_of_mem_goodGridAt {r : ℝ} (hr : 0 < r) {k : ℤ} {D : Grid}
    (hD : D ∈ goodGridAt r k) :
    8 * r ≤ side D k ∧ side D k < 16 * r ∧
      Metric.closedBall (0 : Plane) r ⊆ halfOpenSquare D (originIndex k) := by
  obtain ⟨hphase, hrel, -⟩ := hD
  have hph : D.phase ∈ Set.Ico (scaleLog r - (k : ℝ)) (scaleLog r - (k : ℝ) + 1) := hphase
  have hrel' : ∀ i : Fin 2, -D.origin k i / side D k ∈ Set.Ico (1 / 8 : ℝ) (7 / 8) :=
    fun i => hrel i (Set.mem_univ i)
  have h2 : (1 : ℝ) < 2 := by norm_num
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hsideval : side D k = (2 : ℝ) ^ (D.phase + (k : ℝ)) := rfl
  have hc : (2 : ℝ) ^ (scaleLog r) = 8 * r := two_rpow_scaleLog hr
  have hc1 : (2 : ℝ) ^ (scaleLog r + 1) = 16 * r := by
    rw [Real.rpow_add h2pos, hc, Real.rpow_one]; ring
  have hlow : 8 * r ≤ side D k := by
    rw [hsideval, ← hc]
    exact (Real.rpow_le_rpow_left_iff h2).2 (by linarith [hph.1])
  have hhigh : side D k < 16 * r := by
    rw [hsideval, ← hc1]
    exact (Real.rpow_lt_rpow_left_iff h2).2 (by linarith [hph.2])
  refine ⟨hlow, hhigh, ?_⟩
  intro z hz i
  have hsidepos : 0 < side D k := side_pos D k
  have hzi : |z i| ≤ r := by
    have ha : ‖z i‖ ≤ ‖z‖ := PiLp.norm_apply_le z i
    have hb : ‖z‖ ≤ r := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.1 hz
    simpa using le_trans ha hb
  have hzi1 : -r ≤ z i := by linarith [(abs_le.1 hzi).1]
  have hzi2 : z i ≤ r := (abs_le.1 hzi).2
  have hulow : (1 / 8 : ℝ) ≤ -D.origin k i / side D k := (hrel' i).1
  have huhigh : -D.origin k i / side D k < 7 / 8 := (hrel' i).2
  have horiginlow : D.origin k i ≤ -(side D k / 8) := by
    rw [le_div_iff₀ hsidepos] at hulow
    linarith
  have horiginhigh : side D k / 8 < D.origin k i + side D k := by
    rw [div_lt_iff₀ hsidepos] at huhigh
    linarith
  have hr8 : r ≤ side D k / 8 := by linarith
  have hlowk : (square D (originIndex k)).lower i
      = D.origin k i + side D k * ((0 : ℤ) : ℝ) := rfl
  have huppk : (square D (originIndex k)).upper i
      = D.origin k i + side D k * ((0 : ℤ) : ℝ) + side D k := rfl
  rw [hlowk, huppk]
  push_cast
  exact ⟨by linarith, by linarith⟩

/-- The good grid event for radius `r`: the two levels whose phase windows tile
the unit phase interval. -/
def goodGrid (r : ℝ) : Set Grid :=
  goodGridAt r ⌈scaleLog r⌉ ∪ goodGridAt r (⌈scaleLog r⌉ - 1)

theorem measurableSet_goodGrid (r : ℝ) : MeasurableSet (goodGrid r) :=
  (measurableSet_goodGridAt r _).union (measurableSet_goodGridAt r _)

/-- The law prescribed by `UniformGridLaw` for the depth-zero cylinder. -/
noncomputable def cylLaw : Measure (ℝ × ((Fin 2 → ℝ) × (Fin 0 → Fin 2 → Fin 2))) :=
  (volume.restrict (Set.Ico (0 : ℝ) 1)).prod
    ((Measure.pi fun _ : Fin 2 => volume.restrict (Set.Ico (0 : ℝ) 1)).prod
      (PMF.uniformOfFintype (Fin 0 → Fin 2 → Fin 2)).toMeasure)

theorem measure_goodCyl (r : ℝ) (k : ℤ) :
    cylLaw (goodCyl r k)
      = volume (Set.Ico (scaleLog r - (k : ℝ)) (scaleLog r - (k : ℝ) + 1) ∩ Set.Ico (0 : ℝ) 1)
        * ENNReal.ofReal (3 / 4) ^ 2 := by
  have hprob : IsProbabilityMeasure (PMF.uniformOfFintype (Fin 0 → Fin 2 → Fin 2)).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hsub : Set.Ico (1 / 8 : ℝ) (7 / 8) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hone : (volume.restrict (Set.Ico (0 : ℝ) 1)) (Set.Ico (1 / 8 : ℝ) (7 / 8))
      = ENNReal.ofReal (3 / 4) := by
    rw [Measure.restrict_apply' measurableSet_Ico, Set.inter_eq_self_of_subset_left hsub,
      Real.volume_Ico]
    norm_num
  have hpi : (Measure.pi fun _ : Fin 2 => volume.restrict (Set.Ico (0 : ℝ) 1))
      (Set.univ.pi fun _ : Fin 2 => Set.Ico (1 / 8 : ℝ) (7 / 8))
      = ENNReal.ofReal (3 / 4) ^ 2 := by
    rw [Measure.pi_pi]
    simp only [hone, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [goodCyl, cylLaw, Measure.prod_prod, Measure.prod_prod, hpi, measure_univ, mul_one,
    Measure.restrict_apply' measurableSet_Ico]

theorem measure_goodGridAt {ν : Measure Grid} (hlaw : UniformGridLaw ν) (r : ℝ) (k : ℤ) :
    ν (goodGridAt r k)
      = volume (Set.Ico (scaleLog r - (k : ℝ)) (scaleLog r - (k : ℝ) + 1) ∩ Set.Ico (0 : ℝ) 1)
        * ENNReal.ofReal (3 / 4) ^ 2 := by
  rw [goodGridAt,
    ← Measure.map_apply (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k 0)
      (measurableSet_goodCyl r k),
    hlaw.2 k 0]
  exact measure_goodCyl r k

theorem volume_phase_window_lower {d : ℝ} (hd0 : d ≤ 0) (hd1 : -1 < d) :
    volume (Set.Ico d (d + 1) ∩ Set.Ico (0 : ℝ) 1) = ENNReal.ofReal (d + 1) := by
  have hset : Set.Ico d (d + 1) ∩ Set.Ico (0 : ℝ) 1 = Set.Ico (0 : ℝ) (d + 1) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ico]
    constructor
    · rintro ⟨⟨-, h2⟩, h3, -⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, h2⟩, h1, by linarith⟩
  rw [hset, Real.volume_Ico]
  congr 1
  ring

theorem volume_phase_window_upper {d : ℝ} (hd0 : d ≤ 0) (hd1 : -1 < d) :
    volume (Set.Ico (d + 1) (d + 1 + 1) ∩ Set.Ico (0 : ℝ) 1) = ENNReal.ofReal (-d) := by
  have hset : Set.Ico (d + 1) (d + 1 + 1) ∩ Set.Ico (0 : ℝ) 1 = Set.Ico (d + 1) (1 : ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h1, -⟩, -, h4⟩
      exact ⟨h1, h4⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by linarith⟩, by linarith, h2⟩
  rw [hset, Real.volume_Ico]
  congr 1
  ring

/-- **The independent grid contains the ball with probability at least one
half.**  Conditionally on the phase, the level of side length `ℓ ∈ [8r, 16r)`
has its origin square containing `B̄_r` with probability `(3/4)² > 1/2`; the two
admissible levels tile the unit phase window, so the conditioning is an honest
two-term decomposition. -/
theorem half_le_measure_goodGrid {ν : Measure Grid} (hlaw : UniformGridLaw ν) (r : ℝ) :
    (2 : ℝ≥0∞)⁻¹ ≤ ν (goodGrid r) := by
  have hcn : scaleLog r ≤ ((⌈scaleLog r⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hnc : ((⌈scaleLog r⌉ : ℤ) : ℝ) < scaleLog r + 1 := Int.ceil_lt_add_one _
  have hd0 : scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ) ≤ 0 := by linarith
  have hd1 : -1 < scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ) := by linarith
  have hcast : scaleLog r - (((⌈scaleLog r⌉ - 1 : ℤ)) : ℝ)
      = (scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ)) + 1 := by push_cast; ring
  have hmA : ν (goodGridAt r ⌈scaleLog r⌉)
      = ENNReal.ofReal ((scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ)) + 1)
        * ENNReal.ofReal (3 / 4) ^ 2 := by
    rw [measure_goodGridAt hlaw r ⌈scaleLog r⌉, volume_phase_window_lower hd0 hd1]
  have hmB : ν (goodGridAt r (⌈scaleLog r⌉ - 1))
      = ENNReal.ofReal (-(scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ)))
        * ENNReal.ofReal (3 / 4) ^ 2 := by
    rw [measure_goodGridAt hlaw r (⌈scaleLog r⌉ - 1), hcast,
      volume_phase_window_upper hd0 hd1]
  have hdisj : Disjoint (goodGridAt r ⌈scaleLog r⌉) (goodGridAt r (⌈scaleLog r⌉ - 1)) := by
    rw [Set.disjoint_left]
    rintro D ⟨hD1, -, -⟩ ⟨hD2, -, -⟩
    have e1 : D.phase < scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ) + 1 := hD1.2
    have e2 : scaleLog r - (((⌈scaleLog r⌉ - 1 : ℤ)) : ℝ) ≤ D.phase := hD2.1
    rw [hcast] at e2
    linarith
  have hunion : ν (goodGrid r)
      = ν (goodGridAt r ⌈scaleLog r⌉) + ν (goodGridAt r (⌈scaleLog r⌉ - 1)) := by
    rw [goodGrid]
    exact measure_union hdisj (measurableSet_goodGridAt r _)
  have hsum : ENNReal.ofReal ((scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ)) + 1)
      + ENNReal.ofReal (-(scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ))) = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      show (scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ)) + 1
          + -(scaleLog r - ((⌈scaleLog r⌉ : ℤ) : ℝ)) = 1 by ring,
      ENNReal.ofReal_one]
  rw [hunion, hmA, hmB, ← add_mul, hsum, one_mul]
  have h34 : ENNReal.ofReal (3 / 4) ^ 2 = ENNReal.ofReal (9 / 16) := by
    rw [← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [h34, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-! ### From a ball average to an origin square average -/

/-- **On the containment event the origin square average exceeds `λ/256`.**  The
square has side `ℓ < 16 r`, so `ℓ⁻² ∫_S ρ ≥ ℓ⁻² ∫_{B̄_r} ρ > (r/ℓ)² λ > λ/256`. -/
theorem originAverage_gt_of_ball (R : MarkedReRooting Ω) (F : Ω → ℝ) {ω : Ω} {lam r : ℝ}
    {k : ℤ} (hlam : 0 < lam) (hr : 0 < r)
    (h8 : 8 * r ≤ side (R.grid ω) k) (h16 : side (R.grid ω) k < 16 * r)
    (hsub : Metric.closedBall (0 : Plane) r ⊆ halfOpenSquare (R.grid ω) (originIndex k))
    (hball : ENNReal.ofReal lam < ballAverage R F r ω) :
    ENNReal.ofReal (lam / 256) < originAverage R F k ω := by
  have hlpos : 0 < side (R.grid ω) k := side_pos _ _
  have hl2 : (0 : ℝ) < side (R.grid ω) k ^ 2 := by positivity
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hIJ : (∫⁻ z in Metric.closedBall (0 : Plane) r,
      ENNReal.ofReal (F (R.shift z ω)) ∂volume)
      ≤ ∫⁻ z in halfOpenSquare (R.grid ω) (originIndex k),
          ENNReal.ofReal (F (R.shift z ω)) ∂volume := lintegral_mono_set hsub
  have hkey := lt_lintegral_of_lt_ballAverage R F ω hlam hr hball
  have hnz : ENNReal.ofReal (side (R.grid ω) k ^ 2) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.2 hl2]
  have hinv0 : (ENNReal.ofReal (side (R.grid ω) k ^ 2))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hinvtop : (ENNReal.ofReal (side (R.grid ω) k ^ 2))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hnz
  have hlsq : side (R.grid ω) k ^ 2 ≤ 256 * r ^ 2 := by nlinarith
  have hreal : lam / 256 ≤ (side (R.grid ω) k ^ 2)⁻¹ * (lam * r ^ 2) := by
    have hdiff : lam * r ^ 2 / side (R.grid ω) k ^ 2 - lam / 256
        = lam * (256 * r ^ 2 - side (R.grid ω) k ^ 2) / (256 * side (R.grid ω) k ^ 2) := by
      field_simp
    have hnum : 0 ≤ lam * (256 * r ^ 2 - side (R.grid ω) k ^ 2) := by nlinarith
    have hnonneg : 0 ≤ lam * r ^ 2 / side (R.grid ω) k ^ 2 - lam / 256 := by
      rw [hdiff]
      exact div_nonneg hnum (by positivity)
    rw [← div_eq_inv_mul]
    linarith
  have hstep : ENNReal.ofReal (lam / 256)
      ≤ (ENNReal.ofReal (side (R.grid ω) k ^ 2))⁻¹ * ENNReal.ofReal (lam * r ^ 2) := by
    rw [← ENNReal.ofReal_inv_of_pos hl2, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc ENNReal.ofReal (lam / 256)
      ≤ (ENNReal.ofReal (side (R.grid ω) k ^ 2))⁻¹ * ENNReal.ofReal (lam * r ^ 2) := hstep
    _ < (ENNReal.ofReal (side (R.grid ω) k ^ 2))⁻¹ *
          ∫⁻ z in Metric.closedBall (0 : Plane) r,
            ENNReal.ofReal (F (R.shift z ω)) ∂volume :=
        ENNReal.mul_lt_mul_right hinv0 hinvtop hkey
    _ ≤ (ENNReal.ofReal (side (R.grid ω) k ^ 2))⁻¹ *
          ∫⁻ z in halfOpenSquare (R.grid ω) (originIndex k),
            ENNReal.ofReal (F (R.shift z ω)) ∂volume := by gcongr
    _ = originAverage R F k ω := rfl

/-! ### The spatial maximal inequality -/

/-- **`s:eq:maximal` from the origin-chain estimate.**  The weak-`L¹` bound
`P[M(ρ) > λ] ≤ 512 E[F]/λ`, taking as input the complete origin dyadic chain
bound `P[sup_k A(S_k) > t] ≤ E[F]/t` (`hchainbound`) in place of the producer
data that yield it. -/
theorem measure_ballMaximal_gt_le_of_originBound (R : MarkedReRooting Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} {𝒜 : EnvSigma Ω}
    (henv : EnvironmentGrid R μ F 𝒜)
    (hchainbound : ∀ t : ℝ, 0 < t →
      μ {ω | ∃ k : ℤ, ENNReal.ofReal t < originAverage R F k ω}
        ≤ ENNReal.ofReal ((∫ ω, F ω ∂μ) / t))
    {lam : ℝ} (hlam : 0 < lam) :
    μ {ω | ENNReal.ofReal lam < ballMaximal R F ω}
      ≤ ENNReal.ofReal (512 * (∫ ω, F ω ∂μ) / lam) := by
  classical
  set S : ℕ → Set Ω := fun n =>
    {ω | 0 < ((Denumerable.ofNat ℚ n : ℚ) : ℝ) ∧
      ENNReal.ofReal lam < ballAverage R F ((Denumerable.ofNat ℚ n : ℚ) : ℝ) ω} with hSdef
  have hSmeas : ∀ n, MeasurableSet[𝒜.sigma] (S n) := by
    intro n
    by_cases hpos : 0 < ((Denumerable.ofNat ℚ n : ℚ) : ℝ)
    · have hset : S n =
          ballAverage R F ((Denumerable.ofNat ℚ n : ℚ) : ℝ) ⁻¹' Set.Ioi (ENNReal.ofReal lam) := by
        ext ω
        simp only [hSdef, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi, hpos, true_and]
      rw [hset]
      exact measurable_ballAverage henv _ measurableSet_Ioi
    · have hset : S n = (∅ : Set Ω) := by
        ext ω
        simp only [hSdef, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hc
        exact absurd hc hpos
      rw [hset]
      exact @MeasurableSet.empty Ω 𝒜.sigma
  have hunion : {ω | ENNReal.ofReal lam < ballMaximal R F ω} = ⋃ n, S n := by
    ext ω
    constructor
    · intro hω
      obtain ⟨p, hp0, hp⟩ := exists_rat_ballAverage R F ω hlam hω
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Denumerable.ofNat ℚ n = p := ⟨_, Denumerable.ofNat_encode p⟩
      refine Set.mem_iUnion.2 ⟨n, ?_, ?_⟩
      · rw [hn]; exact hp0
      · rw [hn]; exact hp
    · intro hω
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω
      exact lt_of_lt_of_le hn.2 (ballAverage_le_ballMaximal R F hn.1 ω)
  have hDsub : ∀ n, disjointed S n ⊆ S n := fun n => disjointed_le S n
  have hDmeasA : ∀ n, MeasurableSet[𝒜.sigma] (disjointed S n) := fun n =>
    MeasurableSet.disjointed hSmeas n
  have hDmeas : ∀ n, MeasurableSet (disjointed S n) := fun n => henv.le _ (hDmeasA n)
  have hDdisj : Pairwise (Function.onFun Disjoint (disjointed S)) := disjoint_disjointed S
  have hGmeas : ∀ n : ℕ, MeasurableSet (goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) :=
    fun n => measurableSet_goodGrid _
  have hpre : ∀ n : ℕ,
      MeasurableSet (R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) :=
    fun n => henv.measurable_grid (hGmeas n)
  have hincl : (⋃ n : ℕ, disjointed S n ∩
        R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ))
      ⊆ {ω | ∃ k : ℤ, ENNReal.ofReal (lam / 256) < originAverage R F k ω} := by
    intro ω hω
    obtain ⟨n, hn1, hn2⟩ := Set.mem_iUnion.1 hω
    obtain ⟨hqpos, hqlt⟩ := hDsub n hn1
    rcases hn2 with hg | hg
    · obtain ⟨h8, h16, hs⟩ := closedBall_subset_of_mem_goodGridAt hqpos hg
      exact ⟨_, originAverage_gt_of_ball R F hlam hqpos h8 h16 hs hqlt⟩
    · obtain ⟨h8, h16, hs⟩ := closedBall_subset_of_mem_goodGridAt hqpos hg
      exact ⟨_, originAverage_gt_of_ball R F hlam hqpos h8 h16 hs hqlt⟩
  have hstep : ∀ n : ℕ, μ (disjointed S n)
      ≤ 2 * μ (disjointed S n ∩ R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) := by
    intro n
    by_cases hpos : 0 < ((Denumerable.ofNat ℚ n : ℚ) : ℝ)
    · have hprod : μ (disjointed S n ∩
          R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ))
          = μ (disjointed S n) * μ (R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) :=
        (ProbabilityTheory.Indep_iff _ _ _).1 henv.indep _ _ (hDmeasA n)
          ⟨_, hGmeas n, rfl⟩
      have hmapeq : μ (R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ))
          = (μ.map R.grid) (goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) :=
        (Measure.map_apply henv.measurable_grid (hGmeas n)).symm
      have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ μ (R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) := by
        rw [hmapeq]
        exact half_le_measure_goodGrid henv.law _
      have hmul : μ (disjointed S n) * (2 : ℝ≥0∞)⁻¹
          ≤ μ (disjointed S n ∩ R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) := by
        rw [hprod]
        gcongr
      calc μ (disjointed S n) = 2 * (μ (disjointed S n) * (2 : ℝ≥0∞)⁻¹) := by
            rw [mul_comm (μ (disjointed S n)) ((2 : ℝ≥0∞)⁻¹), ← mul_assoc,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ 2 * μ (disjointed S n ∩
              R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) := by gcongr
    · have hempty : disjointed S n = ∅ := by
        refine Set.eq_empty_of_subset_empty ?_
        intro ω hω
        exact absurd (hDsub n hω).1 hpos
      simp [hempty]
  have hchainbound := hchainbound (lam / 256) (show (0 : ℝ) < lam / 256 by positivity)
  calc μ {ω | ENNReal.ofReal lam < ballMaximal R F ω}
      = μ (⋃ n, disjointed S n) := by rw [hunion, iUnion_disjointed]
    _ = ∑' n, μ (disjointed S n) := measure_iUnion hDdisj hDmeas
    _ ≤ ∑' n : ℕ, 2 * μ (disjointed S n ∩
          R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) :=
        ENNReal.tsum_le_tsum hstep
    _ = 2 * ∑' n : ℕ, μ (disjointed S n ∩
          R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) := ENNReal.tsum_mul_left
    _ = 2 * μ (⋃ n : ℕ, disjointed S n ∩
          R.grid ⁻¹' goodGrid ((Denumerable.ofNat ℚ n : ℚ) : ℝ)) := by
          rw [measure_iUnion
            (fun i j hij => (hDdisj hij).mono Set.inter_subset_left Set.inter_subset_left)
            fun n => (hDmeas n).inter (hpre n)]
    _ ≤ 2 * μ {ω | ∃ k : ℤ, ENNReal.ofReal (lam / 256) < originAverage R F k ω} := by
          gcongr
    _ ≤ 2 * ENNReal.ofReal ((∫ ω, F ω ∂μ) / (lam / 256)) := by gcongr
    _ = ENNReal.ofReal (512 * (∫ ω, F ω ∂μ) / lam) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          field_simp
          ring

/-- **`M(ρ) < ∞` almost surely, from the origin-chain estimate.** -/
theorem ballMaximal_lt_top_ae_of_originBound (R : MarkedReRooting Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℝ} {𝒜 : EnvSigma Ω}
    (henv : EnvironmentGrid R μ F 𝒜)
    (hchainbound : ∀ t : ℝ, 0 < t →
      μ {ω | ∃ k : ℤ, ENNReal.ofReal t < originAverage R F k ω}
        ≤ ENNReal.ofReal ((∫ ω, F ω ∂μ) / t)) :
    ∀ᵐ ω ∂μ, ballMaximal R F ω < ∞ := by
  have hzero : μ {ω | ballMaximal R F ω = ∞} = 0 := by
    refine le_antisymm ?_ zero_le
    have hbound : ∀ᶠ n : ℕ in Filter.atTop,
        μ {ω | ballMaximal R F ω = ∞}
          ≤ ENNReal.ofReal ((512 * ∫ ω, F ω ∂μ) * (1 / (n : ℝ))) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
      have hsub : {ω | ballMaximal R F ω = ∞}
          ⊆ {ω | ENNReal.ofReal (n : ℝ) < ballMaximal R F ω} := by
        intro ω hω
        show ENNReal.ofReal (n : ℝ) < ballMaximal R F ω
        rw [hω]
        exact ENNReal.ofReal_lt_top
      refine le_trans (measure_mono hsub) ?_
      refine le_trans (measure_ballMaximal_gt_le_of_originBound R henv hchainbound hnpos)
        (le_of_eq ?_)
      congr 1
      field_simp
    have hlim : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal ((512 * ∫ ω, F ω ∂μ) * (1 / (n : ℝ))))
        Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun n : ℕ => (512 * ∫ ω, F ω ∂μ) * (1 / (n : ℝ)))
          Filter.atTop (nhds ((512 * ∫ ω, F ω ∂μ) * 0)) :=
        tendsto_one_div_atTop_nhds_zero_nat.const_mul _
      simpa using ENNReal.tendsto_ofReal h0
    exact ge_of_tendsto hlim hbound
  rw [ae_iff]
  refine le_antisymm ?_ zero_le
  rw [← hzero]
  exact measure_mono fun ω hω => top_le_iff.1 (not_lt.1 hω)

end ReflectedGMS.SpatialMaximalInequality
