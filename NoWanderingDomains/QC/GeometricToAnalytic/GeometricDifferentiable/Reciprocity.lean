/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.RectifiablePathHelpers

/-!
# Rectifiable arcs and the Hausdorff arc-length line integral

The Eilenberg-Harrold rectifiable-connectedness theorem, arc-length Lipschitz reparametrization
of a simple rectifiable arc, and the Hausdorff arc-length line integral
`arcLengthLineIntegral_le_setLIntegral_hausdorff`. The per-density length-area inequality and
the conjugate-image modulus reciprocity `square_imageCurveFamily_modulus_ge` are assembled
downstream in `ReciprocityAssembly.lean`, on top of the planar Loewner cross-bound.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal Real

namespace NoWanderingDomains

section RhoPotentialWitness

variable {f : ℂ → ℂ} {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}


/-- **The Eilenberg–Harrold rectifiable-connectedness theorem.**

A **compact connected** set `Γ ⊆ ℂ` of **finite** `μH[1]`-length (a *rectifiable continuum*) is
*rectifiably path-connected*: any two of its points `p, q` are joined by a continuous,
**finite-total-variation** path lying entirely in `Γ`.

## Proof (the Eilenberg–Harrold / Wazewski ε-chain construction, fully formalized)

For each `k` take `ε ↓ 0` and a maximal `ε`-separated set `C = maximalSeparatedSet ε Γ` (Mathlib's
covering-number API), which is also an `ε`-cover. Connectedness threads an `ε`-chain
`p ≈ z₀ — z₁ — … — z_m ≈ q` through `C` with each hop `≤ 2ε`
(`reachable_of_isCover_preconnected`, via the two-coloring `isPreconnected_closed_iff`), and the
chain may be taken *duplicate-free* of length `≤ #C` (`exists_nodup_isChain_subset_card`, loop
excision). The **lower-content / packing bound** `#C · (ε/2) ≤ μH[1] Γ`
(`packing_card_mul_le_hausdorffMeasure_one`) — obtained here from the *localized* continuum length
estimate `ofReal_le_hausdorffMeasure_one_inter_closedBall` with **no boundary-bumping**, the
genuinely two-dimensional ingredient classically absent from Mathlib — bounds the total polygonal
length `≤ #C · 2ε + …` uniformly by `6 · μH[1] Γ`. The polygons `γ_k` (`polyPath`) have traces
within `2ε` of `Γ`; constant-speed reparametrization (`constantSpeedReparam_of_finiteVariation`)
makes them equi-Lipschitz, and Arzelà–Ascoli on the fixed compact `cthickening 1 Γ` extracts a
uniform limit `γ*`, which lies in `Γ` because `infDist (γ* τ) Γ ≤ 2ε → 0` and `Γ` is closed; lower
semicontinuity of `eVariationOn` keeps the limit's variation finite. -/
theorem exists_finiteVariation_path_of_connected_finite_hausdorff {Γ : Set ℂ}
    (hΓcpt : IsCompact Γ) (hΓconn : IsConnected Γ)
    (hΓfin : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ ≠ ∞)
    {p q : ℂ} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) :
    ∃ γ : ℝ → ℂ, γ 0 = p ∧ γ 1 = q ∧ Continuous γ ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 1) ≠ ∞ ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ Γ) := by
  classical
  set I : Set ℝ := Icc (0 : ℝ) 1 with hI
  -- Degenerate case `p = q`: use the constant path.
  by_cases hpq : p = q
  · refine ⟨fun _ => p, rfl, by rw [hpq], continuous_const, ?_, ?_⟩
    · have hsub : ((fun _ : ℝ => p) '' I).Subsingleton := by
        rintro a ⟨_, _, rfl⟩ b ⟨_, _, rfl⟩; rfl
      rw [eVariationOn.constant_on hsub]
      exact ENNReal.zero_ne_top
    · intro τ _; exact hpΓ
  -- Nontrivial case. Basic constants.
  have hΓne : Γ.Nonempty := ⟨p, hpΓ⟩
  have hΓmeas : MeasurableSet Γ := hΓcpt.isClosed.measurableSet
  have hΓpre : IsPreconnected Γ := hΓconn.isPreconnected
  set D : ℝ := ((MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ).toReal with hDdef
  -- ediam finiteness.
  have hediam_ne : Metric.ediam Γ ≠ ∞ := hΓcpt.isBounded.ediam_ne_top
  set E : ℝ := (Metric.ediam Γ).toReal with hEdef
  -- p ≠ q ⟹ 0 < dist p q ≤ ediam Γ ⟹ ediam Γ > 0, E > 0.
  have hpqdist : 0 < dist p q := dist_pos.mpr hpq
  have hdist_le_ediam : ENNReal.ofReal (dist p q) ≤ Metric.ediam Γ := by
    rw [Metric.ediam]
    exact le_trans (le_of_eq (by rw [edist_dist])) (Metric.edist_le_ediam_of_mem hpΓ hqΓ)
  have hediam_pos : 0 < Metric.ediam Γ := by
    refine lt_of_lt_of_le ?_ hdist_le_ediam
    rwa [ENNReal.ofReal_pos]
  have hediam_eq : ENNReal.ofReal E = Metric.ediam Γ := by
    rw [hEdef, ENNReal.ofReal_toReal hediam_ne]
  have hEpos : 0 < E := by
    rw [hEdef]; exact ENNReal.toReal_pos hediam_pos.ne' hediam_ne
  -- ediam ≤ μH[1] Γ, so E ≤ D, and D > 0.
  have hediam_le_H : Metric.ediam Γ ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ :=
    ediam_le_hausdorffMeasure_one_of_isPreconnected hΓpre
  have hE_le_D : E ≤ D := by
    rw [hEdef, hDdef]; exact ENNReal.toReal_mono hΓfin hediam_le_H
  have hDpos : 0 < D := lt_of_lt_of_le hEpos hE_le_D
  -- STEP 1+2: for each `k`, build a polygon path `γ k` with uniform variation bound and trace
  -- within `2 (ε k)` of Γ, where `ε k := min (E/(k+2)) (1/2)`.
  set ε : ℕ → ℝ := fun k => min (E / (k + 2)) (1 / 2) with hεdef
  have hεpos : ∀ k, 0 < ε k := by
    intro k; rw [hεdef]; simp only [lt_min_iff]
    refine ⟨?_, by norm_num⟩
    apply div_pos hEpos; positivity
  have hε_le_half : ∀ k, ε k ≤ 1 / 2 := fun k => by rw [hεdef]; exact min_le_right _ _
  have hε_lt_E : ∀ k, ε k < E := by
    intro k
    have h1 : ε k ≤ E / (k + 2) := by rw [hεdef]; exact min_le_left _ _
    refine lt_of_le_of_lt h1 ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hEpos]
  have hε_le_E : ∀ k, ε k ≤ E := fun k => le_of_lt (hε_lt_E k)
  -- `ofReal (ε k) < ediam Γ`.
  have hofReal_lt : ∀ k, ENNReal.ofReal (ε k) < Metric.ediam Γ := by
    intro k
    rw [← hediam_eq]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt (hεpos k)) |>.mpr (hε_lt_E k)
  -- The per-k polygon construction.
  have hpoly : ∀ k, ∃ (n : ℕ) (z : Fin (n + 1) → ℂ), 1 ≤ n ∧
      polyPath n z 0 = p ∧ polyPath n z 1 = q ∧ Continuous (polyPath n z) ∧
      eVariationOn (polyPath n z) I ≤ ENNReal.ofReal (6 * D) ∧
      (∀ τ ∈ I, ∃ w ∈ Γ, dist (polyPath n z τ) w ≤ 2 * ε k) := by
    intro k
    have hεk : 0 < ε k := hεpos k
    -- NNReal radius and its coercions.
    set rk : ℝ≥0 := (ε k).toNNReal with hrkdef
    have hrk_coe : (rk : ℝ) = ε k := by rw [hrkdef]; exact Real.coe_toNNReal _ (le_of_lt hεk)
    have hrk_enn : (rk : ℝ≥0∞) = ENNReal.ofReal (ε k) := by
      rw [ENNReal.coe_nnreal_eq, hrk_coe]
    set rk2 : ℝ≥0 := (ε k / 2).toNNReal with hrk2def
    have hrk2_coe : (rk2 : ℝ) = ε k / 2 := by
      rw [hrk2def]; exact Real.coe_toNNReal _ (by positivity)
    -- packing number finiteness via a finite cover.
    have hpackne : Metric.packingNumber rk Γ ≠ ⊤ := by
      obtain ⟨N, hNΓ, hNfin, hNcov⟩ :=
        Metric.exists_finite_isCover_of_isCompact (ε := rk2)
          (by rw [hrk2def, ne_eq, Real.toNNReal_eq_zero, not_le]; positivity) hΓcpt
      have hle : Metric.packingNumber rk Γ ≤ Metric.externalCoveringNumber rk2 Γ := by
        have h2 := Metric.packingNumber_two_mul_le_externalCoveringNumber rk2 Γ
        have hcoe : (2 * rk2 : ℝ≥0) = rk := by
          apply NNReal.coe_injective; rw [NNReal.coe_mul, hrk2_coe, hrk_coe]; push_cast; ring
        rwa [hcoe] at h2
      have hext_le : Metric.externalCoveringNumber rk2 Γ ≤ N.encard :=
        hNcov.externalCoveringNumber_le_encard
      exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hNfin) (le_trans hle hext_le)
    -- the maximal separated set: finite, separated, covering.
    set Cset : Set ℂ := Metric.maximalSeparatedSet rk Γ with hCsetdef
    have hCsetfin : Cset.Finite := by
      have hencardle : Cset.encard ≤ Metric.packingNumber rk Γ := by
        rw [hCsetdef, Metric.encard_maximalSeparatedSet hpackne]
      exact Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top hpackne hencardle)
    set C : Finset ℂ := hCsetfin.toFinset with hCfinDef
    have hC_eq : (↑C : Set ℂ) = Cset := hCsetfin.coe_toFinset
    have hCΓ : (↑C : Set ℂ) ⊆ Γ := by rw [hC_eq, hCsetdef]; exact Metric.maximalSeparatedSet_subset
    -- separated: distinct centers have `dist > ε k`.
    have hCsep : ∀ z ∈ C, ∀ w ∈ C, z ≠ w → ε k < dist z w := by
      intro z hz w hw hzw
      have hsep := Metric.isSeparated_maximalSeparatedSet (ε := rk) (A := Γ)
      have hzC : z ∈ Cset := by rw [← hC_eq]; exact hz
      have hwC : w ∈ Cset := by rw [← hC_eq]; exact hw
      have hedist : (rk : ℝ≥0∞) < edist z w := hsep hzC hwC hzw
      rw [edist_dist, hrk_enn] at hedist
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hεk)).mp hedist
    -- covering: every Γ-point is within `ε k` of some center.
    have hcover : ∀ x ∈ Γ, ∃ z ∈ C, dist x z ≤ ε k := by
      intro x hx
      have hcov := Metric.isCover_maximalSeparatedSet (ε := rk) hpackne
      obtain ⟨z, hzCset, hxz⟩ := hcov hx
      refine ⟨z, by rw [hCfinDef, Set.Finite.mem_toFinset]; exact hzCset, ?_⟩
      have hxz' : edist x z ≤ (rk : ℝ≥0∞) := hxz
      rw [edist_dist, hrk_enn] at hxz'
      exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hεk)).mp hxz'
    -- centers for `p` and `q`.
    obtain ⟨zp, hzpC, hpzp⟩ := hcover p hpΓ
    obtain ⟨zq, hzqC, hqzq⟩ := hcover q hqΓ
    -- build the polygon.
    obtain ⟨n, z, hn1, hncard, hz0, hzlast, hzmem, hzedge⟩ :=
      exists_polygon_in_thickening hΓpre hεk hCΓ hcover hpΓ hqΓ hzpC hzqC hpzp hqzq
    -- packing bound in ℝ: `C.card * ε k ≤ 2 D`.
    have hcard_bound : (C.card : ℝ) * ε k ≤ 2 * D := by
      have hpack := packing_card_mul_le_hausdorffMeasure_one hΓconn hΓmeas hεk
        (hofReal_lt k) hCΓ hCsep
      -- take toReal of `C.card * ofReal (ε k / 2) ≤ μH[1] Γ`.
      have hfin : (C.card : ℝ≥0∞) * ENNReal.ofReal (ε k / 2) ≠ ∞ :=
        ne_top_of_le_ne_top hΓfin hpack
      have htoreal := ENNReal.toReal_mono hΓfin hpack
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
        at htoreal
      -- `C.card * (ε k / 2) ≤ D` ⟹ `C.card * ε k ≤ 2 D`.
      nlinarith [htoreal]
    refine ⟨n, z, hn1, polyPath_zero n hn1 z ▸ hz0, ?_, polyPath_continuous n hn1 z, ?_, ?_⟩
    · rw [polyPath_one n hn1 z]; exact hzlast
    · -- variation bound.
      rw [hI]
      refine le_trans (eVariationOn_polyPath_le n hn1 z) ?_
      -- each edge length ≤ ofReal (2 ε k), so the sum ≤ n • ofReal (2 ε k).
      have hedge_enn : ∀ i : Fin n, edist (z i.castSucc) (z i.succ) ≤ ENNReal.ofReal (2 * ε k) := by
        intro i
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hzedge i)
      have hsum_le : (∑ i : Fin n, edist (z i.castSucc) (z i.succ))
          ≤ (n : ℕ) • ENNReal.ofReal (2 * ε k) := by
        refine le_trans (Finset.sum_le_sum (fun i _ => hedge_enn i)) ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      refine le_trans hsum_le ?_
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      -- `n * (2 ε k) ≤ 6 D`.
      have hn_le : (n : ℝ) ≤ (C.card : ℝ) + 1 := by exact_mod_cast hncard
      have hεE : ε k ≤ E := hε_le_E k
      nlinarith [hcard_bound, hn_le, hεpos k, hE_le_D, hDpos]
    · -- trace within `2 ε k` of Γ.
      intro τ hτ
      obtain ⟨i, hi⟩ := polyPath_dist_vertex n hn1 z hzedge τ hτ
      exact ⟨z i, hzmem i, hi⟩
  -- Extract the polygon family.
  choose n z hn1 hpoly0 hpoly1 hpolycont hpolyvar hpolytrace using hpoly
  set γpoly : ℕ → ℝ → ℂ := fun k => polyPath (n k) (z k) with hγpolydef
  -- STEP 3: constant-speed reparametrize each `γpoly k` to `δ k`.
  have hδexists : ∀ k, ∃ δ : ℝ → ℂ, δ 0 = p ∧ δ 1 = q ∧ Continuous δ ∧
      LipschitzWith (ENNReal.ofReal (6 * D)).toReal.toNNReal δ ∧
      eVariationOn δ I ≤ ENNReal.ofReal (6 * D) ∧
      (∀ τ ∈ I, ∃ w ∈ Γ, dist (δ τ) w ≤ 2 * ε k) := by
    intro k
    have hγcont : Continuous (γpoly k) := hpolycont k
    have hγvar : eVariationOn (γpoly k) I ≤ ENNReal.ofReal (6 * D) := hpolyvar k
    have hγfin : eVariationOn (γpoly k) (Icc (0 : ℝ) 1) ≠ ∞ := by
      rw [← hI]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hγvar
    obtain ⟨δ, hδ0, hδ1, hδcont, hδLip, hδvarle, hδtrace, _⟩ :=
      constantSpeedReparam_of_finiteVariation hγcont hγfin
    refine ⟨δ, ?_, ?_, hδcont, ?_, ?_, ?_⟩
    · rw [hδ0]; exact hpoly0 k
    · rw [hδ1]; exact hpoly1 k
    · -- weaken Lipschitz constant to the uniform `ofReal (6D)`-bound.
      refine hδLip.weaken ?_
      apply Real.toNNReal_mono
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      rw [← hI]; exact (le_of_eq rfl).trans (hγvar.trans_eq' (by rw [hI]))
    · -- variation bound carries through.
      exact le_trans hδvarle hγvar
    · -- trace: `δ τ = γpoly k σ` and `γpoly k σ` is within `2 ε k` of Γ.
      intro τ hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := by rw [← hI]; exact hτ
      obtain ⟨σ, hσmem, hσeq⟩ := hδtrace τ hτ'
      rw [← hσeq]
      have hσI : σ ∈ I := by rw [hI]; exact hσmem
      exact hpolytrace k σ hσI
  choose δ hδ0 hδ1 hδcont hδLipK hδvarle hδtrace using hδexists
  -- The uniform Lipschitz constant.
  set K : ℝ≥0 := (ENNReal.ofReal (6 * D)).toReal.toNNReal with hKdef
  have hδLip : ∀ k, LipschitzWith K (δ k) := hδLipK
  -- STEP 4: Arzela-Ascoli on the fixed compact `K0 := cthickening 1 Γ`.
  set K0 : Set ℂ := Metric.cthickening 1 Γ with hK0def
  have hK0cpt : IsCompact K0 := hΓcpt.cthickening
  -- each `δ k τ ∈ K0` for `τ ∈ I`.
  have hδmemK0 : ∀ k, ∀ τ ∈ I, δ k τ ∈ K0 := by
    intro k τ hτ
    obtain ⟨w, hwΓ, hwdist⟩ := hδtrace k τ hτ
    have h2εle : (2 : ℝ) * ε k ≤ 1 := by nlinarith [hε_le_half k]
    rw [hK0def]
    exact Metric.cthickening_mono h2εle Γ
      (Metric.mem_cthickening_of_dist_le _ w (2 * ε k) Γ hwΓ hwdist)
  -- Lift each `δ k` (restricted to the compact `[0,1]`) to a bounded continuous function.
  have hcs : CompactSpace (↥I) := by rw [hI]; exact isCompact_iff_compactSpace.mp isCompact_Icc
  set F : ℕ → BoundedContinuousFunction (↥I) ℂ :=
    fun k => BoundedContinuousFunction.mkOfCompact
      ⟨fun x => δ k x.1, ((hδcont k).comp continuous_subtype_val)⟩ with hFdef
  set A : Set (BoundedContinuousFunction (↥I) ℂ) := Set.range F with hAdef
  have hFmem : ∀ (f : BoundedContinuousFunction (↥I) ℂ) (x : ↥I),
      f ∈ A → f x ∈ K0 := by
    rintro f x ⟨k, rfl⟩
    exact hδmemK0 k x.1 x.2
  have hequi : Equicontinuous
      (fun (x : ↥A) => ⇑(↑x : BoundedContinuousFunction (↥I) ℂ)) := by
    have hlipA : ∀ (c : ↥A),
        LipschitzWith K (fun (x : ↥I) => ((↑c : BoundedContinuousFunction (↥I) ℂ)) x) := by
      rintro ⟨f, k, rfl⟩
      intro a b
      simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using! (hδLip k) (a : ℝ) (b : ℝ)
    exact (LipschitzWith.uniformEquicontinuous _ K hlipA).equicontinuous
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli K0 hK0cpt A hFmem hequi
  obtain ⟨Glim, _, φ, hφmono, hφtend⟩ :=
    hcompact.tendsto_subseq (fun k => subset_closure ⟨k, rfl⟩)
  -- pointwise convergence of the subsequence at each `x : ↥I`.
  have hptsub : ∀ x : ↥I, Tendsto (fun k => F (φ k) x) atTop (𝓝 (Glim x)) := by
    intro x
    exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφtend).tendsto_at x
  -- The limit path, extended off `[0,1]` by clamping (using `clmp` from RectifiablePathHelpers).
  set γstar : ℝ → ℂ := fun τ => Glim ⟨clmp τ, clmp_mem τ⟩ with hγstardef
  have hγstarcont : Continuous γstar := by
    apply Glim.continuous.comp
    apply Continuous.subtype_mk
    unfold clmp; fun_prop
  have hγstarval : ∀ τ (hτ : τ ∈ I), γstar τ = Glim ⟨τ, hτ⟩ := by
    intro τ hτ
    simp only [hγstardef]
    congr 1
    exact Subtype.ext (clmp_eq_self (by rw [← hI]; exact hτ))
  have hptconv : ∀ τ ∈ I, Tendsto (fun k => δ (φ k) τ) atTop (𝓝 (γstar τ)) := by
    intro τ hτ
    have := hptsub ⟨τ, hτ⟩
    rw [hγstarval τ hτ]
    simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using this
  -- endpoints.
  have h0I : (0 : ℝ) ∈ I := by rw [hI]; exact ⟨le_rfl, by norm_num⟩
  have h1I : (1 : ℝ) ∈ I := by rw [hI]; exact ⟨by norm_num, le_rfl⟩
  have hγstar0 : γstar 0 = p := by
    have htend := hptconv 0 h0I
    have hconst : (fun k => δ (φ k) (0:ℝ)) = fun _ => p := by funext k; exact hδ0 (φ k)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (x := p))
  have hγstar1 : γstar 1 = q := by
    have htend := hptconv 1 h1I
    have hconst : (fun k => δ (φ k) (1:ℝ)) = fun _ => q := by funext k; exact hδ1 (φ k)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (x := q))
  -- `ε k → 0`, hence `ε (φ k) → 0` (subsequence).
  have hεtend : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    have htend1 : Tendsto (fun k : ℕ => E / (k + 2)) atTop (𝓝 (0 : ℝ)) := by
      have := tendsto_const_div_atTop_nhds_zero_nat E
      have hcomp := this.comp (tendsto_add_atTop_nat 2)
      refine hcomp.congr ?_
      intro k; simp only [Function.comp_apply]; push_cast; ring_nf
    refine squeeze_zero (fun k => le_of_lt (hεpos k)) (fun k => ?_) htend1
    rw [hεdef]; exact min_le_left _ _
  have hεφtend : Tendsto (fun k => ε (φ k)) atTop (𝓝 (0 : ℝ)) :=
    hεtend.comp hφmono.tendsto_atTop
  -- trace `γstar τ ∈ Γ` via `infDist (γstar τ) Γ = 0` (Γ closed).
  have hγstarmem : ∀ τ ∈ I, γstar τ ∈ Γ := by
    intro τ hτ
    rw [hΓcpt.isClosed.mem_iff_infDist_zero hΓne]
    refine le_antisymm ?_ Metric.infDist_nonneg
    -- `infDist (γstar τ) Γ ≤ dist (γstar τ) (δ (φ k) τ) + 2 ε (φ k) → 0`.
    have hbound : ∀ k, Metric.infDist (γstar τ) Γ
        ≤ dist (γstar τ) (δ (φ k) τ) + 2 * ε (φ k) := by
      intro k
      obtain ⟨w, hwΓ, hwdist⟩ := hδtrace (φ k) τ hτ
      calc Metric.infDist (γstar τ) Γ
          ≤ dist (γstar τ) w := Metric.infDist_le_dist_of_mem hwΓ
        _ ≤ dist (γstar τ) (δ (φ k) τ) + dist (δ (φ k) τ) w := dist_triangle _ _ _
        _ ≤ dist (γstar τ) (δ (φ k) τ) + 2 * ε (φ k) := by gcongr
    -- the right-hand side tends to 0.
    have hrhs_tend : Tendsto (fun k => dist (γstar τ) (δ (φ k) τ) + 2 * ε (φ k))
        atTop (𝓝 (0 : ℝ)) := by
      have hd : Tendsto (fun k => dist (γstar τ) (δ (φ k) τ)) atTop (𝓝 (0 : ℝ)) := by
        have := (hptconv τ hτ).dist (tendsto_const_nhds (x := γstar τ))
        simpa [dist_comm] using this
      have he : Tendsto (fun k => 2 * ε (φ k)) atTop (𝓝 (0 : ℝ)) := by
        have := hεφtend.const_mul (2 : ℝ); simpa using this
      have := hd.add he; simpa using this
    -- pass the inequality to the limit.
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hrhs_tend hbound
  -- variation finiteness via lower semicontinuity.
  have hvarstar_le : eVariationOn γstar I ≤ ENNReal.ofReal (6 * D) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hmv, hvvar⟩ := exists_between hlt
    have hev := eVariationOn.lowerSemicontinuous_aux hptconv hvvar
    -- but each `eVariationOn (δ (φ k)) I ≤ ofReal(6D) < v`, contradiction.
    have hev2 : ∀ k, eVariationOn (δ (φ k)) I < v :=
      fun k => lt_of_le_of_lt (hδvarle (φ k)) hmv
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd hk (not_lt.mpr (le_of_lt (hev2 k)))
  have hvarstar_fin : eVariationOn γstar I ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvarstar_le
  -- Assemble.
  refine ⟨γstar, hγstar0, hγstar1, hγstarcont, ?_, ?_⟩
  · rw [hI] at hvarstar_fin ⊢; exact hvarstar_fin
  · intro τ hτ; rw [hI] at hτ; exact hγstarmem τ hτ


/-- **The Eilenberg–Harrold geodesic existence theorem: a length-minimizing arc exists.**

A **compact connected** set `Γ ⊆ ℂ` of **finite** `μH[1]`-length (a *rectifiable continuum*) is
*rectifiably path-connected* and the path metric is *geodesic*: any two of its points `p ≠ q` are
joined by a continuous, **finite-total-variation** path lying in `Γ` whose length **minimizes** the
total variation over *all* continuous paths from `p` to `q` in `Γ`.

## Proof

The **geodesic-existence** half is obtained here from the rectifiable path-connectedness theorem
`exists_finiteVariation_path_of_connected_finite_hausdorff`: take one finite-variation competitor
from it, so the infimum `m` of competitor lengths is finite. Choose a
minimizing sequence of competitor lengths `≤ V₀` (the first competitor's length), realize each by a
competitor, and constant-speed reparametrize (`constantSpeedReparam_of_finiteVariation`) to obtain
paths `gₙ` that are uniformly `K`-Lipschitz on `[0,1]` (with `K = V₀.toReal`), have the same
endpoints and trace in `Γ`, and length `→ m`. Lift the `gₙ` (restricted to the compact `[0,1]`) to
bounded continuous functions valued in the compact `Γ`; equi-Lipschitz gives equicontinuity, so
**Arzelà–Ascoli** yields a uniformly convergent subsequence with limit `γ*`. Continuity, the
endpoints, and the trace in `Γ` (closedness) pass to the limit, and **lower semicontinuity of
`eVariationOn`** under pointwise convergence (`eVariationOn.lowerSemicontinuous_aux`) bounds
`eVariationOn γ* [0,1] ≤ m`. Since `γ*` is a competitor its length is `≥ m`, so it equals `m` and is
minimal.

The key input is the **rectifiable path-connectedness theorem**
`exists_finiteVariation_path_of_connected_finite_hausdorff` (the Eilenberg–Harrold ε-chain /
covering-number content, classically absent from Mathlib): the existence of *one* finite-variation
competitor.

The hypothesis `p ≠ q` is part of the consumer's interface (it makes the minimal length positive for
the downstream loop-excision in `simpleRectifiableArc_of_compact_connected_finite_hausdorff`); the
minimizer construction itself does not consume it. -/
theorem geodesicMinimizer_of_connected_finite_hausdorff {Γ : Set ℂ}
    (hΓcpt : IsCompact Γ) (hΓconn : IsConnected Γ)
    (hΓfin : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ ≠ ∞)
    {p q : ℂ} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) (_hpq : p ≠ q) :
    ∃ γ : ℝ → ℂ, γ 0 = p ∧ γ 1 = q ∧ Continuous γ ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 1) ≠ ∞ ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ Γ) ∧
      (∀ η : ℝ → ℂ, Continuous η → η 0 = p → η 1 = q →
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, η τ ∈ Γ) →
          eVariationOn γ (Set.Icc (0 : ℝ) 1) ≤ eVariationOn η (Set.Icc (0 : ℝ) 1)) := by
  classical
  set I : Set ℝ := Icc (0 : ℝ) 1 with hI
  -- The competitor class: continuous paths `p → q` lying in `Γ` (no finiteness required).
  set Comp : (ℝ → ℂ) → Prop :=
    fun η => Continuous η ∧ η 0 = p ∧ η 1 = q ∧ (∀ τ ∈ I, η τ ∈ Γ) with hCompdef
  -- The set of competitor lengths in `ℝ≥0∞`, and its infimum `m`.
  set S : Set ℝ≥0∞ := {v | ∃ η, Comp η ∧ eVariationOn η I = v} with hSdef
  set m : ℝ≥0∞ := sInf S with hmdef
  -- From the rectifiable-connectedness theorem: at least one finite-length competitor exists.
  obtain ⟨γ₀, hγ₀0, hγ₀1, hγ₀cont, hγ₀fin, hγ₀mem⟩ :=
    exists_finiteVariation_path_of_connected_finite_hausdorff hΓcpt hΓconn hΓfin hpΓ hqΓ
  have hγ₀comp : Comp γ₀ := ⟨hγ₀cont, hγ₀0, hγ₀1, hγ₀mem⟩
  set V₀ : ℝ≥0∞ := eVariationOn γ₀ I with hV₀def
  have hV₀S : V₀ ∈ S := ⟨γ₀, hγ₀comp, rfl⟩
  -- `m ≤ V₀ < ∞`.
  have hmleV₀ : m ≤ V₀ := sInf_le hV₀S
  have hmne : m ≠ ∞ := ne_top_of_le_ne_top hγ₀fin hmleV₀
  -- Restrict to competitor lengths `≤ V₀`; the infimum is unchanged but now uniformly finite.
  set S' : Set ℝ≥0∞ := S ∩ Set.Iic V₀ with hS'def
  have hV₀S' : V₀ ∈ S' := ⟨hV₀S, Set.mem_Iic.mpr le_rfl⟩
  -- `sInf S' = m`.
  have hSinf' : sInf S' = m := by
    apply le_antisymm
    · -- `sInf S' ≤ m = sInf S`: any `s ∈ S` dominates an element of `S'`.
      refine le_sInf ?_
      intro s hs
      by_cases hsle : s ≤ V₀
      · exact sInf_le ⟨hs, hsle⟩
      · exact (sInf_le hV₀S').trans (le_of_lt (not_le.mp hsle))
    · -- `m = sInf S ≤ sInf S'` since `S' ⊆ S`.
      exact le_sInf (fun s hs => sInf_le hs.1)
  -- A minimizing antitone sequence of competitor lengths `≤ V₀`, tending to `m`.
  obtain ⟨u, humono, hutend, humem'⟩ :=
    exists_seq_tendsto_sInf ⟨V₀, hV₀S'⟩ (OrderBot.bddBelow S')
  rw [hSinf'] at hutend
  -- each `u n` is a competitor length `≤ V₀ < ∞`.
  have hule : ∀ n, u n ≤ V₀ := fun n => (humem' n).2
  have hune : ∀ n, u n ≠ ∞ := fun n => ne_top_of_le_ne_top hγ₀fin (hule n)
  have humem : ∀ n, u n ∈ S := fun n => (humem' n).1
  -- choose a competitor `η n` realizing each length `u n`.
  have hηchoice : ∀ n, ∃ ζ, Comp ζ ∧ eVariationOn ζ I = u n := fun n => humem n
  choose ζ hζcomp hζlen using hηchoice
  -- constant-speed reparametrization `g n` of `ζ n`: globally Lipschitz with constant
  -- `(u n).toReal`, same endpoints, trace in `Γ`, variation `≤ u n`.
  have hgexists : ∀ n, ∃ g : ℝ → ℂ, g 0 = p ∧ g 1 = q ∧ Continuous g ∧
      LipschitzWith (u n).toReal.toNNReal g ∧
      eVariationOn g I ≤ u n ∧ (∀ τ ∈ I, g τ ∈ Γ) := by
    intro n
    obtain ⟨hζcont, hζ0, hζ1, hζmem⟩ := hζcomp n
    have hζfin : eVariationOn (ζ n) I ≠ ∞ := by rw [hζlen]; exact hune n
    obtain ⟨g, hg0, hg1, hgcont, hgLip, hgvarle, hgtrace, _⟩ :=
      constantSpeedReparam_of_finiteVariation hζcont hζfin
    refine ⟨g, ?_, ?_, hgcont, ?_, ?_, ?_⟩
    · rw [hg0, hζ0]
    · rw [hg1, hζ1]
    · rw [hζlen] at hgLip; exact hgLip
    · rw [hζlen] at hgvarle; exact hgvarle
    · intro τ hτ
      obtain ⟨σ, hσmem, hσeq⟩ := hgtrace τ hτ
      rw [← hσeq]; exact hζmem σ hσmem
  choose g hg0 hg1 hgcont hgLip hgvarle hgtrace using hgexists
  -- uniform Lipschitz bound `K := (V₀).toReal.toNNReal` for all `g n`.
  set K : ℝ≥0 := V₀.toReal.toNNReal with hKdef
  have hgLipK : ∀ n, LipschitzWith K (g n) := by
    intro n
    refine (hgLip n).weaken ?_
    exact Real.toNNReal_mono ((ENNReal.toReal_le_toReal (hune n) hγ₀fin).mpr (hule n))
  -- variation of `g n` is squeezed `m ≤ eVariationOn (g n) I ≤ u n → m`.
  have hgvar_ge : ∀ n, m ≤ eVariationOn (g n) I := by
    intro n
    refine sInf_le ⟨g n, ⟨hgcont n, hg0 n, hg1 n, hgtrace n⟩, rfl⟩
  have hgvar_tend : Tendsto (fun n => eVariationOn (g n) I) atTop (𝓝 m) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hutend hgvar_ge hgvarle
  -- **Arzelà–Ascoli extraction.** Lift each `g n` (restricted to the compact `[0,1]`) to a
  -- bounded continuous function; the family is valued in the compact `Γ` and is equi-`K`-Lipschitz,
  -- hence equicontinuous. Arzelà–Ascoli gives a uniformly convergent subsequence.
  have hcs : CompactSpace (↥I) := by rw [hI]; exact isCompact_iff_compactSpace.mp isCompact_Icc
  set F : ℕ → BoundedContinuousFunction (↥I) ℂ :=
    fun n => BoundedContinuousFunction.mkOfCompact
      ⟨fun x => g n x.1, ((hgcont n).comp continuous_subtype_val)⟩ with hFdef
  set A : Set (BoundedContinuousFunction (↥I) ℂ) := Set.range F with hAdef
  have hFmem : ∀ (f : BoundedContinuousFunction (↥I) ℂ) (x : ↥I),
      f ∈ A → f x ∈ Γ := by
    rintro f x ⟨n, rfl⟩
    exact hgtrace n x.1 x.2
  have hequi : Equicontinuous
      (fun (x : ↥A) => ⇑(↑x : BoundedContinuousFunction (↥I) ℂ)) := by
    have hlipA : ∀ (c : ↥A),
        LipschitzWith K (fun (x : ↥I) => ((↑c : BoundedContinuousFunction (↥I) ℂ)) x) := by
      rintro ⟨f, n, rfl⟩
      intro a b
      simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using! (hgLipK n) (a : ℝ) (b : ℝ)
    exact (LipschitzWith.uniformEquicontinuous _ K hlipA).equicontinuous
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli Γ hΓcpt A hFmem hequi
  obtain ⟨Glim, _, φ, hφmono, hφtend⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  -- pointwise convergence of the subsequence at each `x : ↥I`.
  have hptsub : ∀ x : ↥I, Tendsto (fun n => F (φ n) x) atTop (𝓝 (Glim x)) := by
    intro x
    exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφtend).tendsto_at x
  -- **The limit path** `γstar`, extended off `[0,1]` by clamping.
  set γstar : ℝ → ℂ := fun τ => Glim ⟨clamp01 τ, clamp01_mem τ⟩ with hγstardef
  -- continuity of `γstar`.
  have hγstarcont : Continuous γstar := by
    apply Glim.continuous.comp
    apply Continuous.subtype_mk
    unfold clamp01; fun_prop
  -- on `[0,1]`, `γstar τ = Glim ⟨τ, _⟩`, and `g (φ n) τ → γstar τ`.
  have hγstarval : ∀ τ (hτ : τ ∈ I), γstar τ = Glim ⟨τ, hτ⟩ := by
    intro τ hτ
    simp only [hγstardef]
    congr 1
    exact Subtype.ext (clamp01_eq_self hτ)
  have hptconv : ∀ τ ∈ I, Tendsto (fun n => g (φ n) τ) atTop (𝓝 (γstar τ)) := by
    intro τ hτ
    have := hptsub ⟨τ, hτ⟩
    rw [hγstarval τ hτ]
    simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using this
  -- endpoints: `γstar 0 = p`, `γstar 1 = q`.
  have h0I : (0 : ℝ) ∈ I := by rw [hI]; exact ⟨le_rfl, by norm_num⟩
  have h1I : (1 : ℝ) ∈ I := by rw [hI]; exact ⟨by norm_num, le_rfl⟩
  have hγstar0 : γstar 0 = p := by
    have htend := hptconv 0 h0I
    have hconst : (fun n => g (φ n) (0:ℝ)) = fun _ => p := by funext n; exact hg0 (φ n)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (x := p))
  have hγstar1 : γstar 1 = q := by
    have htend := hptconv 1 h1I
    have hconst : (fun n => g (φ n) (1:ℝ)) = fun _ => q := by funext n; exact hg1 (φ n)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (x := q))
  -- trace: `γstar τ ∈ Γ` for `τ ∈ [0,1]` (`Γ` is closed and each `g (φ n) τ ∈ Γ`).
  have hγstarmem : ∀ τ ∈ I, γstar τ ∈ Γ := by
    intro τ hτ
    refine hΓcpt.isClosed.mem_of_tendsto (hptconv τ hτ) (Eventually.of_forall ?_)
    intro n; exact hgtrace (φ n) τ hτ
  -- **Lower semicontinuity:** `eVariationOn γstar I ≤ m`.
  have hvarstar_le : eVariationOn γstar I ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hmv, hvvar⟩ := exists_between hlt
    have hev := eVariationOn.lowerSemicontinuous_aux hptconv hvvar
    -- `eVariationOn (g (φ n)) I → m < v`, so eventually `< v`.
    have hsubtend : Tendsto (fun n => eVariationOn (g (φ n)) I) atTop (𝓝 m) :=
      hgvar_tend.comp hφmono.tendsto_atTop
    have hev2 : ∀ᶠ n in atTop, eVariationOn (g (φ n)) I < v := hsubtend.eventually_lt_const hmv
    obtain ⟨n, h1, h2⟩ := (hev.and hev2).exists
    exact absurd h1 (not_lt.mpr h2.le)
  -- `γstar` is a competitor, so its length is `≥ m`; hence `= m`, and it is finite.
  have hvarstar_ge : m ≤ eVariationOn γstar I :=
    sInf_le ⟨γstar, ⟨hγstarcont, hγstar0, hγstar1, hγstarmem⟩, rfl⟩
  have hvarstar_eq : eVariationOn γstar I = m := le_antisymm hvarstar_le hvarstar_ge
  have hvarstar_fin : eVariationOn γstar I ≠ ∞ := by rw [hvarstar_eq]; exact hmne
  -- **Assemble the minimizer.** Any competitor `η` has length `≥ m = eVariationOn γstar I`.
  refine ⟨γstar, hγstar0, hγstar1, hγstarcont, hvarstar_fin, hγstarmem, ?_⟩
  intro η hηcont hη0 hη1 hηmem
  rw [hvarstar_eq]
  exact sInf_le ⟨η, ⟨hηcont, hη0, hη1, hηmem⟩, rfl⟩

/-- **The Eilenberg–Harrold / Hahn–Mazurkiewicz topological core (reduced to geodesic existence
via `geodesicMinimizer_of_connected_finite_hausdorff`).**

A **compact connected** set `Γ ⊆ ℂ` of **finite** `μH[1]`-length is arcwise connected by a
**simple** (injective on `[0,1]`) arc of **finite total variation** lying entirely in `Γ`.

The proof is **honest analytic content** built on geodesic existence: take a
length-minimizing path `γ` (from `geodesicMinimizer_of_connected_finite_hausdorff`), pass to its
constant-speed reparametrization `δ` (`constantSpeedReparam_of_finiteVariation`), and show `δ` is
**injective** by *loop excision*: if `δ s = δ t` with `s < t`, the constant-speed identity gives the
sub-loop positive length `L·(t−s) > 0`, so excising it (re-routing over `[0,s] ∪ [t,1]`, which is
continuous precisely because `δ s = δ t`) produces a strictly shorter competitor, contradicting the
minimality of `γ`. -/
theorem simpleRectifiableArc_of_compact_connected_finite_hausdorff {Γ : Set ℂ}
    (hΓcpt : IsCompact Γ) (hΓconn : IsConnected Γ)
    (hΓfin : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ ≠ ∞)
    {p q : ℂ} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) (hpq : p ≠ q) :
    ∃ γ : ℝ → ℂ, γ 0 = p ∧ γ 1 = q ∧ Continuous γ ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 1) ≠ ∞ ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ Γ := by
  classical
  -- Geodesic minimizer `γ₀` from the EH/Arzelà–Ascoli construction.
  obtain ⟨γ₀, hγ₀0, hγ₀1, hγ₀cont, hγ₀bv, hγ₀mem, hmin⟩ :=
    geodesicMinimizer_of_connected_finite_hausdorff hΓcpt hΓconn hΓfin hpΓ hqΓ hpq
  -- Constant-speed reparametrization `δ` of `γ₀`.
  obtain ⟨δ, hδ0, hδ1, hδcont, hδLip, hδvarle, hδtrace, hδspeed⟩ :=
    constantSpeedReparam_of_finiteVariation hγ₀cont hγ₀bv
  set L : ℝ := (eVariationOn γ₀ (Icc (0 : ℝ) 1)).toReal with hLdef
  have hδ0p : δ 0 = p := by rw [hδ0, hγ₀0]
  have hδ1q : δ 1 = q := by rw [hδ1, hγ₀1]
  -- `δ` lands in `Γ` (its trace is inside `γ₀ '' [0,1] ⊆ Γ`).
  have hδmem : ∀ τ ∈ Icc (0 : ℝ) 1, δ τ ∈ Γ := by
    intro τ hτ
    obtain ⟨σ, hσmem, hσeq⟩ := hδtrace τ hτ
    rw [← hσeq]; exact hγ₀mem σ hσmem
  -- `δ` is itself a competitor, so its length is `≥` the minimal length; hence `= L`.
  have hδlen_ge : eVariationOn γ₀ (Icc (0 : ℝ) 1) ≤ eVariationOn δ (Icc (0 : ℝ) 1) :=
    hmin δ hδcont hδ0p hδ1q hδmem
  have hδlen : eVariationOn δ (Icc (0 : ℝ) 1) = eVariationOn γ₀ (Icc (0 : ℝ) 1) :=
    le_antisymm hδvarle hδlen_ge
  -- minimal length is finite and positive: `L = eVariationOn γ₀ [0,1] ∈ (0, ∞)`.
  have hγ₀ne : eVariationOn γ₀ (Icc (0 : ℝ) 1) ≠ ∞ := hγ₀bv
  have hδne : eVariationOn δ (Icc (0 : ℝ) 1) ≠ ∞ := by rw [hδlen]; exact hγ₀ne
  have hpos : 0 < eVariationOn δ (Icc (0 : ℝ) 1) := by
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
    have hle : edist (δ 0) (δ 1) ≤ eVariationOn δ (Icc (0 : ℝ) 1) :=
      eVariationOn.edist_le δ h0mem h1mem
    have hedpos : 0 < edist (δ 0) (δ 1) := by
      rw [edist_pos, hδ0p, hδ1q]; exact hpq
    exact lt_of_lt_of_le hedpos hle
  have hLpos : 0 < L := by
    rw [hLdef, ← hδlen]
    exact ENNReal.toReal_pos (ne_of_gt hpos) hδne
  -- constant-speed identity in `ℝ≥0∞` form is what `hδspeed` gives in `ℝ` form; record both.
  -- `variationOnFromTo δ [0,1] x y = L * (y - x)` for `x ≤ y` in `[0,1]`.
  have hδloc : LocallyBoundedVariationOn δ (Icc (0 : ℝ) 1) :=
    (BoundedVariationOn.locallyBoundedVariationOn (hδne))
  have hvarft : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      variationOnFromTo δ (Icc (0 : ℝ) 1) x y = L * (y - x) := by
    intro x hx y hy
    have hadd := variationOnFromTo.add hδloc (⟨le_rfl, by norm_num⟩ : (0:ℝ) ∈ Icc (0:ℝ) 1) hx hy
    have hsx := hδspeed x hx
    have hsy := hδspeed y hy
    -- `variationOnFromTo δ s 0 y = variationOnFromTo δ s 0 x + variationOnFromTo δ s x y`
    have : variationOnFromTo δ (Icc (0 : ℝ) 1) x y
        = variationOnFromTo δ (Icc (0:ℝ) 1) 0 y - variationOnFromTo δ (Icc (0:ℝ) 1) 0 x := by
      linarith [hadd]
    rw [this, hsx, hsy]; ring
  -- **Injectivity of `δ` via loop excision.**
  -- Core: if `δ s = δ t` with `s < t` (both in `[0,1]`), we reach a contradiction.
  have hexcise : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s < t → δ s = δ t → False := by
    intro s hs t ht hslt hst
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨ht0, ht1⟩ := ht
    have hsm : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hs1⟩
    have htm : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
    -- positive sub-loop length on `[s,t]`.
    have hloopvar : variationOnFromTo δ (Icc (0 : ℝ) 1) s t = L * (t - s) :=
      hvarft s hsm t htm
    have hlooppos : 0 < L * (t - s) := by
      apply mul_pos hLpos; linarith
    -- The loop endpoints cannot be `(0,1)`: else `δ 0 = δ 1`, i.e. `p = q`, contradicting `p ≠ q`.
    have hnot01 : ¬ (s = 0 ∧ t = 1) := by
      rintro ⟨rfl, rfl⟩
      rw [hδ0p, hδ1q] at hst; exact hpq hst
    have htms : t - s < 1 := by
      rcases lt_or_eq_of_le hs0 with hs0' | hs0'
      · linarith
      · rcases lt_or_eq_of_le ht1 with ht1' | ht1'
        · linarith
        · exact absurd ⟨hs0'.symm, ht1'⟩ hnot01
    -- Build the excised competitor `η` on `[0,1]`, skipping the loop `(s,t)`.
    set m : ℝ := 1 - (t - s) with hmdef
    have hmpos : 0 < m := by rw [hmdef]; linarith
    set c : ℝ := s / m with hcdef
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    have hcm : m * c = s := by rw [hcdef]; field_simp
    have hc1 : c ≤ 1 := by
      rw [hcdef, div_le_one hmpos, hmdef]; linarith
    set η : ℝ → ℂ := fun τ => if τ ≤ c then δ (m * τ) else δ (m * τ + (t - s)) with hηdef
    -- continuity of `η`: each branch continuous; they agree at `τ = c` since `δ s = δ t`.
    have hηcont : Continuous η := by
      have hcont1 : Continuous (fun τ : ℝ => δ (m * τ)) :=
        hδcont.comp (continuous_const.mul continuous_id)
      have hcont2 : Continuous (fun τ : ℝ => δ (m * τ + (t - s))) :=
        hδcont.comp ((continuous_const.mul continuous_id).add continuous_const)
      have hagree : (fun τ : ℝ => δ (m * τ)) c = (fun τ : ℝ => δ (m * τ + (t - s))) c := by
        simp only
        have e1 : m * c = s := hcm
        have e2 : m * c + (t - s) = t := by rw [hcm]; ring
        rw [e1] at e2 ⊢
        rw [e2]; exact hst
      simpa only [hηdef] using!
        (Continuous.if_le hcont1 hcont2 continuous_id continuous_const (fun x hx => by
          subst hx; exact hagree))
    -- `η 0 = p`, `η 1 = q`.
    have hη0 : η 0 = p := by
      simp only [hηdef]
      rw [if_pos hc0, mul_zero, hδ0p]
    have hη1 : η 1 = q := by
      simp only [hηdef]
      by_cases hcge : (1 : ℝ) ≤ c
      · -- `c ≥ 1` forces `c = 1` (we have `c ≤ 1`), so `m = s`, hence `t = 1` and `δ (m·1) = δ 1`.
        rw [if_pos hcge]
        have hceq : c = 1 := le_antisymm hc1 hcge
        -- `m * c = s` with `c = 1` gives `m = s`; and `m = 1-(t-s)` gives `t = 1`.
        have hms : m = s := by rw [← hcm, hceq, mul_one]
        have ht1' : t = 1 := by rw [hmdef] at hms; linarith
        rw [show m * 1 = s by rw [mul_one, hms]]
        rw [hst, ht1', hδ1q]
      · rw [if_neg hcge]
        rw [show m * 1 + (t - s) = 1 by rw [hmdef]; ring, hδ1q]
    -- trace of `η` in `Γ`.
    have hηmem : ∀ τ ∈ Icc (0 : ℝ) 1, η τ ∈ Γ := by
      intro τ hτ
      obtain ⟨hτ0, hτ1⟩ := hτ
      simp only [hηdef]
      split_ifs with h
      · apply hδmem; constructor
        · positivity
        · -- `m * τ ≤ m * c = s ≤ 1`.
          have h1 : m * τ ≤ m * c := mul_le_mul_of_nonneg_left h hmpos.le
          rw [hcm] at h1; linarith
      · apply hδmem; constructor
        · push Not at h
          have : 0 ≤ m * τ := by positivity
          linarith
        · -- `m * τ + (t - s) ≤ 1`: since `τ ≤ 1`, `m*τ ≤ m`, so `m*τ + (t-s) ≤ m + (t-s) = 1`.
          have hmt : m * τ ≤ m := by nlinarith [hmpos, hτ1]
          rw [hmdef] at hmt; linarith
    -- variation of `η`: split `[0,1]` at `c`; each piece is a monotone reparam of `δ`.
    have hηvar : eVariationOn η (Icc (0 : ℝ) 1) < eVariationOn δ (Icc (0 : ℝ) 1) := by
      -- sub-interval variation of `δ` in `ℝ≥0∞` form: `eVar δ ([0,1] ∩ [x,y]) = ofReal (L (y-x))`.
      have hδsub : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x ≤ y →
          eVariationOn δ (Icc (0 : ℝ) 1 ∩ Icc x y) = ENNReal.ofReal (L * (y - x)) := by
        intro x hx y hy hxy
        have hft := hvarft x hx y hy
        rw [variationOnFromTo.eq_of_le δ (Icc (0 : ℝ) 1) hxy] at hft
        have hsubne : eVariationOn δ (Icc (0 : ℝ) 1 ∩ Icc x y) ≠ ∞ :=
          ne_top_of_le_ne_top hδne (eVariationOn.mono δ inter_subset_left)
        rw [← hft, ENNReal.ofReal_toReal hsubne]
      -- pieces: `0 ≤ c ≤ 1`, split `[0,1]` at `c`.
      have hcmem : c ∈ Icc (0 : ℝ) 1 := ⟨hc0, hc1⟩
      have hsplit := eVariationOn.Icc_add_Icc η (a := (0:ℝ)) (b := c) (c := (1:ℝ))
        (s := Icc (0:ℝ) 1) hc0 hc1 hcmem
      -- `[0,1] ∩ [0,c] = [0,c]`, `[0,1] ∩ [c,1] = [c,1]`, `[0,1] ∩ [0,1] = [0,1]`.
      have hI1 : Icc (0:ℝ) 1 ∩ Icc 0 c = Icc 0 c := by
        rw [inter_eq_right]; exact Icc_subset_Icc le_rfl hc1
      have hI2 : Icc (0:ℝ) 1 ∩ Icc c 1 = Icc c 1 := by
        rw [inter_eq_right]; exact Icc_subset_Icc hc0 le_rfl
      have hI3 : Icc (0:ℝ) 1 ∩ Icc 0 1 = Icc (0:ℝ) 1 := by rw [inter_self]
      rw [hI1, hI2, hI3] at hsplit
      -- piece 1: `η = δ ∘ (m·)` on `[0,c]`; variation `= eVar δ [0, m·c] = eVar δ [0, s]`.
      have hpiece1 : eVariationOn η (Icc 0 c) = eVariationOn δ (Icc (0:ℝ) 1 ∩ Icc 0 s) := by
        have hcongr : eVariationOn η (Icc 0 c) = eVariationOn (fun τ => δ (m * τ)) (Icc 0 c) := by
          apply eVariationOn.congr
          intro τ hτ; simp only [hηdef]; rw [if_pos hτ.2]
        rw [hcongr]
        have hmono : MonotoneOn (fun τ => m * τ) (Icc (0:ℝ) c) := fun a _ b _ hab =>
          mul_le_mul_of_nonneg_left hab hmpos.le
        rw [show (fun τ => δ (m * τ)) = δ ∘ (fun τ => m * τ) from rfl,
          eVariationOn.comp_eq_of_monotoneOn δ (fun τ => m * τ) hmono]
        congr 1
        -- `(m·) '' [0,c] = [0,1] ∩ [0, s]`
        have hssub : Icc (0:ℝ) s ⊆ Icc (0:ℝ) 1 :=
          Icc_subset_Icc le_rfl (by rw [← hcm]; nlinarith [hmpos, hc1])
        rw [inter_eq_right.mpr hssub]
        ext v; simp only [mem_image, mem_Icc]
        constructor
        · rintro ⟨w, ⟨hw0, hwc⟩, rfl⟩
          refine ⟨by positivity, ?_⟩
          rw [← hcm]; exact mul_le_mul_of_nonneg_left hwc hmpos.le
        · rintro ⟨hv0, hvs⟩
          refine ⟨v / m, ⟨by positivity, ?_⟩, by field_simp⟩
          rw [div_le_iff₀ hmpos, mul_comm]
          rw [← hcm] at hvs; exact hvs
      -- piece 2: `η = δ ∘ (m·+(t-s))` on `[c,1]`; variation `= eVar δ [t, 1]`.
      have hpiece2 : eVariationOn η (Icc c 1) = eVariationOn δ (Icc (0:ℝ) 1 ∩ Icc t 1) := by
        have hcongr : eVariationOn η (Icc c 1)
            = eVariationOn (fun τ => δ (m * τ + (t - s))) (Icc c 1) := by
          apply eVariationOn.congr
          intro τ hτ; simp only [hηdef]
          rcases eq_or_lt_of_le hτ.1 with hc | hc
          · -- at `τ = c`, both branches agree (`δ s = δ t`).
            rw [← hc, if_pos le_rfl]
            have e2 : m * c + (t - s) = t := by rw [hcm]; ring
            rw [e2, show m * c = s from hcm, hst]
          · rw [if_neg (not_le.mpr hc)]
        rw [hcongr]
        have hmono : MonotoneOn (fun τ => m * τ + (t - s)) (Icc c (1:ℝ)) := fun a _ b _ hab => by
          simp only; nlinarith [mul_le_mul_of_nonneg_left hab hmpos.le]
        rw [show (fun τ => δ (m * τ + (t - s))) = δ ∘ (fun τ => m * τ + (t - s)) from rfl,
          eVariationOn.comp_eq_of_monotoneOn δ (fun τ => m * τ + (t - s)) hmono]
        congr 1
        -- `(m·+(t-s)) '' [c,1] = [0,1] ∩ [t, 1]`
        rw [inter_eq_right.mpr (Icc_subset_Icc (by linarith) le_rfl)]
        ext v; simp only [mem_image, mem_Icc]
        constructor
        · rintro ⟨w, ⟨hcw, hw1⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · -- `m*w+(t-s) ≥ m*c+(t-s) = s+(t-s) = t`
            have : m * c + (t - s) ≤ m * w + (t - s) := by
              have := mul_le_mul_of_nonneg_left hcw hmpos.le; linarith
            rw [hcm] at this; linarith
          · -- `m*w+(t-s) ≤ m*1+(t-s) = m+(t-s) = 1`
            have : m * w + (t - s) ≤ m * 1 + (t - s) := by
              have := mul_le_mul_of_nonneg_left hw1 hmpos.le; linarith
            rw [hmdef] at this; linarith
        · rintro ⟨hvt, hv1⟩
          refine ⟨(v - (t - s)) / m, ⟨?_, ?_⟩, ?_⟩
          · rw [le_div_iff₀ hmpos]
            have hh : m * c = s := hcm
            nlinarith [hh, hvt]
          · rw [div_le_one hmpos, hmdef]; linarith
          · rw [mul_div_cancel₀ _ (ne_of_gt hmpos)]; ring
      -- assemble: `eVar η [0,1] = L·s + L·(1-t) = L·m`, and `L·m < L = eVar δ [0,1]`.
      rw [← hsplit, hpiece1, hpiece2]
      rw [hδsub 0 ⟨le_rfl, by norm_num⟩ s hsm hs0, hδsub t htm 1 ⟨by norm_num, le_rfl⟩ ht1]
      -- `eVar δ [0,1] = ofReal L`
      have hδtot : eVariationOn δ (Icc (0:ℝ) 1) = ENNReal.ofReal L := by
        have := hδsub 0 ⟨le_rfl, by norm_num⟩ 1 ⟨by norm_num, le_rfl⟩ (by norm_num)
        rw [hI3] at this; rw [this]; congr 1; ring
      have hnn1 : 0 ≤ L * (s - 0) := by nlinarith [hLpos, hs0]
      have hnn2 : 0 ≤ L * (1 - t) := by nlinarith [hLpos, ht1]
      rw [hδtot, ← ENNReal.ofReal_add hnn1 hnn2]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by nlinarith [hnn1, hnn2])).mpr
      nlinarith [hLpos, hslt, hs0, ht1]
    -- contradiction with minimality.
    have hcontra : eVariationOn γ₀ (Icc (0 : ℝ) 1) ≤ eVariationOn η (Icc (0 : ℝ) 1) :=
      hmin η hηcont hη0 hη1 hηmem
    rw [hδlen] at hηvar
    exact absurd hcontra (not_le.mpr hηvar)
  have hδinj : InjOn δ (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    by_contra hne
    rcases lt_trichotomy s t with h | h | h
    · exact hexcise s hs t ht h hst
    · exact hne h
    · exact hexcise t ht s hs h hst.symm
  -- Final assembly: `δ` is the simple finite-variation arc.
  exact ⟨δ, hδ0p, hδ1q, hδcont, hδne, hδinj, hδmem⟩

/-- **(B) — A rectifiable continuum is arcwise connected by a simple absolutely continuous arc.**

A **compact connected** set `Γ ⊆ ℂ` of **finite** `μH[1]`-length (a *rectifiable continuum*) is a
Peano continuum, hence arcwise connected; any two of its points `p, q` are joined by a **simple**
(injective) Lipschitz — and therefore absolutely continuous — arc `δ : [0,1] → ℂ` lying entirely in
`Γ`, with `δ 0 = p`, `δ 1 = q`.

## Classical content (Eilenberg–Harrold / Hahn–Mazurkiewicz)

This is the **Eilenberg–Harrold / Wazewski** theorem (a continuum of finite linear
measure is a Peano continuum, so **Hahn–Mazurkiewicz** gives arcwise connectedness; loops are
removed to get a simple arc, and arc-length parametrization makes it Lipschitz hence absolutely
continuous).

## Decomposition

The proof separates two ingredients:

* the **topological core** — existence of a simple (injective) *finite-variation* arc joining `p`
  and `q` inside `Γ` — is the (classically Mathlib-absent) Eilenberg–Harrold / Hahn–Mazurkiewicz
  content `simpleRectifiableArc_of_compact_connected_finite_hausdorff`;
* the **arc-length Lipschitz reparametrization** — turning a simple finite-variation arc into a
  globally Lipschitz simple arc on `[0,1]` with the same endpoints, trace, and injectivity — is
  carried out in `lipschitz_simpleArc_of_finiteVariation`, using Mathlib's
  `variationOnFromTo` cumulative-variation machinery. -/
theorem rectifiable_continuum_simple_arc {Γ : Set ℂ}
    (hΓcpt : IsCompact Γ) (hΓconn : IsConnected Γ)
    (hΓfin : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ ≠ ∞)
    {p q : ℂ} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) (hpq : p ≠ q) :
    ∃ δ : ℝ → ℂ, δ 0 = p ∧ δ 1 = q ∧ Continuous δ ∧
      (∃ K : ℝ≥0, LipschitzOnWith K δ (Set.uIcc 0 1)) ∧
      Set.InjOn δ (Set.Icc (0 : ℝ) 1) ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, δ τ ∈ Γ := by
  -- Topological core: a simple finite-variation arc `γ : [0,1] → Γ` joining `p` and `q`.
  obtain ⟨γ, hγ0, hγ1, hγcont, hγbv, hγinj, hγmem⟩ :=
    simpleRectifiableArc_of_compact_connected_finite_hausdorff hΓcpt hΓconn hΓfin hpΓ hqΓ hpq
  -- Analytic half: reparametrize `γ` by arc length to a globally Lipschitz simple arc.
  obtain ⟨δ, hδ0, hδ1, hδcont, hδLip, hδinj, hδmem⟩ :=
    lipschitz_simpleArc_of_finiteVariation hγcont hγinj hγbv
  refine ⟨δ, ?_, ?_, hδcont, hδLip, hδinj, ?_⟩
  · rw [hδ0, hγ0]
  · rw [hδ1, hγ1]
  · -- `δ τ ∈ γ '' [0,1] ⊆ Γ`.
    intro τ hτ
    obtain ⟨σ, hσmem, hσeq⟩ := hδmem τ hτ
    rw [← hσeq]; exact hγmem σ hσmem



open scoped Pointwise in
/-- **1-rectifiable area inequality: line integral ≤ trace Hausdorff integral.**

For a measurable density `σ` and an **injective** curve `δ` on `[0, 1]`, the arc-length line
integral of `σ` along `δ` is at most the `σ`-weighted `μH[1]`-integral over the *trace*
`δ '' [0, 1]`: `∫₀¹ σ(δ t) ‖δ'(t)‖ dt ≤ ∫_{δ''[0,1]} σ dμH[1]`.

## Why injectivity is required (the inequality is FALSE without it)

For a *non-injective* `δ` the left-hand side counts the trace **with multiplicity** while the
right-hand side does not, so the `≤` direction fails. Concretely, take `σ ≡ 1` and a `δ` that
traverses the unit segment `[0, 1] ⊆ ℝ ⊆ ℂ` and then retraces it (`δ` has `‖δ'‖ = 2` a.e.,
parametrizing the same segment twice). Then `LHS = ∫₀¹ 2 dt = 2` while
`RHS = μH[1]([0,1]) = 1`, so `LHS ≤ RHS` is false. The injectivity hypothesis
`Set.InjOn δ (Set.Icc 0 1)` rules out exactly this overcounting; the (sole) caller
`level_slice_sigma_ge` supplies it from the injective simple arc of
`rectifiable_continuum_simple_arc`.

## Proof (measure-pushforward area formula)

The argument is the **measure-pushforward** form of the area formula:
writing `μp = (volume ⌞ [0,1]).withDensity ‖δ'‖` (the arc-length parameter measure), the LHS is
`∫⁻ z, σ z ∂(Measure.map δ μp)` (change of variables: `lintegral_map` + `withDensity`), and the
pushforward is dominated by the trace Hausdorff measure, `Measure.map δ μp ≤ μH[1] ⌞ (δ''[0,1])`,
whence `lintegral_mono'` gives the conclusion. The measure domination reduces, testing on a
measurable set, to the **reverse 1-rectifiable area inequality** for the injective absolutely
continuous curve `δ`:
`∫_A ‖δ'‖ ≤ μH[1] (δ '' A)` for every measurable `A ⊆ [0,1]`.
This is the *reverse* direction of the 1-D area formula (the forward direction
`μH[1] (δ '' A) ≤ ∫_A ‖δ'‖`, no injectivity, is `hausdorffMeasure_one_image_le`).

The reverse-area inequality `hrevarea` is established here directly, since Mathlib's tools do not
apply: its area formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul` is *equidimensional*
(`E → E`), not applicable to `δ : ℝ → ℂ`, and its only reverse-area tool `le_hausdorffMeasure_image`
needs an *antilipschitz* map, which a general injective AC curve is not. (The repo's
`eVariationOn_le_volume_image_of_injOn` is the real-valued, `ℝ → ℝ`, codimension-`0` analogue.) -/
theorem arcLengthLineIntegral_le_setLIntegral_hausdorff {σ : ℂ → ℝ≥0∞} (hσm : Measurable σ)
    {δ : ℝ → ℂ} (hδcont : Continuous δ) (hδac : AbsolutelyContinuousOnInterval δ 0 1)
    (hδinj : Set.InjOn δ (Set.Icc (0 : ℝ) 1)) :
    arcLengthLineIntegral σ δ
      ≤ ∫⁻ z in δ '' Set.Icc (0 : ℝ) 1, σ z
          ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) := by
  classical
  have hδmeas : Measurable δ := hδcont.measurable
  set w : ℝ → ℝ≥0∞ := fun t => (‖deriv δ t‖₊ : ℝ≥0∞) with hw
  have hwmeas : Measurable w := ((measurable_deriv δ).nnnorm).coe_nnreal_ennreal
  have hσδ : Measurable (fun t => σ (δ t)) := hσm.comp hδmeas
  set μp : Measure ℝ := (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity w with hμp
  -- The pushforward of the arc-length parameter measure is dominated by the trace `μH[1]`.
  have hrev : Measure.map δ μp
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ).restrict
          (δ '' Set.Icc (0 : ℝ) 1) := by
    -- ISOLATED Mathlib-absent ingredient: the reverse 1-rectifiable area inequality for the
    -- injective AC curve `δ : ℝ → ℂ`, `∫_A ‖δ'‖ ≤ μH[1] (δ '' A)` for measurable `A ⊆ [0,1]`.
    have hrevarea : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (0 : ℝ) 1 →
        ∫⁻ t in A, w t ∂volume
          ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (δ '' A) := by
      simp only [hw]
      classical
      -- f' x = smulRight 1 (deriv δ x); ‖f' x‖₊ = ‖deriv δ x‖₊
      set f' : ℝ → (ℝ →L[ℝ] ℂ) := fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (deriv δ x) with hf'def
      have hnorm : ∀ x, ‖f' x‖₊ = ‖deriv δ x‖₊ := by
        intro x; apply NNReal.coe_injective
        simp only [hf'def, coe_nnnorm, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
      -- Exact 1-D linear-map norm identity for any A = f' y
      have hAexact : ∀ y : ℝ, ∀ v : ℝ, ‖(f' y) v‖ = ‖f' y‖ * ‖v‖ := by
        intro y v
        rw [hf'def]
        simp only
        rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
          ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul, norm_smul, mul_comm]
      -- nfsl: a.e. ‖f' x - A‖ ≤ δ on s where δ is ApproximatesLinearOn (copied from Foundations)
      have nfsl : ∀ (A : ℝ →L[ℝ] ℂ) (d : ℝ≥0) (s : Set ℝ),
          MeasurableSet s → ApproximatesLinearOn δ A s d →
          (∀ x ∈ s, HasFDerivWithinAt δ (f' x) s x) →
          ∀ᵐ x ∂(volume : Measure ℝ).restrict s, ‖f' x - A‖₊ ≤ d := by
        intro A d s hs hf hfd_s
        filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) s,
          ae_restrict_mem hs]
        intro x hx xs
        apply ContinuousLinearMap.opNorm_le_bound _ d.2 fun z => ?_
        suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (d + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
          have hT : Tendsto (fun ε : ℝ => ((d : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
              (𝓝 ((d + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
            Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
          simp only [add_zero, mul_zero] at hT
          apply le_of_tendsto_of_tendsto tendsto_const_nhds hT
          filter_upwards [self_mem_nhdsWithin]; exact H
        intro ε εpos
        have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty :=
          Measure.eventually_nonempty_inter_smul_of_density_one (volume : Measure ℝ) s x hx _
            measurableSet_closedBall (Metric.measure_closedBall_pos (volume : Measure ℝ) z εpos).ne'
        obtain ⟨ρ, ρpos, hρ⟩ :
            ∃ ρ > 0, Metric.ball x ρ ∩ s ⊆ {y : ℝ | ‖δ y - δ x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
          Metric.mem_nhdsWithin_iff.1 (((hfd_s x xs).isLittleO).def εpos)
        have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ := by
          apply nhdsWithin_le_nhds
          exact eventually_singleton_add_smul_subset Metric.isBounded_closedBall
            (Metric.ball_mem_nhds x ρpos)
        obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
            ∃ r : ℝ, (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty ∧
              {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ ∧ 0 < r :=
          (B₁.and (B₂.and self_mem_nhdsWithin)).exists
        obtain ⟨a, az, ya⟩ : ∃ a, a ∈ Metric.closedBall z ε ∧ y = x + r • a := by
          simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
          rcases hy with ⟨a, az, ha⟩
          exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
        have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
          calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
            _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
            _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
        have Iineq : r * ‖(f' x - A) a‖ ≤ r * (d + ε) * (‖z‖ + ε) :=
          calc r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
                rw [map_smul, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg rpos.le]
            _ = ‖δ y - δ x - A (y - x) - (δ y - δ x - (f' x) (y - x))‖ := by
                congr 1
                simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left,
                  FunLike.coe_sub, Pi.sub_apply, map_smul]
                module
            _ ≤ ‖δ y - δ x - A (y - x)‖ + ‖δ y - δ x - (f' x) (y - x)‖ := norm_sub_le _ _
            _ ≤ d * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
            _ = r * (d + ε) * ‖a‖ := by
                simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
                  abs_of_nonneg rpos.le]
                ring
            _ ≤ r * (d + ε) * (‖z‖ + ε) := by gcongr
        calc ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
              congr 1
              simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]; abel
          _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
          _ ≤ (d + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
              apply add_le_add
              · rw [mul_assoc] at Iineq; exact (mul_le_mul_iff_right₀ rpos).1 Iineq
              · apply ContinuousLinearMap.le_opNorm
          _ ≤ (d + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
              rw [mem_closedBall_iff_norm'] at az; gcongr
      -- expand': per-piece antilipschitz LOWER bound, valid for any A = f' y when d < ‖A‖₊.
      have expand' : ∀ (y : ℝ) (d : ℝ≥0) (t : Set ℝ),
          ApproximatesLinearOn δ (f' y) t d → d < ‖f' y‖₊ →
          ((‖f' y‖₊ - d : ℝ≥0) : ℝ≥0∞) * μH[1] t ≤ μH[1] (δ '' t) := by
        intro y d t hAL hclt
        set A : ℝ →L[ℝ] ℂ := f' y with hAdef
        set K : ℝ≥0 := (‖A‖₊ - d)⁻¹ with hK
        have hAcpos : (0:ℝ) < ‖A‖ - d := by
          have : (d:ℝ) < ‖A‖ := by exact_mod_cast hclt;
          linarith
        have hKcoe : (K : ℝ) = (‖A‖ - d)⁻¹ := by
          rw [hK, NNReal.coe_inv, NNReal.coe_sub hclt.le, coe_nnnorm]
        have hanti : AntilipschitzWith K (t.domRestrict δ) := by
          apply AntilipschitzWith.of_le_mul_dist
          rintro ⟨x, hx⟩ ⟨w, hw⟩
          simp only [Set.domRestrict_apply, Subtype.dist_eq, Real.dist_eq, Complex.dist_eq]
          have hlb : (‖A‖ - d) * ‖x - w‖ ≤ ‖δ x - δ w‖ := by
            have h1 : ‖A (x - w)‖ - ‖δ x - δ w‖ ≤ ‖δ x - δ w - A (x - w)‖ := by
              calc ‖A (x - w)‖ - ‖δ x - δ w‖ ≤ ‖A (x - w) - (δ x - δ w)‖ := norm_sub_norm_le _ _
                _ = ‖δ x - δ w - A (x - w)‖ := by rw [← norm_neg]; congr 1; ring
            have h2 := hAL x hx w hw
            rw [hAexact y (x - w)] at h1
            nlinarith [norm_nonneg (x - w), norm_nonneg (δ x - δ w), le_trans h1 h2]
          rw [hKcoe, ← Real.norm_eq_abs, inv_mul_eq_div, le_div_iff₀ hAcpos]
          linarith [hlb]
        have key := hanti.le_hausdorffMeasure_image (by norm_num : (0:ℝ) ≤ 1) (univ : Set ↥t)
        rw [ENNReal.rpow_one] at key
        have him1 : μH[1] (Subtype.val '' (univ : Set ↥t)) = μH[1] (univ : Set ↥t) :=
          isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num)) _
        have himt : (Subtype.val '' (univ : Set ↥t)) = t := by simp
        rw [himt] at him1
        have himg : (t.domRestrict δ) '' (univ : Set ↥t) = δ '' t := by
          ext z; constructor
          · rintro ⟨⟨a, ha⟩, _, rfl⟩; exact ⟨a, ha, rfl⟩
          · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, mem_univ _, rfl⟩
        rw [himg, ← him1] at key
        have hmul : ((‖A‖₊ - d : ℝ≥0) : ℝ≥0∞) * K = 1 := by
          rw [hK, ← ENNReal.coe_mul, mul_inv_cancel₀ ?_, ENNReal.coe_one]
          · rw [ne_eq, tsub_eq_zero_iff_le, not_le]; exact hclt
        calc ((‖A‖₊ - d : ℝ≥0) : ℝ≥0∞) * μH[1] t
            ≤ ((‖A‖₊ - d : ℝ≥0) : ℝ≥0∞) * ((K : ℝ≥0∞) * μH[1] (δ '' t)) := by gcongr
          _ = (((‖A‖₊ - d : ℝ≥0) : ℝ≥0∞) * K) * μH[1] (δ '' t) := by rw [mul_assoc]
          _ = μH[1] (δ '' t) := by rw [hmul, one_mul]
      -- On the source `ℝ`, `μH[1] = volume`.
      have hHvol : (μH[1] : Measure ℝ) = volume := hausdorffMeasure_real
      -- aux1': the finite-error LOWER estimate.
      have aux1 : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Set.Icc (0:ℝ) 1 →
          (∀ x ∈ s, HasFDerivWithinAt δ (f' x) s x) → ∀ {ε : ℝ≥0}, 0 < ε →
          ∫⁻ x in s, (‖deriv δ x‖₊ : ℝ≥0∞) ≤ μH[1] (δ '' s) + 2 * ε * (volume s) := by
        intro s hs hsIcc hfds ε εpos
        obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hAy⟩ :
            ∃ (t : ℕ → Set ℝ) (A : ℕ → (ℝ →L[ℝ] ℂ)),
              Pairwise (Function.onFun Disjoint t) ∧
                (∀ n : ℕ, MeasurableSet (t n)) ∧
                  (s ⊆ ⋃ n : ℕ, t n) ∧
                    (∀ n : ℕ, ApproximatesLinearOn δ (A n) (s ∩ t n) ε) ∧
                      (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt δ s f' hfds (fun _ => ε)
            (fun _ => εpos.ne')
        -- ∫_s ‖δ'‖ = ∑' ∫_{s∩tₙ} ‖δ'‖  (disjoint cover)
        have hsplit_int : ∫⁻ x in s, (‖deriv δ x‖₊ : ℝ≥0∞)
            = ∑' n, ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞) := by
          rw [← lintegral_iUnion (fun n => hs.inter (t_meas n))
            (pairwise_disjoint_mono t_disj fun n => inter_subset_right),
            ← inter_iUnion, inter_eq_self_of_subset_left t_cover]
        rw [hsplit_int]
        -- per piece: ∫_{s∩tₙ} ‖δ'‖ ≤ μH[1](δ''(s∩tₙ)) + 2ε·vol(s∩tₙ)
        have hpiece : ∀ n, ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞)
            ≤ μH[1] (δ '' (s ∩ t n)) + 2 * ε * volume (s ∩ t n) := by
          intro n
          rcases eq_empty_or_nonempty s with hse | hsne
          · subst hse; simp [Set.empty_inter]
          -- get y with A n = f' y
          obtain ⟨y, hys, hAyn⟩ := hAy hsne n
          -- ∫_{s∩tₙ} ‖δ'‖ ≤ (‖A n‖₊ + ε)·vol(s∩tₙ)  via nfsl
          have hub : ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞)
              ≤ ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) := by
            calc ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞)
                ≤ ∫⁻ _ in s ∩ t n, ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) := by
                  apply lintegral_mono_ae
                  filter_upwards [nfsl (A n) ε (s ∩ t n) (hs.inter (t_meas n)) (ht n)
                    (fun x hx => (hfds x hx.1).mono inter_subset_left)]
                  intro x hx
                  -- goal: ‖deriv δ x‖₊ ≤ ‖A n‖₊ + ε
                  rw [ENNReal.coe_le_coe]
                  have hd : ‖f' x‖₊ ≤ ‖A n‖₊ + ε := by
                    calc ‖f' x‖₊ = ‖A n + (f' x - A n)‖₊ := by rw [add_sub_cancel]
                      _ ≤ ‖A n‖₊ + ‖f' x - A n‖₊ := nnnorm_add_le _ _
                      _ ≤ ‖A n‖₊ + ε := by gcongr
                  rwa [hnorm] at hd
                _ = ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) := by
                  rw [setLIntegral_const]
          -- combine with expand' (handle d<‖A‖ vs not) using the per-piece numeric lemma
          have hexp : ε < ‖A n‖₊ →
              ((‖A n‖₊ - ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) ≤ μH[1] (δ '' (s ∩ t n)) := by
            intro hlt
            have hclt' : ε < ‖f' y‖₊ := by rwa [← hAyn]
            have he := expand' y ε (s ∩ t n) (hAyn ▸ ht n) hclt'
            rw [← hAyn, hHvol] at he
            exact he
          -- numeric per-piece bound
          have hnum : ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n)
              ≤ μH[1] (δ '' (s ∩ t n)) + 2 * (ε : ℝ≥0∞) * volume (s ∩ t n) := by
            rcases lt_or_ge ε (‖A n‖₊) with hlt | hge
            · have h := hexp hlt
              have hsplitc : ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞)
                  = ((‖A n‖₊ - ε : ℝ≥0) : ℝ≥0∞) + 2 * (ε : ℝ≥0∞) := by
                rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by rfl, ← ENNReal.coe_mul,
                  ← ENNReal.coe_add, ENNReal.coe_inj, two_mul, ← add_assoc,
                  tsub_add_cancel_of_le hlt.le]
              rw [hsplitc, add_mul, mul_assoc]
              exact add_le_add h le_rfl
            · have hle : ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) ≤ 2 * (ε : ℝ≥0∞) := by
                rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by rfl, ← ENNReal.coe_mul,
                  ENNReal.coe_le_coe, two_mul]
                gcongr
              calc ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n)
                  ≤ 2 * (ε : ℝ≥0∞) * volume (s ∩ t n) := by gcongr
                _ ≤ μH[1] (δ '' (s ∩ t n)) + 2 * (ε : ℝ≥0∞) * volume (s ∩ t n) := le_add_self
          exact hub.trans hnum
        -- sum the pieces
        calc ∑' n, ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞)
            ≤ ∑' n, (μH[1] (δ '' (s ∩ t n)) + 2 * ε * volume (s ∩ t n)) :=
              ENNReal.tsum_le_tsum hpiece
          _ = (∑' n, μH[1] (δ '' (s ∩ t n))) + ∑' n, 2 * ε * volume (s ∩ t n) := by
              rw [ENNReal.tsum_add]
          _ ≤ μH[1] (δ '' s) + 2 * ε * volume s := by
              apply add_le_add
              · -- reassembly superadditivity
                set P : ℕ → Set ℝ := fun n => s ∩ t n with hP
                have hPmeas : ∀ n, MeasurableSet (P n) := fun n => hs.inter (t_meas n)
                have hPsub : ∀ n, P n ⊆ Set.Icc (0:ℝ) 1 := fun n => (inter_subset_left).trans hsIcc
                have hinjImgMeas : ∀ n, MeasurableSet (δ '' P n) := fun n =>
                  (hPmeas n).image_of_continuousOn_injOn hδcont.continuousOn (hδinj.mono (hPsub n))
                have hImgDisj : Pairwise (Function.onFun Disjoint (fun n => δ '' P n)) := by
                  intro i j hij
                  simp only [Function.onFun]
                  rw [Set.disjoint_iff_inter_eq_empty]
                  ext z
                  simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
                  rintro ⟨a, haP, rfl⟩ ⟨b, hbP, hb⟩
                  have hab : a = b := hδinj (hPsub i haP) (hPsub j hbP) hb.symm
                  subst hab
                  exact (Set.disjoint_left.mp (t_disj hij) haP.2) hbP.2
                have hmU : μH[1] (⋃ n, δ '' P n) = ∑' n, μH[1] (δ '' P n) :=
                  measure_iUnion hImgDisj hinjImgMeas
                calc ∑' n, μH[1] (δ '' (s ∩ t n)) = μH[1] (⋃ n, δ '' P n) := hmU.symm
                  _ ≤ μH[1] (δ '' s) := by
                      apply measure_mono
                      rw [← image_iUnion]
                      exact Set.image_mono (iUnion_subset (fun n => inter_subset_left))
              · -- ∑' 2ε vol(s∩tₙ) = 2ε vol s
                rw [ENNReal.tsum_mul_left, ← measure_iUnion
                  (pairwise_disjoint_mono t_disj fun n => inter_subset_right)
                  (fun n => hs.inter (t_meas n)), ← inter_iUnion,
                  inter_eq_self_of_subset_left t_cover]
      -- aux2': let ε → 0 for finite-volume sets.
      have aux2 : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Set.Icc (0:ℝ) 1 → volume s ≠ ∞ →
          (∀ x ∈ s, HasFDerivWithinAt δ (f' x) s x) →
          ∫⁻ x in s, (‖deriv δ x‖₊ : ℝ≥0∞) ≤ μH[1] (δ '' s) := by
        intro s hs hsIcc hsfin hfds
        have hlim : Tendsto (fun ε : ℝ≥0 =>
            μH[1] (δ '' s) + 2 * (ε : ℝ≥0∞) * (volume s)) (𝓝[>] 0)
            (𝓝 (μH[1] (δ '' s) + 2 * (0 : ℝ≥0) * (volume s))) := by
          apply Tendsto.mono_left _ nhdsWithin_le_nhds
          refine tendsto_const_nhds.add ?_
          refine ENNReal.Tendsto.mul_const ?_ (Or.inr hsfin)
          exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id)
            (Or.inr ENNReal.coe_ne_top)
        simp only [ENNReal.coe_zero, mul_zero, zero_mul, add_zero] at hlim
        apply ge_of_tendsto hlim
        filter_upwards [self_mem_nhdsWithin]
        intro ε εpos
        rw [mem_Ioi] at εpos
        exact aux1 hs hsIcc hfds εpos
      -- Main: reduce arbitrary measurable A ⊆ [0,1] to the a.e.-differentiability set D.
      intro A hA hAIcc
      -- a.e. differentiability of δ on [0,1].
      have hδdiff : ∀ᵐ x : ℝ, x ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ x :=
        hδac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
      set Dgood : Set ℝ := {x : ℝ | DifferentiableAt ℝ δ x} with hDgood
      have hDgoodMeas : MeasurableSet Dgood := by
        have : Dgood = {x | DifferentiableAt ℝ δ x} := rfl
        -- the set of differentiability points of a continuous function is measurable
        rw [this]
        exact (measurableSet_of_differentiableAt ℝ δ)
      set D : Set ℝ := A ∩ Dgood with hDdef
      have hDmeas : MeasurableSet D := hA.inter hDgoodMeas
      have hDIcc : D ⊆ Set.Icc (0:ℝ) 1 := (inter_subset_left).trans hAIcc
      -- volume (A \ D) = 0
      have hADnull : volume (A \ D) = 0 := by
        -- A \ D = A \ Dgood ⊆ {x ∈ uIcc 0 1 | ¬ diff} (since A ⊆ [0,1]), which is null.
        have hsub : A \ D ⊆ {x : ℝ | ¬ (x ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ x)} := by
          intro x hx
          rw [mem_ofPred_eq, Classical.not_imp]
          refine ⟨Set.mem_uIcc.mpr (Or.inl (hAIcc hx.1)), ?_⟩
          intro hxd
          exact hx.2 ⟨hx.1, hxd⟩
        exact measure_mono_null hsub (ae_iff.mp hδdiff)
      -- ∫_A ‖δ'‖ = ∫_D ‖δ'‖
      have hintEq : ∫⁻ x in A, (‖deriv δ x‖₊ : ℝ≥0∞) = ∫⁻ x in D, (‖deriv δ x‖₊ : ℝ≥0∞) := by
        have haeeq : A =ᵐ[volume] D := by
          rw [ae_eq_set]
          refine ⟨hADnull, ?_⟩
          rw [Set.sdiff_eq_empty.mpr (inter_subset_left)]; simp
        exact setLIntegral_congr haeeq
      -- δ''D ⊆ δ''A
      have himgSub : δ '' D ⊆ δ '' A := Set.image_mono inter_subset_left
      -- HasFDerivWithinAt on D
      have hfdsD : ∀ x ∈ D, HasFDerivWithinAt δ (f' x) D x := by
        intro x hx
        have hxd : DifferentiableAt ℝ δ x := hx.2
        have : HasDerivAt δ (deriv δ x) x := hxd.hasDerivAt
        have hfd : HasFDerivAt δ (f' x) x := by
          rw [hf'def]; exact this.hasFDerivAt
        exact hfd.hasFDerivWithinAt
      -- Reduce A to finite-measure disjoint pieces via spanning sets of volume.
      set u : ℕ → Set ℝ := fun n => disjointed (spanningSets (volume : Measure ℝ)) n with hu_def
      have u_meas : ∀ n, MeasurableSet (u n) := fun n =>
        MeasurableSet.disjointed (fun i => measurableSet_spanningSets (volume : Measure ℝ) i) n
      have hDcover : D = ⋃ n, D ∩ u n := by
        rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
      rw [hintEq]
      calc ∫⁻ x in D, (‖deriv δ x‖₊ : ℝ≥0∞)
          = ∑' n, ∫⁻ x in D ∩ u n, (‖deriv δ x‖₊ : ℝ≥0∞) := by
            rw [← lintegral_iUnion (fun n => hDmeas.inter (u_meas n))
              (pairwise_disjoint_mono (disjoint_disjointed (spanningSets (volume : Measure ℝ)))
                (fun n => inter_subset_right)), ← hDcover]
        _ ≤ ∑' n, μH[1] (δ '' (D ∩ u n)) := by
            apply ENNReal.tsum_le_tsum fun n => ?_
            apply aux2 (hDmeas.inter (u_meas n)) ((inter_subset_left).trans hDIcc) ?_
              (fun x hx => (hfdsD x hx.1).mono inter_subset_left)
            have : volume (u n) < ∞ :=
              lt_of_le_of_lt (measure_mono (disjointed_subset _ _))
                (measure_spanningSets_lt_top (volume : Measure ℝ) n)
            exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
        _ = μH[1] (⋃ n, δ '' (D ∩ u n)) := by
            rw [measure_iUnion ?_ ?_]
            · -- pairwise disjoint images via injectivity
              intro i j hij
              simp only [Function.onFun]
              rw [Set.disjoint_iff_inter_eq_empty]
              ext z
              simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
              rintro ⟨a, haP, rfl⟩ ⟨b, hbP, hb⟩
              have hsubIcc : ∀ k, D ∩ u k ⊆ Set.Icc (0:ℝ) 1 :=
                fun k => (inter_subset_left).trans hDIcc
              have hab : a = b := hδinj (hsubIcc i haP) (hsubIcc j hbP) hb.symm
              subst hab
              exact (Set.disjoint_left.mp
                (disjoint_disjointed (spanningSets (volume : Measure ℝ)) hij) haP.2) hbP.2
            · intro n
              exact (hDmeas.inter (u_meas n)).image_of_continuousOn_injOn hδcont.continuousOn
                (hδinj.mono ((inter_subset_left).trans hDIcc))
        _ ≤ μH[1] (δ '' A) := by
            apply measure_mono
            rw [← image_iUnion, ← hDcover]
            exact himgSub
    -- Wrap the per-set reverse-area bound into the measure inequality.
    refine Measure.le_iff.mpr (fun E hE => ?_)
    rw [Measure.map_apply hδmeas hE, hμp, withDensity_apply _ (hδmeas hE),
      Measure.restrict_restrict (hδmeas hE), Measure.restrict_apply hE]
    set A : Set ℝ := δ ⁻¹' E ∩ Set.Icc (0 : ℝ) 1 with hA
    have hAmeas : MeasurableSet A := (hδmeas hE).inter measurableSet_Icc
    have h1 : ∫⁻ t in A, w t ∂volume ≤ μH[1] (δ '' A) :=
      hrevarea A hAmeas Set.inter_subset_right
    have h2 : δ '' A ⊆ E ∩ (δ '' Set.Icc (0 : ℝ) 1) := by
      rintro z ⟨τ, ⟨hτE, hτI⟩, rfl⟩
      exact ⟨hτE, ⟨τ, hτI, rfl⟩⟩
    exact h1.trans (measure_mono h2)
  -- The LHS is the σ-integral against the pushforward (change of variables).
  have hstep1 : arcLengthLineIntegral σ δ = ∫⁻ z, σ z ∂(Measure.map δ μp) := by
    rw [lintegral_map hσm hδmeas]
    have hcov : ∫⁻ t, σ (δ t) ∂μp
        = ∫⁻ t, (w t) * σ (δ t) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      rw [hμp, lintegral_withDensity_eq_lintegral_mul _ hwmeas hσδ]; rfl
    rw [hcov]
    unfold arcLengthLineIntegral
    refine lintegral_congr (fun t => ?_)
    simp only [hw]; ring
  rw [hstep1]
  calc ∫⁻ z, σ z ∂(Measure.map δ μp)
      ≤ ∫⁻ z, σ z ∂((MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ).restrict
          (δ '' Set.Icc (0 : ℝ) 1)) := lintegral_mono' hrev le_rfl
    _ = ∫⁻ z in δ '' Set.Icc (0 : ℝ) 1, σ z
          ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) := rfl


end RhoPotentialWitness

end NoWanderingDomains
