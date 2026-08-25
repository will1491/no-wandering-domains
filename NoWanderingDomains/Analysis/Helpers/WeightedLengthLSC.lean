/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.RectifiablePathHelpers
import NoWanderingDomains.QC.Defs.Geometric

/-!
# Weighted-length lower semicontinuity and chain interpolation

Compactness and semicontinuity bricks for the Beurling chain potential of the planar Loewner
reciprocity workstream (`QC/GeometricToAnalytic/Loewner/`):

* `lipschitzOnWith_uIcc_absolutelyContinuousOnInterval` — a curve Lipschitz on `[0,1]` is
  absolutely continuous on `[0,1]` (the bridge from the Eilenberg–Harrold arc regularity to
  curve-family membership);
* `exists_subseq_tendstoUniformlyOn_of_lipschitzWith` — Arzelà–Ascoli for a uniformly
  Lipschitz, uniformly bounded sequence of curves on `[0,1]`;
* `arcLengthLineIntegral_le_liminf_of_tendstoUniformlyOn` — lower semicontinuity of the
  weighted length `∫_γ g ds` against a **continuous** weight under uniform convergence of
  uniformly Lipschitz curves;
* `exists_lipschitz_interpolation` — a discrete chain interpolates to a single Lipschitz
  curve whose weighted length against **any** Lipschitz weight is controlled by the chain
  cost plus an error `Kg · h · L` (Riemann-sum comparison; the error vanishes as the mesh
  `h → 0` for a fixed weight).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Lipschitz on `[0,1]` implies absolutely continuous on `[0,1]`.** The `ε`–`δ`
characterization is immediate: take `δ = ε / (K + 1)`. This bridges the arc-length
Lipschitz regularity produced by the Eilenberg–Harrold machinery to the
`AbsolutelyContinuousOnInterval` regularity required for curve-family membership. -/
theorem lipschitzOnWith_uIcc_absolutelyContinuousOnInterval {δ : ℝ → ℂ} {K : ℝ≥0}
    (h : LipschitzOnWith K δ (Set.uIcc 0 1)) :
    AbsolutelyContinuousOnInterval δ 0 1 :=
  h.absolutelyContinuousOnInterval

/-- **Arzelà–Ascoli for uniformly Lipschitz curves.** A sequence of `L`-Lipschitz curves
`γ j : ℝ → ℂ`, uniformly bounded on `[0,1]`, has a subsequence converging uniformly on
`[0,1]` to a globally `L`-Lipschitz limit (build the limit on `[0,1]` and extend by
clamping the parameter, which preserves the Lipschitz constant).

Proof route: diagonal extraction on the rationals of `[0,1]` (pointwise values lie in a
compact ball), then equicontinuity upgrades pointwise-on-dense to uniform convergence, and
the limit inherits the Lipschitz bound. -/
theorem exists_subseq_tendstoUniformlyOn_of_lipschitzWith {γ : ℕ → ℝ → ℂ} {L : ℝ≥0}
    (hlip : ∀ j, LipschitzWith L (γ j)) {R : ℝ}
    (hbd : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ Metric.closedBall (0 : ℂ) R) :
    ∃ (φ : ℕ → ℕ) (γ₀ : ℝ → ℂ), StrictMono φ ∧ LipschitzWith L γ₀ ∧
      TendstoUniformlyOn (fun j => γ (φ j)) γ₀ atTop (Set.Icc 0 1) := by
  classical
  set I : Set ℝ := Set.Icc (0 : ℝ) 1 with hI
  have hcs : CompactSpace (↥I) := isCompact_iff_compactSpace.mp isCompact_Icc
  -- Lift the curves (restricted to the compact `[0,1]`) to bounded continuous functions.
  set F : ℕ → BoundedContinuousFunction (↥I) ℂ :=
    fun n => BoundedContinuousFunction.mkOfCompact
      ⟨fun x => γ n x.1, ((hlip n).continuous.comp continuous_subtype_val)⟩ with hFdef
  set A : Set (BoundedContinuousFunction (↥I) ℂ) := Set.range F with hAdef
  have hFmem : ∀ (f : BoundedContinuousFunction (↥I) ℂ) (x : ↥I),
      f ∈ A → f x ∈ Metric.closedBall (0 : ℂ) R := by
    rintro f x ⟨n, rfl⟩
    exact hbd n x.1 x.2
  -- Equi-Lipschitz ⇒ equicontinuous.
  have hequi : Equicontinuous
      (fun (x : ↥A) => ⇑(↑x : BoundedContinuousFunction (↥I) ℂ)) := by
    have hlipA : ∀ (c : ↥A),
        LipschitzWith L (fun (x : ↥I) => ((↑c : BoundedContinuousFunction (↥I) ℂ)) x) := by
      rintro ⟨f, n, rfl⟩
      intro a b
      simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using! (hlip n) (a : ℝ) (b : ℝ)
    exact (LipschitzWith.uniformEquicontinuous _ L hlipA).equicontinuous
  -- Arzelà–Ascoli: the closure of the family is compact; extract a convergent subsequence.
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) R)
      (isCompact_closedBall _ _) A hFmem hequi
  obtain ⟨Glim, _, φ, hφmono, hφtend⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  -- The limit curve, extended off `[0,1]` by clamping the parameter.
  set γ₀ : ℝ → ℂ := fun τ => Glim ⟨clmp τ, clmp_mem τ⟩ with hγ₀def
  have hptsub : ∀ x : ↥I, Tendsto (fun n => F (φ n) x) atTop (𝓝 (Glim x)) := fun x =>
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφtend).tendsto_at x
  have hγ₀val : ∀ τ (hτ : τ ∈ I), γ₀ τ = Glim ⟨τ, hτ⟩ := by
    intro τ hτ
    simp only [hγ₀def]
    congr 1
    exact Subtype.ext (clmp_eq_self hτ)
  -- `Glim` satisfies the `L`-Lipschitz bound on `I` (limit of `L`-Lipschitz maps).
  have hGlip : ∀ x y : ↥I, dist (Glim x) (Glim y) ≤ (L : ℝ) * dist (x : ℝ) (y : ℝ) := by
    intro x y
    have hconv : Tendsto (fun n => dist (F (φ n) x) (F (φ n) y)) atTop
        (𝓝 (dist (Glim x) (Glim y))) := (hptsub x).dist (hptsub y)
    refine le_of_tendsto hconv (Eventually.of_forall fun n => ?_)
    have := (hlip (φ n)).dist_le_mul (x : ℝ) (y : ℝ)
    simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using this
  -- `clmp` is `1`-Lipschitz, so the clamped limit is globally `L`-Lipschitz.
  have hclmp : LipschitzWith 1 clmp := by
    have h := ((LipschitzWith.id (α := ℝ)).const_min 1).const_max 0
    exact h
  have hγ₀lip : LipschitzWith L γ₀ := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    calc dist (γ₀ a) (γ₀ b)
        ≤ (L : ℝ) * dist (clmp a) (clmp b) := hGlip ⟨clmp a, clmp_mem a⟩ ⟨clmp b, clmp_mem b⟩
      _ ≤ (L : ℝ) * dist a b := by
          have := hclmp.dist_le_mul a b
          rw [NNReal.coe_one, one_mul] at this
          exact mul_le_mul_of_nonneg_left this L.coe_nonneg
  -- Uniform convergence on `[0,1]` from convergence in the sup metric.
  have huc : TendstoUniformlyOn (fun j => γ (φ j)) γ₀ atTop I := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev : ∀ᶠ n in atTop, dist ((F ∘ φ) n) Glim < ε :=
      (Metric.tendsto_nhds.mp hφtend) ε hε
    filter_upwards [hev] with n hn τ hτ
    have hle : dist (F (φ n) ⟨τ, hτ⟩) (Glim ⟨τ, hτ⟩) ≤ dist ((F ∘ φ) n) Glim :=
      BoundedContinuousFunction.dist_coe_le_dist _
    have heq : F (φ n) ⟨τ, hτ⟩ = γ (φ n) τ := by
      simp [hFdef, BoundedContinuousFunction.mkOfCompact]
    rw [hγ₀val τ hτ]
    rw [heq] at hle
    calc dist (Glim ⟨τ, hτ⟩) (γ (φ n) τ) = dist (γ (φ n) τ) (Glim ⟨τ, hτ⟩) := dist_comm _ _
      _ ≤ dist ((F ∘ φ) n) Glim := hle
      _ < ε := hn
  exact ⟨φ, γ₀, hφmono, hγ₀lip, huc⟩

/-- **Lower semicontinuity of the weighted length under uniform convergence.** For a
continuous nonnegative weight `g` and uniformly `L`-Lipschitz curves `γ j → γ₀` uniformly
on `[0,1]`,

  `∫_{γ₀} g ds ≤ liminf_j ∫_{γ_j} g ds`.

Proof route: for a partition `0 = t₀ < ⋯ < t_m = 1`, each piece satisfies
`∫_{γ_j|[t_k,t_{k+1}]} g ds ≥ (inf of g on a tube around γ₀([t_k,t_{k+1}])) ·
dist (γ_j t_k) (γ_j t_{k+1})` for `j` large (uniform convergence puts `γ_j`-pieces in the
tube; the arc length of a Lipschitz piece dominates the endpoint distance via the
fundamental theorem of calculus for Lipschitz curves). Sum, let `j → ∞`, then refine the
partition: for a Lipschitz curve and continuous weight the inscribed weighted sums converge
to `∫_{γ₀} g ds` (uniform continuity of `g` on a compact tube plus convergence of inscribed
polygon lengths to the total variation `∫‖γ₀'‖`). -/
theorem arcLengthLineIntegral_le_liminf_of_tendstoUniformlyOn {g : ℂ → ℝ}
    (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) {γ : ℕ → ℝ → ℂ} {γ₀ : ℝ → ℂ} {L : ℝ≥0}
    (hlip : ∀ j, LipschitzWith L (γ j)) (hlip₀ : LipschitzWith L γ₀)
    (hconv : TendstoUniformlyOn γ γ₀ atTop (Set.Icc 0 1)) :
    arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀
      ≤ liminf (fun j => arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) (γ j))
          atTop := by
  classical
  have hnsmul : ∀ (r : ℝ) (v : ℂ), ‖r • v‖ = |r| * ‖v‖ := by
    intro r v
    rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  -- Unfolding of the arc-length line integral.
  have hΛ : ∀ δ : ℝ → ℂ, arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) δ
      = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (g (δ t)) * (‖deriv δ t‖₊ : ℝ≥0∞) :=
    fun δ => rfl
  -- **FTC lower bound**: endpoint distance is dominated by the integral of the speed.
  have hFTC : ∀ (δ : ℝ → ℂ), LipschitzWith L δ → ∀ a b : ℝ, a ≤ b →
      ENNReal.ofReal (dist (δ a) (δ b)) ≤ ∫⁻ t in Set.Icc a b, (‖deriv δ t‖₊ : ℝ≥0∞) := by
    intro δ hδ a b hab
    by_cases hw : δ b - δ a = 0
    · have h0 : dist (δ a) (δ b) = 0 := by
        rw [dist_comm, dist_eq_norm, hw]
        exact norm_zero
      rw [h0, ENNReal.ofReal_zero]
      exact zero_le
    · set w : ℂ := δ b - δ a with hwdef
      have hwnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      set cu : ℂ := (starRingEnd ℂ) ((‖w‖⁻¹ : ℝ) • w) with hcu
      have hcunorm : ‖cu‖ = 1 := by
        rw [hcu, Complex.norm_conj, Complex.real_smul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
          inv_mul_cancel₀ hwnorm]
      -- the scalar test function
      set p : ℝ → ℝ := fun t => (cu * δ t).re with hp
      have hp_eq : ∀ t, p t = (cu * δ t).re := fun t => by rw [hp]
      have hplip : LipschitzWith L p := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        rw [Real.dist_eq, hp_eq, hp_eq]
        have h1 : (cu * δ x).re - (cu * δ y).re = (cu * (δ x - δ y)).re := by
          rw [mul_sub, Complex.sub_re]
        rw [h1]
        calc |(cu * (δ x - δ y)).re| ≤ ‖cu * (δ x - δ y)‖ := Complex.abs_re_le_norm _
          _ = ‖δ x - δ y‖ := by rw [norm_mul, hcunorm, one_mul]
          _ = dist (δ x) (δ y) := (dist_eq_norm _ _).symm
          _ ≤ L * dist x y := hδ.dist_le_mul x y
      have hpac : AbsolutelyContinuousOnInterval p a b :=
        (hplip.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval
      have hftc : ∫ x in a..b, deriv p x = p b - p a := hpac.integral_deriv_eq_sub
      -- endpoint value: `p b - p a = ‖w‖`
      have hval : p b - p a = ‖w‖ := by
        rw [hp_eq, hp_eq]
        have h1 : (cu * δ b).re - (cu * δ a).re = (cu * w).re := by
          rw [hwdef, mul_sub, Complex.sub_re]
        rw [h1, hcu]
        have h2 : (starRingEnd ℂ) ((‖w‖⁻¹ : ℝ) • w) * w
            = ((‖w‖⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) w * w) := by
          rw [Complex.real_smul, map_mul, Complex.conj_ofReal, mul_assoc]
        rw [h2]
        have h3 : (starRingEnd ℂ) w * w = (Complex.normSq w : ℂ) := by
          rw [mul_comm, Complex.mul_conj]
        rw [h3, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq, sq,
          ← mul_assoc, inv_mul_cancel₀ hwnorm, one_mul]
      -- a.e. domination of `deriv p` by `‖deriv δ‖`
      have hae : ∀ᵐ t : ℝ, deriv p t ≤ ‖deriv δ t‖ := by
        filter_upwards [hδ.ae_differentiableAt (μ := volume)] with t hdiff
        have hd : HasDerivAt δ (deriv δ t) t := hdiff.hasDerivAt
        have hd1 : HasDerivAt (fun s => cu * δ s) (cu * deriv δ t) t := hd.const_mul cu
        have hd2 : HasDerivAt p ((cu * deriv δ t).re) t := by
          have := (Complex.reCLM.hasFDerivAt (x := cu * δ t)).comp_hasDerivAt t hd1
          simpa [hp] using! this
        rw [hd2.deriv]
        calc (cu * deriv δ t).re ≤ ‖cu * deriv δ t‖ := Complex.re_le_norm _
          _ = ‖deriv δ t‖ := by rw [norm_mul, hcunorm, one_mul]
      -- integrability of the dominating function
      have hmeas : Measurable fun t : ℝ => ‖deriv δ t‖ := (measurable_deriv δ).norm
      have hbdd : ∀ t : ℝ, ‖deriv δ t‖ ≤ (L : ℝ) := fun t => norm_deriv_le_of_lipschitz hδ
      have hint : IntervalIntegrable (fun t : ℝ => ‖deriv δ t‖) volume a b := by
        rw [intervalIntegrable_iff]
        refine Measure.integrableOn_of_bounded (M := (L : ℝ)) ?_ hmeas.aestronglyMeasurable ?_
        · rw [Set.uIoc, Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top
        · exact Eventually.of_forall fun t => by
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            exact hbdd t
      have hcmp : ‖w‖ ≤ ∫ t in a..b, ‖deriv δ t‖ := by
        rw [← hval, ← hftc]
        exact intervalIntegral.integral_mono_ae hab hpac.intervalIntegrable_deriv hint hae
      have hIoc : ENNReal.ofReal (∫ t in a..b, ‖deriv δ t‖)
          = ∫⁻ t in Set.Ioc a b, (‖deriv δ t‖₊ : ℝ≥0∞) := by
        rw [intervalIntegral.integral_of_le hab,
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint)
            (Eventually.of_forall fun t => norm_nonneg _)]
        refine lintegral_congr fun t => ?_
        rw [ofReal_norm, enorm_eq_nnnorm]
      calc ENNReal.ofReal (dist (δ a) (δ b))
          ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv δ t‖) := by
            apply ENNReal.ofReal_le_ofReal
            rw [dist_comm, dist_eq_norm]
            exact hcmp
        _ = ∫⁻ t in Set.Ioc a b, (‖deriv δ t‖₊ : ℝ≥0∞) := hIoc
        _ ≤ ∫⁻ t in Set.Icc a b, (‖deriv δ t‖₊ : ℝ≥0∞) :=
            lintegral_mono_set Set.Ioc_subset_Icc_self
  -- **Weighted piece lower bound.**
  have hPIECE : ∀ (δ : ℝ → ℂ), LipschitzWith L δ → ∀ a b : ℝ, a ≤ b → ∀ cmin : ℝ, 0 ≤ cmin →
      (∀ t ∈ Set.Icc a b, cmin ≤ g (δ t)) →
      ENNReal.ofReal cmin * ENNReal.ofReal (dist (δ a) (δ b))
        ≤ ∫⁻ t in Set.Icc a b, ENNReal.ofReal (g (δ t)) * (‖deriv δ t‖₊ : ℝ≥0∞) := by
    intro δ hδ a b hab cmin _ hle
    calc ENNReal.ofReal cmin * ENNReal.ofReal (dist (δ a) (δ b))
        ≤ ENNReal.ofReal cmin * ∫⁻ t in Set.Icc a b, (‖deriv δ t‖₊ : ℝ≥0∞) :=
          mul_le_mul' le_rfl (hFTC δ hδ a b hab)
      _ = ∫⁻ t in Set.Icc a b, ENNReal.ofReal cmin * (‖deriv δ t‖₊ : ℝ≥0∞) :=
          (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Set.Icc a b, ENNReal.ofReal (g (δ t)) * (‖deriv δ t‖₊ : ℝ≥0∞) := by
          refine lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hle t ht)) le_rfl
  -- **Splitting of the lintegral along a monotone partition.**
  have hSPLIT : ∀ (F : ℝ → ℝ≥0∞) (aa : ℕ → ℝ), Monotone aa → ∀ M : ℕ,
      (∫⁻ t in Set.Ioc (aa 0) (aa M), F t)
        = ∑ k ∈ Finset.range M, ∫⁻ t in Set.Ioc (aa k) (aa (k + 1)), F t := by
    intro F aa haa M
    induction M with
    | zero => simp
    | succ M ih =>
      have hdisj : Disjoint (Set.Ioc (aa 0) (aa M)) (Set.Ioc (aa M) (aa (M + 1))) :=
        Set.Ioc_disjoint_Ioc.mpr (le_trans (min_le_left _ _) (le_max_right _ _))
      rw [Finset.sum_range_succ, ← ih,
        ← MeasureTheory.lintegral_union measurableSet_Ioc hdisj,
        Set.Ioc_union_Ioc_eq_Ioc (haa (Nat.zero_le M)) (haa (Nat.le_succ M))]
  -- **Uniform speed bound for the limit curve.**
  have hDle : ∀ t : ℝ, ((‖deriv γ₀ t‖₊ : ℝ≥0) : ℝ≥0∞) ≤ (L : ℝ≥0∞) := by
    intro t
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
    exact norm_deriv_le_of_lipschitz hlip₀
  -- **The trace and its compact thickening.**
  set T : Set ℂ := γ₀ '' Set.Icc 0 1 with hTdef
  have hTcpt : IsCompact T := isCompact_Icc.image hlip₀.continuous
  set K : Set ℂ := Metric.cthickening ((L : ℝ) + 1) T with hKdef
  have hKcpt : IsCompact K := hTcpt.cthickening
  have hTK : T ⊆ K := by rw [hKdef]; exact Metric.self_subset_cthickening T
  -- **Finiteness of the limit weighted length.**
  obtain ⟨G, hG⟩ := hTcpt.exists_bound_of_continuousOn hg.continuousOn
  have hΛfin : arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀ ≠ ⊤ := by
    have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (g (γ₀ t)) * (‖deriv γ₀ t‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal G * (L : ℝ≥0∞) := by
      intro t ht
      refine mul_le_mul' ?_ (hDle t)
      apply ENNReal.ofReal_le_ofReal
      calc g (γ₀ t) ≤ |g (γ₀ t)| := le_abs_self _
        _ = ‖g (γ₀ t)‖ := (Real.norm_eq_abs _).symm
        _ ≤ G := hG (γ₀ t) ⟨t, ht, rfl⟩
    have hup : arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀
        ≤ ENNReal.ofReal G * (L : ℝ≥0∞) * volume (Set.Icc (0 : ℝ) 1) := by
      rw [hΛ γ₀]
      calc (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (g (γ₀ t)) * (‖deriv γ₀ t‖₊ : ℝ≥0∞))
          ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal G * (L : ℝ≥0∞) :=
            setLIntegral_mono_ae aemeasurable_const (Eventually.of_forall hb)
        _ = ENNReal.ofReal G * (L : ℝ≥0∞) * volume (Set.Icc (0 : ℝ) 1) :=
            setLIntegral_const _ _
    refine ne_top_of_le_ne_top ?_ hup
    rw [Real.volume_Icc]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) ENNReal.ofReal_ne_top
  -- **The difference-quotient approximants.**
  set q : ℕ → ℝ → ℝ≥0∞ := fun M s =>
    ∑ k ∈ Finset.range M, (Set.Ico ((k : ℝ) / M) (((k : ℝ) + 1) / M)).indicator
      (fun s' => ENNReal.ofReal (g (γ₀ s')) *
        ENNReal.ofReal ((M : ℝ) * dist (γ₀ ((k : ℝ) / M)) (γ₀ (((k : ℝ) + 1) / M)))) s
    with hqdef
  have hq_eq : ∀ M s, q M s
      = ∑ k ∈ Finset.range M, (Set.Ico ((k : ℝ) / M) (((k : ℝ) + 1) / M)).indicator
          (fun s' => ENNReal.ofReal (g (γ₀ s')) *
            ENNReal.ofReal ((M : ℝ) * dist (γ₀ ((k : ℝ) / M)) (γ₀ (((k : ℝ) + 1) / M)))) s :=
    fun M s => by rw [hqdef]
  have hqmeas : ∀ M, Measurable (q M) := by
    intro M
    have hfun : q M = fun s =>
        ∑ k ∈ Finset.range M, (Set.Ico ((k : ℝ) / M) (((k : ℝ) + 1) / M)).indicator
          (fun s' => ENNReal.ofReal (g (γ₀ s')) *
            ENNReal.ofReal ((M : ℝ) * dist (γ₀ ((k : ℝ) / M)) (γ₀ (((k : ℝ) + 1) / M)))) s :=
      funext fun s => hq_eq M s
    rw [hfun]
    apply Finset.measurable_sum
    intro k _
    exact (((hg.comp hlip₀.continuous).measurable.ennreal_ofReal).mul_const _).indicator
      measurableSet_Ico
  -- value of `q M` at a point of `[0,1)`
  have hqval : ∀ M : ℕ, 1 ≤ M → ∀ s : ℝ, 0 ≤ s → s < 1 →
      q M s = ENNReal.ofReal (g (γ₀ s)) *
        ENNReal.ofReal ((M : ℝ) *
          dist (γ₀ ((⌊s * M⌋₊ : ℝ) / M)) (γ₀ (((⌊s * M⌋₊ : ℝ) + 1) / M))) := by
    intro M hM1 s hs0 hs1
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hk0M : ⌊s * M⌋₊ < M := by
      rw [Nat.floor_lt (by positivity)]
      calc s * M < 1 * M := mul_lt_mul_of_pos_right hs1 hM0
        _ = M := one_mul _
    have hmem : s ∈ Set.Ico ((⌊s * M⌋₊ : ℝ) / M) (((⌊s * M⌋₊ : ℝ) + 1) / M) := by
      constructor
      · rw [div_le_iff₀ hM0]
        exact Nat.floor_le (by positivity)
      · rw [lt_div_iff₀ hM0]
        exact Nat.lt_floor_add_one _
    rw [hq_eq]
    rw [Finset.sum_eq_single_of_mem ⌊s * M⌋₊ (Finset.mem_range.mpr hk0M)]
    · rw [Set.indicator_of_mem hmem]
    · intro k hk hkne
      apply Set.indicator_of_notMem
      intro hmem'
      rcases lt_or_gt_of_ne hkne with hlt | hgt
      · have h1 : ((k : ℝ) + 1) / M ≤ (⌊s * M⌋₊ : ℝ) / M := by
          gcongr
          exact_mod_cast Nat.succ_le_of_lt hlt
        exact absurd hmem'.2 (not_lt.mpr (h1.trans hmem.1))
      · have h1 : ((⌊s * M⌋₊ : ℝ) + 1) / M ≤ (k : ℝ) / M := by
          gcongr
          exact_mod_cast Nat.succ_le_of_lt hgt
        exact absurd hmem.2 (not_lt.mpr (h1.trans hmem'.1))
  -- **Pointwise convergence of the approximants (straddle lemma + Fatou).**
  have hqconv : ∀ s : ℝ, 0 ≤ s → s < 1 → DifferentiableAt ℝ γ₀ s →
      Tendsto (fun M => q M s) atTop
        (𝓝 (ENNReal.ofReal (g (γ₀ s)) * (‖deriv γ₀ s‖₊ : ℝ≥0∞))) := by
    intro s hs0 hs1 hdiff
    have hstraddle : Tendsto (fun M : ℕ => (M : ℝ) *
        dist (γ₀ ((⌊s * M⌋₊ : ℝ) / M)) (γ₀ (((⌊s * M⌋₊ : ℝ) + 1) / M)))
        atTop (𝓝 ‖deriv γ₀ s‖) := by
      have hd : HasDerivAt γ₀ (deriv γ₀ s) s := hdiff.hasDerivAt
      have hlo := hasDerivAt_iff_isLittleO.mp hd
      rw [Metric.tendsto_atTop]
      intro εr hεr
      have hb := hlo.def (show (0 : ℝ) < εr / 4 by positivity)
      rw [Metric.eventually_nhds_iff] at hb
      obtain ⟨δ', hδ'pos, hδ'⟩ := hb
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ')
      refine ⟨max N 1, fun M hM => ?_⟩
      have hM1 : 1 ≤ M := le_trans (le_max_right N 1) hM
      have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hM1
      have hMδ : (1 : ℝ) / M < δ' := by
        have hNM : (N : ℝ) ≤ M := by exact_mod_cast le_trans (le_max_left N 1) hM
        have h1 : 1 / δ' < (M : ℝ) := lt_of_lt_of_le hN hNM
        rw [div_lt_iff₀ hM0]
        rw [div_lt_iff₀ hδ'pos] at h1
        linarith
      set a' : ℝ := (⌊s * M⌋₊ : ℝ) / M with ha'
      set b' : ℝ := ((⌊s * M⌋₊ : ℝ) + 1) / M with hb'
      have hka : (⌊s * M⌋₊ : ℝ) ≤ s * M := Nat.floor_le (by positivity)
      have hkb : s * M < (⌊s * M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have ha't : a' ≤ s := by
        rw [ha', div_le_iff₀ hM0]
        exact hka
      have htb' : s < b' := by
        rw [hb', lt_div_iff₀ hM0]
        exact hkb
      have hba : b' - a' = 1 / M := by
        rw [ha', hb']
        ring
      have hdista : dist a' s < δ' := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith)]
        have h2 : s < a' + 1 / M := by
          have h3 := htb'
          rw [hb'] at h3
          rw [ha']
          rw [show (⌊s * M⌋₊ : ℝ) / M + 1 / M = ((⌊s * M⌋₊ : ℝ) + 1) / M by ring]
          exact h3
        linarith
      have hdistb : dist b' s < δ' := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        have h2 : b' - s ≤ 1 / M := by linarith [hba, ha't]
        linarith
      have hA := hδ' hdistb
      have hB := hδ' hdista
      set Av : ℂ := γ₀ b' - γ₀ s - (b' - s) • deriv γ₀ s with hAdef
      set Bv : ℂ := γ₀ a' - γ₀ s - (a' - s) • deriv γ₀ s with hBdef
      have hAn : ‖Av‖ ≤ εr / 4 * (b' - s) := by
        rw [hAdef]
        have h4 := hA
        rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b' - s)] at h4
      have hBn : ‖Bv‖ ≤ εr / 4 * (s - a') := by
        rw [hBdef]
        have h4 := hB
        rwa [Real.norm_eq_abs, abs_of_nonpos (by linarith : a' - s ≤ 0), neg_sub] at h4
      set Xv : ℂ := γ₀ b' - γ₀ a' with hXdef
      set Yv : ℂ := (b' - a') • deriv γ₀ s with hYdef
      have hXY : Xv - Yv = Av - Bv := by
        rw [hXdef, hYdef, hAdef, hBdef]
        module
      have hXYn : ‖Xv - Yv‖ ≤ εr / 4 * (1 / M) := by
        rw [hXY]
        calc ‖Av - Bv‖ ≤ ‖Av‖ + ‖Bv‖ := norm_sub_le _ _
          _ ≤ εr / 4 * (b' - s) + εr / 4 * (s - a') := add_le_add hAn hBn
          _ = εr / 4 * (b' - a') := by ring
          _ = εr / 4 * (1 / M) := by rw [hba]
      have hYn : ‖Yv‖ = 1 / M * ‖deriv γ₀ s‖ := by
        rw [hYdef, hnsmul, hba, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / M)]
      have hveq : ‖deriv γ₀ s‖ = M * ‖Yv‖ := by
        rw [hYn]
        field_simp
      have hXdist : dist (γ₀ a') (γ₀ b') = ‖Xv‖ := by
        rw [hXdef, dist_eq_norm']
      rw [Real.dist_eq, hXdist, hveq]
      have habs : |(M : ℝ) * ‖Xv‖ - M * ‖Yv‖| = M * |‖Xv‖ - ‖Yv‖| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hM0.le]
      rw [habs]
      calc (M : ℝ) * |‖Xv‖ - ‖Yv‖| ≤ M * ‖Xv - Yv‖ :=
            mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le Xv Yv) hM0.le
        _ ≤ M * (εr / 4 * (1 / M)) := mul_le_mul_of_nonneg_left hXYn hM0.le
        _ = εr / 4 := by field_simp
        _ < εr := by linarith
    have h1 : Tendsto (fun M : ℕ => ENNReal.ofReal (g (γ₀ s)) *
        ENNReal.ofReal ((M : ℝ) *
          dist (γ₀ ((⌊s * M⌋₊ : ℝ) / M)) (γ₀ (((⌊s * M⌋₊ : ℝ) + 1) / M)))) atTop
        (𝓝 (ENNReal.ofReal (g (γ₀ s)) * ENNReal.ofReal ‖deriv γ₀ s‖)) :=
      ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hstraddle)
        (Or.inr ENNReal.ofReal_ne_top)
    have h2 : ENNReal.ofReal ‖deriv γ₀ s‖ = ((‖deriv γ₀ s‖₊ : ℝ≥0) : ℝ≥0∞) := by
      rw [ofReal_norm, enorm_eq_nnnorm]
    rw [← h2]
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact (hqval M hM s hs0 hs1).symm
  -- **Fatou.**
  have hFatou : arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀
      ≤ liminf (fun M => ∫⁻ s in Set.Icc (0 : ℝ) 1, q M s) atTop := by
    rw [hΛ γ₀]
    have hrad : ∀ᵐ s : ℝ ∂volume, DifferentiableAt ℝ γ₀ s := hlip₀.ae_differentiableAt
    have hne1 : ∀ᵐ s : ℝ ∂volume, s ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      have hset : {a : ℝ | ¬a ≠ 1} = {1} := by
        ext x
        simp
      rw [hset]
      exact Real.volume_singleton
    calc (∫⁻ s in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (g (γ₀ s)) * (‖deriv γ₀ s‖₊ : ℝ≥0∞))
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1, liminf (fun M => q M s) atTop := by
          apply lintegral_mono_ae
          filter_upwards [MeasureTheory.ae_restrict_of_ae hrad,
            MeasureTheory.ae_restrict_of_ae hne1,
            MeasureTheory.ae_restrict_mem measurableSet_Icc] with s h1 h2 h3
          have hs1 : s < 1 := lt_of_le_of_ne h3.2 h2
          rw [(hqconv s h3.1 hs1 h1).liminf_eq]
      _ ≤ liminf (fun M => ∫⁻ s in Set.Icc (0 : ℝ) 1, q M s) atTop :=
          lintegral_liminf_le hqmeas
  -- **Reduce to an `ε`-approximation.**
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < ε := hε
  -- uniform continuity of `g` on the compact thickening
  have hgu : UniformContinuousOn g K := hKcpt.uniformContinuousOn_of_continuous hg.continuousOn
  set ε₁ : ℝ := (ε : ℝ) / (2 * ((L : ℝ) + 1)) with hε₁def
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]
    apply div_pos hεr
    positivity
  obtain ⟨δg, hδgpos, hδg⟩ := Metric.uniformContinuousOn_iff.mp hgu ε₁ hε₁pos
  -- choose the mesh
  have hev1 : ∀ᶠ M in atTop, arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀
      ≤ (∫⁻ s in Set.Icc (0 : ℝ) 1, q M s) + ENNReal.ofReal ((ε : ℝ) / 2) := by
    by_cases hcase : arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀
        ≤ ENNReal.ofReal ((ε : ℝ) / 2)
    · exact Eventually.of_forall fun M => hcase.trans le_add_self
    · rw [not_le] at hcase
      have hne0 : arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀ ≠ 0 :=
        fun h0 => by simp [h0] at hcase
      have hofRne : ENNReal.ofReal ((ε : ℝ) / 2) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
      have hlt := ENNReal.sub_lt_self hΛfin hne0 hofRne
      have := Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hlt hFatou)
      filter_upwards [this] with M hM
      rw [← tsub_le_iff_right]
      exact hM.le
  have hev2 : ∀ᶠ M : ℕ in atTop, 2 * ((L : ℝ) + 1) / M < δg :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * ((L : ℝ) + 1))).eventually_lt_const hδgpos
  obtain ⟨m, hm1, hmesh, hΛA⟩ :
      ∃ M : ℕ, 1 ≤ M ∧ 2 * ((L : ℝ) + 1) / M < δg ∧
        arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀
          ≤ (∫⁻ s in Set.Icc (0 : ℝ) 1, q M s) + ENNReal.ofReal ((ε : ℝ) / 2) := by
    obtain ⟨M, hM⟩ := ((eventually_ge_atTop 1).and (hev2.and hev1)).exists
    exact ⟨M, hM.1, hM.2.1, hM.2.2⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  -- **Tube minima for the chosen mesh.**
  have hball : ∀ k : ℕ, ∃ w ∈ Metric.closedBall (γ₀ ((k : ℝ) / m)) (((L : ℝ) + 1) / m),
      IsMinOn g (Metric.closedBall (γ₀ ((k : ℝ) / m)) (((L : ℝ) + 1) / m)) w :=
    fun k => (isCompact_closedBall _ _).exists_isMinOn
      ⟨γ₀ ((k : ℝ) / m), Metric.mem_closedBall_self (by positivity)⟩ hg.continuousOn
  choose w hwmem hwmin using hball
  -- basic piece geometry
  have hnode : ∀ k : ℕ, k ≤ m → (k : ℝ) / m ∈ Set.Icc (0 : ℝ) 1 := by
    intro k hk
    constructor
    · positivity
    · rw [div_le_one hm0]
      exact_mod_cast hk
  have hpiece_sub : ∀ k, k < m →
      Set.Icc ((k : ℝ) / m) (((k : ℝ) + 1) / m) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro k hk s hs
    have h1 := hnode k hk.le
    have h2 : ((k : ℝ) + 1) / m ≤ 1 := by
      rw [div_le_one hm0]
      exact_mod_cast Nat.succ_le_of_lt hk
    exact ⟨le_trans h1.1 hs.1, le_trans hs.2 h2⟩
  have hnode_dist : ∀ k : ℕ, ∀ s ∈ Set.Icc ((k : ℝ) / m) (((k : ℝ) + 1) / m),
      dist (γ₀ s) (γ₀ ((k : ℝ) / m)) ≤ (L : ℝ) / m := by
    intro k s hs
    calc dist (γ₀ s) (γ₀ ((k : ℝ) / m)) ≤ L * dist s ((k : ℝ) / m) := hlip₀.dist_le_mul _ _
      _ ≤ L * (1 / m) := by
          apply mul_le_mul_of_nonneg_left ?_ L.coe_nonneg
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
          have h2 : s ≤ (k : ℝ) / m + 1 / m := by
            rw [show (k : ℝ) / m + 1 / m = ((k : ℝ) + 1) / m by ring]
            exact hs.2
          linarith
      _ = (L : ℝ) / m := by ring
  -- membership of relevant points in `K`
  have hwK : ∀ k : ℕ, k < m → w k ∈ K := by
    intro k hk
    rw [hKdef]
    refine Metric.mem_cthickening_of_dist_le (w k) (γ₀ ((k : ℝ) / m)) _ _
      ⟨(k : ℝ) / m, hnode k hk.le, rfl⟩ ?_
    have h1 := Metric.mem_closedBall.mp (hwmem k)
    calc dist (w k) (γ₀ ((k : ℝ) / m)) ≤ ((L : ℝ) + 1) / m := h1
      _ ≤ (L : ℝ) + 1 := div_le_self (by positivity) (by exact_mod_cast hm1)
  have hγ₀K : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ₀ s ∈ K := fun s hs => hTK ⟨s, hs, rfl⟩
  -- **Sub-step (i): the Fatou approximant is controlled by the tube-minima sums.**
  have hAmb : (∫⁻ s in Set.Icc (0 : ℝ) 1, q m s)
      ≤ (∑ k ∈ Finset.range m, ENNReal.ofReal (g (w k)) *
          ENNReal.ofReal (dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))))
        + ENNReal.ofReal ((ε : ℝ) / 2) := by
    -- decompose into pieces
    have h1 : (∫⁻ s in Set.Icc (0 : ℝ) 1, q m s)
        = ∑ k ∈ Finset.range m, ∫⁻ s in Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m),
            ENNReal.ofReal (g (γ₀ s)) *
              ENNReal.ofReal ((m : ℝ) * dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) := by
      calc (∫⁻ s in Set.Icc (0 : ℝ) 1, q m s)
          = ∫⁻ s in Set.Icc (0 : ℝ) 1,
              ∑ k ∈ Finset.range m, (Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m)).indicator
                (fun s' => ENNReal.ofReal (g (γ₀ s')) *
                  ENNReal.ofReal ((m : ℝ) *
                    dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)))) s :=
            lintegral_congr fun s => hq_eq m s
        _ = ∑ k ∈ Finset.range m, ∫⁻ s in Set.Icc (0 : ℝ) 1,
              (Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m)).indicator
                (fun s' => ENNReal.ofReal (g (γ₀ s')) *
                  ENNReal.ofReal ((m : ℝ) *
                    dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)))) s :=
            MeasureTheory.lintegral_finsetSum _ fun k _ =>
              (((hg.comp hlip₀.continuous).measurable.ennreal_ofReal).mul_const _).indicator
                measurableSet_Ico
        _ = ∑ k ∈ Finset.range m, ∫⁻ s in Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m),
              ENNReal.ofReal (g (γ₀ s)) *
                ENNReal.ofReal ((m : ℝ) *
                  dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [MeasureTheory.lintegral_indicator measurableSet_Ico,
              MeasureTheory.Measure.restrict_restrict measurableSet_Ico,
              Set.inter_eq_left.mpr
                ((Set.Ico_subset_Icc_self).trans (hpiece_sub k (Finset.mem_range.mp hk)))]
    -- weight bound on each piece
    have hwt : ∀ k, k < m → ∀ s ∈ Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m),
        g (γ₀ s) ≤ g (w k) + ε₁ := by
      intro k hk s hs
      have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 :=
        hpiece_sub k hk (Set.Ico_subset_Icc_self hs)
      have hdw : dist (γ₀ s) (w k) < δg := by
        have h3 := Metric.mem_closedBall.mp (hwmem k)
        calc dist (γ₀ s) (w k)
            ≤ dist (γ₀ s) (γ₀ ((k : ℝ) / m)) + dist (γ₀ ((k : ℝ) / m)) (w k) :=
              dist_triangle _ _ _
          _ ≤ (L : ℝ) / m + ((L : ℝ) + 1) / m :=
              add_le_add (hnode_dist k s (Set.Ico_subset_Icc_self hs))
                (by rw [dist_comm]; exact h3)
          _ ≤ 2 * ((L : ℝ) + 1) / m := by
              rw [show (L : ℝ) / m + ((L : ℝ) + 1) / m = (2 * (L : ℝ) + 1) / m by ring]
              gcongr
              linarith
          _ < δg := hmesh
      have h4 := hδg (γ₀ s) (hγ₀K s hsIcc) (w k) (hwK k hk) hdw
      rw [Real.dist_eq] at h4
      have h5 := (abs_lt.mp h4).2
      linarith
    -- per-piece integral bound
    have h2 : ∀ k, k < m →
        (∫⁻ s in Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m),
          ENNReal.ofReal (g (γ₀ s)) *
            ENNReal.ofReal ((m : ℝ) * dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))))
        ≤ ENNReal.ofReal ((g (w k) + ε₁) *
            dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) := by
      intro k hk
      calc (∫⁻ s in Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m),
            ENNReal.ofReal (g (γ₀ s)) *
              ENNReal.ofReal ((m : ℝ) * dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))))
          ≤ ∫⁻ _ in Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m),
              ENNReal.ofReal (g (w k) + ε₁) *
                ENNReal.ofReal ((m : ℝ) *
                  dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) :=
            setLIntegral_mono_ae aemeasurable_const (Eventually.of_forall fun s hs =>
              mul_le_mul' (ENNReal.ofReal_le_ofReal (hwt k hk s hs)) le_rfl)
        _ = ENNReal.ofReal (g (w k) + ε₁) *
              ENNReal.ofReal ((m : ℝ) *
                dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) *
              volume (Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m)) := setLIntegral_const _ _
        _ = ENNReal.ofReal ((g (w k) + ε₁) *
              dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) := by
            rw [Real.volume_Ico,
              show ((k : ℝ) + 1) / m - (k : ℝ) / m = 1 / m by ring, mul_assoc,
              ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (m : ℝ) *
                dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))),
              show (m : ℝ) * dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)) * (1 / m)
                = dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)) by field_simp,
              ← ENNReal.ofReal_mul (add_nonneg (hg0 _) hε₁pos.le)]
    -- total inscribed length bound
    have hd0sum : ∑ k ∈ Finset.range m,
        dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)) ≤ (L : ℝ) := by
      have hb : ∀ k ∈ Finset.range m,
          dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)) ≤ (L : ℝ) / m := by
        intro k _
        calc dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))
            ≤ L * dist ((k : ℝ) / m) (((k : ℝ) + 1) / m) := hlip₀.dist_le_mul _ _
          _ = (L : ℝ) / m := by
              rw [Real.dist_eq, show (k : ℝ) / m - ((k : ℝ) + 1) / m = -(1 / m) by ring,
                abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / m)]
              ring
      calc ∑ k ∈ Finset.range m, dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))
          ≤ ∑ _k ∈ Finset.range m, (L : ℝ) / m := Finset.sum_le_sum hb
        _ = m * ((L : ℝ) / m) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = (L : ℝ) := by field_simp
    have hε₁L : ε₁ * (L : ℝ) ≤ (ε : ℝ) / 2 := by
      have h2 : (0 : ℝ) < 2 * ((L : ℝ) + 1) := by positivity
      rw [hε₁def, div_mul_eq_mul_div, div_le_iff₀ h2]
      nlinarith [hεr.le, L.coe_nonneg]
    -- assemble
    calc (∫⁻ s in Set.Icc (0 : ℝ) 1, q m s)
        = ∑ k ∈ Finset.range m, ∫⁻ s in Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m),
            ENNReal.ofReal (g (γ₀ s)) *
              ENNReal.ofReal ((m : ℝ) *
                dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) := h1
      _ ≤ ∑ k ∈ Finset.range m, ENNReal.ofReal ((g (w k) + ε₁) *
            dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) :=
          Finset.sum_le_sum fun k hk => h2 k (Finset.mem_range.mp hk)
      _ = ENNReal.ofReal (∑ k ∈ Finset.range m, (g (w k) + ε₁) *
            dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) :=
          (ENNReal.ofReal_sum_of_nonneg fun k _ =>
            mul_nonneg (add_nonneg (hg0 _) hε₁pos.le) dist_nonneg).symm
      _ ≤ ENNReal.ofReal ((∑ k ∈ Finset.range m, g (w k) *
            dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))) + (ε : ℝ) / 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hexp : ∑ k ∈ Finset.range m, (g (w k) + ε₁) *
              dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))
              = (∑ k ∈ Finset.range m, g (w k) *
                  dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)))
                + ε₁ * ∑ k ∈ Finset.range m,
                    dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [hexp]
          have h3 : ε₁ * ∑ k ∈ Finset.range m,
              dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)) ≤ ε₁ * (L : ℝ) :=
            mul_le_mul_of_nonneg_left hd0sum hε₁pos.le
          linarith
      _ ≤ ENNReal.ofReal (∑ k ∈ Finset.range m, g (w k) *
            dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m)))
          + ENNReal.ofReal ((ε : ℝ) / 2) := ENNReal.ofReal_add_le
      _ = (∑ k ∈ Finset.range m, ENNReal.ofReal (g (w k)) *
            ENNReal.ofReal (dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))))
          + ENNReal.ofReal ((ε : ℝ) / 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun k _ =>
            mul_nonneg (hg0 _) dist_nonneg]
          congr 1
          exact Finset.sum_congr rfl fun k _ => ENNReal.ofReal_mul (hg0 _)
  -- **Sub-step (ii): the tube-minima sums lower-bound the approximating lengths.**
  have hii : (∑ k ∈ Finset.range m, ENNReal.ofReal (g (w k)) *
      ENNReal.ofReal (dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))))
      ≤ liminf (fun j => arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) (γ j)) atTop := by
    have hevj : ∀ᶠ j in atTop, (∑ k ∈ Finset.range m, ENNReal.ofReal (g (w k)) *
        ENNReal.ofReal (dist (γ j ((k : ℝ) / m)) (γ j (((k : ℝ) + 1) / m))))
        ≤ arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) (γ j) := by
      filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) (1 / m) (by positivity)]
        with j hj
      -- each piece
      have hpb : ∀ k, k < m → ENNReal.ofReal (g (w k)) *
          ENNReal.ofReal (dist (γ j ((k : ℝ) / m)) (γ j (((k : ℝ) + 1) / m)))
          ≤ ∫⁻ s in Set.Icc ((k : ℝ) / m) (((k : ℝ) + 1) / m),
              ENNReal.ofReal (g (γ j s)) * (‖deriv (γ j) s‖₊ : ℝ≥0∞) := by
        intro k hk
        have hab : (k : ℝ) / m ≤ ((k : ℝ) + 1) / m := by
          gcongr
          linarith [hm0]
        refine hPIECE (γ j) (hlip j) _ _ hab (g (w k)) (hg0 _) ?_
        intro s hs
        refine isMinOn_iff.mp (hwmin k) _ ?_
        rw [Metric.mem_closedBall]
        have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := hpiece_sub k hk hs
        calc dist (γ j s) (γ₀ ((k : ℝ) / m))
            ≤ dist (γ j s) (γ₀ s) + dist (γ₀ s) (γ₀ ((k : ℝ) / m)) := dist_triangle _ _ _
          _ ≤ 1 / m + (L : ℝ) / m :=
              add_le_add (by rw [dist_comm]; exact (hj s hsIcc).le) (hnode_dist k s hs)
          _ = ((L : ℝ) + 1) / m := by ring
      -- sum the pieces
      calc (∑ k ∈ Finset.range m, ENNReal.ofReal (g (w k)) *
            ENNReal.ofReal (dist (γ j ((k : ℝ) / m)) (γ j (((k : ℝ) + 1) / m))))
          ≤ ∑ k ∈ Finset.range m, ∫⁻ s in Set.Icc ((k : ℝ) / m) (((k : ℝ) + 1) / m),
              ENNReal.ofReal (g (γ j s)) * (‖deriv (γ j) s‖₊ : ℝ≥0∞) :=
            Finset.sum_le_sum fun k hk => hpb k (Finset.mem_range.mp hk)
        _ = ∑ k ∈ Finset.range m, ∫⁻ s in Set.Ioc ((k : ℝ) / m) (((k : ℝ) + 1) / m),
              ENNReal.ofReal (g (γ j s)) * (‖deriv (γ j) s‖₊ : ℝ≥0∞) :=
            Finset.sum_congr rfl fun k _ =>
              (MeasureTheory.setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc)).symm
        _ = ∫⁻ s in Set.Ioc ((0 : ℝ) / m) ((m : ℝ) / m),
              ENNReal.ofReal (g (γ j s)) * (‖deriv (γ j) s‖₊ : ℝ≥0∞) := by
            have hmono : Monotone fun k : ℕ => (k : ℝ) / m := by
              intro k l hkl
              change (k : ℝ) / m ≤ (l : ℝ) / m
              gcongr
            have h := (hSPLIT (fun s => ENNReal.ofReal (g (γ j s)) * (‖deriv (γ j) s‖₊ : ℝ≥0∞))
              (fun k => (k : ℝ) / m) hmono m).symm
            push_cast at h
            exact h
        _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal (g (γ j s)) * (‖deriv (γ j) s‖₊ : ℝ≥0∞) := by
            rw [zero_div, div_self (ne_of_gt hm0)]
        _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1,
              ENNReal.ofReal (g (γ j s)) * (‖deriv (γ j) s‖₊ : ℝ≥0∞) :=
            lintegral_mono_set Set.Ioc_subset_Icc_self
        _ = arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) (γ j) := (hΛ (γ j)).symm
    have hlim : Tendsto (fun j => ∑ k ∈ Finset.range m, ENNReal.ofReal (g (w k)) *
        ENNReal.ofReal (dist (γ j ((k : ℝ) / m)) (γ j (((k : ℝ) + 1) / m)))) atTop
        (𝓝 (∑ k ∈ Finset.range m, ENNReal.ofReal (g (w k)) *
          ENNReal.ofReal (dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))))) := by
      apply tendsto_finsetSum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hmem1 : (k : ℝ) / m ∈ Set.Icc (0 : ℝ) 1 := hnode k hk'.le
      have hmem2 : ((k : ℝ) + 1) / m ∈ Set.Icc (0 : ℝ) 1 := by
        have := hnode (k + 1) (Nat.succ_le_of_lt hk')
        rwa [Nat.cast_add, Nat.cast_one] at this
      exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal
        ((hconv.tendsto_at hmem1).dist (hconv.tendsto_at hmem2)))
        (Or.inr ENNReal.ofReal_ne_top)
    rw [← hlim.liminf_eq]
    exact Filter.liminf_le_liminf hevj
  -- **Final assembly.**
  calc arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) γ₀
      ≤ (∫⁻ s in Set.Icc (0 : ℝ) 1, q m s) + ENNReal.ofReal ((ε : ℝ) / 2) := hΛA
    _ ≤ ((∑ k ∈ Finset.range m, ENNReal.ofReal (g (w k)) *
          ENNReal.ofReal (dist (γ₀ ((k : ℝ) / m)) (γ₀ (((k : ℝ) + 1) / m))))
          + ENNReal.ofReal ((ε : ℝ) / 2)) + ENNReal.ofReal ((ε : ℝ) / 2) :=
        add_le_add hAmb le_rfl
    _ ≤ ((liminf (fun j => arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) (γ j)) atTop)
          + ENNReal.ofReal ((ε : ℝ) / 2)) + ENNReal.ofReal ((ε : ℝ) / 2) :=
        add_le_add (add_le_add hii le_rfl) le_rfl
    _ = (liminf (fun j => arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) (γ j)) atTop)
          + (ENNReal.ofReal ((ε : ℝ) / 2) + ENNReal.ofReal ((ε : ℝ) / 2)) := by
        rw [add_assoc]
    _ = (liminf (fun j => arcLengthLineIntegral (fun z => ENNReal.ofReal (g z)) (γ j)) atTop)
          + ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          show (ε : ℝ) / 2 + (ε : ℝ) / 2 = (ε : ℝ) by ring, ENNReal.ofReal_coe_nnreal]

/-- **Chain interpolation with weighted-length control.** A discrete chain
`z 0, …, z n` with steps `≤ h` and total step length `≤ L` interpolates to a single
Lipschitz curve `γ` (arclength-proportional piecewise-linear parametrization on `[0,1]`)
from `z 0` to `z n`, whose trace lies on the union of the chain segments, and whose
weighted length against **any** `Kg`-Lipschitz nonnegative weight `g` is bounded by the
chain cost `∑ g(z_k)·d(z_k, z_{k+1})` plus the Riemann-sum error `Kg · h · L`:

on each segment, `g` deviates from its left-endpoint value by at most `Kg · h`, and the
segment contributes exactly its length to the arc-length measure.

The quantifier over `g` is inside the conclusion: one interpolating curve works for every
Lipschitz weight simultaneously (the curve depends only on the chain). -/
theorem exists_lipschitz_interpolation {n : ℕ} (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ)
    {h : ℝ} (h0 : 0 < h)
    (hstep : ∀ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ h) {L : ℝ}
    (hL : ∑ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ L) :
    ∃ γ : ℝ → ℂ, γ 0 = z 0 ∧ γ 1 = z (Fin.last n) ∧
      LipschitzWith (Real.toNNReal L) γ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ i : Fin n, γ t ∈ segment ℝ (z i.castSucc) (z i.succ)) ∧
      ∀ (g : ℂ → ℝ) (Kg : ℝ≥0), LipschitzWith Kg g → (∀ w, 0 ≤ g w) →
        arcLengthLineIntegral (fun w => ENNReal.ofReal (g w)) γ
          ≤ ENNReal.ofReal
              (∑ i : Fin n, g (z i.castSucc) * dist (z i.castSucc) (z i.succ)
                + Kg * h * L) := by
  classical
  -- ℕ-indexed vertices, constant beyond index `n`.
  set Z : ℕ → ℂ := fun k => z ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩ with hZdef
  have hZcs : ∀ i : Fin n, Z i.1 = z i.castSucc := by
    intro i
    rw [hZdef]
    exact congrArg z (Fin.ext (min_eq_left i.isLt.le))
  have hZsu : ∀ i : Fin n, Z (i.1 + 1) = z i.succ := by
    intro i
    rw [hZdef]
    exact congrArg z (Fin.ext (min_eq_left (Nat.succ_le_of_lt i.isLt)))
  have hZ0 : Z 0 = z 0 := by
    rw [hZdef]
    exact congrArg z (Fin.ext (by
      change min 0 n = ((0 : Fin (n + 1)) : ℕ)
      simp))
  have hZn : Z n = z (Fin.last n) := by
    rw [hZdef]
    exact congrArg z (Fin.ext (min_self n))
  set d : ℕ → ℝ := fun i => dist (Z i) (Z (i + 1)) with hddef
  have hd_eq : ∀ i, d i = dist (Z i) (Z (i + 1)) := fun i => by rw [hddef]
  have hd0 : ∀ i, 0 ≤ d i := fun i => by rw [hd_eq]; exact dist_nonneg
  have hZnorm : ∀ i, ‖Z (i + 1) - Z i‖ = d i := by
    intro i
    rw [← dist_eq_norm, dist_comm, hd_eq]
  have hdh : ∀ i, d i ≤ h := by
    intro i
    by_cases hi : i < n
    · have := hstep ⟨i, hi⟩
      rwa [← hZcs ⟨i, hi⟩, ← hZsu ⟨i, hi⟩, ← hd_eq] at this
    · have hZeq : Z i = Z (i + 1) := by
        rw [hZdef]
        exact congrArg z (Fin.ext
          ((min_eq_right (not_lt.mp hi)).trans
            (min_eq_right ((not_lt.mp hi).trans (Nat.le_succ i))).symm))
      rw [hd_eq, ← hZeq, dist_self]
      exact h0.le
  have hdist_sum : ∑ i : Fin n, dist (z i.castSucc) (z i.succ) = ∑ i ∈ Finset.range n, d i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => d i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd_eq, hZcs i, hZsu i]
  set S : ℝ := ∑ i ∈ Finset.range n, d i with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun i _ => hd0 i
  have hSL : S ≤ L := by rw [← hdist_sum]; exact hL
  have hL0 : (0 : ℝ) ≤ L := hS0.trans hSL
  by_cases hSzero : S = 0
  · -- Degenerate chain: all points coincide; the constant curve works.
    have hdz : ∀ i ∈ Finset.range n, d i = 0 := by
      have hsum0 : ∑ i ∈ Finset.range n, d i = 0 := by rw [← hSdef]; exact hSzero
      exact fun i hi =>
        le_antisymm (hsum0 ▸ Finset.single_le_sum (fun j _ => hd0 j) hi) (hd0 i)
    have hZconst : ∀ k, k ≤ n → Z k = Z 0 := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        have hdm : d m = 0 := hdz m (Finset.mem_range.mpr (Nat.lt_of_succ_le hm))
        rw [hd_eq] at hdm
        rw [← dist_eq_zero.mp hdm]
        exact ih ((Nat.le_succ m).trans hm)
    have hzlast : z (Fin.last n) = z 0 := by
      rw [← hZn, ← hZ0]
      exact hZconst n le_rfl
    refine ⟨fun _ => z 0, rfl, by rw [hzlast], (LipschitzWith.const (z 0)).weaken (zero_le),
      ?_, ?_⟩
    · intro t _
      refine ⟨⟨0, hn⟩, ?_⟩
      have h00 : (⟨0, hn⟩ : Fin n).castSucc = (0 : Fin (n + 1)) := by
        ext; simp
      rw [h00]
      exact left_mem_segment ℝ _ _
    · intro g Kg hglip hg0
      have hzero : arcLengthLineIntegral (fun w => ENNReal.ofReal (g w)) (fun _ => z 0) = 0 := by
        simp [arcLengthLineIntegral]
      rw [hzero]
      exact zero_le
  · -- Main case: positive total length, arclength-proportional parametrization.
    have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSzero)
    -- Cumulative breakpoints.
    set c : ℕ → ℝ := fun k => (∑ i ∈ Finset.range k, d i) / S with hcdef
    have hc_eq : ∀ k, c k = (∑ i ∈ Finset.range k, d i) / S := fun k => by rw [hcdef]
    have hc0 : c 0 = 0 := by rw [hc_eq]; simp
    have hcn : c n = 1 := by rw [hc_eq, ← hSdef]; exact div_self hSzero
    have hcsucc : ∀ k, c (k + 1) = c k + d k / S := by
      intro k
      rw [hc_eq, hc_eq, Finset.sum_range_succ, add_div]
    have hcmono : Monotone c := by
      apply monotone_nat_of_le_succ
      intro k
      rw [hcsucc k]
      have : 0 ≤ d k / S := div_nonneg (hd0 k) hS0
      linarith
    have hc_nonneg : ∀ k, 0 ≤ c k := fun k => hc0 ▸ hcmono (Nat.zero_le k)
    have hc_le_one : ∀ k, k ≤ n → c k ≤ 1 := fun k hk => hcn ▸ hcmono hk
    -- Per-piece clamped parameter.
    set u : ℕ → ℝ → ℝ := fun i t => min (max t (c i)) (c (i + 1)) with hudef
    have hu_eq : ∀ i t, u i t = min (max t (c i)) (c (i + 1)) := fun i t => by rw [hudef]
    have hu_mono : ∀ i, Monotone (u i) := fun i s t hst =>
      min_le_min (max_le_max hst le_rfl) le_rfl
    have hnsmul : ∀ (r : ℝ) (v : ℂ), ‖r • v‖ = |r| * ‖v‖ := by
      intro r v
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    -- The interpolating curve.
    set γ : ℝ → ℂ := fun t =>
      Z 0 + ∑ i ∈ Finset.range n, ((u i t - c i) * (S / d i)) • (Z (i + 1) - Z i) with hγdef
    have hγ_eq : ∀ t, γ t
        = Z 0 + ∑ i ∈ Finset.range n, ((u i t - c i) * (S / d i)) • (Z (i + 1) - Z i) :=
      fun t => by rw [hγdef]
    -- A completed piece contributes exactly its segment vector.
    have hterm_full : ∀ i,
        ((c (i + 1) - c i) * (S / d i)) • (Z (i + 1) - Z i) = Z (i + 1) - Z i := by
      intro i
      by_cases hdi : d i = 0
      · have hZi : Z i = Z (i + 1) := dist_eq_zero.mp (by rw [← hd_eq]; exact hdi)
        rw [← hZi]
        simp
      · have hone : (c (i + 1) - c i) * (S / d i) = 1 := by
          rw [hcsucc i]
          field_simp
          ring
        rw [hone]
        exact one_smul ℝ _
    -- Partial telescoping: the local affine formula on piece `k`.
    have hpiece : ∀ k, k < n → ∀ t, c k ≤ t → t ≤ c (k + 1) →
        γ t = Z k + ((t - c k) * (S / d k)) • (Z (k + 1) - Z k) := by
      intro k hk t hct htc
      rw [hγ_eq]
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hk)]
      have htail : ∑ i ∈ Finset.Ico (k + 1) n,
          ((u i t - c i) * (S / d i)) • (Z (i + 1) - Z i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hik : k + 1 ≤ i := (Finset.mem_Ico.mp hi).1
        have hci : t ≤ c i := htc.trans (hcmono hik)
        have hui : u i t = c i := by
          rw [hu_eq, max_eq_right hci]
          exact min_eq_left (hcmono (Nat.le_succ i))
        rw [hui, sub_self, zero_mul]
        exact zero_smul ℝ _
      rw [htail, add_zero, Finset.sum_range_succ]
      have hhead : ∑ i ∈ Finset.range k,
          ((u i t - c i) * (S / d i)) • (Z (i + 1) - Z i) = Z k - Z 0 := by
        have hcongr : ∀ i ∈ Finset.range k,
            ((u i t - c i) * (S / d i)) • (Z (i + 1) - Z i) = Z (i + 1) - Z i := by
          intro i hi
          have hik : i < k := Finset.mem_range.mp hi
          have h2 : c (i + 1) ≤ t := (hcmono (Nat.succ_le_of_lt hik)).trans hct
          have h1 : c i ≤ t := (hcmono (Nat.le_succ i)).trans h2
          have hui : u i t = c (i + 1) := by
            rw [hu_eq, max_eq_left h1]
            exact min_eq_right h2
          rw [hui]
          exact hterm_full i
        rw [Finset.sum_congr rfl hcongr, Finset.sum_range_sub Z k]
      have huk : u k t = t := by
        rw [hu_eq, max_eq_left hct]
        exact min_eq_left htc
      rw [hhead, huk]
      abel
    -- Endpoints.
    have hγ0 : γ 0 = z 0 := by
      rw [hγ_eq]
      have hzero : ∀ i ∈ Finset.range n,
          ((u i 0 - c i) * (S / d i)) • (Z (i + 1) - Z i) = 0 := by
        intro i _
        have hui : u i 0 = c i := by
          rw [hu_eq, max_eq_right (hc_nonneg i)]
          exact min_eq_left (hcmono (Nat.le_succ i))
        rw [hui, sub_self, zero_mul]
        exact zero_smul ℝ _
      rw [Finset.sum_eq_zero hzero, add_zero, hZ0]
    have hγ1 : γ 1 = z (Fin.last n) := by
      rw [hγ_eq]
      have hfull : ∀ i ∈ Finset.range n,
          ((u i 1 - c i) * (S / d i)) • (Z (i + 1) - Z i) = Z (i + 1) - Z i := by
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        have hui : u i 1 = c (i + 1) := by
          rw [hu_eq, max_eq_left (hc_le_one i hi'.le)]
          exact min_eq_right (hc_le_one (i + 1) (Nat.succ_le_of_lt hi'))
        rw [hui]
        exact hterm_full i
      rw [Finset.sum_congr rfl hfull, Finset.sum_range_sub Z n, ← hZn]
      abel
    -- The telescoping increment bound: total parameter progress is `≤ t - s`.
    have hu_incr : ∀ s t : ℝ, s ≤ t → ∀ m : ℕ,
        ∑ i ∈ Finset.range m, (u i t - u i s) ≤ min t (c m) - min s (c m) := by
      intro s t hst m
      induction m with
      | zero =>
        rw [Finset.sum_range_zero]
        exact sub_nonneg.mpr (min_le_min hst le_rfl)
      | succ m ih =>
        rw [Finset.sum_range_succ]
        have hkey : ∀ x : ℝ, min x (c m) + u m x = min x (c (m + 1)) + c m := by
          intro x
          rcases le_total x (c m) with hx | hx
          · rw [min_eq_left hx, min_eq_left (hx.trans (hcmono (Nat.le_succ m)))]
            have hux : u m x = c m := by
              rw [hu_eq, max_eq_right hx]
              exact min_eq_left (hcmono (Nat.le_succ m))
            rw [hux]
          · rw [min_eq_right hx]
            have hux : u m x = min x (c (m + 1)) := by
              rw [hu_eq, max_eq_left hx]
            rw [hux]
            ring
        have h1 := hkey t
        have h2 := hkey s
        linarith
    have hu_sum_le : ∀ s t : ℝ, s ≤ t →
        ∑ i ∈ Finset.range n, (u i t - u i s) ≤ t - s := by
      intro s t hst
      refine (hu_incr s t hst n).trans ?_
      rcases le_total t (c n) with hcase | hcase
      · rw [min_eq_left hcase, min_eq_left (hst.trans hcase)]
      · rw [min_eq_right hcase]
        rcases le_total s (c n) with hcase' | hcase'
        · rw [min_eq_left hcase']
          linarith
        · rw [min_eq_right hcase']
          linarith
    -- Global Lipschitz bound with constant `S ≤ L`.
    have hγdist : ∀ s t : ℝ, s ≤ t → dist (γ t) (γ s) ≤ S * (t - s) := by
      intro s t hst
      rw [dist_eq_norm, hγ_eq t, hγ_eq s, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      have hterms : ∀ i ∈ Finset.range n,
          ((u i t - c i) * (S / d i)) • (Z (i + 1) - Z i)
            - ((u i s - c i) * (S / d i)) • (Z (i + 1) - Z i)
          = ((u i t - u i s) * (S / d i)) • (Z (i + 1) - Z i) := by
        intro i _
        have hsc : (u i t - c i) - (u i s - c i) = u i t - u i s := by ring
        rw [← hsc]
        module
      rw [Finset.sum_congr rfl hterms]
      have hbound : ∀ i ∈ Finset.range n,
          ‖((u i t - u i s) * (S / d i)) • (Z (i + 1) - Z i)‖ ≤ S * (u i t - u i s) := by
        intro i _
        rw [hnsmul, hZnorm i]
        have hut : 0 ≤ u i t - u i s := sub_nonneg.mpr (hu_mono i hst)
        rw [abs_of_nonneg (mul_nonneg hut (div_nonneg hS0 (hd0 i)))]
        by_cases hdi : d i = 0
        · rw [hdi, mul_zero]
          exact mul_nonneg hS0 hut
        · rw [mul_assoc, div_mul_cancel₀ _ hdi, mul_comm]
      calc ‖∑ i ∈ Finset.range n, ((u i t - u i s) * (S / d i)) • (Z (i + 1) - Z i)‖
          ≤ ∑ i ∈ Finset.range n, ‖((u i t - u i s) * (S / d i)) • (Z (i + 1) - Z i)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range n, S * (u i t - u i s) := Finset.sum_le_sum hbound
        _ = S * ∑ i ∈ Finset.range n, (u i t - u i s) := by rw [Finset.mul_sum]
        _ ≤ S * (t - s) := mul_le_mul_of_nonneg_left (hu_sum_le s t hst) hS0
    have hγlip : LipschitzWith (Real.toNNReal L) γ := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have hcoe : ((Real.toNNReal L : ℝ≥0) : ℝ) = L := Real.coe_toNNReal L hL0
      rw [hcoe]
      rcases le_total x y with hxy | hxy
      · rw [dist_comm (γ x) (γ y), Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
        calc dist (γ y) (γ x) ≤ S * (y - x) := hγdist x y hxy
          _ ≤ L * (y - x) := mul_le_mul_of_nonneg_right hSL (sub_nonneg.mpr hxy)
          _ = L * -(x - y) := by ring
      · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)]
        calc dist (γ x) (γ y) ≤ S * (x - y) := hγdist y x hxy
          _ ≤ L * (x - y) := mul_le_mul_of_nonneg_right hSL (sub_nonneg.mpr hxy)
    -- Locating the active piece.
    have hfind : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ k, k < n ∧ c k ≤ t ∧ t ≤ c (k + 1) := by
      intro t ht0 ht1
      have hn' : 0 < n := hn
      set P : Finset ℕ := (Finset.range n).filter (fun i => c i ≤ t) with hPdef
      have hP0 : 0 ∈ P := by
        rw [hPdef]
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn', ?_⟩
        rw [hc0]
        exact ht0
      have hPne : P.Nonempty := ⟨0, hP0⟩
      refine ⟨P.max' hPne, ?_, ?_, ?_⟩
      · exact Finset.mem_range.mp (Finset.mem_filter.mp (P.max'_mem hPne)).1
      · exact (Finset.mem_filter.mp (P.max'_mem hPne)).2
      · set k := P.max' hPne with hkdef
        by_cases hk1 : k + 1 < n
        · by_contra hcon
          rw [not_le] at hcon
          have hmem : k + 1 ∈ P := by
            rw [hPdef]
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk1, hcon.le⟩
          have := P.le_max' _ hmem
          omega
        · have hkn : k < n := Finset.mem_range.mp (Finset.mem_filter.mp (P.max'_mem hPne)).1
          have hk1n : k + 1 = n := by omega
          rw [hk1n, hcn]
          exact ht1
    -- Trace on the chain segments.
    have htrace : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∃ i : Fin n, γ t ∈ segment ℝ (z i.castSucc) (z i.succ) := by
      rintro t ⟨ht0, ht1⟩
      obtain ⟨k, hkn, hck, htk⟩ := hfind t ht0 ht1
      refine ⟨⟨k, hkn⟩, ?_⟩
      rw [← hZcs ⟨k, hkn⟩, ← hZsu ⟨k, hkn⟩]
      change γ t ∈ segment ℝ (Z k) (Z (k + 1))
      rw [hpiece k hkn t hck htk]
      by_cases hdk : d k = 0
      · have hZk : Z k = Z (k + 1) := dist_eq_zero.mp (by rw [← hd_eq]; exact hdk)
        have hγt : Z k + ((t - c k) * (S / d k)) • (Z (k + 1) - Z k) = Z k := by
          rw [← hZk]
          module
        rw [hγt]
        exact left_mem_segment ℝ (Z k) (Z (k + 1))
      · have hθ0 : 0 ≤ (t - c k) * (S / d k) :=
          mul_nonneg (sub_nonneg.mpr hck) (div_nonneg hS0 (hd0 k))
        have hθ1 : (t - c k) * (S / d k) ≤ 1 := by
          have h1 : t - c k ≤ d k / S := by
            have := hcsucc k
            linarith
          calc (t - c k) * (S / d k) ≤ (d k / S) * (S / d k) :=
                mul_le_mul_of_nonneg_right h1 (div_nonneg hS0 (hd0 k))
            _ = 1 := by field_simp
        exact ⟨1 - (t - c k) * (S / d k), (t - c k) * (S / d k),
          by linarith, hθ0, by ring, by module⟩
    -- Weighted-length bound against every Lipschitz nonnegative weight.
    have hweight : ∀ (g : ℂ → ℝ) (Kg : ℝ≥0), LipschitzWith Kg g → (∀ w, 0 ≤ g w) →
        arcLengthLineIntegral (fun w => ENNReal.ofReal (g w)) γ
          ≤ ENNReal.ofReal
              (∑ i : Fin n, g (z i.castSucc) * dist (z i.castSucc) (z i.succ)
                + Kg * h * L) := by
      intro g Kg hglip hg0
      have hgd_sum : ∑ i : Fin n, g (z i.castSucc) * dist (z i.castSucc) (z i.succ)
          = ∑ i ∈ Finset.range n, g (Z i) * d i := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => g (Z i) * d i) n]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hd_eq, hZcs i, hZsu i]
      -- Split the lintegral along the breakpoints.
      have hsplit : ∀ m : ℕ,
          (∫⁻ t in Set.Ioc (c 0) (c m),
            ENNReal.ofReal (g (γ t)) * (‖deriv γ t‖₊ : ℝ≥0∞))
          = ∑ k ∈ Finset.range m, ∫⁻ t in Set.Ioc (c k) (c (k + 1)),
              ENNReal.ofReal (g (γ t)) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          have hdisj : Disjoint (Set.Ioc (c 0) (c m)) (Set.Ioc (c m) (c (m + 1))) :=
            Set.Ioc_disjoint_Ioc.mpr (le_trans (min_le_left _ _) (le_max_right _ _))
          rw [Finset.sum_range_succ, ← ih,
            ← MeasureTheory.lintegral_union measurableSet_Ioc hdisj,
            Set.Ioc_union_Ioc_eq_Ioc (hcmono (Nat.zero_le m)) (hcmono (Nat.le_succ m))]
      -- Per-piece bound.
      have hpiece_bound : ∀ k, k < n →
          (∫⁻ t in Set.Ioc (c k) (c (k + 1)),
            ENNReal.ofReal (g (γ t)) * (‖deriv γ t‖₊ : ℝ≥0∞))
          ≤ ENNReal.ofReal ((g (Z k) + Kg * h) * d k) := by
        intro k hkn
        by_cases hdk : d k = 0
        · have hcc : c (k + 1) = c k := by rw [hcsucc k, hdk, zero_div, add_zero]
          rw [hcc, Set.Ioc_self]
          simp
        · have hdk' : 0 < d k := lt_of_le_of_ne (hd0 k) (Ne.symm hdk)
          have hgZh : 0 ≤ g (Z k) + Kg * h :=
            add_nonneg (hg0 _) (mul_nonneg Kg.coe_nonneg h0.le)
          -- Pass to the open piece (a.e. equal).
          rw [MeasureTheory.setLIntegral_congr
            (MeasureTheory.Ioo_ae_eq_Ioc (a := c k) (b := c (k + 1))).symm]
          have hbnd : ∀ t ∈ Set.Ioo (c k) (c (k + 1)),
              ENNReal.ofReal (g (γ t)) * (‖deriv γ t‖₊ : ℝ≥0∞)
                ≤ ENNReal.ofReal (g (Z k) + Kg * h) * ENNReal.ofReal S := by
            intro t ht
            -- Derivative on the open piece: constant speed `S`.
            have hderiv : HasDerivAt γ ((S / d k) • (Z (k + 1) - Z k)) t := by
              have h1 : HasDerivAt (fun τ : ℝ => (τ - c k) * (S / d k)) (S / d k) t := by
                simpa using ((hasDerivAt_id t).sub_const (c k)).mul_const (S / d k)
              have h2 := (h1.smul_const (Z (k + 1) - Z k)).const_add (Z k)
              refine HasDerivAt.congr_of_eventuallyEq h2 ?_
              filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
              exact hpiece k hkn τ hτ.1.le hτ.2.le
            have hnrm : ((‖deriv γ t‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal S := by
              have hnorm : ‖deriv γ t‖ = S := by
                rw [hderiv.deriv, hnsmul,
                  abs_of_nonneg (div_nonneg hS0 (hd0 k)), hZnorm k,
                  div_mul_cancel₀ _ hdk]
              rw [← hnorm, ofReal_norm, enorm_eq_nnnorm]
            -- Weight bound along the segment.
            have hseg : dist (γ t) (Z k) ≤ d k := by
              rw [hpiece k hkn t ht.1.le ht.2.le, dist_eq_norm, add_sub_cancel_left,
                hnsmul, hZnorm k]
              have hθ0 : 0 ≤ (t - c k) * (S / d k) :=
                mul_nonneg (sub_nonneg.mpr ht.1.le) (div_nonneg hS0 (hd0 k))
              have hθ1 : (t - c k) * (S / d k) ≤ 1 := by
                have h1 : t - c k ≤ d k / S := by
                  have := hcsucc k
                  linarith [ht.2.le]
                calc (t - c k) * (S / d k) ≤ (d k / S) * (S / d k) :=
                      mul_le_mul_of_nonneg_right h1 (div_nonneg hS0 (hd0 k))
                  _ = 1 := by field_simp
              rw [abs_of_nonneg hθ0]
              calc (t - c k) * (S / d k) * d k ≤ 1 * d k :=
                    mul_le_mul_of_nonneg_right hθ1 (hd0 k)
                _ = d k := one_mul _
            have hgb : g (γ t) ≤ g (Z k) + Kg * h := by
              have hd := hglip.dist_le_mul (γ t) (Z k)
              rw [Real.dist_eq] at hd
              have h2 : (Kg : ℝ) * dist (γ t) (Z k) ≤ Kg * h :=
                mul_le_mul_of_nonneg_left (hseg.trans (hdh k)) Kg.coe_nonneg
              have h3 := (abs_le.mp hd).2
              linarith
            rw [hnrm]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hgb) le_rfl
          calc (∫⁻ t in Set.Ioo (c k) (c (k + 1)),
                ENNReal.ofReal (g (γ t)) * (‖deriv γ t‖₊ : ℝ≥0∞))
              ≤ ∫⁻ _ in Set.Ioo (c k) (c (k + 1)),
                  ENNReal.ofReal (g (Z k) + Kg * h) * ENNReal.ofReal S :=
                setLIntegral_mono_ae aemeasurable_const (Filter.Eventually.of_forall hbnd)
            _ = ENNReal.ofReal (g (Z k) + Kg * h) * ENNReal.ofReal S
                  * volume (Set.Ioo (c k) (c (k + 1))) := setLIntegral_const _ _
            _ = ENNReal.ofReal ((g (Z k) + Kg * h) * d k) := by
                rw [Real.volume_Ioo, hcsucc k,
                  show c k + d k / S - c k = d k / S by ring, mul_assoc,
                  ← ENNReal.ofReal_mul hS0, mul_div_cancel₀ _ hSzero,
                  ← ENNReal.ofReal_mul hgZh]
      -- Assemble.
      have hLHS : arcLengthLineIntegral (fun w => ENNReal.ofReal (g w)) γ
          = ∫⁻ t in Set.Ioc (c 0) (c n),
              ENNReal.ofReal (g (γ t)) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
        rw [hc0, hcn, arcLengthLineIntegral,
          MeasureTheory.setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc (a := (0:ℝ)) (b := 1))]
      rw [hLHS, hsplit n]
      calc (∑ k ∈ Finset.range n, ∫⁻ t in Set.Ioc (c k) (c (k + 1)),
              ENNReal.ofReal (g (γ t)) * (‖deriv γ t‖₊ : ℝ≥0∞))
          ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal ((g (Z k) + Kg * h) * d k) :=
            Finset.sum_le_sum fun k hk => hpiece_bound k (Finset.mem_range.mp hk)
        _ = ENNReal.ofReal (∑ k ∈ Finset.range n, (g (Z k) + Kg * h) * d k) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ =>
              mul_nonneg (add_nonneg (hg0 _) (mul_nonneg Kg.coe_nonneg h0.le)) (hd0 i)).symm
        _ ≤ ENNReal.ofReal
              (∑ i : Fin n, g (z i.castSucc) * dist (z i.castSucc) (z i.succ)
                + Kg * h * L) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hgd_sum]
            have hexp : ∑ k ∈ Finset.range n, (g (Z k) + Kg * h) * d k
                = ∑ k ∈ Finset.range n, g (Z k) * d k + Kg * h * S := by
              rw [hSdef, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [hexp]
            have hKgh : (0 : ℝ) ≤ Kg * h := mul_nonneg Kg.coe_nonneg h0.le
            have : (Kg : ℝ) * h * S ≤ Kg * h * L := mul_le_mul_of_nonneg_left hSL hKgh
            linarith
    exact ⟨γ, hγ0, hγ1, hγlip, htrace, hweight⟩

end NoWanderingDomains
