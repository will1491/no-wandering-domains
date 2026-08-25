/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.NeumannSeries.PrincipalSolution
import NoWanderingDomains.QC.MRMT.SmoothCase.Stability
import NoWanderingDomains.QC.Calculus.AnalyticClosedness
import NoWanderingDomains.QC.Calculus.Compactness

/-!
# Existence of quasiconformal solutions of the Beltrami equation

The measurable Riemann mapping theorem, existence half: every Beltrami coefficient
`b` (measurable `μ`, `‖μ‖∞ < 1`) admits a quasiconformal solution of `∂̄f = μ·∂f` —
`mrmt_exists : ∃ f, IsQCAnalytic f b`.

The compactly-vanishing case runs through the principal solution of
`QC/MRMT/NeumannSeries/` and three upgrades:

* **Injectivity** (`IsPrincipalSolution.injective`) — the exponential-quotient
  representation: for each `w` an auxiliary fixed-point solve produces `u_w` with
  `f z − f w = (z − w)·exp (u_w z)`, so `f` separates points.
* **Homeomorphism** (`IsPrincipalSolution.isHomeomorph`) — openness and surjectivity
  from injectivity, properness (`f − id → 0` at infinity), and the plane topology
  of sense data.
* **Orientation** (`IsPrincipalSolution.ae_det_pos`) — almost-everywhere positivity
  of the Jacobian, the nondegeneracy upgrade feeding `OrientationPreservingHomeo`.

The general (not compactly vanishing) coefficient reduces to the compact case by
truncation: solve for `μ·1_{|z|≤n}`, normalize the solutions at `0` and `1`, extract
a locally uniform limit through the two-point-normalized geometric compactness
theorem, and pass the Beltrami equation to the limit — on every compact set the
truncated coefficients eventually agree with `μ`, so the weak-gradient pairing
against test functions carries the equation over directly.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Injectivity of the principal solution** (Ahlfors–Bers 1960, Lemma 8 limit
argument). Truncate the coefficient to the support ball of the fixed-point field
(`f` is a principal solution of the truncated coefficient as well), mollify it
(`exists_contDiff_mollification_beltrami`), and solve the smooth cases
(`exists_contDiffOne_principalSolution`). The two-sided Hölder inequality
`‖z₁ − z₂‖ ≤ ‖fₙ z₁ − fₙ z₂‖ + c·‖fₙ z₁ − fₙ z₂‖^α` holds with constants uniform
over the smooth family (`isPrincipalSolution_two_sided_holder`); the smooth
solutions converge uniformly to `f`
(`isPrincipalSolution_tendstoUniformly_of_ae_tendsto`), so the inequality passes
to the limit and forces `f z₁ = f z₂ → z₁ = z₂`. -/
theorem IsPrincipalSolution.injective {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : Function.Injective f := by
  classical
  -- Step 0: unpack the principal-solution bundle and truncate the coefficient
  -- to the support ball of the fixed-point field `h`.
  obtain ⟨p, h, R, hp, hp', hmem, hsupp_h, heq, hrepr⟩ := hf
  have hμt_meas : Measurable fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    Measurable.ite (measurableSet_le measurable_norm measurable_const) b.measurable
      measurable_const
  have hμt_essSup :
      eLpNormEssSup (fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0) volume
        ≤ eLpNormEssSup b.μ volume := by
    rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hzR : ‖z‖ ≤ R
    · simp [hzR]
    · simp [hzR]
  obtain ⟨bt, hbtμ⟩ : ∃ bt : BeltramiCoeff,
      bt.μ = fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    ⟨⟨fun z => if ‖z‖ ≤ R then b.μ z else 0, hμt_meas,
      lt_of_le_of_lt hμt_essSup b.bound⟩, rfl⟩
  have hbt_le : eLpNormEssSup bt.μ volume ≤ eLpNormEssSup b.μ volume := by
    rw [hbtμ]; exact hμt_essSup
  have hbt_supp : ∀ z : ℂ, R < ‖z‖ → bt.μ z = 0 := by
    intro z hz
    rw [hbtμ]
    exact if_neg (not_le.mpr hz)
  -- `f` is also a principal solution of the truncated coefficient.
  have heq' : h =ᵐ[volume] fun z => bt.μ z * beurling h z + bt.μ z := by
    filter_upwards [heq] with z hzeq
    simp only [hbtμ]
    by_cases hzR : ‖z‖ ≤ R
    · rw [if_pos hzR]
      exact hzeq
    · rw [if_neg hzR, hsupp_h z (not_le.mp hzR), zero_mul, zero_add]
  have hf' : IsPrincipalSolution bt f := ⟨p, h, R, hp, hp', hmem, hsupp_h, heq', hrepr⟩
  -- Step 1: mollify the truncated coefficient.
  obtain ⟨bs, hbs_smooth, hbs_cpt, hbs_bnd, hbs_supp, hbs_tend⟩ :=
    exists_contDiff_mollification_beltrami bt hbt_supp
  -- Step 2: smooth-case principal solutions for the mollified coefficients.
  choose fs hfs _hfs1 _hfs2 _hfs3 using fun n =>
    exists_contDiffOne_principalSolution (bs n) (hbs_smooth n) (hbs_cpt n)
  -- Step 3: uniform dilatation bound `k = ‖μ‖∞ < 1` for the whole family.
  have hk0 : 0 ≤ b.normInf := b.normInf_nonneg
  have hk1 : b.normInf < 1 := b.normInf_lt_one
  have hofReal : ENNReal.ofReal b.normInf = eLpNormEssSup b.μ volume :=
    ENNReal.ofReal_toReal (ne_top_of_lt b.bound)
  have hbnd_n : ∀ n, eLpNormEssSup (bs n).μ volume ≤ ENNReal.ofReal b.normInf := by
    intro n
    rw [hofReal]
    exact (hbs_bnd n).trans hbt_le
  have hbnd' : eLpNormEssSup bt.μ volume ≤ ENNReal.ofReal b.normInf := by
    rw [hofReal]; exact hbt_le
  -- The uniform two-sided Hölder inequality over the smooth family.
  obtain ⟨c, α, hc0, hα, hholder⟩ :=
    isPrincipalSolution_two_sided_holder (R := R + 1) hk0 hk1
  have hineq : ∀ (n : ℕ) (z₁ z₂ : ℂ),
      ‖z₁ - z₂‖ ≤ ‖fs n z₁ - fs n z₂‖ + c * ‖fs n z₁ - fs n z₂‖ ^ α := fun n =>
    hholder (bs n) (fs n) (hbs_smooth n) (hbs_cpt n) (hbnd_n n) (hbs_supp n) (hfs n)
  -- Step 4: uniform convergence of the smooth solutions to `f`.
  have hbt_supp' : ∀ z : ℂ, R + 1 < ‖z‖ → bt.μ z = 0 := fun z hz =>
    hbt_supp z (by linarith)
  have hunif : TendstoUniformly fs f atTop :=
    isPrincipalSolution_tendstoUniformly_of_ae_tendsto hk0 hk1 hbnd_n hbnd'
      hbs_supp hbt_supp' hbs_tend hfs hf'
  -- Step 5: pass the Hölder inequality to the limit.
  intro z₁ z₂ hz
  have h1 : Tendsto (fun n => ‖fs n z₁ - fs n z₂‖) atTop (𝓝 0) := by
    have hsub := (hunif.tendsto_at z₁).sub (hunif.tendsto_at z₂)
    rw [hz, sub_self] at hsub
    simpa using hsub.norm
  have h2 : Tendsto (fun n => ‖fs n z₁ - fs n z₂‖ ^ α) atTop (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ α) 0 :=
      Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
    have hcomp := hcont.tendsto.comp h1
    simpa [Real.zero_rpow hα.ne'] using! hcomp
  have h3 : Tendsto (fun n => ‖fs n z₁ - fs n z₂‖ + c * ‖fs n z₁ - fs n z₂‖ ^ α)
      atTop (𝓝 0) := by
    have := h1.add (h2.const_mul c)
    simpa using this
  have hle0 : ‖z₁ - z₂‖ ≤ 0 := ge_of_tendsto' h3 fun n => hineq n z₁ z₂
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle0)

/-- **The principal solution is a homeomorphism of the plane**: injective
(`IsPrincipalSolution.injective`), continuous, proper (`f − id → 0` at infinity),
with open image — hence a homeomorphism onto the connected plane. -/
theorem IsPrincipalSolution.isHomeomorph {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : IsHomeomorph f := by
  classical
  -- Continuity, injectivity, and normalization at infinity.
  have hcont : Continuous f := hf.continuous
  have hinj : Function.Injective f := hf.injective
  have hdecay : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0) :=
    hf.tendsto_sub_id_cocompact
  -- Properness: `‖f z‖ → ∞` as `‖z‖ → ∞`, since the displacement is eventually `< 1`.
  have hnormf : Tendsto (fun z : ℂ => ‖f z‖) (cocompact ℂ) atTop := by
    have h1 : Tendsto (fun z : ℂ => ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
      simpa using hdecay.norm
    have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖f z - z‖ < 1 :=
      h1.eventually_lt_const one_pos
    have hz1 : Tendsto (fun z : ℂ => ‖z‖ - 1) (cocompact ℂ) atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right (cocompact ℂ) (-1 : ℝ) tendsto_norm_cocompact_atTop
    refine tendsto_atTop_mono' (cocompact ℂ) ?_ hz1
    filter_upwards [hev] with z hz
    have h2 : ‖z‖ ≤ ‖f z‖ + ‖f z - z‖ := by
      simpa [sub_sub_cancel] using norm_sub_le (f z) (f z - z)
    linarith
  have hcoc : Tendsto f (cocompact ℂ) (cocompact ℂ) := by
    rw [Filter.hasBasis_cocompact.tendsto_right_iff]
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    filter_upwards [hnormf.eventually (eventually_gt_atTop r)] with z hz
    exact fun hmem => absurd (mem_closedBall_zero_iff.mp (hr hmem)) (not_le.mpr hz)
  have hproper : IsProperMap f := isProperMap_iff_tendsto_cocompact.mpr ⟨hcont, hcoc⟩
  have hclosedmap : IsClosedMap f := hproper.isClosedMap
  -- Reconstruct the Ahlfors–Bers approximation data (as in `injective`).
  obtain ⟨p, h, R, hp, hp', hmem, hsupp_h, heq, hrepr⟩ := hf
  have hμt_meas : Measurable fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    Measurable.ite (measurableSet_le measurable_norm measurable_const) b.measurable
      measurable_const
  have hμt_essSup :
      eLpNormEssSup (fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0) volume
        ≤ eLpNormEssSup b.μ volume := by
    rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hzR : ‖z‖ ≤ R
    · simp [hzR]
    · simp [hzR]
  obtain ⟨bt, hbtμ⟩ : ∃ bt : BeltramiCoeff,
      bt.μ = fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    ⟨⟨fun z => if ‖z‖ ≤ R then b.μ z else 0, hμt_meas,
      lt_of_le_of_lt hμt_essSup b.bound⟩, rfl⟩
  have hbt_le : eLpNormEssSup bt.μ volume ≤ eLpNormEssSup b.μ volume := by
    rw [hbtμ]; exact hμt_essSup
  have hbt_supp : ∀ z : ℂ, R < ‖z‖ → bt.μ z = 0 := by
    intro z hz
    rw [hbtμ]
    exact if_neg (not_le.mpr hz)
  have heq' : h =ᵐ[volume] fun z => bt.μ z * beurling h z + bt.μ z := by
    filter_upwards [heq] with z hzeq
    simp only [hbtμ]
    by_cases hzR : ‖z‖ ≤ R
    · rw [if_pos hzR]
      exact hzeq
    · rw [if_neg hzR, hsupp_h z (not_le.mp hzR), zero_mul, zero_add]
  have hf' : IsPrincipalSolution bt f := ⟨p, h, R, hp, hp', hmem, hsupp_h, heq', hrepr⟩
  obtain ⟨bs, hbs_smooth, hbs_cpt, hbs_bnd, hbs_supp, hbs_tend⟩ :=
    exists_contDiff_mollification_beltrami bt hbt_supp
  choose fs hfs hfs1 hfs2 _hfs3 using fun n =>
    exists_contDiffOne_principalSolution (bs n) (hbs_smooth n) (hbs_cpt n)
  have hk0 : 0 ≤ b.normInf := b.normInf_nonneg
  have hk1 : b.normInf < 1 := b.normInf_lt_one
  have hofReal : ENNReal.ofReal b.normInf = eLpNormEssSup b.μ volume :=
    ENNReal.ofReal_toReal (ne_top_of_lt b.bound)
  have hbnd_n : ∀ n, eLpNormEssSup (bs n).μ volume ≤ ENNReal.ofReal b.normInf := by
    intro n
    rw [hofReal]
    exact (hbs_bnd n).trans hbt_le
  have hbnd' : eLpNormEssSup bt.μ volume ≤ ENNReal.ofReal b.normInf := by
    rw [hofReal]; exact hbt_le
  obtain ⟨c, α, hc0, hα, hholder⟩ :=
    isPrincipalSolution_two_sided_holder (R := R + 1) hk0 hk1
  have hineq : ∀ (n : ℕ) (z₁ z₂ : ℂ),
      ‖z₁ - z₂‖ ≤ ‖fs n z₁ - fs n z₂‖ + c * ‖fs n z₁ - fs n z₂‖ ^ α := fun n =>
    hholder (bs n) (fs n) (hbs_smooth n) (hbs_cpt n) (hbnd_n n) (hbs_supp n) (hfs n)
  have hbt_supp' : ∀ z : ℂ, R + 1 < ‖z‖ → bt.μ z = 0 := fun z hz =>
    hbt_supp z (by linarith)
  have hunif : TendstoUniformly fs f atTop :=
    isPrincipalSolution_tendstoUniformly_of_ae_tendsto hk0 hk1 hbnd_n hbnd'
      hbs_supp hbt_supp' hbs_tend hfs hf'
  -- Surjectivity: solve `fs n zₙ = w` (the smooth solutions are homeomorphisms),
  -- the two-sided Hölder inequality bounds `(zₙ)`, and a convergent subsequence
  -- produces a preimage of `w` under `f`.
  have hsurj : Function.Surjective f := by
    intro w
    have hsurj_n : ∀ n, Function.Surjective (fs n) := fun n =>
      (isHomeomorph_of_contDiffOne_principalSolution (hfs n) (hfs1 n) (hfs2 n)).bijective.2
    choose zs hzs using fun n => hsurj_n n w
    -- The displacement bound: `‖zₙ‖ ≤ ‖w − fs n 0‖ + c·‖w − fs n 0‖^α`.
    have hzs_bound : ∀ n, ‖zs n‖ ≤ ‖w - fs n 0‖ + c * ‖w - fs n 0‖ ^ α := by
      intro n
      have h := hineq n (zs n) 0
      rw [hzs n] at h
      simpa using h
    -- `fs n 0 → f 0`, so `‖w − fs n 0‖` is bounded by some `M`.
    have h0 : Tendsto (fun n => ‖w - fs n 0‖) atTop (𝓝 ‖w - f 0‖) :=
      (tendsto_const_nhds.sub (hunif.tendsto_at 0)).norm
    obtain ⟨M, hM⟩ := h0.bddAbove_range
    have hM' : ∀ n, ‖w - fs n 0‖ ≤ M := fun n => hM (Set.mem_range_self n)
    -- Hence `(zₙ)` lives in a fixed closed ball.
    have hzs_mem : ∀ n, zs n ∈ Metric.closedBall (0 : ℂ) (M + c * M ^ α) := by
      intro n
      rw [mem_closedBall_zero_iff]
      have h1 : ‖w - fs n 0‖ ^ α ≤ M ^ α :=
        Real.rpow_le_rpow (norm_nonneg _) (hM' n) hα.le
      have h2 : c * ‖w - fs n 0‖ ^ α ≤ c * M ^ α := mul_le_mul_of_nonneg_left h1 hc0
      linarith [hzs_bound n, hM' n]
    -- Bolzano–Weierstrass and passage to the limit.
    obtain ⟨a, -, φ, hφ, hφtend⟩ :=
      (isCompact_closedBall (0 : ℂ) (M + c * M ^ α)).tendsto_subseq hzs_mem
    refine ⟨a, ?_⟩
    have hlim1 : Tendsto (fun k => f (zs (φ k))) atTop (𝓝 (f a)) :=
      (hcont.tendsto a).comp hφtend
    have hlim2 : Tendsto (fun k => f (zs (φ k))) atTop (𝓝 w) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hφ.tendsto_atTop.eventually
        (Metric.tendstoUniformly_iff.mp hunif ε hε)] with k hk
      have h := hk (zs (φ k))
      rwa [hzs (φ k)] at h
    exact tendsto_nhds_unique hlim1 hlim2
  -- Assembly: a closed continuous bijection is open, hence a homeomorphism.
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  have hopen : IsOpenMap f := by
    intro U hU
    have himg : f '' U = (f '' Uᶜ)ᶜ := by
      rw [← Set.image_compl_eq hbij, compl_compl]
    rw [himg]
    exact isOpen_compl_iff.mpr (hclosedmap _ hU.isClosed_compl)
  exact ⟨hcont, hopen, hbij⟩

/-- **Almost-everywhere positivity of the Jacobian of the principal solution** — the
orientation/nondegeneracy upgrade: `0 < det (Df)` a.e.

The milestone-9 geometric route: the Ahlfors–Bers approximation scheme (truncation,
mollification, smooth-case solutions, uniform convergence — as in `injective` and
`isHomeomorph`) exhibits `f` as the uniform limit of `C¹` principal solutions `fsₙ`
with everywhere-positive Jacobian. Each `fsₙ` is analytically quasiconformal (the
weak Beltrami equation upgrades to the pointwise Wirtinger one by a.e. uniqueness of
weak derivatives against the classical `C¹` partials), hence geometrically
`K`-quasiconformal with the *uniform* `K = (1 + ‖μ‖∞)/(1 − ‖μ‖∞)`
(`isQCGeometric_of_isQCAnalytic`). The inverses `gsₙ = fsₙ⁻¹` are geometrically
`K`-quasiconformal (`isQCGeometric_inv_of_isQCGeometric`) and converge uniformly to
`f⁻¹` — quantitatively, from the two-sided Hölder inequality read at
`z₁ = gsₙ w`, `z₂ = f⁻¹ w`. The closedness theorem
`isQCGeometric_of_tendstoLocallyUniformly_inverse` then makes the limit `f`
geometrically `K`-quasiconformal, and the reverse length–area data deliver the
almost-everywhere positive Jacobian. -/
theorem IsPrincipalSolution.ae_det_pos {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : ∀ᵐ z : ℂ, 0 < (fderiv ℝ f z).det := by
  classical
  -- The measurable-case principal solution is a homeomorphism (proved above).
  have hhomeo : IsHomeomorph f := hf.isHomeomorph
  -- Step 0: unpack the principal-solution bundle and truncate the coefficient
  -- to the support ball of the fixed-point field `h` (as in `injective`).
  obtain ⟨p, h, R, hp, hp', hmem, hsupp_h, heq, hrepr⟩ := hf
  have hμt_meas : Measurable fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    Measurable.ite (measurableSet_le measurable_norm measurable_const) b.measurable
      measurable_const
  have hμt_essSup :
      eLpNormEssSup (fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0) volume
        ≤ eLpNormEssSup b.μ volume := by
    rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hzR : ‖z‖ ≤ R
    · simp [hzR]
    · simp [hzR]
  obtain ⟨bt, hbtμ⟩ : ∃ bt : BeltramiCoeff,
      bt.μ = fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    ⟨⟨fun z => if ‖z‖ ≤ R then b.μ z else 0, hμt_meas,
      lt_of_le_of_lt hμt_essSup b.bound⟩, rfl⟩
  have hbt_le : eLpNormEssSup bt.μ volume ≤ eLpNormEssSup b.μ volume := by
    rw [hbtμ]; exact hμt_essSup
  have hbt_supp : ∀ z : ℂ, R < ‖z‖ → bt.μ z = 0 := by
    intro z hz
    rw [hbtμ]
    exact if_neg (not_le.mpr hz)
  -- `f` is also a principal solution of the truncated coefficient.
  have heq' : h =ᵐ[volume] fun z => bt.μ z * beurling h z + bt.μ z := by
    filter_upwards [heq] with z hzeq
    simp only [hbtμ]
    by_cases hzR : ‖z‖ ≤ R
    · rw [if_pos hzR]
      exact hzeq
    · rw [if_neg hzR, hsupp_h z (not_le.mp hzR), zero_mul, zero_add]
  have hf' : IsPrincipalSolution bt f := ⟨p, h, R, hp, hp', hmem, hsupp_h, heq', hrepr⟩
  -- Step 1: mollify the truncated coefficient.
  obtain ⟨bs, hbs_smooth, hbs_cpt, hbs_bnd, hbs_supp, hbs_tend⟩ :=
    exists_contDiff_mollification_beltrami bt hbt_supp
  -- Step 2: smooth-case principal solutions for the mollified coefficients.
  choose fs hfs hfs1 hfs2 _hfs3 using fun n =>
    exists_contDiffOne_principalSolution (bs n) (hbs_smooth n) (hbs_cpt n)
  -- Step 3: uniform dilatation bound `k = ‖μ‖∞ < 1` for the whole family.
  have hk0 : 0 ≤ b.normInf := b.normInf_nonneg
  have hk1 : b.normInf < 1 := b.normInf_lt_one
  have hofReal : ENNReal.ofReal b.normInf = eLpNormEssSup b.μ volume :=
    ENNReal.ofReal_toReal (ne_top_of_lt b.bound)
  have hbnd_n : ∀ n, eLpNormEssSup (bs n).μ volume ≤ ENNReal.ofReal b.normInf := by
    intro n
    rw [hofReal]
    exact (hbs_bnd n).trans hbt_le
  have hbnd' : eLpNormEssSup bt.μ volume ≤ ENNReal.ofReal b.normInf := by
    rw [hofReal]; exact hbt_le
  -- The uniform two-sided Hölder inequality over the smooth family.
  obtain ⟨c, α, hc0, hα, hholder⟩ :=
    isPrincipalSolution_two_sided_holder (R := R + 1) hk0 hk1
  have hineq : ∀ (n : ℕ) (z₁ z₂ : ℂ),
      ‖z₁ - z₂‖ ≤ ‖fs n z₁ - fs n z₂‖ + c * ‖fs n z₁ - fs n z₂‖ ^ α := fun n =>
    hholder (bs n) (fs n) (hbs_smooth n) (hbs_cpt n) (hbnd_n n) (hbs_supp n) (hfs n)
  have hbt_supp' : ∀ z : ℂ, R + 1 < ‖z‖ → bt.μ z = 0 := fun z hz =>
    hbt_supp z (by linarith)
  -- Step 4: uniform convergence of the smooth solutions to `f`.
  have hunif : TendstoUniformly fs f atTop :=
    isPrincipalSolution_tendstoUniformly_of_ae_tendsto hk0 hk1 hbnd_n hbnd'
      hbs_supp hbt_supp' hbs_tend hfs hf'
  -- Step 5: each smooth solution is analytically quasiconformal — the C¹ data
  -- supply the orientation-preserving homeomorphism, `W^{1,2}_loc`, and the
  -- pointwise Wirtinger–Beltrami equation (weak Beltrami + a.e. uniqueness of
  -- weak derivatives against the classical partials).
  have hQCa : ∀ n, IsQCAnalytic (fs n) (bs n) := by
    intro n
    have hhomeo_n : IsHomeomorph (fs n) :=
      isHomeomorph_of_contDiffOne_principalSolution (hfs n) (hfs1 n) (hfs2 n)
    have hbelt : ∀ᵐ z, dzbar (fs n) z = (bs n).μ z * dz (fs n) z := by
      obtain ⟨u, v, hgrad, hu2, hv2, _humeas, _hvmeas, hbel⟩ := (hfs n).weak_beltrami
      -- `L²_loc ⟹ L¹_loc` on the plane.
      have hLIofL2 : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
          LocallyIntegrableOn g Set.univ := by
        intro g hg
        refine (MeasureTheory.locallyIntegrable_iff.mpr fun K hK => ?_).locallyIntegrableOn _
        have : IsFiniteMeasure (volume.restrict K) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
        exact ((hg K (Set.subset_univ _) hK).mono_exponent (by norm_num)).integrable le_rfl
      -- The classical partials of the C¹ map are weak partials.
      have hcd : ContDiffOn ℝ 1 (fs n) Set.univ := (hfs1 n).contDiffOn
      have hclassx : HasWeakDirDeriv 1 (fun z => (fderiv ℝ (fs n) z) 1) (fs n) Set.univ :=
        HasWeakDirDeriv.of_contDiffOn isOpen_univ hcd
      have hclassy : HasWeakDirDeriv Complex.I
          (fun z => (fderiv ℝ (fs n) z) Complex.I) (fs n) Set.univ :=
        HasWeakDirDeriv.of_contDiffOn isOpen_univ hcd
      have hfder_cont : Continuous fun z => fderiv ℝ (fs n) z :=
        (hfs1 n).continuous_fderiv one_ne_zero
      have hLIx : LocallyIntegrableOn (fun z => (fderiv ℝ (fs n) z) 1) Set.univ :=
        ((hfder_cont.clm_apply continuous_const).locallyIntegrable).locallyIntegrableOn _
      have hLIy : LocallyIntegrableOn (fun z => (fderiv ℝ (fs n) z) Complex.I) Set.univ :=
        ((hfder_cont.clm_apply continuous_const).locallyIntegrable).locallyIntegrableOn _
      -- A.e. uniqueness of weak derivatives identifies `u`, `v` with the partials.
      have hux : ∀ᵐ z : ℂ, z ∈ Set.univ → u z = (fderiv ℝ (fs n) z) 1 :=
        HasWeakDirDeriv.ae_eq isOpen_univ hgrad.1 hclassx (hLIofL2 hu2) hLIx
      have hvy : ∀ᵐ z : ℂ, z ∈ Set.univ → v z = (fderiv ℝ (fs n) z) Complex.I :=
        HasWeakDirDeriv.ae_eq isOpen_univ hgrad.2 hclassy (hLIofL2 hv2) hLIy
      filter_upwards [hbel, hux, hvy] with z hbz huz hvz
      unfold dzbar dz
      rw [← huz (Set.mem_univ z), ← hvz (Set.mem_univ z)]
      exact hbz
    exact ⟨⟨hhomeo_n, Filter.Eventually.of_forall (hfs2 n)⟩, (hfs n).memW12loc, hbelt⟩
  -- Step 6: uniform geometric dilatation `K = (1 + k)/(1 − k)`, `k = ‖μ‖∞`.
  have h1k : (0 : ℝ) < 1 - b.normInf := by linarith
  set K : ℝ := (1 + b.normInf) / (1 - b.normInf) with hK_def
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hK_def, le_div_iff₀ h1k]
    linarith
  have hKk : (K - 1) / (K + 1) = b.normInf := by
    have hKp : (0 : ℝ) < K + 1 := by linarith
    rw [div_eq_iff hKp.ne', hK_def]
    field_simp
    ring
  have hb_norm : ∀ n, (bs n).normInf ≤ (K - 1) / (K + 1) := by
    intro n
    rw [hKk]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbnd_n n)
    rwa [ENNReal.toReal_ofReal hk0] at h
  have hQCg : ∀ n, IsQCGeometric (fs n) K := fun n =>
    isQCGeometric_of_isQCAnalytic hK1 (hb_norm n) (hQCa n)
  -- Step 7: the inverse family — geometrically `K`-quasiconformal as well.
  set hom : ℕ → (ℂ ≃ₜ ℂ) := fun n => (hQCg n).2.1.isHomeomorph.homeomorph (fs n) with hhom
  set gs : ℕ → ℂ → ℂ := fun n => ⇑(hom n).symm with hgs
  have hli : ∀ n, Function.LeftInverse (gs n) (fs n) := fun n => (hom n).left_inv
  have hri : ∀ n, Function.RightInverse (gs n) (fs n) := fun n => (hom n).right_inv
  have hgK : ∀ n, IsQCGeometric (gs n) K := fun n =>
    isQCGeometric_inv_of_isQCGeometric (hQCg n)
  -- The limit inverse.
  set finv : ℂ → ℂ := ⇑(hhomeo.homeomorph f).symm with hfinv
  have hffinv : ∀ w, f (finv w) = w := by
    intro w
    have happ := (hhomeo.homeomorph f).apply_symm_apply w
    rwa [IsHomeomorph.homeomorph_apply f hhomeo ((hhomeo.homeomorph f).symm w)] at happ
  -- Step 8: uniform convergence of the inverses. The two-sided Hölder
  -- inequality at `z₁ = gsₙ w`, `z₂ = f⁻¹ w` reads
  -- `‖gsₙ w − f⁻¹ w‖ ≤ t + c·t^α` with `t = ‖w − fsₙ (f⁻¹ w)‖ = ‖(f − fsₙ)(f⁻¹ w)‖`,
  -- which the uniform convergence of `fsₙ` sends to `0` uniformly in `w`.
  have hconvg_unif : TendstoUniformly gs finv atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hφcont : ContinuousAt (fun t : ℝ => t + c * t ^ α) 0 :=
      continuousAt_id.add (continuousAt_const.mul
        (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)))
    have hφtend : Tendsto (fun t : ℝ => t + c * t ^ α) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hα.ne'] using hφcont.tendsto
    have hev : ∀ᶠ t : ℝ in 𝓝 0, t + c * t ^ α < ε := hφtend.eventually_lt_const hε
    obtain ⟨η, hη0, hηball⟩ := Metric.eventually_nhds_iff.mp hev
    filter_upwards [Metric.tendstoUniformly_iff.mp hunif η hη0] with n hn w
    have hmain := hineq n (gs n w) (finv w)
    rw [hri n w] at hmain
    have htη : dist (‖w - fs n (finv w)‖) 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      calc ‖w - fs n (finv w)‖ = dist (f (finv w)) (fs n (finv w)) := by
            rw [dist_eq_norm, hffinv w]
        _ < η := hn (finv w)
    calc dist (finv w) (gs n w) = ‖gs n w - finv w‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ ‖w - fs n (finv w)‖ + c * ‖w - fs n (finv w)‖ ^ α := hmain
      _ < ε := hηball htη
  -- Step 9: closedness of geometric quasiconformality under locally uniform
  -- limits with inverse data — the limit `f` is geometrically `K`-quasiconformal.
  have hQCf : IsQCGeometric f K :=
    isQCGeometric_of_tendstoLocallyUniformly_inverse hQCg hgK hli hri
      hunif.tendstoLocallyUniformly hconvg_unif.tendstoLocallyUniformly hhomeo
  -- Step 10: the geometric machinery yields the a.e. positive Jacobian.
  exact (IsQCGeometric.reverseLengthArea_data hQCf).2.1

/-- **The principal solution is analytically quasiconformal**: assembly of the
homeomorphism, orientation, `W^{1,2}_loc`, and pointwise Beltrami data. The pointwise
Wirtinger equation follows from the weak one through almost-everywhere
differentiability (Gehring–Lehto) and the weak-to-pointwise bridge. -/
theorem IsPrincipalSolution.isQCAnalytic {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : IsQCAnalytic f b := by
  classical
  -- The three proved measurable-case upgrades.
  have hhomeo : IsHomeomorph f := hf.isHomeomorph
  have hdet : ∀ᵐ z, 0 < (fderiv ℝ f z).det := hf.ae_det_pos
  have hW12 : MemW12loc f := hf.memW12loc
  have hcont : Continuous f := hf.continuous
  -- The weak Beltrami equation of the fixed-point construction.
  obtain ⟨u, v, hgrad, hu2, hv2, _humeas, _hvmeas, hbel⟩ := hf.weak_beltrami
  -- Local integrability of `f` and of the weak partials.
  have hfloc : LocallyIntegrable f := hcont.locallyIntegrable
  have memLpLoc_to_loc : ∀ {w : ℂ → ℂ}, MemLpLocOn w 2 Set.univ →
      LocallyIntegrableOn w Set.univ := by
    intro w hw
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro K hK
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hw K (Set.subset_univ _) hK).mono_exponent (by norm_num))
  have huloc : LocallyIntegrableOn u Set.univ := memLpLoc_to_loc hu2
  have hvloc : LocallyIntegrableOn v Set.univ := memLpLoc_to_loc hv2
  -- Gehring–Lehto: the `W^{1,2}_loc` homeomorphism is differentiable a.e.
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ f z :=
    GehringLehto.ae_differentiableAt_of_W12loc_homeomorph hhomeo hgrad hu2 hv2
  -- The weak-to-pointwise bridge: classical partials agree a.e. with the weak ones.
  have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = u z :=
    fderiv_ae_eq_weakDirDeriv hgrad.1 huloc hdiff (Or.inl rfl) hfloc
  have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = v z :=
    fderiv_ae_eq_weakDirDeriv hgrad.2 hvloc hdiff (Or.inr rfl) hfloc
  -- Assembly: the pointwise Wirtinger–Beltrami equation a.e.
  refine ⟨⟨hhomeo, hdet⟩, hW12, ?_⟩
  filter_upwards [hbel, haex, haey] with z hbz hx hy
  simp only [dzbar, dz, hx, hy]
  exact hbz

/-- **Existence for compactly vanishing coefficients**: the principal solution is a
quasiconformal solution. -/
theorem mrmt_exists_of_support (b : BeltramiCoeff) {R : ℝ}
    (hsupp : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0) :
    ∃ f : ℂ → ℂ, IsQCAnalytic f b := by
  obtain ⟨f, hf⟩ := exists_isPrincipalSolution b hsupp
  exact ⟨f, hf.isQCAnalytic⟩

/-- **The measurable Riemann mapping theorem, existence half.** Every Beltrami
coefficient admits a quasiconformal solution of the Beltrami equation.

Truncation + normalized-compactness + weak-limit route. Truncate the coefficient to
the balls of radius `n + 1` (`btₙ`, dilatation ≤ `‖μ‖∞`), solve each truncated
problem (`mrmt_exists_of_support`), and renormalize the solutions affinely to
`gsₙ 0 = 0`, `gsₙ 1 = 1` — affine post-composition preserves the analytic package
with the same coefficient (homeomorphism composes, the weak gradient and the
Wirtinger derivatives scale by the same constant, the Jacobian scales by its squared
modulus). The family is uniformly geometrically `K`-quasiconformal with
`K = (1 + ‖μ‖∞)/(1 − ‖μ‖∞)` (`isQCGeometric_of_isQCAnalytic`), so the two-point
normalized compactness theorem
(`exists_subseq_tendstoLocallyUniformly_isQCGeometric`) extracts a locally uniformly
convergent subsequence with geometrically `K`-quasiconformal limit `g`;
`isQCAnalytic_of_isQCGeometric` supplies the orientation-preserving homeomorphism
and `W^{1,2}_loc` structure of `g`. The Beltrami equation for the **original**
coefficient passes to the limit through the weak `W^{1,2}` package
(`exists_subseq_weakGradient_package`): pairing the approximants' equations against
the twisted tests `(1 − μ)·φ`, `i(1 + μ)·φ` — on the support of a fixed test the
truncated coefficients eventually agree with `μ` — and applying the fundamental
lemma of the calculus of variations yields `(1 − μ)u + i(1 + μ)v = 0` a.e. for the
weak gradient `(u, v)` of `g`, which is the weak Wirtinger–Beltrami equation; the
Gehring–Lehto a.e. differentiability and the weak-to-pointwise bridge
(`fderiv_ae_eq_weakDirDeriv`) convert it to the pointwise one. -/
theorem mrmt_exists (b : BeltramiCoeff) :
    ∃ f : ℂ → ℂ, IsQCAnalytic f b := by
  classical
  -- § 0. Constants: `k = ‖μ‖∞ < 1` and the uniform dilatation `K = (1+k)/(1−k)`.
  have hk0 : 0 ≤ b.normInf := b.normInf_nonneg
  have hk1 : b.normInf < 1 := b.normInf_lt_one
  have h1k : (0 : ℝ) < 1 - b.normInf := by linarith
  have hofReal : ENNReal.ofReal b.normInf = eLpNormEssSup b.μ volume :=
    ENNReal.ofReal_toReal (ne_top_of_lt b.bound)
  set K : ℝ := (1 + b.normInf) / (1 - b.normInf) with hK_def
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hK_def, le_div_iff₀ h1k]
    linarith
  have hKk : (K - 1) / (K + 1) = b.normInf := by
    have hKp : (0 : ℝ) < K + 1 := by linarith
    rw [div_eq_iff hKp.ne', hK_def]
    field_simp
    ring
  -- `L²_loc ⟹ L¹_loc` on the plane (shared helper).
  have hLIofL2 : ∀ {w : ℂ → ℂ}, MemLpLocOn w 2 Set.univ →
      LocallyIntegrableOn w Set.univ := by
    intro w hw
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro Kc hKc
    have : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hw Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
  -- § 1. The truncated coefficients `btₙ` (radius `n + 1`).
  have hbt_ex : ∀ n : ℕ, ∃ btn : BeltramiCoeff,
      btn.μ = fun z : ℂ => if ‖z‖ ≤ (n : ℝ) + 1 then b.μ z else 0 := by
    intro n
    refine ⟨⟨fun z => if ‖z‖ ≤ (n : ℝ) + 1 then b.μ z else 0, ?_, ?_⟩, rfl⟩
    · exact Measurable.ite (measurableSet_le measurable_norm measurable_const) b.measurable
        measurable_const
    · refine lt_of_le_of_lt ?_ b.bound
      rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
      refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
      by_cases hzR : ‖z‖ ≤ (n : ℝ) + 1
      · simp [hzR]
      · simp [hzR]
  choose bt hbtμ using hbt_ex
  have hbt_supp : ∀ n : ℕ, ∀ z : ℂ, (n : ℝ) + 1 < ‖z‖ → (bt n).μ z = 0 := by
    intro n z hz
    simp only [hbtμ n]
    exact if_neg (not_le.mpr hz)
  have hbt_norm : ∀ n, (bt n).normInf ≤ (K - 1) / (K + 1) := by
    intro n
    rw [hKk]
    have hle : eLpNormEssSup (bt n).μ volume ≤ ENNReal.ofReal b.normInf := by
      rw [hofReal, hbtμ n, ← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
      refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
      by_cases hzR : ‖z‖ ≤ (n : ℝ) + 1
      · simp [hzR]
      · simp [hzR]
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal hk0] at h2
  -- § 2. Quasiconformal solutions for the truncations, normalized at `0 ↦ 0, 1 ↦ 1`.
  choose f0 hf0 using fun n => mrmt_exists_of_support (bt n) (hbt_supp n)
  have hd_ne : ∀ n, f0 n 1 - f0 n 0 ≠ 0 := fun n =>
    sub_ne_zero.mpr fun h => one_ne_zero ((hf0 n).1.1.injective h)
  set gs : ℕ → ℂ → ℂ := fun n z => (f0 n 1 - f0 n 0)⁻¹ * (f0 n z - f0 n 0) with hgs_def
  have hgs0 : ∀ n, gs n 0 = 0 := by
    intro n
    change (f0 n 1 - f0 n 0)⁻¹ * (f0 n 0 - f0 n 0) = 0
    rw [sub_self, mul_zero]
  have hgs1 : ∀ n, gs n 1 = 1 := by
    intro n
    change (f0 n 1 - f0 n 0)⁻¹ * (f0 n 1 - f0 n 0) = 1
    exact inv_mul_cancel₀ (hd_ne n)
  -- § 3. Affine post-composition preserves the analytic package (same coefficient).
  have haffine : ∀ (F : ℂ → ℂ) (bF : BeltramiCoeff) (a c : ℂ), a ≠ 0 →
      IsQCAnalytic F bF → IsQCAnalytic (fun z => a * (F z - c)) bF := by
    intro F bF a c ha hF
    obtain ⟨⟨hFhomeo, hFdet⟩, hFW12, hFbelt⟩ := hF
    have hFcont : Continuous F := hFhomeo.continuous
    -- a.e. differentiability from the a.e. positive Jacobian (`det (0) = 0`).
    have hFdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ F z := by
      filter_upwards [hFdet] with z hz
      by_contra hnd
      rw [det_fderiv_eq_wirtinger] at hz
      simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hnd] at hz
    -- the affine chain rule and Wirtinger scaling, a.e.
    have hkey : ∀ᵐ z : ℂ, fderiv ℝ (fun w => a * (F w - c)) z = a • fderiv ℝ F z := by
      filter_upwards [hFdiff] with z hz
      have h1 : DifferentiableAt ℝ (fun w => F w - c) z := hz.sub_const c
      have hfun : (fun w => a * (F w - c)) = a • fun w => F w - c := by
        funext w
        simp [smul_eq_mul]
      rw [hfun, fderiv_const_smul h1 a, fderiv_sub_const]
    have hdzs : ∀ᵐ z : ℂ, dz (fun w => a * (F w - c)) z = a * dz F z
        ∧ dzbar (fun w => a * (F w - c)) z = a * dzbar F z := by
      filter_upwards [hkey] with z hk
      constructor
      · simp only [dz, hk, smul_apply, smul_eq_mul]
        ring
      · simp only [dzbar, hk, smul_apply, smul_eq_mul]
        ring
    -- (1) orientation-preserving homeomorphism.
    have hAhomeo : IsHomeomorph (fun z => a * (F z - c)) := by
      have h1 := ((Homeomorph.subRight c).trans (Homeomorph.mulLeft₀ a ha)).isHomeomorph
      have h2 : ⇑((Homeomorph.subRight c).trans (Homeomorph.mulLeft₀ a ha))
          = fun w : ℂ => a * (w - c) := by
        funext w
        simp [Homeomorph.trans_apply]
      rw [h2] at h1
      exact h1.comp hFhomeo
    have hAdet : ∀ᵐ z : ℂ, 0 < (fderiv ℝ (fun w => a * (F w - c)) z).det := by
      filter_upwards [hdzs, hFdet] with z hdw hd
      rw [det_fderiv_eq_wirtinger, hdw.1, hdw.2, norm_mul, norm_mul, mul_pow, mul_pow,
        ← mul_sub]
      rw [det_fderiv_eq_wirtinger] at hd
      exact mul_pos (pow_pos (norm_pos_iff.mpr ha) 2) hd
    -- (2) `W^{1,2}_loc` via the scaled weak gradient.
    have hAcont : Continuous fun z => a * (F z - c) :=
      continuous_const.mul (hFcont.sub continuous_const)
    have hAW12 : MemW12loc (fun z => a * (F z - c)) := by
      obtain ⟨hFloc, gx, gy, hFgrad, hgx, hgy⟩ := hFW12
      -- weak derivative of the constant `c` is `0`.
      have hconst : ∀ v : ℂ, HasWeakDirDeriv v (fun _ : ℂ => (0 : ℂ)) (fun _ : ℂ => c)
          Set.univ := by
        intro v
        have h := HasWeakDirDeriv.of_contDiffOn (v := v) isOpen_univ
          (contDiffOn_const (c := c))
        have hzero : (fun z : ℂ => (fderiv ℝ (fun _ : ℂ => c) z) v) = fun _ => (0 : ℂ) := by
          funext z
          rw [(hasFDerivAt_const c z).fderiv]
          simp
        rwa [hzero] at h
      -- local integrability side conditions.
      have hLIF : LocallyIntegrableOn F Set.univ :=
        hFcont.locallyIntegrable.locallyIntegrableOn _
      have hLIc : LocallyIntegrableOn (fun _ : ℂ => c) Set.univ :=
        continuous_const.locallyIntegrable.locallyIntegrableOn _
      have hLI0 : LocallyIntegrableOn (fun _ : ℂ => (0 : ℂ)) Set.univ :=
        continuous_const.locallyIntegrable.locallyIntegrableOn _
      -- the scaled weak partials of the affine composite.
      have hgoalx : HasWeakDirDeriv 1 (fun z => a * gx z) (fun z => a * (F z - c))
          Set.univ := by
        have hsub := HasWeakDirDeriv.sub hFgrad.1 (hconst 1) hLIF hLIc (hLIofL2 hgx) hLI0
        have hsub' : HasWeakDirDeriv 1 gx (fun z => F z - c) Set.univ := by
          simpa using hsub
        simpa [smul_eq_mul] using HasWeakDirDeriv.const_smul a hsub'
      have hgoaly : HasWeakDirDeriv Complex.I (fun z => a * gy z) (fun z => a * (F z - c))
          Set.univ := by
        have hsub := HasWeakDirDeriv.sub hFgrad.2 (hconst Complex.I) hLIF hLIc
          (hLIofL2 hgy) hLI0
        have hsub' : HasWeakDirDeriv Complex.I gy (fun z => F z - c) Set.univ := by
          simpa using hsub
        simpa [smul_eq_mul] using HasWeakDirDeriv.const_smul a hsub'
      -- the composite is locally `L²` (continuous, bounded on compacts).
      have hAloc : MemLpLocOn (fun z => a * (F z - c)) 2 Set.univ := by
        intro Kc _ hKc
        have : IsFiniteMeasure (volume.restrict Kc) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
        obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hAcont.continuousOn
        refine MemLp.of_bound hAcont.aestronglyMeasurable.restrict C ?_
        filter_upwards [ae_restrict_mem hKc.measurableSet] with z hz
        exact hC z hz
      exact ⟨hAloc, fun z => a * gx z, fun z => a * gy z, ⟨hgoalx, hgoaly⟩,
        fun Kc hs hKc => (hgx Kc hs hKc).const_mul a,
        fun Kc hs hKc => (hgy Kc hs hKc).const_mul a⟩
    -- (3) the Beltrami equation is invariant under the scaling.
    have hAbelt : ∀ᵐ z, dzbar (fun w => a * (F w - c)) z
        = bF.μ z * dz (fun w => a * (F w - c)) z := by
      filter_upwards [hdzs, hFbelt] with z hdw hb
      rw [hdw.1, hdw.2, hb]
      ring
    exact ⟨⟨hAhomeo, hAdet⟩, hAW12, hAbelt⟩
  have hQCgs : ∀ n, IsQCAnalytic (gs n) (bt n) := fun n =>
    haffine (f0 n) (bt n) (f0 n 1 - f0 n 0)⁻¹ (f0 n 0) (inv_ne_zero (hd_ne n)) (hf0 n)
  -- § 4. The normalized family is uniformly geometrically `K`-quasiconformal;
  -- extract a locally uniformly convergent subsequence with geometric limit.
  have hgs_geo : ∀ n, IsQCGeometric (gs n) K := fun n =>
    isQCGeometric_of_isQCAnalytic hK1 (hbt_norm n) (hQCgs n)
  obtain ⟨ψ, g, hψ, hgK, hconv⟩ :=
    exists_subseq_tendstoLocallyUniformly_isQCGeometric hgs_geo
      (zero_ne_one) (zero_ne_one) hgs0 hgs1
  -- § 5. Analytic data for the limit `g` (homeomorphism, orientation, `W^{1,2}_loc`).
  obtain ⟨b', _hb'norm, hb'⟩ := isQCAnalytic_of_isQCGeometric hK1 hgK
  obtain ⟨⟨hghomeo, hgdet⟩, hgW12, _hb'belt⟩ := hb'
  have hgcont : Continuous g := hghomeo.continuous
  -- § 6. The weak `W^{1,2}` limit package along the convergent subsequence.
  obtain ⟨φ, u, v, hφ, hWG, humeas, hvmeas, hu2, hv2, hwx, hwy, _hE⟩ :=
    exists_subseq_weakGradient_package (fun k => hgs_geo (ψ k)) hconv hgcont
  have hwx' : TendstoWeaklyL2Loc (fun k => partialX (gs (ψ (φ k)))) u := hwx
  have hwy' : TendstoWeaklyL2Loc (fun k => partialY (gs (ψ (φ k)))) v := hwy
  -- the a.e. pointwise bound `‖μ‖ ≤ 1`.
  have hbμ_ae : ∀ᵐ z : ℂ, ‖b.μ z‖ ≤ 1 := by
    filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with z hz
    have h1 : ‖b.μ z‖ₑ ≤ 1 := hz.trans b.bound.le
    rwa [← ofReal_norm, ← ENNReal.ofReal_one,
      ENNReal.ofReal_le_ofReal_iff zero_le_one] at h1
  -- products of `L²_loc` fields with compactly supported `L²` tests are integrable.
  have hmul_int : ∀ (X ψt : ℂ → ℂ), AEStronglyMeasurable X volume →
      MemLpLocOn X 2 Set.univ → MemLp ψt 2 volume → HasCompactSupport ψt →
      Integrable (fun z => X z * ψt z) volume := by
    intro X ψt hXmeas hX2 hψ2 hψcs
    have hon : IntegrableOn (fun z => X z * ψt z) (tsupport ψt) volume :=
      (hX2 _ (Set.subset_univ _) hψcs).integrable_mul (hψ2.restrict _)
    have hsupp : Function.support (fun z => X z * ψt z) ⊆ tsupport ψt := by
      intro z hz
      apply subset_tsupport ψt
      simp only [Function.mem_support] at hz ⊢
      intro h0
      apply hz
      rw [h0, mul_zero]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  -- § 6c. The limit Beltrami equation for the weak gradient `(u, v)` with the
  -- ORIGINAL coefficient `b.μ`: pass the equation of the approximants through the
  -- weak `L²_loc` pairing (the truncations agree with `b.μ` on the support of any
  -- fixed test function, eventually).
  set W : ℂ → ℂ := fun z => (1 - b.μ z) * u z + Complex.I * ((1 + b.μ z) * v z)
    with hW_def
  have hWmeas : AEStronglyMeasurable W volume := by
    rw [hW_def]
    exact ((measurable_const.sub b.measurable).aestronglyMeasurable.mul humeas).add
      (aestronglyMeasurable_const.mul
        ((measurable_const.add b.measurable).aestronglyMeasurable.mul hvmeas))
  have hWloc : LocallyIntegrableOn W Set.univ := by
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro Kc hKc
    have : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    have hu1 : Integrable u (volume.restrict Kc) := memLp_one_iff_integrable.mp
      ((hu2 Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
    have hv1 : Integrable v (volume.restrict Kc) := memLp_one_iff_integrable.mp
      ((hv2 Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
    refine Integrable.mono' ((hu1.norm.const_mul 2).add (hv1.norm.const_mul 2))
      hWmeas.restrict ?_
    filter_upwards [ae_restrict_of_ae hbμ_ae] with z hz
    simp only [hW_def]
    calc ‖(1 - b.μ z) * u z + Complex.I * ((1 + b.μ z) * v z)‖
        ≤ ‖(1 - b.μ z) * u z‖ + ‖Complex.I * ((1 + b.μ z) * v z)‖ := norm_add_le _ _
      _ = ‖1 - b.μ z‖ * ‖u z‖ + ‖1 + b.μ z‖ * ‖v z‖ := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul]
      _ ≤ 2 * ‖u z‖ + 2 * ‖v z‖ := by
          have h1 : ‖(1 : ℂ) - b.μ z‖ ≤ 2 :=
            le_trans (norm_sub_le _ _) (by rw [norm_one]; linarith)
          have h2 : ‖(1 : ℂ) + b.μ z‖ ≤ 2 :=
            le_trans (norm_add_le _ _) (by rw [norm_one]; linarith)
          have hu0 := norm_nonneg (u z)
          have hv0 := norm_nonneg (v z)
          nlinarith
  have hWzero : ∀ᵐ z : ℂ, z ∈ Set.univ → W z = 0 := by
    refine isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hWloc ?_
    intro φt hφt hφcs _hts
    -- the twisted compactly supported `L²` tests.
    set ψ₁ : ℂ → ℂ := fun z => (1 - b.μ z) * (φt z : ℂ) with hψ₁_def
    set ψ₂ : ℂ → ℂ := fun z => Complex.I * ((1 + b.μ z) * (φt z : ℂ)) with hψ₂_def
    have hφcoe_cont : Continuous fun z : ℂ => (φt z : ℂ) :=
      Complex.continuous_ofReal.comp hφt.continuous
    have hφcoe_cs : HasCompactSupport fun z : ℂ => (φt z : ℂ) :=
      hφcs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have h2φ_L2 : MemLp (fun z : ℂ => (2 : ℂ) * (φt z : ℂ)) 2 volume :=
      (hφcoe_cont.memLp_of_hasCompactSupport hφcoe_cs).const_mul 2
    have hψ₁_meas : AEStronglyMeasurable ψ₁ volume := by
      rw [hψ₁_def]
      exact (measurable_const.sub b.measurable).aestronglyMeasurable.mul
        hφcoe_cont.aestronglyMeasurable
    have hψ₂_meas : AEStronglyMeasurable ψ₂ volume := by
      rw [hψ₂_def]
      exact aestronglyMeasurable_const.mul
        ((measurable_const.add b.measurable).aestronglyMeasurable.mul
          hφcoe_cont.aestronglyMeasurable)
    have hψ₁_L2 : MemLp ψ₁ 2 volume := by
      refine h2φ_L2.of_le hψ₁_meas ?_
      filter_upwards [hbμ_ae] with z hz
      simp only [hψ₁_def]
      rw [norm_mul, norm_mul]
      have h1 : ‖(1 : ℂ) - b.μ z‖ ≤ ‖(2 : ℂ)‖ := by
        rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
        exact le_trans (norm_sub_le _ _) (by rw [norm_one]; linarith)
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hψ₂_L2 : MemLp ψ₂ 2 volume := by
      refine h2φ_L2.of_le hψ₂_meas ?_
      filter_upwards [hbμ_ae] with z hz
      simp only [hψ₂_def]
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, norm_mul]
      have h1 : ‖(1 : ℂ) + b.μ z‖ ≤ ‖(2 : ℂ)‖ := by
        rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
        exact le_trans (norm_add_le _ _) (by rw [norm_one]; linarith)
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hψ₁_cs : HasCompactSupport ψ₁ := hφcoe_cs.mul_left
    have hψ₂_cs : HasCompactSupport ψ₂ := by
      have h := (hφcoe_cs.mul_left
        (f := fun z : ℂ => (1 : ℂ) + b.μ z)).mul_left (f := fun _ : ℂ => Complex.I)
      simpa [mul_assoc] using! h
    -- convergence of the paired integrals along the subsequence.
    have hlim : Tendsto (fun k => (∫ z, partialX (gs (ψ (φ k))) z * ψ₁ z)
        + ∫ z, partialY (gs (ψ (φ k))) z * ψ₂ z) atTop
        (𝓝 ((∫ z, u z * ψ₁ z) + ∫ z, v z * ψ₂ z)) :=
      (hwx' ψ₁ hψ₁_L2 hψ₁_cs).add (hwy' ψ₂ hψ₂_L2 hψ₂_cs)
    -- the paired integrals vanish eventually: the truncation covers the support.
    have hev0 : ∀ᶠ k in atTop, (∫ z, partialX (gs (ψ (φ k))) z * ψ₁ z)
        + ∫ z, partialY (gs (ψ (φ k))) z * ψ₂ z = 0 := by
      obtain ⟨R, hR⟩ := hφcs.isBounded.subset_closedBall (0 : ℂ)
      obtain ⟨N, hN⟩ := exists_nat_ge R
      rw [eventually_atTop]
      refine ⟨N, fun k hk => ?_⟩
      set m : ℕ := ψ (φ k) with hm_def
      have hmk : (N : ℝ) ≤ (m : ℝ) := by
        have h1 : N ≤ m := le_trans hk (le_trans hφ.le_apply hψ.le_apply)
        exact_mod_cast h1
      -- the geometric per-map Sobolev data for the partials.
      have hXfun : partialX (gs m) = fun w => (fderiv ℝ (gs m) w) 1 :=
        funext fun w => partialX_def _ w
      have hYfun : partialY (gs m) = fun w => (fderiv ℝ (gs m) w) Complex.I :=
        funext fun w => partialY_def _ w
      have hX2 : MemLpLocOn (partialX (gs m)) 2 Set.univ := by
        rw [hXfun]; exact (hgs_geo m).forwardW12Data.2.2.1
      have hY2 : MemLpLocOn (partialY (gs m)) 2 Set.univ := by
        rw [hYfun]; exact (hgs_geo m).forwardW12Data.2.2.2.1
      have hXmeas : AEStronglyMeasurable (partialX (gs m)) volume := by
        rw [hXfun]
        exact (measurable_fderiv_apply_const ℝ (gs m) 1).aestronglyMeasurable
      have hYmeas : AEStronglyMeasurable (partialY (gs m)) volume := by
        rw [hYfun]
        exact (measurable_fderiv_apply_const ℝ (gs m) Complex.I).aestronglyMeasurable
      have hint1 : Integrable (fun z => partialX (gs m) z * ψ₁ z) volume :=
        hmul_int _ _ hXmeas hX2 hψ₁_L2 hψ₁_cs
      have hint2 : Integrable (fun z => partialY (gs m) z * ψ₂ z) volume :=
        hmul_int _ _ hYmeas hY2 hψ₂_L2 hψ₂_cs
      rw [← integral_add hint1 hint2]
      apply integral_eq_zero_of_ae
      filter_upwards [(hQCgs m).2.2] with z hbz
      by_cases hz : z ∈ tsupport φt
      · -- inside the support the truncation agrees with `b.μ`.
        have hzR : ‖z‖ ≤ (m : ℝ) + 1 := by
          have h1 : z ∈ Metric.closedBall (0 : ℂ) R := hR hz
          rw [Metric.mem_closedBall, dist_zero_right] at h1
          calc ‖z‖ ≤ R := h1
            _ ≤ (N : ℝ) := hN
            _ ≤ (m : ℝ) := hmk
            _ ≤ (m : ℝ) + 1 := by linarith
        have hbtz : (bt m).μ z = b.μ z := by
          simp only [hbtμ m]
          exact if_pos hzR
        -- the Wirtinger–Beltrami equation in coordinate-partial form.
        have hXY0 : (1 - b.μ z) * partialX (gs m) z
            + Complex.I * ((1 + b.μ z) * partialY (gs m) z) = 0 := by
          rw [hbtz] at hbz
          rw [partialX_def, partialY_def]
          simp only [dzbar, dz] at hbz
          linear_combination (2 : ℂ) * hbz
        change partialX (gs m) z * ψ₁ z + partialY (gs m) z * ψ₂ z = 0
        simp only [hψ₁_def, hψ₂_def]
        linear_combination ((φt z : ℂ)) * hXY0
      · -- outside the support the test factor vanishes.
        have hz0 : φt z = 0 := image_eq_zero_of_notMem_tsupport hz
        change partialX (gs m) z * ψ₁ z + partialY (gs m) z * ψ₂ z = 0
        simp [hψ₁_def, hψ₂_def, hz0]
    -- the limit of an eventually-zero sequence is zero.
    have h0 : (∫ z, u z * ψ₁ z) + ∫ z, v z * ψ₂ z = 0 :=
      tendsto_nhds_unique hlim (Tendsto.congr' (EventuallyEq.symm hev0) tendsto_const_nhds)
    -- reassemble the test pairing.
    have hint_u : Integrable (fun z => u z * ψ₁ z) volume :=
      hmul_int _ _ humeas hu2 hψ₁_L2 hψ₁_cs
    have hint_v : Integrable (fun z => v z * ψ₂ z) volume :=
      hmul_int _ _ hvmeas hv2 hψ₂_L2 hψ₂_cs
    calc ∫ z, φt z • W z
        = ∫ z, (u z * ψ₁ z + v z * ψ₂ z) := by
          apply integral_congr_ae
          filter_upwards with z
          simp only [hW_def, hψ₁_def, hψ₂_def, real_smul]
          ring
      _ = (∫ z, u z * ψ₁ z) + ∫ z, v z * ψ₂ z := integral_add hint_u hint_v
      _ = 0 := h0
  -- § 6d. From the weak-gradient equation to the pointwise Wirtinger equation of `g`.
  have hgdiff : ∀ᵐ z, DifferentiableAt ℝ g z :=
    GehringLehto.ae_differentiableAt_of_W12loc_homeomorph hghomeo hWG hu2 hv2
  have hgfloc : LocallyIntegrable g := hgcont.locallyIntegrable
  have haex : ∀ᵐ z, (fderiv ℝ g z) (1 : ℂ) = u z :=
    fderiv_ae_eq_weakDirDeriv hWG.1 (hLIofL2 hu2) hgdiff (Or.inl rfl) hgfloc
  have haey : ∀ᵐ z, (fderiv ℝ g z) Complex.I = v z :=
    fderiv_ae_eq_weakDirDeriv hWG.2 (hLIofL2 hv2) hgdiff (Or.inr rfl) hgfloc
  have hgbelt : ∀ᵐ z, dzbar g z = b.μ z * dz g z := by
    filter_upwards [hWzero, haex, haey] with z hw hx hy
    have hw' : (1 - b.μ z) * u z + Complex.I * ((1 + b.μ z) * v z) = 0 := hw trivial
    simp only [dzbar, dz, hx, hy]
    linear_combination (1 / 2 : ℂ) * hw'
  -- § 7. Assembly.
  exact ⟨g, ⟨hghomeo, hgdet⟩, hgW12, hgbelt⟩

end NoWanderingDomains
