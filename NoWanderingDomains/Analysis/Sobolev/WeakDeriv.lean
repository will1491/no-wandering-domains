/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.Wirtinger
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Weak derivatives and Sobolev membership on `ℂ`

This file develops the weak (distributional) first derivatives of a function
`f : ℂ → ℂ` and the local Sobolev membership predicate `W^{k,p}_loc`, working
directly over `ℂ ≃ ℝ²` so that complex-valued maps and Beltrami coefficients
are handled without a real componentwise detour.

`g` is a **weak directional derivative** of `f` in the real direction `v : ℂ`
on `Ω` when the integration-by-parts identity

`∫ (∂ᵥφ) • f = − ∫ φ • g`

holds against every smooth, compactly supported real test function `φ`
supported in `Ω`. The two weak partial derivatives are `HasWeakDirDeriv 1`
(in the `x`-direction) and `HasWeakDirDeriv I` (in the `y`-direction), packaged
as `HasWeakGradient`.

On top of weak gradients we define:

* `MemLpLocOn f p Ω` — `f` is `Lᵖ` on every compact subset of `Ω`;
* `MemWklocP f k p Ω` — local membership in `W^{k,p}`: `f ∈ Lᵖ_loc` together
  with weak partial derivatives of every order up to `k` that are themselves
  in `W^{k-1,p}_loc`;
* `MemW12loc f` — the abbreviation `MemWklocP f 1 2 univ`, the `W^{1,2}_loc(ℂ)`
  class the analytic quasiconformal theory lives in.

The calculus proved here is what the rest of the engine consumes: weak
derivatives are unique almost everywhere (the fundamental lemma of the calculus
of variations); they are linear (`add`/`sub`/`neg`/`const_smul`), restrict to
subsets, and are closed under multiplication by smooth functions (the Leibniz
rule); and a `C¹` function's classical directional derivative is a weak
derivative (`of_contDiffOn`, by integration by parts), which identifies the
strong Wirtinger derivatives `dz`/`dzbar` as weak `∂`/`∂̄` derivatives
(`HasWeakDz`/`HasWeakDzbar`). The absolute-continuity-on-lines characterization
— the genuine converse, that a `W^{1,p}` function is differentiable a.e. — is
developed in `QC/Equivalence.lean`, its only consumer.
-/

open MeasureTheory Complex
open scoped ContDiff ENNReal

namespace NoWanderingDomains

variable {f g g₁ g₂ : ℂ → ℂ} {v : ℂ} {Ω : Set ℂ}

/-- `g` is a **weak directional derivative** of `f` in the real direction `v`
on `Ω`: the integration-by-parts identity `∫ (∂ᵥφ) • f = − ∫ φ • g` holds for
every smooth compactly supported real test function `φ` supported in `Ω`. -/
def HasWeakDirDeriv (v : ℂ) (g f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ z, ((fderiv ℝ φ z) v) • f z = - ∫ z, φ z • g z

/-- A **weak gradient** of `f` on `Ω`: weak partial derivatives `gx` in the
`x`-direction (`v = 1`) and `gy` in the `y`-direction (`v = I`). -/
def HasWeakGradient (gx gy f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  HasWeakDirDeriv 1 gx f Ω ∧ HasWeakDirDeriv Complex.I gy f Ω

/-- `f` is **locally `Lᵖ`** on `Ω`: `Lᵖ` with respect to `volume` restricted to
every compact subset of `Ω`. -/
def MemLpLocOn (f : ℂ → ℂ) (p : ℝ≥0∞) (Ω : Set ℂ) : Prop :=
  ∀ K : Set ℂ, K ⊆ Ω → IsCompact K → MemLp f p (volume.restrict K)

/-- **Local Sobolev membership** `f ∈ W^{k,p}_loc(Ω)`: defined by recursion on
the order `k`. Order `0` is `Lᵖ_loc`; order `k+1` asks for `Lᵖ_loc` membership
together with a weak gradient whose components lie in `W^{k,p}_loc`. -/
def MemWklocP (f : ℂ → ℂ) (k : ℕ) (p : ℝ≥0∞) (Ω : Set ℂ) : Prop :=
  match k with
  | 0 => MemLpLocOn f p Ω
  | k + 1 =>
      MemLpLocOn f p Ω ∧
        ∃ gx gy : ℂ → ℂ, HasWeakGradient gx gy f Ω ∧
          MemWklocP gx k p Ω ∧ MemWklocP gy k p Ω

/-- The class `W^{1,2}_loc(ℂ)` the analytic quasiconformal theory lives in. -/
def MemW12loc (f : ℂ → ℂ) : Prop :=
  MemWklocP f 1 2 Set.univ

/-- `g` is a **weak `∂`-derivative** (weak holomorphic Wirtinger derivative) of
`f` on `Ω`: there are weak partial derivatives `gx` (direction `1`) and `gy`
(direction `I`) of `f` with `g = ½(gx − i gy)` pointwise. -/
def HasWeakDz (g f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∃ gx gy : ℂ → ℂ, HasWeakDirDeriv 1 gx f Ω ∧ HasWeakDirDeriv Complex.I gy f Ω ∧
    ∀ z, g z = (1 / 2 : ℂ) * (gx z - Complex.I * gy z)

/-- `g` is a **weak `∂̄`-derivative** (weak antiholomorphic Wirtinger derivative)
of `f` on `Ω`: there are weak partial derivatives `gx` (direction `1`) and `gy`
(direction `I`) of `f` with `g = ½(gx + i gy)` pointwise. -/
def HasWeakDzbar (g f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∃ gx gy : ℂ → ℂ, HasWeakDirDeriv 1 gx f Ω ∧ HasWeakDirDeriv Complex.I gy f Ω ∧
    ∀ z, g z = (1 / 2 : ℂ) * (gx z + Complex.I * gy z)

/-- **Uniqueness of weak derivatives.** On an open set two weak directional
derivatives of the same function in the same direction agree almost everywhere
(the fundamental lemma of the calculus of variations). -/
theorem HasWeakDirDeriv.ae_eq (hΩ : IsOpen Ω)
    (h₁ : HasWeakDirDeriv v g₁ f Ω) (h₂ : HasWeakDirDeriv v g₂ f Ω)
    (hg₁ : LocallyIntegrableOn g₁ Ω) (hg₂ : LocallyIntegrableOn g₂ Ω) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω → g₁ z = g₂ z := by
  -- (smooth, compactly supported real `φ` with `tsupport φ ⊆ Ω`) • (locally integrable on `Ω`)
  -- is integrable on all of `ℂ`.
  have integ : ∀ (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∀ {g : ℂ → ℂ}, LocallyIntegrableOn g Ω → Integrable (fun z => φ z • g z) volume := by
    intro φ hφ hcs htsupp g hg
    have hK : IsCompact (tsupport φ) := hcs
    have hgon : IntegrableOn g (tsupport φ) volume :=
      hg.integrableOn_compact_subset htsupp hK
    have hon : IntegrableOn (fun z => φ z • g z) (tsupport φ) volume :=
      hgon.continuousOn_smul hφ.continuous.continuousOn hK
    have hsupp : Function.support (fun z => φ z • g z) ⊆ tsupport φ := by
      intro z hz
      apply subset_tsupport φ
      simp only [Function.mem_support] at hz ⊢
      intro hφz; apply hz; simp [hφz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  -- The fundamental lemma of the calculus of variations applied to `g₁ - g₂`.
  have key : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω → (g₁ - g₂) z = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg₁.sub hg₂)
    intro φ hφ hcs htsupp
    have e1 : ∫ z, φ z • g₁ z = ∫ z, φ z • g₂ z := by
      refine neg_inj.mp ?_
      rw [← h₁ φ hφ hcs htsupp, ← h₂ φ hφ hcs htsupp]
    have hi1 := integ φ hφ hcs htsupp hg₁
    have hi2 := integ φ hφ hcs htsupp hg₂
    calc ∫ z, φ z • (g₁ - g₂) z
        = ∫ z, (φ z • g₁ z - φ z • g₂ z) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [Pi.sub_apply]; exact smul_sub _ _ _
      _ = (∫ z, φ z • g₁ z) - ∫ z, φ z • g₂ z := integral_sub hi1 hi2
      _ = 0 := by rw [e1]; ring
  filter_upwards [key] with z hz hzΩ
  have := hz hzΩ
  simpa [Pi.sub_apply, sub_eq_zero] using this

/-- **Restriction.** A weak directional derivative on `Ω` is a weak directional
derivative on every subset. -/
theorem HasWeakDirDeriv.mono (h : HasWeakDirDeriv v g f Ω) {Ω' : Set ℂ}
    (hsub : Ω' ⊆ Ω) : HasWeakDirDeriv v g f Ω' := by
  intro φ hφ hcs htsupp
  exact h φ hφ hcs (htsupp.trans hsub)

/-- **Leibniz rule / closure under smooth multiplication.** If `g` is a weak
directional derivative of `f` and `ψ` is smooth, then `ψ • g + (∂ᵥψ) • f` is a
weak directional derivative of `ψ • f` — the product rule
`∂ᵥ(ψ f) = ψ ∂ᵥf + (∂ᵥψ) f` at the level of weak derivatives. -/
theorem HasWeakDirDeriv.smul_smooth (hf : HasWeakDirDeriv v g f Ω)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hfloc : LocallyIntegrableOn f Ω) (hgloc : LocallyIntegrableOn g Ω) :
    HasWeakDirDeriv v (fun z => ψ z • g z + ((fderiv ℝ ψ z) v) • f z)
      (fun z => ψ z • f z) Ω := by
  -- (continuous real, compactly supported in `Ω`) • (locally integrable on `Ω`) is integrable.
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ Ω →
      ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h Ω → Integrable (fun z => m z • h z) volume := by
    intro m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • (ψ z • f z) = - ∫ z, φ z • (ψ z • g z + ((fderiv ℝ ψ z) v) • f z)
  -- Test the hypothesis against the product test function `Φ = ψ * φ`.
  set Φ : ℂ → ℝ := fun z => ψ z * φ z with hΦ
  have hΦsmooth : ContDiff ℝ ∞ Φ := hψ.mul hφ
  have hΦcs : HasCompactSupport Φ := hcs.mul_left
  have hΦtsupp : tsupport Φ ⊆ Ω := subset_trans (tsupport_mul_subset_right) htsupp
  -- Product rule for the directional derivative `(fderiv ℝ Φ z) v`.
  have hpr : ∀ z, (fderiv ℝ Φ z) v = ψ z * ((fderiv ℝ φ z) v) + φ z * ((fderiv ℝ ψ z) v) := by
    intro z
    have hdψ : DifferentiableAt ℝ ψ z := (hψ.differentiable (by norm_num)).differentiableAt
    have hdφ : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
    change (fderiv ℝ (fun y => ψ y * φ y) z) v = _
    rw [fderiv_fun_mul hdψ hdφ]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hfΦ := hf Φ hΦsmooth hΦcs hΦtsupp
  have hcont_ψ : Continuous ψ := hψ.continuous
  have hcont_φ : Continuous φ := hφ.continuous
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont_dψ : Continuous (fun z => (fderiv ℝ ψ z) v) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_m1 : HasCompactSupport (fun z => ψ z * ((fderiv ℝ φ z) v)) :=
    HasCompactSupport.mul_left (HasCompactSupport.fderiv_apply ℝ hcs v)
  have hts_m1 : tsupport (fun z => ψ z * ((fderiv ℝ φ z) v)) ⊆ Ω :=
    subset_trans (tsupport_mul_subset_right)
      (subset_trans (tsupport_fderiv_apply_subset ℝ v) htsupp)
  have hcs_m2 : HasCompactSupport (fun z => φ z * ((fderiv ℝ ψ z) v)) := hcs.mul_right
  have hts_m2 : tsupport (fun z => φ z * ((fderiv ℝ ψ z) v)) ⊆ Ω :=
    subset_trans (tsupport_mul_subset_left) htsupp
  have iI_m1f : Integrable (fun z => (ψ z * ((fderiv ℝ φ z) v)) • f z) volume :=
    integ _ (hcont_ψ.mul hcont_dφ) hcs_m1 hts_m1 hfloc
  have iI_m2f : Integrable (fun z => (φ z * ((fderiv ℝ ψ z) v)) • f z) volume :=
    integ _ (hcont_φ.mul hcont_dψ) hcs_m2 hts_m2 hfloc
  -- Split the tested identity along the product rule.
  have hfΦ' : (∫ z, (ψ z * ((fderiv ℝ φ z) v)) • f z)
      + ∫ z, (φ z * ((fderiv ℝ ψ z) v)) • f z = - ∫ z, Φ z • g z := by
    rw [← integral_add iI_m1f iI_m2f, ← hfΦ]
    apply integral_congr_ae
    filter_upwards with z
    rw [hpr z]; module
  -- Rewrite the goal's two sides into the same pieces.
  have goalLHS : (∫ z, ((fderiv ℝ φ z) v) • (ψ z • f z))
      = ∫ z, (ψ z * ((fderiv ℝ φ z) v)) • f z := by
    apply integral_congr_ae
    filter_upwards with z
    module
  have goalRHS : (∫ z, φ z • (ψ z • g z + ((fderiv ℝ ψ z) v) • f z))
      = (∫ z, Φ z • g z) + ∫ z, (φ z * ((fderiv ℝ ψ z) v)) • f z := by
    have iI_g : Integrable (fun z => Φ z • g z) volume :=
      integ _ (hcont_ψ.mul hcont_φ) hΦcs hΦtsupp hgloc
    rw [← integral_add iI_g iI_m2f]
    apply integral_congr_ae
    filter_upwards with z
    simp only [hΦ]; module
  rw [goalLHS, goalRHS, neg_add, ← hfΦ']
  ring

/-- Weak directional derivatives are additive. -/
theorem HasWeakDirDeriv.add {f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (h₁ : HasWeakDirDeriv v g₁ f₁ Ω) (h₂ : HasWeakDirDeriv v g₂ f₂ Ω)
    (hf₁ : LocallyIntegrableOn f₁ Ω) (hf₂ : LocallyIntegrableOn f₂ Ω)
    (hg₁ : LocallyIntegrableOn g₁ Ω) (hg₂ : LocallyIntegrableOn g₂ Ω) :
    HasWeakDirDeriv v (fun z => g₁ z + g₂ z) (fun z => f₁ z + f₂ z) Ω := by
  -- (continuous real, compactly supported in `Ω`) • (locally integrable on `Ω`) is integrable.
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ Ω →
      ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h Ω → Integrable (fun z => m z • h z) volume := by
    intro m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • (f₁ z + f₂ z) = - ∫ z, φ z • (g₁ z + g₂ z)
  -- Integrability facts for the directional-derivative test function and `φ` itself.
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) v) :=
    HasCompactSupport.fderiv_apply ℝ hcs v
  have hts_dφ : tsupport (fun z => (fderiv ℝ φ z) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans htsupp
  have iIf₁ : Integrable (fun z => ((fderiv ℝ φ z) v) • f₁ z) volume :=
    integ _ hcont_dφ hcs_dφ hts_dφ hf₁
  have iIf₂ : Integrable (fun z => ((fderiv ℝ φ z) v) • f₂ z) volume :=
    integ _ hcont_dφ hcs_dφ hts_dφ hf₂
  have iIg₁ : Integrable (fun z => φ z • g₁ z) volume :=
    integ _ hφ.continuous hcs htsupp hg₁
  have iIg₂ : Integrable (fun z => φ z • g₂ z) volume :=
    integ _ hφ.continuous hcs htsupp hg₂
  have hlhs : (∫ z, ((fderiv ℝ φ z) v) • (f₁ z + f₂ z))
      = (∫ z, ((fderiv ℝ φ z) v) • f₁ z) + ∫ z, ((fderiv ℝ φ z) v) • f₂ z := by
    rw [← integral_add iIf₁ iIf₂]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_add _ _ _
  have hrhs : (∫ z, φ z • (g₁ z + g₂ z))
      = (∫ z, φ z • g₁ z) + ∫ z, φ z • g₂ z := by
    rw [← integral_add iIg₁ iIg₂]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_add _ _ _
  rw [hlhs, hrhs, h₁ φ hφ hcs htsupp, h₂ φ hφ hcs htsupp]
  ring

/-- Weak directional derivatives respect negation. -/
theorem HasWeakDirDeriv.neg (h : HasWeakDirDeriv v g f Ω) :
    HasWeakDirDeriv v (fun z => -g z) (fun z => -f z) Ω := by
  intro φ hφ hcs htsupp
  have hL : (∫ z, ((fderiv ℝ φ z) v) • (-f z)) = - ∫ z, ((fderiv ℝ φ z) v) • f z := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_neg _ _
  have hR : (∫ z, φ z • (-g z)) = - ∫ z, φ z • g z := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_neg _ _
  change (∫ z, ((fderiv ℝ φ z) v) • (-f z)) = - ∫ z, φ z • (-g z)
  rw [hL, hR, h φ hφ hcs htsupp]

/-- Weak directional derivatives are subtractive. -/
theorem HasWeakDirDeriv.sub {f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (h₁ : HasWeakDirDeriv v g₁ f₁ Ω) (h₂ : HasWeakDirDeriv v g₂ f₂ Ω)
    (hf₁ : LocallyIntegrableOn f₁ Ω) (hf₂ : LocallyIntegrableOn f₂ Ω)
    (hg₁ : LocallyIntegrableOn g₁ Ω) (hg₂ : LocallyIntegrableOn g₂ Ω) :
    HasWeakDirDeriv v (fun z => g₁ z - g₂ z) (fun z => f₁ z - f₂ z) Ω := by
  -- (continuous real, compactly supported in `Ω`) • (locally integrable on `Ω`) is integrable.
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ Ω →
      ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h Ω → Integrable (fun z => m z • h z) volume := by
    intro m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • (f₁ z - f₂ z) = - ∫ z, φ z • (g₁ z - g₂ z)
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) v) :=
    HasCompactSupport.fderiv_apply ℝ hcs v
  have hts_dφ : tsupport (fun z => (fderiv ℝ φ z) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans htsupp
  have iIf₁ : Integrable (fun z => ((fderiv ℝ φ z) v) • f₁ z) volume :=
    integ _ hcont_dφ hcs_dφ hts_dφ hf₁
  have iIf₂ : Integrable (fun z => ((fderiv ℝ φ z) v) • f₂ z) volume :=
    integ _ hcont_dφ hcs_dφ hts_dφ hf₂
  have iIg₁ : Integrable (fun z => φ z • g₁ z) volume :=
    integ _ hφ.continuous hcs htsupp hg₁
  have iIg₂ : Integrable (fun z => φ z • g₂ z) volume :=
    integ _ hφ.continuous hcs htsupp hg₂
  have hlhs : (∫ z, ((fderiv ℝ φ z) v) • (f₁ z - f₂ z))
      = (∫ z, ((fderiv ℝ φ z) v) • f₁ z) - ∫ z, ((fderiv ℝ φ z) v) • f₂ z := by
    rw [← integral_sub iIf₁ iIf₂]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_sub _ _ _
  have hrhs : (∫ z, φ z • (g₁ z - g₂ z))
      = (∫ z, φ z • g₁ z) - ∫ z, φ z • g₂ z := by
    rw [← integral_sub iIg₁ iIg₂]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_sub _ _ _
  rw [hlhs, hrhs, h₁ φ hφ hcs htsupp, h₂ φ hφ hcs htsupp]
  ring

/-- Weak directional derivatives are homogeneous: scaling `f` by a complex
constant scales its weak derivative by the same constant. -/
theorem HasWeakDirDeriv.const_smul (c : ℂ) (h : HasWeakDirDeriv v g f Ω) :
    HasWeakDirDeriv v (fun z => c • g z) (fun z => c • f z) Ω := by
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • (c • f z) = - ∫ z, φ z • (c • g z)
  have hlhs : (∫ z, ((fderiv ℝ φ z) v) • (c • f z))
      = c • ∫ z, ((fderiv ℝ φ z) v) • f z := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_comm _ c _
  have hrhs : (∫ z, φ z • (c • g z)) = c • ∫ z, φ z • g z := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_comm _ c _
  rw [hlhs, hrhs, h φ hφ hcs htsupp, smul_neg]

/-- **Additivity in the direction.** If `g₁` is a weak directional derivative of
`f` in the direction `v₁` and `g₂` in the direction `v₂`, then `g₁ + g₂` is a
weak directional derivative in the direction `v₁ + v₂` (the directional
derivative `z ↦ (fderiv ℝ φ z) v` is linear in `v`). -/
theorem HasWeakDirDeriv.dir_add {v₁ v₂ : ℂ}
    (h₁ : HasWeakDirDeriv v₁ g₁ f Ω) (h₂ : HasWeakDirDeriv v₂ g₂ f Ω)
    (hf : LocallyIntegrableOn f Ω) (hg₁ : LocallyIntegrableOn g₁ Ω)
    (hg₂ : LocallyIntegrableOn g₂ Ω) :
    HasWeakDirDeriv (v₁ + v₂) (fun z => g₁ z + g₂ z) f Ω := by
  -- (continuous real, compactly supported in `Ω`) • (locally integrable on `Ω`) is integrable.
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ Ω →
      ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h Ω → Integrable (fun z => m z • h z) volume := by
    intro m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) (v₁ + v₂)) • f z = - ∫ z, φ z • (g₁ z + g₂ z)
  -- Integrability facts.
  have hcont1 : Continuous (fun z => (fderiv ℝ φ z) v₁) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont2 : Continuous (fun z => (fderiv ℝ φ z) v₂) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs1 : HasCompactSupport (fun z => (fderiv ℝ φ z) v₁) :=
    HasCompactSupport.fderiv_apply ℝ hcs v₁
  have hcs2 : HasCompactSupport (fun z => (fderiv ℝ φ z) v₂) :=
    HasCompactSupport.fderiv_apply ℝ hcs v₂
  have hts1 : tsupport (fun z => (fderiv ℝ φ z) v₁) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v₁).trans htsupp
  have hts2 : tsupport (fun z => (fderiv ℝ φ z) v₂) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v₂).trans htsupp
  have iI1 : Integrable (fun z => ((fderiv ℝ φ z) v₁) • f z) volume := integ _ hcont1 hcs1 hts1 hf
  have iI2 : Integrable (fun z => ((fderiv ℝ φ z) v₂) • f z) volume := integ _ hcont2 hcs2 hts2 hf
  have iIg1 : Integrable (fun z => φ z • g₁ z) volume := integ _ hφ.continuous hcs htsupp hg₁
  have iIg2 : Integrable (fun z => φ z • g₂ z) volume := integ _ hφ.continuous hcs htsupp hg₂
  have hlhs : (∫ z, ((fderiv ℝ φ z) (v₁ + v₂)) • f z)
      = (∫ z, ((fderiv ℝ φ z) v₁) • f z) + ∫ z, ((fderiv ℝ φ z) v₂) • f z := by
    rw [← integral_add iI1 iI2]
    apply integral_congr_ae
    filter_upwards with z
    rw [map_add]; module
  have hrhs : (∫ z, φ z • (g₁ z + g₂ z)) = (∫ z, φ z • g₁ z) + ∫ z, φ z • g₂ z := by
    rw [← integral_add iIg1 iIg2]
    apply integral_congr_ae
    filter_upwards with z
    exact smul_add _ _ _
  rw [hlhs, hrhs, h₁ φ hφ hcs htsupp, h₂ φ hφ hcs htsupp]
  ring

/-- **Homogeneity in the direction.** Scaling the direction by a real constant
scales the weak directional derivative by the same constant. -/
theorem HasWeakDirDeriv.dir_smul (c : ℝ) (h : HasWeakDirDeriv v g f Ω) :
    HasWeakDirDeriv (c • v) (fun z => c • g z) f Ω := by
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) (c • v)) • f z = - ∫ z, φ z • (c • g z)
  have hlhs : (∫ z, ((fderiv ℝ φ z) (c • v)) • f z)
      = c • ∫ z, ((fderiv ℝ φ z) v) • f z := by
    have heq : (fun z => ((fderiv ℝ φ z) (c • v)) • f z)
        = fun z => c • (((fderiv ℝ φ z) v) • f z) := by
      funext z; rw [map_smul, smul_assoc]
    rw [heq]
    exact integral_smul c (fun z => ((fderiv ℝ φ z) v) • f z)
  have hrhs : (∫ z, φ z • (c • g z)) = c • ∫ z, φ z • g z := by
    have heq : (fun z => φ z • (c • g z)) = fun z => c • (φ z • g z) := by
      funext z; rw [smul_comm]
    rw [heq]
    exact integral_smul c (fun z => φ z • g z)
  rw [hlhs, hrhs, h φ hφ hcs htsupp]; module

/-- **Classical derivatives are weak derivatives.** A `C¹` function on an open
set has its classical directional derivative `z ↦ (fderiv ℝ f z) v` as a weak
directional derivative — integration by parts with no boundary term. -/
theorem HasWeakDirDeriv.of_contDiffOn (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) :
    HasWeakDirDeriv v (fun z => (fderiv ℝ f z) v) f Ω := by
  -- (continuous real, compactly supported in `Ω`) • (locally integrable on `Ω`) is integrable.
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ Ω →
      ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h Ω → Integrable (fun z => m z • h z) volume := by
    intro m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • f z = - ∫ z, φ z • ((fderiv ℝ f z) v)
  -- Local integrability of `f` and of its directional derivative on `Ω`.
  have hfloc : LocallyIntegrableOn f Ω :=
    hf.continuousOn.locallyIntegrableOn hΩ.measurableSet
  have hf'loc : LocallyIntegrableOn (fun z => (fderiv ℝ f z) v) Ω :=
    ((hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const).locallyIntegrableOn
      hΩ.measurableSet
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) v) :=
    HasCompactSupport.fderiv_apply ℝ hcs v
  have hts_dφ : tsupport (fun z => (fderiv ℝ φ z) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans htsupp
  -- The three integrability hypotheses of the integration-by-parts lemma.
  have h1 : Integrable (fun x => (fderiv ℝ φ x) v • f x) volume :=
    integ _ hcont_dφ hcs_dφ hts_dφ hfloc
  have h2 : Integrable (fun x => φ x • (fderiv ℝ f x) v) volume :=
    integ _ hφ.continuous hcs htsupp hf'loc
  have h3 : Integrable (fun x => φ x • f x) volume :=
    integ _ hφ.continuous hcs htsupp hfloc
  -- Differentiability witnesses on the relevant supports.
  have hd1 : ∀ x ∈ tsupport f, DifferentiableAt ℝ φ x :=
    fun x _ => (hφ.differentiable (by norm_num)).differentiableAt
  have hd2 : ∀ x ∈ tsupport φ, DifferentiableAt ℝ f x :=
    fun x hx => (hf.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds (htsupp hx))
  have L := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h3 hd1 hd2
  have L' : (∫ z, φ z • ((fderiv ℝ f z) v)) = -∫ z, ((fderiv ℝ φ z) v) • f z := L
  rw [L', neg_neg]

/-- For a `C¹` function the strong holomorphic Wirtinger derivative `dz f` is a
weak `∂`-derivative. -/
theorem hasWeakDz_of_contDiffOn (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) :
    HasWeakDz (fun z => dz f z) f Ω := by
  exact ⟨fun z => (fderiv ℝ f z) 1, fun z => (fderiv ℝ f z) Complex.I,
    HasWeakDirDeriv.of_contDiffOn hΩ hf, HasWeakDirDeriv.of_contDiffOn hΩ hf, fun z => rfl⟩

/-- For a `C¹` function the strong antiholomorphic Wirtinger derivative `dzbar f`
is a weak `∂̄`-derivative. -/
theorem hasWeakDzbar_of_contDiffOn (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) :
    HasWeakDzbar (fun z => dzbar f z) f Ω := by
  exact ⟨fun z => (fderiv ℝ f z) 1, fun z => (fderiv ℝ f z) Complex.I,
    HasWeakDirDeriv.of_contDiffOn hΩ hf, HasWeakDirDeriv.of_contDiffOn hΩ hf, fun z => rfl⟩

/-- Local `Lᵖ` membership restricts to subsets. -/
theorem MemLpLocOn.mono {p : ℝ≥0∞} (h : MemLpLocOn f p Ω) {Ω' : Set ℂ}
    (hsub : Ω' ⊆ Ω) : MemLpLocOn f p Ω' := by
  intro K hK hKc
  exact h K (hK.trans hsub) hKc

/-- Local Sobolev membership restricts to subsets. -/
theorem MemWklocP.mono {k : ℕ} {p : ℝ≥0∞} (h : MemWklocP f k p Ω) {Ω' : Set ℂ}
    (hsub : Ω' ⊆ Ω) : MemWklocP f k p Ω' := by
  induction k generalizing f with
  | zero => exact MemLpLocOn.mono h hsub
  | succ k ih =>
      obtain ⟨hLp, gx, gy, ⟨hgx, hgy⟩, hmgx, hmgy⟩ := h
      exact ⟨MemLpLocOn.mono hLp hsub, gx, gy,
        ⟨hgx.mono hsub, hgy.mono hsub⟩, ih hmgx, ih hmgy⟩

end NoWanderingDomains
