/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.GehringHigherIntegrability.SobolevPoincare

/-!
# Gehring self-improvement: weak IBP (N2) and the Caccioppoli inequality (N3)

The weak integration-by-parts / weak-Leibniz identity against a `W^{1,2}` test function
(`weakIBP_against_W12`, N2), and the `f`-level Caccioppoli inequality
`caccioppoli_of_beltrami` (N3) for a `W^{1,2}_loc` solution of `∂̄f = μ·∂f`.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace NoWanderingDomains

/-! ## N2 — weak integration by parts against a `W^{1,2}` test function -/

/-- **N2 (`weakIBP_against_W12`).** **Weak integration by parts / weak Leibniz against a
`W^{1,2}` test function.** The weak-derivative identity `∫ (∂ᵥφ)·F = −∫ φ·(∂ᵥF)` extends
from smooth compactly supported `φ` (the definition of `HasWeakDirDeriv`) to a compactly
supported `W^{1,2}` test function `φ` with weak directional derivative `φ'` in direction `v`.

This is what lets the Caccioppoli step (N3) test the Beltrami structure against the
non-smooth test function `φ = χ²·(F − c)` (which is only `W^{1,2}`, not `C^∞`).

*Derivation.* `φ` is the `W^{1,2}` limit of smooth compactly supported `φₙ`
(Mathlib's `MeasureTheory.MemLp.exist_eLpNorm_sub_le` applied to `φ` and `φ'`); the
identity for each `φₙ` (the `HasWeakDirDeriv` definition / `smul_smooth`) passes to the
limit by the `L²`-`L²` Cauchy–Schwarz pairing with `F` and its weak derivative `G`. -/
theorem weakIBP_against_W12 {v : ℂ} {F G φ φ' : ℂ → ℂ}
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hφ : MemLp φ 2 volume) (hφ' : MemLp φ' 2 volume)
    (hφcs : HasCompactSupport φ)
    (hGweak : HasWeakDirDeriv v G F Set.univ)
    (hφweak : HasWeakDirDeriv v φ' φ Set.univ) :
    ∫ z, φ' z * F z = - ∫ z, φ z * G z := by
  classical
  -- `2` and `2` are Hölder conjugates (`1/2 + 1/2 = 1`), so the product of two
  -- `L²` functions is `L¹` and the pairing is bounded by the product of the `L²` norms.
  have hHolder : ENNReal.HolderTriple 2 2 1 := ⟨by
    rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  -- ====================================================================
  -- (L) `L²`-`L²` Hölder pairing continuity: `‖∫ a·H‖ ≤ ‖a‖₂·‖H‖₂` for `a, H ∈ L²`.
  -- ====================================================================
  have pairing_le : ∀ {a H : ℂ → ℂ}, MemLp a 2 volume → MemLp H 2 volume →
      ‖∫ z, a z * H z‖ ≤ (eLpNorm a 2 volume * eLpNorm H 2 volume).toReal := by
    intro a H ha hH
    -- `‖∫ a·H‖ ≤ ∫⁻ ‖a·H‖ₑ = eLpNorm (a·H) 1`, then Hölder bounds the `L¹` norm.
    have h1 : ‖∫ z, a z * H z‖ₑ ≤ ∫⁻ z, ‖a z * H z‖ₑ ∂volume :=
      enorm_integral_le_lintegral_enorm _
    have h2 : (∫⁻ z, ‖a z * H z‖ₑ ∂volume) = eLpNorm (fun z => a z * H z) 1 volume :=
      eLpNorm_one_eq_lintegral_enorm.symm
    have h3 : eLpNorm (fun z => a z * H z) 1 volume
        ≤ eLpNorm a 2 volume * eLpNorm H 2 volume := by
      have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hH.1 ha.1
      simpa only [smul_eq_mul] using! this
    have h4 : ‖∫ z, a z * H z‖ₑ ≤ eLpNorm a 2 volume * eLpNorm H 2 volume :=
      le_trans h1 (le_trans (le_of_eq h2) h3)
    -- Pass from `‖·‖ₑ` to `‖·‖` (real).
    have hfin : eLpNorm a 2 volume * eLpNorm H 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top ha.eLpNorm_lt_top.ne hH.eLpNorm_lt_top.ne
    have := (ENNReal.toReal_le_toReal (by simp [enorm]) hfin).mpr h4
    simpa [enorm, ENNReal.toReal_ofReal, norm_nonneg] using this
  -- ====================================================================
  -- (ℂ) Complex-test-function lift of `hGweak`: the weak IBP identity holds against
  -- every SMOOTH compactly supported COMPLEX-valued test function `ψ`, with `*`.
  -- ====================================================================
  have hGweakℂ : ∀ ψ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      ∫ z, ((fderiv ℝ ψ z) v) * F z = - ∫ z, ψ z * G z := by
    intro ψ hψ hψcs
    -- Real and imaginary coordinate test functions.
    set χ₁ : ℂ → ℝ := fun z => (ψ z).re with hχ₁
    set χ₂ : ℂ → ℝ := fun z => (ψ z).im with hχ₂
    have hχ₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₁ := Complex.reCLM.contDiff.comp hψ
    have hχ₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₂ := Complex.imCLM.contDiff.comp hψ
    have hχ₁cs : HasCompactSupport χ₁ :=
      hψcs.comp_left (g := Complex.reCLM) (by simp)
    have hχ₂cs : HasCompactSupport χ₂ :=
      hψcs.comp_left (g := Complex.imCLM) (by simp)
    have hψdiff : Differentiable ℝ ψ := hψ.differentiable (by
      exact_mod_cast (by norm_num : ((⊤ : ℕ∞)) ≠ 0))
    -- The directional derivative of `ψ` splits along real/imaginary parts.
    have hreim : ∀ z, (fderiv ℝ ψ z) v
        = (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) + (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * Complex.I := by
      intro z
      have hdψ : HasFDerivAt ψ (fderiv ℝ ψ z) z := hψdiff.differentiableAt.hasFDerivAt
      have hd1 : HasFDerivAt χ₁ (Complex.reCLM.comp (fderiv ℝ ψ z)) z :=
        Complex.reCLM.hasFDerivAt.comp z hdψ
      have hd2 : HasFDerivAt χ₂ (Complex.imCLM.comp (fderiv ℝ ψ z)) z :=
        Complex.imCLM.hasFDerivAt.comp z hdψ
      rw [hd1.fderiv, hd2.fderiv]
      simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
      exact (Complex.re_add_im _).symm
    -- Pointwise rewrite of the LHS integrand.
    have hLHSpt : ∀ z, ((fderiv ℝ ψ z) v) * F z
        = (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z
            + Complex.I * ((((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z) := by
      intro z; rw [hreim z]; ring
    have hRHSpt : ∀ z, ψ z * G z
        = ((χ₁ z : ℝ) : ℂ) * G z + Complex.I * (((χ₂ z : ℝ) : ℂ) * G z) := by
      intro z
      have : ψ z = ((χ₁ z : ℝ) : ℂ) + ((χ₂ z : ℝ) : ℂ) * Complex.I := (Complex.re_add_im _).symm
      rw [this]; ring
    -- The two real test functions give the IBP identity (with `•` = real scalar `*`).
    have hG1 := hGweak χ₁ hχ₁sm hχ₁cs (Set.subset_univ _)
    have hG2 := hGweak χ₂ hχ₂sm hχ₂cs (Set.subset_univ _)
    -- Recast the `•` pairings as complex `*` pairings.
    have smul_to_mul : ∀ (c : ℝ) (w : ℂ), c • w = ((c : ℝ) : ℂ) * w :=
      fun c w => (Complex.real_smul).symm ▸ rfl
    -- Integrability of the four pieces (continuous compactly supported × `L²` is integrable).
    have integ_real : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m →
        ∀ {h : ℂ → ℂ}, MemLp h 2 volume →
        Integrable (fun z => ((m z : ℝ) : ℂ) * h z) volume := by
      intro m hm hmcs h hh
      have hmcsℂ : HasCompactSupport (fun z => ((m z : ℝ) : ℂ)) :=
        hmcs.comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
      have hmcont : Continuous (fun z => ((m z : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp hm
      have hmmem : MemLp (fun z => ((m z : ℝ) : ℂ)) 2 volume :=
        hmcont.memLp_of_hasCompactSupport hmcsℂ
      exact hmmem.integrable_mul hh
    have hcont_dχ₁ : Continuous (fun z => (fderiv ℝ χ₁ z) v) :=
      (hχ₁sm.continuous_fderiv (by exact_mod_cast (by norm_num : ((⊤ : ℕ∞)) ≠ 0))).clm_apply
        continuous_const
    have hcont_dχ₂ : Continuous (fun z => (fderiv ℝ χ₂ z) v) :=
      (hχ₂sm.continuous_fderiv (by exact_mod_cast (by norm_num : ((⊤ : ℕ∞)) ≠ 0))).clm_apply
        continuous_const
    have hcs_dχ₁ : HasCompactSupport (fun z => (fderiv ℝ χ₁ z) v) :=
      HasCompactSupport.fderiv_apply ℝ hχ₁cs v
    have hcs_dχ₂ : HasCompactSupport (fun z => (fderiv ℝ χ₂ z) v) :=
      HasCompactSupport.fderiv_apply ℝ hχ₂cs v
    -- LHS pieces.
    have iLHS1 : Integrable (fun z => (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z) volume :=
      integ_real _ hcont_dχ₁ hcs_dχ₁ hF
    have iLHS2 : Integrable (fun z => (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z) volume :=
      integ_real _ hcont_dχ₂ hcs_dχ₂ hF
    have iRHS1 : Integrable (fun z => ((χ₁ z : ℝ) : ℂ) * G z) volume :=
      integ_real _ hχ₁sm.continuous hχ₁cs hG
    have iRHS2 : Integrable (fun z => ((χ₂ z : ℝ) : ℂ) * G z) volume :=
      integ_real _ hχ₂sm.continuous hχ₂cs hG
    -- The two real identities, rephrased with complex `*`.
    have hG1' : (∫ z, (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z)
        = -∫ z, ((χ₁ z : ℝ) : ℂ) * G z := by
      have e1 : (∫ z, ((fderiv ℝ χ₁ z) v) • F z)
          = ∫ z, (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z := by
        apply integral_congr_ae; filter_upwards with z; exact smul_to_mul _ _
      have e2 : (∫ z, χ₁ z • G z) = ∫ z, ((χ₁ z : ℝ) : ℂ) * G z := by
        apply integral_congr_ae; filter_upwards with z; exact smul_to_mul _ _
      rw [← e1, ← e2, hG1]
    have hG2' : (∫ z, (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z)
        = -∫ z, ((χ₂ z : ℝ) : ℂ) * G z := by
      have e1 : (∫ z, ((fderiv ℝ χ₂ z) v) • F z)
          = ∫ z, (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z := by
        apply integral_congr_ae; filter_upwards with z; exact smul_to_mul _ _
      have e2 : (∫ z, χ₂ z • G z) = ∫ z, ((χ₂ z : ℝ) : ℂ) * G z := by
        apply integral_congr_ae; filter_upwards with z; exact smul_to_mul _ _
      rw [← e1, ← e2, hG2]
    -- Assemble.
    calc ∫ z, ((fderiv ℝ ψ z) v) * F z
        = ∫ z, ((((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z
            + Complex.I * ((((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z)) := by
          apply integral_congr_ae; filter_upwards with z; exact hLHSpt z
      _ = (∫ z, (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z)
            + Complex.I * ∫ z, (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z := by
          rw [integral_add iLHS1 (iLHS2.const_mul Complex.I)]
          congr 1
          exact integral_const_mul Complex.I (fun z => (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z)
      _ = (-∫ z, ((χ₁ z : ℝ) : ℂ) * G z)
            + Complex.I * (-∫ z, ((χ₂ z : ℝ) : ℂ) * G z) := by rw [hG1', hG2']
      _ = -((∫ z, ((χ₁ z : ℝ) : ℂ) * G z)
            + Complex.I * ∫ z, ((χ₂ z : ℝ) : ℂ) * G z) := by ring
      _ = -∫ z, (((χ₁ z : ℝ) : ℂ) * G z + Complex.I * (((χ₂ z : ℝ) : ℂ) * G z)) := by
          rw [integral_add iRHS1 (iRHS2.const_mul Complex.I)]
          congr 2
          exact (integral_const_mul Complex.I (fun z => ((χ₂ z : ℝ) : ℂ) * G z)).symm
      _ = -∫ z, ψ z * G z := by
          congr 1; apply integral_congr_ae; filter_upwards with z; exact (hRHSpt z).symm
  -- ====================================================================
  -- (F) Mollification commutes with the weak directional derivative (P3 technique).
  -- ====================================================================
  have fderiv_conv : ∀ {f gv : ℂ → ℂ},
      HasWeakDirDeriv v gv f Set.univ →
      MeasureTheory.LocallyIntegrable f → MeasureTheory.LocallyIntegrable gv →
      ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
      HasCompactSupport ρ → ∀ (z : ℂ),
        (fderiv ℝ (MeasureTheory.convolution ρ f
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
          = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro f gv hv hf hgv ρ hρ_smooth hρ_supp z
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
    have hρ_diff : Differentiable ℝ ρ :=
      hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
    have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
    have hderiv :
        HasFDerivAt (MeasureTheory.convolution ρ f L volume)
          (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
    rw [hderiv.fderiv]
    have hconvexists :
        MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) volume :=
      (hdρ_supp.convolutionExists_left (L.precompL ℂ)
        (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
    rw [MeasureTheory.convolution_def,
        ContinuousLinearMap.integral_apply hconvexists.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
    have hcv :
        (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂volume)
          = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume := by
      have hself := MeasureTheory.integral_sub_left_eq_self
        (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) volume z
      simp only [sub_sub_cancel] at hself
      exact hself.symm
    refine hcv.trans ?_
    set φz : ℂ → ℝ := fun u => ρ (z - u) with hφz
    have hφz_fderiv : ∀ u, (fderiv ℝ φz u) v = -((fderiv ℝ ρ (z - u)) v) := by
      intro u
      have hsub : HasFDerivAt (fun u : ℂ => z - u) (-ContinuousLinearMap.id ℝ ℂ) u := by
        simpa using (hasFDerivAt_id u).const_sub z
      have hcomp : HasFDerivAt φz
          ((fderiv ℝ ρ (z - u)).comp (-ContinuousLinearMap.id ℝ ℂ)) u :=
        (hρ_diff (z - u)).hasFDerivAt.comp u hsub
      rw [hcomp.fderiv]
      simp only [ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.id_apply, map_neg]
    have hint_eq :
        (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume)
          = -∫ u, ((fderiv ℝ φz u) v) • f u ∂volume := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
      rw [hφz_fderiv u]
      rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
        from neg_smul _ _, neg_neg]
    rw [hint_eq]
    have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
      hρ_smooth.comp (contDiff_const.sub contDiff_id)
    have hφz_supp : HasCompactSupport φz :=
      hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
    have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
    rw [hwd, neg_neg]
    rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
        (fun t => (L (ρ t)) (gv (z - t))) volume z]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
  -- ====================================================================
  -- (C) `L²` mollification convergence `‖ρ_n ⋆ g - g‖₂ → 0` for `g ∈ L²`.
  -- ====================================================================
  have conv_tendsto : ∀ {g : ℂ → ℂ},
      MemLp g 2 volume → ∀ (φb : ℕ → ContDiffBump (0 : ℂ)),
      Filter.Tendsto (fun n => (φb n).rOut) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φb n).normed volume) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - g) 2 volume)
        Filter.atTop (nhds 0) := by
    intro g hg φb hφrout
    set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φb n).normed volume)
      g (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
    have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
        Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φb n).normed volume) h
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
          Filter.atTop (nhds 0) := by
      intro h hh_supp hh_smooth
      obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
      have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
      set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
      have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
      have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
      have hKfin : volume Kset < ⊤ := hKcompact.measure_lt_top
      have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
      set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φb n).normed volume)
        h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
      have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
        HasCompactSupport.continuous_convolution_left _ ((φb n).hasCompactSupport_normed)
          ((φb n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
        ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
      have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
        intro n x
        set ρ := (φb n).normed volume with hρ
        have hρnn : ∀ t, 0 ≤ ρ t := (φb n).nonneg_normed
        rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
        calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
            ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ t, ρ t * M ∂volume := by
              have hint : Integrable ρ volume :=
                ((φb n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                  ((φb n).hasCompactSupport_normed)
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
              refine Filter.Eventually.of_forall (fun t => ?_)
              simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
              exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
          _ = (∫ t, ρ t ∂volume) * M := by rw [integral_mul_const]
          _ = M := by rw [(φb n).integral_normed]; ring
      have hMh : ∀ y, ‖h y‖ ≤ M := hM
      have hsupp_in_K : ∀ᶠ n in Filter.atTop, Function.support (Cn n) ⊆ Kset := by
        have hev : ∀ᶠ n in Filter.atTop, (φb n).rOut ≤ 1 := by
          have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
          filter_upwards [this] with n hn using hn
        filter_upwards [hev] with n hrout1
        have haddsub : Metric.closedBall (0 : ℂ) (φb n).rOut + tsupport h ⊆ Kset := by
          intro w hw
          obtain ⟨a, ha, b, hb, rfl⟩ := hw
          rw [Metric.mem_closedBall, dist_zero_right] at ha
          refine Metric.mem_cthickening_of_dist_le (a + b) b 1 (tsupport h) hb ?_
          rw [dist_eq_norm]; simp only [add_sub_cancel_right]; exact le_trans ha hrout1
        have hsub := MeasureTheory.support_convolution_subset (μ := volume)
          (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
          (f := (φb n).normed volume) (g := h)
        refine hsub.trans (le_trans ?_ haddsub)
        apply Set.add_subset_add _ (subset_tsupport h)
        intro w hw
        have h1 : w ∈ tsupport ((φb n).normed volume) := subset_tsupport _ hw
        rwa [(φb n).tsupport_normed_eq] at h1
      have : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
        constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
      set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
      have hrestrict : ∀ᶠ n in Filter.atTop,
          eLpNorm (D n) 2 volume = eLpNorm (D n) 2 (volume.restrict Kset) := by
        filter_upwards [hsupp_in_K] with n hn
        have hDsupp : Function.support (D n) ⊆ Kset := by
          intro x hx
          simp only [hD, Pi.sub_apply, Function.mem_support, ne_eq] at hx
          by_contra hxK
          have h1 : Cn n x = 0 := Function.notMem_support.mp (fun hc => hxK (hn hc))
          have h2 : h x = 0 := Function.notMem_support.mp
            (fun hc => hxK (htsupp_sub (subset_tsupport h hc)))
          rw [h1, h2, sub_zero] at hx; exact hx rfl
        rw [← eLpNorm_indicator_eq_eLpNorm_restrict hKmeas, Set.indicator_eq_self.mpr hDsupp]
      have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (volume.restrict Kset))
          Filter.atTop (nhds 0) := by
        have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
          refine MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num)
            (fun n => (hCn_cont n).aestronglyMeasurable) (fun ε hε => ?_)
          refine ⟨(M.toNNReal + 1), fun n => ?_⟩
          have hempty : {x | (M.toNNReal + 1 : ℝ≥0) ≤ ‖Cn n x‖₊} = (∅ : Set ℂ) := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
            have hb' : ‖Cn n x‖₊ ≤ M.toNNReal := by
              rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM0]; exact hCnbd n x
            exact lt_of_le_of_lt hb' (by simp)
          rw [hempty, Set.indicator_empty]; simp
        have hhmem : MemLp h 2 (volume.restrict Kset) :=
          MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
            (Filter.Eventually.of_forall hMh)
        exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
          (Filter.Eventually.of_forall hptwise)
      exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
    have hP2 : ∀ (u : ℂ → ℂ), MemLp u 2 volume → ∀ (ε : ℝ),
        eLpNorm u 2 volume ≤ ENNReal.ofReal ε → ∀ n,
          eLpNorm (MeasureTheory.convolution ((φb n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
      intro u hu ε hclose n
      set ρc : ℂ → ℂ := fun z => (((φb n).normed volume z : ℝ) : ℂ) with hρc
      have hconv_eq : MeasureTheory.convolution ((φb n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          = MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ) volume := by
        funext x
        rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
        exact (Complex.real_smul).symm
      rw [hconv_eq]
      have hρc_memLp : MemLp ρc 1 volume := by
        have hcont : Continuous ρc :=
          Complex.continuous_ofReal.comp ((φb n).contDiff_normed (n := 0)).continuous
        have hsupp : HasCompactSupport ρc :=
          ((φb n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
        exact hcont.memLp_of_hasCompactSupport hsupp
      have hρc_norm : eLpNorm ρc 1 volume = 1 := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have hint : Integrable ((φb n).normed volume) volume :=
          ((φb n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
            ((φb n).hasCompactSupport_normed)
        have hnn : 0 ≤ᵐ[volume] (φb n).normed volume :=
          Filter.Eventually.of_forall (fun z => (φb n).nonneg_normed z)
        calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
            = ∫⁻ z, ENNReal.ofReal ((φb n).normed volume z) ∂volume := by
              refine lintegral_congr (fun z => ?_)
              rw [hρc,
                show ‖(((φb n).normed volume z : ℝ) : ℂ)‖ₑ
                    = ‖(φb n).normed volume z‖ₑ from by
                  rw [← enorm_norm, Complex.norm_real, enorm_norm],
                Real.enorm_of_nonneg ((φb n).nonneg_normed z)]
          _ = ENNReal.ofReal (∫ z, (φb n).normed volume z ∂volume) :=
              (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
          _ = 1 := by rw [(φb n).integral_normed]; simp
      calc eLpNorm (MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ)
              volume) 2 volume
          ≤ eLpNorm ρc 1 volume * eLpNorm u 2 volume :=
            eLpNorm_convolution_le hρc_memLp hu
        _ = eLpNorm u 2 volume := by rw [hρc_norm, one_mul]
        _ ≤ ENNReal.ofReal ε := hclose
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · refine Filter.Eventually.of_forall (fun n => ?_)
      rw [htop]; exact le_top
    set δ : ℝ := ε.toReal with hδ
    have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
    have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
    obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ε := δ / 3) (by positivity)
    have hh_memLp : MemLp hh 2 volume :=
      hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
    have hgh_memLp : MemLp (g - hh) 2 volume := hg.sub hh_memLp
    have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φb n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      hP2 (g - hh) hgh_memLp (δ / 3) hh_close
    have hP3ev : ∀ᶠ n in Filter.atTop,
        eLpNorm (MeasureTheory.convolution ((φb n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
        (ENNReal.ofReal_pos.mpr (by positivity)))
    have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φb n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φb n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g) := by
      intro n
      have hce1 : MeasureTheory.ConvolutionExists ((φb n).normed volume) (g - hh)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        refine HasCompactSupport.convolutionExists_left _ ((φb n).hasCompactSupport_normed)
          ((φb n).contDiff_normed (n := 0)).continuous ?_
        exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
      have hce2 : MeasureTheory.ConvolutionExists ((φb n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        HasCompactSupport.convolutionExists_left _ ((φb n).hasCompactSupport_normed)
          ((φb n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hsplit : Cg n = MeasureTheory.convolution ((φb n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + MeasureTheory.convolution ((φb n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        rw [hCg]; simp only
        rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
        congr 1; abel
      rw [hsplit]; abel
    filter_upwards [hP3ev] with n hn3
    rw [hdecomp n]
    have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φb n).normed volume) (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) volume :=
      (HasCompactSupport.continuous_convolution_left _ ((φb n).hasCompactSupport_normed)
        ((φb n).contDiff_normed (n := 0)).continuous
        ((hg.locallyIntegrable (by norm_num)).sub
          hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φb n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
        volume - hh) volume :=
      ((HasCompactSupport.continuous_convolution_left _ ((φb n).hasCompactSupport_normed)
        ((φb n).contDiff_normed (n := 0)).continuous
        hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (hh - g) volume :=
      (hh_memLp.sub hg).1
    have hkey : eLpNorm (MeasureTheory.convolution ((φb n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φb n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g)) 2
          volume
        ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
      refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
      refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
      · exact add_le_add (hP2gh n) hn3
      · rw [eLpNorm_sub_comm]; exact hh_close
    refine le_trans hkey ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
    apply le_of_eq; congr 1; ring
  -- ====================================================================
  -- Assembly: build the mollified sequence and pass to the limit.
  -- ====================================================================
  -- Local integrability of `φ`, `φ'` (both `L²`, hence locally integrable).
  have hφ_li : MeasureTheory.LocallyIntegrable φ := hφ.locallyIntegrable (by norm_num)
  have hφ'_li : MeasureTheory.LocallyIntegrable φ' := hφ'.locallyIntegrable (by norm_num)
  -- A canonical mollifier sequence with `rOut = 2/(n+2) → 0`.
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [heq]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- The mollified test functions and their directional derivatives.
  set ρn : ℕ → ℂ → ℝ := fun n => (φ₀ n).normed volume with hρn
  set φn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρn n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume with hφn
  set φ'n : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρn n) φ' (ContinuousLinearMap.lsmul ℝ ℝ) volume with hφ'n
  have hρn_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρn n) := fun n =>
    (φ₀ n).contDiff_normed
  have hρn_cs : ∀ n, HasCompactSupport (ρn n) := fun n => (φ₀ n).hasCompactSupport_normed
  -- (1) Each `φn` is `C^∞`, compactly supported (a valid smooth test function).
  have hφn_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φn n) := by
    intro n
    refine HasCompactSupport.contDiff_convolution_left _ (hρn_cs n) ?_ hφ_li
    exact hρn_smooth n
  have hφn_cs : ∀ n, HasCompactSupport (φn n) := fun n =>
    HasCompactSupport.convolution _ (hρn_cs n) hφcs
  -- (2) The directional derivative of `φn` is `ρn ⋆ φ'`.
  have hφn_deriv : ∀ n z, (fderiv ℝ (φn n) z) v = φ'n n z := by
    intro n z
    exact fderiv_conv hφweak hφ_li hφ'_li (hρn_smooth n) (hρn_cs n) z
  -- (3) For each `n`, the smooth IBP identity from `hGweakℂ`.
  have hident : ∀ n, ∫ z, φ'n n z * F z = - ∫ z, φn n z * G z := by
    intro n
    have h := hGweakℂ (φn n) (hφn_smooth n) (hφn_cs n)
    rw [← h]
    apply integral_congr_ae; filter_upwards with z; rw [hφn_deriv n z]
  -- (4) `φn` is `L²` (continuous, compactly supported); `φ'n = ρn ⋆ φ'` is `L²` by Young.
  have hφn_memLp : ∀ n, MemLp (φn n) 2 volume := fun n =>
    (hφn_smooth n).continuous.memLp_of_hasCompactSupport (hφn_cs n)
  -- `‖ρn‖₁ = 1`, hence `‖ρn ⋆ φ'‖₂ ≤ ‖φ'‖₂ < ⊤`, giving `φ'n ∈ L²`.
  have hρn_memLp : ∀ n, MemLp (ρn n) 1 volume := fun n =>
    (hρn_smooth n).continuous.memLp_of_hasCompactSupport (hρn_cs n)
  have hρn_memLpℂ : ∀ n, MemLp (fun z => (((ρn n) z : ℝ) : ℂ)) 1 volume := by
    intro n
    have hcont : Continuous (fun z => (((ρn n) z : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hρn_smooth n).continuous
    have hsupp : HasCompactSupport (fun z => (((ρn n) z : ℝ) : ℂ)) :=
      (hρn_cs n).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
    exact hcont.memLp_of_hasCompactSupport hsupp
  have hφ'n_conv_eq : ∀ n, φ'n n
      = MeasureTheory.convolution (fun z => (((ρn n) z : ℝ) : ℂ)) φ'
        (ContinuousLinearMap.mul ℂ ℂ) volume := by
    intro n
    funext x
    rw [hφ'n]; simp only
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
    exact (Complex.real_smul).symm
  have hφ'n_memLp : ∀ n, MemLp (φ'n n) 2 volume := by
    intro n
    -- Measurability: `φ'n n` is a continuous `lsmul`-convolution.
    have hmeas : AEStronglyMeasurable (φ'n n) volume :=
      (HasCompactSupport.continuous_convolution_left _ (hρn_cs n)
        (hρn_smooth n).continuous hφ'_li).aestronglyMeasurable
    -- Finiteness: rewrite to the `mul`-convolution and apply Young `‖ρ ⋆ φ'‖₂ ≤ ‖ρ‖₁·‖φ'‖₂`.
    have hfin : eLpNorm (fun z => (((ρn n) z : ℝ) : ℂ)) 1 volume * eLpNorm φ' 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top (hρn_memLpℂ n).eLpNorm_lt_top.ne hφ'.eLpNorm_lt_top.ne
    have hlt : eLpNorm (φ'n n) 2 volume < ⊤ := by
      rw [hφ'n_conv_eq n]
      exact lt_of_le_of_lt (eLpNorm_convolution_le (hρn_memLpℂ n) hφ')
        (lt_of_le_of_ne le_top hfin)
    exact ⟨hmeas, hlt⟩
  -- (5) `L²` convergence of the two mollified sequences to `φ`, `φ'`.
  have hconvφ : Filter.Tendsto (fun n => eLpNorm (φn n - φ) 2 volume)
      Filter.atTop (nhds 0) := conv_tendsto hφ φ₀ hφ₀rout
  have hconvφ' : Filter.Tendsto (fun n => eLpNorm (φ'n n - φ') 2 volume)
      Filter.atTop (nhds 0) := conv_tendsto hφ' φ₀ hφ₀rout
  -- ====================================================================
  -- (Limit) Pass `n → ∞` in `∫ φ'n·F = -∫ φn·G`, using the Hölder pairing.
  -- ====================================================================
  -- Generic lemma: an `L²`-convergent sequence pairs continuously against a fixed `L²`
  -- function. From `‖aₙ − a‖₂ → 0` we get `∫ aₙ·H → ∫ a·H`.
  have pair_tendsto : ∀ {an : ℕ → ℂ → ℂ} {a H : ℂ → ℂ},
      (∀ n, MemLp (an n) 2 volume) → MemLp a 2 volume → MemLp H 2 volume →
      Filter.Tendsto (fun n => eLpNorm (an n - a) 2 volume) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => ∫ z, an n z * H z) Filter.atTop (nhds (∫ z, a z * H z)) := by
    intro an a H han ha hH hconv
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- `‖∫ aₙ·H − ∫ a·H‖ = ‖∫ (aₙ − a)·H‖ ≤ ‖aₙ − a‖₂·‖H‖₂`.
    have hbound : ∀ n, ‖(∫ z, an n z * H z) - ∫ z, a z * H z‖
        ≤ (eLpNorm (an n - a) 2 volume * eLpNorm H 2 volume).toReal := by
      intro n
      have hint1 : Integrable (fun z => an n z * H z) volume := (han n).integrable_mul hH
      have hint2 : Integrable (fun z => a z * H z) volume := ha.integrable_mul hH
      have hsub : (∫ z, an n z * H z) - ∫ z, a z * H z
          = ∫ z, (an n z - a z) * H z := by
        rw [← integral_sub hint1 hint2]
        apply integral_congr_ae; filter_upwards with z; ring
      rw [hsub]
      have hpe := pairing_le ((han n).sub ha) hH
      refine le_trans (le_of_eq ?_) hpe
      simp only [Pi.sub_apply]
    -- The bound `→ 0`, so eventually `< ε`.
    have htend0 : Filter.Tendsto
        (fun n => (eLpNorm (an n - a) 2 volume * eLpNorm H 2 volume).toReal)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => eLpNorm (an n - a) 2 volume * eLpNorm H 2 volume)
          Filter.atTop (nhds (0 * eLpNorm H 2 volume)) :=
        ENNReal.Tendsto.mul_const hconv (Or.inr hH.eLpNorm_lt_top.ne)
      rw [zero_mul] at h1
      have h2 := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp h1
      simpa only [Function.comp_def, ENNReal.toReal_zero] using h2
    rw [Metric.tendsto_atTop] at htend0
    obtain ⟨N, hN⟩ := htend0 ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hbound n) ?_
    have hNn := hN n hn
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg ENNReal.toReal_nonneg] at hNn
    exact hNn
  -- LHS `∫ φ'n·F → ∫ φ'·F`, RHS `-∫ φn·G → -∫ φ·G`.
  have hLHS_tendsto : Filter.Tendsto (fun n => ∫ z, φ'n n z * F z)
      Filter.atTop (nhds (∫ z, φ' z * F z)) :=
    pair_tendsto hφ'n_memLp hφ' hF hconvφ'
  have hRHS_tendsto : Filter.Tendsto (fun n => -∫ z, φn n z * G z)
      Filter.atTop (nhds (-∫ z, φ z * G z)) :=
    (pair_tendsto hφn_memLp hφ hG hconvφ).neg
  -- The two sequences are equal for each `n`, so their limits agree.
  exact tendsto_nhds_unique (hLHS_tendsto.congr (fun n => (hident n))) hRHS_tendsto

/-! ## N3 — the `f`-level Caccioppoli inequality -/

set_option maxHeartbeats 400000 in
-- The proof bundles the full Beurling-`L²`-energy mollification argument (the `∂`/`∂̄`
-- isometry on the smooth approximants) together with the commutator absorption and the
-- planar `⨍⁻`-average conversion in a single elaboration, so it needs a raised budget.
/-- **N3 (`caccioppoli_of_beltrami`).** The **`f`-level Caccioppoli (reverse-Poincaré)
inequality** for a weak holomorphic gradient `G = ½(Gx − I·Gy)` of a primitive `F` (weak
partials `Gx, Gy`) that solves the **differential** Beltrami relation `∂̄F = μ·∂F + R`, i.e.
`½(Gx + I·Gy) = μ·G + R` a.e., with inhomogeneity `R ∈ L²`.

There is a constant `A ≥ 0`, depending only on `‖μ‖∞` (hence **independent of the ball**
`x, r` and of the solution), such that on every ball `B = ball x r` the gradient energy is
bounded by the oscillation of `F` on the doubled ball `2B = ball x (2r)` (scaled by `r⁻²`)
plus the inhomogeneity:
`(⨍⁻_{B} ‖G‖²)^(1/2) ≤ A · r⁻¹ · (⨍⁻_{2B} ‖F − F_{2B}‖²)^(1/2)
    + A · (⨍⁻_{2B} ‖R‖²)^(1/2)`.

The localized relation is consumed as a hypothesis; the caller `reverseHolder_of_weakGradient`
(S1) supplies it (with `R = ½(Gx + I·Gy) − μ·G`, automatically `L²`), so no `L²`-Beurling
machinery enters here.

*Derivation.* Test the differential relation against `φ = χ²·(F − F_{2B})` for a cutoff `χ`
adapted to `B` (with `|∇χ| ≲ r⁻¹`), using the weak IBP node N2 (the test function is only
`W^{1,2}`). The cross term and the `∇χ`-commutator are absorbed by the ellipticity `‖μ‖∞ < 1`,
converting the gradient energy on `B` into the lower-order oscillation
`r⁻²·⨍⁻_{2B}‖F − F_{2B}‖²` plus the forcing `‖R‖`, the classical Caccioppoli step.
*Dependency:* N2. -/
theorem caccioppoli_of_beltrami {μ : ℂ → ℂ}
    (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hμbound : eLpNormEssSup μ volume < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {F G Gx Gy R : ℂ → ℂ},
      MemLp F 2 volume → MemLp G 2 volume → MemLp R 2 volume →
      MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      (∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) →
      (∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z) →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r, (‖G z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) ≤
            ENNReal.ofReal (A / r) *
              (⨍⁻ z in Metric.ball x (2 * r),
                (‖F z - (⨍ w in Metric.ball x (2 * r), F w)‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
                ^ (1 / (2 : ℝ)) +
            ENNReal.ofReal A *
              (⨍⁻ z in Metric.ball x (2 * r), (‖R z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
                ^ (1 / (2 : ℝ)) := by
  classical
  -- The uniform cutoff gradient constant `Cχ` (ball-independent).
  obtain ⟨Cχ, hCχ0, hCut⟩ := exists_cutoff_ball_uniform
  -- `M := ‖μ‖∞.toReal < 1`.
  set M : ℝ := (eLpNormEssSup μ volume).toReal with hM_def
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hμessSup_eq : eLpNormEssSup μ volume = ENNReal.ofReal M := by
    rw [hM_def, ENNReal.ofReal_toReal hμfin]
  have hM1 : M < 1 := by
    rw [hM_def]
    have : (1 : ℝ≥0∞).toReal = 1 := by norm_num
    rw [← this]
    exact (ENNReal.toReal_lt_toReal hμfin (by norm_num)).mpr hμbound
  have h1M0 : (0 : ℝ) < 1 - M := by linarith
  -- The combined Caccioppoli constant.
  refine ⟨(4 * Cχ + 2) / (1 - M), by positivity, ?_⟩
  intro F G Gx Gy R hFmem hGmem hRmem hGxmem hGymem hGxweak hGyweak hGdef hRrel x r hr
  set A : ℝ := (4 * Cχ + 2) / (1 - M) with hA_def
  have hA0 : 0 ≤ A := by rw [hA_def]; positivity
  -- ====================================================================
  -- (Setup) The cutoff `χ`, the centring constant `c = ⨍_{2B} F`, the balls.
  -- ====================================================================
  set B : Set ℂ := Metric.ball x r with hB_def
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  have hVolB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVolBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hVolB20 : volume B2 ≠ 0 := (Metric.measure_ball_pos volume x h2r).ne'
  have hVolB2top : volume B2 ≠ ⊤ := measure_ball_lt_top.ne
  set c : ℂ := ⨍ w in B2, F w ∂volume with hc_def
  -- The cutoff adapted to `B`.
  obtain ⟨χ, hχcd, hχcs, hχ0, hχ1, hχB, hχsupp, hχgrad⟩ := hCut x r hr
  have hχcont : Continuous χ := hχcd.continuous
  have hsupp_sub_B2 : tsupport χ ⊆ B2 := by
    refine hχsupp.trans ?_
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [hB2_def, Metric.mem_ball]
    exact lt_of_le_of_lt hz (by linarith)
  -- ====================================================================
  -- (u, gxu, gyu) the cutoff product and its weak partials.
  -- ====================================================================
  set u : ℂ → ℂ := fun z => χ z • (F z - c) with hu_def
  set gxu : ℂ → ℂ := fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c) with hgxu_def
  set gyu : ℂ → ℂ := fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c) with hgyu_def
  obtain ⟨hxweak, hyweak⟩ :=
    cutoff_weak_partials (c := c) hFmem hGxmem hGymem hGxweak hGyweak hχcd
  -- `MemLp` of `u`, `gxu`, `gyu` at `L²`, with compact support.
  have hHT221 : ENNReal.HolderTriple 2 2 1 := ⟨by
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one, ENNReal.inv_two_add_inv_two]⟩
  have hdχcont : Continuous (fun z => (fderiv ℝ χ z) 1) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχIcont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hχmemTop : MemLp χ ∞ volume := hχcont.memLp_top_of_hasCompactSupport hχcs volume
  have hdχcs : HasCompactSupport (fun z => (fderiv ℝ χ z) 1) :=
    HasCompactSupport.fderiv_apply ℝ hχcs 1
  have hdχIcs : HasCompactSupport (fun z => (fderiv ℝ χ z) Complex.I) :=
    HasCompactSupport.fderiv_apply ℝ hχcs Complex.I
  have hdχmemTop : MemLp (fun z => (fderiv ℝ χ z) 1) ∞ volume :=
    hdχcont.memLp_top_of_hasCompactSupport hdχcs volume
  have hdχImemTop : MemLp (fun z => (fderiv ℝ χ z) Complex.I) ∞ volume :=
    hdχIcont.memLp_top_of_hasCompactSupport hdχIcs volume
  have hχc_mem2 : MemLp (fun z => χ z • c) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hχcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]; fun_prop
  have hdχc_mem2 : MemLp (fun z => ((fderiv ℝ χ z) 1) • c) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hdχcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp hdχcont).mul continuous_const
  have hdχIc_mem2 : MemLp (fun z => ((fderiv ℝ χ z) Complex.I) • c) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hdχIcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp hdχIcont).mul continuous_const
  have hχF2 : MemLp (fun z => χ z • F z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hFmem hχmemTop
  have hχGx2 : MemLp (fun z => χ z • Gx z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hGxmem hχmemTop
  have hχGy2 : MemLp (fun z => χ z • Gy z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hGymem hχmemTop
  have hdχF2 : MemLp (fun z => ((fderiv ℝ χ z) 1) • F z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hFmem hdχmemTop
  have hdχIF2 : MemLp (fun z => ((fderiv ℝ χ z) Complex.I) • F z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hFmem hdχImemTop
  have humem : MemLp u 2 volume := by
    refine MemLp.ae_eq ?_ (hχF2.sub hχc_mem2)
    filter_upwards with z
    simp only [hu_def, Pi.sub_apply]
    module
  have hucs : HasCompactSupport u :=
    hχcs.smul_right (f' := fun z => F z - c)
  have hgxumem : MemLp gxu 2 volume := by
    refine MemLp.ae_eq ?_ (hχGx2.add (hdχF2.sub hdχc_mem2))
    filter_upwards with z
    simp only [hgxu_def, Pi.sub_apply, Pi.add_apply]
    module
  have hgyumem : MemLp gyu 2 volume := by
    refine MemLp.ae_eq ?_ (hχGy2.add (hdχIF2.sub hdχIc_mem2))
    filter_upwards with z
    simp only [hgyu_def, Pi.sub_apply, Pi.add_apply]
    module
  -- The weak `∂` and `∂̄` of `u`.
  set Du : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gxu z - Complex.I * gyu z) with hDu_def
  set Dbaru : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gxu z + Complex.I * gyu z) with hDbaru_def
  have hDumem : MemLp Du 2 volume := by
    have hmem := (hgxumem.sub (hgyumem.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
    refine MemLp.ae_eq ?_ hmem
    filter_upwards with z
    simp only [hDu_def, Pi.sub_apply]
  have hDbarumem : MemLp Dbaru 2 volume := by
    have hmem := (hgxumem.add (hgyumem.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
    refine MemLp.ae_eq ?_ hmem
    filter_upwards with z
    simp only [hDbaru_def, Pi.add_apply]
  -- ====================================================================
  -- (E) KEY ENERGY EQUALITY: `eLpNorm Du 2 = eLpNorm Dbaru 2`.
  -- ====================================================================
  have hEnergy : eLpNorm Du 2 volume = eLpNorm Dbaru 2 volume := by
    -- Local integrability of `u`, `gxu`, `gyu` (from `L²` membership).
    have hu_li : MeasureTheory.LocallyIntegrable u := humem.locallyIntegrable (by norm_num)
    have hgxu_li : MeasureTheory.LocallyIntegrable gxu := hgxumem.locallyIntegrable (by norm_num)
    have hgyu_li : MeasureTheory.LocallyIntegrable gyu := hgyumem.locallyIntegrable (by norm_num)
    -- ================================================================
    -- (F) Mollification commutes with the weak directional derivative.
    -- ================================================================
    have fderiv_conv : ∀ {f gv : ℂ → ℂ} {v : ℂ},
        HasWeakDirDeriv v gv f Set.univ →
        MeasureTheory.LocallyIntegrable f → MeasureTheory.LocallyIntegrable gv →
        ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
        HasCompactSupport ρ → ∀ (z : ℂ),
          (fderiv ℝ (MeasureTheory.convolution ρ f
              (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
            = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
      intro f gv v hv hf hgv ρ hρ_smooth hρ_supp z
      set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
      have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ :=
        hρ_smooth.of_le (by exact_mod_cast le_top)
      have hρ_diff : Differentiable ℝ ρ :=
        hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
      have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
      have hderiv :
          HasFDerivAt (MeasureTheory.convolution ρ f L volume)
            (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) volume z) z :=
        HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
      rw [hderiv.fderiv]
      have hconvexists :
          MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) volume :=
        (hdρ_supp.convolutionExists_left (L.precompL ℂ)
          (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
      rw [MeasureTheory.convolution_def,
          ContinuousLinearMap.integral_apply hconvexists.integrable]
      simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
      have hcv :
          (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂volume)
            = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume := by
        have hself := MeasureTheory.integral_sub_left_eq_self
          (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) volume z
        simp only [sub_sub_cancel] at hself
        exact hself.symm
      refine hcv.trans ?_
      set φz : ℂ → ℝ := fun u => ρ (z - u) with hφz
      have hφz_fderiv : ∀ u, (fderiv ℝ φz u) v = -((fderiv ℝ ρ (z - u)) v) := by
        intro u
        have hsub : HasFDerivAt (fun u : ℂ => z - u) (-ContinuousLinearMap.id ℝ ℂ) u := by
          simpa using (hasFDerivAt_id u).const_sub z
        have hcomp : HasFDerivAt φz
            ((fderiv ℝ ρ (z - u)).comp (-ContinuousLinearMap.id ℝ ℂ)) u :=
          (hρ_diff (z - u)).hasFDerivAt.comp u hsub
        rw [hcomp.fderiv]
        simp only [ContinuousLinearMap.comp_apply, neg_apply,
          ContinuousLinearMap.id_apply, map_neg]
      have hint_eq :
          (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume)
            = -∫ u, ((fderiv ℝ φz u) v) • f u ∂volume := by
        rw [← MeasureTheory.integral_neg]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
        rw [hφz_fderiv u]
        rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
          from neg_smul _ _, neg_neg]
      rw [hint_eq]
      have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
        hρ_smooth.comp (contDiff_const.sub contDiff_id)
      have hφz_supp : HasCompactSupport φz :=
        hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
      have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
      rw [hwd, neg_neg]
      rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
          (fun t => (L (ρ t)) (gv (z - t))) volume z]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
    -- ================================================================
    -- (C) `L²` mollification convergence `‖ρ_n ⋆ g - g‖₂ → 0` for `g ∈ L²`.
    -- ================================================================
    have conv_tendsto : ∀ {g : ℂ → ℂ},
        MemLp g 2 volume → ∀ (φ : ℕ → ContDiffBump (0 : ℂ)),
        Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => eLpNorm
            (MeasureTheory.convolution ((φ n).normed volume) g
              (ContinuousLinearMap.lsmul ℝ ℝ) volume - g) 2 volume)
          Filter.atTop (nhds 0) := by
      intro g hg φ hφrout
      set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
        g (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
      have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
          Filter.Tendsto (fun n => eLpNorm
            (MeasureTheory.convolution ((φ n).normed volume) h
              (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
            Filter.atTop (nhds 0) := by
        intro h hh_supp hh_smooth
        obtain ⟨Mbd, hMbd⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
        have hMbd0 : 0 ≤ Mbd := le_trans (norm_nonneg (h 0)) (hMbd 0)
        set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
        have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
        have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
        have hKfin : volume Kset < ⊤ := hKcompact.measure_lt_top
        have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
        set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
          h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
        have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
          HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
            ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
        have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
          ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
        have hCnbd : ∀ n x, ‖Cn n x‖ ≤ Mbd := by
          intro n x
          set ρ := (φ n).normed volume with hρ
          have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
          rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
          calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
              ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
                norm_integral_le_integral_norm _
            _ ≤ ∫ t, ρ t * Mbd ∂volume := by
                have hint : Integrable ρ volume :=
                  ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                    ((φ n).hasCompactSupport_normed)
                apply integral_mono_of_nonneg
                  (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const Mbd)
                refine Filter.Eventually.of_forall (fun t => ?_)
                simp only [ContinuousLinearMap.lsmul_apply, norm_smul,
                  Real.norm_of_nonneg (hρnn t)]
                exact mul_le_mul_of_nonneg_left (hMbd _) (hρnn t)
            _ = (∫ t, ρ t ∂volume) * Mbd := by rw [integral_mul_const]
            _ = Mbd := by rw [(φ n).integral_normed]; ring
        have hMh : ∀ y, ‖h y‖ ≤ Mbd := hMbd
        have hsupp_in_K : ∀ᶠ n in Filter.atTop, Function.support (Cn n) ⊆ Kset := by
          have hev : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 1 := by
            have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
            filter_upwards [this] with n hn using hn
          filter_upwards [hev] with n hrout1
          have haddsub : Metric.closedBall (0 : ℂ) (φ n).rOut + tsupport h ⊆ Kset := by
            intro z hz
            obtain ⟨a, ha, b, hb, rfl⟩ := hz
            rw [Metric.mem_closedBall, dist_zero_right] at ha
            refine Metric.mem_cthickening_of_dist_le (a + b) b 1 (tsupport h) hb ?_
            rw [dist_eq_norm]; simp only [add_sub_cancel_right]; exact le_trans ha hrout1
          have hsub := MeasureTheory.support_convolution_subset (μ := volume)
            (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
            (f := (φ n).normed volume) (g := h)
          refine hsub.trans (le_trans ?_ haddsub)
          apply Set.add_subset_add _ (subset_tsupport h)
          intro z hz
          have h1 : z ∈ tsupport ((φ n).normed volume) := subset_tsupport _ hz
          rwa [(φ n).tsupport_normed_eq] at h1
        have : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
          constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
        set Dn : ℕ → ℂ → ℂ := fun n => Cn n - h with hDn
        have hrestrict : ∀ᶠ n in Filter.atTop,
            eLpNorm (Dn n) 2 volume = eLpNorm (Dn n) 2 (volume.restrict Kset) := by
          filter_upwards [hsupp_in_K] with n hn
          have hDsupp : Function.support (Dn n) ⊆ Kset := by
            intro x hx
            simp only [hDn, Pi.sub_apply, Function.mem_support, ne_eq] at hx
            by_contra hxK
            have h1 : Cn n x = 0 := Function.notMem_support.mp (fun hc => hxK (hn hc))
            have h2 : h x = 0 := Function.notMem_support.mp
              (fun hc => hxK (htsupp_sub (subset_tsupport h hc)))
            rw [h1, h2, sub_zero] at hx; exact hx rfl
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict hKmeas, Set.indicator_eq_self.mpr hDsupp]
        have hgoal : Filter.Tendsto (fun n => eLpNorm (Dn n) 2 (volume.restrict Kset))
            Filter.atTop (nhds 0) := by
          have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
            refine MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num)
              (fun n => (hCn_cont n).aestronglyMeasurable) (fun ε hε => ?_)
            refine ⟨(Mbd.toNNReal + 1), fun n => ?_⟩
            have hempty : {x | (Mbd.toNNReal + 1 : ℝ≥0) ≤ ‖Cn n x‖₊} = (∅ : Set ℂ) := by
              ext x
              simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
              have hb' : ‖Cn n x‖₊ ≤ Mbd.toNNReal := by
                rw [← NNReal.coe_le_coe, Real.coe_toNNReal Mbd hMbd0]; exact hCnbd n x
              exact lt_of_le_of_lt hb' (by simp)
            rw [hempty, Set.indicator_empty]; simp
          have hhmem : MemLp h 2 (volume.restrict Kset) :=
            MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable Mbd
              (Filter.Eventually.of_forall hMh)
          exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
            (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
            (Filter.Eventually.of_forall hptwise)
        exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
      have hP2 : ∀ (uu : ℂ → ℂ), MemLp uu 2 volume → ∀ (ε : ℝ),
          eLpNorm uu 2 volume ≤ ENNReal.ofReal ε → ∀ n,
            eLpNorm (MeasureTheory.convolution ((φ n).normed volume) uu
              (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
        intro uu hu ε hclose n
        set ρc : ℂ → ℂ := fun z => (((φ n).normed volume z : ℝ) : ℂ) with hρc
        have hconv_eq : MeasureTheory.convolution ((φ n).normed volume) uu
              (ContinuousLinearMap.lsmul ℝ ℝ) volume
            = MeasureTheory.convolution ρc uu (ContinuousLinearMap.mul ℂ ℂ) volume := by
          funext x
          rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
          simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
          exact (Complex.real_smul).symm
        rw [hconv_eq]
        have hρc_memLp : MemLp ρc 1 volume := by
          have hcont : Continuous ρc :=
            Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
          have hsupp : HasCompactSupport ρc :=
            ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
          exact hcont.memLp_of_hasCompactSupport hsupp
        have hρc_norm : eLpNorm ρc 1 volume = 1 := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          have hint : Integrable ((φ n).normed volume) volume :=
            ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
              ((φ n).hasCompactSupport_normed)
          have hnn : 0 ≤ᵐ[volume] (φ n).normed volume :=
            Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
          calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
              = ∫⁻ z, ENNReal.ofReal ((φ n).normed volume z) ∂volume := by
                refine lintegral_congr (fun z => ?_)
                rw [hρc,
                  show ‖(((φ n).normed volume z : ℝ) : ℂ)‖ₑ
                      = ‖(φ n).normed volume z‖ₑ from by
                    rw [← enorm_norm, Complex.norm_real, enorm_norm],
                  Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
            _ = ENNReal.ofReal (∫ z, (φ n).normed volume z ∂volume) :=
                (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
            _ = 1 := by rw [(φ n).integral_normed]; simp
        calc eLpNorm (MeasureTheory.convolution ρc uu (ContinuousLinearMap.mul ℂ ℂ)
                volume) 2 volume
            ≤ eLpNorm ρc 1 volume * eLpNorm uu 2 volume :=
              eLpNorm_convolution_le hρc_memLp hu
          _ = eLpNorm uu 2 volume := by rw [hρc_norm, one_mul]
          _ ≤ ENNReal.ofReal ε := hclose
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      by_cases htop : ε = ⊤
      · refine Filter.Eventually.of_forall (fun n => ?_)
        rw [htop]; exact le_top
      set δ : ℝ := ε.toReal with hδ
      have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
      have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
      obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (ε := δ / 3) (by positivity)
      have hh_memLp : MemLp hh 2 volume :=
        hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
      have hgh_memLp : MemLp (g - hh) 2 volume := hg.sub hh_memLp
      have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
            ≤ ENNReal.ofReal (δ / 3) :=
        hP2 (g - hh) hgh_memLp (δ / 3) hh_close
      have hP3ev : ∀ᶠ n in Filter.atTop,
          eLpNorm (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
            ≤ ENNReal.ofReal (δ / 3) :=
        (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
          (ENNReal.ofReal_pos.mpr (by positivity)))
      have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + (MeasureTheory.convolution ((φ n).normed volume) hh
              (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g) := by
        intro n
        have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed volume) (g - hh)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
          refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
            ((φ n).contDiff_normed (n := 0)).continuous ?_
          exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
        have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
          HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
            ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
        have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed volume)
              (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
            + MeasureTheory.convolution ((φ n).normed volume) hh
              (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
          rw [hCg]; simp only
          rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
          congr 1; abel
        rw [hsplit]; abel
      filter_upwards [hP3ev] with n hn3
      rw [hdecomp n]
      have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
          ((φ n).normed volume) (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
          volume) volume :=
        (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous
          ((hg.locallyIntegrable (by norm_num)).sub
            hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
      have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
          ((φ n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
          volume - hh) volume :=
        ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous
          hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (hh - g) volume :=
        (hh_memLp.sub hg).1
      have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + (MeasureTheory.convolution ((φ n).normed volume) hh
              (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g)) 2
            volume
          ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
        refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
        refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
        · exact add_le_add (hP2gh n) hn3
        · rw [eLpNorm_sub_comm]; exact hh_close
      refine le_trans hkey ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
      apply le_of_eq; congr 1; ring
    -- ================================================================
    -- The canonical mollifier sequence and the mollified sequences.
    -- ================================================================
    set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
    have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
      have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
      rw [heq]
      exact Filter.Tendsto.div_atTop tendsto_const_nhds
        (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    set ρN : ℕ → ℂ → ℝ := fun n => (φ₀ n).normed volume with hρN
    have hρN_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρN n) :=
      fun n => (φ₀ n).contDiff_normed
    have hρN_cs : ∀ n, HasCompactSupport (ρN n) := fun n => (φ₀ n).hasCompactSupport_normed
    set un : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρN n) u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hun
    set Pn : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρN n) gxu (ContinuousLinearMap.lsmul ℝ ℝ) volume with hPn
    set Qn : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρN n) gyu (ContinuousLinearMap.lsmul ℝ ℝ) volume with hQn
    -- `un` is `C^∞` and compactly supported.
    have hun_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (un n) := fun n =>
      HasCompactSupport.contDiff_convolution_left _ (hρN_cs n) (hρN_smooth n) hu_li
    have hun_cs : ∀ n, HasCompactSupport (un n) := fun n =>
      HasCompactSupport.convolution _ (hρN_cs n) hucs
    -- `(fderiv un) 1 = Pn`, `(fderiv un) I = Qn`.
    have hfd1 : ∀ n z, (fderiv ℝ (un n) z) 1 = Pn n z := fun n z =>
      fderiv_conv hxweak hu_li hgxu_li (hρN_smooth n) (hρN_cs n) z
    have hfdI : ∀ n z, (fderiv ℝ (un n) z) Complex.I = Qn n z := fun n z =>
      fderiv_conv hyweak hu_li hgyu_li (hρN_smooth n) (hρN_cs n) z
    -- `dz un = (1/2)(Pn - I Qn)`, `dzbar un = (1/2)(Pn + I Qn)`.
    have hdz_un : ∀ n z, dz (un n) z = (1 / 2 : ℂ) * (Pn n z - Complex.I * Qn n z) := by
      intro n z; rw [dz, hfd1 n z, hfdI n z]
    have hdzbar_un : ∀ n z, dzbar (un n) z = (1 / 2 : ℂ) * (Pn n z + Complex.I * Qn n z) := by
      intro n z; rw [dzbar, hfd1 n z, hfdI n z]
    -- ================================================================
    -- (Iso) `eLpNorm (dz un) 2 = eLpNorm (dzbar un) 2` for each `n`.
    -- ================================================================
    have hiso : ∀ n, eLpNorm (dz (un n)) 2 volume = eLpNorm (dzbar (un n)) 2 volume := by
      intro n
      have hun2 : ContDiff ℝ (2 : ℕ∞) (un n) :=
        HasCompactSupport.contDiff_convolution_left _ (hρN_cs n)
          ((hρN_smooth n).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))) hu_li
      have hun1 : ContDiff ℝ (1 : ℕ∞) (un n) :=
        hun2.of_le (by exact_mod_cast (by norm_num : (1 : ℕ∞) ≤ 2))
      -- `dzbar un` is `C^∞` and compactly supported (the smooth `Φ` applied to `fderiv un`).
      set Φ : (ℂ →L[ℝ] ℂ) → ℂ := fun D => (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I) with hΦ
      have hdzbar_eq : (fun ζ => dzbar (un n) ζ) = Φ ∘ (fun ζ => fderiv ℝ (un n) ζ) := by
        funext ζ; rfl
      have hfderiv_cinf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => fderiv ℝ (un n) ζ) :=
        (hun_smooth n).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by
          simp)
      have hfderiv_c1 : ContDiff ℝ 1 (fun ζ => fderiv ℝ (un n) ζ) :=
        hun2.fderiv_right (m := 1) (by norm_num)
      have hΦ_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
        have hΦ_lin : Φ = (fun D : ℂ →L[ℝ] ℂ =>
            (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
              + Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
          funext D; simp [hΦ, ContinuousLinearMap.apply_apply, smul_eq_mul]
        rw [hΦ_lin]
        exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).add
          ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
      have hdzbar_cinf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => dzbar (un n) ζ) := by
        rw [hdzbar_eq]; exact hΦ_cd.comp hfderiv_cinf
      have hdzbar_c1 : ContDiff ℝ 1 (fun ζ => dzbar (un n) ζ) :=
        hdzbar_cinf.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
      have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ (un n) ζ) :=
        (hun_cs n).fderiv (𝕜 := ℝ)
      have hdzbar_cs : HasCompactSupport (fun ζ => dzbar (un n) ζ) := by
        rw [hdzbar_eq]; refine hfderiv_cs.comp_left ?_; simp [hΦ]
      -- `dz un = beurling (dzbar un)` (inlined `dz_eq_beurling_dzbar`, via Cauchy–Pompeiu).
      have hP : cauchyTransform (fun ζ => dzbar (un n) ζ) = un n := by
        funext z; exact cauchyTransform_dzbar hun1 (hun_cs n) z
      have hbeur : ∀ z, dz (un n) z = beurling (fun ζ => dzbar (un n) ζ) z := by
        intro z
        calc dz (un n) z = dz (cauchyTransform (fun ζ => dzbar (un n) ζ)) z := by rw [hP]
          _ = beurling (fun ζ => dzbar (un n) ζ) z :=
              beurling_eq_dz_cauchyTransform hdzbar_c1 hdzbar_cs z
      -- The isometry.
      have hiso0 : eLpNorm (beurling (fun ζ => dzbar (un n) ζ)) 2 volume
          = eLpNorm (fun ζ => dzbar (un n) ζ) 2 volume :=
        beurling_l2_isometry_smooth hdzbar_cinf hdzbar_cs
      calc eLpNorm (dz (un n)) 2 volume
          = eLpNorm (fun z => beurling (fun ζ => dzbar (un n) ζ) z) 2 volume := by
            refine congrArg (fun f => eLpNorm f 2 volume) ?_; funext z; exact hbeur z
        _ = eLpNorm (fun ζ => dzbar (un n) ζ) 2 volume := hiso0
    -- ================================================================
    -- (Conv) `dz un → Du` and `dzbar un → Dbaru` in `L²`.
    -- ================================================================
    have hPconv : Filter.Tendsto (fun n => eLpNorm (fun z => Pn n z - gxu z) 2 volume)
        Filter.atTop (nhds 0) := conv_tendsto hgxumem φ₀ hφ₀rout
    have hQconv : Filter.Tendsto (fun n => eLpNorm (fun z => Qn n z - gyu z) 2 volume)
        Filter.atTop (nhds 0) := conv_tendsto hgyumem φ₀ hφ₀rout
    -- AE-strong-measurability facts.
    have hPn_aesm : ∀ n, AEStronglyMeasurable (Pn n) volume := fun n =>
      (HasCompactSupport.continuous_convolution_left _ (hρN_cs n)
        (hρN_smooth n).continuous hgxu_li).aestronglyMeasurable
    have hQn_aesm : ∀ n, AEStronglyMeasurable (Qn n) volume := fun n =>
      (HasCompactSupport.continuous_convolution_left _ (hρN_cs n)
        (hρN_smooth n).continuous hgyu_li).aestronglyMeasurable
    have hPn_cont : ∀ n, Continuous (Pn n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ (hρN_cs n)
        (hρN_smooth n).continuous hgxu_li
    have hQn_cont : ∀ n, Continuous (Qn n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ (hρN_cs n)
        (hρN_smooth n).continuous hgyu_li
    have hdz_aesm : ∀ n, AEStronglyMeasurable (dz (un n)) volume := fun n => by
      have hc : Continuous (dz (un n)) := by
        rw [show dz (un n) = fun z => (1 / 2 : ℂ) * (Pn n z - Complex.I * Qn n z)
          from funext (hdz_un n)]
        exact continuous_const.mul ((hPn_cont n).sub (continuous_const.mul (hQn_cont n)))
      exact hc.aestronglyMeasurable
    have hdzbar_aesm : ∀ n, AEStronglyMeasurable (dzbar (un n)) volume := fun n => by
      have hc : Continuous (dzbar (un n)) := by
        rw [show dzbar (un n) = fun z => (1 / 2 : ℂ) * (Pn n z + Complex.I * Qn n z)
          from funext (hdzbar_un n)]
        exact continuous_const.mul ((hPn_cont n).add (continuous_const.mul (hQn_cont n)))
      exact hc.aestronglyMeasurable
    -- Half-norm and `I`-norm as `ENNReal` constants.
    have hhalf_e : ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2) := by
      rw [← ofReal_norm]; norm_num
    have hI_e : ‖(Complex.I : ℂ)‖ₑ = 1 := by
      rw [← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one]
    -- A generic const-smul `eLpNorm` bound for the relevant lambdas.
    have hcsmul : ∀ (c : ℂ) (f : ℂ → ℂ),
        eLpNorm (fun z => c • f z) 2 volume = ‖c‖ₑ * eLpNorm f 2 volume := fun c f => by
      have := eLpNorm_const_smul (μ := volume) (p := 2) c f
      simpa using! this
    -- `eLpNorm (dz un - Du) ≤ (1/2)(eLpNorm (Pn-gxu) + eLpNorm (Qn-gyu))`, and similarly for ∂̄.
    have htri_dz : ∀ n, eLpNorm (fun z => dz (un n) z - Du z) 2 volume ≤
        ENNReal.ofReal (1 / 2) *
          (eLpNorm (fun z => Pn n z - gxu z) 2 volume
            + eLpNorm (fun z => Qn n z - gyu z) 2 volume) := by
      intro n
      have heq : (fun z => dz (un n) z - Du z)
          = fun z => (1 / 2 : ℂ) • ((Pn n z - gxu z) - Complex.I • (Qn n z - gyu z)) := by
        funext z
        rw [hdz_un n z, hDu_def]
        simp only [smul_eq_mul]; ring
      rw [heq, hcsmul, hhalf_e]
      gcongr
      refine le_trans (eLpNorm_sub_le ((hPn_aesm n).sub hgxumem.1)
        (((hQn_aesm n).sub hgyumem.1).const_smul Complex.I) (by norm_num)) ?_
      gcongr
      rw [show (fun z => Complex.I • (Qn n z - gyu z))
          = (fun z => Complex.I • ((fun w => Qn n w - gyu w) z)) from rfl, hcsmul, hI_e, one_mul]
    have htri_dzbar : ∀ n, eLpNorm (fun z => dzbar (un n) z - Dbaru z) 2 volume ≤
        ENNReal.ofReal (1 / 2) *
          (eLpNorm (fun z => Pn n z - gxu z) 2 volume
            + eLpNorm (fun z => Qn n z - gyu z) 2 volume) := by
      intro n
      have heq : (fun z => dzbar (un n) z - Dbaru z)
          = fun z => (1 / 2 : ℂ) • ((Pn n z - gxu z) + Complex.I • (Qn n z - gyu z)) := by
        funext z
        rw [hdzbar_un n z, hDbaru_def]
        simp only [smul_eq_mul]; ring
      rw [heq, hcsmul, hhalf_e]
      gcongr
      refine le_trans (eLpNorm_add_le ((hPn_aesm n).sub hgxumem.1)
        (((hQn_aesm n).sub hgyumem.1).const_smul Complex.I) (by norm_num)) ?_
      gcongr
      rw [show (fun z => Complex.I • (Qn n z - gyu z))
          = (fun z => Complex.I • ((fun w => Qn n w - gyu w) z)) from rfl, hcsmul, hI_e, one_mul]
    -- The `L²`-distances `dz un → Du`, `dzbar un → Dbaru` tend to `0`.
    have hRHStendsto : Filter.Tendsto
        (fun n => ENNReal.ofReal (1 / 2) *
          (eLpNorm (fun z => Pn n z - gxu z) 2 volume
            + eLpNorm (fun z => Qn n z - gyu z) 2 volume))
        Filter.atTop (nhds 0) := by
      have hsum : Filter.Tendsto
          (fun n => eLpNorm (fun z => Pn n z - gxu z) 2 volume
            + eLpNorm (fun z => Qn n z - gyu z) 2 volume) Filter.atTop (nhds 0) := by
        have := hPconv.add hQconv; simpa using this
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (1 / 2)) hsum
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    have hdzdist : Filter.Tendsto (fun n => eLpNorm (fun z => dz (un n) z - Du z) 2 volume)
        Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHStendsto
        (fun n => zero_le) htri_dz
    have hdzbardist : Filter.Tendsto
        (fun n => eLpNorm (fun z => dzbar (un n) z - Dbaru z) 2 volume)
        Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHStendsto
        (fun n => zero_le) htri_dzbar
    -- eLpNorm continuity: `eLpNorm (a_n) → eLpNorm a` when `eLpNorm (a_n - a) → 0`.
    have eLpNorm_tendsto : ∀ {a : ℂ → ℂ} {an : ℕ → ℂ → ℂ},
        (∀ n, AEStronglyMeasurable (an n) volume) → AEStronglyMeasurable a volume →
        eLpNorm a 2 volume ≠ ⊤ →
        Filter.Tendsto (fun n => eLpNorm (fun z => an n z - a z) 2 volume)
          Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => eLpNorm (an n) 2 volume) Filter.atTop
          (nhds (eLpNorm a 2 volume)) := by
      intro a an han ha hafin hdist
      set en : ℕ → ℝ≥0∞ := fun n => eLpNorm (fun z => an n z - a z) 2 volume with hen
      have hupper : ∀ n, eLpNorm (an n) 2 volume ≤ eLpNorm a 2 volume + en n := by
        intro n
        have hsplit : (an n) = (fun z => (an n z - a z) + a z) := by funext z; ring
        calc eLpNorm (an n) 2 volume
            = eLpNorm (fun z => (an n z - a z) + a z) 2 volume := by rw [← hsplit]
          _ ≤ eLpNorm (fun z => an n z - a z) 2 volume + eLpNorm a 2 volume :=
              eLpNorm_add_le ((han n).sub ha) ha (by norm_num)
          _ = eLpNorm a 2 volume + en n := by rw [hen]; ring
      have hlower : ∀ n, eLpNorm a 2 volume ≤ eLpNorm (an n) 2 volume + en n := by
        intro n
        have hsplit : a = (fun z => a z - an n z + an n z) := by funext z; ring
        have hcomm : en n = eLpNorm (fun z => a z - an n z) 2 volume := by
          rw [hen]; exact eLpNorm_sub_comm (an n) a 2 volume
        calc eLpNorm a 2 volume
            = eLpNorm (fun z => (a z - an n z) + an n z) 2 volume := by rw [← hsplit]
          _ ≤ eLpNorm (fun z => a z - an n z) 2 volume + eLpNorm (an n) 2 volume :=
              eLpNorm_add_le (ha.sub (han n)) (han n) (by norm_num)
          _ = eLpNorm (an n) 2 volume + en n := by rw [hcomm]; ring
      -- Squeeze: `eLpNorm a - en ≤ eLpNorm (an n) ≤ eLpNorm a + en`.
      have hupper_t : Filter.Tendsto (fun n => eLpNorm a 2 volume + en n) Filter.atTop
          (nhds (eLpNorm a 2 volume)) := by
        have := Filter.Tendsto.const_add (eLpNorm a 2 volume) hdist
        simpa using this
      have hlower_t : Filter.Tendsto (fun n => eLpNorm a 2 volume - en n) Filter.atTop
          (nhds (eLpNorm a 2 volume)) := by
        have hsub := ENNReal.Tendsto.sub (tendsto_const_nhds (x := eLpNorm a 2 volume))
          hdist (Or.inl hafin)
        simpa using hsub
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower_t hupper_t (fun n => ?_)
        (fun n => hupper n)
      exact tsub_le_iff_right.mpr (hlower n)
    have hdzlim : Filter.Tendsto (fun n => eLpNorm (dz (un n)) 2 volume) Filter.atTop
        (nhds (eLpNorm Du 2 volume)) :=
      eLpNorm_tendsto hdz_aesm hDumem.1 hDumem.eLpNorm_lt_top.ne hdzdist
    have hdzbarlim : Filter.Tendsto (fun n => eLpNorm (dzbar (un n)) 2 volume) Filter.atTop
        (nhds (eLpNorm Dbaru 2 volume)) :=
      eLpNorm_tendsto hdzbar_aesm hDbarumem.1 hDbarumem.eLpNorm_lt_top.ne hdzbardist
    -- The two limits coincide by the per-`n` isometry.
    have hdzbarlim' : Filter.Tendsto (fun n => eLpNorm (dz (un n)) 2 volume) Filter.atTop
        (nhds (eLpNorm Dbaru 2 volume)) := by
      refine hdzbarlim.congr (fun n => ?_)
      exact (hiso n).symm
    exact tendsto_nhds_unique hdzlim hdzbarlim'
  -- ====================================================================
  -- (Cacc) The Caccioppoli bound from the energy equality.
  -- ====================================================================
  -- Abbreviations for the gradient-norm constant `Cχ/r` and the half-balls' supports.
  have hCr0 : (0 : ℝ) ≤ Cχ / r := by positivity
  have hdχ_supp1 : Function.support (fun z => (fderiv ℝ χ z) 1) ⊆ B2 :=
    (subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset (𝕜 := ℝ) 1).trans hsupp_sub_B2)
  have hdχ_suppI : Function.support (fun z => (fderiv ℝ χ z) Complex.I) ⊆ B2 :=
    (subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset (𝕜 := ℝ) Complex.I).trans hsupp_sub_B2)
  have hχ_supp : Function.support χ ⊆ B2 := (subset_tsupport χ).trans hsupp_sub_B2
  -- `χ•G` is in `L²` (`MemLp.smul`), with the convenient enorm identity `‖χ•G‖ₑ = ‖χ‖ₑ·‖G‖ₑ`.
  have hχG2 : MemLp (fun z => χ z • G z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hGmem hχmemTop
  have hχR2 : MemLp (fun z => χ z • R z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hRmem hχmemTop
  -- `μ·G` is in `L²` (`‖μ‖∞ < ∞`), hence so is `χ•(μ·G)`.
  have hμG2 : MemLp (fun z => μ z * G z) 2 volume := by
    have := MemLp.smul (r := 2) (p := ∞) (q := 2) hGmem
      (μ := volume) (f := G) (φ := μ) ?_
    · refine MemLp.ae_eq ?_ this
      filter_upwards with z; simp [smul_eq_mul]
    · refine ⟨hμmeas.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_exponent_top, hμessSup_eq]; exact ENNReal.ofReal_lt_top
  have hχμG2 : MemLp (fun z => χ z • (μ z * G z)) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hμG2 hχmemTop
  -- ‖μ z‖ₑ ≤ ofReal M a.e.
  have hμae : ∀ᵐ z ∂(volume : Measure ℂ), (‖μ z‖ₑ) ≤ ENNReal.ofReal M := by
    filter_upwards [ae_le_eLpNormEssSup (f := μ) (μ := volume)] with z hz
    rwa [hμessSup_eq] at hz
  -- ================================================================
  -- (D-split) `Du = χ•G + Eχ`, `Dbaru =ᵐ χ•(μG) + χ•R + Eχbar`,  with the commutator bound.
  -- ================================================================
  -- `Du z - χ z • G z` and `Dbaru z - χ z•(μG z) - χ z•R z` are commutators `≲ (Cχ/r)‖F-c‖`.
  set Eχ : ℂ → ℂ := fun z => Du z - χ z • G z with hEχ_def
  set Eχbar : ℂ → ℂ := fun z => Dbaru z - χ z • (μ z * G z) - χ z • R z with hEχbar_def
  -- Pointwise formulas for the commutators (purely algebraic, using `hGdef`/`hRrel`).
  have hEχ_eq : ∀ z, Eχ z = (1 / 2 : ℂ) * ((((fderiv ℝ χ z) 1 : ℝ) : ℂ) * (F z - c)
      - Complex.I * ((((fderiv ℝ χ z) Complex.I : ℝ) : ℂ) * (F z - c))) := by
    intro z
    simp only [hEχ_def, hDu_def, hgxu_def, hgyu_def, Complex.real_smul]
    rw [hGdef z]; ring
  have hEχbar_eq : ∀ᵐ z, Eχbar z = (1 / 2 : ℂ) * ((((fderiv ℝ χ z) 1 : ℝ) : ℂ) * (F z - c)
      + Complex.I * ((((fderiv ℝ χ z) Complex.I : ℝ) : ℂ) * (F z - c))) := by
    filter_upwards [hRrel] with z hz
    simp only [hEχbar_def, hDbaru_def, hgxu_def, hgyu_def, Complex.real_smul]
    have hrel : (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z := hz
    -- `(1/2)(χGx + (∂χ)(F-c) + I(χGy + (∂χ)(F-c))) = χ((1/2)(Gx+IGy)) + commutator`
    have hkey : (1 / 2 : ℂ) * (((χ z : ℝ) : ℂ) * Gx z + (((fderiv ℝ χ z) 1 : ℝ) : ℂ) * (F z - c)
        + Complex.I * (((χ z : ℝ) : ℂ) * Gy z
          + (((fderiv ℝ χ z) Complex.I : ℝ) : ℂ) * (F z - c)))
        = ((χ z : ℝ) : ℂ) * ((1 / 2 : ℂ) * (Gx z + Complex.I * Gy z))
          + (1 / 2 : ℂ) * ((((fderiv ℝ χ z) 1 : ℝ) : ℂ) * (F z - c)
            + Complex.I * ((((fderiv ℝ χ z) Complex.I : ℝ) : ℂ) * (F z - c))) := by ring
    rw [hkey, hrel]; ring
  -- The pointwise commutator enorm bound `‖E z‖ₑ ≤ (Cχ/r)‖F z - c‖ₑ` (for `E ∈ {Eχ, Eχbar}`).
  have hcomm_bd : ∀ (a b : ℝ), |a| ≤ Cχ / r → |b| ≤ Cχ / r → ∀ (w : ℂ),
      ‖(1 / 2 : ℂ) * (((a : ℝ) : ℂ) * w + Complex.I * (((b : ℝ) : ℂ) * w))‖ₑ
        ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ ∧
      ‖(1 / 2 : ℂ) * (((a : ℝ) : ℂ) * w - Complex.I * (((b : ℝ) : ℂ) * w))‖ₑ
        ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
    intro a b ha hb w
    have hbound : ∀ (s : ℂ), s = (((a : ℝ) : ℂ) * w + Complex.I * (((b : ℝ) : ℂ) * w))
        ∨ s = (((a : ℝ) : ℂ) * w - Complex.I * (((b : ℝ) : ℂ) * w)) →
        ‖(1 / 2 : ℂ) * s‖ₑ ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
      intro s hs
      -- The two enorm building blocks: `‖a•w‖ₑ ≤ ofReal(Cχ/r)·‖w‖ₑ` and likewise for `b`.
      have hae : ‖((a : ℝ) : ℂ) * w‖ₑ ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
        rw [enorm_mul]
        gcongr
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal ha
      have hI_e : ‖(Complex.I : ℂ)‖ₑ = 1 := by
        rw [← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one]
      have hbe : ‖Complex.I * (((b : ℝ) : ℂ) * w)‖ₑ ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
        rw [enorm_mul, hI_e, one_mul, enorm_mul]
        gcongr
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal hb
      have hsbd : ‖s‖ₑ ≤ ENNReal.ofReal (2 * (Cχ / r)) * ‖w‖ₑ := by
        have htwo : ENNReal.ofReal (2 * (Cχ / r)) * ‖w‖ₑ
            = ENNReal.ofReal (Cχ / r) * ‖w‖ₑ + ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
          rw [← add_mul, ← ENNReal.ofReal_add hCr0 hCr0]; congr 2; ring
        rw [htwo]
        rcases hs with hs | hs
        · rw [hs]; exact le_trans (enorm_add_le _ _) (add_le_add hae hbe)
        · rw [hs]; exact le_trans enorm_sub_le (add_le_add hae hbe)
      calc ‖(1 / 2 : ℂ) * s‖ₑ = ‖(1 / 2 : ℂ)‖ₑ * ‖s‖ₑ := by rw [enorm_mul]
        _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * (Cχ / r)) * ‖w‖ₑ) := by
            refine mul_le_mul' ?_ hsbd
            rw [← ofReal_norm]; norm_num
        _ = ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]; congr 2; ring
    constructor
    · exact hbound _ (Or.inl rfl)
    · exact hbound _ (Or.inr rfl)
  -- The half-norms over `2B` and the gradient energy over `B`.
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  set oscHalf : ℝ≥0∞ := (∫⁻ z in B2, ‖F z - c‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
    with hoscHalf_def
  set RHalf : ℝ≥0∞ := (∫⁻ z in B2, ‖R z‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hRHalf_def
  -- |∂_v χ| ≤ Cχ/r for `v ∈ {1, I}` (operator-norm bound).
  have hdχ1_bd : ∀ z, |(fderiv ℝ χ z) 1| ≤ Cχ / r := by
    intro z
    calc |(fderiv ℝ χ z) 1| = ‖(fderiv ℝ χ z) 1‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ χ z‖ * ‖(1 : ℂ)‖ := (fderiv ℝ χ z).le_opNorm 1
      _ ≤ (Cχ / r) * 1 := by
          refine mul_le_mul (hχgrad z) ?_ (norm_nonneg _) (by positivity)
          simp
      _ = Cχ / r := mul_one _
  have hdχI_bd : ∀ z, |(fderiv ℝ χ z) Complex.I| ≤ Cχ / r := by
    intro z
    calc |(fderiv ℝ χ z) Complex.I| = ‖(fderiv ℝ χ z) Complex.I‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ χ z‖ * ‖Complex.I‖ := (fderiv ℝ χ z).le_opNorm Complex.I
      _ ≤ (Cχ / r) * 1 := by
          refine mul_le_mul (hχgrad z) ?_ (norm_nonneg _) (by positivity)
          rw [Complex.norm_I]
      _ = Cχ / r := mul_one _
  -- Off `2B`, both `∂_v χ` vanish.
  have hd1_zero : ∀ z, z ∉ B2 → (fderiv ℝ χ z) 1 = 0 := by
    intro z hz
    by_contra hne
    exact hz (hdχ_supp1 hne)
  have hdI_zero : ∀ z, z ∉ B2 → (fderiv ℝ χ z) Complex.I = 0 := by
    intro z hz
    by_contra hne
    exact hz (hdχ_suppI hne)
  -- Pointwise commutator enorm bounds with the `2B`-support.
  have hEχ_pt : ∀ z, ‖Eχ z‖ₑ ≤ B2.indicator (fun z => ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z := by
    intro z
    by_cases hz : z ∈ B2
    · rw [Set.indicator_of_mem hz, hEχ_eq z]
      exact (hcomm_bd _ _ (hdχ1_bd z) (hdχI_bd z) (F z - c)).2
    · rw [Set.indicator_of_notMem hz, hEχ_eq z, hd1_zero z hz, hdI_zero z hz]; simp
  have hEχbar_pt : ∀ᵐ z, ‖Eχbar z‖ₑ
      ≤ B2.indicator (fun z => ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z := by
    filter_upwards [hEχbar_eq] with z hz
    by_cases hzm : z ∈ B2
    · rw [Set.indicator_of_mem hzm, hz]
      exact (hcomm_bd _ _ (hdχ1_bd z) (hdχI_bd z) (F z - c)).1
    · rw [Set.indicator_of_notMem hzm, hz, hd1_zero z hzm, hdI_zero z hzm]; simp
  have hχR_pt : ∀ z, ‖χ z • R z‖ₑ ≤ B2.indicator (fun z => ‖R z‖ₑ) z := by
    intro z
    by_cases hz : z ∈ B2
    · rw [Set.indicator_of_mem hz, Complex.real_smul, enorm_mul]
      calc ‖((χ z : ℝ) : ℂ)‖ₑ * ‖R z‖ₑ ≤ 1 * ‖R z‖ₑ := by
            gcongr
            rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (hχ0 z)]
            exact ENNReal.ofReal_le_one.2 (hχ1 z)
        _ = ‖R z‖ₑ := one_mul _
    · rw [Set.indicator_of_notMem hz]
      have hχz : χ z = 0 := Function.notMem_support.1 (fun h => hz (hχ_supp h))
      rw [hχz]; simp
  -- The `L²`-mass bounds: `eLpNorm E ≤ ofReal(Cχ/r)·oscHalf` and `eLpNorm (χ•R) ≤ RHalf`.
  -- `eLpNorm E 2 = (∫⁻ ‖E‖²)^{1/2}`, for any `E`.
  have heLp_sq : ∀ (E : ℂ → ℂ), eLpNorm E 2 volume
      = (∫⁻ z, ‖E z‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    intro E
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top,
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
  -- Helper: `(K² · J)^{1/2} = ofReal K · J^{1/2}` for `K ≥ 0`.
  have hsqrt_const : ∀ (K : ℝ) (J : ℝ≥0∞), 0 ≤ K →
      ((ENNReal.ofReal K) ^ (2 : ℝ) * J) ^ (1 / (2 : ℝ))
        = ENNReal.ofReal K * J ^ (1 / (2 : ℝ)) := by
    intro K J hK
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
      ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  have hcomm_eLp : ∀ (E : ℂ → ℂ),
      (∀ᵐ z, ‖E z‖ₑ ≤ B2.indicator (fun z => ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z) →
      eLpNorm E 2 volume ≤ ENNReal.ofReal (Cχ / r) * oscHalf := by
    intro E hpt
    rw [heLp_sq, hoscHalf_def, ← hsqrt_const (Cχ / r) _ hCr0]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ z, ‖E z‖ₑ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ z, (B2.indicator (fun z => ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z) ^ (2 : ℝ)
            ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with z hz
          exact ENNReal.rpow_le_rpow hz (by norm_num)
      _ = ∫⁻ z in B2, (ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) ^ (2 : ℝ) ∂volume := by
          rw [← lintegral_indicator hB2meas]
          refine lintegral_congr (fun z => ?_)
          by_cases hz : z ∈ B2
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
            rw [ENNReal.zero_rpow_of_pos (by norm_num)]
      _ = (ENNReal.ofReal (Cχ / r)) ^ (2 : ℝ)
            * ∫⁻ z in B2, ‖F z - c‖ₑ ^ (2 : ℝ) ∂volume := by
          rw [← lintegral_const_mul' _ _ (by
            exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
          refine lintegral_congr (fun z => ?_)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  have hχR_eLp : eLpNorm (fun z => χ z • R z) 2 volume ≤ RHalf := by
    rw [heLp_sq, hRHalf_def]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ z, ‖χ z • R z‖ₑ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ z, (B2.indicator (fun z => ‖R z‖ₑ) z) ^ (2 : ℝ) ∂volume := by
          refine lintegral_mono (fun z => ?_)
          exact ENNReal.rpow_le_rpow (hχR_pt z) (by norm_num)
      _ = ∫⁻ z in B2, ‖R z‖ₑ ^ (2 : ℝ) ∂volume := by
          rw [← lintegral_indicator hB2meas]
          refine lintegral_congr (fun z => ?_)
          by_cases hz : z ∈ B2
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
              ENNReal.zero_rpow_of_pos (by norm_num)]
  -- `eLpNorm (χ•(μG)) ≤ ofReal M · eLpNorm (χ•G)`.
  have hχμG_eLp : eLpNorm (fun z => χ z • (μ z * G z)) 2 volume
      ≤ ENNReal.ofReal M * eLpNorm (fun z => χ z • G z) 2 volume := by
    rw [heLp_sq, heLp_sq, ← hsqrt_const M _ hM0]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← lintegral_const_mul' _ _ (by
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
    refine lintegral_mono_ae ?_
    filter_upwards [hμae] with z hz
    rw [Complex.real_smul, Complex.real_smul, enorm_mul, enorm_mul,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (ENNReal.ofReal M) ^ (2 : ℝ) * (‖((χ z : ℝ) : ℂ)‖ₑ ^ (2:ℝ) * ‖G z‖ₑ ^ (2:ℝ))
        = ‖((χ z : ℝ) : ℂ)‖ₑ ^ (2:ℝ) * ((ENNReal.ofReal M) ^ (2:ℝ) * ‖G z‖ₑ ^ (2:ℝ)) from by
      ring]
    have hmono : (‖μ z‖ₑ) ^ (2:ℝ) ≤ (ENNReal.ofReal M) ^ (2:ℝ) :=
      ENNReal.rpow_le_rpow hz (by norm_num)
    gcongr
  -- ================================================================
  -- (Absorb) The energy equality + the mass bounds yield `(1-M)·X ≤ Y`.
  -- ================================================================
  set X : ℝ≥0∞ := eLpNorm (fun z => χ z • G z) 2 volume with hX_def
  have hXfin : X ≠ ⊤ := hχG2.eLpNorm_lt_top.ne
  -- AESM facts.
  have hEχ_aesm : AEStronglyMeasurable Eχ volume := hDumem.1.sub hχG2.1
  have hEχbar_aesm : AEStronglyMeasurable Eχbar volume :=
    (hDbarumem.1.sub hχμG2.1).sub hχR2.1
  -- Commutator `L²` bounds.
  have hEχ_le : eLpNorm Eχ 2 volume ≤ ENNReal.ofReal (Cχ / r) * oscHalf :=
    hcomm_eLp Eχ (Filter.Eventually.of_forall hEχ_pt)
  have hEχbar_le : eLpNorm Eχbar 2 volume ≤ ENNReal.ofReal (Cχ / r) * oscHalf :=
    hcomm_eLp Eχbar hEχbar_pt
  -- `X ≤ eLpNorm Du + eLpNorm Eχ`.
  have hX_upper : X ≤ eLpNorm Du 2 volume + eLpNorm Eχ 2 volume := by
    have heq : (fun z => χ z • G z) = fun z => Du z - Eχ z := by
      funext z; rw [hEχ_def]; ring
    rw [hX_def, heq]
    exact eLpNorm_sub_le hDumem.1 hEχ_aesm (by norm_num)
  -- `eLpNorm Dbaru ≤ eLpNorm (χμG) + eLpNorm (χR) + eLpNorm Eχbar`.
  have hDbar_upper : eLpNorm Dbaru 2 volume ≤
      eLpNorm (fun z => χ z • (μ z * G z)) 2 volume
        + eLpNorm (fun z => χ z • R z) 2 volume + eLpNorm Eχbar 2 volume := by
    have heq : Dbaru = fun z => (χ z • (μ z * G z) + χ z • R z) + Eχbar z := by
      funext z; rw [hEχbar_def]; ring
    rw [heq]
    refine le_trans (eLpNorm_add_le (hχμG2.1.add hχR2.1) hEχbar_aesm (by norm_num)) ?_
    gcongr
    exact eLpNorm_add_le hχμG2.1 hχR2.1 (by norm_num)
  -- Combine: `X ≤ ofReal M · X + Y` with `Y = RHalf + 2·ofReal(Cχ/r)·oscHalf`.
  set Y : ℝ≥0∞ := RHalf + 2 * (ENNReal.ofReal (Cχ / r) * oscHalf) with hY_def
  have hself : X ≤ ENNReal.ofReal M * X + Y := by
    calc X ≤ eLpNorm Du 2 volume + eLpNorm Eχ 2 volume := hX_upper
      _ = eLpNorm Dbaru 2 volume + eLpNorm Eχ 2 volume := by rw [hEnergy]
      _ ≤ (eLpNorm (fun z => χ z • (μ z * G z)) 2 volume
            + eLpNorm (fun z => χ z • R z) 2 volume + eLpNorm Eχbar 2 volume)
            + eLpNorm Eχ 2 volume := by gcongr
      _ ≤ (ENNReal.ofReal M * X + RHalf + ENNReal.ofReal (Cχ / r) * oscHalf)
            + ENNReal.ofReal (Cχ / r) * oscHalf := by
          gcongr
      _ = ENNReal.ofReal M * X + Y := by rw [hY_def]; ring
  -- Absorb `ofReal M · X`: `ofReal (1-M) · X ≤ Y`, hence `X ≤ ofReal ((1-M)⁻¹) · Y`.
  have hMabs : ENNReal.ofReal (1 - M) * X ≤ Y := by
    have hsub : X - ENNReal.ofReal M * X ≤ Y := tsub_le_iff_left.mpr hself
    have hfac : ENNReal.ofReal (1 - M) * X = X - ENNReal.ofReal M * X := by
      rw [ENNReal.ofReal_sub _ hM0, ENNReal.ofReal_one, ENNReal.sub_mul (fun _ _ => hXfin),
        one_mul]
    rwa [hfac]
  have h1M_pos : (0 : ℝ) < 1 - M := h1M0
  have hX_le : X ≤ ENNReal.ofReal ((1 - M)⁻¹) * Y := by
    calc X = ENNReal.ofReal ((1 - M)⁻¹) * (ENNReal.ofReal (1 - M) * X) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            inv_mul_cancel₀ h1M_pos.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal ((1 - M)⁻¹) * Y := by gcongr
  -- The gradient half-energy over `B`, dominated by `X` (χ ≡ 1 on `B`).
  set LHShalf : ℝ≥0∞ := (∫⁻ z in B, ‖G z‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hLHShalf_def
  have hLHS_le_X : LHShalf ≤ X := by
    rw [hLHShalf_def, hX_def, eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top,
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc (∫⁻ z in B, ‖G z‖ₑ ^ (2 : ℝ) ∂volume)
        = ∫⁻ z in B, ‖χ z • G z‖ₑ ^ (2 : ℝ) ∂volume := by
          refine setLIntegral_congr_fun hBmeas (fun z hz => ?_)
          have hχz : χ z = 1 := hχB z (by rw [hB_def] at hz; exact hz)
          rw [Complex.real_smul, hχz]; simp
      _ ≤ ∫⁻ z, ‖χ z • G z‖ₑ ^ (2 : ℝ) ∂volume := setLIntegral_le_lintegral _ _
  -- Master half-energy inequality (the commutator-absorbed Caccioppoli).
  have hMaster : LHShalf ≤ ENNReal.ofReal (2 * Cχ / ((1 - M) * r)) * oscHalf
      + ENNReal.ofReal ((1 - M)⁻¹) * RHalf := by
    refine le_trans hLHS_le_X (le_trans hX_le (le_of_eq ?_))
    rw [hY_def, mul_add]
    rw [show ENNReal.ofReal ((1 - M)⁻¹) * (2 * (ENNReal.ofReal (Cχ / r) * oscHalf))
        = ENNReal.ofReal (2 * Cχ / ((1 - M) * r)) * oscHalf from by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
        ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp]
    rw [add_comm]
  -- ================================================================
  -- (Convert) Pass to `⨍⁻`-averages via the planar volume ratio.
  -- ================================================================
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_eq : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hvolB : volume B = ENNReal.ofReal (r ^ 2 * Real.pi) := by
    rw [hB_def, Complex.volume_ball, hpi_eq, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity)]
  have hvolB2 : volume B2 = ENNReal.ofReal (4 * r ^ 2 * Real.pi) := by
    rw [hB2_def, Complex.volume_ball, hpi_eq, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  have hVB_half : (volume B) ^ (1 / (2 : ℝ)) = ENNReal.ofReal (r * Real.sqrt Real.pi) := by
    rw [hvolB, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.mul_rpow (by positivity) hpi0.le, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
  have hvol_ratio : volume B2 = 4 * volume B := by
    rw [hvolB, hvolB2, show (4 : ℝ) * r ^ 2 * Real.pi = (4 : ℝ) * (r ^ 2 * Real.pi) from by ring,
      ENNReal.ofReal_mul (by norm_num), show ENNReal.ofReal 4 = (4 : ℝ≥0∞) from by
        simp [ENNReal.ofReal_ofNat]]
  have hVB2_half : (volume B2) ^ (1 / (2 : ℝ)) = 2 * (volume B) ^ (1 / (2 : ℝ)) := by
    rw [hvol_ratio, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by simp [ENNReal.ofReal_ofNat],
      ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
      show (4 : ℝ) ^ (1 / (2:ℝ)) = 2 from by
        rw [show (4:ℝ) = 2 ^ (2:ℝ) from by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num,
      show ENNReal.ofReal 2 = (2 : ℝ≥0∞) from by simp [ENNReal.ofReal_ofNat]]
  have hVB_half_ne0 : (volume B) ^ (1 / (2 : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
    exact ⟨Or.inl hVolB0, Or.inr (by norm_num)⟩
  have hVB_half_top : (volume B) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVolBtop
  have hVB2_half_ne0 : (volume B2) ^ (1 / (2 : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
    exact ⟨Or.inl hVolB20, Or.inr (by norm_num)⟩
  have hVB2_half_top : (volume B2) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVolB2top
  -- Rewrite the goal's `⨍⁻`-averages as `half / volume^{1/2}` and reduce to `hMaster`.
  simp only [← enorm_eq_nnnorm]
  rw [setLAverage_eq, setLAverage_eq, setLAverage_eq,
    ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
    ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
    ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  rw [← hLHShalf_def, ← hoscHalf_def, ← hRHalf_def]
  rw [ENNReal.div_le_iff hVB_half_ne0 hVB_half_top]
  -- `RHS_goal * (volB)^{1/2}`: cancel the volume ratio (`(volB2)^{1/2} = 2·(volB)^{1/2}`).
  have hofReal_half : ENNReal.ofReal (1 / 2) = (1 : ℝ≥0∞) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (ENNReal.ofReal 1) / (ENNReal.ofReal 2) from by
      simp [ENNReal.ofReal_one, ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_div_of_pos (by norm_num)]
  have hhalf_ratio : (volume B) ^ (1 / (2:ℝ)) / (volume B2) ^ (1 / (2:ℝ))
      = ENNReal.ofReal (1 / 2) := by
    rw [hofReal_half, hVB2_half,
      show (volume B) ^ (1 / (2:ℝ)) / (2 * (volume B) ^ (1 / (2:ℝ)))
        = 1 * (volume B) ^ (1 / (2:ℝ)) / (2 * (volume B) ^ (1 / (2:ℝ))) from by rw [one_mul],
      ENNReal.mul_div_mul_right 1 2 hVB_half_ne0 hVB_half_top]
  have hosc_cancel : oscHalf / (volume B2) ^ (1 / (2 : ℝ)) * (volume B) ^ (1 / (2 : ℝ))
      = ENNReal.ofReal (1 / 2) * oscHalf := by
    rw [ENNReal.mul_comm_div, hhalf_ratio, mul_comm]
  have hR_cancel : RHalf / (volume B2) ^ (1 / (2 : ℝ)) * (volume B) ^ (1 / (2 : ℝ))
      = ENNReal.ofReal (1 / 2) * RHalf := by
    rw [ENNReal.mul_comm_div, hhalf_ratio, mul_comm]
  rw [add_mul, mul_assoc, mul_assoc, hosc_cancel, hR_cancel]
  -- Final term-by-term comparison, both coefficients dominated.
  refine le_trans hMaster (add_le_add ?_ ?_)
  · -- oscHalf coefficient: `2Cχ/((1-M)r) ≤ A/r · (1/2)`.
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ A / r)]
    gcongr
    rw [hA_def,
      show (4 * Cχ + 2) / (1 - M) / r * (1 / 2) = (2 * Cχ + 1) / ((1 - M) * r) from by
        field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hCχ0, h1M_pos, hr]
  · -- RHalf coefficient: `(1-M)⁻¹ ≤ A · (1/2)`.
    rw [← mul_assoc, ← ENNReal.ofReal_mul hA0]
    gcongr
    rw [hA_def,
      show (4 * Cχ + 2) / (1 - M) * (1 / 2) = (2 * Cχ + 1) / (1 - M) from by field_simp; ring,
      inv_eq_one_div]
    rw [div_le_div_iff₀ h1M_pos h1M_pos]
    nlinarith [hCχ0, h1M_pos]


end NoWanderingDomains
