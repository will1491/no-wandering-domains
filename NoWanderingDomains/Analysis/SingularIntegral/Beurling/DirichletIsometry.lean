/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.Kernel

/-!
# The Beurling transform — DirichletIsometry

Supporting linearity lemmas, the Wirtinger/Dirichlet-energy isometry
`dirichlet_energy_isometry`, and the smooth-class `L²` isometry
`beurling_l2_isometry_smooth`.

Part of the `Beurling` development (overview in `Beurling/Kernel.lean`). -/

open MeasureTheory Complex Filter Topology
open scoped Real ENNReal NNReal Convolution InnerProductSpace

namespace NoWanderingDomains

variable {μ : ℂ → ℂ} {z : ℂ} {p : ℝ≥0∞}

/-! ## `Lᵖ` boundedness — supporting lemmas

The three boundedness theorems below rest on a dependency tree rooted at the
`L²` isometry on the smooth dense class (`beurling_l2_isometry_smooth`). The
helpers here build that tree leaf-first. -/

/-- Additivity of the truncated Beurling operator in the function argument. -/
lemma czOperator_beurling_add {f g : ℂ → ℂ} {r : ℝ} {w : ℂ}
    (hf : IntegrableOn (fun y => beurlingKernel w y * f y) (Metric.ball w r)ᶜ volume)
    (hg : IntegrableOn (fun y => beurlingKernel w y * g y) (Metric.ball w r)ᶜ volume) :
    czOperator beurlingKernel r (f + g) w
      = czOperator beurlingKernel r f w + czOperator beurlingKernel r g w := by
  change (∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * (f + g) y)
      = (∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * f y)
        + ∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * g y
  simp only [Pi.add_apply, mul_add]
  exact integral_add hf hg

/-- Homogeneity of the truncated Beurling operator in the function argument. -/
lemma czOperator_beurling_const_smul {f : ℂ → ℂ} {r : ℝ} {w : ℂ} (c : ℂ) :
    czOperator beurlingKernel r (c • f) w = c * czOperator beurlingKernel r f w := by
  change (∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * (c • f) y)
      = c * ∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * f y
  have h1 : (∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * (c • f) y)
      = ∫ y in (Metric.ball w r)ᶜ, c * (beurlingKernel w y * f y) := by
    refine setIntegral_congr_fun measurableSet_ball.compl (fun y _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [h1]
  exact integral_const_mul c _

/-- On the smooth compactly supported class the truncated Beurling integrals
converge as `r → 0⁺` to `-π · beurling μ` — read off the proof of
`beurling_eq_dz_cauchyTransform`, which already exhibits this limit. -/
lemma beurling_ae_tendsto_smooth {ν : ℂ → ℂ} (hν : ContDiff ℝ 1 ν)
    (hνc : HasCompactSupport ν) (w : ℂ) :
    Filter.Tendsto (fun r => czOperator beurlingKernel r ν w) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * beurling ν w)) := by
  have h := czOperator_beurling_tendsto_smooth hν hνc w
  have hval : (∫ ζ, (dz ν ζ) / (ζ - w)) = -(π : ℂ) * beurling ν w := by
    have hlim : limUnder (𝓝[>] (0:ℝ))
        (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν w)
        = (∫ ζ, (dz ν ζ) / (ζ - w)) := by
      apply Filter.Tendsto.limUnder_eq
      have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν w
          = czOperator beurlingKernel r ν w := fun r => rfl
      simpa only [hcz] using h
    have hb : beurling ν w = -(1 / (π : ℂ)) * (∫ ζ, (dz ν ζ) / (ζ - w)) := by
      rw [beurling, hlim]
    rw [hb]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rwa [hval] at h

set_option maxHeartbeats 400000 in
-- The proof inlines, as one local `mult_ae` helper, the whole-plane distributional
-- integration by parts (the `bridge`), the line-derivative Fourier multiplier, and the
-- a.e. extraction against smooth compactly supported test functions; elaborating these
-- many nested `have`s in a single declaration needs extra budget.
open FourierTransform TemperedDistribution SchwartzMap in
open scoped LineDeriv in
/-- **Wirtinger / Dirichlet-energy `L²` isometry.** For two `C¹` `L²` functions
`B` and `N` on `ℂ` whose first directional derivatives all lie in `L²` and which
satisfy the Beltrami-type identity `∂̄B = ∂N` pointwise, the `L²` norms agree:
`‖B‖₂ = ‖N‖₂`.

This is the analytic linchpin of the Beurling `L²` isometry. The proof is the
whole-plane integration by parts identifying the *distributional* line-derivative
of a `C¹` `L²` function with the tempered distribution of its *classical*
directional derivative (boundary terms vanish by `L²` decay against Schwartz test
functions, via `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`), combined
with the modulus-one Fourier multiplier `ξ̄/ξ`: applying
`TemperedDistribution.fourier_lineDerivOp_eq` to `∂̄B = ∂N` turns the identity into
`ξ · 𝓕B = ξ̄ · 𝓕N` a.e., whence `|𝓕B| = |𝓕N|` a.e. and Plancherel
(`Lp.norm_fourier_eq`) gives the claim. -/
lemma dirichlet_energy_isometry {B N : ℂ → ℂ}
    (hB : ContDiff ℝ 1 B) (hN : ContDiff ℝ 1 N)
    (hBL2 : MemLp B 2 volume) (hNL2 : MemLp N 2 volume)
    (hB1L2 : MemLp (fun z => (fderiv ℝ B z) 1) 2 volume)
    (hBIL2 : MemLp (fun z => (fderiv ℝ B z) Complex.I) 2 volume)
    (hN1L2 : MemLp (fun z => (fderiv ℝ N z) 1) 2 volume)
    (hNIL2 : MemLp (fun z => (fderiv ℝ N z) Complex.I) 2 volume)
    (hClairaut : ∀ z, dzbar B z = dz N z) :
    eLpNorm B 2 volume = eLpNorm N 2 volume := by
  -- Local helper: the a.e. Fourier-multiplier identity for one `C¹` `L²` function `g`
  -- and one direction `m`, the combination of the distributional integration by parts
  -- (`bridge`) with the line-derivative Fourier multiplier.
  have mult_ae : ∀ (g : ℂ → ℂ), ContDiff ℝ 1 g → ∀ (hgL2 : MemLp g 2 volume) (m : ℂ)
      (hdgL2 : MemLp (fun z => (fderiv ℝ g z) m) 2 volume),
      (fun ζ => (2 * Real.pi * Complex.I) * ((inner ℝ ζ m : ℝ) : ℂ) *
          (𝓕 (hgL2.toLp g) : Lp ℂ 2 volume) ζ)
        =ᵐ[volume]
          (fun ζ => (𝓕 (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) : Lp ℂ 2 volume) ζ) := by
    intro g hg hgL2 m hdgL2
    -- distributional integration by parts (the bridge)
    have bridge : ∂_{m} (Lp.toTemperedDistribution (hgL2.toLp g))
        = Lp.toTemperedDistribution (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) := by
      ext φ
      rw [lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
        Lp.toTemperedDistribution_apply]
      have hL : ∫ (x : ℂ), (-∂_{m} φ) x • (hgL2.toLp g) x
          = ∫ (x : ℂ), -((fderiv ℝ φ x) m) * g x := by
        apply integral_congr_ae
        filter_upwards [hgL2.coeFn_toLp] with x hx
        rw [hx]; simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
      have hR : ∫ (x : ℂ), φ x • (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) x
          = ∫ (x : ℂ), φ x * (fderiv ℝ g x m) := by
        apply integral_congr_ae
        filter_upwards [hdgL2.coeFn_toLp] with x hx
        rw [hx]; simp [smul_eq_mul]
      rw [hL, hR]
      have hφmem : MemLp (φ : ℂ → ℂ) 2 volume := φ.memLp 2 volume
      have hφ'mem : MemLp (fun x => (fderiv ℝ φ x) m) 2 volume :=
        (∂_{m} φ : 𝓢(ℂ, ℂ)).memLp 2 volume
      have I1 : Integrable (fun x => (fderiv ℝ g x m) * φ x) volume :=
        hdgL2.integrable_mul hφmem
      have I2 : Integrable (fun x => g x * (fderiv ℝ φ x m)) volume :=
        hgL2.integrable_mul hφ'mem
      have I3 : Integrable (fun x => g x * φ x) volume := hgL2.integrable_mul hφmem
      have key : ∫ x, g x * (fderiv ℝ φ x m) = - ∫ x, (fderiv ℝ g x m) * φ x :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable I1 I2 I3
          (fun x _ => hg.differentiable (by norm_num) x) (fun x _ => φ.differentiableAt)
      have hLgoal : ∫ (x : ℂ), -((fderiv ℝ φ x) m) * g x
          = -∫ x, g x * (fderiv ℝ φ x m) := by
        rw [← integral_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only []; rw [neg_mul, mul_comm]
      have hRgoal : ∫ (x : ℂ), φ x * (fderiv ℝ g x m)
          = ∫ x, (fderiv ℝ g x m) * φ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only []; rw [mul_comm (φ x)]
      rw [hLgoal, hRgoal, key, neg_neg]
    -- distributional multiplier identity
    have mult_dist : (2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ)) (𝓕 (Lp.toTemperedDistribution (hgL2.toLp g)))
        = Lp.toTemperedDistribution
            (𝓕 (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) : Lp ℂ 2 volume) := by
      have hf := TemperedDistribution.fourier_lineDerivOp_eq
        (Lp.toTemperedDistribution (hgL2.toLp g)) m
      rw [bridge] at hf
      rw [Lp.fourier_toTemperedDistribution_eq] at hf
      rw [← hf]
    -- distributional identity transported to L²-Fourier on both sides
    have hmd0 : (2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ))
          (Lp.toTemperedDistribution (𝓕 (hgL2.toLp g) : Lp ℂ 2 volume))
        = Lp.toTemperedDistribution
            (𝓕 (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) : Lp ℂ 2 volume) := by
      rw [← Lp.fourier_toTemperedDistribution_eq]
      exact mult_dist
    -- extract the a.e. identity
    set Fg : Lp ℂ 2 volume := 𝓕 (hgL2.toLp g) with hFg
    set Fdg : Lp ℂ 2 volume := 𝓕 (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) with hFdg
    have hcont : Continuous
        (fun ζ : ℂ => (2 * Real.pi * Complex.I) * ((inner ℝ ζ m : ℝ) : ℂ)) := by
      fun_prop
    have hFgli : LocallyIntegrable (fun ζ => Fg ζ) volume :=
      (Lp.memLp Fg).locallyIntegrable (by norm_num)
    have hFdgli : LocallyIntegrable (fun ζ => Fdg ζ) volume :=
      (Lp.memLp Fdg).locallyIntegrable (by norm_num)
    have hfli : LocallyIntegrable
        (fun ζ => (2 * Real.pi * Complex.I) * ((inner ℝ ζ m : ℝ) : ℂ) * Fg ζ) volume := by
      rw [MeasureTheory.locallyIntegrable_iff]
      intro K hK
      have hIK : IntegrableOn (fun ζ => Fg ζ) K volume := hFgli.integrableOn_isCompact hK
      have := hIK.continuousOn_mul (hcont.continuousOn) hK
      simpa [mul_assoc] using this
    refine ae_eq_of_integral_contDiff_smul_eq hfli hFdgli (fun χ hχ hχc => ?_)
    have hmd := hmd0
    have hχcs : HasCompactSupport (fun x => (Complex.ofRealCLM (χ x))) := hχc.comp_left rfl
    have hχsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => (Complex.ofRealCLM (χ x))) :=
      Complex.ofRealCLM.contDiff.comp hχ
    set φ : 𝓢(ℂ, ℂ) := hχcs.toSchwartzMap hχsm with hφ
    have hφval : ∀ x, φ x = ((χ x : ℝ) : ℂ) := fun x => rfl
    have hev := congrArg (fun (D : 𝓢'(ℂ, ℂ)) => D φ) hmd
    have hLHS : ((2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ)) (Lp.toTemperedDistribution Fg)) φ
        = (2 * Real.pi * Complex.I) *
            ∫ ζ, (((inner ℝ ζ m : ℝ) : ℂ) • φ ζ) • Fg ζ := by
      rw [show ((2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ)) (Lp.toTemperedDistribution Fg)) φ
          = (2 * Real.pi * Complex.I) • (TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ)) (Lp.toTemperedDistribution Fg)) φ from rfl]
      rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
      congr 1
      apply integral_congr_ae
      filter_upwards with ζ
      have htg : (fun x => ((inner ℝ x m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
      rw [SchwartzMap.smulLeftCLM_apply_apply htg]
    have hRHS : (Lp.toTemperedDistribution Fdg) φ = ∫ ζ, φ ζ • Fdg ζ :=
      Lp.toTemperedDistribution_apply Fdg φ
    try simp only at hev
    rw [hLHS, hRHS] at hev
    have hLconv : (∫ x, χ x • (2 * Real.pi * Complex.I * ((inner ℝ x m : ℝ) : ℂ) * Fg x))
        = 2 * Real.pi * Complex.I
            * ∫ ζ, (((inner ℝ ζ m : ℝ) : ℂ) • φ ζ) • Fg ζ := by
      rw [show (2 * Real.pi * Complex.I
              * ∫ ζ, (((inner ℝ ζ m : ℝ) : ℂ) • φ ζ) • Fg ζ)
          = ∫ ζ, 2 * Real.pi * Complex.I * ((((inner ℝ ζ m : ℝ) : ℂ) • φ ζ) • Fg ζ)
          from (MeasureTheory.integral_const_mul _ _).symm]
      apply integral_congr_ae
      filter_upwards with ζ
      rw [hφval]
      simp only [Complex.real_smul, smul_eq_mul]
      ring
    have hRconv : (∫ x, χ x • Fdg x) = ∫ ζ, φ ζ • Fdg ζ := by
      apply integral_congr_ae
      filter_upwards with ζ
      rw [hφval, Complex.real_smul, smul_eq_mul]
    exact hLconv.trans (hev.trans hRconv.symm)
  -- ===== final assembly =====
  set FB : Lp ℂ 2 volume := 𝓕 (hBL2.toLp B) with hFB
  set FN : Lp ℂ 2 volume := 𝓕 (hNL2.toLp N) with hFN
  have mB1 := mult_ae B hB hBL2 1 hB1L2
  have mBI := mult_ae B hB hBL2 Complex.I hBIL2
  have mN1 := mult_ae N hN hNL2 1 hN1L2
  have mNI := mult_ae N hN hNL2 Complex.I hNIL2
  have hin1 : ∀ ζ : ℂ, (inner ℝ ζ (1 : ℂ) : ℝ) = ζ.re := by
    intro ζ; rw [Complex.inner]; simp
  have hinI : ∀ ζ : ℂ, (inner ℝ ζ Complex.I : ℝ) = ζ.im := by
    intro ζ; rw [Complex.inner]; simp
  have hLpfn :
      (hB1L2.toLp (fun z => (fderiv ℝ B z) 1)
        + Complex.I • hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I))
      = (hN1L2.toLp (fun z => (fderiv ℝ N z) 1)
        - Complex.I • hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (hB1L2.toLp (fun z => (fderiv ℝ B z) 1))
        (Complex.I • hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I)),
      Lp.coeFn_smul Complex.I (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I)),
      Lp.coeFn_sub (hN1L2.toLp (fun z => (fderiv ℝ N z) 1))
        (Complex.I • hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)),
      Lp.coeFn_smul Complex.I (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)),
      hB1L2.coeFn_toLp, hBIL2.coeFn_toLp, hN1L2.coeFn_toLp, hNIL2.coeFn_toLp]
      with ζ ha hsmB hs hsmN hb1 hbi hn1 hni
    rw [ha, hs]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hsmB, hsmN, hb1, hbi, hn1, hni,
      smul_eq_mul]
    have hcl := hClairaut ζ
    rw [dzbar, dz] at hcl
    linear_combination 2 * hcl
  have hLpeq :
      𝓕 (hB1L2.toLp (fun z => (fderiv ℝ B z) 1))
        + Complex.I • 𝓕 (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I))
      = 𝓕 (hN1L2.toLp (fun z => (fderiv ℝ N z) 1))
        - Complex.I • 𝓕 (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)) := by
    have hap := congrArg (fun (x : Lp ℂ 2 volume) => 𝓕 x) hLpfn
    try simp only at hap
    rw [FourierAdd.fourier_add, FourierSMul.fourier_smul,
      sub_eq_add_neg, ← neg_smul, FourierAdd.fourier_add, FourierSMul.fourier_smul,
      neg_smul, ← sub_eq_add_neg] at hap
    exact hap
  have hLpeq_ae :
      (fun ζ => 𝓕 (hB1L2.toLp (fun z => (fderiv ℝ B z) 1)) ζ
          + Complex.I * 𝓕 (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I)) ζ)
      =ᵐ[volume]
      (fun ζ => 𝓕 (hN1L2.toLp (fun z => (fderiv ℝ N z) 1)) ζ
          - Complex.I * 𝓕 (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)) ζ) := by
    have hc := congrArg (fun (x : Lp ℂ 2 volume) => (x : ℂ → ℂ)) hLpeq
    filter_upwards [Lp.coeFn_add (𝓕 (hB1L2.toLp (fun z => (fderiv ℝ B z) 1)))
        (Complex.I • 𝓕 (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I))),
      Lp.coeFn_smul Complex.I (𝓕 (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I))),
      Lp.coeFn_sub (𝓕 (hN1L2.toLp (fun z => (fderiv ℝ N z) 1)))
        (Complex.I • 𝓕 (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I))),
      Lp.coeFn_smul Complex.I (𝓕 (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)))]
      with ζ ha hsmB hs hsmN
    have := congrFun hc ζ
    try simp only at this
    rw [ha, hs] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hsmB, hsmN, smul_eq_mul] at this
    exact this
  have hmod : (fun ζ => ζ * FB ζ) =ᵐ[volume] (fun ζ => (starRingEnd ℂ) ζ * FN ζ) := by
    filter_upwards [mB1, mBI, mN1, mNI, hLpeq_ae] with ζ hB1 hBI hN1 hNI hcomb
    rw [hin1] at hB1 hN1
    rw [hinI] at hBI hNI
    rw [← hB1, ← hBI, ← hN1, ← hNI] at hcomb
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hre : ζ = (ζ.re : ℂ) + ζ.im * Complex.I := by
      rw [Complex.ext_iff]; simp
    have hconj : (starRingEnd ℂ) ζ = (ζ.re : ℂ) - ζ.im * Complex.I := by
      rw [Complex.ext_iff]; simp
    have hkey : (2 * (Real.pi : ℂ) * Complex.I) * (ζ * FB ζ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((starRingEnd ℂ) ζ * FN ζ) := by
      rw [hconj]
      nth_rewrite 1 [hre]
      linear_combination hcomb
    exact mul_left_cancel₀ hpi hkey
  have habs : (fun ζ => ‖FB ζ‖) =ᵐ[volume] (fun ζ => ‖FN ζ‖) := by
    filter_upwards [hmod, volume.ae_ne (0 : ℂ)] with ζ hm hne
    have h1 : ‖ζ * FB ζ‖ = ‖(starRingEnd ℂ) ζ * FN ζ‖ := by rw [hm]
    rw [norm_mul, norm_mul, RCLike.norm_conj] at h1
    exact mul_left_cancel₀ (by simpa [norm_eq_zero] using hne) h1
  have henorm : (fun ζ => ‖FB ζ‖ₑ) =ᵐ[volume] (fun ζ => ‖FN ζ‖ₑ) := by
    filter_upwards [habs] with ζ h
    simp only [enorm_eq_nnnorm, ← norm_toNNReal]
    rw [h]
  have hnormeq : ‖FB‖ = ‖FN‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_enorm_ae henorm
  rw [hFB, hFN, Lp.norm_fourier_eq, Lp.norm_fourier_eq,
    Lp.norm_toLp B hBL2, Lp.norm_toLp N hNL2] at hnormeq
  have hBfin : eLpNorm B 2 volume ≠ ⊤ := hBL2.2.ne
  have hNfin : eLpNorm N 2 volume ≠ ⊤ := hNL2.2.ne
  exact (ENNReal.toReal_eq_toReal_iff' hBfin hNfin).mp hnormeq

set_option maxHeartbeats 400000 in
-- The proof inlines the smoothness of the Cauchy transform, the integral
-- representation of `beurling ν` off the support, and the differentiation-under-
-- the-integral decay estimates for `beurling ν` and its directional derivatives;
-- elaborating this many nested `have`s in a single declaration needs extra budget.
/-- **`L²` isometry on the smooth dense class** — the analytic core of the whole
milestone. For `μ ∈ C^∞_c`, `‖beurling μ‖₂ = ‖μ‖₂`. On this class
`beurling μ = ∂(Pμ)` (`beurling_eq_dz_cauchyTransform`) and `μ = ∂̄(Pμ)`
(`dzbar_cauchyTransform`), so the statement is the Dirichlet-energy identity
`‖∂F‖₂ = ‖∂̄F‖₂` for `F = Pμ`. -/
lemma beurling_l2_isometry_smooth {ν : ℂ → ℂ} (hν : ContDiff ℝ (⊤ : ℕ∞) ν)
    (hνc : HasCompactSupport ν) :
    eLpNorm (beurling ν) 2 volume = eLpNorm ν 2 volume := by
  have hν1 : ContDiff ℝ 1 ν := hν.of_le (by exact_mod_cast le_top)
  set B : ℂ → ℂ := beurling ν with hBdef
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport ν ⊆ Metric.closedBall (0 : ℂ) R :=
    (hνc.isCompact.isBounded).subset_closedBall 0
  have hClairaut : ∀ z, dzbar B z = dz ν z := by
    rw [hBdef]
    -- F smooth (inlined, abbreviated by reusing the lemma's existing infra via cauchyTransform)
    have hF : ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform ν) := by
      set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
      set k : ℂ → ℂ := fun u => -u⁻¹ with hk
      have hk_loc : LocallyIntegrable k volume := by
        rw [hk]
        apply LocallyIntegrable.neg
        rw [MeasureTheory.locallyIntegrable_iff]
        intro K hK
        obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
        apply MeasureTheory.IntegrableOn.mono_set _ hR₀
        rw [IntegrableOn]
        refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
        rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
          ← Complex.lintegral_comp_polarCoord_symm]
        set box : ℝ × ℝ → ENNReal :=
          (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
        have hbound : ∀ p ∈ polarCoord.target,
            ENNReal.ofReal p.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
              (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p) ≤ box p := by
          intro p hp
          simp only [hbox]
          rw [polarCoord_target, Set.mem_prod] at hp
          obtain ⟨hp1, hp2⟩ := hp
          simp only [Set.mem_Ioi] at hp1
          by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R₀
          · rw [Set.indicator_of_mem hmem]
            have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
              rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
            have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
              rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
            rw [enorm_inv hsymm_ne]
            have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
              rw [← ofReal_norm, hnorm]
            rw [henorm, smul_eq_mul,
              ENNReal.mul_inv_cancel
                (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
                ENNReal.ofReal_lt_top.ne]
            have hpR : p.1 ≤ R₀ := by
              rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
            rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩)]
          · rw [Set.indicator_of_notMem hmem]; simp
        calc
          ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
              (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p)
              ≤ ∫⁻ p in polarCoord.target, box p :=
                setLIntegral_mono (measurable_const.indicator
                  (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
          _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
          _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-π) π) := by
                rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]; simp
          _ < ⊤ := by
                rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
                exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hCT : cauchyTransform ν
          = fun w => (-(1 / (π : ℂ))) • (MeasureTheory.convolution ν k L volume) w := by
        funext w
        rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
        congr 1
        apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
        rw [hL, ContinuousLinearMap.mul_apply']
        change ν ζ / (ζ - w) = ν ζ * -(w - ζ)⁻¹
        have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
        rw [hflip, div_eq_mul_inv]
      rw [hCT]
      exact (hνc.contDiff_convolution_left L hν hk_loc).const_smul _
    -- B = dz F
    have hBeqF : beurling ν = fun z => dz (cauchyTransform ν) z := by
      funext z; exact (beurling_eq_dz_cauchyTransform hν1 hνc z).symm
    -- Clairaut core for F
    intro z
    rw [hBeqF]
    set F := cauchyTransform ν with hFdef
    -- mixed-partial symmetry core
    have hClairautCore : dzbar (fun w => dz F w) z = dz (fun w => dzbar F w) z := by
      set S := fderiv ℝ (fderiv ℝ F) z with hS
      have hfd : ContDiff ℝ (⊤:ℕ∞) (fun w => fderiv ℝ F w) := hF.fderiv_right (by simp)
      have hf'diff : Differentiable ℝ (fun w => fderiv ℝ F w) := hfd.differentiable (by simp)
      have hsymm : ∀ v w : ℂ, (S v) w = (S w) v := by
        have hsymF : IsSymmSndFDerivAt ℝ F z := by
          apply (hF.contDiffAt).isSymmSndFDerivAt
          rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top
        intro v w; exact hsymF.eq v w
      have hdzF : ∀ m' : ℂ, (fderiv ℝ (fun w => dz F w) z) m'
          = (1/2 : ℂ) * ((S m') 1 - Complex.I * (S m') Complex.I) := by
        intro m'
        have hd1 : HasFDerivAt (fun w => (fderiv ℝ F w) (1:ℂ))
            ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).comp S) z := by
          rw [hS]
          exact (ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).hasFDerivAt.comp z (hf'diff z).hasFDerivAt
        have hdI : HasFDerivAt (fun w => (fderiv ℝ F w) Complex.I)
            ((ContinuousLinearMap.apply ℝ ℂ Complex.I).comp S) z := by
          rw [hS]
          exact (ContinuousLinearMap.apply ℝ ℂ Complex.I).hasFDerivAt.comp z (hf'diff z).hasFDerivAt
        have hcomb : HasFDerivAt (fun w => dz F w)
            ((1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).comp S
              - Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I).comp S)) z :=
          (hd1.sub (hdI.const_smul Complex.I)).const_smul (1/2 : ℂ)
        rw [hcomb.fderiv]
        simp only [smul_apply, sub_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
      have hdzbarF : ∀ m' : ℂ, (fderiv ℝ (fun w => dzbar F w) z) m'
          = (1/2 : ℂ) * ((S m') 1 + Complex.I * (S m') Complex.I) := by
        intro m'
        have hd1 : HasFDerivAt (fun w => (fderiv ℝ F w) (1:ℂ))
            ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).comp S) z := by
          rw [hS]
          exact (ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).hasFDerivAt.comp z (hf'diff z).hasFDerivAt
        have hdI : HasFDerivAt (fun w => (fderiv ℝ F w) Complex.I)
            ((ContinuousLinearMap.apply ℝ ℂ Complex.I).comp S) z := by
          rw [hS]
          exact (ContinuousLinearMap.apply ℝ ℂ Complex.I).hasFDerivAt.comp z (hf'diff z).hasFDerivAt
        have hcomb : HasFDerivAt (fun w => dzbar F w)
            ((1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).comp S
              + Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I).comp S)) z :=
          (hd1.add (hdI.const_smul Complex.I)).const_smul (1/2 : ℂ)
        rw [hcomb.fderiv]
        simp only [smul_apply, add_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
      rw [dzbar, dz, hdzF 1, hdzF Complex.I, hdzbarF 1, hdzbarF Complex.I]
      rw [hsymm Complex.I 1, hsymm 1 Complex.I]
      ring
    -- dzbar F = ν as functions
    have hdzbarF_eq : (fun w => dzbar F w) = ν := by
      funext w; rw [hFdef]; exact dzbar_cauchyTransform hν1 hνc w
    rw [hClairautCore, hdzbarF_eq]
  have hB : ContDiff ℝ 1 B := by
    rw [hBdef]
    -- F = cauchyTransform ν is C^∞
    have hF : ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform ν) := by
      set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
      set k : ℂ → ℂ := fun u => -u⁻¹ with hk
      have hk_loc : LocallyIntegrable k volume := by
        rw [hk]
        apply LocallyIntegrable.neg
        rw [MeasureTheory.locallyIntegrable_iff]
        intro K hK
        obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
        apply MeasureTheory.IntegrableOn.mono_set _ hR₀
        rw [IntegrableOn]
        refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
        rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
          ← Complex.lintegral_comp_polarCoord_symm]
        set lhs : ℝ × ℝ → ENNReal := fun p =>
          ENNReal.ofReal p.1 •
            (Metric.closedBall (0 : ℂ) R₀).indicator (fun u : ℂ => ‖u⁻¹‖ₑ)
              (Complex.polarCoord.symm p)
          with hlhs
        set box : ℝ × ℝ → ENNReal :=
          (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
        have hbound : ∀ p ∈ polarCoord.target, lhs p ≤ box p := by
          intro p hp
          simp only [hlhs, hbox]
          rw [polarCoord_target, Set.mem_prod] at hp
          obtain ⟨hp1, hp2⟩ := hp
          simp only [Set.mem_Ioi] at hp1
          by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R₀
          · rw [Set.indicator_of_mem hmem]
            have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
              rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
            have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
              rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
            rw [enorm_inv hsymm_ne]
            have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
              rw [← ofReal_norm, hnorm]
            rw [henorm, smul_eq_mul,
              ENNReal.mul_inv_cancel
                (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
                ENNReal.ofReal_lt_top.ne]
            have hpR : p.1 ≤ R₀ := by
              rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
            rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩)]
          · rw [Set.indicator_of_notMem hmem]; simp
        calc
          ∫⁻ p in polarCoord.target, lhs p
              ≤ ∫⁻ p in polarCoord.target, box p :=
                setLIntegral_mono (measurable_const.indicator
                  (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
          _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
          _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-π) π) := by
                rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]; simp
          _ < ⊤ := by
                rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
                exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hCT : cauchyTransform ν
          = fun w => (-(1 / (π : ℂ))) • (MeasureTheory.convolution ν k L volume) w := by
        funext w
        rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
        congr 1
        apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
        rw [hL, ContinuousLinearMap.mul_apply']
        change ν ζ / (ζ - w) = ν ζ * -(w - ζ)⁻¹
        have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
        rw [hflip, div_eq_mul_inv]
      rw [hCT]
      exact (hνc.contDiff_convolution_left L hν hk_loc).const_smul _
    -- B = dz F
    have hBeqF : beurling ν = fun z => dz (cauchyTransform ν) z := by
      funext z; exact (beurling_eq_dz_cauchyTransform hν1 hνc z).symm
    rw [hBeqF]
    -- dz F is C^1
    apply ContDiff.of_le _ (by exact_mod_cast le_top : (1:WithTop ℕ∞) ≤ (⊤:ℕ∞))
    have hfd : ContDiff ℝ (⊤:ℕ∞) (fun w => fderiv ℝ (cauchyTransform ν) w) :=
      hF.fderiv_right (by simp)
    have h1 : ContDiff ℝ (⊤:ℕ∞) (fun w => (fderiv ℝ (cauchyTransform ν) w) (1:ℂ)) :=
      hfd.clm_apply contDiff_const
    have hI : ContDiff ℝ (⊤:ℕ∞) (fun w => (fderiv ℝ (cauchyTransform ν) w) Complex.I) :=
      hfd.clm_apply contDiff_const
    have heq : (fun z => dz (cauchyTransform ν) z)
        = fun z => (1/2:ℂ) * ((fderiv ℝ (cauchyTransform ν) z) 1
          - Complex.I * (fderiv ℝ (cauchyTransform ν) z) Complex.I) := by
      funext z; rw [dz]
    rw [heq]
    exact (contDiff_const.mul (h1.sub (contDiff_const.mul hI)))
  have hNL2 : MemLp ν 2 volume := hν1.continuous.memLp_of_hasCompactSupport hνc
  have hderivMemLp : ∀ (f : ℂ → ℂ), ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ m : ℂ, MemLp (fun z => (fderiv ℝ f z) m) 2 volume := by
    intro f hf hfc m
    have hcont : Continuous (fun z => (fderiv ℝ f z) m) :=
      (hf.continuous_fderiv (n := 1) one_ne_zero).clm_apply continuous_const
    have hcs : HasCompactSupport (fun z => (fderiv ℝ f z) m) := by
      have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ f ζ) := hfc.fderiv (𝕜 := ℝ)
      have heq : (fun z => (fderiv ℝ f z) m)
          = (fun D : ℂ →L[ℝ] ℂ => D m) ∘ (fun ζ => fderiv ℝ f ζ) := rfl
      rw [heq]; exact hfderiv_cs.comp_left (by simp)
    exact hcont.memLp_of_hasCompactSupport hcs
  have hN1L2 : MemLp (fun z => (fderiv ℝ ν z) 1) 2 volume := hderivMemLp ν hν1 hνc 1
  have hNIL2 : MemLp (fun z => (fderiv ℝ ν z) Complex.I) 2 volume :=
    hderivMemLp ν hν1 hνc Complex.I
  have hBL2 : MemLp B 2 volume := by
    rw [hBdef]
    -- nonneg radius
    set R' : ℝ := max R 0 with hR'def
    have hR'nn : 0 ≤ R' := le_max_right _ _
    have hR' : tsupport ν ⊆ Metric.closedBall (0 : ℂ) R' :=
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    -- M = sup ‖ν‖
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ, ‖ν ζ‖ ≤ M := hνc.exists_bound_of_continuous hν1.continuous
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    -- integral representation for ‖z‖ > R' + 1
    have Hrepr : ∀ z : ℂ, R' + 1 < ‖z‖ →
        beurling ν z = -(1/(π:ℂ)) * ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
      intro z hz
      have hvanr : ∀ r : ℝ, r ≤ 1 → ∀ y ∈ Metric.ball z r, ν y = 0 := by
        intro r hr y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hy
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h1 := hR' hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        have h2 : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := norm_le_insert y z
        have h3 : ‖y - z‖ < 1 := lt_of_lt_of_le hy hr
        linarith
      have hcont : Continuous (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        rw [← continuousOn_univ]
        apply ContinuousOn.mono (s := {y | y ≠ z} ∪ Metric.ball z 1) _ (by
          intro y _; by_cases h : y = z
          · right; rw [h]; simp [Metric.mem_ball]
          · left; exact h)
        apply ContinuousOn.union_of_isOpen _ _ isOpen_ne Metric.isOpen_ball
        · apply ContinuousOn.mul _ hν1.continuous.continuousOn
          apply ContinuousOn.zpow₀ (by fun_prop)
          intro y hy; left; rw [sub_ne_zero]; exact fun h => hy h.symm
        · have hg : ContinuousOn (fun _ : ℂ => (0:ℂ)) (Metric.ball z 1) := continuousOn_const
          refine hg.congr ?_
          intro y hy
          change (z - y) ^ (-2:ℤ) * ν y = 0
          rw [hvanr 1 le_rfl y hy, mul_zero]
      have hcs : HasCompactSupport (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        have heq : (fun y => (z - y) ^ (-2:ℤ) * ν y) = (fun y => (z - y) ^ (-2:ℤ)) * ν := rfl
        rw [heq]; exact hνc.mul_left
      have hint : Integrable (fun y => (z - y) ^ (-2:ℤ) * ν y) volume :=
        hcont.integrable_of_hasCompactSupport hcs
      have hcz : ∀ r : ℝ, r ≤ 1 →
          czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z = ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
        intro r hr
        rw [czOperator]
        have hfull : (∫ y, (z - y) ^ (-2 : ℤ) * ν y)
            = (∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y)
              + ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * ν y := by
          rw [← setIntegral_univ (μ := volume), ← Set.union_compl_self (Metric.ball z r),
            setIntegral_union disjoint_compl_right measurableSet_ball.compl
              hint.integrableOn hint.integrableOn]
        have hzero : ∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y = 0 := by
          rw [setIntegral_eq_zero_of_forall_eq_zero]
          intro y hy; rw [hvanr r hr y hy, mul_zero]
        rw [hfull, hzero, zero_add]
      rw [beurling]
      congr 1
      apply Filter.Tendsto.limUnder_eq
      have hev : (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z)
          =ᶠ[𝓝[>] (0:ℝ)] (fun _ => ∫ y, (z - y) ^ (-2 : ℤ) * ν y) := by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with r hr
        exact hcz r (le_of_lt hr.2)
      exact Tendsto.congr' hev.symm tendsto_const_nhds
    -- decay bound: ‖B z‖ ≤ Cb / ‖z‖² for ‖z‖ > 2R'+2
    set Cb : ℝ := M * (volume (Metric.closedBall (0:ℂ) R')).toReal / π * 4 with hCb
    have hCbnn : 0 ≤ Cb := by
      rw [hCb]; positivity
    have hdecay : ∀ z : ℂ, (2*R'+2) < ‖z‖ → ‖beurling ν z‖ ≤ Cb / ‖z‖^2 := by
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hhalf : ‖z‖ / 2 ≤ ‖z‖ - R' := by linarith
      have hsupp : ∀ y ∉ Metric.closedBall (0:ℂ) R', (z - y) ^ (-2:ℤ) * ν y = 0 := by
        intro y hy; rw [image_eq_zero_of_notMem_tsupport (fun hmem => hy (hR' hmem)), mul_zero]
      have hinteq : (∫ y, (z - y) ^ (-2 : ℤ) * ν y)
          = ∫ y in Metric.closedBall (0:ℂ) R', (z - y) ^ (-2 : ℤ) * ν y :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
      set Cval : ℝ := M * (‖z‖/2)⁻¹^2 with hCval
      have hbd : ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖(z - y) ^ (-2:ℤ) * ν y‖ ≤ Cval := by
        intro y hy
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        rw [norm_mul]
        have hzy : ‖z‖ / 2 ≤ ‖z - y‖ := by
          have : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
          linarith
        have hzhalfpos : (0:ℝ) < ‖z‖/2 := by positivity
        have hkn : ‖(z - y) ^ (-2:ℤ)‖ = ‖z - y‖⁻¹^2 := by
          rw [norm_zpow, zpow_neg, zpow_two, mul_inv, ← pow_two]
        rw [hkn, hCval]
        have h1 : ‖z - y‖⁻¹^2 ≤ (‖z‖/2)⁻¹^2 := by gcongr
        calc ‖z - y‖⁻¹^2 * ‖ν y‖
            ≤ (‖z‖/2)⁻¹^2 * M := mul_le_mul h1 (hM y) (norm_nonneg _) (by positivity)
          _ = M * (‖z‖/2)⁻¹^2 := by ring
      rw [Hrepr z (by linarith), norm_mul, hinteq]
      have hballfin : volume (Metric.closedBall (0:ℂ) R') < ⊤ := by
        rw [Complex.volume_closedBall]; finiteness
      have hib := norm_setIntegral_le_of_norm_le_const hballfin hbd
      have hnormconst : ‖-(1/(π:ℂ))‖ = 1/π := by
        rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hnormconst]
      have hπpos : 0 < π := Real.pi_pos
      have hvolnn : 0 ≤ (volume (Metric.closedBall (0:ℂ) R')).toReal := ENNReal.toReal_nonneg
      calc (1/π) * ‖∫ y in Metric.closedBall (0:ℂ) R', (z - y) ^ (-2 : ℤ) * ν y‖
          ≤ (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal) :=
            mul_le_mul_of_nonneg_left hib (by positivity)
        _ ≤ Cb / ‖z‖^2 := by
            rw [hCval, hCb]
            have he : (‖z‖/2)⁻¹^2 = 4 / ‖z‖^2 := by rw [inv_div, div_pow]; norm_num
            rw [he]
            have hzne : ‖z‖ ≠ 0 := ne_of_gt hzpos
            have hπne : π ≠ 0 := ne_of_gt hπpos
            apply le_of_eq
            field_simp
    -- apply MemLp decay helper
    have hcont : Continuous (beurling ν) := hB.continuous
    have haesm : AEStronglyMeasurable (beurling ν) volume := hcont.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm haesm]
    set R'' : ℝ := 2*R'+2 with hR''def
    have hR''pos : 0 < R'' := by rw [hR''def]; positivity
    have hball : IntegrableOn (fun z => ‖beurling ν z‖^2) (Metric.closedBall (0:ℂ) R'') volume :=
      (hcont.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 R'')
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (Cb / p.1^2)^2)) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      apply Measurable.pow_const
      exact measurable_const.div (measurable_fst.pow_const 2)
    have hcompl : IntegrableOn (fun z => ‖beurling ν z‖^2)
        (Metric.closedBall (0:ℂ) R'')ᶜ volume := by
      refine ⟨((hcont.norm.pow 2).aestronglyMeasurable).restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hpt : ∀ z ∈ (Metric.closedBall (0:ℂ) R'')ᶜ,
          ‖(‖beurling ν z‖^2 : ℝ)‖ₑ ≤ ENNReal.ofReal ((Cb / ‖z‖^2)^2) := by
        intro z hz
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hb := hdecay z hz
        have hnn : 0 ≤ ‖beurling ν z‖ := norm_nonneg _
        nlinarith [hb, hnn]
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_closedBall.compl hpt) ?_
      rw [← lintegral_indicator measurableSet_closedBall.compl]
      rw [← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ioi R'' ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * (Cb / p.1^2)^2)) p with hbox
      have hbound : ∀ p ∈ polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
            (fun z => ENNReal.ofReal ((Cb / ‖z‖^2)^2)) (Complex.polarCoord.symm p) ≤ box p := by
        intro p hp
        rw [polarCoord_target, Set.mem_prod] at hp
        obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        by_cases hmem : Complex.polarCoord.symm p ∈ (Metric.closedBall (0:ℂ) R'')ᶜ
        · rw [Set.indicator_of_mem hmem]
          have hpR : R'' < p.1 := by
            rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, hnorm, not_le] at hmem
            exact hmem
          rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hpR, hp2⟩)]
          rw [hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]
          exact zero_le
      have hboxmeas : Measurable box :=
        hmeas_polar.indicator (measurableSet_Ioi.prod measurableSet_Ioo)
      calc
        ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
              (fun z => ENNReal.ofReal ((Cb / ‖z‖^2)^2)) (Complex.polarCoord.symm p)
            ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hboxmeas hbound
        _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
        _ = ∫⁻ p in (Set.Ioi R'' ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (p.1 * (Cb / p.1^2)^2) := by
              rw [hbox, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ]
              rw [setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint : IntegrableOn (fun r : ℝ => r * (Cb / r^2)^2) (Set.Ioi R'') volume := by
                have heq : (fun r : ℝ => r * (Cb / r^2)^2) =ᶠ[ae (volume.restrict (Set.Ioi R''))]
                    (fun r : ℝ => Cb^2 * r^(-3 : ℝ)) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
                  simp only [Set.mem_Ioi] at hr
                  have hrpos : 0 < r := lt_trans hR''pos hr
                  have hrne : r ≠ 0 := ne_of_gt hrpos
                  rw [Real.rpow_neg hrpos.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
                  field_simp
                rw [integrableOn_congr_fun_ae heq]
                apply Integrable.const_mul
                rw [← IntegrableOn, integrableOn_Ioi_rpow_iff hR''pos]
                norm_num
              have hfin := hint.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun x hx => ?_)) hfin
              · apply Measurable.enorm
                apply Measurable.mul measurable_id
                apply Measurable.pow_const
                exact measurable_const.div (measurable_id.pow_const 2)
              · simp only [Set.mem_Ioi] at hx
                have hxpos : 0 < x := lt_trans hR''pos hx
                rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hball.union hcompl
    rw [Set.union_compl_self, integrableOn_univ] at this
    exact this
  have hB1L2 : MemLp (fun z => (fderiv ℝ B z) 1) 2 volume := by
    rw [hBdef]
    suffices h : ∀ m : ℂ, MemLp (fun z => (fderiv ℝ (beurling ν) z) m) 2 volume from h 1
    intro m
    set R' : ℝ := max R 0 with hR'def
    have hR'nn : 0 ≤ R' := le_max_right _ _
    have hR' : tsupport ν ⊆ Metric.closedBall (0 : ℂ) R' :=
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ, ‖ν ζ‖ ≤ M := hνc.exists_bound_of_continuous hν1.continuous
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    -- representation (as in hBL2)
    have Hrepr : ∀ z : ℂ, R' + 1 < ‖z‖ →
        beurling ν z = -(1/(π:ℂ)) * ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
      intro z hz
      have hvanr : ∀ r : ℝ, r ≤ 1 → ∀ y ∈ Metric.ball z r, ν y = 0 := by
        intro r hr y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hy
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h1 := hR' hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        have h2 : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := norm_le_insert y z
        have h3 : ‖y - z‖ < 1 := lt_of_lt_of_le hy hr
        linarith
      have hcont : Continuous (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        rw [← continuousOn_univ]
        apply ContinuousOn.mono (s := {y | y ≠ z} ∪ Metric.ball z 1) _ (by
          intro y _; by_cases h : y = z
          · right; rw [h]; simp [Metric.mem_ball]
          · left; exact h)
        apply ContinuousOn.union_of_isOpen _ _ isOpen_ne Metric.isOpen_ball
        · apply ContinuousOn.mul _ hν1.continuous.continuousOn
          apply ContinuousOn.zpow₀ (by fun_prop)
          intro y hy; left; rw [sub_ne_zero]; exact fun h => hy h.symm
        · have hg : ContinuousOn (fun _ : ℂ => (0:ℂ)) (Metric.ball z 1) := continuousOn_const
          refine hg.congr ?_
          intro y hy
          change (z - y) ^ (-2:ℤ) * ν y = 0
          rw [hvanr 1 le_rfl y hy, mul_zero]
      have hcs : HasCompactSupport (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        have heq : (fun y => (z - y) ^ (-2:ℤ) * ν y) = (fun y => (z - y) ^ (-2:ℤ)) * ν := rfl
        rw [heq]; exact hνc.mul_left
      have hint : Integrable (fun y => (z - y) ^ (-2:ℤ) * ν y) volume :=
        hcont.integrable_of_hasCompactSupport hcs
      have hcz : ∀ r : ℝ, r ≤ 1 →
          czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z = ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
        intro r hr
        rw [czOperator]
        have hfull : (∫ y, (z - y) ^ (-2 : ℤ) * ν y)
            = (∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y)
              + ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * ν y := by
          rw [← setIntegral_univ (μ := volume), ← Set.union_compl_self (Metric.ball z r),
            setIntegral_union disjoint_compl_right measurableSet_ball.compl
              hint.integrableOn hint.integrableOn]
        have hzero : ∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y = 0 := by
          rw [setIntegral_eq_zero_of_forall_eq_zero]
          intro y hy; rw [hvanr r hr y hy, mul_zero]
        rw [hfull, hzero, zero_add]
      rw [beurling]
      congr 1
      apply Filter.Tendsto.limUnder_eq
      have hev : (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z)
          =ᶠ[𝓝[>] (0:ℝ)] (fun _ => ∫ y, (z - y) ^ (-2 : ℤ) * ν y) := by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with r hr
        exact hcz r (le_of_lt hr.2)
      exact Tendsto.congr' hev.symm tendsto_const_nhds
    -- DUI: HasFDerivAt of parametric integral over ball
    have hG : ∀ w : ℂ, 2 * R' + 3 < ‖w‖ → HasFDerivAt
        (fun u => ∫ y in Metric.closedBall (0:ℂ) R', (u - y) ^ (-2 : ℤ) * ν y)
        (∫ y in Metric.closedBall (0:ℂ) R',
          ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ))) w := by
      intro z hz
      set Fp' : ℂ → ℂ → (ℂ →L[ℝ] ℂ) := fun w y =>
        (((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ) with hFp'
      set s : Set ℂ := Metric.ball z 1 with hs_def
      set bnd : ℝ := 2 * (‖z‖ - R' - 1)⁻¹^3 * M with hbnd
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hbdpos : 0 < ‖z‖ - R' - 1 := by linarith
      have hgeo : ∀ w ∈ s, ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖z‖ - R' - 1 ≤ ‖w - y‖ := by
        intro w hw y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hw
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        have h1 : ‖w - y‖ ≥ ‖z - y‖ - ‖z - w‖ := by
          have := norm_sub_norm_le (z - y) (z - w)
          have heq : (z - y) - (z - w) = w - y := by ring
          rw [heq] at this; linarith
        have h2 : ‖z - y‖ ≥ ‖z‖ - ‖y‖ := norm_sub_norm_le z y
        have h3 : ‖z - w‖ < 1 := by rw [norm_sub_rev]; exact hw
        linarith
      have hne : ∀ w ∈ s, ∀ y ∈ Metric.closedBall (0:ℂ) R', w ≠ y := by
        intro w hw y hy h
        have := hgeo w hw y hy; rw [h, sub_self, norm_zero] at this; linarith
      have hcontFp : ∀ w ∈ s, ContinuousOn (fun y => (w - y)^(-2:ℤ) * ν y)
          (Metric.closedBall (0:ℂ) R') := by
        intro w hw
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne w hw y hy
      have hFp'_cont : ContinuousOn (fun y => Fp' z y) (Metric.closedBall (0:ℂ) R') := by
        rw [hFp']
        apply ContinuousOn.fun_smul _ continuousOn_const
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne z (Metric.mem_ball_self (by norm_num)) y hy
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => bnd)
        (F' := Fp') (s := s) (Metric.ball_mem_nhds z (by norm_num))
      · filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0:ℝ) < 1)] with w hw
        exact (hcontFp w hw).aestronglyMeasurable measurableSet_closedBall
      · exact (hcontFp z (Metric.mem_ball_self (by norm_num))).integrableOn_compact
          (isCompact_closedBall 0 R')
      · exact hFp'_cont.aestronglyMeasurable measurableSet_closedBall
      · rw [ae_restrict_iff' measurableSet_closedBall]
        apply ae_of_all
        intro y hy w hw
        rw [hFp', hbnd]
        rw [norm_smul]
        have h1norm : ‖(1 : ℂ →L[ℝ] ℂ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        have hwy : ‖z‖ - R' - 1 ≤ ‖w - y‖ := hgeo w hw y hy
        have hwypos : 0 < ‖w - y‖ := lt_of_lt_of_le hbdpos hwy
        have hknorm : ‖((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y‖
            ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by
          rw [norm_mul, norm_mul]
          have hk1 : ‖((-2:ℤ):ℂ)‖ = 2 := by norm_num
          have hk2 : ‖(w - y) ^ ((-2:ℤ) - 1)‖ = ‖w - y‖⁻¹^3 := by
            rw [norm_zpow, show ((-2:ℤ) - 1) = (-3:ℤ) by ring, zpow_neg,
              show ((3:ℤ)) = ((3:ℕ):ℤ) by norm_num, zpow_natCast, inv_pow]
          rw [hk1, hk2]
          have hmono : ‖w - y‖⁻¹^3 ≤ (‖z‖ - R' - 1)⁻¹^3 := by gcongr
          have h2 : (0:ℝ) ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 := by positivity
          exact mul_le_mul (by apply mul_le_mul_of_nonneg_left hmono (by norm_num)) (hM y)
            (norm_nonneg _) h2
        have hbndnn : (0:ℝ) ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by positivity
        calc ‖((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖
            ≤ (2 * (‖z‖ - R' - 1)⁻¹^3 * M) * 1 :=
              mul_le_mul hknorm h1norm (norm_nonneg _) hbndnn
          _ = 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by ring
      · exact integrableOn_const (by rw [Complex.volume_closedBall]; finiteness) (by finiteness)
      · rw [ae_restrict_iff' measurableSet_closedBall]
        apply ae_of_all
        intro y hy w hw
        change HasFDerivAt (fun u => (u - y) ^ (-2:ℤ) * ν y) (Fp' w y) w
        have hsub : HasFDerivAt (fun u : ℂ => u - y) (1 : ℂ →L[ℝ] ℂ) w := by
          exact hasFDerivAt_sub_const y
        have hzpw : HasFDerivAt (fun u : ℂ => (u - y) ^ (-2:ℤ))
            ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1)) • (1 : ℂ →L[ℝ] ℂ)) w := by
          have hc := (hasDerivAt_zpow (-2 : ℤ) (w - y)
            (Or.inl (sub_ne_zero.mpr (hne w hw y hy)))).comp_hasFDerivAt w hsub
          exact hc
        have hmul := hzpw.mul_const (ν y)
        rw [hFp']
        change HasFDerivAt (fun u => (u - y) ^ (-2:ℤ) * ν y)
          ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)) w
        have heq : (((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)
            = (ν y) • ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1)) • (1 : ℂ →L[ℝ] ℂ)) := by
          rw [smul_smul]; ring_nf
        rw [heq]; exact hmul
    -- derivative decay bound: ‖fderiv B z m‖ ≤ Cd / ‖z‖²  for ‖z‖ > 2R'+4
    set Cd : ℝ := 16 * (volume (Metric.closedBall (0:ℂ) R')).toReal * M * ‖m‖ / π with hCd
    have hCdnn : 0 ≤ Cd := by rw [hCd]; positivity
    have hdecay : ∀ z : ℂ, (2*R'+4) < ‖z‖ → ‖(fderiv ℝ (beurling ν) z) m‖ ≤ Cd / ‖z‖^2 := by
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hsuppeq : ∀ w : ℂ, R' + 1 < ‖w‖ →
          (∫ y, (w - y) ^ (-2 : ℤ) * ν y)
            = ∫ y in Metric.closedBall (0:ℂ) R', (w - y) ^ (-2 : ℤ) * ν y := by
        intro w hw
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
        intro y hy; rw [image_eq_zero_of_notMem_tsupport (fun hmem => hy (hR' hmem)), mul_zero]
      have hBeq : (beurling ν) =ᶠ[nhds z]
          fun w => -(1/(π:ℂ)) * ∫ y in Metric.closedBall (0:ℂ) R', (w - y) ^ (-2 : ℤ) * ν y := by
        have hopen : {w : ℂ | 2 * R' + 4 < ‖w‖} ∈ nhds z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hz
        filter_upwards [hopen] with w hw
        rw [Hrepr w (by linarith), hsuppeq w (by linarith)]
      have hGz := hG z (by linarith)
      have hBfd : HasFDerivAt (beurling ν)
          ((-(1/(π:ℂ))) • (∫ y in Metric.closedBall (0:ℂ) R',
              ((((-2 : ℤ):ℂ) * (z - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)))) z := by
        apply HasFDerivAt.congr_of_eventuallyEq _ hBeq
        exact hGz.const_smul (-(1/(π:ℂ)))
      rw [hBfd.fderiv]
      have hbdpos : 0 < ‖z‖ - R' := by linarith [hz]
      have hne : ∀ y ∈ Metric.closedBall (0:ℂ) R', z ≠ y := by
        intro y hy h
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        rw [h] at hz; linarith
      set Fp' : ℂ → (ℂ →L[ℝ] ℂ) := fun y =>
        (((-2 : ℤ):ℂ) * (z - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ) with hFp'
      have hFp'_cont : ContinuousOn Fp' (Metric.closedBall (0:ℂ) R') := by
        rw [hFp']
        apply ContinuousOn.fun_smul _ continuousOn_const
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne y hy
      have hFp'_int : IntegrableOn Fp' (Metric.closedBall (0:ℂ) R') volume :=
        hFp'_cont.integrableOn_compact (isCompact_closedBall 0 R')
      rw [smul_apply, ContinuousLinearMap.integral_apply hFp'_int]
      rw [norm_smul]
      have hnormconst : ‖-(1/(π:ℂ))‖ = 1/π := by
        rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hnormconst]
      have hπpos : 0 < π := Real.pi_pos
      set Cval : ℝ := 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖ with hCval
      have hbd : ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖(Fp' y) m‖ ≤ Cval := by
        intro y hy
        rw [hFp', smul_apply, one_apply_eq_self, smul_eq_mul]
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        have hzy : ‖z‖ - R' ≤ ‖z - y‖ := by
          have : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
          linarith
        have hzypos : 0 < ‖z - y‖ := lt_of_lt_of_le hbdpos hzy
        rw [norm_mul, norm_mul, norm_mul]
        have hk1 : ‖((-2:ℤ):ℂ)‖ = 2 := by norm_num
        have hk2 : ‖(z - y) ^ ((-2:ℤ) - 1)‖ = ‖z - y‖⁻¹^3 := by
          rw [norm_zpow, show ((-2:ℤ) - 1) = (-3:ℤ) by ring, zpow_neg,
            show ((3:ℤ)) = ((3:ℕ):ℤ) by norm_num, zpow_natCast, inv_pow]
        rw [hk1, hk2, hCval]
        have hmono : ‖z - y‖⁻¹^3 ≤ (‖z‖ - R')⁻¹^3 := by gcongr
        have hstep : 2 * ‖z - y‖⁻¹^3 * ‖ν y‖ * ‖m‖ ≤ 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖ := by
          apply mul_le_mul _ le_rfl (norm_nonneg _) (by positivity)
          apply mul_le_mul _ (hM y) (norm_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_left hmono (by norm_num)
        exact hstep
      have hballfin : volume (Metric.closedBall (0:ℂ) R') < ⊤ := by
        rw [Complex.volume_closedBall]; finiteness
      have hib := norm_setIntegral_le_of_norm_le_const hballfin hbd
      have hvolnn : 0 ≤ (volume (Metric.closedBall (0:ℂ) R')).toReal := ENNReal.toReal_nonneg
      have hCvalbd : Cval ≤ 16 * M * ‖m‖ / ‖z‖^2 := by
        rw [hCval]
        have he : (‖z‖ - R')⁻¹^3 ≤ (‖z‖/2)⁻¹^3 := by
          apply pow_le_pow_left₀ (inv_nonneg.mpr hbdpos.le)
          apply inv_anti₀ (by positivity)
          linarith [hz]
        have he2 : (‖z‖/2)⁻¹^3 ≤ 8 / ‖z‖^2 := by
          rw [inv_div, div_pow]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (1:ℝ) ≤ ‖z‖ := by linarith [hz]
          nlinarith [pow_pos hzpos 2, sq_nonneg ‖z‖, hzpos.le]
        calc 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖
            ≤ 2 * (8 / ‖z‖^2) * M * ‖m‖ := by
              apply mul_le_mul _ le_rfl (norm_nonneg _) (by positivity)
              apply mul_le_mul _ le_rfl hMnn (by positivity)
              apply mul_le_mul_of_nonneg_left (le_trans he he2) (by norm_num)
          _ = 16 * M * ‖m‖ / ‖z‖^2 := by ring
      calc (1/π) * ‖∫ y in Metric.closedBall (0:ℂ) R', (Fp' y) m‖
          ≤ (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [Measure.real] at hib; exact hib
        _ ≤ Cd / ‖z‖^2 := by
            rw [hCd]
            have hstep : (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal)
                ≤ (1/π) * ((16 * M * ‖m‖ / ‖z‖^2)
                  * (volume (Metric.closedBall (0:ℂ) R')).toReal) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul_of_nonneg_right hCvalbd hvolnn
            refine le_trans hstep (le_of_eq ?_)
            field_simp
    -- now MemLp via decay helper
    have hcont : Continuous (fun z => (fderiv ℝ (beurling ν) z) m) :=
      (hB.continuous_fderiv (n := 1) one_ne_zero).clm_apply continuous_const
    have haesm : AEStronglyMeasurable (fun z => (fderiv ℝ (beurling ν) z) m) volume :=
      hcont.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm haesm]
    set R'' : ℝ := 2*R'+4 with hR''def
    have hR''pos : 0 < R'' := by rw [hR''def]; positivity
    have hball : IntegrableOn (fun z => ‖(fderiv ℝ (beurling ν) z) m‖^2)
        (Metric.closedBall (0:ℂ) R'') volume :=
      (hcont.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 R'')
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (Cd / p.1^2)^2)) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      apply Measurable.pow_const
      exact measurable_const.div (measurable_fst.pow_const 2)
    have hcompl : IntegrableOn (fun z => ‖(fderiv ℝ (beurling ν) z) m‖^2)
        (Metric.closedBall (0:ℂ) R'')ᶜ volume := by
      refine ⟨((hcont.norm.pow 2).aestronglyMeasurable).restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hpt : ∀ z ∈ (Metric.closedBall (0:ℂ) R'')ᶜ,
          ‖(‖(fderiv ℝ (beurling ν) z) m‖^2 : ℝ)‖ₑ ≤ ENNReal.ofReal ((Cd / ‖z‖^2)^2) := by
        intro z hz
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hb := hdecay z hz
        have hnn : 0 ≤ ‖(fderiv ℝ (beurling ν) z) m‖ := norm_nonneg _
        nlinarith [hb, hnn]
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_closedBall.compl hpt) ?_
      rw [← lintegral_indicator measurableSet_closedBall.compl]
      rw [← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ioi R'' ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * (Cd / p.1^2)^2)) p with hbox
      have hbound : ∀ p ∈ polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
            (fun z => ENNReal.ofReal ((Cd / ‖z‖^2)^2)) (Complex.polarCoord.symm p) ≤ box p := by
        intro p hp
        rw [polarCoord_target, Set.mem_prod] at hp
        obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        by_cases hmem : Complex.polarCoord.symm p ∈ (Metric.closedBall (0:ℂ) R'')ᶜ
        · rw [Set.indicator_of_mem hmem]
          have hpR : R'' < p.1 := by
            rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, hnorm, not_le] at hmem
            exact hmem
          rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hpR, hp2⟩)]
          rw [hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]
          exact zero_le
      have hboxmeas : Measurable box :=
        hmeas_polar.indicator (measurableSet_Ioi.prod measurableSet_Ioo)
      calc
        ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
              (fun z => ENNReal.ofReal ((Cd / ‖z‖^2)^2)) (Complex.polarCoord.symm p)
            ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hboxmeas hbound
        _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
        _ = ∫⁻ p in (Set.Ioi R'' ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (p.1 * (Cd / p.1^2)^2) := by
              rw [hbox, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ]
              rw [setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint : IntegrableOn (fun r : ℝ => r * (Cd / r^2)^2) (Set.Ioi R'') volume := by
                have heq : (fun r : ℝ => r * (Cd / r^2)^2) =ᶠ[ae (volume.restrict (Set.Ioi R''))]
                    (fun r : ℝ => Cd^2 * r^(-3 : ℝ)) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
                  simp only [Set.mem_Ioi] at hr
                  have hrpos : 0 < r := lt_trans hR''pos hr
                  have hrne : r ≠ 0 := ne_of_gt hrpos
                  rw [Real.rpow_neg hrpos.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
                  field_simp
                rw [integrableOn_congr_fun_ae heq]
                apply Integrable.const_mul
                rw [← IntegrableOn, integrableOn_Ioi_rpow_iff hR''pos]
                norm_num
              have hfin := hint.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun x hx => ?_)) hfin
              · apply Measurable.enorm
                apply Measurable.mul measurable_id
                apply Measurable.pow_const
                exact measurable_const.div (measurable_id.pow_const 2)
              · simp only [Set.mem_Ioi] at hx
                have hxpos : 0 < x := lt_trans hR''pos hx
                rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hball.union hcompl
    rw [Set.union_compl_self, integrableOn_univ] at this
    exact this
  have hBIL2 : MemLp (fun z => (fderiv ℝ B z) Complex.I) 2 volume := by
    rw [hBdef]
    suffices h : ∀ m : ℂ, MemLp (fun z => (fderiv ℝ (beurling ν) z) m) 2 volume from h Complex.I
    intro m
    set R' : ℝ := max R 0 with hR'def
    have hR'nn : 0 ≤ R' := le_max_right _ _
    have hR' : tsupport ν ⊆ Metric.closedBall (0 : ℂ) R' :=
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ, ‖ν ζ‖ ≤ M := hνc.exists_bound_of_continuous hν1.continuous
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    -- representation (as in hBL2)
    have Hrepr : ∀ z : ℂ, R' + 1 < ‖z‖ →
        beurling ν z = -(1/(π:ℂ)) * ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
      intro z hz
      have hvanr : ∀ r : ℝ, r ≤ 1 → ∀ y ∈ Metric.ball z r, ν y = 0 := by
        intro r hr y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hy
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h1 := hR' hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        have h2 : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := norm_le_insert y z
        have h3 : ‖y - z‖ < 1 := lt_of_lt_of_le hy hr
        linarith
      have hcont : Continuous (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        rw [← continuousOn_univ]
        apply ContinuousOn.mono (s := {y | y ≠ z} ∪ Metric.ball z 1) _ (by
          intro y _; by_cases h : y = z
          · right; rw [h]; simp [Metric.mem_ball]
          · left; exact h)
        apply ContinuousOn.union_of_isOpen _ _ isOpen_ne Metric.isOpen_ball
        · apply ContinuousOn.mul _ hν1.continuous.continuousOn
          apply ContinuousOn.zpow₀ (by fun_prop)
          intro y hy; left; rw [sub_ne_zero]; exact fun h => hy h.symm
        · have hg : ContinuousOn (fun _ : ℂ => (0:ℂ)) (Metric.ball z 1) := continuousOn_const
          refine hg.congr ?_
          intro y hy
          change (z - y) ^ (-2:ℤ) * ν y = 0
          rw [hvanr 1 le_rfl y hy, mul_zero]
      have hcs : HasCompactSupport (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        have heq : (fun y => (z - y) ^ (-2:ℤ) * ν y) = (fun y => (z - y) ^ (-2:ℤ)) * ν := rfl
        rw [heq]; exact hνc.mul_left
      have hint : Integrable (fun y => (z - y) ^ (-2:ℤ) * ν y) volume :=
        hcont.integrable_of_hasCompactSupport hcs
      have hcz : ∀ r : ℝ, r ≤ 1 →
          czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z = ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
        intro r hr
        rw [czOperator]
        have hfull : (∫ y, (z - y) ^ (-2 : ℤ) * ν y)
            = (∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y)
              + ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * ν y := by
          rw [← setIntegral_univ (μ := volume), ← Set.union_compl_self (Metric.ball z r),
            setIntegral_union disjoint_compl_right measurableSet_ball.compl
              hint.integrableOn hint.integrableOn]
        have hzero : ∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y = 0 := by
          rw [setIntegral_eq_zero_of_forall_eq_zero]
          intro y hy; rw [hvanr r hr y hy, mul_zero]
        rw [hfull, hzero, zero_add]
      rw [beurling]
      congr 1
      apply Filter.Tendsto.limUnder_eq
      have hev : (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z)
          =ᶠ[𝓝[>] (0:ℝ)] (fun _ => ∫ y, (z - y) ^ (-2 : ℤ) * ν y) := by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with r hr
        exact hcz r (le_of_lt hr.2)
      exact Tendsto.congr' hev.symm tendsto_const_nhds
    -- DUI: HasFDerivAt of parametric integral over ball
    have hG : ∀ w : ℂ, 2 * R' + 3 < ‖w‖ → HasFDerivAt
        (fun u => ∫ y in Metric.closedBall (0:ℂ) R', (u - y) ^ (-2 : ℤ) * ν y)
        (∫ y in Metric.closedBall (0:ℂ) R',
          ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ))) w := by
      intro z hz
      set Fp' : ℂ → ℂ → (ℂ →L[ℝ] ℂ) := fun w y =>
        (((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ) with hFp'
      set s : Set ℂ := Metric.ball z 1 with hs_def
      set bnd : ℝ := 2 * (‖z‖ - R' - 1)⁻¹^3 * M with hbnd
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hbdpos : 0 < ‖z‖ - R' - 1 := by linarith
      have hgeo : ∀ w ∈ s, ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖z‖ - R' - 1 ≤ ‖w - y‖ := by
        intro w hw y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hw
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        have h1 : ‖w - y‖ ≥ ‖z - y‖ - ‖z - w‖ := by
          have := norm_sub_norm_le (z - y) (z - w)
          have heq : (z - y) - (z - w) = w - y := by ring
          rw [heq] at this; linarith
        have h2 : ‖z - y‖ ≥ ‖z‖ - ‖y‖ := norm_sub_norm_le z y
        have h3 : ‖z - w‖ < 1 := by rw [norm_sub_rev]; exact hw
        linarith
      have hne : ∀ w ∈ s, ∀ y ∈ Metric.closedBall (0:ℂ) R', w ≠ y := by
        intro w hw y hy h
        have := hgeo w hw y hy; rw [h, sub_self, norm_zero] at this; linarith
      have hcontFp : ∀ w ∈ s, ContinuousOn (fun y => (w - y)^(-2:ℤ) * ν y)
          (Metric.closedBall (0:ℂ) R') := by
        intro w hw
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne w hw y hy
      have hFp'_cont : ContinuousOn (fun y => Fp' z y) (Metric.closedBall (0:ℂ) R') := by
        rw [hFp']
        apply ContinuousOn.fun_smul _ continuousOn_const
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne z (Metric.mem_ball_self (by norm_num)) y hy
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => bnd)
        (F' := Fp') (s := s) (Metric.ball_mem_nhds z (by norm_num))
      · filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0:ℝ) < 1)] with w hw
        exact (hcontFp w hw).aestronglyMeasurable measurableSet_closedBall
      · exact (hcontFp z (Metric.mem_ball_self (by norm_num))).integrableOn_compact
          (isCompact_closedBall 0 R')
      · exact hFp'_cont.aestronglyMeasurable measurableSet_closedBall
      · rw [ae_restrict_iff' measurableSet_closedBall]
        apply ae_of_all
        intro y hy w hw
        rw [hFp', hbnd]
        rw [norm_smul]
        have h1norm : ‖(1 : ℂ →L[ℝ] ℂ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        have hwy : ‖z‖ - R' - 1 ≤ ‖w - y‖ := hgeo w hw y hy
        have hwypos : 0 < ‖w - y‖ := lt_of_lt_of_le hbdpos hwy
        have hknorm : ‖((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y‖
            ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by
          rw [norm_mul, norm_mul]
          have hk1 : ‖((-2:ℤ):ℂ)‖ = 2 := by norm_num
          have hk2 : ‖(w - y) ^ ((-2:ℤ) - 1)‖ = ‖w - y‖⁻¹^3 := by
            rw [norm_zpow, show ((-2:ℤ) - 1) = (-3:ℤ) by ring, zpow_neg,
              show ((3:ℤ)) = ((3:ℕ):ℤ) by norm_num, zpow_natCast, inv_pow]
          rw [hk1, hk2]
          have hmono : ‖w - y‖⁻¹^3 ≤ (‖z‖ - R' - 1)⁻¹^3 := by gcongr
          have h2 : (0:ℝ) ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 := by positivity
          exact mul_le_mul (by apply mul_le_mul_of_nonneg_left hmono (by norm_num)) (hM y)
            (norm_nonneg _) h2
        have hbndnn : (0:ℝ) ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by positivity
        calc ‖((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖
            ≤ (2 * (‖z‖ - R' - 1)⁻¹^3 * M) * 1 :=
              mul_le_mul hknorm h1norm (norm_nonneg _) hbndnn
          _ = 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by ring
      · exact integrableOn_const (by rw [Complex.volume_closedBall]; finiteness) (by finiteness)
      · rw [ae_restrict_iff' measurableSet_closedBall]
        apply ae_of_all
        intro y hy w hw
        change HasFDerivAt (fun u => (u - y) ^ (-2:ℤ) * ν y) (Fp' w y) w
        have hsub : HasFDerivAt (fun u : ℂ => u - y) (1 : ℂ →L[ℝ] ℂ) w := by
          exact hasFDerivAt_sub_const y
        have hzpw : HasFDerivAt (fun u : ℂ => (u - y) ^ (-2:ℤ))
            ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1)) • (1 : ℂ →L[ℝ] ℂ)) w := by
          have hc := (hasDerivAt_zpow (-2 : ℤ) (w - y)
            (Or.inl (sub_ne_zero.mpr (hne w hw y hy)))).comp_hasFDerivAt w hsub
          exact hc
        have hmul := hzpw.mul_const (ν y)
        rw [hFp']
        change HasFDerivAt (fun u => (u - y) ^ (-2:ℤ) * ν y)
          ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)) w
        have heq : (((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)
            = (ν y) • ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1)) • (1 : ℂ →L[ℝ] ℂ)) := by
          rw [smul_smul]; ring_nf
        rw [heq]; exact hmul
    -- derivative decay bound: ‖fderiv B z m‖ ≤ Cd / ‖z‖²  for ‖z‖ > 2R'+4
    set Cd : ℝ := 16 * (volume (Metric.closedBall (0:ℂ) R')).toReal * M * ‖m‖ / π with hCd
    have hCdnn : 0 ≤ Cd := by rw [hCd]; positivity
    have hdecay : ∀ z : ℂ, (2*R'+4) < ‖z‖ → ‖(fderiv ℝ (beurling ν) z) m‖ ≤ Cd / ‖z‖^2 := by
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hsuppeq : ∀ w : ℂ, R' + 1 < ‖w‖ →
          (∫ y, (w - y) ^ (-2 : ℤ) * ν y)
            = ∫ y in Metric.closedBall (0:ℂ) R', (w - y) ^ (-2 : ℤ) * ν y := by
        intro w hw
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
        intro y hy; rw [image_eq_zero_of_notMem_tsupport (fun hmem => hy (hR' hmem)), mul_zero]
      have hBeq : (beurling ν) =ᶠ[nhds z]
          fun w => -(1/(π:ℂ)) * ∫ y in Metric.closedBall (0:ℂ) R', (w - y) ^ (-2 : ℤ) * ν y := by
        have hopen : {w : ℂ | 2 * R' + 4 < ‖w‖} ∈ nhds z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hz
        filter_upwards [hopen] with w hw
        rw [Hrepr w (by linarith), hsuppeq w (by linarith)]
      have hGz := hG z (by linarith)
      have hBfd : HasFDerivAt (beurling ν)
          ((-(1/(π:ℂ))) • (∫ y in Metric.closedBall (0:ℂ) R',
              ((((-2 : ℤ):ℂ) * (z - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)))) z := by
        apply HasFDerivAt.congr_of_eventuallyEq _ hBeq
        exact hGz.const_smul (-(1/(π:ℂ)))
      rw [hBfd.fderiv]
      have hbdpos : 0 < ‖z‖ - R' := by linarith [hz]
      have hne : ∀ y ∈ Metric.closedBall (0:ℂ) R', z ≠ y := by
        intro y hy h
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        rw [h] at hz; linarith
      set Fp' : ℂ → (ℂ →L[ℝ] ℂ) := fun y =>
        (((-2 : ℤ):ℂ) * (z - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ) with hFp'
      have hFp'_cont : ContinuousOn Fp' (Metric.closedBall (0:ℂ) R') := by
        rw [hFp']
        apply ContinuousOn.fun_smul _ continuousOn_const
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne y hy
      have hFp'_int : IntegrableOn Fp' (Metric.closedBall (0:ℂ) R') volume :=
        hFp'_cont.integrableOn_compact (isCompact_closedBall 0 R')
      rw [smul_apply, ContinuousLinearMap.integral_apply hFp'_int]
      rw [norm_smul]
      have hnormconst : ‖-(1/(π:ℂ))‖ = 1/π := by
        rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hnormconst]
      have hπpos : 0 < π := Real.pi_pos
      set Cval : ℝ := 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖ with hCval
      have hbd : ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖(Fp' y) m‖ ≤ Cval := by
        intro y hy
        rw [hFp', smul_apply, one_apply_eq_self, smul_eq_mul]
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        have hzy : ‖z‖ - R' ≤ ‖z - y‖ := by
          have : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
          linarith
        have hzypos : 0 < ‖z - y‖ := lt_of_lt_of_le hbdpos hzy
        rw [norm_mul, norm_mul, norm_mul]
        have hk1 : ‖((-2:ℤ):ℂ)‖ = 2 := by norm_num
        have hk2 : ‖(z - y) ^ ((-2:ℤ) - 1)‖ = ‖z - y‖⁻¹^3 := by
          rw [norm_zpow, show ((-2:ℤ) - 1) = (-3:ℤ) by ring, zpow_neg,
            show ((3:ℤ)) = ((3:ℕ):ℤ) by norm_num, zpow_natCast, inv_pow]
        rw [hk1, hk2, hCval]
        have hmono : ‖z - y‖⁻¹^3 ≤ (‖z‖ - R')⁻¹^3 := by gcongr
        have hstep : 2 * ‖z - y‖⁻¹^3 * ‖ν y‖ * ‖m‖ ≤ 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖ := by
          apply mul_le_mul _ le_rfl (norm_nonneg _) (by positivity)
          apply mul_le_mul _ (hM y) (norm_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_left hmono (by norm_num)
        exact hstep
      have hballfin : volume (Metric.closedBall (0:ℂ) R') < ⊤ := by
        rw [Complex.volume_closedBall]; finiteness
      have hib := norm_setIntegral_le_of_norm_le_const hballfin hbd
      have hvolnn : 0 ≤ (volume (Metric.closedBall (0:ℂ) R')).toReal := ENNReal.toReal_nonneg
      have hCvalbd : Cval ≤ 16 * M * ‖m‖ / ‖z‖^2 := by
        rw [hCval]
        have he : (‖z‖ - R')⁻¹^3 ≤ (‖z‖/2)⁻¹^3 := by
          apply pow_le_pow_left₀ (inv_nonneg.mpr hbdpos.le)
          apply inv_anti₀ (by positivity)
          linarith [hz]
        have he2 : (‖z‖/2)⁻¹^3 ≤ 8 / ‖z‖^2 := by
          rw [inv_div, div_pow]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (1:ℝ) ≤ ‖z‖ := by linarith [hz]
          nlinarith [pow_pos hzpos 2, sq_nonneg ‖z‖, hzpos.le]
        calc 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖
            ≤ 2 * (8 / ‖z‖^2) * M * ‖m‖ := by
              apply mul_le_mul _ le_rfl (norm_nonneg _) (by positivity)
              apply mul_le_mul _ le_rfl hMnn (by positivity)
              apply mul_le_mul_of_nonneg_left (le_trans he he2) (by norm_num)
          _ = 16 * M * ‖m‖ / ‖z‖^2 := by ring
      calc (1/π) * ‖∫ y in Metric.closedBall (0:ℂ) R', (Fp' y) m‖
          ≤ (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [Measure.real] at hib; exact hib
        _ ≤ Cd / ‖z‖^2 := by
            rw [hCd]
            have hstep : (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal)
                ≤ (1/π) * ((16 * M * ‖m‖ / ‖z‖^2)
                  * (volume (Metric.closedBall (0:ℂ) R')).toReal) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul_of_nonneg_right hCvalbd hvolnn
            refine le_trans hstep (le_of_eq ?_)
            field_simp
    -- now MemLp via decay helper
    have hcont : Continuous (fun z => (fderiv ℝ (beurling ν) z) m) :=
      (hB.continuous_fderiv (n := 1) one_ne_zero).clm_apply continuous_const
    have haesm : AEStronglyMeasurable (fun z => (fderiv ℝ (beurling ν) z) m) volume :=
      hcont.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm haesm]
    set R'' : ℝ := 2*R'+4 with hR''def
    have hR''pos : 0 < R'' := by rw [hR''def]; positivity
    have hball : IntegrableOn (fun z => ‖(fderiv ℝ (beurling ν) z) m‖^2)
        (Metric.closedBall (0:ℂ) R'') volume :=
      (hcont.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 R'')
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (Cd / p.1^2)^2)) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      apply Measurable.pow_const
      exact measurable_const.div (measurable_fst.pow_const 2)
    have hcompl : IntegrableOn (fun z => ‖(fderiv ℝ (beurling ν) z) m‖^2)
        (Metric.closedBall (0:ℂ) R'')ᶜ volume := by
      refine ⟨((hcont.norm.pow 2).aestronglyMeasurable).restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hpt : ∀ z ∈ (Metric.closedBall (0:ℂ) R'')ᶜ,
          ‖(‖(fderiv ℝ (beurling ν) z) m‖^2 : ℝ)‖ₑ ≤ ENNReal.ofReal ((Cd / ‖z‖^2)^2) := by
        intro z hz
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hb := hdecay z hz
        have hnn : 0 ≤ ‖(fderiv ℝ (beurling ν) z) m‖ := norm_nonneg _
        nlinarith [hb, hnn]
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_closedBall.compl hpt) ?_
      rw [← lintegral_indicator measurableSet_closedBall.compl]
      rw [← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ioi R'' ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * (Cd / p.1^2)^2)) p with hbox
      have hbound : ∀ p ∈ polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
            (fun z => ENNReal.ofReal ((Cd / ‖z‖^2)^2)) (Complex.polarCoord.symm p) ≤ box p := by
        intro p hp
        rw [polarCoord_target, Set.mem_prod] at hp
        obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        by_cases hmem : Complex.polarCoord.symm p ∈ (Metric.closedBall (0:ℂ) R'')ᶜ
        · rw [Set.indicator_of_mem hmem]
          have hpR : R'' < p.1 := by
            rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, hnorm, not_le] at hmem
            exact hmem
          rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hpR, hp2⟩)]
          rw [hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]
          exact zero_le
      have hboxmeas : Measurable box :=
        hmeas_polar.indicator (measurableSet_Ioi.prod measurableSet_Ioo)
      calc
        ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
              (fun z => ENNReal.ofReal ((Cd / ‖z‖^2)^2)) (Complex.polarCoord.symm p)
            ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hboxmeas hbound
        _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
        _ = ∫⁻ p in (Set.Ioi R'' ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (p.1 * (Cd / p.1^2)^2) := by
              rw [hbox, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ]
              rw [setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint : IntegrableOn (fun r : ℝ => r * (Cd / r^2)^2) (Set.Ioi R'') volume := by
                have heq : (fun r : ℝ => r * (Cd / r^2)^2) =ᶠ[ae (volume.restrict (Set.Ioi R''))]
                    (fun r : ℝ => Cd^2 * r^(-3 : ℝ)) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
                  simp only [Set.mem_Ioi] at hr
                  have hrpos : 0 < r := lt_trans hR''pos hr
                  have hrne : r ≠ 0 := ne_of_gt hrpos
                  rw [Real.rpow_neg hrpos.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
                  field_simp
                rw [integrableOn_congr_fun_ae heq]
                apply Integrable.const_mul
                rw [← IntegrableOn, integrableOn_Ioi_rpow_iff hR''pos]
                norm_num
              have hfin := hint.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun x hx => ?_)) hfin
              · apply Measurable.enorm
                apply Measurable.mul measurable_id
                apply Measurable.pow_const
                exact measurable_const.div (measurable_id.pow_const 2)
              · simp only [Set.mem_Ioi] at hx
                have hxpos : 0 < x := lt_trans hR''pos hx
                rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hball.union hcompl
    rw [Set.union_compl_self, integrableOn_univ] at this
    exact this
  exact dirichlet_energy_isometry hB hν1 hBL2 hNL2 hB1L2 hBIL2 hN1L2 hNIL2 hClairaut

end NoWanderingDomains
