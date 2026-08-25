/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.GehringHigherIntegrability.Poincare

/-!
# Gehring self-improvement: the Sobolev–Poincaré node (N1)

Assembles the cutoff Sobolev–Poincaré inequality `sobolevPoincare_ball` on a ball from the
endpoint Sobolev embedding and the `(1,1)`-Poincaré bound, via the cutoff weak-partial
identities (`cutoff_weak_partials`, `cutoff_sobolev_oscL2`, `cutoff_commutator_bound`,
`cutoff_partial_l1_le`) and the constant-subtraction helper `hasWeakDirDeriv_const`.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace NoWanderingDomains

/-- **Auxiliary: the constant function has weak directional derivative `0`.** A constant `c`
is `C¹` with vanishing Fréchet derivative, so the weak directional derivative supplied by
`HasWeakDirDeriv.of_contDiffOn` is the zero function. Used to subtract the centring constant
from the cutoff product in the Sobolev–Poincaré node N1. -/
private theorem hasWeakDirDeriv_const (v : ℂ) (c : ℂ) :
    HasWeakDirDeriv v (fun _ => (0 : ℂ)) (fun _ => c) (Set.univ : Set ℂ) := by
  have hcd : ContDiffOn ℝ 1 (fun _ : ℂ => c) (Set.univ : Set ℂ) :=
    (contDiff_const).contDiffOn
  have h := HasWeakDirDeriv.of_contDiffOn (v := v) isOpen_univ hcd
  -- `fderiv ℝ (const) = 0`, so the supplied weak derivative is the zero function.
  have hfd : (fun z => (fderiv ℝ (fun _ : ℂ => c) z) v) = (fun _ => (0 : ℂ)) := by
    funext z
    rw [show (fun _ : ℂ => c) = Function.const ℂ c from rfl, fderiv_const]
    rfl
  rwa [hfd] at h

/-- **Auxiliary: the compactly-supported `W^{1,1}→L²` Sobolev embedding.** A compactly
supported `MemLp 2` function `u` whose weak directional partials `gx` (direction `1`) and
`gy` (direction `I`) are `MemLp 1` satisfies the genuine planar endpoint Sobolev bound
`‖u‖_{L²} ≤ C·(‖gx‖_{L¹} + ‖gy‖_{L¹})` with the dimensional constant `C` of P1
(`eLpNorm_two_le_eLpNorm_fderiv_one`). Proof: mollify `u` to a `C¹` compactly-supported `w`
with `‖w − u‖_{L²} ≤ ε` and `‖∇w‖_{L¹} ≤ ‖gx‖₁ + ‖gy‖₁ + ε` (P3
`exists_contDiff_approx_W11`), apply P1 to `w`, and let `ε → 0`. This is the cutoff route's
only use of the P-stack; it returns the constant `C` of P1 unchanged. -/
private theorem sobolev_compactSupport_W11 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u gx gy : ℂ → ℂ},
      MemLp u 2 volume → HasCompactSupport u →
      HasWeakDirDeriv 1 gx u Set.univ → HasWeakDirDeriv Complex.I gy u Set.univ →
      MemLp gx 1 volume → MemLp gy 1 volume →
        eLpNorm u 2 volume ≤
          ENNReal.ofReal C * (eLpNorm gx 1 volume + eLpNorm gy 1 volume) := by
  obtain ⟨C, hC0, hP1⟩ := eLpNorm_two_le_eLpNorm_fderiv_one
  refine ⟨C, hC0, ?_⟩
  intro u gx gy hu2 hucs hgx hgy hgx1 hgy1
  -- The target bound holds with any positive slack `ε`; pass `ε → 0`.
  set RHS₀ : ℝ≥0∞ := ENNReal.ofReal C * (eLpNorm gx 1 volume + eLpNorm gy 1 volume) with hRHS₀
  have hslack : ∀ ε : ℝ, 0 < ε →
      eLpNorm u 2 volume ≤ RHS₀ + ENNReal.ofReal ((C + 1) * ε) := by
    intro ε hε
    obtain ⟨w, hwcd, hwcs, hwdist, hwgrad⟩ :=
      exists_contDiff_approx_W11 hu2 hucs hgx hgy hgx1 hgy1 hε
    -- P1 on the `C¹` compactly-supported approximant `w`.
    have hP1w : eLpNorm w 2 volume ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ w) 1 volume :=
      hP1 hwcd hwcs
    -- `‖u‖₂ ≤ ‖w‖₂ + ‖w − u‖₂`.
    have htri : eLpNorm u 2 volume
        ≤ eLpNorm w 2 volume + eLpNorm (fun z => w z - u z) 2 volume := by
      have hsub : eLpNorm (fun z => u z) 2 volume
          ≤ eLpNorm (fun z => w z) 2 volume + eLpNorm (fun z => u z - w z) 2 volume := by
        have hadd := eLpNorm_add_le (f := fun z => w z) (g := fun z => u z - w z)
          hwcd.continuous.aestronglyMeasurable (hu2.1.sub hwcd.continuous.aestronglyMeasurable)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        have hfun : ((fun z => w z) + fun z => u z - w z) = (fun z => u z) := by
          funext z; simp
        rwa [hfun] at hadd
      -- `‖u − w‖₂ = ‖w − u‖₂`.
      have hflip : eLpNorm (fun z => u z - w z) 2 volume
          = eLpNorm (fun z => w z - u z) 2 volume := by
        rw [← eLpNorm_neg]; congr 1; funext z; simp
      rwa [hflip] at hsub
    -- Assemble: `‖u‖₂ ≤ ofReal C·(‖gx‖₁ + ‖gy‖₁ + ofReal ε) + ofReal ε`.
    refine le_trans htri ?_
    refine le_trans (add_le_add hP1w hwdist) ?_
    refine le_trans (add_le_add (by gcongr : ENNReal.ofReal C * eLpNorm (fderiv ℝ w) 1 volume
      ≤ ENNReal.ofReal C * (eLpNorm gx 1 volume + eLpNorm gy 1 volume + ENNReal.ofReal ε))
      le_rfl) ?_
    -- Distribute and collect into `RHS₀ + ofReal((C+1)·ε)`.
    rw [mul_add, mul_add]
    -- `ofReal C · ofReal ε = ofReal (C·ε)`; `ofReal ε = ofReal ε`.
    have hCe : ENNReal.ofReal C * ENNReal.ofReal ε = ENNReal.ofReal (C * ε) :=
      (ENNReal.ofReal_mul hC0).symm
    rw [hCe]
    have hsplit : ENNReal.ofReal ((C + 1) * ε)
        = ENNReal.ofReal (C * ε) + ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) hε.le]; congr 1; ring
    rw [hRHS₀, hsplit]
    -- Rearrange `(ofReal C·‖gx‖₁ + ofReal C·‖gy‖₁ + ofReal(C·ε)) + ofReal ε`.
    rw [mul_add]
    ring_nf
    -- After `ring_nf` both sides are sums of the same five `ℝ≥0∞` terms.
    rfl
  -- Pass to the limit `ε → 0⁺`: the slack `ofReal((C+1)·ε) → 0`.
  have hlim : Tendsto (fun ε : ℝ => RHS₀ + ENNReal.ofReal ((C + 1) * ε)) (𝓝[>] 0)
      (𝓝 (RHS₀ + 0)) := by
    refine Filter.Tendsto.const_add RHS₀ ?_
    have : Tendsto (fun ε : ℝ => ENNReal.ofReal ((C + 1) * ε)) (𝓝 0) (𝓝 (ENNReal.ofReal 0)) := by
      refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
      have : Tendsto (fun ε : ℝ => (C + 1) * ε) (𝓝 0) (𝓝 ((C + 1) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this
    rw [ENNReal.ofReal_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hslack ε hε

/-! ## N1 — Sobolev–Poincaré on a ball for the `W^{1,2}` primitive -/

set_option maxHeartbeats 400000 in
-- Extracted Leibniz weak-derivative algebra for the N1 cutoff product, isolated so its
-- single self-contained elaboration stays within the heartbeat budget.
/-- **Auxiliary for N1: the cutoff weak partials.** The cutoff product `u = χ·(F − c)`
has Leibniz weak directional partials `χ·Gx + (∂₁χ)(F − c)` (direction `1`) and
`χ·Gy + (∂_I χ)(F − c)` (direction `I`). Proof: `HasWeakDirDeriv.smul_smooth` on `F` and
on the centring constant (`hasWeakDirDeriv_const`), combined by `HasWeakDirDeriv.sub`. -/
theorem cutoff_weak_partials {F Gx Gy : ℂ → ℂ} {c : ℂ} {χ : ℂ → ℝ}
    (hFmem : MemLp F 2 volume) (hGxmem : MemLp Gx 2 volume) (hGymem : MemLp Gy 2 volume)
    (hGxweak : HasWeakDirDeriv 1 Gx F Set.univ)
    (hGyweak : HasWeakDirDeriv Complex.I Gy F Set.univ)
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) :
    HasWeakDirDeriv 1 (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c))
        (fun z => χ z • (F z - c)) Set.univ ∧
      HasWeakDirDeriv Complex.I (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c))
        (fun z => χ z • (F z - c)) Set.univ := by
  have hχcont : Continuous χ := hχcd.continuous
  set u : ℂ → ℂ := fun z => χ z • (F z - c) with hu_def
  -- Local integrability of `F` and the constant `c`.
  have hFloc : LocallyIntegrableOn F (Set.univ : Set ℂ) :=
    (hFmem.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hGxloc : LocallyIntegrableOn Gx (Set.univ : Set ℂ) :=
    (hGxmem.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hGyloc : LocallyIntegrableOn Gy (Set.univ : Set ℂ) :=
    (hGymem.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hcloc : LocallyIntegrableOn (fun _ : ℂ => c) (Set.univ : Set ℂ) :=
    (locallyIntegrable_const c).locallyIntegrableOn _
  have hχsmoothTop : ContDiff ℝ (⊤ : ℕ∞) χ := hχcd
  -- Weak partials of `χ•F` and `χ•(const c)` via the Leibniz rule, then subtract.
  have hwF1 : HasWeakDirDeriv 1
      (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • F z) (fun z => χ z • F z) Set.univ :=
    hGxweak.smul_smooth hχsmoothTop hFloc hGxloc
  have hwc1 : HasWeakDirDeriv 1
      (fun z => χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c) (fun z => χ z • c) Set.univ :=
    (hasWeakDirDeriv_const 1 c).smul_smooth hχsmoothTop hcloc
      ((locallyIntegrable_const (0 : ℂ)).locallyIntegrableOn _)
  have hwF2 : HasWeakDirDeriv Complex.I
      (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z) (fun z => χ z • F z) Set.univ :=
    hGyweak.smul_smooth hχsmoothTop hFloc hGyloc
  have hwc2 : HasWeakDirDeriv Complex.I
      (fun z => χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c) (fun z => χ z • c) Set.univ :=
    (hasWeakDirDeriv_const Complex.I c).smul_smooth hχsmoothTop hcloc
      ((locallyIntegrable_const (0 : ℂ)).locallyIntegrableOn _)
  have hdχcont : Continuous (fun z => (fderiv ℝ χ z) 1) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχIcont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hzeroloc : LocallyIntegrableOn (fun _ : ℂ => (0 : ℂ)) (Set.univ : Set ℂ) :=
    (locallyIntegrable_const (0 : ℂ)).locallyIntegrableOn _
  have hχFloc : LocallyIntegrableOn (fun z => χ z • F z) (Set.univ : Set ℂ) :=
    MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hFloc
      hχcont.continuousOn
  have hχcloc : LocallyIntegrableOn (fun z => χ z • c) (Set.univ : Set ℂ) :=
    MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hcloc
      hχcont.continuousOn
  have hg1F_loc : LocallyIntegrableOn
      (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • F z) (Set.univ : Set ℂ) :=
    (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hGxloc
      hχcont.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hFloc
        hdχcont.continuousOn)
  have hg2F_loc : LocallyIntegrableOn
      (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z) (Set.univ : Set ℂ) :=
    (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hGyloc
      hχcont.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hFloc
        hdχIcont.continuousOn)
  have hg1c_loc : LocallyIntegrableOn
      (fun z => χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c) (Set.univ : Set ℂ) :=
    (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hzeroloc
      hχcont.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hcloc
        hdχcont.continuousOn)
  have hg2c_loc : LocallyIntegrableOn
      (fun z => χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c) (Set.univ : Set ℂ) :=
    (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hzeroloc
      hχcont.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hcloc
        hdχIcont.continuousOn)
  set gxu : ℂ → ℂ := fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c) with hgxu_def
  set gyu : ℂ → ℂ := fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c) with hgyu_def
  have hu_eq : u = fun z => χ z • F z - χ z • c := by
    funext z
    change χ z • (F z - c) = χ z • F z - χ z • c
    module
  have hgxu_eq : gxu = fun z => (χ z • Gx z + ((fderiv ℝ χ z) 1) • F z)
      - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c) := by
    funext z
    change χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)
      = (χ z • Gx z + ((fderiv ℝ χ z) 1) • F z) - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c)
    module
  have hgyu_eq : gyu = fun z => (χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z)
      - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c) := by
    funext z
    change χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)
      = (χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z)
        - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c)
    module
  have hxweak : HasWeakDirDeriv 1 gxu u Set.univ := by
    rw [hu_eq, hgxu_eq]
    exact hwF1.sub hwc1 hχFloc hχcloc hg1F_loc hg1c_loc
  have hyweak : HasWeakDirDeriv Complex.I gyu u Set.univ := by
    rw [hu_eq, hgyu_eq]
    exact hwF2.sub hwc2 hχFloc hχcloc hg2F_loc hg2c_loc
  exact ⟨hxweak, hyweak⟩

set_option maxHeartbeats 400000 in
-- The Leibniz weak-derivative algebra + `MemLp`-membership + Sobolev-embedding chain is a
-- single self-contained elaboration, so it needs a modestly raised heartbeat budget.
/-- **Auxiliary for N1: the cutoff Sobolev oscillation bound.** For a `W^{1,2}` primitive
`F` (weak partials `Gx, Gy`), a centring constant `c`, and a smooth compactly-supported
cutoff `χ`, the cutoff product `u = χ·(F − c)` satisfies the compactly-supported Sobolev
embedding `‖u‖_{L²} ≤ C₁·(‖gxu‖_{L¹} + ‖gyu‖_{L¹})` where `gxu = χ·Gx + (∂₁χ)(F − c)` and
`gyu = χ·Gy + (∂_I χ)(F − c)` are the Leibniz weak partials of `u`. The constant `C₁` is the
endpoint Sobolev constant of `sobolev_compactSupport_W11`. This packages the entire
weak-derivative-algebra + `MemLp` + Sobolev portion of the N1 proof into one lemma so the
main node only does the (lighter) integral bookkeeping. -/
private theorem cutoff_sobolev_oscL2 :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ {F Gx Gy : ℂ → ℂ} {c : ℂ} {χ : ℂ → ℝ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        eLpNorm (fun z => χ z • (F z - c)) 2 volume ≤
          ENNReal.ofReal C₁ *
            (eLpNorm (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)) 1 volume +
             eLpNorm (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)) 1 volume) := by
  obtain ⟨C₁, hC₁0, hSob⟩ := sobolev_compactSupport_W11
  refine ⟨C₁, hC₁0, ?_⟩
  intro F Gx Gy c χ hFmem hGxmem hGymem hGxweak hGyweak hχcd hχcs
  have hχcont : Continuous χ := hχcd.continuous
  have hdχcont : Continuous (fun z => (fderiv ℝ χ z) 1) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχIcont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨hxweak, hyweak⟩ :=
    cutoff_weak_partials (c := c) hFmem hGxmem hGymem hGxweak hGyweak hχcd
  have hHT221 : ENNReal.HolderTriple 2 2 1 := ⟨by
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
    rw [ENNReal.inv_two_add_inv_two]⟩
  -- `MemLp` membership of the cutoff product `u` and its two partials, via Hölder products
  -- of the (compactly-supported, bounded) cutoff factors with the `L²` data `F, Gx, Gy`.
  have hχmemTop : MemLp χ ∞ volume := hχcont.memLp_top_of_hasCompactSupport hχcs volume
  have hχmem2 : MemLp χ 2 volume := hχcont.memLp_of_hasCompactSupport hχcs
  have hdχcs : HasCompactSupport (fun z => (fderiv ℝ χ z) 1) :=
    HasCompactSupport.fderiv_apply ℝ hχcs 1
  have hdχIcs : HasCompactSupport (fun z => (fderiv ℝ χ z) Complex.I) :=
    HasCompactSupport.fderiv_apply ℝ hχcs Complex.I
  have hdχmem2 : MemLp (fun z => (fderiv ℝ χ z) 1) 2 volume :=
    hdχcont.memLp_of_hasCompactSupport hdχcs
  have hdχImem2 : MemLp (fun z => (fderiv ℝ χ z) Complex.I) 2 volume :=
    hdχIcont.memLp_of_hasCompactSupport hdχIcs
  -- `c`-scaled cutoff factors are continuous, compactly supported, hence `MemLp` at any exponent.
  have hχc_mem2 : MemLp (fun z => χ z • c) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hχcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]; fun_prop
  have hdχc_mem1 : MemLp (fun z => ((fderiv ℝ χ z) 1) • c) 1 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hdχcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp hdχcont).mul continuous_const
  have hdχIc_mem1 : MemLp (fun z => ((fderiv ℝ χ z) Complex.I) • c) 1 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hdχIcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp hdχIcont).mul continuous_const
  -- The Hölder smul products at the explicit exponents (exponents pinned to avoid the
  -- `HolderTriple` semi-out-param unification blowup).
  have hχF2 : MemLp (fun z => χ z • F z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hFmem hχmemTop
  have hχGx1 : MemLp (fun z => χ z • Gx z) 1 volume :=
    MemLp.smul (r := 1) (p := 2) (q := 2) hGxmem hχmem2
  have hχGy1 : MemLp (fun z => χ z • Gy z) 1 volume :=
    MemLp.smul (r := 1) (p := 2) (q := 2) hGymem hχmem2
  have hdχF1 : MemLp (fun z => ((fderiv ℝ χ z) 1) • F z) 1 volume :=
    MemLp.smul (r := 1) (p := 2) (q := 2) hFmem hdχmem2
  have hdχIF1 : MemLp (fun z => ((fderiv ℝ χ z) Complex.I) • F z) 1 volume :=
    MemLp.smul (r := 1) (p := 2) (q := 2) hFmem hdχImem2
  -- `u = χ•F − χ•c ∈ L²` with compact support.
  have humem : MemLp (fun z => χ z • (F z - c)) 2 volume := by
    refine MemLp.ae_eq ?_ (hχF2.sub hχc_mem2)
    filter_upwards with z
    change χ z • F z - χ z • c = χ z • (F z - c)
    module
  have hucs : HasCompactSupport (fun z => χ z • (F z - c)) :=
    hχcs.smul_right (f' := fun z => F z - c)
  -- `gxu = χ•Gx + (∂₁χ)•F − (∂₁χ)•c ∈ L¹`.
  have hgxumem : MemLp (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)) 1 volume := by
    refine MemLp.ae_eq ?_ (hχGx1.add (hdχF1.sub hdχc_mem1))
    filter_upwards with z
    change χ z • Gx z + (((fderiv ℝ χ z) 1) • F z - ((fderiv ℝ χ z) 1) • c)
      = χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)
    module
  -- `gyu = χ•Gy + (∂_Iχ)•F − (∂_Iχ)•c ∈ L¹`.
  have hgyumem : MemLp (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)) 1 volume := by
    refine MemLp.ae_eq ?_ (hχGy1.add (hdχIF1.sub hdχIc_mem1))
    filter_upwards with z
    change χ z • Gy z + (((fderiv ℝ χ z) Complex.I) • F z - ((fderiv ℝ χ z) Complex.I) • c)
      = χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)
    module
  exact hSob humem hucs hxweak hyweak hgxumem hgyumem

set_option maxHeartbeats 400000 in
-- The recentring average-Jensen + `(1,1)`-Poincaré chain is a single self-contained
-- elaboration, so it needs a modestly raised heartbeat budget.
/-- **Auxiliary for N1: the cutoff commutator bound.** The `L¹`-mass over the doubled ball
`2B = ball x (2r)` of the oscillation of `F` about its **inner** average `c = ⨍_B F` is
controlled by `r` times the full-gradient `L¹`-mass over `2B`:
`∫⁻_{2B} ‖F − c‖ ≤ 5·Cp·(2r)·∫⁻_{2B}(‖Gx‖+‖Gy‖)`, where `Cp` is the `(1,1)`-Poincaré constant.
Proof: the `(1,1)`-Poincaré (`poincare_one_one_ball`) at radius `2r` bounds the oscillation
about the **outer** average `c₂ = ⨍_{2B} F`; the inner/outer recentring costs the factor `5`
via the average-Jensen bound `‖c − c₂‖·|B| ≤ ∫⁻_{2B}‖F − c₂‖` and the planar ratio
`|2B|/|B| = 4`. This is the commutator the N1 cutoff proof must absorb. -/
private theorem cutoff_commutator_bound :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ {F Gx Gy : ℂ → ℂ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          ∫⁻ z in Metric.ball x (2 * r),
              (‖F z - (⨍ w in Metric.ball x r, F w)‖₊ : ℝ≥0∞) ∂volume ≤
            ENNReal.ofReal (5 * Cp * (2 * r)) *
              ∫⁻ z in Metric.ball x (2 * r),
                ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume := by
  obtain ⟨Cp, hCp0, hPoin⟩ := poincare_one_one_ball
  refine ⟨Cp, hCp0, ?_⟩
  intro F Gx Gy hFmem hGxmem hGymem hGxweak hGyweak x r hr
  set B : Set ℂ := Metric.ball x r with hB_def
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  have hVolB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVolBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hVolB2top : volume B2 ≠ ⊤ := measure_ball_lt_top.ne
  set c : ℂ := ⨍ w in B, F w ∂volume with hc_def
  set c2 : ℂ := ⨍ w in B2, F w ∂volume with hc2_def
  set gradInt : ℝ≥0∞ := ∫⁻ z in B2, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume
    with hgradInt_def
  -- Integrability of `F` (hence of `F − c₂`) on the finite-measure ball `B2`.
  have : IsFiniteMeasure (volume.restrict B2) := isFiniteMeasure_restrict.2 hVolB2top
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hVolBtop
  have hF_intB2 : IntegrableOn F B2 volume := (hFmem.restrict B2).integrable (by norm_num)
  have hF_intB : IntegrableOn F B volume := (hFmem.restrict B).integrable (by norm_num)
  have hconst_intB : IntegrableOn (fun _ : ℂ => c2) B volume :=
    integrableOn_const (C := c2) (by rw [hB_def]; exact measure_ball_lt_top.ne)
  have hFc2_intB : IntegrableOn (fun z => F z - c2) B volume := hF_intB.sub hconst_intB
  -- (P) Poincaré at radius `2r`: oscillation about the outer average `c₂`.
  have hOuter : ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume
      ≤ ENNReal.ofReal (Cp * (2 * r)) * gradInt := by
    have := hPoin hFmem hGxmem hGymem hGxweak hGyweak x (2 * r) h2r
    -- `hPoin` gives the oscillation about `⨍_{ball x (2r)} F = c₂`.
    rwa [← hc2_def, ← hB2_def, ← hgradInt_def] at this
  -- (J) Average-Jensen recentring: `‖c − c₂‖·|B| ≤ ∫⁻_{2B} ‖F − c₂‖`.
  -- `c − c₂ = ⨍_B (F − c₂)`, so `‖c − c₂‖·|B| = ‖∫_B (F − c₂)‖ ≤ ∫_B ‖F − c₂‖ ≤ ∫_{2B} ‖F − c₂‖`.
  have hB_sub_B2 : B ⊆ B2 := by
    intro z hz; rw [hB_def, Metric.mem_ball] at hz; rw [hB2_def, Metric.mem_ball]; linarith
  have hBrealpos : 0 < volume.real B :=
    ENNReal.toReal_pos hVolB0 hVolBtop
  -- `c − c₂ = ⨍_B (F − c₂)` by linearity of the set average over `B`.
  have hcdiff : c - c2 = ⨍ w in B, (F w - c2) ∂volume := by
    have hlin : (⨍ w in B, (F w - c2) ∂volume) = (⨍ w in B, F w ∂volume) - c2 := by
      rw [setAverage_eq, setAverage_eq, integral_sub hF_intB hconst_intB,
        setIntegral_const, smul_sub, smul_smul, inv_mul_cancel₀ hBrealpos.ne', one_smul]
    rw [hlin, ← hc_def]
  -- `‖c − c₂‖·|B| ≤ ∫_B ‖F − c₂‖` (Jensen / norm of integral).
  have hJensenReal : ‖c - c2‖ * volume.real B ≤ ∫ w in B, ‖F w - c2‖ ∂volume := by
    rw [hcdiff, setAverage_eq, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg measureReal_nonneg]
    calc (volume.real B)⁻¹ * ‖∫ w in B, (F w - c2) ∂volume‖ * volume.real B
        = ‖∫ w in B, (F w - c2) ∂volume‖ := by
          field_simp
      _ ≤ ∫ w in B, ‖F w - c2‖ ∂volume := norm_integral_le_integral_norm _
  -- Enorm form of Jensen: `‖c − c₂‖ₑ · |B| ≤ ∫⁻_B ‖F − c₂‖ₑ`.
  have hintE_eq : ∫ w in B, ‖F w - c2‖ ∂volume
      = (∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume).toReal := by
    rw [integral_norm_eq_lintegral_enorm hFc2_intB.aestronglyMeasurable]
    simp only [enorm_eq_nnnorm]
  have hintE_lt : ∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume < ⊤ := by
    have := hFc2_intB.2
    rw [hasFiniteIntegral_iff_enorm] at this
    simpa only [enorm_eq_nnnorm] using this
  have hJensenE : (‖c - c2‖₊ : ℝ≥0∞) * volume B ≤ ∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume := by
    have hreal : ‖c - c2‖ * volume.real B ≤
        (∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume).toReal := by rw [← hintE_eq]; exact hJensenReal
    -- Lift the real inequality to `ℝ≥0∞` using `ENNReal.ofReal` and `toReal` round-trips.
    have hlhs_eq : (‖c - c2‖₊ : ℝ≥0∞) * volume B
        = ENNReal.ofReal (‖c - c2‖ * volume.real B) := by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm,
        Measure.real, ENNReal.ofReal_toReal hVolBtop]
    rw [hlhs_eq, ← ENNReal.ofReal_toReal hintE_lt.ne]
    exact ENNReal.ofReal_le_ofReal hreal
  -- `|2B| = 4·|B|` (planar volume scaling).
  have hvol_ratio : volume B2 = 4 * volume B := by
    rw [hB_def, hB2_def, Complex.volume_ball, Complex.volume_ball]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [mul_pow]
    rw [show ENNReal.ofReal 2 ^ 2 = (4 : ℝ≥0∞) from by
      rw [show (2 : ℝ) = ((2 : ℝ≥0∞).toReal) from by norm_num, ENNReal.ofReal_toReal (by norm_num)]
      norm_num]
    ring
  -- (Assemble) `∫⁻_{2B} ‖F − c‖ ≤ 5·∫⁻_{2B} ‖F − c₂‖ ≤ ofReal(5·Cp·2r)·gradInt`.
  have hFc2_intB2 : ∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume
      ≤ ∫⁻ w in B2, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume :=
    lintegral_mono_set hB_sub_B2
  -- Triangle split of the inner-centred oscillation.
  have htriE : ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume
      ≤ (∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume) + (‖c2 - c‖₊ : ℝ≥0∞) * volume B2 := by
    have hpt : ∀ z, (‖F z - c‖₊ : ℝ≥0∞) ≤ (‖F z - c2‖₊ : ℝ≥0∞) + (‖c2 - c‖₊ : ℝ≥0∞) := by
      intro z
      rw [← enorm_eq_nnnorm, ← enorm_eq_nnnorm, ← enorm_eq_nnnorm]
      have : F z - c = (F z - c2) + (c2 - c) := by ring
      rw [this]; exact enorm_add_le _ _
    calc ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume
        ≤ ∫⁻ z in B2, ((‖F z - c2‖₊ : ℝ≥0∞) + (‖c2 - c‖₊ : ℝ≥0∞)) ∂volume :=
          lintegral_mono (fun z => hpt z)
      _ = (∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume)
            + ∫⁻ _ in B2, (‖c2 - c‖₊ : ℝ≥0∞) ∂volume := by
          rw [lintegral_add_right _ measurable_const]
      _ = (∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume) + (‖c2 - c‖₊ : ℝ≥0∞) * volume B2 := by
          rw [setLIntegral_const]
  -- `‖c₂ − c‖ₑ · |2B| ≤ 4·∫⁻_{2B} ‖F − c₂‖`.
  have hcomm2 : (‖c2 - c‖₊ : ℝ≥0∞) * volume B2 ≤ 4 * ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume := by
    have hsymm : (‖c2 - c‖₊ : ℝ≥0∞) = (‖c - c2‖₊ : ℝ≥0∞) := by
      rw [show c2 - c = -(c - c2) from by ring, nnnorm_neg]
    rw [hsymm, hvol_ratio]
    calc (‖c - c2‖₊ : ℝ≥0∞) * (4 * volume B)
        = 4 * ((‖c - c2‖₊ : ℝ≥0∞) * volume B) := by ring
      _ ≤ 4 * ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume := by
          gcongr; exact le_trans hJensenE hFc2_intB2
  -- Combine: total factor `5`, then Poincaré.
  calc ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume
      ≤ (∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume)
          + 4 * ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume := by
        refine le_trans htriE ?_; gcongr
    _ = 5 * ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume := by ring
    _ ≤ 5 * (ENNReal.ofReal (Cp * (2 * r)) * gradInt) := by gcongr
    _ = ENNReal.ofReal (5 * Cp * (2 * r)) * gradInt := by
        rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 from by simp [ENNReal.ofReal_ofNat],
          ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), mul_assoc 5 Cp (2 * r)]

/-- **Auxiliary for N1: the cutoff-partial `L¹` bound.** A single Leibniz partial
`χ·G + (∂_v χ)·(F − c)` (supported in the doubled ball `B2 = ball x (2r)`) has `L¹`-mass
controlled by the `L¹`-mass of `G` over `B2` plus the commutator `(Cχ/r)·∫_{B2}‖F − c‖`:
`∫⁻ ‖χ·G + (∂_v χ)·(F − c)‖ ≤ ∫⁻_{B2} ‖G‖ + (Cχ/r)·∫⁻_{B2} ‖F − c‖`. Proof: pointwise
`‖·‖ₑ ≤ B2.indicator (‖G‖ₑ + (Cχ/r)·‖F − c‖ₑ)` using `|χ| ≤ 1`, `‖∂_v χ‖ ≤ ‖∇χ‖ ≤ Cχ/r`, and
the support containments (off `B2` both `χ` and `∂_v χ` vanish). -/
private theorem cutoff_partial_l1_le {F G : ℂ → ℂ} {c : ℂ} {χ : ℂ → ℝ} {v : ℂ}
    {x : ℂ} {r Cχ : ℝ} (hv : ‖v‖ ≤ 1)
    (hGmeas : AEMeasurable G volume)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hχsupp : Function.support χ ⊆ Metric.ball x (2 * r))
    (hdχsupp : Function.support (fun z => (fderiv ℝ χ z) v) ⊆ Metric.ball x (2 * r))
    (hχgrad : ∀ z, ‖fderiv ℝ χ z‖ ≤ Cχ / r) :
    eLpNorm (fun z => χ z • G z + ((fderiv ℝ χ z) v) • (F z - c)) 1 volume ≤
      (∫⁻ z in Metric.ball x (2 * r), (‖G z‖₊ : ℝ≥0∞) ∂volume)
        + ENNReal.ofReal (Cχ / r)
            * ∫⁻ z in Metric.ball x (2 * r), (‖F z - c‖₊ : ℝ≥0∞) ∂volume := by
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  rw [eLpNorm_one_eq_lintegral_enorm]
  -- Pointwise bound by the `B2`-indicator of `‖G‖ₑ + (Cχ/r)·‖F − c‖ₑ`.
  have hpt : ∀ z, ‖χ z • G z + ((fderiv ℝ χ z) v) • (F z - c)‖ₑ ≤
      B2.indicator (fun z => (‖G z‖ₑ + ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ)) z := by
    intro z
    by_cases hz : z ∈ B2
    · rw [Set.indicator_of_mem hz]
      refine le_trans (enorm_add_le _ _) (add_le_add ?_ ?_)
      · -- `‖χ z • G z‖ₑ = ‖χ z‖ₑ · ‖G z‖ₑ ≤ ‖G z‖ₑ`.
        rw [Complex.real_smul, enorm_mul]
        calc (‖(χ z : ℂ)‖ₑ) * ‖G z‖ₑ ≤ 1 * ‖G z‖ₑ := by
              gcongr
              rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (hχ0 z)]
              exact ENNReal.ofReal_le_one.2 (hχ1 z)
          _ = ‖G z‖ₑ := one_mul _
      · -- `‖(∂_v χ z) • (F z − c)‖ₑ ≤ (Cχ/r)·‖F z − c‖ₑ`.
        rw [Complex.real_smul, enorm_mul,
          show ‖((fderiv ℝ χ z) v : ℂ)‖ₑ = ENNReal.ofReal |(fderiv ℝ χ z) v| from by
            rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]]
        gcongr
        calc |(fderiv ℝ χ z) v| = ‖(fderiv ℝ χ z) v‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ χ z‖ * ‖v‖ := (fderiv ℝ χ z).le_opNorm v
          _ ≤ (Cχ / r) * 1 := by
              refine mul_le_mul (hχgrad z) hv (norm_nonneg _) ?_
              exact le_trans (norm_nonneg _) (hχgrad z)
          _ = Cχ / r := mul_one _
    · -- Off `B2`: `χ z = 0` and `(∂_v χ z) = 0`, so the integrand vanishes.
      rw [Set.indicator_of_notMem hz]
      have hχz : χ z = 0 := Function.notMem_support.1 (fun h => hz (hχsupp h))
      have hdχz : (fderiv ℝ χ z) v = 0 := Function.notMem_support.1 (fun h => hz (hdχsupp h))
      simp [hχz, hdχz]
  calc ∫⁻ z, ‖χ z • G z + ((fderiv ℝ χ z) v) • (F z - c)‖ₑ ∂volume
      ≤ ∫⁻ z, B2.indicator (fun z => ‖G z‖ₑ + ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z ∂volume :=
        lintegral_mono hpt
    _ = ∫⁻ z in B2, (‖G z‖ₑ + ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) ∂volume := by
        rw [lintegral_indicator hB2meas]
    _ = (∫⁻ z in B2, ‖G z‖ₑ ∂volume)
          + ENNReal.ofReal (Cχ / r) * ∫⁻ z in B2, ‖F z - c‖ₑ ∂volume := by
        rw [lintegral_add_left' (hGmeas.enorm.restrict)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = (∫⁻ z in B2, (‖G z‖₊ : ℝ≥0∞) ∂volume)
          + ENNReal.ofReal (Cχ / r) * ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume := by
        simp only [enorm_eq_nnnorm]

/-- **N1 (`sobolevPoincare_ball`).** The **Sobolev–Poincaré inequality on a ball** for a
`W^{1,2}` primitive `F` with weak directional derivatives `Gx` (direction `1`) and `Gy`
(direction `I`).

There is a dimensional constant `C ≥ 0` such that on every ball `B = ball x r` the
`L²`-oscillation of `F` about its average `F_B := ⨍_B F` is controlled by `r` times the
`L¹`-average of the **full gradient** `‖Gx‖ + ‖Gy‖` over the **doubled ball** `2B =
ball x (2r)`:
`(⨍⁻_{B} ‖F − F_B‖²)^(1/2) ≤ C · r · ⨍⁻_{2B} (‖Gx‖ + ‖Gy‖)`.

This is the genuine `L² → L¹` gain. The constant `C` is **independent of the ball**
`(x, r)` and of `F`; it is the endpoint Sobolev constant. The inequality is **asymmetric**
(oscillation over `B`, gradient over the larger `2B`): the cutoff route is the only
Riesz-free derivation available in this development, and it produces exactly this enlarged
form (the same-ball statement would require a `W^{1,1}` extension operator, absent from
Mathlib).

**Why the full gradient.** The naive weight `‖G‖ = ‖½(Gx − I·Gy)‖` (the holomorphic
`∂`-part alone) is **false**: it is blind to the antiholomorphic part `∂̄F = ½(Gx + I·Gy)`.
A localized `F = conj` has `Gx = 1`, `Gy = −I`, so `G ≡ 0` while `∂̄F ≡ 1`, making the
naive RHS vanish below a positive LHS. The genuine `(2,1)` Sobolev–Poincaré inequality
uses the full gradient `‖Gx‖ + ‖Gy‖`, which sees both parts.

*Derivation (via the sound P-stack — the `I₁` Riesz route was unsound).* Form the cutoff
product `u = χ·(F − F_B)` with `χ` adapted to `B` (`χ ≡ 1` on `B`, supported in a fixed
dilate `closedBall x (3r/2) ⊆ 2B`, `|∇χ| ≲ r⁻¹`); its weak partials are
`χ·Gx + (∂₁χ)(F − F_B)` and `χ·Gy + (∂_I χ)(F − F_B)` by the Leibniz rule
`HasWeakDirDeriv.smul_smooth` (with `hasWeakDirDeriv_const` for the centring constant).
Mollify `u` to a `C¹` compactly-supported `w` (P3 `exists_contDiff_approx_W11`), apply the
genuine endpoint Sobolev inequality P1 (`eLpNorm_two_le_eLpNorm_fderiv_one`,
`‖w‖_{L²} ≤ C·‖∇w‖_{L¹}`), and pass `ε → 0` in the `L²` distance
(`sobolev_compactSupport_W11`). Since `χ ≡ 1` on `B`, this bounds `‖F − F_B‖_{L²(B)}` by
`∫_{2B}(‖Gx‖+‖Gy‖)` plus the lower-order commutator `(C/r)·∫_{2B}‖F − F_B‖`. The commutator
is absorbed by the `(1,1)`-Poincaré `poincare_one_one_ball` applied at radius `2r`
(`∫_{2B}‖F − F_{2B}‖ ≤ 8·(2r)·∫_{2B}(‖Gx‖+‖Gy‖)`) after recentering `F_B → F_{2B}` via the
average-Jensen bound `‖F_B − F_{2B}‖ ≤ ⨍_B‖F − F_{2B}‖` (giving the harmless factor `5`).
Converting to `⨍⁻`-averages via the planar `volume_ball = ofReal r² · π` produces the factor
`r`, giving the scale-invariant constant. *Dependency:* P1, P3, `poincare_one_one_ball`,
`sobolev_compactSupport_W11`, `hasWeakDirDeriv_const`. -/
theorem sobolevPoincare_ball :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F Gx Gy : ℂ → ℂ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r,
              (‖F z - (⨍ w in Metric.ball x r, F w)‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
              ^ (1 / (2 : ℝ)) ≤
            ENNReal.ofReal (C * r) *
              (⨍⁻ z in Metric.ball x (2 * r),
                ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume) := by
  classical
  -- The cutoff Sobolev oscillation constant `C₁` (P1, via `cutoff_sobolev_oscL2`), the uniform
  -- cutoff gradient constant `Cχ` (ball-independent), and the commutator constant `Cp`
  -- (`cutoff_commutator_bound`, packaging the `(1,1)`-Poincaré + recentring).
  obtain ⟨C₁, hC₁0, hSob⟩ := cutoff_sobolev_oscL2
  obtain ⟨Cχ, hCχ0, hCut⟩ := exists_cutoff_ball_uniform
  obtain ⟨Cp, hCp0, hComm⟩ := cutoff_commutator_bound
  -- The ball-independent constant. The factor `4·√π` is the planar volume-ratio conversion
  -- `|2B| / |B|^{1/2} = 4·r·√π`; the bracket `1 + Cχ·(2·(5·Cp·2))` collects the gradient term
  -- and the absorbed commutator (`(2·Cχ/r)·(5·Cp·2r)·gradInt`).
  refine ⟨4 * Real.sqrt Real.pi * C₁ * (1 + Cχ * (2 * (5 * Cp * 2))), by positivity, ?_⟩
  intro F Gx Gy hFmem hGxmem hGymem hGxweak hGyweak x r hr
  -- Abbreviations for the two balls and basic measure facts.
  set B : Set ℂ := Metric.ball x r with hB_def
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  have hVolB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVolBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hVolB20 : volume B2 ≠ 0 := (Metric.measure_ball_pos volume x h2r).ne'
  have hVolB2top : volume B2 ≠ ⊤ := measure_ball_lt_top.ne
  -- The centring constant `c := F_B = ⨍_B F`.
  set c : ℂ := ⨍ w in B, F w ∂volume with hc_def
  -- Local integrability facts on the (finite-measure) ball `B2`, needed throughout.
  have hF_intB2 : IntegrableOn F B2 volume := by
    have : IsFiniteMeasure (volume.restrict B2) :=
      isFiniteMeasure_restrict.2 hVolB2top
    exact (hFmem.restrict B2).integrable (by norm_num)
  have hF_intB : IntegrableOn F B volume := by
    have : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.2 hVolBtop
    exact (hFmem.restrict B).integrable (by norm_num)
  -- ====================================================================
  -- (Cut) The cutoff `χ` adapted to `B`, with uniform gradient bound `‖∇χ‖ ≤ Cχ/r`.
  -- ====================================================================
  obtain ⟨χ, hχcd, hχcs, hχ0, hχ1, hχB, hχsupp, hχgrad⟩ := hCut x r hr
  have hχcont : Continuous χ := hχcd.continuous
  -- `tsupport χ ⊆ closedBall x (3r/2) ⊆ B2 = ball x (2r)`.
  have hsupp_sub_B2 : tsupport χ ⊆ B2 := by
    refine hχsupp.trans ?_
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [hB2_def, Metric.mem_ball]
    exact lt_of_le_of_lt hz (by linarith)
  -- ====================================================================
  -- (u) The cutoff product `u = χ·(F − c)`, its weak partials `gxu, gyu`, and the
  -- compactly-supported Sobolev oscillation bound (factored into `cutoff_sobolev_oscL2`).
  -- ====================================================================
  set u : ℂ → ℂ := fun z => χ z • (F z - c) with hu_def
  set gxu : ℂ → ℂ := fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c) with hgxu_def
  set gyu : ℂ → ℂ := fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c) with hgyu_def
  have hSobu : eLpNorm u 2 volume ≤
      ENNReal.ofReal C₁ * (eLpNorm gxu 1 volume + eLpNorm gyu 1 volume) :=
    hSob hFmem hGxmem hGymem hGxweak hGyweak hχcd hχcs
  -- Abbreviation: the full-gradient `L¹`-mass over `2B`.
  set gradInt : ℝ≥0∞ := ∫⁻ z in B2, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume
    with hgradInt_def
  -- ====================================================================
  -- (A) `(∫⁻_B ‖F − c‖²)^{1/2} ≤ eLpNorm u 2`  (since `χ ≡ 1` on `B`).
  -- ====================================================================
  have hu_on_B : ∀ z ∈ B, u z = F z - c := by
    intro z hz
    change χ z • (F z - c) = F z - c
    rw [hχB z (by rw [hB_def] at hz; exact hz)]
    module
  have hLHS_le_u : (∫⁻ z in B, (‖F z - c‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
      ≤ eLpNorm u 2 volume := by
    have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top]
    rw [show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc (∫⁻ z in B, (‖F z - c‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
        = ∫⁻ z in B, (‖u z‖ₑ) ^ (2 : ℝ) ∂volume := by
          refine setLIntegral_congr_fun hBmeas (fun z hz => ?_)
          rw [hu_on_B z hz, ← enorm_eq_nnnorm]
      _ ≤ ∫⁻ z, (‖u z‖ₑ) ^ (2 : ℝ) ∂volume := setLIntegral_le_lintegral _ _
  -- ====================================================================
  -- (B) Gradient + commutator bound:
  --   `eLpNorm gxu 1 + eLpNorm gyu 1 ≤ (1 + Cχ·(5·(2·Cp·2)))·gradInt`.
  -- ====================================================================
  -- (B0) `tsupport (∂_v χ) ⊆ tsupport χ ⊆ B2`, so the cutoff partials are supported in `2B`.
  have hdχ_supp1 : Function.support (fun z => (fderiv ℝ χ z) 1) ⊆ B2 :=
    (subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset (𝕜 := ℝ) 1).trans hsupp_sub_B2)
  have hdχ_suppI : Function.support (fun z => (fderiv ℝ χ z) Complex.I) ⊆ B2 :=
    (subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset (𝕜 := ℝ) Complex.I).trans hsupp_sub_B2)
  have hχ_supp : Function.support χ ⊆ B2 := (subset_tsupport χ).trans hsupp_sub_B2
  -- Abbreviation: the commutator `L¹`-mass over `2B`.
  set commInt : ℝ≥0∞ := ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume with hcommInt_def
  -- (B1) Per-direction `L¹` bounds for the two cutoff partials, via `cutoff_partial_l1_le`.
  have hgxu_le : eLpNorm gxu 1 volume ≤
      (∫⁻ z in B2, (‖Gx z‖₊ : ℝ≥0∞) ∂volume) + ENNReal.ofReal (Cχ / r) * commInt :=
    cutoff_partial_l1_le (by simp) hGxmem.1.aemeasurable hχ0 hχ1 hχ_supp hdχ_supp1 hχgrad
  have hgyu_le : eLpNorm gyu 1 volume ≤
      (∫⁻ z in B2, (‖Gy z‖₊ : ℝ≥0∞) ∂volume) + ENNReal.ofReal (Cχ / r) * commInt :=
    cutoff_partial_l1_le (by simp) hGymem.1.aemeasurable hχ0 hχ1 hχ_supp hdχ_suppI hχgrad
  -- (B2) The commutator bound (Poincaré + recentring).
  have hCommBound : commInt ≤ ENNReal.ofReal (5 * Cp * (2 * r)) * gradInt :=
    hComm hFmem hGxmem hGymem hGxweak hGyweak x r hr
  -- (B3) `∫⁻_{2B} ‖Gx‖ + ∫⁻_{2B} ‖Gy‖ = gradInt`.
  have hsplit_grad : (∫⁻ z in B2, (‖Gx z‖₊ : ℝ≥0∞) ∂volume)
      + ∫⁻ z in B2, (‖Gy z‖₊ : ℝ≥0∞) ∂volume = gradInt := by
    rw [hgradInt_def, ← lintegral_add_left' (hGxmem.1.aemeasurable.enorm.restrict.congr
      (by filter_upwards with z; simp [enorm_eq_nnnorm]))]
  -- (B-assemble) `eLpNorm gxu 1 + eLpNorm gyu 1 ≤ (1 + Cχ·(2·(5·Cp·2)))·gradInt`.
  have hGradTot : eLpNorm gxu 1 volume + eLpNorm gyu 1 volume ≤
      ENNReal.ofReal (1 + Cχ * (2 * (5 * Cp * 2))) * gradInt := by
    have hsum : eLpNorm gxu 1 volume + eLpNorm gyu 1 volume ≤
        gradInt + 2 * (ENNReal.ofReal (Cχ / r) * commInt) := by
      calc eLpNorm gxu 1 volume + eLpNorm gyu 1 volume
          ≤ ((∫⁻ z in B2, (‖Gx z‖₊ : ℝ≥0∞) ∂volume) + ENNReal.ofReal (Cχ / r) * commInt)
              + ((∫⁻ z in B2, (‖Gy z‖₊ : ℝ≥0∞) ∂volume) + ENNReal.ofReal (Cχ / r) * commInt) :=
            add_le_add hgxu_le hgyu_le
        _ = gradInt + 2 * (ENNReal.ofReal (Cχ / r) * commInt) := by
            rw [← hsplit_grad]; ring
    refine le_trans hsum ?_
    -- Absorb the commutator: `2·(Cχ/r)·commInt ≤ 2·(Cχ/r)·ofReal(5Cp·2r)·gradInt`, and the
    -- `r` cancels to give `Cχ·(2·(5·Cp·2))·gradInt`.
    have hrne : r ≠ 0 := hr.ne'
    have hcomm_abs : 2 * (ENNReal.ofReal (Cχ / r) * commInt)
        ≤ ENNReal.ofReal (Cχ * (2 * (5 * Cp * 2))) * gradInt := by
      calc 2 * (ENNReal.ofReal (Cχ / r) * commInt)
          ≤ 2 * (ENNReal.ofReal (Cχ / r) * (ENNReal.ofReal (5 * Cp * (2 * r)) * gradInt)) := by
            gcongr
        _ = ENNReal.ofReal (Cχ * (2 * (5 * Cp * 2))) * gradInt := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
              ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            field_simp
    calc gradInt + 2 * (ENNReal.ofReal (Cχ / r) * commInt)
        ≤ gradInt + ENNReal.ofReal (Cχ * (2 * (5 * Cp * 2))) * gradInt := by
          gcongr
      _ = ENNReal.ofReal (1 + Cχ * (2 * (5 * Cp * 2))) * gradInt := by
          rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
            add_mul, one_mul]
  -- ====================================================================
  -- (C) Chain `LHSint ≤ ofReal(C₁·bracket)·gradInt`, then convert to `⨍⁻`-averages.
  -- ====================================================================
  set bracket : ℝ := 1 + Cχ * (2 * (5 * Cp * 2)) with hbracket_def
  have hbracket0 : 0 ≤ bracket := by rw [hbracket_def]; positivity
  -- `LHSint ≤ ofReal(C₁·bracket)·gradInt`.
  have hLHSint_le : (∫⁻ z in B, (‖F z - c‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
      ≤ ENNReal.ofReal (C₁ * bracket) * gradInt := by
    calc (∫⁻ z in B, (‖F z - c‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
        ≤ eLpNorm u 2 volume := hLHS_le_u
      _ ≤ ENNReal.ofReal C₁ * (eLpNorm gxu 1 volume + eLpNorm gyu 1 volume) := hSobu
      _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal bracket * gradInt) := by gcongr
      _ = ENNReal.ofReal (C₁ * bracket) * gradInt := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₁0]
  -- Volume identities, all as `ENNReal.ofReal` of positive reals.
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
  -- `(volume B)^{1/2} = ofReal(r·√π)`.
  have hVB_half : (volume B) ^ (1 / (2 : ℝ)) = ENNReal.ofReal (r * Real.sqrt Real.pi) := by
    rw [hvolB, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.mul_rpow (by positivity) hpi0.le, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
  have hVB_half_ne0 : (volume B) ^ (1 / (2 : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
    exact ⟨Or.inl hVolB0, Or.inr (by norm_num)⟩
  have hVB_half_top : (volume B) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVolBtop
  -- The constant/volume identity: `ofReal(C₁·bracket)·|2B| = ofReal(C·r)·|B|^{1/2}` with
  -- `C = 4√π·C₁·bracket` (the planar volume-ratio conversion).
  set Cfull : ℝ := 4 * Real.sqrt Real.pi * C₁ * bracket with hCfull_def
  have hkey : ENNReal.ofReal (C₁ * bracket) * volume B2
      = ENNReal.ofReal (Cfull * r) * (volume B) ^ (1 / (2 : ℝ)) := by
    rw [hvolB2, hVB_half, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    -- Real identity: `C₁·bracket·(4r²π) = (4√π·C₁·bracket·r)·(r·√π)`.
    have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi0.le
    rw [hCfull_def]
    linear_combination (-(4 : ℝ) * C₁ * bracket * r ^ 2) * hsqrt
  -- Convert the goal's `⨍⁻`-averages to `∫⁻ / volume` and finish.
  rw [setLAverage_eq, setLAverage_eq, ← hgradInt_def,
    ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
    ENNReal.div_le_iff hVB_half_ne0 hVB_half_top]
  -- The RHS equals `ofReal(C₁·bracket)·gradInt`, dominating `LHSint` by `hLHSint_le`.
  refine le_trans hLHSint_le (le_of_eq ?_)
  rw [mul_comm (ENNReal.ofReal (Cfull * r)) (gradInt / volume B2), mul_assoc, ← hkey,
    ← mul_assoc, mul_comm (gradInt / volume B2), mul_assoc,
    ENNReal.div_mul_cancel hVolB20 hVolB2top]


end NoWanderingDomains
