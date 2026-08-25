/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.LengthArea.Mollification
import NoWanderingDomains.Analysis.WeakLimits.WeakCompactness
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Null-Lagrangian structure of the Jacobian

The real Jacobian determinant of a planar map `f : ℂ → ℂ` is a *null Lagrangian*: tested
against a smooth compactly supported function it integrates by parts into an expression
that is first order in `f`, linear in `Re f` against the gradient of the test function.
This file fixes the vocabulary for that identity — the coordinate partials `partialX`,
`partialY`, the Jacobian `jacobianWeak` of a pair of (weak) partials, and the
integral-pairing forms `TendstoWeaklyL2` / `TendstoWeaklyL2Loc` of weak `L²` convergence —
and then proves the identity twice: for a `C²` map, and by mollification for a continuous
map with `L²_loc` weak partials. The weak-continuity half of the cluster — the limit passage
`tendsto_integral_jacobianWeak_smul`, the only consumer of the `W^{1,2}` identity, together
with the weighted lower-semicontinuity and weak-derivative limit results — lives in
`NoWanderingDomains.Analysis.WeakLimits.JacobianWeakContinuity.WeakContinuity`.

## Main definitions

* `NoWanderingDomains.partialX` — the partial `∂ₓ h z`, defined as the Fréchet directional
  derivative `(fderiv ℝ h z) 1`. No differentiability is assumed anywhere: at points where
  `h` is not differentiable Mathlib's `fderiv` is `0`, hence so is `partialX h z`.
* `NoWanderingDomains.partialY` — the partial `∂ᵧ h z`, the same construction in the direction
  `Complex.I`: `(fderiv ℝ h z) Complex.I`.
* `NoWanderingDomains.jacobianWeak` — the Jacobian written in a pair `(gx, gy)` standing for
  `(∂ₓf, ∂ᵧf)`: `(gx z).re * (gy z).im − (gy z).re * (gx z).im`. Note the order in the
  subtracted term: it is `Re gy` times `Im gx`.
* `NoWanderingDomains.TendstoWeaklyL2` — weak `L²(volume)` convergence `hₙ ⇀ h`, phrased as
  convergence of the bilinear pairings `∫ hₙ z * ψ z → ∫ h z * ψ z` (a plain complex
  product, no conjugation) for every test function `ψ` with `MemLp ψ 2 volume`.
* `NoWanderingDomains.TendstoWeaklyL2Loc` — the same pairing convergence, but demanded only for
  test functions that are `MemLp ψ 2 volume` *and* `HasCompactSupport ψ`. This is the notion
  used throughout, since a merely locally square-integrable sequence has no global pairing.

## Main results

* `NoWanderingDomains.det_fderiv_eq_partials` — for every `f` and `z`, with no hypotheses,
  `(fderiv ℝ f z).det = (∂ₓf z).re * (∂ᵧf z).im − (∂ᵧf z).re * (∂ₓf z).im`; that is, the
  determinant of the differential is `jacobianWeak (partialX f) (partialY f) z`.
* `NoWanderingDomains.integral_jacobian_smul_eq` — the null-Lagrangian integration-by-parts
  identity in the `C²` case. For `f` with `ContDiff ℝ 2 f` and a real test function `φ` with
  `ContDiff ℝ ∞ φ` and `HasCompactSupport φ`,
  `∫ (fderiv ℝ f z).det * φ z = ∫ (f z).re * ((∂ₓf z).im * ∂ᵧφ z − (∂ᵧf z).im * ∂ₓφ z)`,
  where `∂ₓφ z = (fderiv ℝ φ z) 1` and `∂ᵧφ z = (fderiv ℝ φ z) Complex.I`. The `C²`
  hypothesis is used exactly to cancel the mixed second partials of `Im f` (Clairaut).
* `NoWanderingDomains.integral_jacobianWeak_smul_eq` — the same identity with the weak
  partials in place of the classical ones. For `f` continuous, a.e. differentiable and in
  `MemW12loc`, with `HasWeakGradient gx gy f Set.univ` and both `MemLpLocOn gx 2 Set.univ`,
  `MemLpLocOn gy 2 Set.univ`, and for `φ` smooth with compact support,
  `∫ jacobianWeak gx gy z * φ z = ∫ (f z).re * ((gx z).im * ∂ᵧφ z − (gy z).im * ∂ₓφ z)`.
  Proved by mollifying with normed `ContDiffBump`s: each mollification is `C²`, so the `C²`
  identity applies to it, and its partials are the mollified `gx`, `gy`. Continuity of `f` and
  the two `L²_loc` bounds give `L²`-convergence on `tsupport φ` of the mollifications of `f`,
  `gx`, `gy`, which is what carries both sides of that identity to the limit.

## Unfolding and plumbing lemmas

* `NoWanderingDomains.partialX_def`, `NoWanderingDomains.partialY_def` — the two `rfl` unfolding
  lemmas. `partialX` and `partialY` are marked `attribute [irreducible]` right after they are
  defined, so these lemmas are the intended route back to `fderiv`.
* `NoWanderingDomains.jacobianWeak_def` — the `rfl` unfolding lemma for `jacobianWeak`.
* `NoWanderingDomains.TendstoWeaklyL2.tendstoWeaklyL2Loc` — global weak `L²` convergence implies
  the compactly-supported-test form, by restricting the class of test functions.
* `NoWanderingDomains.TendstoWeaklyL2Loc.comp_strictMono` — local weak `L²` convergence is
  inherited by any subsequence `fun k => hₙ (φ k)` with `StrictMono φ`; this is what lets two
  successive weak-compactness extractions be combined.
-/

open MeasureTheory Complex
open scoped ContDiff ENNReal NNReal

namespace NoWanderingDomains

variable {f : ℂ → ℂ} {φ : ℂ → ℝ}

/-- The coordinate partial derivative `∂ₓ h` as the Fréchet directional derivative in
the direction `1`. -/
noncomputable def partialX (h : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ h z) 1

/-- The coordinate partial derivative `∂ᵧ h` as the Fréchet directional derivative in
the direction `I`. -/
noncomputable def partialY (h : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ h z) Complex.I

/-- Unfolding lemma for `partialX`: `∂ₓ h z = (Df z) 1`. -/
theorem partialX_def (h : ℂ → ℂ) (z : ℂ) : partialX h z = (fderiv ℝ h z) 1 := rfl

/-- Unfolding lemma for `partialY`: `∂ᵧ h z = (Df z) I`. -/
theorem partialY_def (h : ℂ → ℂ) (z : ℂ) : partialY h z = (fderiv ℝ h z) Complex.I := rfl

attribute [irreducible] partialX partialY

/-- The Jacobian determinant written in a pair of weak partial derivatives
`(gx, gy)` standing for `(∂ₓf, ∂ᵧf)`: `(Re gx)(Im gy) − (Re gy)(Im gx)`. When
`gx = ∂ₓf` and `gy = ∂ᵧf` this equals the real determinant of the differential
`Df`. -/
def jacobianWeak (gx gy : ℂ → ℂ) (z : ℂ) : ℝ :=
  (gx z).re * (gy z).im - (gy z).re * (gx z).im

/-- Unfolding lemma for `jacobianWeak`: `J gx gy z = (gx z).re·(gy z).im − (gy z).re·(gx z).im`. -/
theorem jacobianWeak_def (gx gy : ℂ → ℂ) (z : ℂ) :
    jacobianWeak gx gy z = (gx z).re * (gy z).im - (gy z).re * (gx z).im := rfl

/-- **Weak `L²` convergence tested against `L²` functions.** The sequence `hₙ`
converges weakly in `L²(volume)` to `h` if the pairing `∫ (hₙ z) * ψ z` converges to
`∫ (h z) * ψ z` for every complex `L²(volume)` test function `ψ`. This is the concrete
integral-pairing form of weak `L²` convergence; the Hilbert inner-product convergence
of `exists_weak_subseq_of_bounded` specializes to it. -/
def TendstoWeaklyL2 (hₙ : ℕ → ℂ → ℂ) (h : ℂ → ℂ) : Prop :=
  ∀ ψ : ℂ → ℂ, MemLp ψ 2 volume →
    Filter.Tendsto (fun n => ∫ z, hₙ n z * ψ z) Filter.atTop (nhds (∫ z, h z * ψ z))

/-- **Local weak `L²` convergence tested against compactly supported `L²` functions.**
The sequence `hₙ` converges weakly in `L²_loc` to `h` if the pairing `∫ (hₙ z) * ψ z`
converges to `∫ (h z) * ψ z` for every complex `L²(volume)` test function `ψ` with
compact support. This is the correct notion for sequences that are only locally
square-integrable (a globally `L²` pairing need not even be defined for them): every
divergence-structure test that arises from a compactly supported smooth weight is of
this compactly-supported form, so the null-Lagrangian cluster below runs on it. -/
def TendstoWeaklyL2Loc (hₙ : ℕ → ℂ → ℂ) (h : ℂ → ℂ) : Prop :=
  ∀ ψ : ℂ → ℂ, MemLp ψ 2 volume → HasCompactSupport ψ →
    Filter.Tendsto (fun n => ∫ z, hₙ n z * ψ z) Filter.atTop (nhds (∫ z, h z * ψ z))

/-- Global weak `L²` convergence implies the compactly-supported-test form. -/
theorem TendstoWeaklyL2.tendstoWeaklyL2Loc {hₙ : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hw : TendstoWeaklyL2 hₙ h) : TendstoWeaklyL2Loc hₙ h :=
  fun ψ hψ _ => hw ψ hψ

/-- Local weak `L²` convergence passes to subsequences. -/
theorem TendstoWeaklyL2Loc.comp_strictMono {hₙ : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hw : TendstoWeaklyL2Loc hₙ h) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoWeaklyL2Loc (fun k => hₙ (φ k)) h :=
  fun ψ hψ hcs => (hw ψ hψ hcs).comp hφ.tendsto_atTop

/-- The real determinant of the differential in the two coordinate partial
derivatives: `det (Df) = (∂ₓ(Re f))(∂ᵧ(Im f)) − (∂ᵧ(Re f))(∂ₓ(Im f))`. Equivalently,
in terms of the complex partials `∂ₓf`, `∂ᵧf` this is
`(∂ₓf).re·(∂ᵧf).im − (∂ᵧf).re·(∂ₓf).im`. -/
theorem det_fderiv_eq_partials (f : ℂ → ℂ) (z : ℂ) :
    (fderiv ℝ f z).det = (partialX f z).re * (partialY f z).im
      - (partialY f z).re * (partialX f z).im := by
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  have key : ∀ M : ℂ →ₗ[ℝ] ℂ, LinearMap.det M
      = (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI M).det := fun M =>
    (LinearMap.det_toMatrix Complex.basisOneI M).symm
  have hdet : A.det = (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
    rw [ContinuousLinearMap.det, key]
    have hb0 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 0 = (1 : ℂ) := by
      simp [Complex.coe_basisOneI]
    have hb1 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 1 = Complex.I := by
      simp [Complex.coe_basisOneI]
    have c00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 0 = (A 1).re := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
      rfl
    have c10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 0 = (A 1).im := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
      rfl
    have c01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 1 = (A Complex.I).re := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
      rfl
    have c11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 1 = (A Complex.I).im := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
      rfl
    have h0 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ))
        = !![(A 1).re, (A Complex.I).re; (A 1).im, (A Complex.I).im] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
          Matrix.cons_val_fin_one] <;>
        first | exact c00 | exact c01 | exact c10 | exact c11
    rw [h0, Matrix.det_fin_two_of]; ring
  have hx : partialX f z = A 1 := by rw [partialX_def, hA]
  have hy : partialY f z = A Complex.I := by rw [partialY_def, hA]
  rw [hx, hy, hdet]; ring

/-- **Null-Lagrangian integration-by-parts identity, `C²` case.** For a
twice–continuously-differentiable `f : ℂ → ℂ` and a smooth compactly supported real
test function `φ`, the Jacobian determinant integrates by parts to a first-order
expression against `Re f`:
`∫ (J f)·φ = ∫ (Re f)·(∂ₓ(Im f)·∂ᵧφ − ∂ᵧ(Im f)·∂ₓφ)`.

The `C²` hypothesis is used exactly to cancel the mixed second partials
`∂ᵧ∂ₓ(Im f) = ∂ₓ∂ᵧ(Im f)` (Clairaut / `second_derivative_symmetric`). -/
theorem integral_jacobian_smul_eq (hf : ContDiff ℝ 2 f)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ z, (fderiv ℝ f z).det * φ z
      = ∫ z, (f z).re * ((partialX f z).im * (fderiv ℝ φ z) Complex.I
          - (partialY f z).im * (fderiv ℝ φ z) 1) := by
  -- Real components of `f`; both are `C²`.
  set u : ℂ → ℝ := fun z => (f z).re with hu_def
  set p : ℂ → ℝ := fun z => (f z).im with hp_def
  have hu_c2 : ContDiff ℝ 2 u := by
    rw [hu_def]
    have := Complex.reCLM.contDiff.comp hf
    simpa [Function.comp] using! this
  have hp_c2 : ContDiff ℝ 2 p := by
    rw [hp_def]
    have := Complex.imCLM.contDiff.comp hf
    simpa [Function.comp] using! this
  have hu_diff : Differentiable ℝ u := hu_c2.differentiable (by norm_num)
  have hp_diff : Differentiable ℝ p := hp_c2.differentiable (by norm_num)
  -- `fderiv ℝ p` is `C¹`, hence differentiable.
  have hfp_c1 : ContDiff ℝ 1 (fderiv ℝ p) := hp_c2.fderiv_right (by norm_num)
  have hfp_diff : Differentiable ℝ (fderiv ℝ p) := hfp_c1.differentiable (by norm_num)
  -- The two first partials of `p`, with their smoothness.
  set px : ℂ → ℝ := fun z => (fderiv ℝ p z) 1 with hpx_def
  set py : ℂ → ℝ := fun z => (fderiv ℝ p z) Complex.I with hpy_def
  have hpx_c1 : ContDiff ℝ 1 px := by
    rw [hpx_def]; exact hfp_c1.clm_apply contDiff_const
  have hpy_c1 : ContDiff ℝ 1 py := by
    rw [hpy_def]; exact hfp_c1.clm_apply contDiff_const
  have hpx_diff : Differentiable ℝ px := by
    rw [hpx_def]; exact fun z => (hfp_diff z).clm_apply (differentiableAt_const _)
  have hpy_diff : Differentiable ℝ py := by
    rw [hpy_def]; exact fun z => (hfp_diff z).clm_apply (differentiableAt_const _)
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ_c1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hu_c1 : ContDiff ℝ 1 u := hu_c2.of_le (by norm_num)
  -- Bridge: directional partials of `u`, `p` are the components of those of `f`.
  have hbridge_re : ∀ (z w : ℂ), (fderiv ℝ u z) w = ((fderiv ℝ f z) w).re := by
    intro z w
    have hfd : HasFDerivAt f (fderiv ℝ f z) z := (hf.differentiable (by norm_num) z).hasFDerivAt
    have hcomp : HasFDerivAt u (Complex.reCLM.comp (fderiv ℝ f z)) z := by
      rw [hu_def]
      have := (Complex.reCLM.hasFDerivAt (x := f z)).comp z hfd
      simpa [Function.comp] using! this
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  have hbridge_im : ∀ (z w : ℂ), (fderiv ℝ p z) w = ((fderiv ℝ f z) w).im := by
    intro z w
    have hfd : HasFDerivAt f (fderiv ℝ f z) z := (hf.differentiable (by norm_num) z).hasFDerivAt
    have hcomp : HasFDerivAt p (Complex.imCLM.comp (fderiv ℝ f z)) z := by
      rw [hp_def]
      have := (Complex.imCLM.hasFDerivAt (x := f z)).comp z hfd
      simpa [Function.comp] using! this
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
  -- Differentiating the evaluation of `fderiv ℝ p` at a constant direction.
  have hclm_apply : ∀ (c d z : ℂ),
      (fderiv ℝ (fun w => (fderiv ℝ p w) c) z) d = ((fderiv ℝ (fderiv ℝ p) z) d) c := by
    intro c d z
    have hc : HasFDerivAt (fderiv ℝ p) (fderiv ℝ (fderiv ℝ p) z) z := (hfp_diff z).hasFDerivAt
    have hcst : HasFDerivAt (fun _ : ℂ => c) (0 : ℂ →L[ℝ] ℂ) z := hasFDerivAt_const c z
    rw [(hc.clm_apply hcst).fderiv]
    simp
  -- A coordinate partial of a compactly supported `C¹` real function integrates to `0`.
  have hvanish : ∀ (G : ℂ → ℝ) (w : ℂ), ContDiff ℝ 1 G → HasCompactSupport G →
      ∫ z, (fderiv ℝ G z) w = 0 := by
    intro G w hG hGc
    set cf : ℂ → ℝ := fun _ => (1 : ℝ) with hcf
    have hGcont : Continuous G := hG.continuous
    have hdcont : Continuous (fun z => (fderiv ℝ G z) w) :=
      (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hdcs : HasCompactSupport (fun z => (fderiv ℝ G z) w) :=
      HasCompactSupport.fderiv_apply ℝ hGc w
    have h1 : Integrable (fun z => (fderiv ℝ cf z) w • G z) volume := by
      have he : (fun z => (fderiv ℝ cf z) w • G z) = fun _ => (0 : ℝ) := by
        funext z; simp [hcf]
      rw [he]; exact integrable_zero _ _ _
    have h2 : Integrable (fun z => cf z • (fderiv ℝ G z) w) volume := by
      have he : (fun z => cf z • (fderiv ℝ G z) w) = fun z => (fderiv ℝ G z) w := by
        funext z; simp [hcf]
      rw [he]; exact hdcont.integrable_of_hasCompactSupport hdcs
    have h3 : Integrable (fun z => cf z • G z) volume := by
      have he : (fun z => cf z • G z) = G := by funext z; simp [hcf]
      rw [he]; exact hGcont.integrable_of_hasCompactSupport hGc
    have hdf1 : ∀ x ∈ tsupport G, DifferentiableAt ℝ cf x :=
      fun x _ => (differentiable_const (1 : ℝ)).differentiableAt
    have hdf2 : ∀ x ∈ tsupport cf, DifferentiableAt ℝ G x :=
      fun x _ => (hG.differentiable (by norm_num)).differentiableAt
    have L := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h3 hdf1 hdf2
    have hrw1 : (fun z => cf z • (fderiv ℝ G z) w) = fun z => (fderiv ℝ G z) w := by
      funext z; simp [hcf]
    have hrw2 : (fun z => (fderiv ℝ cf z) w • G z) = fun _ => (0 : ℝ) := by
      funext z; simp [hcf]
    rw [hrw1, hrw2] at L
    simpa using L
  -- The two divergence fluxes: `P` is differentiated in `x`, `Q` in `y`.
  set P : ℂ → ℝ := fun z => u z * py z * φ z with hP_def
  set Q : ℂ → ℝ := fun z => u z * px z * φ z with hQ_def
  have hP_c1 : ContDiff ℝ 1 P := by
    rw [hP_def]; exact (hu_c1.mul hpy_c1).mul hφ_c1
  have hQ_c1 : ContDiff ℝ 1 Q := by
    rw [hQ_def]; exact (hu_c1.mul hpx_c1).mul hφ_c1
  have hP_cs : HasCompactSupport P := by
    rw [hP_def]; exact hφc.mul_left
  have hQ_cs : HasCompactSupport Q := by
    rw [hQ_def]; exact hφc.mul_left
  -- Product rule for a triple product, evaluated at a direction `v`.
  have htriple : ∀ (a b c : ℂ → ℝ) (z v : ℂ), DifferentiableAt ℝ a z → DifferentiableAt ℝ b z →
      DifferentiableAt ℝ c z →
      (fderiv ℝ (fun z => a z * b z * c z) z) v
        = (fderiv ℝ a z) v * b z * c z + a z * (fderiv ℝ b z) v * c z
          + a z * b z * (fderiv ℝ c z) v := by
    intro a b c z v ha hb hc
    have hab : DifferentiableAt ℝ (fun z => a z * b z) z := ha.mul hb
    rw [show (fun z => a z * b z * c z) = (fun z => a z * b z) * c from rfl]
    rw [fderiv_mul hab hc]
    rw [show (fun z => a z * b z) = a * b from rfl, fderiv_mul ha hb]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- Pointwise divergence identity: the second derivatives of `p` cancel by Clairaut.
  have hpt : ∀ z, ((fderiv ℝ u z) 1 * py z - (fderiv ℝ u z) Complex.I * px z) * φ z
      = ((fderiv ℝ P z) 1 - (fderiv ℝ Q z) Complex.I)
        + u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) := by
    intro z
    have hdP := htriple u py φ z 1 (hu_diff z) (hpy_diff z) (hφ_diff z)
    have hdQ := htriple u px φ z Complex.I (hu_diff z) (hpx_diff z) (hφ_diff z)
    rw [hP_def, hQ_def, hdP, hdQ]
    have hmix1 : (fderiv ℝ py z) 1 = ((fderiv ℝ (fderiv ℝ p) z) 1) Complex.I := by
      rw [hpy_def]; exact hclm_apply Complex.I 1 z
    have hmix2 : (fderiv ℝ px z) Complex.I = ((fderiv ℝ (fderiv ℝ p) z) Complex.I) 1 := by
      rw [hpx_def]; exact hclm_apply 1 Complex.I z
    have hclairaut : ((fderiv ℝ (fderiv ℝ p) z) 1) Complex.I
        = ((fderiv ℝ (fderiv ℝ p) z) Complex.I) 1 := by
      have hff : ∀ y, HasFDerivAt p (fderiv ℝ p y) y := fun y => (hp_diff y).hasFDerivAt
      have hff' : HasFDerivAt (fderiv ℝ p) (fderiv ℝ (fderiv ℝ p) z) z :=
        (hfp_diff z).hasFDerivAt
      exact second_derivative_symmetric hff hff' 1 Complex.I
    rw [hmix1, hmix2, hclairaut]
    ring
  -- The determinant integrand in terms of the real partials.
  have hdet_eq : ∀ z, (fderiv ℝ f z).det * φ z
      = ((fderiv ℝ u z) 1 * py z - (fderiv ℝ u z) Complex.I * px z) * φ z := by
    intro z
    rw [det_fderiv_eq_partials f z]
    have h1 : (partialX f z).re = (fderiv ℝ u z) 1 := by
      simp only [partialX_def]; exact (hbridge_re z 1).symm
    have h2 : (partialY f z).im = py z := by
      simp only [partialY_def, hpy_def]; exact (hbridge_im z Complex.I).symm
    have h3 : (partialY f z).re = (fderiv ℝ u z) Complex.I := by
      simp only [partialY_def]; exact (hbridge_re z Complex.I).symm
    have h4 : (partialX f z).im = px z := by
      simp only [partialX_def, hpx_def]; exact (hbridge_im z 1).symm
    rw [h1, h2, h3, h4]
  -- The target right-hand integrand in terms of the real partials.
  have hrhs_eq : ∀ z, (f z).re * ((partialX f z).im * (fderiv ℝ φ z) Complex.I
        - (partialY f z).im * (fderiv ℝ φ z) 1)
      = u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) := by
    intro z
    have h4 : (partialX f z).im = px z := by
      simp only [partialX_def, hpx_def]; exact (hbridge_im z 1).symm
    have h2 : (partialY f z).im = py z := by
      simp only [partialY_def, hpy_def]; exact (hbridge_im z Complex.I).symm
    rw [h4, h2, hu_def]
  -- Integrability of the flux divergence and of the first-order remainder.
  have hintP : Integrable (fun z => (fderiv ℝ P z) 1) volume := by
    have hcP : Continuous (fun z => (fderiv ℝ P z) 1) :=
      (hP_c1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcP.integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply ℝ hP_cs 1)
  have hintQ : Integrable (fun z => (fderiv ℝ Q z) Complex.I) volume := by
    have hcQ : Continuous (fun z => (fderiv ℝ Q z) Complex.I) :=
      (hQ_c1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcQ.integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply ℝ hQ_cs Complex.I)
  have hintR : Integrable (fun z =>
      u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1)) volume := by
    have hcφI : Continuous (fun z => (fderiv ℝ φ z) Complex.I) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcφ1 : Continuous (fun z => (fderiv ℝ φ z) 1) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcont : Continuous (fun z =>
        u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1)) :=
      hu_c2.continuous.mul ((hpx_c1.continuous.mul hcφI).sub (hpy_c1.continuous.mul hcφ1))
    have hcs : HasCompactSupport (fun z =>
        u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1)) := by
      have hsI : HasCompactSupport (fun z => px z * (fderiv ℝ φ z) Complex.I) :=
        (HasCompactSupport.fderiv_apply ℝ hφc Complex.I).mul_left
      have hs1 : HasCompactSupport (fun z => py z * (fderiv ℝ φ z) 1) :=
        (HasCompactSupport.fderiv_apply ℝ hφc 1).mul_left
      have hsub : HasCompactSupport (fun z =>
          px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) := by
        simpa [sub_eq_add_neg] using! hsI.add hs1.neg
      exact hsub.mul_left
    exact hcont.integrable_of_hasCompactSupport hcs
  -- Assemble: integrate the pointwise identity; the flux terms vanish.
  calc ∫ z, (fderiv ℝ f z).det * φ z
      = ∫ z, (((fderiv ℝ P z) 1 - (fderiv ℝ Q z) Complex.I)
          + u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1)) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hdet_eq z, hpt z]
    _ = (∫ z, ((fderiv ℝ P z) 1 - (fderiv ℝ Q z) Complex.I))
          + ∫ z, u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) :=
        integral_add (hintP.sub hintQ) hintR
    _ = ∫ z, u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) := by
        have hsplit : (∫ z, ((fderiv ℝ P z) 1 - (fderiv ℝ Q z) Complex.I))
            = (∫ z, (fderiv ℝ P z) 1) - ∫ z, (fderiv ℝ Q z) Complex.I :=
          integral_sub hintP hintQ
        rw [hsplit, hvanish P 1 hP_c1 hP_cs, hvanish Q Complex.I hQ_c1 hQ_cs]
        simp
    _ = ∫ z, (f z).re * ((partialX f z).im * (fderiv ℝ φ z) Complex.I
          - (partialY f z).im * (fderiv ℝ φ z) 1) := by
        apply integral_congr_ae
        filter_upwards with z
        exact (hrhs_eq z).symm

set_option maxHeartbeats 400000 in
-- This mollification-and-limit proof carries a large local context (four Hölder
-- estimates, two dominating sequences, per-`n` integrability), so the elaboration
-- of its `calc` chains exceeds the default heartbeat budget.
/-- **Null-Lagrangian identity, `W^{1,2}` case.** For a continuous `W^{1,2}_loc`
map `f` with weak partial derivatives `gx` (direction `1`) and `gy` (direction `I`),
both locally `L²`, the weak Jacobian integrates by parts against a smooth compactly
supported real test function `φ`:
`∫ (jacobianWeak gx gy)·φ = ∫ (Re f)·((Im gx)·∂ᵧφ − (Im gy)·∂ₓφ)`.

Obtained from `integral_jacobian_smul_eq` by mollification: the mollifications `fε` are
`C^∞`, converge locally uniformly to `f`, and their differentials converge to `(gx, gy)`
in `L²_loc`; the quadratic left-hand side and the bilinear right-hand side both pass to
the limit. -/
theorem integral_jacobianWeak_smul_eq (hfcont : Continuous f)
    (_hdiff : ∀ᵐ z, DifferentiableAt ℝ f z) (_hW12 : MemW12loc f)
    {gx gy : ℂ → ℂ} (hg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ z, jacobianWeak gx gy z * φ z
      = ∫ z, (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
          - (gy z).im * (fderiv ℝ φ z) 1) := by
  classical
  -- The support of the test function and an enclosing ball.
  set K : Set ℂ := tsupport φ with hK_def
  have hKc : IsCompact K := hφc
  have hKm : MeasurableSet K := (isClosed_tsupport φ).measurableSet
  obtain ⟨R, hKR⟩ := hKc.isBounded.subset_ball (0 : ℂ)
  have hK2 : K ⊆ Metric.ball (0 : ℂ) (R + 2) :=
    hKR.trans (Metric.ball_subset_ball (by linarith))
  -- Local integrability of `f`, `gx`, `gy`.
  have hfLI : LocallyIntegrable f := hfcont.locallyIntegrable
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ → LocallyIntegrable g := by
    intro g hgl
    rw [← locallyIntegrableOn_univ, locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hgl k (Set.subset_univ _) hk).mono_exponent (by norm_num))
  have hgxLI : LocallyIntegrable gx := memLpLoc_to_loc hgx
  have hgyLI : LocallyIntegrable gy := memLpLoc_to_loc hgy
  have hfLp : MemLpLocOn f 2 Set.univ := by
    intro k _ hkc
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
    obtain ⟨Cf', hCf'⟩ := hkc.exists_bound_of_continuousOn hfcont.continuousOn
    refine MemLp.of_bound hfcont.aestronglyMeasurable.restrict Cf' ?_
    rw [ae_restrict_iff' hkc.isClosed.measurableSet]
    exact ae_of_all _ hCf'
  -- The mollifier sequence, with outer radius tending to `0`.
  set φb : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨((n : ℝ) + 2)⁻¹, 2 * ((n : ℝ) + 2)⁻¹, by positivity, by
      have h2 : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
      linarith⟩ with hφb_def
  have hrout : Filter.Tendsto (fun n => (φb n).rOut) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h3 := h1.inv_tendsto_atTop.const_mul (2 : ℝ)
    have he : (fun n => (φb n).rOut) = fun n : ℕ => 2 * ((n : ℝ) + 2)⁻¹ := rfl
    rw [he]
    simpa using h3
  set ρ : ℕ → ℂ → ℝ := fun n => (φb n).normed volume with hρ_def
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φb n).contDiff_normed (n := ⊤)
  have hρcs : ∀ n, HasCompactSupport (ρ n) := fun n => (φb n).hasCompactSupport_normed
  -- Smoothness and continuity of the mollifications.
  have hFC2 : ∀ n, ContDiff ℝ 2
      (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun n => by
    have := HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρcs n) ((φb n).contDiff_normed (n := 2)) hfLI
    exact_mod_cast this
  have hXc : ∀ n, Continuous
      (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρcs n)
      ((φb n).contDiff_normed (n := 0)).continuous hgxLI
  have hYc : ∀ n, Continuous
      (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρcs n)
      ((φb n).contDiff_normed (n := 0)).continuous hgyLI
  have hFc : ∀ n, Continuous
      (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun n =>
    (hFC2 n).continuous
  -- The two partial derivatives of the mollification are the mollified weak partials.
  have hpx : ∀ n z, partialX (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
      = convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z := fun n z => by
    rw [partialX_def]
    exact fderiv_convolution_normed_apply_eq hg.1 hfLI hgxLI (hρsm n) (hρcs n) z
  have hpy : ∀ n z, partialY (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
      = convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z := fun n z => by
    rw [partialY_def]
    exact fderiv_convolution_normed_apply_eq hg.2 hfLI hgyLI (hρsm n) (hρcs n) z
  -- The `C²` identity applied to each mollification, rewritten through the identified partials.
  have hJ1 : ∀ n, ∫ z, (fderiv ℝ (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) z).det * φ z
      = ∫ z, (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((partialX (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z).im
              * (fderiv ℝ φ z) Complex.I
            - (partialY (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z).im
              * (fderiv ℝ φ z) 1) := fun n =>
    integral_jacobian_smul_eq (hFC2 n) hφ hφc
  have hAB : ∀ n, ∫ z, jacobianWeak
        (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
      = ∫ z, (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1) := by
    intro n
    have h1 : (fun z => jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z)
        = fun z => (fderiv ℝ (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ)
            volume) z).det * φ z := by
      funext z
      rw [det_fderiv_eq_partials (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) z, hpx n z, hpy n z, jacobianWeak_def]
    have h2 : (fun z => (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((partialX (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z).im
              * (fderiv ℝ φ z) Complex.I
            - (partialY (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z).im
              * (fderiv ℝ φ z) 1))
        = fun z => (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1) := by
      funext z; rw [hpx n z, hpy n z]
    rw [h1, hJ1 n, h2]
  -- Truncation of a locally-`L²` function to a global `L²` function.
  have htrunc : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ →
      MemLp ((Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume := by
    intro h hh
    rw [memLp_indicator_iff_restrict measurableSet_ball]
    exact (hh (Metric.closedBall 0 (R + 2)) (Set.subset_univ _)
      (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  -- Squared `eLpNorm` as a squared-`enorm` integral.
  have heLpSq : ∀ (μ : Measure ℂ) (h : ℂ → ℂ),
      (eLpNorm h 2 μ) ^ 2 = ∫⁻ z, ‖h z‖ₑ ^ 2 ∂μ := by
    intro μ h
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num]
    have hin : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ z, ‖h z‖ₑ ^ 2 ∂μ := by
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.rpow_natCast (‖h z‖ₑ) 2]; norm_num
    rw [hin, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  -- Convolution on `K` only sees the truncation once the bump radius is `≤ 1`.
  have hconv_trunc : ∀ (h : ℂ → ℂ), ∀ n, (φb n).rOut ≤ 1 → ∀ z ∈ K,
      convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume z
        = convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro h n hr1 z hz
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    by_cases ht : ρ n t = 0
    · simp [ht]
    · have htsupp : t ∈ Function.support (ρ n) := ht
      simp only [hρ_def] at htsupp
      rw [(φb n).support_normed_eq] at htsupp
      rw [Metric.mem_ball, dist_zero_right] at htsupp
      have hzR : ‖z‖ < R := by
        have := hKR hz
        rwa [Metric.mem_ball, dist_zero_right] at this
      have hmem : z - t ∈ Metric.ball (0 : ℂ) (R + 2) := by
        rw [Metric.mem_ball, dist_zero_right]
        have ht1 : ‖t‖ < 1 := lt_of_lt_of_le htsupp hr1
        calc ‖z - t‖ ≤ ‖z‖ + ‖t‖ := norm_sub_le _ _
          _ < R + 2 := by linarith
      rw [Set.indicator_of_mem hmem]
  -- The `K`-localized `L²` convergence of the mollification to the function.
  have hloc : ∀ (h : ℂ → ℂ), LocallyIntegrable h → MemLpLocOn h 2 Set.univ →
      Filter.Tendsto (fun n => ∫⁻ z in K,
        ‖convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume z - h z‖ₑ ^ 2)
        Filter.atTop (nhds 0) := by
    intro h hLI hLp
    have hT2 : MemLp ((Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume := htrunc hLp
    have hE : Filter.Tendsto (fun n => eLpNorm
        (convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          - (Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume)
        Filter.atTop (nhds 0) :=
      eLpNorm_convolution_normed_sub_tendsto_zero hT2 φb hrout
    have hev : ∀ᶠ n in Filter.atTop, (φb n).rOut ≤ 1 :=
      hrout.eventually (eventually_le_nhds one_pos)
    have hbd : ∀ᶠ n in Filter.atTop, (∫⁻ z in K,
        ‖convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume z - h z‖ₑ ^ 2)
        ≤ (eLpNorm (convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          - (Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume) ^ 2 := by
      filter_upwards [hev] with n hr1
      calc (∫⁻ z in K,
          ‖convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume z - h z‖ₑ ^ 2)
          = ∫⁻ z in K, ‖convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - (Metric.ball (0 : ℂ) (R + 2)).indicator h z‖ₑ ^ 2 := by
            refine setLIntegral_congr_fun hKm fun z hz => ?_
            rw [hconv_trunc h n hr1 z hz, Set.indicator_of_mem (hK2 hz)]
        _ ≤ ∫⁻ z, ‖convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - (Metric.ball (0 : ℂ) (R + 2)).indicator h z‖ₑ ^ 2 :=
            setLIntegral_le_lintegral _ _
        _ = (eLpNorm (convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume
            - (Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume) ^ 2 :=
            (heLpSq volume _).symm
    have hE2 := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hE
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Filter.Eventually.of_forall fun n => zero_le) hbd
    simpa [Function.comp] using! hE2
  have hTf := hloc f hfLI hfLp
  have hTx := hloc gx hgxLI hgx
  have hTy := hloc gy hgyLI hgy
  -- Finite masses of `gx`, `gy` on `K`.
  have hgxK : MemLp gx 2 (volume.restrict K) := hgx K (Set.subset_univ K) hKc
  have hgyK : MemLp gy 2 (volume.restrict K) := hgy K (Set.subset_univ K) hKc
  have hGX : (∫⁻ z in K, ‖gx z‖ₑ ^ 2) < ⊤ := by
    rw [← heLpSq (volume.restrict K) gx]
    exact ENNReal.pow_lt_top hgxK.2
  have hGY : (∫⁻ z in K, ‖gy z‖ₑ ^ 2) < ⊤ := by
    rw [← heLpSq (volume.restrict K) gy]
    exact ENNReal.pow_lt_top hgyK.2
  have hvolK : volume K < ⊤ := hKc.measure_lt_top
  -- The `(a+b)² ≤ 2(a²+b²)` inequality in `ℝ≥0∞`.
  have hsq2 : ∀ a b : ℝ≥0∞, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    intro a b
    have hkey := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (by norm_num : (1 : ℝ) ≤ 2)
    have htwo : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
    rw [htwo] at hkey
    rw [← ENNReal.rpow_natCast (a + b) 2, ← ENNReal.rpow_natCast a 2,
      ← ENNReal.rpow_natCast b 2]
    push_cast
    exact hkey
  -- Cauchy–Schwarz for the lower integral on `K`.
  have holder : ∀ (u v : ℂ → ℝ≥0∞), AEMeasurable u (volume.restrict K) →
      AEMeasurable v (volume.restrict K) →
      ∫⁻ z in K, u z * v z
        ≤ (∫⁻ z in K, u z ^ 2) ^ (1/2 : ℝ) * (∫⁻ z in K, v z ^ 2) ^ (1/2 : ℝ) := by
    intro u v hu hv
    have h2 : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
    have hup : (∫⁻ z in K, u z ^ (2 : ℝ)) = ∫⁻ z in K, u z ^ 2 := by
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.rpow_natCast (u z) 2]; norm_num
    have hvp : (∫⁻ z in K, v z ^ (2 : ℝ)) = ∫⁻ z in K, v z ^ 2 := by
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.rpow_natCast (v z) 2]; norm_num
    have hmain := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K) h2 hu hv
    rw [hup, hvp] at hmain
    exact hmain
  -- Mass comparison: an `L²`-mass within distance `1` of a fixed one is controlled.
  have hmass : ∀ (u g0 : ℂ → ℂ), AEStronglyMeasurable u (volume.restrict K) →
      AEStronglyMeasurable g0 (volume.restrict K) →
      (∫⁻ z in K, ‖u z - g0 z‖ₑ ^ 2) ≤ 1 →
      (∫⁻ z in K, ‖u z‖ₑ ^ 2) ≤ 2 * (1 + ∫⁻ z in K, ‖g0 z‖ₑ ^ 2) := by
    intro u g0 hu hg0 hle
    have hpt : ∀ z, ‖u z‖ₑ ^ 2 ≤ 2 * (‖u z - g0 z‖ₑ ^ 2 + ‖g0 z‖ₑ ^ 2) := by
      intro z
      calc ‖u z‖ₑ ^ 2 = ‖(u z - g0 z) + g0 z‖ₑ ^ 2 := by rw [sub_add_cancel]
        _ ≤ (‖u z - g0 z‖ₑ + ‖g0 z‖ₑ) ^ 2 := by
            gcongr
            exact enorm_add_le _ _
        _ ≤ 2 * (‖u z - g0 z‖ₑ ^ 2 + ‖g0 z‖ₑ ^ 2) := hsq2 _ _
    have hmeas : AEMeasurable (fun z => ‖u z - g0 z‖ₑ ^ 2) (volume.restrict K) :=
      ((hu.sub hg0).enorm).pow_const 2
    calc (∫⁻ z in K, ‖u z‖ₑ ^ 2)
        ≤ ∫⁻ z in K, 2 * (‖u z - g0 z‖ₑ ^ 2 + ‖g0 z‖ₑ ^ 2) := lintegral_mono hpt
      _ = 2 * ((∫⁻ z in K, ‖u z - g0 z‖ₑ ^ 2) + ∫⁻ z in K, ‖g0 z‖ₑ ^ 2) := by
          rw [lintegral_const_mul' 2 _ (by norm_num), lintegral_add_left' hmeas]
      _ ≤ 2 * (1 + ∫⁻ z in K, ‖g0 z‖ₑ ^ 2) := by gcongr
  -- The global bound on the test function, and componentwise `L²` truncations.
  obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hφe : ∀ z, ‖φ z‖ₑ ≤ ENNReal.ofReal Cφ := by
    intro z
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by rw [← Real.norm_eq_abs]; exact hCφ z)
  have hmemRe : ∀ (g0 : ℂ → ℂ), MemLp g0 2 (volume.restrict K) →
      MemLp (K.indicator fun z => (g0 z).re) 2 volume := by
    intro g0 hg0
    rw [memLp_indicator_iff_restrict hKm]
    refine hg0.norm.mono'
      (Complex.continuous_re.comp_aestronglyMeasurable hg0.aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hmemIm : ∀ (g0 : ℂ → ℂ), MemLp g0 2 (volume.restrict K) →
      MemLp (K.indicator fun z => (g0 z).im) 2 volume := by
    intro g0 hg0
    rw [memLp_indicator_iff_restrict hKm]
    refine hg0.norm.mono'
      (Complex.continuous_im.comp_aestronglyMeasurable hg0.aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  -- Pointwise four-term bound for a difference of Jacobians.
  have hjac_pt : ∀ a b c d : ℂ,
      ‖(a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)‖ₑ
        ≤ ‖a - c‖ₑ * ‖b‖ₑ + ‖c‖ₑ * ‖b - d‖ₑ
          + (‖b - d‖ₑ * ‖a‖ₑ + ‖d‖ₑ * ‖a - c‖ₑ) := by
    intro a b c d
    have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => abs_sub x y
    have h1 : (a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)
        = ((a - c).re * b.im + c.re * (b - d).im)
          - ((b - d).re * a.im + d.re * (a - c).im) := by
      simp only [Complex.sub_re, Complex.sub_im]; ring
    have habs : |(a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)|
        ≤ ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ + (‖b - d‖ * ‖a‖ + ‖d‖ * ‖a - c‖) := by
      rw [h1]
      have t1 := habs_sub ((a - c).re * b.im + c.re * (b - d).im)
        ((b - d).re * a.im + d.re * (a - c).im)
      have t2 : |(a - c).re * b.im + c.re * (b - d).im|
          ≤ |(a - c).re| * |b.im| + |c.re| * |(b - d).im| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
      have t3 : |(b - d).re * a.im + d.re * (a - c).im|
          ≤ |(b - d).re| * |a.im| + |d.re| * |(a - c).im| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
      have b1 : |(a - c).re| * |b.im| ≤ ‖a - c‖ * ‖b‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      have b2 : |c.re| * |(b - d).im| ≤ ‖c‖ * ‖b - d‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      have b3 : |(b - d).re| * |a.im| ≤ ‖b - d‖ * ‖a‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      have b4 : |d.re| * |(a - c).im| ≤ ‖d‖ * ‖a - c‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      linarith
    calc ‖(a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)‖ₑ
        = ENNReal.ofReal
            |(a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)| :=
          Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖
            + (‖b - d‖ * ‖a‖ + ‖d‖ * ‖a - c‖)) := ENNReal.ofReal_le_ofReal habs
      _ = ‖a - c‖ₑ * ‖b‖ₑ + ‖c‖ₑ * ‖b - d‖ₑ
            + (‖b - d‖ₑ * ‖a‖ₑ + ‖d‖ₑ * ‖a - c‖ₑ) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _),
            ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _)]
          simp only [ofReal_norm]
  -- Measurability data on `K`.
  have hgxm : AEStronglyMeasurable gx (volume.restrict K) := hgxK.aestronglyMeasurable
  have hgym : AEStronglyMeasurable gy (volume.restrict K) := hgyK.aestronglyMeasurable
  -- Passage to the limit on both sides of the per-`n` identity.
  have hAtend : Filter.Tendsto (fun n => ∫ z, jacobianWeak
        (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z)
      Filter.atTop (nhds (∫ z, jacobianWeak gx gy z * φ z)) := by
    -- Integrability of the target.
    have h1 : Integrable ((K.indicator fun z => (gx z).re)
        * (K.indicator fun z => (gy z).im)) volume :=
      (hmemRe gx hgxK).integrable_mul (hmemIm gy hgyK)
    have h2 : Integrable ((K.indicator fun z => (gy z).re)
        * (K.indicator fun z => (gx z).im)) volume :=
      (hmemRe gy hgyK).integrable_mul (hmemIm gx hgxK)
    have h1' : Integrable (fun z => φ z * ((K.indicator fun w => (gx w).re) z
        * (K.indicator fun w => (gy w).im) z)) volume :=
      h1.bdd_mul hφ.continuous.aestronglyMeasurable (ae_of_all _ hCφ)
    have h2' : Integrable (fun z => φ z * ((K.indicator fun w => (gy w).re) z
        * (K.indicator fun w => (gx w).im) z)) volume :=
      h2.bdd_mul hφ.continuous.aestronglyMeasurable (ae_of_all _ hCφ)
    have heq : (fun z => jacobianWeak gx gy z * φ z)
        = fun z => φ z * ((K.indicator fun w => (gx w).re) z
            * (K.indicator fun w => (gy w).im) z)
          - φ z * ((K.indicator fun w => (gy w).re) z
            * (K.indicator fun w => (gx w).im) z) := by
      funext z
      by_cases hz : z ∈ K
      · simp only [Set.indicator_of_mem hz, jacobianWeak]
        ring
      · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [jacobianWeak, hφz]
    have hA_int : Integrable (fun z => jacobianWeak gx gy z * φ z) volume := by
      rw [heq]; exact h1'.sub h2'
    -- Integrability of each approximant.
    have hAn_int : ∀ n, Integrable (fun z => jacobianWeak
        (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z) volume := by
      intro n
      have hjc : Continuous (fun z => jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) :=
        ((Complex.continuous_re.comp (hXc n)).mul
            (Complex.continuous_im.comp (hYc n))).sub
          ((Complex.continuous_re.comp (hYc n)).mul (Complex.continuous_im.comp (hXc n)))
      exact (hjc.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    -- The `L¹` convergence of the integrands, localized to `K`.
    refine tendsto_integral_of_L1 _ hA_int.aestronglyMeasurable
      (Filter.Eventually.of_forall hAn_int) ?_
    have hred : ∀ n, (∫⁻ z, ‖jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
        - jacobianWeak gx gy z * φ z‖ₑ)
        = ∫⁻ z in K, ‖jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
        - jacobianWeak gx gy z * φ z‖ₑ := by
      intro n
      rw [← lintegral_indicator hKm]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        rw [Set.indicator_of_notMem hz, hφz]
        simp
    -- Constants for the dominating sequence.
    set BX : ℝ≥0∞ := 2 * (1 + ∫⁻ z in K, ‖gx z‖ₑ ^ 2) with hBX_def
    set BY : ℝ≥0∞ := 2 * (1 + ∫⁻ z in K, ‖gy z‖ₑ ^ 2) with hBY_def
    have hBXfin : BX ≠ ⊤ := by
      rw [hBX_def]
      exact (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hGX⟩)).ne
    have hBYfin : BY ≠ ⊤ := by
      rw [hBY_def]
      exact (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hGY⟩)).ne
    have hGXfin : (∫⁻ z in K, ‖gx z‖ₑ ^ 2) ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hGX.ne).ne
    have hGYfin : (∫⁻ z in K, ‖gy z‖ₑ ^ 2) ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hGY.ne).ne
    -- The dominating sequence.
    set D : ℕ → ℝ≥0∞ := fun n =>
      ((∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) * BY ^ (1/2 : ℝ)
        + (∫⁻ z in K, ‖gx z‖ₑ ^ 2) ^ (1/2 : ℝ)
          * (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ)
        + ((∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) * BX ^ (1/2 : ℝ)
          + (∫⁻ z in K, ‖gy z‖ₑ ^ 2) ^ (1/2 : ℝ)
            * (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                - gx z‖ₑ ^ 2) ^ (1/2 : ℝ)))
        * ENNReal.ofReal Cφ with hD_def
    -- The dominating sequence tends to `0`.
    have hx12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gx z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTx
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hy12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gy z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTy
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hD0 : Filter.Tendsto D Filter.atTop (nhds 0) := by
      have hBY12 : BY ^ (1/2 : ℝ) ≠ ⊤ :=
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBYfin).ne
      have hBX12 : BX ^ (1/2 : ℝ) ≠ ⊤ :=
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBXfin).ne
      have t1 := ENNReal.Tendsto.mul_const hx12 (Or.inr hBY12)
      have t2 := ENNReal.Tendsto.const_mul hy12 (Or.inr hGXfin)
      have t3 := ENNReal.Tendsto.mul_const hy12 (Or.inr hBX12)
      have t4 := ENNReal.Tendsto.const_mul hx12 (Or.inr hGYfin)
      have hsum := (t1.add t2).add (t3.add t4)
      have hfin := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal Cφ) hsum
        (Or.inr ENNReal.ofReal_ne_top)
      rw [hD_def]
      simpa using hfin
    -- The eventual domination.
    have hex1 := (ENNReal.tendsto_nhds_zero.mp hTx) 1 (by norm_num)
    have hey1 := (ENNReal.tendsto_nhds_zero.mp hTy) 1 (by norm_num)
    have hDbd : ∀ᶠ n in Filter.atTop, (∫⁻ z in K, ‖jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
        - jacobianWeak gx gy z * φ z‖ₑ) ≤ D n := by
      filter_upwards [hex1, hey1] with n hx1 hy1
      have hXm : AEStronglyMeasurable
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hXc n).aestronglyMeasurable.restrict
      have hYm : AEStronglyMeasurable
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hYc n).aestronglyMeasurable.restrict
      have hmassX := hmass _ gx hXm hgxm hx1
      have hmassY := hmass _ gy hYm hgym hy1
      -- the four `enorm` factors and their measurability
      have me1 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
          (volume.restrict K) := (hXm.sub hgxm).enorm
      have me2 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
          (volume.restrict K) := (hYm.sub hgym).enorm
      have me3 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          (volume.restrict K) := hXm.enorm
      have me4 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          (volume.restrict K) := hYm.enorm
      have mgx : AEMeasurable (fun z => ‖gx z‖ₑ) (volume.restrict K) := hgxm.enorm
      have mgy : AEMeasurable (fun z => ‖gy z‖ₑ) (volume.restrict K) := hgym.enorm
      -- Hölder estimates for the four products
      have e1 : (∫⁻ z in K,
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ
            * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) * BY ^ (1/2 : ℝ) := by
        refine (holder _ _ me1 me4).trans ?_
        gcongr
      have e2 : (∫⁻ z in K, ‖gx z‖ₑ
            * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
          ≤ (∫⁻ z in K, ‖gx z‖ₑ ^ 2) ^ (1/2 : ℝ)
            * (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) := holder _ _ mgx me2
      have e3 : (∫⁻ z in K,
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ
            * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) * BX ^ (1/2 : ℝ) := by
        refine (holder _ _ me2 me3).trans ?_
        gcongr
      have e4 : (∫⁻ z in K, ‖gy z‖ₑ
            * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
          ≤ (∫⁻ z in K, ‖gy z‖ₑ ^ 2) ^ (1/2 : ℝ)
            * (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) := holder _ _ mgy me1
      -- assemble
      calc (∫⁻ z in K, ‖jacobianWeak
            (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
            (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
          - jacobianWeak gx gy z * φ z‖ₑ)
          ≤ ∫⁻ z in K, ‖jacobianWeak
              (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
              (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
            - jacobianWeak gx gy z‖ₑ * ENNReal.ofReal Cφ := by
            refine lintegral_mono fun z => ?_
            have hz : jacobianWeak
                (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
                (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
                - jacobianWeak gx gy z * φ z
                = (jacobianWeak
                    (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
                    (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
                  - jacobianWeak gx gy z) * φ z := by ring
            rw [hz, enorm_mul]
            exact mul_le_mul' le_rfl (hφe z)
        _ = (∫⁻ z in K, ‖jacobianWeak
              (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
              (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
            - jacobianWeak gx gy z‖ₑ) * ENNReal.ofReal Cφ :=
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ ≤ D n := by
            rw [hD_def]
            refine mul_le_mul' ?_ le_rfl
            calc (∫⁻ z in K, ‖jacobianWeak
                  (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
                  (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
                - jacobianWeak gx gy z‖ₑ)
                ≤ ∫⁻ z in K,
                    (‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                        - gx z‖ₑ
                      * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ
                    + ‖gx z‖ₑ
                      * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                          - gy z‖ₑ
                    + (‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                          - gy z‖ₑ
                        * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ
                      + ‖gy z‖ₑ
                        * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                            - gx z‖ₑ)) := by
                  refine lintegral_mono fun z => ?_
                  exact hjac_pt
                    (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
                    (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
                    (gx z) (gy z)
              _ = (∫⁻ z in K,
                    ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                        - gx z‖ₑ
                      * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
                  + (∫⁻ z in K, ‖gx z‖ₑ
                      * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                          - gy z‖ₑ)
                  + ((∫⁻ z in K,
                      ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                          - gy z‖ₑ
                        * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
                    + ∫⁻ z in K, ‖gy z‖ₑ
                        * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                            - gx z‖ₑ) := by
                  rw [lintegral_add_left' ((me1.fun_mul me4).fun_add (mgx.fun_mul me2)),
                    lintegral_add_left' (me1.fun_mul me4),
                    lintegral_add_left' (me2.fun_mul me3)]
              _ ≤ _ := add_le_add (add_le_add e1 e2) (add_le_add e3 e4)
    -- squeeze, then transfer from `K` back to the whole plane
    have hKlim : Filter.Tendsto (fun n => ∫⁻ z in K, ‖jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
        - jacobianWeak gx gy z * φ z‖ₑ) Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD0
        (Filter.Eventually.of_forall fun n => zero_le) hDbd
    exact hKlim.congr fun n => (hred n).symm
  have hBtend : Filter.Tendsto (fun n =>
      ∫ z, (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1))
      Filter.atTop (nhds (∫ z, (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
          - (gy z).im * (fderiv ℝ φ z) 1))) := by
    -- Continuity, compact support, and bounds for the test-function partials.
    have hqc : Continuous fun z => (fderiv ℝ φ z) Complex.I :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hpc : Continuous fun z => (fderiv ℝ φ z) 1 :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hqcs : HasCompactSupport fun z => (fderiv ℝ φ z) Complex.I :=
      HasCompactSupport.fderiv_apply ℝ hφc Complex.I
    have hpcs : HasCompactSupport fun z => (fderiv ℝ φ z) 1 :=
      HasCompactSupport.fderiv_apply ℝ hφc 1
    obtain ⟨Cq, hCq⟩ := hqcs.exists_bound_of_continuous hqc
    obtain ⟨Cp, hCp⟩ := hpcs.exists_bound_of_continuous hpc
    have hCq0 : 0 ≤ Cq := le_trans (norm_nonneg _) (hCq 0)
    have hCp0 : 0 ≤ Cp := le_trans (norm_nonneg _) (hCp 0)
    obtain ⟨Cf1, hCf1⟩ := hKc.exists_bound_of_continuousOn hfcont.continuousOn
    set Cf : ℝ := max Cf1 0 with hCf_def
    have hCf : ∀ z ∈ K, ‖f z‖ ≤ Cf := fun z hz =>
      le_trans (hCf1 z hz) (le_max_left _ _)
    have hCf0 : 0 ≤ Cf := le_max_right _ _
    -- Vanishing of the partials off `K`.
    have hqzero : ∀ z, z ∉ K → (fderiv ℝ φ z) Complex.I = 0 := by
      intro z hz
      have hnot : z ∉ tsupport (fun x => (fderiv ℝ φ x) Complex.I) := fun hmem =>
        hz (tsupport_fderiv_apply_subset ℝ Complex.I hmem)
      have := image_eq_zero_of_notMem_tsupport (f := fun x => (fderiv ℝ φ x) Complex.I) hnot
      exact this
    have hpzero : ∀ z, z ∉ K → (fderiv ℝ φ z) 1 = 0 := by
      intro z hz
      have hnot : z ∉ tsupport (fun x => (fderiv ℝ φ x) 1) := fun hmem =>
        hz (tsupport_fderiv_apply_subset ℝ 1 hmem)
      have := image_eq_zero_of_notMem_tsupport (f := fun x => (fderiv ℝ φ x) 1) hnot
      exact this
    -- Integrability of the target.
    have hq2 : MemLp (fun z => (fderiv ℝ φ z) Complex.I) 2 volume :=
      hqc.memLp_of_hasCompactSupport hqcs
    have hp2 : MemLp (fun z => (fderiv ℝ φ z) 1) 2 volume :=
      hpc.memLp_of_hasCompactSupport hpcs
    have ht1 : Integrable ((K.indicator fun w => (gx w).im)
        * fun z => (fderiv ℝ φ z) Complex.I) volume :=
      (hmemIm gx hgxK).integrable_mul hq2
    have ht2 : Integrable ((K.indicator fun w => (gy w).im)
        * fun z => (fderiv ℝ φ z) 1) volume :=
      (hmemIm gy hgyK).integrable_mul hp2
    have heq1 : (fun z => (gx z).im * (fderiv ℝ φ z) Complex.I)
        = (K.indicator fun w => (gx w).im) * fun z => (fderiv ℝ φ z) Complex.I := by
      funext z
      by_cases hz : z ∈ K
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz, hqzero z hz]
    have heq2 : (fun z => (gy z).im * (fderiv ℝ φ z) 1)
        = (K.indicator fun w => (gy w).im) * fun z => (fderiv ℝ φ z) 1 := by
      funext z
      by_cases hz : z ∈ K
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz, hpzero z hz]
    have hsub12 : Integrable (fun z => (gx z).im * (fderiv ℝ φ z) Complex.I
        - (gy z).im * (fderiv ℝ φ z) 1) volume := by
      rw [show (fun z => (gx z).im * (fderiv ℝ φ z) Complex.I
          - (gy z).im * (fderiv ℝ φ z) 1)
        = (fun z => (gx z).im * (fderiv ℝ φ z) Complex.I)
          - fun z => (gy z).im * (fderiv ℝ φ z) 1 from rfl, heq1, heq2]
      exact ht1.sub ht2
    have hfreK : AEStronglyMeasurable (K.indicator fun w => (f w).re) volume :=
      (Complex.continuous_re.comp hfcont).aestronglyMeasurable.indicator hKm
    have hfreKbd : ∀ z, ‖(K.indicator fun w => (f w).re) z‖ ≤ Cf := by
      intro z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz, Real.norm_eq_abs]
        exact le_trans (Complex.abs_re_le_norm _) (hCf z hz)
      · rw [Set.indicator_of_notMem hz]
        simpa using hCf0
    have heqB : (fun z => (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
          - (gy z).im * (fderiv ℝ φ z) 1))
        = fun z => (K.indicator fun w => (f w).re) z
            * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1) := by
      funext z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hqzero z hz, hpzero z hz]
        ring
    have hB_int : Integrable (fun z => (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
        - (gy z).im * (fderiv ℝ φ z) 1)) volume := by
      rw [heqB]
      exact hsub12.bdd_mul hfreK (ae_of_all _ hfreKbd)
    -- Integrability of each approximant.
    have hBn_int : ∀ n, Integrable (fun z =>
        (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1)) volume := by
      intro n
      have hcont : Continuous (fun z =>
          (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)) :=
        (Complex.continuous_re.comp (hFc n)).mul
          (((Complex.continuous_im.comp (hXc n)).mul hqc).sub
            ((Complex.continuous_im.comp (hYc n)).mul hpc))
      have hcs : HasCompactSupport (fun z =>
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1) := by
        have h1 : HasCompactSupport (fun z =>
            (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I) := hqcs.mul_left
        have h2 : HasCompactSupport (fun z =>
            (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1) := hpcs.mul_left
        exact h1.sub h2
      exact hcont.integrable_of_hasCompactSupport hcs.mul_left
    refine tendsto_integral_of_L1 _ hB_int.aestronglyMeasurable
      (Filter.Eventually.of_forall hBn_int) ?_
    -- Reduce the `L¹` distance to `K`.
    have hred : ∀ n, (∫⁻ z,
        ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)
          - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ)
        = ∫⁻ z in K,
        ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)
          - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ := by
      intro n
      rw [← lintegral_indicator hKm]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hqzero z hz, hpzero z hz]
        simp
    -- Pointwise bound in `ℝ≥0∞` for the difference of the integrands.
    have hB_pt : ∀ (A a b c cx cy : ℂ) (qv pv : ℝ), |qv| ≤ Cq → |pv| ≤ Cp → ‖c‖ ≤ Cf →
        ‖A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)‖ₑ
          ≤ ‖A - c‖ₑ * ‖a‖ₑ * ENNReal.ofReal Cq + ‖A - c‖ₑ * ‖b‖ₑ * ENNReal.ofReal Cp
            + (‖a - cx‖ₑ * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
              + ‖b - cy‖ₑ * (ENNReal.ofReal Cf * ENNReal.ofReal Cp)) := by
      intro A a b c cx cy qv pv hqv hpv hc
      have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => abs_sub x y
      have h1 : A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)
          = (A - c).re * (a.im * qv - b.im * pv)
            + c.re * ((a - cx).im * qv - (b - cy).im * pv) := by
        simp only [Complex.sub_re, Complex.sub_im]; ring
      have s1 : |a.im * qv - b.im * pv| ≤ ‖a‖ * Cq + ‖b‖ * Cp := by
        refine (habs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        gcongr
        · exact Complex.abs_im_le_norm _
        · exact Complex.abs_im_le_norm _
      have s2 : |(a - cx).im * qv - (b - cy).im * pv|
          ≤ ‖a - cx‖ * Cq + ‖b - cy‖ * Cp := by
        refine (habs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        gcongr
        · exact Complex.abs_im_le_norm _
        · exact Complex.abs_im_le_norm _
      have habs : |A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)|
          ≤ ‖A - c‖ * ‖a‖ * Cq + ‖A - c‖ * ‖b‖ * Cp
            + (‖a - cx‖ * (Cf * Cq) + ‖b - cy‖ * (Cf * Cp)) := by
        rw [h1]
        have tX : |(A - c).re * (a.im * qv - b.im * pv)|
            ≤ ‖A - c‖ * (‖a‖ * Cq + ‖b‖ * Cp) := by
          rw [abs_mul]
          exact mul_le_mul (Complex.abs_re_le_norm _) s1 (abs_nonneg _) (norm_nonneg _)
        have tY : |c.re * ((a - cx).im * qv - (b - cy).im * pv)|
            ≤ Cf * (‖a - cx‖ * Cq + ‖b - cy‖ * Cp) := by
          rw [abs_mul]
          exact mul_le_mul (le_trans (Complex.abs_re_le_norm _) hc) s2
            (abs_nonneg _) hCf0
        calc |(A - c).re * (a.im * qv - b.im * pv)
              + c.re * ((a - cx).im * qv - (b - cy).im * pv)|
            ≤ |(A - c).re * (a.im * qv - b.im * pv)|
              + |c.re * ((a - cx).im * qv - (b - cy).im * pv)| := abs_add_le _ _
          _ ≤ ‖A - c‖ * (‖a‖ * Cq + ‖b‖ * Cp)
              + Cf * (‖a - cx‖ * Cq + ‖b - cy‖ * Cp) := add_le_add tX tY
          _ = ‖A - c‖ * ‖a‖ * Cq + ‖A - c‖ * ‖b‖ * Cp
              + (‖a - cx‖ * (Cf * Cq) + ‖b - cy‖ * (Cf * Cp)) := by ring
      calc ‖A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)‖ₑ
          = ENNReal.ofReal
              |A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)| :=
            Real.enorm_eq_ofReal_abs _
        _ ≤ ENNReal.ofReal (‖A - c‖ * ‖a‖ * Cq + ‖A - c‖ * ‖b‖ * Cp
              + (‖a - cx‖ * (Cf * Cq) + ‖b - cy‖ * (Cf * Cp))) :=
            ENNReal.ofReal_le_ofReal habs
        _ = ‖A - c‖ₑ * ‖a‖ₑ * ENNReal.ofReal Cq + ‖A - c‖ₑ * ‖b‖ₑ * ENNReal.ofReal Cp
              + (‖a - cx‖ₑ * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
                + ‖b - cy‖ₑ * (ENNReal.ofReal Cf * ENNReal.ofReal Cp)) := by
            rw [← ofReal_norm (A - c), ← ofReal_norm a,
              ← ofReal_norm b, ← ofReal_norm (a - cx),
              ← ofReal_norm (b - cy),
              ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul hCf0, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul hCf0, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
    -- Constants and the dominating sequence.
    set BX : ℝ≥0∞ := 2 * (1 + ∫⁻ z in K, ‖gx z‖ₑ ^ 2) with hBX_def
    set BY : ℝ≥0∞ := 2 * (1 + ∫⁻ z in K, ‖gy z‖ₑ ^ 2) with hBY_def
    have hBXfin : BX ≠ ⊤ := by
      rw [hBX_def]
      exact (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hGX⟩)).ne
    have hBYfin : BY ≠ ⊤ := by
      rw [hBY_def]
      exact (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hGY⟩)).ne
    have hBX12 : BX ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBXfin).ne
    have hBY12 : BY ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBYfin).ne
    have hvol12 : (volume K) ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvolK.ne).ne
    have hfq' : ENNReal.ofReal Cf * ENNReal.ofReal Cq ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
    have hfp' : ENNReal.ofReal Cf * ENNReal.ofReal Cp ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
    set D : ℕ → ℝ≥0∞ := fun n =>
      (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - f z‖ₑ ^ 2) ^ (1/2 : ℝ) * BX ^ (1/2 : ℝ) * ENNReal.ofReal Cq
        + (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
            - f z‖ₑ ^ 2) ^ (1/2 : ℝ) * BY ^ (1/2 : ℝ) * ENNReal.ofReal Cp
        + ((∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) * (volume K) ^ (1/2 : ℝ)
            * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
          + (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) * (volume K) ^ (1/2 : ℝ)
            * (ENNReal.ofReal Cf * ENNReal.ofReal Cp)) with hD_def
    have hf12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - f z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTf
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hx12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gx z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTx
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hy12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gy z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTy
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hD0 : Filter.Tendsto D Filter.atTop (nhds 0) := by
      have t1 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal Cq)
        (ENNReal.Tendsto.mul_const hf12 (Or.inr hBX12)) (Or.inr ENNReal.ofReal_ne_top)
      have t2 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal Cp)
        (ENNReal.Tendsto.mul_const hf12 (Or.inr hBY12)) (Or.inr ENNReal.ofReal_ne_top)
      have hfq : ENNReal.ofReal Cf * ENNReal.ofReal Cq ≠ ⊤ :=
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
      have hfp : ENNReal.ofReal Cf * ENNReal.ofReal Cp ≠ ⊤ :=
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
      have t3 := ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.mul_const hx12 (Or.inr hvol12)) (Or.inr hfq)
      have t4 := ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.mul_const hy12 (Or.inr hvol12)) (Or.inr hfp)
      have hsum := (t1.add t2).add (t3.add t4)
      rw [hD_def]
      simpa using hsum
    -- The eventual domination.
    have hex1 := (ENNReal.tendsto_nhds_zero.mp hTx) 1 (by norm_num)
    have hey1 := (ENNReal.tendsto_nhds_zero.mp hTy) 1 (by norm_num)
    have hDbd : ∀ᶠ n in Filter.atTop, (∫⁻ z in K,
        ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)
          - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ) ≤ D n := by
      filter_upwards [hex1, hey1] with n hx1 hy1
      have hXm : AEStronglyMeasurable
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hXc n).aestronglyMeasurable.restrict
      have hYm : AEStronglyMeasurable
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hYc n).aestronglyMeasurable.restrict
      have hFm : AEStronglyMeasurable
          (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hFc n).aestronglyMeasurable.restrict
      have hfm : AEStronglyMeasurable f (volume.restrict K) :=
        hfcont.aestronglyMeasurable.restrict
      have hmassX := hmass _ gx hXm hgxm hx1
      have hmassY := hmass _ gy hYm hgym hy1
      have mef : AEMeasurable (fun z =>
          ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ)
          (volume.restrict K) := (hFm.sub hfm).enorm
      have me1 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
          (volume.restrict K) := (hXm.sub hgxm).enorm
      have me2 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
          (volume.restrict K) := (hYm.sub hgym).enorm
      have me3 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          (volume.restrict K) := hXm.enorm
      have me4 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          (volume.restrict K) := hYm.enorm
      -- Hölder estimates.
      have e1 : (∫⁻ z in K,
          ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
            * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - f z‖ₑ ^ 2) ^ (1/2 : ℝ) * BX ^ (1/2 : ℝ) := by
        refine (holder _ _ mef me3).trans ?_
        gcongr
      have e2 : (∫⁻ z in K,
          ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
            * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - f z‖ₑ ^ 2) ^ (1/2 : ℝ) * BY ^ (1/2 : ℝ) := by
        refine (holder _ _ mef me4).trans ?_
        gcongr
      have e3 : (∫⁻ z in K,
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) * (volume K) ^ (1/2 : ℝ) := by
        have h := holder _ (fun _ => (1 : ℝ≥0∞)) me1 aemeasurable_const
        simpa [setLIntegral_one] using h
      have e4 : (∫⁻ z in K,
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) * (volume K) ^ (1/2 : ℝ) := by
        have h := holder _ (fun _ => (1 : ℝ≥0∞)) me2 aemeasurable_const
        simpa [setLIntegral_one] using h
      -- Assemble via the pointwise bound.
      calc (∫⁻ z in K,
          ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
              * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                  * (fderiv ℝ φ z) Complex.I
                - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                  * (fderiv ℝ φ z) 1)
            - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
                - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ)
          ≤ ∫⁻ z in K,
            (‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
                * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ
                * ENNReal.ofReal Cq
              + ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
                * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ
                * ENNReal.ofReal Cp
              + (‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ
                  * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
                + ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ
                  * (ENNReal.ofReal Cf * ENNReal.ofReal Cp))) := by
            refine lintegral_mono_ae ((ae_restrict_iff' hKm).mpr (ae_of_all _
              fun z hz => ?_))
            have hb := hB_pt
              (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
              (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
              (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
              (f z) (gx z) (gy z) ((fderiv ℝ φ z) Complex.I) ((fderiv ℝ φ z) 1)
              (by rw [← Real.norm_eq_abs]; exact hCq z)
              (by rw [← Real.norm_eq_abs]; exact hCp z) (hCf z hz)
            exact hb
        _ = (∫⁻ z in K,
              ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
                * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
              * ENNReal.ofReal Cq
            + (∫⁻ z in K,
              ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
                * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
              * ENNReal.ofReal Cp
            + ((∫⁻ z in K,
                ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
                * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
              + (∫⁻ z in K,
                ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
                * (ENNReal.ofReal Cf * ENNReal.ofReal Cp)) := by
            rw [lintegral_add_left' (((mef.fun_mul me3).mul_const _).fun_add
                ((mef.fun_mul me4).mul_const _)),
              lintegral_add_left' ((mef.fun_mul me3).mul_const _),
              lintegral_add_left' (me1.mul_const _),
              lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
              lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
              lintegral_mul_const' _ _ hfq', lintegral_mul_const' _ _ hfp']
        _ ≤ D n := by
            rw [hD_def]
            refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ ?_)
            · exact mul_le_mul' e1 le_rfl
            · exact mul_le_mul' e2 le_rfl
            · exact mul_le_mul' e3 le_rfl
            · exact mul_le_mul' e4 le_rfl
    have hKlim : Filter.Tendsto (fun n => ∫⁻ z in K,
        ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)
          - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ) Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD0
        (Filter.Eventually.of_forall fun n => zero_le) hDbd
    exact hKlim.congr fun n => (hred n).symm
  exact tendsto_nhds_unique (hAtend.congr hAB) hBtend

end NoWanderingDomains
