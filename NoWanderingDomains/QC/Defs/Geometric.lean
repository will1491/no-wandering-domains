/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Modulus
import NoWanderingDomains.QC.Defs.SensePreserving
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Quasiconformal maps: the geometric definition

This file gives the **geometric** definition of a quasiconformal map, via the
quasi-invariance of the **modulus of quadrilaterals**. A quadrilateral is a
topological embedding of the closed unit square `[0, 1]²` into `ℂ`; its modulus is
the conformal modulus (`curveModulus`) of the family of curves joining the left
side `{0} × [0, 1]` to the right side `{1} × [0, 1]` inside the embedded square.
Taking the square as data sidesteps the Jordan curve theorem (which Mathlib does
not have): the four sides are the images of the four sides of the standard square.

A homeomorphism `f : ℂ → ℂ` is **`K`-quasiconformal** when it distorts the modulus
of every quadrilateral by at most the factor `K`:

`modulus (f Q) ≤ K · modulus Q` for every quadrilateral `Q`.

For a homeomorphism this single inequality (applied also to `f⁻¹`) is equivalent to
the two-sided bound `K⁻¹ · modulus Q ≤ modulus (f Q) ≤ K · modulus Q`.

This is the geometric track of the two quasiconformal definitions; the analytic
track (`IsQCAnalytic`, via the Beltrami equation) lives in `QC/Defs/Analytic.lean`, and
the two are proved equivalent in `QC/Equivalence.lean`. The geometric track owns the
compactness and Weyl (`1`-quasiconformal ⇒ conformal) lemmas.

## Main definitions

* `Quadrilateral` — a continuous embedding of the closed unit square into `ℂ`;
* `Quadrilateral.curveFamily Q` — the family of curves in the embedded square
  joining the left side to the right side;
* `Quadrilateral.modulus Q` — the conformal modulus of that curve family;
* `IsQCGeometric f K` — `f` is a topologically sense-preserving homeomorphism
  (`SensePreserving`) distorting every quadrilateral's modulus by at most `K`.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- Restriction of absolute continuity to a subinterval of `[0, 1]`: if `γ` is absolutely
continuous on `[0, 1]` and `uIcc a c ⊆ Icc 0 1`, then `γ` is absolutely continuous on
`uIcc a c`. A thin specialization of `AbsolutelyContinuousOnInterval.mono`, used to supply
the curve-family AC hypothesis (only required on `[0, 1]`) at the subintervals the
length–area machinery integrates over. -/
theorem _root_.AbsolutelyContinuousOnInterval.mono_subinterval {γ : ℝ → ℂ} {a c : ℝ}
    (h : AbsolutelyContinuousOnInterval γ 0 1) (hac : Set.uIcc a c ⊆ Set.Icc 0 1) :
    AbsolutelyContinuousOnInterval γ a c :=
  h.mono (by rwa [Set.uIcc_of_le (zero_le_one)])

/-- The closed unit square `[0, 1] × [0, 1] ⊆ ℝ × ℝ`. -/
def unitSquare : Set (ℝ × ℝ) := Set.Icc 0 1 ×ˢ Set.Icc 0 1

/-- A **quadrilateral**: a continuous map `ℝ × ℝ → ℂ` injective on the closed unit
square. Its image is a topological square whose four sides are the images of the
four sides of `[0, 1]²`; taking the parametrization as data avoids the Jordan curve
theorem. -/
structure Quadrilateral where
  /-- The parametrizing map; only its values on `unitSquare` matter. -/
  toFun : ℝ × ℝ → ℂ
  /-- The parametrization is continuous. -/
  continuous_toFun : Continuous toFun
  /-- The parametrization is injective on the closed unit square. -/
  injOn_unitSquare : Set.InjOn toFun unitSquare

namespace Quadrilateral

/-- The image of the closed unit square under the quadrilateral. -/
def image (Q : Quadrilateral) : Set ℂ := Q.toFun '' unitSquare

/-- The **left side** of the quadrilateral: the image of `{0} × [0, 1]`. -/
def leftSide (Q : Quadrilateral) : Set ℂ := Q.toFun '' (({0} : Set ℝ) ×ˢ Set.Icc 0 1)

/-- The **right side** of the quadrilateral: the image of `{1} × [0, 1]`. -/
def rightSide (Q : Quadrilateral) : Set ℂ := Q.toFun '' (({1} : Set ℝ) ×ˢ Set.Icc 0 1)

/-- The **connecting curve family** of the quadrilateral: absolutely continuous
curves in the embedded square that start on the left side and end on the right side.
Restricting to absolutely continuous curves is the mathematically correct domain for
the modulus: the arc-length line integral uses `deriv γ`, which is meaningful only
when `γ` is differentiable a.e. (as it is for absolutely continuous curves), and
non-rectifiable curves never lower the modulus, so the value is unchanged. -/
def curveFamily (Q : Quadrilateral) : Set (ℝ → ℂ) :=
  {γ | Continuous γ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧
    γ 0 ∈ Q.leftSide ∧ γ 1 ∈ Q.rightSide ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Q.image}

/-- The **modulus** of the quadrilateral: the conformal modulus of its connecting
curve family. -/
noncomputable def modulus (Q : Quadrilateral) : ℝ≥0∞ := curveModulus Q.curveFamily

/-- The **image connecting curve family** of the quadrilateral under a map `f`: the
absolutely continuous curves that join the image left side `f '' leftSide` to the
image right side `f '' rightSide` while staying inside the image region
`f '' image`. When `f` is a homeomorphism this is exactly the connecting family of
the image quadrilateral `f ∘ Q` (since `f '' (Q.toFun '' S) = (f ∘ Q.toFun) '' S`),
so its modulus is the genuine modulus `M(f(Q))`.

This is the mathematically correct object for the geometric definition: it ranges
over *all* AC curves in the image quadrilateral, not only those of the form `f ∘ γ`
with `γ` absolutely continuous. A quasiconformal map is ACL but need not send every
AC curve to an AC curve, so the pushforward `(f ∘ ·) '' Q.curveFamily` is in general
a proper subfamily with strictly smaller modulus — using it would state a condition
strictly weaker than `M(f(Q)) ≤ K · M(Q)`. -/
def imageCurveFamily (Q : Quadrilateral) (f : ℂ → ℂ) : Set (ℝ → ℂ) :=
  {δ | Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
    δ 0 ∈ f '' Q.leftSide ∧ δ 1 ∈ f '' Q.rightSide ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ f '' Q.image}

/-- For a **conformal** homeomorphism `φ` (an entire homeomorphism of the plane, hence
affine and bi-Lipschitz), the image connecting family of a quadrilateral is exactly the
pushforward of its connecting family: `Q.imageCurveFamily φ = (φ ∘ ·) '' Q.curveFamily`.
An entire homeomorphism and its inverse are holomorphic, hence locally Lipschitz, so
each preserves absolute continuity of curves on `[0, 1]`; this matches the two families
curve-for-curve in both directions. It is what transports the pushforward conformal
invariance `curveModulus_conformal_invariant` to the genuine image family that
`IsQCGeometric` is stated with. -/
theorem imageCurveFamily_eq_pushforward_of_conformal {φ : ℂ → ℂ}
    (hφ : IsHomeomorph φ) (hφ' : DifferentiableOn ℂ φ Set.univ) (Q : Quadrilateral) :
    Q.imageCurveFamily φ = (fun γ : ℝ → ℂ => φ ∘ γ) '' Q.curveFamily := by
  -- `φ` is an entire homeomorphism; its inverse `χ` is also an entire homeomorphism
  -- (holomorphic inverse function theorem, via nonvanishing derivative). Both `φ` and
  -- `χ` are holomorphic, hence locally Lipschitz, so each preserves absolute
  -- continuity of curves on every interval. We match the two families curve-for-curve.
  have hφentire : Differentiable ℂ φ := fun z =>
    (hφ' z (Set.mem_univ z)).differentiableAt (by simp)
  -- An injective entire map has nowhere-vanishing derivative.
  have deriv_ne_zero : ∀ (η : ℂ → ℂ), IsHomeomorph η → Differentiable ℂ η →
      ∀ z, deriv η z ≠ 0 := by
    intro η hη hη' z hderiv0
    have hinj : Function.Injective η := hη.injective
    set g : ℂ → ℂ := fun w => η w - η z with hg_def
    have hη_an : ∀ w, AnalyticAt ℂ η w := fun w =>
      (hη'.differentiableOn).analyticAt Filter.univ_mem
    have hg_an : AnalyticAt ℂ g z := (hη_an z).sub analyticAt_const
    have hge2 : 2 ≤ analyticOrderAt g z := by
      have hdη_an : AnalyticAt ℂ (deriv η) z := (hη_an z).deriv
      have key := (hη_an z).analyticOrderAt_deriv_add_one
      have hge1 : 1 ≤ analyticOrderAt (deriv η) z := by
        rw [Order.one_le_iff_ne_zero, Ne, analyticOrderAt_eq_zero, not_or, not_not, not_ne_iff]
        exact ⟨hdη_an, hderiv0⟩
      calc (2 : ℕ∞) = 1 + 1 := by rfl
        _ ≤ analyticOrderAt (deriv η) z + 1 := by gcongr
        _ = analyticOrderAt g z := key
    have hne_top : analyticOrderAt g z ≠ ⊤ := by
      rw [Ne, analyticOrderAt_eq_top]
      intro hev
      have hev2 : ∀ᶠ w in 𝓝[≠] z, η w = η z := by
        have hev' : ∀ᶠ w in 𝓝[≠] z, g w = 0 := hev.filter_mono nhdsWithin_le_nhds
        filter_upwards [hev'] with w hw
        simpa [hg_def, sub_eq_zero] using hw
      obtain ⟨w, hw, hwne⟩ := (hev2.and self_mem_nhdsWithin).exists
      exact hwne (hinj hw)
    -- An analytic n-th root of a nonvanishing analytic germ.
    have analytic_nth_root : ∀ {G : ℂ → ℂ} {z₀ : ℂ} {n : ℕ}, AnalyticAt ℂ G z₀ →
        G z₀ ≠ 0 → 1 ≤ n →
        ∃ H : ℂ → ℂ, AnalyticAt ℂ H z₀ ∧ H z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, (H z) ^ n = G z := by
      intro G z₀ n hG hGz hn
      set c : ℂ := (↑‖G z₀‖ : ℂ) / G z₀ with hc_def
      have hnorm_pos : 0 < ‖G z₀‖ := by positivity
      have hc_ne : c ≠ 0 := by
        rw [hc_def]; exact div_ne_zero (by exact_mod_cast (norm_ne_zero_iff).mpr hGz) hGz
      have hcG : c * G z₀ = (↑‖G z₀‖ : ℂ) := by rw [hc_def]; field_simp
      have hcG_an : AnalyticAt ℂ (fun z => c * G z) z₀ := analyticAt_const.mul hG
      have hval_slit : (fun z => c * G z) z₀ ∈ Complex.slitPlane := by
        simp only [hcG]; rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.ofReal_re]; positivity
      set cr : ℂ := Complex.exp (Complex.log c / n) with hcr_def
      have hcr_ne : cr ≠ 0 := Complex.exp_ne_zero _
      have hcr_pow : cr ^ n = c := by
        rw [hcr_def, ← Complex.exp_nat_mul, mul_div_cancel₀]
        · exact Complex.exp_log hc_ne
        · exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
      refine ⟨fun z => Complex.exp (Complex.log (c * G z) / n) / cr, ?_, ?_, ?_⟩
      · apply AnalyticAt.div _ analyticAt_const hcr_ne
        have hlog : AnalyticAt ℂ (fun z => Complex.log (c * G z)) z₀ := hcG_an.clog hval_slit
        have hdiv : AnalyticAt ℂ (fun z => Complex.log (c * G z) / n) z₀ :=
          hlog.div analyticAt_const (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
        simpa [Function.comp] using! hdiv.cexp
      · exact div_ne_zero (Complex.exp_ne_zero _) hcr_ne
      · have hcont : ContinuousAt (fun z => c * G z) z₀ := hcG_an.continuousAt
        have hGne_ev : ∀ᶠ z in 𝓝 z₀, c * G z ≠ 0 := hcont.eventually_ne (mul_ne_zero hc_ne hGz)
        filter_upwards [hGne_ev] with z hz
        rw [div_pow, ← Complex.exp_nat_mul,
          mul_div_cancel₀ _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn) : (n : ℂ) ≠ 0)]
        rw [Complex.exp_log hz, hcr_pow]; field_simp
    obtain ⟨n, hn2, hordern⟩ : ∃ n : ℕ, 2 ≤ n ∧ analyticOrderAt g z = (n : ℕ∞) := by
      lift analyticOrderAt g z to ℕ using hne_top with m hm
      exact ⟨m, by exact_mod_cast hge2, rfl⟩
    obtain ⟨G, hG_an, hGz, hdecomp⟩ := (hg_an.analyticOrderAt_eq_natCast).mp hordern
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
    obtain ⟨H, hH_an, hHz, hHpow⟩ := analytic_nth_root hG_an hGz hn1
    set u : ℂ → ℂ := fun w => (w - z) * H w with hu_def
    have hu_an : AnalyticAt ℂ u z := (analyticAt_id.sub analyticAt_const).mul hH_an
    have huz : u z = 0 := by simp [hu_def]
    have hu_deriv : HasDerivAt u (H z) z := by
      have h1 : HasDerivAt (fun w : ℂ => w - z) 1 z := by
        simpa using (hasDerivAt_id z).sub_const z
      have h2 : HasDerivAt H (deriv H z) z := hH_an.differentiableAt.hasDerivAt
      have h3 := h1.mul h2
      simp only [sub_self, zero_mul, add_zero, one_mul] at h3
      exact h3
    have hu_strict : HasStrictDerivAt u (H z) z := by
      have hs := hu_an.hasStrictDerivAt
      rwa [hu_deriv.deriv] at hs
    have hg_eq_un : ∀ᶠ w in 𝓝 z, g w = (u w) ^ n := by
      filter_upwards [hdecomp, hHpow] with w hw hHw
      rw [hw, hu_def]; simp only; rw [mul_pow, smul_eq_mul, hHw]
    have hu_locinj := hu_strict.eventually_left_inverse hHz
    have hu_open : 𝓝 (0 : ℂ) ≤ Filter.map u (𝓝 z) := by
      rcases hu_an.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
      · exfalso
        have hconst' : u =ᶠ[𝓝 z] fun _ => u z := hconst
        have hd0 : deriv u z = 0 := by rw [hconst'.deriv_eq, deriv_const]
        rw [hu_deriv.deriv] at hd0; exact hHz hd0
      · rwa [huz] at hopen
    have hcombined : ∀ᶠ w in 𝓝 z,
        (hu_strict.localInverse u (H z) z hHz) (u w) = w ∧ g w = (u w) ^ n :=
      hu_locinj.and hg_eq_un
    obtain ⟨s, hs_mem, hs_prop⟩ := Filter.eventually_iff_exists_mem.mp hcombined
    have himg : u '' s ∈ 𝓝 (0 : ℂ) := Filter.le_map_iff.mp hu_open s hs_mem
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp himg
    set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n) with hζ_def
    have hζpow : ζ ^ n = 1 := (Complex.isPrimitiveRoot_exp n (by omega)).pow_eq_one
    have hζne1 : ζ ≠ 1 := (Complex.isPrimitiveRoot_exp n (by omega)).ne_one (by omega)
    have hζabs : ‖ζ‖ = 1 := by
      rw [hζ_def, Complex.norm_exp]
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    set t : ℂ := ((ρ / 2 : ℝ) : ℂ) with ht_def
    have ht_norm : ‖t‖ < ρ := by
      rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
    have ht_ne : t ≠ 0 := by
      rw [ht_def]; simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
    have ht_ball : t ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right]; exact ht_norm
    have hζt_ball : ζ * t ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, hζabs, one_mul]; exact ht_norm
    obtain ⟨z₁, hz₁s, hz₁u⟩ := hball ht_ball
    obtain ⟨z₂, hz₂s, hz₂u⟩ := hball hζt_ball
    have hu_z₁ : u z₁ = t := hz₁u
    have hu_z₂ : u z₂ = ζ * t := hz₂u
    have hne12 : z₁ ≠ z₂ := by
      intro h; subst h
      rw [hu_z₁] at hu_z₂
      have hζeq1 : ζ = 1 := by
        have hkey : (1 - ζ) * t = 0 := by linear_combination hu_z₂
        rcases mul_eq_zero.mp hkey with h1 | h2
        · linear_combination -h1
        · exact (ht_ne h2).elim
      exact hζne1 hζeq1
    have hg1 := (hs_prop z₁ hz₁s).2
    have hg2 := (hs_prop z₂ hz₂s).2
    have heq : g z₁ = g z₂ := by
      rw [hg1, hg2, hu_z₁, hu_z₂, mul_pow, hζpow, one_mul]
    have hηeq : η z₁ = η z₂ := by
      rw [hg_def] at heq; simp only at heq; linear_combination heq
    exact hne12 (hinj hηeq)
  -- The inverse homeomorphism `χ = φ⁻¹` and the fact that it is entire.
  set χ := (hφ.homeomorph φ).symm with hχ
  have hd1 : ∀ z, deriv φ z ≠ 0 := deriv_ne_zero φ hφ hφentire
  have hχhomeo : IsHomeomorph χ := (hφ.homeomorph φ).symm.isHomeomorph
  have hχentire : Differentiable ℂ χ := by
    intro a
    have hψd : HasDerivAt χ (deriv φ (χ a))⁻¹ a := by
      apply HasDerivAt.of_local_left_inverse
        χ.continuous.continuousAt ((hφentire (χ a)).hasDerivAt) (hd1 _)
      filter_upwards with y using (hφ.homeomorph φ).apply_symm_apply y
    exact hψd.differentiableAt
  have hχcont : Continuous χ := χ.continuous
  have hφcont : Continuous φ := hφ.continuous
  -- The composition lemma: a holomorphic map sends an absolutely continuous curve to an
  -- absolutely continuous curve. The curve has compact trace on every `uIcc a c`; the
  -- holomorphic map is Lipschitz on a closed ball containing it (bounded derivative on a
  -- convex compact), and Lipschitz-on-trace ∘ AC is AC.
  have hAC_comp : ∀ (ψ : ℂ → ℂ), Differentiable ℂ ψ → ∀ (η : ℝ → ℂ), Continuous η →
      AbsolutelyContinuousOnInterval η 0 1 →
      AbsolutelyContinuousOnInterval (fun t => ψ (η t)) 0 1 := by
    intro ψ hψ η hηcont hηac
    have htrace_cpt : IsCompact (η '' Set.uIcc (0 : ℝ) 1) := (isCompact_uIcc).image hηcont
    obtain ⟨R, hRpos, hRsub⟩ : ∃ R > 0, η '' Set.uIcc (0 : ℝ) 1 ⊆ Metric.closedBall (0 : ℂ) R := by
      obtain ⟨R, hRsub⟩ := htrace_cpt.isBounded.subset_closedBall (0 : ℂ)
      exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
        hRsub.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
    have hcpt : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
    have hψcd : ContDiff ℂ (1 : WithTop ℕ∞) ψ := hψ.contDiff
    have hfd_cont : Continuous (fun z => fderiv ℂ ψ z) :=
      hψcd.continuous_fderiv (by norm_num)
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖fderiv ℂ ψ z‖ ≤ C :=
      hcpt.exists_bound_of_continuousOn hfd_cont.continuousOn
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by simp [hRpos.le]))
    obtain ⟨K, hK⟩ : ∃ K : NNReal, LipschitzOnWith K ψ (Metric.closedBall (0 : ℂ) R) := by
      refine ⟨⟨C, hCnn⟩, Convex.lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x _ => hψ.differentiableAt) (fun x hx => ?_) (convex_closedBall _ _)⟩
      exact NNReal.coe_le_coe.mp (hC x hx)
    have hηac' := hηac
    rw [absolutelyContinuousOnInterval_iff] at hηac' ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hηac' (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have hmem : ∀ s : ℝ, s ∈ Set.uIcc (0 : ℝ) 1 → η s ∈ Metric.closedBall (0 : ℂ) R :=
      fun s hs => hRsub ⟨s, hs, rfl⟩
    have hsubmem := hE.1
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (ψ (η (E.2 i).1)) (ψ (η (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (η (E.2 i).1) (η (E.2 i).2) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact hK.dist_le_mul _ (hmem _ (hsubmem i hi).1) _ (hmem _ (hsubmem i hi).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (η (E.2 i).1) (η (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- Pointwise facts about the homeomorphism and its inverse.
  have hχφ : ∀ z, χ (φ z) = z := fun z => (hφ.homeomorph φ).symm_apply_apply z
  have hφχ : ∀ w, φ (χ w) = w := fun w => (hφ.homeomorph φ).apply_symm_apply w
  -- The set equality, proved by two inclusions.
  apply Set.ext
  intro δ
  constructor
  · -- `δ ∈ imageCurveFamily φ` ⇒ `δ = φ ∘ (χ ∘ δ)` with `χ ∘ δ ∈ curveFamily`.
    rintro ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩
    refine ⟨fun t => χ (δ t), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hχcont.comp hδcont
    · exact hAC_comp χ hχentire δ hδcont hδac
    · obtain ⟨p, hp, hpeq⟩ := hδ0
      change χ (δ 0) ∈ Q.leftSide
      have : χ (δ 0) = p := by rw [← hpeq, hχφ]
      rw [this]; exact hp
    · obtain ⟨p, hp, hpeq⟩ := hδ1
      change χ (δ 1) ∈ Q.rightSide
      have : χ (δ 1) = p := by rw [← hpeq, hχφ]
      rw [this]; exact hp
    · intro t ht
      obtain ⟨p, hp, hpeq⟩ := hδimg t ht
      change χ (δ t) ∈ Q.image
      have : χ (δ t) = p := by rw [← hpeq, hχφ]
      rw [this]; exact hp
    · funext t; exact hφχ (δ t)
  · -- `δ = φ ∘ γ` with `γ ∈ curveFamily` ⇒ `δ ∈ imageCurveFamily φ`.
    rintro ⟨γ, ⟨hγcont, hγac, hγ0, hγ1, hγimg⟩, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hφcont.comp hγcont
    · exact hAC_comp φ hφentire γ hγcont hγac
    · exact ⟨γ 0, hγ0, rfl⟩
    · exact ⟨γ 1, hγ1, rfl⟩
    · intro t ht; exact ⟨γ t, hγimg t ht, rfl⟩

/-- Conformal invariance of the **image-family** modulus: for an entire homeomorphism
`φ`, the modulus of the image connecting family equals the modulus of the quadrilateral's
own connecting family. Immediate from `imageCurveFamily_eq_pushforward_of_conformal` and
the pushforward conformal invariance `curveModulus_conformal_invariant`. -/
theorem curveModulus_imageCurveFamily_of_conformal {φ : ℂ → ℂ}
    (hφ : IsHomeomorph φ) (hφ' : DifferentiableOn ℂ φ Set.univ) (Q : Quadrilateral) :
    curveModulus (Q.imageCurveFamily φ) = curveModulus Q.curveFamily := by
  rw [imageCurveFamily_eq_pushforward_of_conformal hφ hφ' Q,
    curveModulus_conformal_invariant hφ hφ' Q.curveFamily]

end Quadrilateral

/-- The **geometric definition of a `K`-quasiconformal map**: a topologically
sense-preserving homeomorphism `f : ℂ → ℂ` that distorts the modulus of every
quadrilateral by at most the factor `K`, i.e. `M(f(Q)) ≤ K · M(Q)`. Here `M(f(Q))`
is the modulus of `Q.imageCurveFamily f`, the connecting family of the image
quadrilateral `f ∘ Q` — *all* absolutely continuous curves joining the two image
sides inside the image region. (It must be this family rather than the pushforward
`(f ∘ ·) '' Q.curveFamily`: a quasiconformal map need not carry every AC curve to an
AC curve, so the pushforward is a proper subfamily of strictly smaller modulus and
would yield a strictly weaker condition.) The orientation condition is the purely
topological `SensePreserving` — it carries no differentiability, so that a.e.
differentiability and positivity of the Jacobian remain genuine conclusions of the
geometric ⇒ analytic direction. -/
def IsQCGeometric (f : ℂ → ℂ) (K : ℝ) : Prop :=
  1 ≤ K ∧ SensePreserving f ∧ ∀ Q : Quadrilateral,
    curveModulus (Q.imageCurveFamily f) ≤ ENNReal.ofReal K * Q.modulus

end NoWanderingDomains
