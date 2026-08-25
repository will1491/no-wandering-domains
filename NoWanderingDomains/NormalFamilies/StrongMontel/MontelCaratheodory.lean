/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.NormalFamilies.Montel
import NoWanderingDomains.NormalFamilies.Spherical
import NoWanderingDomains.NormalFamilies.StrongMontel.ModularLift

/-!
# The Montel–Carathéodory theorem (strong Montel)

A family of holomorphic functions on an open `U ⊆ ℂ` omitting the two
values `0` and `1` is normal **as a family of sphere-valued maps**
(`montel_caratheodory`). The spherical statement is the correct one:
the constant family `fₙ ≡ n` omits `0, 1` but converges to `∞`, so
no `ℂ`-valued normality can hold.

The proof is the classical case analysis on a ball
(`montel_caratheodory_ball_seq`), globalized by a diagonal argument
over a countable cover:

* pass to a subsequence with `fₙ(c) → α` in the compact sphere `ℂ̂`;
* `α ∉ {0, 1, ∞}`: lift through `modularLambda` with base points in a
  fixed compact of `𝔻` (`modularLambda_exists_compact_section`), apply
  classical Montel to the bounded lifts, exclude unimodular limits by
  the maximum principle, and push the limit down through `λ`;
* `α = 0`: the square-root trick — a holomorphic square root
  `s` of `f` (via `exists_log_of_ball_of_ne_zero`) omits `0, ±1`, so
  `(s+1)/2` omits `0, 1` with values at `c` tending to the interior
  point `1/2`; the previous case applies, and Hurwitz forces the
  limit of `f = s²` to vanish identically;
* `α = 1` and `α = ∞`: reduce to `α = 0` via `1 − f` and `1/f`.
-/

namespace NoWanderingDomains

open Complex Metric Set Filter OnePoint

/-- The spherical (chordal) distance between finite points is dominated
by twice the Euclidean distance: the chordal denominators are `≥ 1`. -/
theorem sphericalDist_coe_le_norm_sub (z w : ℂ) :
    sphericalDist (z : ℂ̂) (w : ℂ̂) ≤ 2 * ‖z - w‖ := by
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 + ‖z‖ ^ 2) :=
    Real.one_le_sqrt.mpr (le_add_of_nonneg_right (sq_nonneg _))
  have h2 : (1 : ℝ) ≤ Real.sqrt (1 + ‖w‖ ^ 2) :=
    Real.one_le_sqrt.mpr (le_add_of_nonneg_right (sq_nonneg _))
  change 2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2)) ≤ 2 * ‖z - w‖
  exact div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le h1 h2)

/-- Locally uniform convergence of `ℂ`-valued functions upgrades to
locally uniform convergence of the sphere-valued coercions: the
inclusion `ℂ ↪ ℂ̂` is `2`-Lipschitz for the chordal metric. -/
theorem tendstoLocallyUniformlyOn_coe {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {U : Set ℂ}
    (h : TendstoLocallyUniformlyOn F g atTop U) :
    TendstoLocallyUniformlyOn (fun n z => ((F n z : ℂ̂)))
      (fun z => (g z : ℂ̂)) atTop U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at h ⊢
  intro ε hε x hx
  obtain ⟨t, ht, hev⟩ := h (ε / 2) (by linarith) x hx
  refine ⟨t, ht, ?_⟩
  filter_upwards [hev] with n hn y hy
  show dist ((g y : ℂ̂)) ((F n y : ℂ̂)) < ε
  calc dist ((g y : ℂ̂)) ((F n y : ℂ̂)) ≤ 2 * ‖g y - F n y‖ :=
        sphericalDist_coe_le_norm_sub _ _
    _ = 2 * dist (g y) (F n y) := by rw [Complex.dist_eq]
    _ < 2 * (ε / 2) := by have := hn y hy; linarith
    _ = ε := by ring

/-- If the reciprocals of a family tend locally uniformly to `0`, the
family itself tends locally uniformly to `∞` on the sphere:
`sphericalDist (f z) ∞ = 2/√(1 + ‖f z‖²) ≤ 2‖g z‖` when
`f z * g z = 1`. -/
theorem tendstoLocallyUniformlyOn_infty_of_inv {F G : ℕ → ℂ → ℂ}
    {U : Set ℂ}
    (hFG : ∀ n, ∀ z ∈ U, F n z * G n z = 1)
    (h : TendstoLocallyUniformlyOn G (fun _ => (0 : ℂ)) atTop U) :
    TendstoLocallyUniformlyOn (fun n z => ((F n z : ℂ̂)))
      (fun _ => (∞ : ℂ̂)) atTop U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at h ⊢
  intro ε hε x hx
  obtain ⟨t, ht, hev⟩ := h (ε / 2) (by linarith) x hx
  refine ⟨t ∩ U, inter_mem ht self_mem_nhdsWithin, ?_⟩
  filter_upwards [hev] with n hn y hy
  obtain ⟨hyt, hyU⟩ := hy
  have hG_small : ‖G n y‖ < ε / 2 := by
    have := hn y hyt
    rwa [dist_zero_left] at this
  have hprod := hFG n y hyU
  have hF_ne : F n y ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hF_pos : 0 < ‖F n y‖ := norm_pos_iff.mpr hF_ne
  have hGF : ‖G n y‖ * ‖F n y‖ = 1 := by
    rw [← norm_mul, mul_comm, hprod, norm_one]
  have hsq : ‖F n y‖ ≤ Real.sqrt (1 + ‖F n y‖ ^ 2) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      (le_add_of_nonneg_left zero_le_one)
  change dist (∞ : ℂ̂) ((F n y : ℂ̂)) < ε
  calc dist (∞ : ℂ̂) ((F n y : ℂ̂)) = 2 / Real.sqrt (1 + ‖F n y‖ ^ 2) := rfl
    _ ≤ 2 / ‖F n y‖ := div_le_div_of_nonneg_left (by norm_num) hF_pos hsq
    _ = 2 * ‖G n y‖ := by
        rw [div_eq_iff hF_pos.ne']
        linear_combination (-2 : ℝ) * hGF
    _ < 2 * (ε / 2) := by linarith
    _ = ε := by ring

/-- Composition of a locally uniform limit with `modularLambda` on the
disk: if `Fₙ → G` locally uniformly on the open `U` with all values in
`𝔻`, then `λ ∘ Fₙ → λ ∘ G` locally uniformly. On each compact the
values eventually stay in a compact of `𝔻`, where `modularLambda` is
uniformly continuous. -/
theorem tendstoLocallyUniformlyOn_modularLambda_comp
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ n, Set.MapsTo (F n) U (ball (0 : ℂ) 1))
    (hG : Set.MapsTo G U (ball (0 : ℂ) 1))
    (hG_cont : ContinuousOn G U)
    (h : TendstoLocallyUniformlyOn F G atTop U) :
    TendstoLocallyUniformlyOn (fun n z => modularLambda (F n z))
      (fun z => modularLambda (G z)) atTop U := by
  -- `hF` is not needed: `F n y` eventually lies in the `δ`-cthickening of
  -- `G '' K` by the convergence alone.
  have _ := hF
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at h ⊢
  intro K hKU hK
  have hGK_cpt : IsCompact (G '' K) := hK.image_of_continuousOn (hG_cont.mono hKU)
  have hGK_sub : G '' K ⊆ ball (0 : ℂ) 1 :=
    image_subset_iff.mpr fun z hz => hG (hKU hz)
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    hGK_cpt.exists_cthickening_subset_open isOpen_ball hGK_sub
  have hC_cpt : IsCompact (cthickening δ (G '' K)) := hGK_cpt.cthickening
  have huc : UniformContinuousOn modularLambda (cthickening δ (G '' K)) :=
    hC_cpt.uniformContinuousOn_of_continuous
      (modularLambda_differentiableOn.continuousOn.mono hδ_sub)
  have hTU := h K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hTU ⊢
  intro ε hε
  obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  have hmin_pos : 0 < min δ δ' := lt_min hδ_pos hδ'_pos
  filter_upwards [hTU (min δ δ') hmin_pos] with n hn y hy
  have h1 : dist (G y) (F n y) < min δ δ' := hn y hy
  have hGy : G y ∈ cthickening δ (G '' K) :=
    self_subset_cthickening _ (mem_image_of_mem G hy)
  have hFy : F n y ∈ cthickening δ (G '' K) :=
    mem_cthickening_of_dist_le (F n y) (G y) δ _ (mem_image_of_mem G hy)
      (by rw [dist_comm]; exact (h1.trans_le (min_le_left _ _)).le)
  exact hδ' (G y) hGy (F n y) hFy (h1.trans_le (min_le_right _ _))

/-- **Hurwitz vanishing.** If holomorphic functions without zeros on an
open preconnected `V` converge locally uniformly to `g`, and `g`
vanishes at one point of `V`, then `g` vanishes identically on `V`. -/
theorem eqOn_zero_of_tendstoLocallyUniformlyOn_of_ne_zero
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {V : Set ℂ} {c : ℂ}
    (hV : IsOpen V) (hVc : IsPreconnected V)
    (hF_hol : ∀ n, DifferentiableOn ℂ (F n) V)
    (hF_ne : ∀ n, ∀ z ∈ V, F n z ≠ 0)
    (h : TendstoLocallyUniformlyOn F g atTop V)
    (hc : c ∈ V) (hg0 : g c = 0) :
    ∀ z ∈ V, g z = 0 := by
  exact hurwitz hV hVc (Filter.Eventually.of_forall hF_hol) hF_ne h hc hg0

/-- A countable cover of an open set by balls whose doubles still fit:
every point of `U` lies in some `ball (c n) (r n)` with
`ball (c n) (2 * r n) ⊆ U`. Rational centers and radii. -/
theorem exists_countable_ball_cover {U : Set ℂ} (hU : IsOpen U) :
    ∃ (c : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ n, ball (c n) (2 * r n) ⊆ U) ∧
      ∀ z ∈ U, ∃ n, z ∈ ball (c n) (r n) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat (ℚ × ℚ × ℚ)
  refine ⟨fun n => (((e n).1 : ℝ) : ℂ) + (((e n).2.1 : ℝ) : ℂ) * Complex.I,
    fun n => if ball ((((e n).1 : ℝ) : ℂ) + (((e n).2.1 : ℝ) : ℂ) * Complex.I)
        (2 * ((e n).2.2 : ℝ)) ⊆ U then ((e n).2.2 : ℝ) else 0, ?_, ?_⟩
  · intro n
    change ball ((((e n).1 : ℝ) : ℂ) + (((e n).2.1 : ℝ) : ℂ) * Complex.I)
        (2 * (if ball ((((e n).1 : ℝ) : ℂ) + (((e n).2.1 : ℝ) : ℂ) * Complex.I)
          (2 * ((e n).2.2 : ℝ)) ⊆ U then ((e n).2.2 : ℝ) else 0)) ⊆ U
    by_cases hcond : ball ((((e n).1 : ℝ) : ℂ) + (((e n).2.1 : ℝ) : ℂ) * Complex.I)
        (2 * ((e n).2.2 : ℝ)) ⊆ U
    · rwa [if_pos hcond]
    · rw [if_neg hcond, mul_zero, ball_zero]
      exact empty_subset U
  · intro z hz
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hU z hz
    obtain ⟨q₃, hq₃_pos, hq₃_lt⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 4 by linarith)
    obtain ⟨q₁, hq₁⟩ := exists_rat_near z.re (show (0 : ℝ) < (q₃ : ℝ) / 2 by linarith)
    obtain ⟨q₂, hq₂⟩ := exists_rat_near z.im (show (0 : ℝ) < (q₃ : ℝ) / 2 by linarith)
    obtain ⟨n, hn⟩ := he (q₁, q₂, q₃)
    have h1 : (e n).1 = q₁ := by rw [hn]
    have h2 : (e n).2.1 = q₂ := by rw [hn]
    have h3 : (e n).2.2 = q₃ := by rw [hn]
    have hzw : dist z (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I) < (q₃ : ℝ) := by
      rw [Complex.dist_eq]
      calc ‖z - (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I)‖
          ≤ |(z - (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I)).re|
            + |(z - (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = |z.re - (q₁ : ℝ)| + |z.im - (q₂ : ℝ)| := by simp
        _ < (q₃ : ℝ) / 2 + (q₃ : ℝ) / 2 := add_lt_add hq₁ hq₂
        _ = (q₃ : ℝ) := by ring
    have hcond : ball (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I)
        (2 * (q₃ : ℝ)) ⊆ U := by
      intro y hy
      apply hball
      rw [Metric.mem_ball] at hy ⊢
      have htri := dist_triangle y (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I) z
      have hwz : dist (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I) z < (q₃ : ℝ) := by
        rw [dist_comm]; exact hzw
      linarith
    refine ⟨n, ?_⟩
    rw [← h1, ← h2, ← h3] at hzw hcond
    change z ∈ ball ((((e n).1 : ℝ) : ℂ) + (((e n).2.1 : ℝ) : ℂ) * Complex.I)
        (if ball ((((e n).1 : ℝ) : ℂ) + (((e n).2.1 : ℝ) : ℂ) * Complex.I)
          (2 * ((e n).2.2 : ℝ)) ⊆ U then ((e n).2.2 : ℝ) else 0)
    rw [Metric.mem_ball, if_pos hcond]
    exact hzw

/-- **Montel–Carathéodory on a ball, sequence form.** A sequence of
holomorphic functions on `ball c r` omitting `0` and `1` has a
subsequence converging locally uniformly on the ball as sphere-valued
maps. -/
theorem montel_caratheodory_ball_seq {f : ℕ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hol : ∀ n, DifferentiableOn ℂ (f n) (ball c r))
    (homit : ∀ n, ∀ z ∈ ball c r, f n z ≠ 0 ∧ f n z ≠ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : ℂ → ℂ̂,
        TendstoLocallyUniformlyOn (fun k z => ((f (φ k) z : ℂ̂))) g
          atTop (ball c r) := by
  by_cases hne : (ball c r).Nonempty
  case neg =>
    refine ⟨id, strictMono_id, fun _ => (∞ : ℂ̂), ?_⟩
    intro u _ z hz
    exact absurd (Set.nonempty_of_mem hz) hne
  case pos =>
  have hc : c ∈ ball c r := Metric.mem_ball_self (Metric.nonempty_ball.mp hne)
  -- ### Case-A kernel: values at the center converge to a point of `ℂ ∖ {0, 1}`.
  have caseA : ∀ F : ℕ → ℂ → ℂ, (∀ n, DifferentiableOn ℂ (F n) (ball c r)) →
      (∀ n, ∀ z ∈ ball c r, F n z ≠ 0 ∧ F n z ≠ 1) →
      ∀ a : ℂ, a ≠ 0 → a ≠ 1 → Tendsto (fun n => F n c) atTop (nhds a) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ,
        Set.MapsTo G (ball c r) (ball (0 : ℂ) 1) ∧ ContinuousOn G (ball c r) ∧
        TendstoLocallyUniformlyOn (fun k z => F (φ k) z)
          (fun z => modularLambda (G z)) atTop (ball c r) := by
    intro F holF homitF a ha0 ha1 htend
    -- a compact neighborhood of `a` inside `ℂ ∖ {0, 1}`
    have hd0 : 0 < dist a 0 := dist_pos.mpr ha0
    have hd1 : 0 < dist a 1 := dist_pos.mpr ha1
    obtain ⟨δ, hδpos, hδ0, hδ1⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < dist a 0 ∧ δ < dist a 1 := by
      refine ⟨min (dist a 0) (dist a 1) / 2, half_pos (lt_min hd0 hd1), ?_, ?_⟩
      · have := min_le_left (dist a 0) (dist a 1); linarith
      · have := min_le_right (dist a 0) (dist a 1); linarith
    have hL_omits : ∀ w ∈ closedBall a δ, w ≠ 0 ∧ w ≠ 1 := by
      intro w hw
      rw [Metric.mem_closedBall] at hw
      constructor
      · rintro rfl; rw [dist_comm] at hw; linarith
      · rintro rfl; rw [dist_comm] at hw; linarith
    -- a compact section domain over the compact neighborhood
    obtain ⟨K, hK_cpt, hK_sub, hK_sec⟩ :=
      modularLambda_exists_compact_section (isCompact_closedBall a δ) hL_omits
    -- eventually the central values are in the compact neighborhood
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (htend.eventually_mem (Metric.closedBall_mem_nhds a hδpos))
    -- fibre points in `K` over the (shifted) central values
    choose e he_mem he_eq using fun n : ℕ =>
      hK_sec (F (n + N) c) (hN (n + N) (Nat.le_add_left N n))
    -- holomorphic lifts through `modularLambda` with base points `e n`
    choose Lft hLft_hol hLft_maps hLft_eq hLft_c using fun n : ℕ =>
      modularLambda_exists_holomorphic_lift_ball (holF (n + N)) (homitF (n + N)) hc
        (hK_sub (he_mem n)) (he_eq n)
    -- classical Montel for the lifted family (uniformly bounded by 1)
    have hbdd : LocallyUniformlyBounded {h : ℂ → ℂ | ∃ n, h = Lft n} (ball c r) := by
      intro K' hK' _
      refine ⟨1, ?_⟩
      rintro h ⟨n, rfl⟩ z hz
      exact (mem_ball_zero_iff.mp (hLft_maps n (hK' hz))).le
    have hhol𝓖 : ∀ h ∈ {h : ℂ → ℂ | ∃ n, h = Lft n}, DifferentiableOn ℂ h (ball c r) := by
      rintro h ⟨n, rfl⟩
      exact hLft_hol n
    obtain ⟨ψ, hψ, G, hG⟩ :=
      montel_locallyBounded Metric.isOpen_ball hbdd hhol𝓖 (fun n => ⟨Lft n, n, rfl⟩)
    have hG' : TendstoLocallyUniformlyOn (fun k => Lft (ψ k)) G atTop (ball c r) := hG
    -- the limit `G` is holomorphic with `‖G‖ ≤ 1`, and `G c` lies in the compact `K ⊆ 𝔻`
    have hG_hol : DifferentiableOn ℂ G (ball c r) :=
      hG'.differentiableOn (Filter.Eventually.of_forall fun k => hLft_hol (ψ k))
        Metric.isOpen_ball
    have hG_cont : ContinuousOn G (ball c r) := hG_hol.continuousOn
    have hG_le : ∀ z ∈ ball c r, ‖G z‖ ≤ 1 := by
      intro z hz
      exact le_of_tendsto (hG'.tendsto_at hz).norm
        (Filter.Eventually.of_forall fun k =>
          (mem_ball_zero_iff.mp (hLft_maps (ψ k) hz)).le)
    have hGc_lt : ‖G c‖ < 1 := by
      have hGc_mem : G c ∈ K := by
        refine hK_cpt.isClosed.mem_of_tendsto (hG'.tendsto_at hc)
          (Filter.Eventually.of_forall fun k => ?_)
        rw [hLft_c (ψ k)]
        exact he_mem (ψ k)
      exact mem_ball_zero_iff.mp (hK_sub hGc_mem)
    -- maximum principle: `G` maps the ball into the open disk
    have hG_maps : Set.MapsTo G (ball c r) (ball (0 : ℂ) 1) := by
      intro z hz
      rw [mem_ball_zero_iff]
      rcases lt_or_eq_of_le (hG_le z hz) with hlt | heq1
      · exact hlt
      · exfalso
        have hmax : IsMaxOn (norm ∘ G) (ball c r) z := by
          rw [isMaxOn_iff]
          intro w hw
          exact (hG_le w hw).trans_eq heq1.symm
        have heqG := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
          ((convex_ball c r).isPreconnected) Metric.isOpen_ball hG_hol hz hmax
        have hGcz : G c = G z := heqG hc
        rw [hGcz, heq1] at hGc_lt
        exact lt_irrefl _ hGc_lt
    -- push the limit down through `modularLambda`
    have hTLU_lam : TendstoLocallyUniformlyOn (fun k z => modularLambda (Lft (ψ k) z))
        (fun z => modularLambda (G z)) atTop (ball c r) :=
      tendstoLocallyUniformlyOn_modularLambda_comp Metric.isOpen_ball
        (fun k => hLft_maps (ψ k)) hG_maps hG_cont hG'
    refine ⟨fun k => ψ k + N, hψ.add_const N, G, hG_maps, hG_cont, ?_⟩
    exact hTLU_lam.congr fun k z hz => hLft_eq (ψ k) z hz
  -- ### Key-0 kernel: values at the center converge to `0`; the square-root trick.
  have key0 : ∀ F : ℕ → ℂ → ℂ, (∀ n, DifferentiableOn ℂ (F n) (ball c r)) →
      (∀ n, ∀ z ∈ ball c r, F n z ≠ 0 ∧ F n z ≠ 1) →
      Tendsto (fun n => F n c) atTop (nhds (0 : ℂ)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun k z => F (φ k) z) (fun _ => (0 : ℂ))
          atTop (ball c r) := by
    intro F holF homitF htendF
    -- holomorphic logarithms, hence square roots `exp (g/2)`
    choose g hg_hol hg_exp using fun n : ℕ =>
      exists_log_of_ball_of_ne_zero (holF n) (fun z hz => (homitF n z hz).1)
    have hs_sq : ∀ n, ∀ z ∈ ball c r, Complex.exp (g n z / 2) ^ 2 = F n z := by
      intro n z hz
      rw [sq, ← Complex.exp_add, add_halves]
      exact hg_exp n z hz
    -- the family `m = (s + 1) / 2` omits `0, 1` and tends to `1/2` at the center
    have hM_hol : ∀ n, DifferentiableOn ℂ
        ((fun n z => (Complex.exp (g n z / 2) + 1) / 2) n) (ball c r) :=
      fun n => (DifferentiableOn.add_const 1 ((hg_hol n).div_const 2).cexp).div_const 2
    have hM_omit : ∀ n, ∀ z ∈ ball c r,
        (fun n z => (Complex.exp (g n z / 2) + 1) / 2) n z ≠ 0 ∧
        (fun n z => (Complex.exp (g n z / 2) + 1) / 2) n z ≠ 1 := by
      intro n z hz
      constructor
      · intro h0
        have hs : Complex.exp (g n z / 2) = -1 := by
          have h0' : (Complex.exp (g n z / 2) + 1) / 2 = 0 := h0
          linear_combination 2 * h0'
        have : F n z = 1 := by rw [← hs_sq n z hz, hs]; norm_num
        exact (homitF n z hz).2 this
      · intro h1
        have hs : Complex.exp (g n z / 2) = 1 := by
          have h1' : (Complex.exp (g n z / 2) + 1) / 2 = 1 := h1
          linear_combination 2 * h1'
        have : F n z = 1 := by rw [← hs_sq n z hz, hs]; norm_num
        exact (homitF n z hz).2 this
    have hM_tend : Tendsto (fun n => (Complex.exp (g n c / 2) + 1) / 2) atTop
        (nhds ((1 : ℂ) / 2)) := by
      have hs_tend : Tendsto (fun n => Complex.exp (g n c / 2)) atTop (nhds (0 : ℂ)) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hnorm_eq : ∀ n, ‖Complex.exp (g n c / 2)‖ = Real.sqrt ‖F n c‖ := by
          intro n
          rw [← hs_sq n c hc, norm_pow, Real.sqrt_sq (norm_nonneg _)]
        have hFnorm : Tendsto (fun n => ‖F n c‖) atTop (nhds (0 : ℝ)) :=
          tendsto_zero_iff_norm_tendsto_zero.mp htendF
        have hsqrt : Tendsto (fun n => Real.sqrt ‖F n c‖) atTop (nhds (0 : ℝ)) := by
          have := (Real.continuous_sqrt.tendsto 0).comp hFnorm
          simpa [Real.sqrt_zero] using! this
        exact hsqrt.congr fun n => (hnorm_eq n).symm
      have := (hs_tend.add_const 1).div_const 2
      have h02 : ((0 : ℂ) + 1) / 2 = 1 / 2 := by norm_num
      rwa [h02] at this
    -- Case A applied to the `m` family with limit value `1/2 ∉ {0, 1}`
    obtain ⟨ψ, hψ, G, hG_maps, hG_cont, hTLU_M⟩ :=
      caseA (fun n z => (Complex.exp (g n z / 2) + 1) / 2) hM_hol hM_omit
        ((1 : ℂ) / 2) (by norm_num) (by norm_num) hM_tend
    have hTLU_M' : TendstoLocallyUniformlyOn
        (fun k z => (Complex.exp (g (ψ k) z / 2) + 1) / 2)
        (fun z => modularLambda (G z)) atTop (ball c r) := hTLU_M
    -- the limit takes the value `1/2` at the center
    have hHc : modularLambda (G c) = 1 / 2 := by
      refine tendsto_nhds_unique (hTLU_M'.tendsto_at hc) ?_
      exact hM_tend.comp hψ.tendsto_atTop
    have hH_cont : ContinuousOn (fun z => modularLambda (G z)) (ball c r) :=
      modularLambda_differentiableOn.continuousOn.comp hG_cont hG_maps
    -- the affine renormalization `2m - 1 = s` converges locally uniformly
    have hUC : UniformContinuous fun w : ℂ => 2 * w - 1 := by
      have h1 : UniformContinuous fun w : ℂ => (2 : ℂ) • w :=
        uniformContinuous_const_smul (2 : ℂ)
      simpa [smul_eq_mul] using h1.sub uniformContinuous_const
    have hTLU_A : TendstoLocallyUniformlyOn
        (fun k z => 2 * ((Complex.exp (g (ψ k) z / 2) + 1) / 2) - 1)
        (fun z => 2 * modularLambda (G z) - 1) atTop (ball c r) :=
      hurwitz4 hTLU_M' hUC
    -- squares converge locally uniformly: `F ∘ ψ → (2λ∘G - 1)²`
    have hTLU_sq : TendstoLocallyUniformlyOn (fun k z => F (ψ k) z)
        (fun z => (2 * modularLambda (G z) - 1) * (2 * modularLambda (G z) - 1))
        atTop (ball c r) := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
      intro K hK hKc
      have hA_unif : TendstoUniformlyOn
          (fun k z => 2 * ((Complex.exp (g (ψ k) z / 2) + 1) / 2) - 1)
          (fun z => 2 * modularLambda (G z) - 1) atTop K :=
        (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).1
          hTLU_A K hK hKc
      have ha_cont : ContinuousOn (fun z => 2 * modularLambda (G z) - 1) K :=
        (continuousOn_const.mul (hH_cont.mono hK)).sub continuousOn_const
      have hmul := hA_unif.mul_of_compact hA_unif ha_cont ha_cont hKc
      refine hmul.congr (Filter.Eventually.of_forall fun k z hz => ?_)
      change (2 * ((Complex.exp (g (ψ k) z / 2) + 1) / 2) - 1) *
          (2 * ((Complex.exp (g (ψ k) z / 2) + 1) / 2) - 1) = F (ψ k) z
      rw [show (2 : ℂ) * ((Complex.exp (g (ψ k) z / 2) + 1) / 2) - 1
            = Complex.exp (g (ψ k) z / 2) by ring, ← sq]
      exact hs_sq (ψ k) z (hK hz)
    -- Hurwitz: the limit vanishes at `c`, hence identically
    have hvanish : ∀ z ∈ ball c r,
        (2 * modularLambda (G z) - 1) * (2 * modularLambda (G z) - 1) = 0 := by
      refine eqOn_zero_of_tendstoLocallyUniformlyOn_of_ne_zero Metric.isOpen_ball
        ((convex_ball c r).isPreconnected) (fun k => holF (ψ k))
        (fun k z hz => (homitF (ψ k) z hz).1) hTLU_sq hc ?_
      show (2 * modularLambda (G c) - 1) * (2 * modularLambda (G c) - 1) = 0
      rw [hHc]
      norm_num
    exact ⟨ψ, hψ, hTLU_sq.congr_right fun z hz => hvanish z hz⟩
  -- ### Extraction of a sphere-convergent subsequence of central values.
  obtain ⟨α, -, σ, hσ, hα⟩ :=
    isCompact_univ.tendsto_subseq (x := fun n => ((f n c : ℂ̂))) fun n => Set.mem_univ _
  rcases α with _ | a
  · -- `α = ∞`: pass to reciprocals, which tend to `0` at the center
    have hcb : Tendsto (fun k => f (σ k) c) atTop (Bornology.cobounded ℂ) := by
      have h1 : Tendsto (fun k => ((f (σ k) c : ℂ̂))) atTop (nhds (∞ : ℂ̂)) := hα
      have h2 : Tendsto (fun k => f (σ k) c) atTop
          (Filter.comap ((↑) : ℂ → ℂ̂) (nhds (∞ : ℂ̂))) := tendsto_comap_iff.mpr h1
      rwa [OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact,
        ← Metric.cobounded_eq_cocompact] at h2
    have htend_inv : Tendsto (fun k => (f (σ k) c)⁻¹) atTop (nhds (0 : ℂ)) :=
      tendsto_inv₀_cobounded.comp hcb
    obtain ⟨ψ, hψ, hT0⟩ := key0 (fun k z => (f (σ k) z)⁻¹)
      (fun k => (hol (σ k)).inv fun z hz => (homit (σ k) z hz).1)
      (fun k z hz => ⟨inv_ne_zero (homit (σ k) z hz).1,
        fun h1 => (homit (σ k) z hz).2 (inv_eq_one.mp h1)⟩)
      htend_inv
    refine ⟨σ ∘ ψ, hσ.comp hψ, fun _ => (∞ : ℂ̂), ?_⟩
    exact tendstoLocallyUniformlyOn_infty_of_inv
      (fun k z hz => mul_inv_cancel₀ (homit (σ (ψ k)) z hz).1) hT0
  · -- `α = a` finite
    have htendC : Tendsto (fun k => f (σ k) c) atTop (nhds a) := by
      rw [OnePoint.isOpenEmbedding_coe.tendsto_nhds_iff]
      exact hα
    by_cases ha0 : a = 0
    · -- `a = 0`: apply the key-0 kernel directly
      subst ha0
      obtain ⟨ψ, hψ, hT0⟩ :=
        key0 (fun k => f (σ k)) (fun k => hol (σ k)) (fun k => homit (σ k)) htendC
      exact ⟨σ ∘ ψ, hσ.comp hψ, fun _ => ((0 : ℂ) : ℂ̂),
        tendstoLocallyUniformlyOn_coe hT0⟩
    by_cases ha1 : a = 1
    · -- `a = 1`: apply the key-0 kernel to `1 - f`
      subst ha1
      have htend1 : Tendsto (fun k => 1 - f (σ k) c) atTop (nhds (0 : ℂ)) := by
        have h1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds (1 : ℂ)) := tendsto_const_nhds
        have h2 := h1.sub htendC
        rwa [sub_self] at h2
      obtain ⟨ψ, hψ, hT0⟩ := key0 (fun k z => 1 - f (σ k) z)
        (fun k => (hol (σ k)).const_sub 1)
        (fun k z hz => ⟨sub_ne_zero.mpr (Ne.symm (homit (σ k) z hz).2),
          fun h1 => (homit (σ k) z hz).1 (by linear_combination -h1)⟩)
        htend1
      have hTLU1 : TendstoLocallyUniformlyOn (fun k z => f (σ (ψ k)) z)
          (fun _ => (1 : ℂ)) atTop (ball c r) := by
        have h2 : TendstoLocallyUniformlyOn (fun k z => 1 - (1 - f (σ (ψ k)) z))
            (fun _ => 1 - (0 : ℂ)) atTop (ball c r) :=
          hurwitz4 hT0 (uniformContinuous_const.sub uniformContinuous_id)
        refine (h2.congr fun k z _ => by ring).congr_right fun z _ => by norm_num
      exact ⟨σ ∘ ψ, hσ.comp hψ, fun _ => ((1 : ℂ) : ℂ̂),
        tendstoLocallyUniformlyOn_coe hTLU1⟩
    · -- `a ∉ {0, 1}`: the Case-A kernel applies
      obtain ⟨ψ, hψ, G, _, _, hT⟩ :=
        caseA (fun k => f (σ k)) (fun k => hol (σ k)) (fun k => homit (σ k))
          a ha0 ha1 htendC
      exact ⟨σ ∘ ψ, hσ.comp hψ, fun z => ((modularLambda (G z) : ℂ̂)),
        tendstoLocallyUniformlyOn_coe hT⟩

/-- **The Montel–Carathéodory theorem (strong Montel).** A family of
holomorphic functions on an open set omitting the values `0` and `1`
is normal as a family of maps into the Riemann sphere: every sequence
has a subsequence converging locally uniformly for the spherical
metric (the limit may be the constant `∞`).

The conclusion is stated for the sphere-valued coercions of the
family; `ℂ`-valued normality is false (constant functions `fₙ ≡ n`
omit `0, 1` and converge to `∞`). -/
theorem montel_caratheodory {𝓕 : Set (ℂ → ℂ)} {U : Set ℂ}
    (hU : IsOpen U)
    (hol : ∀ f ∈ 𝓕, DifferentiableOn ℂ f U)
    (homit : ∀ f ∈ 𝓕, ∀ z ∈ U, f z ≠ 0 ∧ f z ≠ 1) :
    IsNormal ((fun f : ℂ → ℂ => fun z => ((f z : ℂ̂))) '' 𝓕) U := by
  intro seq
  -- Step 1: choose representatives `f n ∈ 𝓕` of the sequence.
  have hch : ∀ n : ℕ, ∃ f₀ : ℂ → ℂ, f₀ ∈ 𝓕 ∧
      (fun z => ((f₀ z : ℂ̂))) = ((seq n : ℂ → ℂ̂)) := by
    intro n
    obtain ⟨f₀, hf₀, heq⟩ := (seq n).2
    exact ⟨f₀, hf₀, heq⟩
  choose f hf_mem hf_eq using hch
  -- Step 2: countable cover of `U` by balls whose doubles fit in `U`.
  obtain ⟨c, r, hsub, hcover⟩ := exists_countable_ball_cover hU
  -- Step 3: the extraction kernel on each double ball, for any reindexing.
  have step : ∀ (j : ℕ) (h : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ g0 : ℂ → ℂ̂,
        TendstoLocallyUniformlyOn (fun k z => ((f (h (ψ k)) z : ℂ̂))) g0
          atTop (ball (c j) (2 * r j)) := by
    intro j h
    exact montel_caratheodory_ball_seq (f := fun n => f (h n))
      (fun n => (hol _ (hf_mem (h n))).mono (hsub j))
      (fun n z hz => homit _ (hf_mem (h n)) z (hsub j hz))
  choose ψ hψ g hg using step
  -- Nested subsequences: `σ (j+1) = σ j ∘ ψ (j+1) (σ j)`.
  let σ : ℕ → ℕ → ℕ := fun j =>
    Nat.rec (motive := fun _ => ℕ → ℕ) (ψ 0 id) (fun i ih => ih ∘ ψ (i + 1) ih) j
  let G : ℕ → ℂ → ℂ̂ := fun j =>
    Nat.casesOn (motive := fun _ => ℂ → ℂ̂) j (g 0 id) (fun i => g (i + 1) (σ i))
  have σ_mono : ∀ j, StrictMono (σ j) := by
    intro j
    induction j with
    | zero => exact hψ 0 id
    | succ i ih => exact ih.comp (hψ (i + 1) (σ i))
  have σ_tlu : ∀ j, TendstoLocallyUniformlyOn
      (fun k z => ((f (σ j k) z : ℂ̂))) (G j) atTop (ball (c j) (2 * r j)) := by
    intro j
    cases j with
    | zero => exact hg 0 id
    | succ i => exact hg (i + 1) (σ i)
  -- Later stages refine earlier ones, with index growth.
  have σ_refine : ∀ i m, ∃ ρ : ℕ → ℕ, (∀ k, k ≤ ρ k) ∧
      ∀ k, σ (i + m) k = σ i (ρ k) := by
    intro i m
    induction m with
    | zero => exact ⟨id, fun k => le_rfl, fun k => rfl⟩
    | succ m ih =>
      obtain ⟨ρ, hρ, heq⟩ := ih
      exact ⟨fun k => ρ (ψ (i + m + 1) (σ (i + m)) k),
        fun k => le_trans (hψ (i + m + 1) (σ (i + m))).le_apply (hρ _),
        fun k => heq (ψ (i + m + 1) (σ (i + m)) k)⟩
  -- Step 4: the diagonal subsequence.
  let d : ℕ → ℕ := fun k => σ k k
  have d_mono : StrictMono d := by
    apply strictMono_nat_of_lt_succ
    intro k
    calc d k = σ k k := rfl
      _ < σ k (k + 1) := σ_mono k (Nat.lt_succ_self k)
      _ ≤ σ k (ψ (k + 1) (σ k) (k + 1)) :=
          (σ_mono k).monotone (hψ (k + 1) (σ k)).le_apply
      _ = d (k + 1) := rfl
  have d_sub : ∀ j k, j ≤ k → ∃ m, k ≤ m ∧ d k = σ j m := by
    intro j k hjk
    obtain ⟨ρ, hρ, heq⟩ := σ_refine j (k - j)
    have hk : j + (k - j) = k := Nat.add_sub_cancel' hjk
    have h2 := heq k
    rw [hk] at h2
    exact ⟨ρ k, hρ k, h2⟩
  -- The diagonal converges locally uniformly on every double ball.
  have d_tlu : ∀ j, TendstoLocallyUniformlyOn
      (fun k z => ((f (d k) z : ℂ̂))) (G j) atTop (ball (c j) (2 * r j)) := by
    intro j v hv x hx
    obtain ⟨t, ht, hF⟩ := σ_tlu j v hv x hx
    refine ⟨t, ht, ?_⟩
    rw [eventually_atTop] at hF ⊢
    obtain ⟨N, hN⟩ := hF
    refine ⟨max j N, fun k hk => ?_⟩
    obtain ⟨m, hkm, hdm⟩ := d_sub j k (le_trans (le_max_left j N) hk)
    intro y hy
    have h5 := hN m (le_trans (le_trans (le_max_right j N) hk) hkm) y hy
    change (G j y, ((f (d k) y : ℂ̂))) ∈ v
    rw [hdm]
    exact h5
  -- Step 5: patch the stage limits into a single limit function.
  have ball_sub : ∀ j, ball (c j) (r j) ⊆ ball (c j) (2 * r j) := by
    intro j z hz
    have h1 := mem_ball.mp hz
    have h0 : (0 : ℝ) < r j := lt_of_le_of_lt dist_nonneg h1
    exact mem_ball.mpr (by linarith)
  have glex : ∀ z : ℂ, ∃ w : ℂ̂, ∀ j, z ∈ ball (c j) (r j) → w = G j z := by
    intro z
    by_cases hex : ∃ i, z ∈ ball (c i) (r i)
    · obtain ⟨i, hi⟩ := hex
      refine ⟨G i z, fun j hj => ?_⟩
      exact tendsto_nhds_unique ((d_tlu i).tendsto_at (ball_sub i hi))
        ((d_tlu j).tendsto_at (ball_sub j hj))
    · exact ⟨∞, fun j hj => absurd ⟨j, hj⟩ hex⟩
  choose gl hgl using glex
  -- On `U`, the patched limit agrees with each stage limit on its double ball.
  have gl_eq_on : ∀ j, ∀ z ∈ U, z ∈ ball (c j) (2 * r j) → gl z = G j z := by
    intro j z hzU hz
    obtain ⟨i, hi⟩ := hcover z hzU
    rw [hgl z i hi]
    exact tendsto_nhds_unique ((d_tlu i).tendsto_at (ball_sub i hi))
      ((d_tlu j).tendsto_at hz)
  -- Step 6: locally uniform convergence on `U` via finite subcovers.
  refine ⟨d, d_mono, gl, ?_⟩
  have hseq_eq : (fun n => ((seq (d n) : ℂ → ℂ̂))) =
      fun n z => ((f (d n) z : ℂ̂)) := by
    funext n
    exact (hf_eq (d n)).symm
  rw [hseq_eq, tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover (fun j => ball (c j) (r j))
    (fun j => isOpen_ball) (fun z hz => mem_iUnion.mpr (hcover z (hKU hz)))
  -- Uniform convergence on each piece `K ∩ ball (c j) (r j)`.
  have piece : ∀ j : ℕ, TendstoUniformlyOn (fun k z => ((f (d k) z : ℂ̂))) gl
      atTop (K ∩ ball (c j) (r j)) := by
    intro j
    rcases le_or_gt (r j) 0 with h0 | h0
    · rw [ball_eq_empty.mpr h0, inter_empty]
      exact tendstoUniformlyOn_empty
    · have hsubK : K ∩ closedBall (c j) (r j) ⊆ ball (c j) (2 * r j) := fun z hz =>
        mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz.2) (by linarith))
      have hcomp : IsCompact (K ∩ closedBall (c j) (r j)) :=
        hK.inter_right isClosed_closedBall
      have h1 : TendstoUniformlyOn (fun k z => ((f (d k) z : ℂ̂))) (G j) atTop
          (K ∩ closedBall (c j) (r j)) :=
        (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp (d_tlu j) _
          hsubK hcomp
      have h2 : TendstoUniformlyOn (fun k z => ((f (d k) z : ℂ̂))) gl atTop
          (K ∩ closedBall (c j) (r j)) :=
        h1.congr_right fun z hz => (gl_eq_on j z (hKU hz.1) (hsubK hz)).symm
      exact h2.mono fun z hz => ⟨hz.1, ball_subset_closedBall hz.2⟩
  -- Uniform convergence passes to finite unions.
  have tuo_union : ∀ {s t : Set ℂ},
      TendstoUniformlyOn (fun k z => ((f (d k) z : ℂ̂))) gl atTop s →
      TendstoUniformlyOn (fun k z => ((f (d k) z : ℂ̂))) gl atTop t →
      TendstoUniformlyOn (fun k z => ((f (d k) z : ℂ̂))) gl atTop (s ∪ t) := by
    intro s t h1 h2 v hv
    filter_upwards [h1 v hv, h2 v hv] with n hn1 hn2 z hz
    rcases hz with hz | hz
    · exact hn1 z hz
    · exact hn2 z hz
  have main : ∀ t : Finset ℕ, TendstoUniformlyOn (fun k z => ((f (d k) z : ℂ̂))) gl
      atTop (K ∩ ⋃ j ∈ t, ball (c j) (r j)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [show (⋃ j ∈ (∅ : Finset ℕ), ball (c j) (r j)) = (∅ : Set ℂ) by simp,
        inter_empty]
      exact tendstoUniformlyOn_empty
    | insert j t hj ih =>
      rw [Finset.set_biUnion_insert, inter_union_distrib_left]
      exact tuo_union (piece j) ih
  exact (main S).mono fun z hz => ⟨hz, hS hz⟩

end NoWanderingDomains
