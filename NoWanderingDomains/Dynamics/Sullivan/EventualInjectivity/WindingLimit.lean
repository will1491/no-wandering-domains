/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Sullivan.EventualInjectivity.Loops

/-!
# Winding vanishing and the eventually-constant limit

The winding number of the filled curve vanishes when the fill avoids the Julia
set, and a wandering orbit forces eventually-constant limits.
-/

open Function OnePoint Filter Topology

namespace NoWanderingDomains

/-- **Loops whose fills avoid the Julia set are winding-trivial about it.**
If at some forward time every Julia point lies in the `∞`-component of the
complement of the pushed curve's sphere trace, then the pushed curve's fill
lies in its Fatou component; a simply connected neighborhood of the fill
inside the component null-homotopes the pushed curve, the null homotopy
descends through the covering steps, and homotopy invariance kills the
winding of the original loop about every Julia point. -/
theorem windingNumber_eq_zero_of_fill_avoids_julia {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    {N₀ : ℕ} {γ : C(unitInterval, ℂ)} (hγcl : γ 0 = γ 1)
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U N₀)
    {m : ℕ} {Γ : C(unitInterval, ℂ)}
    (hΓ : ∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂))))
    (hfill : ∀ w : ℂ̂, w ∈ JuliaSet f →
      w ∈ connectedComponentIn ((Set.range fun t => ((Γ t : ℂ̂)))ᶜ) ∞) :
    ∀ z : ℂ, ((z : ℂ̂)) ∈ JuliaSet f → windingNumber γ z = 0 := by
  classical
  -- ## Stage 0: shared helpers
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hOpenMap : IsOpenMap f := hf.isOpenMap (fun c => hf.ne_const hd1 c)
  have hjf : ∀ x : ℂ̂, x ∈ FatouSet f → x ∈ JuliaSet f → False := by
    intro x h1 h2
    rw [← compl_fatouSet] at h2
    exact h2 h1
  have hcoe : ∀ p : ℂ̂, p ≠ ∞ → ((chartFiniteMap p : ℂ) : ℂ̂) = p := by
    intro p hp
    cases p with
    | infty => exact absurd rfl hp
    | coe x => rfl
  have hfatou_iter : ∀ (n : ℕ) (x : ℂ̂), x ∈ FatouSet f →
      f^[n] x ∈ FatouSet f := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
        intro x hx
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hOpenMap (ih x hx)
  have hfwd : ∀ (n : ℕ) (x : ℂ̂), x ∈ fcOrbit f U N₀ →
      f^[n] x ∈ fcOrbit f U (N₀ + n) := by
    intro n x hx
    have hVfc' : IsFatouComponent f (fcOrbit f U N₀) :=
      isFatouComponent_fcOrbit N₀ hf hd1 hU
    rw [fcOrbit_add N₀ n hf hd1 hU]
    exact Set.mem_biUnion hx
      (mem_connectedComponentIn (hfatou_iter n x (hVfc'.subset_fatouSet hx)))
  -- ## Stage 1: the sphere trace of the pushed curve and the `∞`-component
  set Rsph : Set ℂ̂ := Set.range fun t => ((Γ t : ℂ̂)) with hRsphdef
  have hRcomp : IsCompact Rsph :=
    isCompact_range (OnePoint.continuous_coe.comp Γ.continuous)
  have hRc_open : IsOpen (Rsphᶜ) := hRcomp.isClosed.isOpen_compl
  have hinfR : ∞ ∈ (Rsphᶜ) := by
    intro h
    obtain ⟨t, ht⟩ := h
    exact OnePoint.coe_ne_infty (Γ t) ht
  set Uinf : Set ℂ̂ := connectedComponentIn (Rsphᶜ) ∞ with hUinfdef
  have hUinf_open : IsOpen Uinf := hRc_open.connectedComponentIn
  have hUinf_sub : Uinf ⊆ (Rsphᶜ) := connectedComponentIn_subset _ _
  have hinfUinf : ∞ ∈ Uinf := mem_connectedComponentIn hinfR
  -- ## Stage 2: the fill `K` — the chart points not in the `∞`-component
  set K : Set ℂ := {z : ℂ | ((z : ℂ̂)) ∉ Uinf} with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact (hUinf_open.isClosed_compl).preimage OnePoint.continuous_coe
  have htrK : ∀ t : unitInterval, Γ t ∈ K := by
    intro t
    change ((Γ t : ℂ̂)) ∉ Uinf
    intro hmem
    exact hUinf_sub hmem ⟨t, rfl⟩
  have hKne : K.Nonempty := ⟨Γ 0, htrK 0⟩
  -- ### boundedness: a punctured neighborhood of `∞` lies in `Uinf`
  obtain ⟨R₀, hR₀⟩ := (isCompact_range Γ.continuous).isBounded.subset_closedBall 0
  have hρpos : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have houter : IsPreconnected {w : ℂ | max R₀ 1 < ‖w‖} := by
    have himg : {w : ℂ | max R₀ 1 < ‖w‖} =
        (fun p : ℝ × ℝ => ((p.1 : ℂ)) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
          (Set.Ioi (max R₀ 1) ×ˢ Set.univ) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioi,
        Set.mem_univ, and_true, Prod.exists]
      constructor
      · intro hw
        exact ⟨‖w‖, Complex.arg w, hw, Complex.norm_mul_exp_arg_mul_I w⟩
      · rintro ⟨t, θ, ht, rfl⟩
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (lt_trans hρpos ht)]
        exact ht
    rw [himg]
    exact (isPreconnected_Ioi.prod isPreconnected_univ).image _
      ((Complex.continuous_ofReal.comp continuous_fst).mul
        (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp continuous_snd).mul
            continuous_const))).continuousOn
  have hclinf : (∞ : ℂ̂) ∈ closure
      ((fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | max R₀ 1 < ‖w‖}) := by
    rw [mem_closure_iff_nhds_basis (OnePoint.hasBasis_nhds_infty (X := ℂ))]
    rintro T ⟨hTcl, hTcp⟩
    obtain ⟨R₁, hR₁⟩ := hTcp.isBounded.subset_closedBall 0
    have hbig : max R₀ 1 < ‖((max (max R₀ 1) R₁ + 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [le_max_left (max R₀ 1) R₁, hρpos])]
      linarith [le_max_left (max R₀ 1) R₁]
    refine ⟨((((max (max R₀ 1) R₁ + 1 : ℝ) : ℂ)) : ℂ̂),
      ⟨((max (max R₀ 1) R₁ + 1 : ℝ) : ℂ), hbig, rfl⟩, Or.inl ⟨_, fun hmem => ?_, rfl⟩⟩
    have h2 := hR₁ hmem
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos (by linarith [le_max_left (max R₀ 1) R₁, hρpos])] at h2
    linarith [le_max_right (max R₀ 1) R₁]
  have hSpre : IsPreconnected
      ((fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | max R₀ 1 < ‖w‖} ∪ {∞}) := by
    refine (houter.image _ OnePoint.continuous_coe.continuousOn).subset_closure
      Set.subset_union_left (Set.union_subset subset_closure ?_)
    exact Set.singleton_subset_iff.mpr hclinf
  have hSsub : ((fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | max R₀ 1 < ‖w‖} ∪ {∞}) ⊆
      (Rsphᶜ) := by
    rintro x (⟨w, hw, rfl⟩ | hx)
    · intro hmem
      obtain ⟨t, ht⟩ := hmem
      have hwt : Γ t = w := OnePoint.coe_eq_coe.mp ht
      have h1 : ‖Γ t‖ ≤ R₀ := by
        have := hR₀ (Set.mem_range_self t)
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      rw [hwt] at h1
      simp only [Set.mem_ofPred_eq] at hw
      have h2 : R₀ ≤ max R₀ 1 := le_max_left _ _
      linarith
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hinfR
  have hSU : ((fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | max R₀ 1 < ‖w‖} ∪ {∞}) ⊆
      Uinf :=
    hSpre.subset_connectedComponentIn (Set.mem_union_right _ rfl) hSsub
  have hKball : K ⊆ Metric.closedBall 0 (max R₀ 1) := by
    intro w hw
    by_contra hout
    have h1 : max R₀ 1 < ‖w‖ := by
      rwa [Metric.mem_closedBall, dist_zero_right, not_le] at hout
    exact hw (hSU (Set.mem_union_left _ ⟨w, h1, rfl⟩))
  have hKcomp : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) (max R₀ 1)).of_isClosed_subset hKclosed hKball
  -- ## Stage 3: fullness — complementary components of `K` are unbounded
  have hUinf_conn : IsConnected Uinf := isConnected_connectedComponentIn_iff.mpr hinfR
  have hUinf_path : IsPathConnected Uinf :=
    (hUinf_open.isConnected_iff_isPathConnected).mp hUinf_conn
  have hKfull : ∀ w ∉ K, ¬Bornology.IsBounded (connectedComponentIn (Kᶜ) w) := by
    intro w hwK hbdd
    have hwU : ((w : ℂ̂)) ∈ Uinf := by
      by_contra h
      exact hwK h
    obtain ⟨p, hp⟩ := hUinf_path.joinedIn _ hwU _ hinfUinf
    -- first hitting time of `∞` along the path
    set S : Set ℝ := {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ p.extend s = ∞} with hSdef
    have hScl : IsClosed S := by
      have hSeq : S = Set.Icc (0 : ℝ) 1 ∩ p.extend ⁻¹' {∞} := rfl
      rw [hSeq]
      exact isClosed_Icc.inter (isClosed_singleton.preimage p.continuous_extend)
    have hSne : S.Nonempty := ⟨1, ⟨zero_le_one, le_refl 1⟩, p.extend_one⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    have ht₀S : sInf S ∈ S := hScl.csInf_mem hSne hSbdd
    have ht₀pos : 0 < sInf S := by
      rcases lt_or_eq_of_le ht₀S.1.1 with h | h
      · exact h
      · exfalso
        have h0 : p.extend (sInf S) = ∞ := ht₀S.2
        rw [← h, p.extend_zero] at h0
        exact OnePoint.coe_ne_infty w h0
    have ht₀le1 : sInf S ≤ 1 := ht₀S.1.2
    -- the arc before the hitting time stays in `Uinf` and off `∞`
    have harc : ∀ s ∈ Set.Ico (0 : ℝ) (sInf S),
        p.extend s ∈ Uinf ∧ p.extend s ≠ ∞ := by
      intro s hs
      have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans (le_of_lt hs.2) ht₀le1⟩
      refine ⟨?_, ?_⟩
      · rw [p.extend_apply hs01]
        exact hp _
      · intro hinfty
        exact absurd (csInf_le hSbdd ⟨hs01, hinfty⟩) (not_le.mpr hs.2)
    have himgarc : IsPreconnected (p.extend '' Set.Ico 0 (sInf S)) :=
      isPreconnected_Ico.image _ p.continuous_extend.continuousOn
    have harcsub : p.extend '' Set.Ico 0 (sInf S) ⊆
        Set.range (fun w : ℂ => ((w : ℂ̂))) := by
      rintro x ⟨s, hs, rfl⟩
      cases hx : p.extend s with
      | infty => exact absurd hx (harc s hs).2
      | coe y => exact ⟨y, rfl⟩
    -- its chart reading is connected, meets `w`, and avoids `K`
    have hApre : IsPreconnected
        ((fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S))) := by
      have h1 : (fun w : ℂ => ((w : ℂ̂))) ''
          ((fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S))) =
          p.extend '' Set.Ico 0 (sInf S) :=
        Set.image_preimage_eq_of_subset harcsub
      refine (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).mp ?_
      rw [h1]
      exact himgarc
    have hwA : w ∈ (fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S)) :=
      ⟨0, ⟨le_refl 0, ht₀pos⟩, p.extend_zero⟩
    have hAsub : (fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S)) ⊆
        (Kᶜ) := by
      rintro x ⟨s, hs, hx⟩
      simp only [Set.mem_compl_iff]
      intro hxK
      have h1 := (harc s hs).1
      rw [hx] at h1
      exact hxK h1
    have hAC : (fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S)) ⊆
        connectedComponentIn (Kᶜ) w :=
      hApre.subset_connectedComponentIn hwA hAsub
    -- the arc escapes every closed ball, contradicting boundedness
    obtain ⟨M, hM⟩ := hbdd.subset_closedBall 0
    have himg_sub : p.extend '' Set.Ico 0 (sInf S) ⊆
        (fun w : ℂ => ((w : ℂ̂))) '' Metric.closedBall 0 M := by
      intro x hx
      obtain ⟨y, hy⟩ := harcsub hx
      refine ⟨y, ?_, hy⟩
      apply hM
      apply hAC
      change ((y : ℂ̂)) ∈ p.extend '' Set.Ico 0 (sInf S)
      rw [← hy] at hx
      exact hx
    have hinfcl : (∞ : ℂ̂) ∈ closure (p.extend '' Set.Ico 0 (sInf S)) := by
      have h1 : sInf S ∈ closure (Set.Ico (0 : ℝ) (sInf S)) := by
        rw [closure_Ico (ne_of_lt ht₀pos)]
        exact ⟨le_of_lt ht₀pos, le_refl _⟩
      have h2 : p.extend (sInf S) ∈ closure (p.extend '' Set.Ico 0 (sInf S)) :=
        image_closure_subset_closure_image p.continuous_extend ⟨sInf S, h1, rfl⟩
      rwa [ht₀S.2] at h2
    have hclosedimg : IsClosed ((fun w : ℂ => ((w : ℂ̂))) '' Metric.closedBall 0 M) :=
      ((isCompact_closedBall (0 : ℂ) M).image OnePoint.continuous_coe).isClosed
    have hbad : (∞ : ℂ̂) ∈ (fun w : ℂ => ((w : ℂ̂))) '' Metric.closedBall 0 M :=
      hclosedimg.closure_subset ((closure_mono himg_sub) hinfcl)
    exact OnePoint.infty_notMem_image_coe hbad
  -- ## Stage 4: connectedness of `K`
  have hKpre : IsPreconnected K := by
    have main : ∀ u v : Set ℂ, IsOpen u → IsOpen v → K ⊆ u ∪ v →
        K ∩ (u ∩ v) = ∅ → (∀ t : unitInterval, Γ t ∈ u) → K ⊆ u := by
      intro u v hu hv hKuv hdisj htr
      by_contra hKu
      obtain ⟨w₀, hw₀K, hw₀u⟩ := Set.not_subset.mp hKu
      have hBclosed : IsClosed (K \ u) := hKclosed.sdiff hu
      have hBopen : IsOpen (K \ u) := by
        rw [isOpen_iff_forall_mem_open]
        intro b hb
        have hbK : b ∈ K := hb.1
        have hbu : b ∉ u := hb.2
        -- `b` is off the trace, so its sphere component of the complement
        -- of the trace is not the `∞`-component
        have hbR : ((b : ℂ̂)) ∉ Rsph := by
          intro hmem
          obtain ⟨t, ht⟩ := hmem
          have hΓtb : Γ t = b := OnePoint.coe_eq_coe.mp ht
          exact hbu (hΓtb ▸ htr t)
        have hObmem : ((b : ℂ̂)) ∈ connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) :=
          mem_connectedComponentIn hbR
        have hOUinf : ∀ x ∈ connectedComponentIn (Rsphᶜ) ((b : ℂ̂)), x ∉ Uinf := by
          intro x hxO hxU
          have h1 : connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) =
              connectedComponentIn (Rsphᶜ) x :=
            connectedComponentIn_eq hxO
          have h2 : Uinf = connectedComponentIn (Rsphᶜ) x :=
            connectedComponentIn_eq hxU
          have hbU : ((b : ℂ̂)) ∈ Uinf := by
            rw [h2, ← h1]
            exact hObmem
          exact hbK hbU
        have hOinf : (∞ : ℂ̂) ∉ connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) :=
          fun h => hOUinf ∞ h hinfUinf
        have hO'open : IsOpen ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) :=
          (hRc_open.connectedComponentIn).preimage OnePoint.continuous_coe
        have hbO' : b ∈ (fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) := hObmem
        have hO'K : ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) ⊆ K :=
          fun x hx => hOUinf _ hx
        have hOsubrange : connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) ⊆
            Set.range (fun w : ℂ => ((w : ℂ̂))) := by
          intro x hx
          cases x with
          | infty => exact absurd hx hOinf
          | coe y => exact ⟨y, rfl⟩
        have hO'pre : IsPreconnected ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) := by
          have h1 : (fun w : ℂ => ((w : ℂ̂))) '' ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
              connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) =
              connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) :=
            Set.image_preimage_eq_of_subset hOsubrange
          refine (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).mp ?_
          rw [h1]
          exact isPreconnected_connectedComponentIn
        have hO'uv : ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) ⊆ u ∪ v :=
          fun x hx => hKuv (hO'K hx)
        have hO'disj : ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) ∩ (u ∩ v) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro x hx
          have hxK : x ∈ K ∩ (u ∩ v) := ⟨hO'K hx.1, hx.2⟩
          rw [hdisj] at hxK
          exact hxK
        rcases isPreconnected_iff_subset_of_disjoint.mp hO'pre u v hu hv
          hO'uv hO'disj with hsub | hsub
        · exact absurd (hsub hbO') hbu
        · refine ⟨(fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂)), ?_, hO'open, hbO'⟩
          intro x hx
          refine ⟨hO'K hx, fun hxu => ?_⟩
          have hxK : x ∈ K ∩ (u ∩ v) := ⟨hO'K hx, hxu, hsub hx⟩
          rw [hdisj] at hxK
          exact hxK
      have hBne : (K \ u).Nonempty := ⟨w₀, hw₀K, hw₀u⟩
      rcases isClopen_iff.mp ⟨hBclosed, hBopen⟩ with h0 | huniv
      · rw [h0] at hBne
        exact Set.not_nonempty_empty hBne
      · have hmem : ((max R₀ 1 + 1 : ℝ) : ℂ) ∈ K \ u := by
          rw [huniv]
          exact Set.mem_univ _
        have h1 := hKball hmem.1
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith [hρpos])] at h1
        linarith
    rw [isPreconnected_iff_subset_of_disjoint]
    intro u v hu hv hKuv hdisj
    have htrpre : IsPreconnected (Set.range fun t : unitInterval => Γ t) :=
      isPreconnected_range Γ.continuous
    have h1 : (Set.range fun t : unitInterval => Γ t) ⊆ u ∪ v := by
      rintro x ⟨t, rfl⟩
      exact hKuv (htrK t)
    have h2 : (Set.range fun t : unitInterval => Γ t) ∩ (u ∩ v) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨t, rfl⟩, hx2⟩
      have hxK : Γ t ∈ K ∩ (u ∩ v) := ⟨htrK t, hx2⟩
      rw [hdisj] at hxK
      exact hxK
    rcases isPreconnected_iff_subset_of_disjoint.mp htrpre u v hu hv h1 h2 with
      htru | htrv
    · exact Or.inl (main u v hu hv hKuv hdisj fun t => htru ⟨t, rfl⟩)
    · refine Or.inr (main v u hv hu ?_ ?_ fun t => htrv ⟨t, rfl⟩)
      · rwa [Set.union_comm]
      · rwa [Set.inter_comm v u]
  -- ## Stage 5: the fill avoids the Julia set, hence sits in one component
  have hKFatou : ∀ x ∈ K, ((x : ℂ̂)) ∈ FatouSet f := by
    intro x hx
    by_contra hF
    have hJ : ((x : ℂ̂)) ∈ JuliaSet f := by
      rw [← compl_fatouSet]
      exact hF
    exact hx (hfill _ hJ)
  have hVfc : IsFatouComponent f (fcOrbit f U (N₀ + m)) :=
    isFatouComponent_fcOrbit (N₀ + m) hf hd1 hU
  have hp₀V : ((Γ 0 : ℂ̂)) ∈ fcOrbit f U (N₀ + m) := by
    have h1 : f^[m] ((γ 0 : ℂ̂)) ∈ fcOrbit f U (N₀ + m) := hfwd m _ (hγmem 0)
    have h2 : f^[m] ((γ 0 : ℂ̂)) ≠ ∞ := fun h => hinf (N₀ + m) (h ▸ h1)
    rw [hΓ 0, hcoe _ h2]
    exact h1
  have hSKV : ∀ x ∈ K, ((x : ℂ̂)) ∈ fcOrbit f U (N₀ + m) := by
    have hpre : IsPreconnected ((fun w : ℂ => ((w : ℂ̂))) '' K) :=
      hKpre.image _ OnePoint.continuous_coe.continuousOn
    have hmem0 : ((Γ 0 : ℂ̂)) ∈ (fun w : ℂ => ((w : ℂ̂))) '' K := ⟨Γ 0, htrK 0, rfl⟩
    have hsubF : (fun w : ℂ => ((w : ℂ̂))) '' K ⊆ FatouSet f := by
      rintro x ⟨x', hx', rfl⟩
      exact hKFatou x' hx'
    have h1 : (fun w : ℂ => ((w : ℂ̂))) '' K ⊆
        connectedComponentIn (FatouSet f) ((Γ 0 : ℂ̂)) :=
      hpre.subset_connectedComponentIn hmem0 hsubF
    obtain ⟨x₀, hx₀F, hVeq⟩ := hVfc
    have hmemx₀ : ((Γ 0 : ℂ̂)) ∈ connectedComponentIn (FatouSet f) x₀ := by
      rw [← hVeq]
      exact hp₀V
    have h2 : connectedComponentIn (FatouSet f) ((Γ 0 : ℂ̂)) =
        fcOrbit f U (N₀ + m) := by
      rw [hVeq]
      exact (connectedComponentIn_eq hmemx₀).symm
    intro x hx
    have h3 := h1 ⟨x, hx, rfl⟩
    rwa [h2] at h3
  -- ## Stage 6: a simply connected neighborhood of the fill
  have hT'open : IsOpen {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (N₀ + m)} :=
    hVfc.isOpen.preimage OnePoint.continuous_coe
  have hKT' : K ⊆ {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (N₀ + m)} :=
    fun x hx => hSKV x hx
  obtain ⟨W, hWopen, hKW, hWT', hWsc⟩ :=
    exists_simplyConnectedSpace_between hKcomp ⟨hKne, hKpre⟩ hKfull hT'open hKT'
  -- ## Stage 7: null-homotope the pushed curve inside the neighborhood
  have hΓcl : Γ 0 = Γ 1 := by rw [hΓ 0, hΓ 1, hγcl]
  have hnullm : IsChartNullHomotopyIn Γ
      {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (N₀ + m)} := by
    have hΓW : ∀ t : unitInterval, Γ t ∈ W := fun t => hKW (htrK t)
    have : SimplyConnectedSpace ↥W := hWsc
    let x₀ : ↥W := ⟨Γ 0, hΓW 0⟩
    let pΓ : Path x₀ x₀ :=
      { toFun := fun s => ⟨Γ s, hΓW s⟩
        continuous_toFun := Γ.continuous.subtype_mk hΓW
        source' := rfl
        target' := Subtype.ext hΓcl.symm }
    obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic pΓ (Path.refl x₀)
    exact ⟨⟨fun q => ((F q : ↥W) : ℂ), continuous_subtype_val.comp F.continuous⟩,
      fun s => congrArg Subtype.val (F.apply_zero s),
      fun s => congrArg Subtype.val (F.apply_one s),
      fun t => ⟨congrArg Subtype.val (Path.Homotopy.source F t),
        congrArg Subtype.val (Path.Homotopy.target F t)⟩,
      fun q => hWT' (F q).2⟩
  -- ## Stage 8: descend the null homotopy through the covering steps
  have descend : ∀ j : ℕ, ∀ Γ' : C(unitInterval, ℂ),
      (∀ t : unitInterval, Γ' t = chartFiniteMap (f^[j] ((γ t : ℂ̂)))) →
      IsChartNullHomotopyIn Γ' {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (N₀ + j)} →
      IsChartNullHomotopyIn γ {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U N₀} := by
    intro j
    induction j with
    | zero =>
        intro Γ' hΓ' hnull
        have hΓ'γ : Γ' = γ := by
          ext t
          rw [hΓ' t, Function.iterate_zero_apply]
          rfl
        rw [hΓ'γ, Nat.add_zero] at hnull
        exact hnull
    | succ k ih =>
        intro Γ' hΓ' hnull
        obtain ⟨Γk, hΓk⟩ := exists_pushed_curve hf hd hU hinf hγmem k
        have hne : ∀ t : unitInterval, f^[k] ((γ t : ℂ̂)) ≠ ∞ := by
          intro t h
          exact hinf (N₀ + k) (h ▸ hfwd k _ (hγmem t))
        have hΓksph : ∀ t : unitInterval, ((Γk t : ℂ̂)) = f^[k] ((γ t : ℂ̂)) := by
          intro t
          rw [hΓk t]
          exact hcoe _ (hne t)
        have hΓkcl : Γk 0 = Γk 1 := by rw [hΓk 0, hΓk 1, hγcl]
        have hΓkmem : ∀ t : unitInterval, ((Γk t : ℂ̂)) ∈ fcOrbit f U (N₀ + k) := by
          intro t
          rw [hΓksph t]
          exact hfwd k _ (hγmem t)
        have hstepev : ∀ t : unitInterval, Γ' t = chartFiniteMap (f ((Γk t : ℂ̂))) := by
          intro t
          rw [hΓksph t, ← Function.iterate_succ_apply' f k ((γ t : ℂ̂))]
          exact hΓ' t
        have hnull' : IsChartNullHomotopyIn Γ'
            {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U ((N₀ + k) + 1)} := by
          rwa [show N₀ + (k + 1) = (N₀ + k) + 1 by omega] at hnull
        have hstep := isChartNullHomotopyIn_of_step hf hd hU (N₀ + k)
          (hinf (N₀ + k)) (hinf ((N₀ + k) + 1)) (hcrit (N₀ + k))
          hΓkcl hΓkmem hstepev hnull'
        exact ih Γk hΓk hstep
  have hnull0 : IsChartNullHomotopyIn γ
      {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U N₀} := descend m Γ hΓ hnullm
  -- ## Stage 9: homotopy invariance kills the winding numbers
  intro z hzJ
  obtain ⟨H, hH0, hH1, hHbd, hHmem⟩ := hnull0
  have hN₀fc : IsFatouComponent f (fcOrbit f U N₀) :=
    isFatouComponent_fcOrbit N₀ hf hd1 hU
  have hγ0z : γ 0 ≠ z := by
    intro heq
    have h0 : ((γ 0 : ℂ̂)) ∈ FatouSet f := hN₀fc.subset_fatouSet (hγmem 0)
    rw [heq] at h0
    exact hjf _ h0 hzJ
  let Hrel : ContinuousMap.HomotopyRel γ
      (ContinuousMap.const unitInterval (γ 0)) {0, 1} :=
    { toFun := fun q => H q
      continuous_toFun := H.continuous
      map_zero_left := hH0
      map_one_left := fun s => hH1 s
      prop' := by
        intro t s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact (hHbd t).1
        · exact (hHbd t).2.trans hγcl }
  have havoid : ∀ (t s : unitInterval), Hrel (t, s) ≠ z := by
    intro t s heq
    have h1 : ((H (t, s) : ℂ̂)) ∈ FatouSet f :=
      hN₀fc.subset_fatouSet (hHmem (t, s))
    have heq' : H (t, s) = z := heq
    rw [heq'] at h1
    exact hjf _ h1 hzJ
  rw [windingNumber_eq_of_homotopicRel hγcl Hrel havoid]
  exact windingNumber_const (γ 0) z hγ0z

open Set unitInterval in
/-- **Normal limits on a wandering orbit are constant**: a locally uniform
subsequential limit of the iterates on a wandering Fatou component has
image of measure zero (the orbit components are pairwise disjoint, so their
spherical areas are summable), and a nonconstant holomorphic map has open
image. -/
theorem eventually_constant_limit_of_wandering {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {g : ℂ̂ → ℂ̂} {K : Set ℂ̂}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hlim : TendstoLocallyUniformlyOn (fun j => f^[φ j]) g Filter.atTop
      (interior K)) :
    ∀ x ∈ interior K, ∀ y ∈ interior K,
      connectedComponentIn (interior K) x =
        connectedComponentIn (interior K) y → g x = g y := by
  classical
  -- ## Stage 0: basic facts
  have _ := hK
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hopenK : IsOpen (interior K) := isOpen_interior
  have hcont_iter : ∀ n : ℕ, Continuous (f^[n]) := by
    intro n
    induction n with
    | zero => simpa using continuous_id
    | succ m ih =>
        rw [Function.iterate_succ]
        exact ih.comp hf.continuous
  have hgcont : ContinuousOn g (interior K) :=
    hlim.continuousOn
      (Filter.Frequently.of_forall fun j => (hcont_iter (φ j)).continuousOn)
  have hOpenMap : IsOpenMap f := hf.isOpenMap (fun c => hf.ne_const hd1 c)
  have hfatou_iter : ∀ (n : ℕ) (z : ℂ̂), z ∈ FatouSet f →
      f^[n] z ∈ FatouSet f := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        intro z hz
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hOpenMap (ih z hz)
  have hmem_orbit : ∀ (n : ℕ) (z : ℂ̂), z ∈ U → f^[n] z ∈ fcOrbit f U n := by
    intro n z hz
    exact Set.mem_biUnion hz
      (mem_connectedComponentIn (hfatou_iter n z (hU.subset_fatouSet hz)))
  have hiter_rat : ∀ n : ℕ, IsRational (f^[n]) := fun n => hf.iterate hd1 n
  -- ## Stage 1: clopen propagation of local constancy on preconnected sets
  have clopen_const : ∀ S : Set ℂ̂, IsPreconnected S →
      (∀ w ∈ S, ∀ᶠ w' in 𝓝 w, g w' = g w) →
      ∀ a ∈ S, ∀ b ∈ S, g a = g b := by
    intro S hS hlc a ha b hb
    by_contra hab
    set N : ℂ̂ → Set ℂ̂ := fun w => interior {w' | g w' = g w} with hNdef
    have hNopen : ∀ w : ℂ̂, IsOpen (N w) := fun w => isOpen_interior
    have hNmem : ∀ w ∈ S, w ∈ N w := by
      intro w hw
      rw [hNdef, mem_interior_iff_mem_nhds]
      exact (hlc w hw).mono fun w' h => h
    have hNval : ∀ w : ℂ̂, ∀ u ∈ N w, g u = g w := by
      intro w u hu
      have h : u ∈ {w' | g w' = g w} := interior_subset hu
      exact h
    have hcover : S ⊆ (⋃ w ∈ {w ∈ S | g w = g a}, N w) ∪
        (⋃ w ∈ {w ∈ S | g w ≠ g a}, N w) := by
      intro w hw
      by_cases hwa : g w = g a
      · exact Or.inl (Set.mem_biUnion ⟨hw, hwa⟩ (hNmem w hw))
      · exact Or.inr (Set.mem_biUnion ⟨hw, hwa⟩ (hNmem w hw))
    have h1 : (S ∩ ⋃ w ∈ {w ∈ S | g w = g a}, N w).Nonempty :=
      ⟨a, ha, Set.mem_biUnion ⟨ha, rfl⟩ (hNmem a ha)⟩
    have h2 : (S ∩ ⋃ w ∈ {w ∈ S | g w ≠ g a}, N w).Nonempty :=
      ⟨b, hb, Set.mem_biUnion ⟨hb, fun h => hab h.symm⟩ (hNmem b hb)⟩
    obtain ⟨u, -, hu₁, hu₂⟩ := hS _ _
      (isOpen_biUnion fun w _ => hNopen w) (isOpen_biUnion fun w _ => hNopen w)
      hcover h1 h2
    obtain ⟨w₁, hw₁, hu₁'⟩ := Set.mem_iUnion₂.mp hu₁
    obtain ⟨w₂, hw₂, hu₂'⟩ := Set.mem_iUnion₂.mp hu₂
    exact hw₂.2 (by rw [← hNval w₂ u hu₂', hNval w₁ u hu₁', hw₁.2])
  -- ## Stage 2: local constancy at finite points of `interior K` (the engine)
  have key : ∀ p₀ : ℂ, ((p₀ : ℂ̂)) ∈ interior K →
      ∀ᶠ w in 𝓝 ((p₀ : ℂ̂)), g w = g ((p₀ : ℂ̂)) := by
    intro p₀ hp₀
    set c : ℂ̂ := g ((p₀ : ℂ̂)) with hcdef
    -- ### chart data around the limit value `c`
    obtain ⟨χ, Cm, s, hCm, hs, hχinj, hχcomp, hread⟩ :
        ∃ (χ : ℂ̂ → ℂ) (Cm s : ℝ), 0 < Cm ∧ 0 < s ∧
          (∀ v v' : ℂ̂, dist c v < s → dist c v' < s → χ v = χ v' → v = v') ∧
          (∀ v v' : ℂ̂, dist c v < s → dist c v' < s →
            ‖χ v - χ v'‖ ≤ Cm * dist v v') ∧
          (∀ n : ℕ, ∃ A B : Polynomial ℂ, ∀ z : ℂ,
            dist c (f^[n] ((z : ℂ̂))) < s →
              B.eval z ≠ 0 ∧ χ (f^[n] ((z : ℂ̂))) = A.eval z / B.eval z) := by
      have hcoe : ∀ p : ℂ̂, p ≠ ∞ → ((chartFiniteMap p : ℂ) : ℂ̂) = p := by
        intro p hp
        cases p with
        | infty => exact absurd rfl hp
        | coe x => rfl
      by_cases hcinf : c = ∞
      · -- infinity chart around `c = ∞`
        rw [hcinf]
        have hbound : ∀ v : ℂ̂, dist (∞ : ℂ̂) v < 1 →
            v ≠ (((0 : ℂ)) : ℂ̂) ∧ ‖chartInftyMap v‖ ≤ 1 := by
          intro v hv
          cases v with
          | infty =>
            refine ⟨(OnePoint.infty_ne_coe (0 : ℂ)), ?_⟩
            rw [show chartInftyMap (∞ : ℂ̂) = 0 from rfl, norm_zero]
            exact zero_le_one
          | coe x =>
            have hx_eq : dist (∞ : ℂ̂) ((x : ℂ̂)) =
                2 / Real.sqrt (1 + ‖x‖ ^ 2) := rfl
            rw [hx_eq] at hv
            have hs0 : 0 < Real.sqrt (1 + ‖x‖ ^ 2) :=
              Real.sqrt_pos.mpr (by positivity)
            have h2 : 2 < Real.sqrt (1 + ‖x‖ ^ 2) := by
              rw [div_lt_iff₀ hs0, one_mul] at hv
              exact hv
            have h3 : (4 : ℝ) < 1 + ‖x‖ ^ 2 := by
              have := (Real.lt_sqrt (by positivity)).mp h2
              nlinarith
            have hxnorm : 1 < ‖x‖ := by nlinarith [norm_nonneg x]
            have hxne : x ≠ 0 := by
              intro h0
              rw [h0, norm_zero] at hxnorm
              linarith
            refine ⟨fun h => hxne (OnePoint.coe_eq_coe.mp h), ?_⟩
            rw [show chartInftyMap ((x : ℂ̂)) = x⁻¹ from rfl, norm_inv]
            exact inv_le_one_of_one_le₀ hxnorm.le
        have hinv_ne : ∀ v : ℂ̂, v ≠ (((0 : ℂ)) : ℂ̂) → inversionGL • v ≠ ∞ := by
          intro v hv
          cases v with
          | infty =>
            rw [inversionGL_smul_infty]
            exact OnePoint.coe_ne_infty 0
          | coe x =>
            have hx : x ≠ 0 := fun h => hv (by rw [h])
            rw [inversionGL_smul_coe, if_neg hx]
            exact OnePoint.coe_ne_infty _
        have hkeyI : ∀ p : ℂ̂, chartInftyMap p = chartFiniteMap (inversionGL • p) := by
          intro p
          cases p with
          | infty =>
            rw [show chartInftyMap (∞ : ℂ̂) = 0 from rfl, inversionGL_smul_infty]
            rfl
          | coe x =>
            by_cases hx : x = 0
            · subst hx
              rw [show chartInftyMap (((0 : ℂ)) : ℂ̂) = (0 : ℂ)⁻¹ from rfl,
                inv_zero, inversionGL_smul_coe, if_pos rfl]
              rfl
            · rw [inversionGL_smul_coe, if_neg hx]
              rfl
        refine ⟨chartInftyMap, 1, 1, one_pos, one_pos, ?_, ?_, ?_⟩
        · -- injectivity on the spherical unit ball about `∞`
          intro v v' hv hv' heq
          have h1 := inversionGL_smul_coe_chartInftyMap (hbound v hv).1
          have h2 := inversionGL_smul_coe_chartInftyMap (hbound v' hv').1
          rw [← h1, ← h2, heq]
        · -- metric comparison via the inversion isometry
          intro v v' hv hv'
          have hvne := (hbound v hv).1
          have hv'ne := (hbound v' hv').1
          have hb1 : ‖chartFiniteMap (inversionGL • v)‖ ≤ 1 := by
            rw [← hkeyI v]
            exact (hbound v hv).2
          have hb2 : ‖chartFiniteMap (inversionGL • v')‖ ≤ 1 := by
            rw [← hkeyI v']
            exact (hbound v' hv').2
          have h1 := norm_sub_le_sphericalDist_mul hb1 hb2
          have h2 : sphericalDist ((chartFiniteMap (inversionGL • v) : ℂ) : ℂ̂)
              ((chartFiniteMap (inversionGL • v') : ℂ) : ℂ̂) = dist v v' := by
            rw [hcoe _ (hinv_ne v hvne), hcoe _ (hinv_ne v' hv'ne),
              sphericalDist_inversionGL_smul v v']
            rfl
          rw [h2] at h1
          rw [hkeyI v, hkeyI v']
          calc ‖chartFiniteMap (inversionGL • v) - chartFiniteMap (inversionGL • v')‖
              ≤ (1 + 1 ^ 2) / 2 * dist v v' := h1
            _ = 1 * dist v v' := by norm_num
        · -- rational reading in the infinity chart: swap numerator/denominator
          intro n
          obtain ⟨rn, hrn⟩ := hiter_rat n
          refine ⟨rn.denReduced, rn.numReduced, fun z hz => ?_⟩
          have he : f^[n] ((z : ℂ̂)) = if rn.denReduced.eval z = 0 then ∞
              else ((rn.numReduced.eval z / rn.denReduced.eval z : ℂ) : ℂ̂) := by
            rw [hrn]
            rfl
          by_cases hden : rn.denReduced.eval z = 0
          · have hnum : rn.numReduced.eval z ≠ 0 :=
              (rn.eval_ne_zero_or z).resolve_right fun h => h hden
            refine ⟨hnum, ?_⟩
            rw [he, if_pos hden, show chartInftyMap (∞ : ℂ̂) = 0 from rfl,
              hden, zero_div]
          · have hval : f^[n] ((z : ℂ̂)) =
                ((rn.numReduced.eval z / rn.denReduced.eval z : ℂ) : ℂ̂) := by
              rw [he, if_neg hden]
            have hne0 : rn.numReduced.eval z / rn.denReduced.eval z ≠ 0 := by
              intro h0
              rw [hval, h0] at hz
              have h2 : dist (∞ : ℂ̂) (((0 : ℂ)) : ℂ̂) = 2 := by
                change (2 : ℝ) / Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) = 2
                simp
              rw [h2] at hz
              linarith
            have hnum : rn.numReduced.eval z ≠ 0 := fun h =>
              hne0 (by rw [h, zero_div])
            refine ⟨hnum, ?_⟩
            rw [hval, show chartInftyMap
                (((rn.numReduced.eval z / rn.denReduced.eval z : ℂ)) : ℂ̂) =
                (rn.numReduced.eval z / rn.denReduced.eval z)⁻¹ from rfl, inv_div]
      · -- finite chart around a finite `c`
        set d : ℝ := dist c (∞ : ℂ̂) with hddef
        have hd0 : 0 < d := dist_pos.mpr hcinf
        have hbound : ∀ v : ℂ̂, dist c v < d / 2 →
            v ≠ ∞ ∧ ‖chartFiniteMap v‖ ≤ 2 / (d / 2) := by
          intro v hv
          cases v with
          | infty =>
            exfalso
            rw [← hddef] at hv
            linarith
          | coe x =>
            refine ⟨OnePoint.coe_ne_infty x, ?_⟩
            have hfar : d / 2 ≤ dist ((x : ℂ̂)) (∞ : ℂ̂) := by
              have htri : d ≤ dist c ((x : ℂ̂)) + dist ((x : ℂ̂)) (∞ : ℂ̂) := by
                rw [hddef]
                exact dist_triangle _ _ _
              linarith
            have hx_eq : dist ((x : ℂ̂)) (∞ : ℂ̂) =
                2 / Real.sqrt (1 + ‖x‖ ^ 2) := rfl
            rw [hx_eq] at hfar
            have hs0 : 0 < Real.sqrt (1 + ‖x‖ ^ 2) :=
              Real.sqrt_pos.mpr (by positivity)
            have hxs : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
              calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
                _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
                    Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖x‖])
            have h2 : d / 2 * Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 := by
              rw [le_div_iff₀ hs0] at hfar
              linarith
            have h3 : Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 / (d / 2) := by
              rw [le_div_iff₀ (by positivity)]
              linarith [mul_comm (d / 2) (Real.sqrt (1 + ‖x‖ ^ 2))]
            exact (show ‖chartFiniteMap ((x : ℂ̂))‖ = ‖x‖ from rfl) ▸ hxs.trans h3
        refine ⟨chartFiniteMap, (1 + (2 / (d / 2)) ^ 2) / 2, d / 2,
          by positivity, by positivity, ?_, ?_, ?_⟩
        · -- injectivity on the ball of finite points
          intro v v' hv hv' heq
          have h1 := hcoe v (hbound v hv).1
          have h2 := hcoe v' (hbound v' hv').1
          rw [← h1, ← h2, heq]
        · -- Euclidean-vs-spherical comparison on the bounded region
          intro v v' hv hv'
          have h1 := norm_sub_le_sphericalDist_mul (hbound v hv).2 (hbound v' hv').2
          have h2 : sphericalDist ((chartFiniteMap v : ℂ) : ℂ̂)
              ((chartFiniteMap v' : ℂ) : ℂ̂) = dist v v' := by
            rw [hcoe v (hbound v hv).1, hcoe v' (hbound v' hv').1]
            rfl
          rw [h2] at h1
          exact h1
        · -- rational reading in the finite chart
          intro n
          obtain ⟨rn, hrn⟩ := hiter_rat n
          refine ⟨rn.numReduced, rn.denReduced, fun z hz => ?_⟩
          have he : f^[n] ((z : ℂ̂)) = if rn.denReduced.eval z = 0 then ∞
              else ((rn.numReduced.eval z / rn.denReduced.eval z : ℂ) : ℂ̂) := by
            rw [hrn]
            rfl
          by_cases hden : rn.denReduced.eval z = 0
          · exfalso
            rw [he, if_pos hden, ← hddef] at hz
            linarith
          · refine ⟨hden, ?_⟩
            rw [he, if_neg hden]
            rfl
    -- ### E1: a closed disk decoding into `interior K` with `g`-values near `c`
    obtain ⟨δ, hδpos, hδprop⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.closedBall p₀ δ,
        ((z : ℂ̂)) ∈ interior K ∧ dist c (g ((z : ℂ̂))) < s / 4 := by
      have h1 : interior K ∈ 𝓝 ((p₀ : ℂ̂)) := hopenK.mem_nhds hp₀
      have h2 : g ⁻¹' (Metric.ball c (s / 4)) ∈ 𝓝 ((p₀ : ℂ̂)) := by
        refine (hgcont.continuousAt h1).preimage_mem_nhds ?_
        rw [← hcdef]
        exact Metric.ball_mem_nhds _ (by positivity)
      have h3 : (fun z : ℂ => ((z : ℂ̂))) ⁻¹'
          (interior K ∩ g ⁻¹' (Metric.ball c (s / 4))) ∈ 𝓝 p₀ :=
        (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds
          (Filter.inter_mem h1 h2)
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp h3
      refine ⟨δ, hδpos, fun z hz => ?_⟩
      obtain ⟨hzK, hzg⟩ := hδsub hz
      refine ⟨hzK, ?_⟩
      rw [Set.mem_preimage, Metric.mem_ball] at hzg
      rw [dist_comm]
      exact hzg
    -- ### E2: uniform convergence on the decoded closed disk
    have hdisk_sub : (fun z : ℂ => ((z : ℂ̂))) '' Metric.closedBall p₀ δ ⊆
        interior K := by
      rintro - ⟨z, hz, rfl⟩
      exact (hδprop z hz).1
    have hTU : TendstoUniformlyOn (fun j => f^[φ j]) g atTop
        ((fun z : ℂ => ((z : ℂ̂))) '' Metric.closedBall p₀ δ) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hopenK).mp hlim _ hdisk_sub
        ((isCompact_closedBall _ _).image OnePoint.continuous_coe)
    have hev_ball : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall p₀ δ,
        dist c (f^[φ j] ((z : ℂ̂))) < s / 2 := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hTU (s / 4)
        (by positivity)] with j hj z hz
      have h1 := hj _ ⟨z, hz, rfl⟩
      have h2 := (hδprop z hz).2
      calc dist c (f^[φ j] ((z : ℂ̂)))
          ≤ dist c (g ((z : ℂ̂))) + dist (g ((z : ℂ̂))) (f^[φ j] ((z : ℂ̂))) :=
            dist_triangle _ _ _
        _ < s / 4 + s / 4 := add_lt_add h2 h1
        _ = s / 2 := by ring
    -- the chart reading of the limit
    set G : ℂ → ℂ := fun z => χ (g ((z : ℂ̂))) with hGdef
    -- ### E2': chart readings converge uniformly on the closed disk
    have hTUχ : TendstoUniformlyOn (fun j (z : ℂ) => χ (f^[φ j] ((z : ℂ̂)))) G atTop
        (Metric.closedBall p₀ δ) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hev_ball, Metric.tendstoUniformlyOn_iff.mp hTU
        (min (s / 4) (ε / Cm)) (lt_min (by positivity) (by positivity))]
        with j hj₁ hj₂ z hz
      have hgb : dist c (g ((z : ℂ̂))) < s := lt_trans (hδprop z hz).2 (by linarith)
      have hfb : dist c (f^[φ j] ((z : ℂ̂))) < s := lt_trans (hj₁ z hz) (by linarith)
      have h3 := hj₂ _ ⟨z, hz, rfl⟩
      have h4 : ‖χ (g ((z : ℂ̂))) - χ (f^[φ j] ((z : ℂ̂)))‖ ≤
          Cm * dist (g ((z : ℂ̂))) (f^[φ j] ((z : ℂ̂))) := hχcomp _ _ hgb hfb
      calc dist (G z) (χ (f^[φ j] ((z : ℂ̂))))
          = ‖χ (g ((z : ℂ̂))) - χ (f^[φ j] ((z : ℂ̂)))‖ := dist_eq_norm _ _
        _ ≤ Cm * dist (g ((z : ℂ̂))) (f^[φ j] ((z : ℂ̂))) := h4
        _ < Cm * (ε / Cm) :=
            mul_lt_mul_of_pos_left (lt_of_lt_of_le h3 (min_le_right _ _)) hCm
        _ = ε := by field_simp
    -- ### E2'': eventual differentiability of the chart readings
    have hFdiff : ∀ᶠ j in atTop, DifferentiableOn ℂ
        (fun z : ℂ => χ (f^[φ j] ((z : ℂ̂)))) (Metric.ball p₀ δ) := by
      filter_upwards [hev_ball] with j hj
      obtain ⟨A, B, hAB⟩ := hread (φ j)
      have hBne : ∀ z ∈ Metric.closedBall p₀ δ, B.eval z ≠ 0 := fun z hz =>
        (hAB z (lt_trans (hj z hz) (by linarith))).1
      have hdiff : DifferentiableOn ℂ (fun z => A.eval z / B.eval z)
          (Metric.ball p₀ δ) :=
        (A.differentiable.differentiableOn).div (B.differentiable.differentiableOn)
          (fun z hz => hBne z (Metric.ball_subset_closedBall hz))
      exact hdiff.congr fun z hz =>
        (hAB z (lt_trans (hj z (Metric.ball_subset_closedBall hz)) (by linarith))).2
    -- ### E2''': the limit reading is analytic on the open disk
    have hGdiff : DifferentiableOn ℂ G (Metric.ball p₀ δ) :=
      (hTUχ.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall).differentiableOn
        hFdiff Metric.isOpen_ball
    have hGanal : AnalyticAt ℂ (fun z => G z - χ c) p₀ :=
      (hGdiff.analyticAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδpos))).sub analyticAt_const
    -- ### E3: the isolated-zeros dichotomy
    rcases hGanal.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · -- constant branch: `g = c` near `p₀`, transfer through the embedding
      have hev : ∀ᶠ z : ℂ in 𝓝 p₀, g ((z : ℂ̂)) = c := by
        have h2 : Metric.closedBall p₀ δ ∈ 𝓝 p₀ :=
          Metric.closedBall_mem_nhds _ hδpos
        filter_upwards [hzero, h2] with z h₁ h₂
        have hgb : dist c (g ((z : ℂ̂))) < s := lt_trans (hδprop z h₂).2 (by linarith)
        have hcb : dist c c < s := by rw [dist_self]; exact hs
        exact hχinj _ _ hgb hcb (sub_eq_zero.mp h₁)
      rw [OnePoint.nhds_coe_eq, Filter.eventually_map]
      exact hev
    · -- nonconstant branch: run the attainment engine to a contradiction
      exfalso
      -- ### E4: a punctured ball where the limit reading avoids `χ c`
      obtain ⟨ε, hεpos, hεprop⟩ : ∃ ε > 0, ∀ z : ℂ, dist z p₀ < ε → z ≠ p₀ →
          G z ≠ χ c := by
        have h1 : ∀ᶠ z in 𝓝 p₀, z ∈ ({p₀}ᶜ : Set ℂ) → G z - χ c ≠ 0 :=
          eventually_nhdsWithin_iff.mp hne
        obtain ⟨ε, hε, h2⟩ := Metric.eventually_nhds_iff.mp h1
        refine ⟨ε, hε, fun z hz hzp hGz => ?_⟩
        exact h2 hz (Set.mem_compl_singleton_iff.mpr hzp) (sub_eq_zero.mpr hGz)
      -- the circle radius
      set r : ℝ := min (ε / 2) (δ / 2) with hrdef
      have hrpos : 0 < r := lt_min (by linarith) (by linarith)
      have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      -- ### E4': the circle curve
      have hcirc_cont : Continuous (fun t : I => p₀ + (r : ℂ) *
          Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) := by
        refine continuous_const.add (continuous_const.mul
          (Complex.continuous_exp.comp ?_))
        exact (Complex.continuous_ofReal.comp
          (continuous_const.mul continuous_subtype_val)).mul continuous_const
      set cir : C(I, ℂ) := ⟨fun t : I => p₀ + (r : ℂ) *
          Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I),
          hcirc_cont⟩ with hcirdef
      have hcir_apply : ∀ t : I, cir t = p₀ + (r : ℂ) *
          Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) :=
        fun t => rfl
      have hcir_dist : ∀ t : I, dist (cir t) p₀ = r := by
        intro t
        rw [hcir_apply t, dist_eq_norm, add_sub_cancel_left, norm_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hrpos]
      have hcir_cl : cir 0 = cir 1 := by
        rw [hcir_apply, hcir_apply]
        have h0 : ((0 : I) : ℝ) = 0 := rfl
        have h1 : ((1 : I) : ℝ) = 1 := rfl
        rw [h0, h1, mul_zero, mul_one]
        push_cast
        rw [zero_mul, Complex.exp_zero, Complex.exp_two_pi_mul_I]
      have hcir_ne : ∀ t : I, cir t ≠ p₀ := by
        intro t h0
        have h1 := hcir_dist t
        rw [h0, dist_self] at h1
        exact (ne_of_gt hrpos) h1.symm
      have hcir_mem_ball : ∀ t : I, cir t ∈ Metric.ball p₀ δ := by
        intro t
        rw [Metric.mem_ball, hcir_dist]
        exact hrδ
      have hcir_mem_cball : ∀ t : I, cir t ∈ Metric.closedBall p₀ δ :=
        fun t => Metric.ball_subset_closedBall (hcir_mem_ball t)
      -- ### E4'': every point of the circle is a value of `cir`
      have hcir_surj : ∀ w : ℂ, dist w p₀ = r → ∃ t : I, cir t = w := by
        intro w hw
        have hwn : ‖w - p₀‖ = r := by rwa [dist_eq_norm] at hw
        set θ := Complex.arg (w - p₀) with hθdef
        have hθlow : -Real.pi < θ := Complex.neg_pi_lt_arg _
        have hθhigh : θ ≤ Real.pi := Complex.arg_le_pi _
        have hπpos := Real.pi_pos
        have hval : ((r : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
            = w - p₀ := by
          have h1 := Complex.norm_mul_exp_arg_mul_I (w - p₀)
          rw [← hθdef, hwn] at h1
          exact h1
        by_cases hθ0 : 0 ≤ θ
        · refine ⟨⟨θ / (2 * Real.pi), Set.mem_Icc.mpr ⟨by positivity, ?_⟩⟩, ?_⟩
          · rw [div_le_one (by positivity)]
            linarith
          · rw [hcir_apply]
            have harg : (2 * Real.pi * (θ / (2 * Real.pi)) : ℝ) = θ := by
              field_simp
            rw [show ((⟨θ / (2 * Real.pi), _⟩ : I) : ℝ) = θ / (2 * Real.pi) from rfl,
              harg]
            linear_combination hval
        · refine ⟨⟨θ / (2 * Real.pi) + 1, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩, ?_⟩
          · have h1 : (-1 : ℝ) ≤ θ / (2 * Real.pi) :=
              (le_div_iff₀ (by positivity)).mpr (by linarith)
            linarith
          · have h1 : θ / (2 * Real.pi) ≤ 0 :=
              div_nonpos_iff.mpr (Or.inr ⟨le_of_not_ge hθ0, by positivity⟩)
            linarith
          · rw [hcir_apply]
            rw [show ((⟨θ / (2 * Real.pi) + 1, _⟩ : I) : ℝ)
                = θ / (2 * Real.pi) + 1 from rfl]
            have harg : (2 * Real.pi * (θ / (2 * Real.pi) + 1) : ℝ)
                = θ + 2 * Real.pi := by
              field_simp
            rw [harg]
            have hsplit : (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
                = ((θ : ℝ) : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
              push_cast
              ring
            rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
            linear_combination hval
      -- ### E5: the limit reading is uniformly far from `χ c` on the circle
      have hGcont : ContinuousOn G (Metric.ball p₀ δ) := hGdiff.continuousOn
      have hGcir_cont : Continuous fun t : I => ‖G (cir t) - χ c‖ :=
        ((hGcont.comp_continuous cir.continuous hcir_mem_ball).sub
          continuous_const).norm
      obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn
        Set.univ_nonempty hGcir_cont.continuousOn
      set ρ : ℝ := ‖G (cir t₀) - χ c‖ / 4 with hρdef
      have hρpos : 0 < ρ := by
        have hne0 : G (cir t₀) ≠ χ c := by
          apply hεprop
          · rw [hcir_dist t₀]
            exact hrε
          · exact hcir_ne t₀
        have h1 : 0 < ‖G (cir t₀) - χ c‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr hne0)
        rw [hρdef]
        linarith
      have hGfar : ∀ t : I, 4 * ρ ≤ ‖G (cir t) - χ c‖ := by
        intro t
        have h1 := isMinOn_iff.mp ht₀ t (Set.mem_univ t)
        rw [hρdef]
        linarith
      -- ### E5': winding numbers of the circle about test points
      have windKey : ∀ (γ : C(I, ℂ)) (ζ : ℂ),
          windingNumber (shiftedCurve γ ζ) 0 = windingNumber γ ζ := by
        intro γ ζ
        have h : shiftedCurve (shiftedCurve γ ζ) 0 = shiftedCurve γ ζ := by
          ext t
          simp [shiftedCurve]
        unfold windingNumber
        rw [h]
      have hwind_center : windingNumber cir p₀ = 1 := by
        have hLcont : Continuous fun t : I => ((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I := by
          refine continuous_const.add ?_
          exact (Complex.continuous_ofReal.comp
            (continuous_const.mul continuous_subtype_val)).mul continuous_const
        have hL : IsLogLiftOf ⟨fun t : I => ((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I, hLcont⟩
            (shiftedCurve cir p₀) := by
          intro t
          have h2 : shiftedCurve cir p₀ t = cir t - p₀ := rfl
          change Complex.exp (((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I) = _
          rw [Complex.exp_add, h2, hcir_apply]
          have h1 : Complex.exp (((Real.log r : ℝ)) : ℂ) = ((r : ℝ) : ℂ) := by
            rw [← Complex.ofReal_exp, Real.exp_log hrpos]
          rw [h1]
          ring
        have hspec := windingNumber_spec hcir_cl hcir_ne hL
        have hincr : (⟨fun t : I => ((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I, hLcont⟩ : C(I, ℂ)) 1 -
            (⟨fun t : I => ((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I, hLcont⟩ : C(I, ℂ)) 0 =
            2 * (Real.pi : ℂ) * Complex.I := by
          change (((Real.log r : ℝ) : ℂ) + (((2 * Real.pi * ((1 : I) : ℝ) : ℝ)) : ℂ) *
            Complex.I) - (((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * ((0 : I) : ℝ) : ℝ)) : ℂ) * Complex.I) = _
          rw [show ((1 : I) : ℝ) = 1 from rfl, show ((0 : I) : ℝ) = 0 from rfl]
          push_cast
          ring
        rw [hincr] at hspec
        have hcast : (2 * (Real.pi : ℂ) * Complex.I) * 1 =
            (2 * (Real.pi : ℂ) * Complex.I) * ((windingNumber cir p₀ : ℤ) : ℂ) := by
          rw [mul_one]
          exact hspec
        have := mul_left_cancel₀ Complex.two_pi_I_ne_zero hcast
        exact_mod_cast this.symm
      have hwind_in : ∀ ζ : ℂ, dist ζ p₀ < r → windingNumber cir ζ = 1 := by
        intro ζ hζ
        have hζn : ‖ζ - p₀‖ < r := by rwa [dist_eq_norm] at hζ
        have hC : IsPreconnected
            ((fun θ : ℝ => p₀ + (θ : ℂ) * (ζ - p₀)) '' Set.Icc 0 1) :=
          isPreconnected_Icc.image _
            (continuous_const.add
              (Complex.continuous_ofReal.mul continuous_const)).continuousOn
        have hdisj : ∀ t : I,
            cir t ∉ (fun θ : ℝ => p₀ + (θ : ℂ) * (ζ - p₀)) '' Set.Icc 0 1 := by
          rintro t ⟨θ, hθ, hteq⟩
          have h1 := hcir_dist t
          rw [← hteq, dist_eq_norm, add_sub_cancel_left, norm_mul,
            Complex.norm_real, Real.norm_eq_abs] at h1
          have habs : |θ| ≤ 1 := abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩
          nlinarith [norm_nonneg (ζ - p₀), abs_nonneg θ]
        have hζC : ζ ∈ (fun θ : ℝ => p₀ + (θ : ℂ) * (ζ - p₀)) '' Set.Icc 0 1 :=
          ⟨1, ⟨zero_le_one, le_refl 1⟩,
            by change p₀ + ((1 : ℝ) : ℂ) * (ζ - p₀) = ζ; push_cast; ring⟩
        have hp₀C : p₀ ∈ (fun θ : ℝ => p₀ + (θ : ℂ) * (ζ - p₀)) '' Set.Icc 0 1 :=
          ⟨0, ⟨le_refl 0, zero_le_one⟩,
            by change p₀ + ((0 : ℝ) : ℂ) * (ζ - p₀) = p₀; push_cast; ring⟩
        rw [windingNumber_eq_of_preconnected hcir_cl hC hdisj hζC hp₀C]
        exact hwind_center
      have hwind_out : ∀ ζ : ℂ, r < dist ζ p₀ → windingNumber cir ζ = 0 := by
        intro ζ hζ
        refine windingNumber_eq_zero_of_ball (c := p₀) (r := dist ζ p₀)
          hcir_cl (fun t => ?_) (fun h => ?_)
        · rw [Metric.mem_ball, hcir_dist]
          exact hζ
        · rw [Metric.mem_ball] at h
          exact lt_irrefl _ h
      -- ### E6: two indices with the uniform estimates
      have hev_close : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall p₀ δ,
          dist (G z) (χ (f^[φ j] ((z : ℂ̂)))) < ρ :=
        Metric.tendstoUniformlyOn_iff.mp hTUχ ρ hρpos
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev_ball.and hev_close)
      -- ### E7: the attainment step at each large index
      have attain : ∀ j, N ≤ j →
          ∃ zₐ : ℂ, dist zₐ p₀ < r ∧ f^[φ j] ((zₐ : ℂ̂)) = c := by
        intro j hj
        obtain ⟨hjball, hjclose⟩ := hN j hj
        obtain ⟨A, B, hAB⟩ := hread (φ j)
        have hBne : ∀ z ∈ Metric.closedBall p₀ δ, B.eval z ≠ 0 := fun z hz =>
          (hAB z (lt_trans (hjball z hz) (by linarith))).1
        have hFeq : ∀ z ∈ Metric.closedBall p₀ δ,
            χ (f^[φ j] ((z : ℂ̂))) = A.eval z / B.eval z := fun z hz =>
          (hAB z (lt_trans (hjball z hz) (by linarith))).2
        have hp₀cb : p₀ ∈ Metric.closedBall p₀ δ :=
          Metric.mem_closedBall_self hδpos.le
        -- the reading at the center and its closeness to `χ c`
        set q₀ : ℂ := A.eval p₀ / B.eval p₀ with hq₀def
        have hq₀close : ‖q₀ - χ c‖ < ρ := by
          have h1 := hjclose p₀ hp₀cb
          rw [dist_eq_norm] at h1
          have h2 : G p₀ = χ c := by simp only [hGdef, hcdef]
          rw [h2, hFeq p₀ hp₀cb] at h1
          rw [norm_sub_rev] at h1
          exact h1
        -- the reading curve over the circle
        have hΓcont : Continuous fun t : I => A.eval (cir t) / B.eval (cir t) :=
          (A.continuous.comp cir.continuous).div
            (B.continuous.comp cir.continuous)
            (fun t => hBne (cir t) (hcir_mem_cball t))
        set Γ : C(I, ℂ) := ⟨fun t => A.eval (cir t) / B.eval (cir t), hΓcont⟩
          with hΓdef
        have hΓ_apply : ∀ t : I, Γ t = A.eval (cir t) / B.eval (cir t) :=
          fun t => rfl
        have hΓ_read : ∀ t : I, Γ t = χ (f^[φ j] (((cir t) : ℂ̂))) :=
          fun t => (hFeq (cir t) (hcir_mem_cball t)).symm
        have hΓcl : Γ 0 = Γ 1 := by
          rw [hΓ_apply, hΓ_apply, hcir_cl]
        -- distance estimates for the reading curve
        have hΓfar : ∀ t : I, 3 * ρ < ‖Γ t - χ c‖ := by
          intro t
          have h2 := hGfar t
          have h3 : ‖G (cir t) - χ c‖ ≤ ‖G (cir t) - Γ t‖ + ‖Γ t - χ c‖ := by
            have h0 := dist_triangle (G (cir t)) (Γ t) (χ c)
            rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h0
            exact h0
          have h4 : ‖G (cir t) - Γ t‖ < ρ := by
            have h5 := hjclose (cir t) (hcir_mem_cball t)
            rw [dist_eq_norm] at h5
            rw [← hΓ_read t] at h5
            exact h5
          linarith
        have hΓq₀far : ∀ t : I, 2 * ρ < ‖Γ t - q₀‖ := by
          intro t
          have h1 := hΓfar t
          have h3 : ‖Γ t - χ c‖ ≤ ‖Γ t - q₀‖ + ‖q₀ - χ c‖ := by
            have h0 := dist_triangle (Γ t) q₀ (χ c)
            rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h0
            exact h0
          linarith [hq₀close]
        -- winding of composed polynomial curves over the circle
        have hpoly_wind : ∀ P : Polynomial ℂ, (∀ t : I, P.eval (cir t) ≠ 0) →
            windingNumber ⟨fun t => P.eval (cir t),
              P.continuous.comp cir.continuous⟩ 0 =
              (P.roots.map fun ζ => windingNumber cir ζ).sum := by
          intro P hP
          have hPne : P ≠ 0 := by
            intro h0
            apply hP 0
            rw [h0]
            simp
          exact windingNumber_polynomial_comp P hPne cir hcir_cl hP
        have hBcirc_ne : ∀ t : I, B.eval (cir t) ≠ 0 :=
          fun t => hBne (cir t) (hcir_mem_cball t)
        have hBwind : windingNumber ⟨fun t => B.eval (cir t),
            B.continuous.comp cir.continuous⟩ 0 = 0 := by
          rw [hpoly_wind B hBcirc_ne]
          refine Multiset.sum_eq_zero ?_
          intro x hx
          obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
          apply hwind_out
          by_contra hle
          push Not at hle
          exact hBne ζ (Metric.mem_closedBall.mpr (le_trans hle hrδ.le))
            (Polynomial.isRoot_of_mem_roots hζ)
        -- generic facts about the shifted polynomials `A - q·B`
        have hTeval : ∀ (q : ℂ) (t : I), (A - Polynomial.C q * B).eval (cir t)
            = (Γ t - q) * B.eval (cir t) := by
          intro q t
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
          rw [hΓ_apply t, sub_mul, div_mul_cancel₀ _ (hBcirc_ne t)]
        have hTcirc_ne : ∀ (q : ℂ), (∀ t : I, Γ t ≠ q) →
            ∀ t : I, (A - Polynomial.C q * B).eval (cir t) ≠ 0 := by
          intro q hq t
          rw [hTeval q t]
          exact mul_ne_zero (sub_ne_zero.mpr (hq t)) (hBcirc_ne t)
        have hTne : ∀ (q : ℂ), (∀ t : I, Γ t ≠ q) →
            A - Polynomial.C q * B ≠ 0 := by
          intro q hq h0
          exact hTcirc_ne q hq 0 (by rw [h0]; simp)
        have hroots_ne_r : ∀ (q : ℂ), (∀ t : I, Γ t ≠ q) →
            ∀ ζ ∈ (A - Polynomial.C q * B).roots, dist ζ p₀ ≠ r := by
          intro q hq ζ hζ heq
          obtain ⟨t, rfl⟩ := hcir_surj ζ heq
          exact hTcirc_ne q hq t (Polynomial.isRoot_of_mem_roots hζ)
        -- the master winding identity for the reading curve
        have hwindΓ : ∀ (q : ℂ), (∀ t : I, Γ t ≠ q) →
            windingNumber Γ q =
              ((A - Polynomial.C q * B).roots.map
                fun ζ => windingNumber cir ζ).sum := by
          intro q hq
          have hcl₁ : (shiftedCurve Γ q) 0 = (shiftedCurve Γ q) 1 := by
            change Γ 0 - q = Γ 1 - q
            rw [hΓcl]
          have h₁ : ∀ t : I, (shiftedCurve Γ q) t ≠ 0 := by
            intro t
            change Γ t - q ≠ 0
            exact sub_ne_zero.mpr (hq t)
          have hcl₂ : (⟨fun t => B.eval (cir t),
              B.continuous.comp cir.continuous⟩ : C(I, ℂ)) 0 =
              (⟨fun t => B.eval (cir t),
              B.continuous.comp cir.continuous⟩ : C(I, ℂ)) 1 := by
            change B.eval (cir 0) = B.eval (cir 1)
            rw [hcir_cl]
          have h₂ : ∀ t : I, (⟨fun t => B.eval (cir t),
              B.continuous.comp cir.continuous⟩ : C(I, ℂ)) t ≠ 0 := hBcirc_ne
          have hmul := windingNumber_mul (shiftedCurve Γ q)
            ⟨fun t => B.eval (cir t), B.continuous.comp cir.continuous⟩
            hcl₁ hcl₂ h₁ h₂
          have hprodeq : (⟨fun t => (A - Polynomial.C q * B).eval (cir t),
              (A - Polynomial.C q * B).continuous.comp cir.continuous⟩ :
                C(I, ℂ)) =
              shiftedCurve Γ q * ⟨fun t => B.eval (cir t),
                B.continuous.comp cir.continuous⟩ := by
            ext t
            change (A - Polynomial.C q * B).eval (cir t) =
              (Γ t - q) * B.eval (cir t)
            exact hTeval q t
          rw [← hpoly_wind (A - Polynomial.C q * B) (hTcirc_ne q hq), hprodeq,
            hmul, windKey Γ q, hBwind, add_zero]
        -- the curve avoids both test points
        have hq₀ne : ∀ t : I, Γ t ≠ q₀ := by
          intro t h0
          have h1 := hΓq₀far t
          rw [h0, sub_self, norm_zero] at h1
          linarith
        have hχcne : ∀ t : I, Γ t ≠ χ c := by
          intro t h0
          have h1 := hΓfar t
          rw [h0, sub_self, norm_zero] at h1
          linarith
        -- winding about the center reading is at least one
        have hone : (1 : ℤ) ≤ windingNumber Γ q₀ := by
          rw [hwindΓ q₀ hq₀ne]
          have hmem : p₀ ∈ (A - Polynomial.C q₀ * B).roots := by
            rw [Polynomial.mem_roots']
            refine ⟨hTne q₀ hq₀ne, ?_⟩
            change (A - Polynomial.C q₀ * B).eval p₀ = 0
            simp only [Polynomial.eval_sub, Polynomial.eval_mul,
              Polynomial.eval_C]
            rw [hq₀def, div_mul_cancel₀ _ (hBne p₀ hp₀cb), sub_self]
          have hmem1 : (1 : ℤ) ∈ (A - Polynomial.C q₀ * B).roots.map
              fun ζ => windingNumber cir ζ := by
            rw [← hwind_in p₀ (by rw [dist_self]; exact hrpos)]
            exact Multiset.mem_map_of_mem _ hmem
          refine Multiset.single_le_sum ?_ _ hmem1
          intro x hx
          obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
          rcases lt_trichotomy (dist ζ p₀) r with hlt | heq | hgt
          · rw [hwind_in ζ hlt]
            exact zero_le_one
          · exact absurd heq (hroots_ne_r q₀ hq₀ne ζ hζ)
          · rw [hwind_out ζ hgt]
        -- transfer the lower bound to the limit reading `χ c`
        have htrans : windingNumber Γ (χ c) = windingNumber Γ q₀ := by
          have hC : IsPreconnected
              ((fun θ : ℝ => χ c + (θ : ℂ) * (q₀ - χ c)) '' Set.Icc 0 1) :=
            isPreconnected_Icc.image _
              (continuous_const.add
                (Complex.continuous_ofReal.mul continuous_const)).continuousOn
          have hdisj : ∀ t : I, Γ t ∉
              (fun θ : ℝ => χ c + (θ : ℂ) * (q₀ - χ c)) '' Set.Icc 0 1 := by
            rintro t ⟨θ, hθ, hteq⟩
            have h1 := hΓfar t
            rw [← hteq, add_sub_cancel_left, norm_mul, Complex.norm_real,
              Real.norm_eq_abs] at h1
            have habs : |θ| ≤ 1 := abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩
            nlinarith [norm_nonneg (q₀ - χ c), abs_nonneg θ, hq₀close, hρpos]
          have hq₁C : χ c ∈
              (fun θ : ℝ => χ c + (θ : ℂ) * (q₀ - χ c)) '' Set.Icc 0 1 :=
            ⟨0, ⟨le_refl 0, zero_le_one⟩,
              by change χ c + ((0 : ℝ) : ℂ) * (q₀ - χ c) = χ c; push_cast; ring⟩
          have hq₂C : q₀ ∈
              (fun θ : ℝ => χ c + (θ : ℂ) * (q₀ - χ c)) '' Set.Icc 0 1 :=
            ⟨1, ⟨zero_le_one, le_refl 1⟩,
              by change χ c + ((1 : ℝ) : ℂ) * (q₀ - χ c) = q₀; push_cast; ring⟩
          exact windingNumber_eq_of_preconnected hΓcl hC hdisj hq₁C hq₂C
        -- a root of `A - χ c · B` inside the open disk
        obtain ⟨ζ, hζroot, hζin⟩ : ∃ ζ ∈ (A - Polynomial.C (χ c) * B).roots,
            dist ζ p₀ < r := by
          by_contra hnone
          push Not at hnone
          have honeχ : (1 : ℤ) ≤ windingNumber Γ (χ c) := by
            rw [htrans]
            exact hone
          have hzero : ((A - Polynomial.C (χ c) * B).roots.map
              fun ζ => windingNumber cir ζ).sum = 0 := by
            refine Multiset.sum_eq_zero ?_
            intro x hx
            obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
            rcases lt_trichotomy (dist ζ p₀) r with hlt | heq | hgt
            · exact absurd hlt (not_lt.mpr (hnone ζ hζ))
            · exact absurd heq (hroots_ne_r (χ c) hχcne ζ hζ)
            · exact hwind_out ζ hgt
          rw [hwindΓ (χ c) hχcne, hzero] at honeχ
          exact absurd honeχ (by norm_num)
        -- decode the root into an attainment of `c`
        refine ⟨ζ, hζin, ?_⟩
        have hζcb : ζ ∈ Metric.closedBall p₀ δ :=
          Metric.mem_closedBall.mpr (le_trans hζin.le hrδ.le)
        have hζval : dist c (f^[φ j] ((ζ : ℂ̂))) < s :=
          lt_trans (hjball ζ hζcb) (by linarith)
        have hroot : (A - Polynomial.C (χ c) * B).eval ζ = 0 :=
          Polynomial.isRoot_of_mem_roots hζroot
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C] at hroot
        have hBζ := (hAB ζ hζval).1
        have hχeq : χ (f^[φ j] ((ζ : ℂ̂))) = χ c := by
          rw [(hAB ζ hζval).2, div_eq_iff hBζ]
          linear_combination hroot
        exact hχinj _ _ hζval (by rw [dist_self]; exact hs) hχeq
      -- ### E8: two attainments contradict the wandering disjointness
      obtain ⟨z₁, hz₁r, hz₁⟩ := attain N (le_refl N)
      obtain ⟨z₂, hz₂r, hz₂⟩ := attain (N + 1) (Nat.le_succ N)
      have hz₁U : ((z₁ : ℂ̂)) ∈ U :=
        hKU (interior_subset (hδprop z₁
          (Metric.mem_closedBall.mpr (le_trans hz₁r.le hrδ.le))).1)
      have hz₂U : ((z₂ : ℂ̂)) ∈ U :=
        hKU (interior_subset (hδprop z₂
          (Metric.mem_closedBall.mpr (le_trans hz₂r.le hrδ.le))).1)
      have hmem₁ : c ∈ fcOrbit f U (φ N) := by
        rw [← hz₁]
        exact hmem_orbit (φ N) _ hz₁U
      have hmem₂ : c ∈ fcOrbit f U (φ (N + 1)) := by
        rw [← hz₂]
        exact hmem_orbit (φ (N + 1)) _ hz₂U
      have hneq : φ N ≠ φ (N + 1) := ne_of_lt (hφ (Nat.lt_succ_self N))
      exact Set.disjoint_left.mp (hW hneq) hmem₁ hmem₂
  -- ## Stage 3: local constancy everywhere on `interior K` (∞ via puncturing)
  have hloc : ∀ w ∈ interior K, ∀ᶠ w' in 𝓝 w, g w' = g w := by
    intro w hw
    cases w with
    | coe p₀ => exact key p₀ hw
    | infty =>
      obtain ⟨S₀, ⟨hS₀cl, hS₀cp⟩, hS₀sub⟩ :=
        (OnePoint.hasBasis_nhds_infty (X := ℂ)).mem_iff.mp (hopenK.mem_nhds hw)
      obtain ⟨R₀, hR₀⟩ := hS₀cp.isBounded.subset_closedBall 0
      have hR1 : (1 : ℝ) ≤ max R₀ 1 := le_max_right _ _
      have hRpos : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos hR1
      set R : ℝ := max R₀ 1 with hRdef
      -- large-norm points decode into `interior K`
      have hWK : ∀ z : ℂ, R < ‖z‖ → ((z : ℂ̂)) ∈ interior K := by
        intro z hz
        apply hS₀sub
        refine Or.inl ⟨z, fun hzS₀ => ?_, rfl⟩
        have h1 : ‖z‖ ≤ R₀ := by
          have h2 := hR₀ hzS₀
          rwa [Metric.mem_closedBall, dist_zero_right] at h2
        exact absurd hz (not_lt.mpr (h1.trans (le_max_left _ _)))
      -- the punctured plane neighborhood is preconnected
      have hWpre : IsPreconnected {z : ℂ | R < ‖z‖} := by
        have himg : {z : ℂ | R < ‖z‖} =
            (fun p : ℝ × ℝ => ((p.1 : ℂ)) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
              (Set.Ioi R ×ˢ Set.univ) := by
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioi,
            Set.mem_univ, and_true, Prod.exists]
          constructor
          · intro hz
            exact ⟨‖z‖, Complex.arg z, hz, Complex.norm_mul_exp_arg_mul_I z⟩
          · rintro ⟨t, θ, ht, rfl⟩
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (lt_trans hRpos ht)]
            exact ht
        rw [himg]
        exact (isPreconnected_Ioi.prod isPreconnected_univ).image _
          ((Complex.continuous_ofReal.comp continuous_fst).mul
            (Complex.continuous_exp.comp
              ((Complex.continuous_ofReal.comp continuous_snd).mul
                continuous_const))).continuousOn
      have hW'pre : IsPreconnected
          ((fun z : ℂ => ((z : ℂ̂))) '' {z : ℂ | R < ‖z‖}) :=
        hWpre.image _ OnePoint.continuous_coe.continuousOn
      have hz₀W : R < ‖((2 * R : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      -- constancy on the decoded punctured neighborhood
      have hconst : ∀ z : ℂ, R < ‖z‖ →
          g ((z : ℂ̂)) = g ((((2 * R : ℝ) : ℂ) : ℂ̂)) := by
        intro z hz
        refine clopen_const _ hW'pre ?_ _ ⟨z, hz, rfl⟩ _
          ⟨((2 * R : ℝ) : ℂ), hz₀W, rfl⟩
        rintro u ⟨zu, hzu, rfl⟩
        exact key zu (hWK zu hzu)
      -- `∞` lies in the closure of the decoded punctured neighborhood
      have hclinf : (∞ : ℂ̂) ∈ closure
          ((fun z : ℂ => ((z : ℂ̂))) '' {z : ℂ | R < ‖z‖}) := by
        rw [mem_closure_iff_nhds_basis (OnePoint.hasBasis_nhds_infty (X := ℂ))]
        rintro T ⟨hTcl, hTcp⟩
        obtain ⟨R₁, hR₁⟩ := hTcp.isBounded.subset_closedBall 0
        have hbig : R < ‖((max R R₁ + 1 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [le_max_left R R₁])]
          linarith [le_max_left R R₁]
        refine ⟨((((max R R₁ + 1 : ℝ) : ℂ)) : ℂ̂),
          ⟨((max R R₁ + 1 : ℝ) : ℂ), hbig, rfl⟩, Or.inl ⟨_, fun hmem => ?_, rfl⟩⟩
        have h2 := hR₁ hmem
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith [le_max_left R R₁])] at h2
        linarith [le_max_right R R₁]
      -- `g ∞` agrees with the constant value
      have hginf : g (∞ : ℂ̂) = g ((((2 * R : ℝ) : ℂ) : ℂ̂)) := by
        have hcw : ContinuousWithinAt g
            ((fun z : ℂ => ((z : ℂ̂))) '' {z : ℂ | R < ‖z‖}) ∞ :=
          (hgcont.continuousAt (hopenK.mem_nhds hw)).continuousWithinAt
        have h1 := hcw.mem_closure_image hclinf
        have h2 : g '' ((fun z : ℂ => ((z : ℂ̂))) '' {z : ℂ | R < ‖z‖}) ⊆
            {g ((((2 * R : ℝ) : ℂ) : ℂ̂))} := by
          rintro - ⟨-, ⟨zu, hzu, rfl⟩, rfl⟩
          exact hconst zu hzu
        have h3 := closure_mono h2 h1
        rwa [closure_singleton, Set.mem_singleton_iff] at h3
      -- conclude the eventual equality at `∞`
      have hnbhd : ((fun z : ℂ => ((z : ℂ̂))) '' (Metric.closedBall (0 : ℂ) R)ᶜ ∪
          {∞}) ∈ 𝓝 (∞ : ℂ̂) :=
        (OnePoint.hasBasis_nhds_infty (X := ℂ)).mem_of_mem
          ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩
      filter_upwards [hnbhd] with w' hw'
      rcases hw' with ⟨zw, hzw, rfl⟩ | hw'
      · have hzwn : R < ‖zw‖ := by
          rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hzw
          exact hzw
        rw [hconst zw hzwn, hginf]
      · rw [Set.mem_singleton_iff] at hw'
        rw [hw']
  -- ## Stage 4: finale
  intro x hx y hy hVeq
  have hyV : y ∈ connectedComponentIn (interior K) x := by
    rw [hVeq]
    exact mem_connectedComponentIn hy
  exact clopen_const _ isPreconnected_connectedComponentIn
    (fun w hw => hloc w (connectedComponentIn_subset _ _ hw))
    x (mem_connectedComponentIn hx) y hyV

end NoWanderingDomains
