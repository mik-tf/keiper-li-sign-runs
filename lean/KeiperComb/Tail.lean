import KeiperComb.Defs

/-!
# The bridge: Li's formula (two Props) plus RH plus the zero intervals give the comb data

From `LiSecondDiff c`, `LiWeightSum`, `RiemannHypothesis` and one zero `1/2 + iγ_k` in each
interval, derive `c n = ∑_{k<K} 2 w_k cos (n θ_k) + e n` with `|e n| ≤ W = C - 2 ∑ w_k`.
RH is used only here, only to put the other zeros on the critical line (so `|q| = 1` and
`ρ (1 - ρ) = |ρ|²`).  The conjugate zero is obtained from `riemannZeta_conj`, never assumed.
-/

open Complex Finset ComplexConjugate

namespace KeiperComb

section lemmas

lemma zpt_re (γ : ℝ) : (zpt γ).re = 1 / 2 := by simp [zpt]

lemma zpt_im (γ : ℝ) : (zpt γ).im = γ := by simp [zpt]

lemma one_sub_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : 1 - ρ = conj ρ := by
  apply Complex.ext <;> simp [h] <;> norm_num

lemma ne_zero_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : ρ ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

lemma mul_one_sub_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : ρ * (1 - ρ) = ((‖ρ‖ ^ 2 : ℝ) : ℂ) := by
  rw [one_sub_of_re h, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma norm_q_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : ‖1 - 1 / ρ‖ = 1 := by
  have h0 := ne_zero_of_re h
  have : 1 - 1 / ρ = -(conj ρ / ρ) := by
    rw [← one_sub_of_re h]; field_simp; ring
  rw [this, norm_neg, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr h0)]

lemma sq_norm_zpt (γ : ℝ) : ‖zpt γ‖ ^ 2 = 1 / 4 + γ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, zpt_re, zpt_im]; ring

lemma wOf_eq (γ : ℝ) : wOf γ = 1 / ‖zpt γ‖ ^ 2 := by
  rw [sq_norm_zpt]; rfl

lemma norm_conj_sq (ρ : ℂ) : ‖conj ρ‖ ^ 2 = ‖ρ‖ ^ 2 := by rw [Complex.norm_conj]

/-- `1/ρ² = -w q` on the line. -/
lemma inv_sq_zpt (γ : ℝ) : 1 / (zpt γ) ^ 2 = -((wOf γ : ℝ) * qOf γ) := by
  have h0 : zpt γ ≠ 0 := ne_zero_of_re (zpt_re γ)
  have hq : qOf γ * (zpt γ) ^ 2 = -(((1 / 4 + γ ^ 2 : ℝ)) : ℂ) := by
    have := mul_one_sub_of_re (zpt_re γ)
    rw [← sq_norm_zpt γ]
    unfold qOf
    rw [← this]; field_simp; ring
  have hpos : (1 / 4 + γ ^ 2 : ℝ) ≠ 0 := by positivity
  have hw : ((wOf γ : ℝ) : ℂ) * (((1 / 4 + γ ^ 2 : ℝ)) : ℂ) = 1 := by
    unfold wOf
    have : ((1 / 4 + γ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
    push_cast at this ⊢
    field_simp
    exact div_self (fun h => this (by linear_combination h / 4))
  have hz2 : (zpt γ) ^ 2 ≠ 0 := pow_ne_zero 2 h0
  field_simp
  calc (1 : ℂ) = ((wOf γ : ℝ) : ℂ) * (((1 / 4 + γ ^ 2 : ℝ)) : ℂ) := hw.symm
    _ = _ := by rw [show (((1 / 4 + γ ^ 2 : ℝ)) : ℂ) = -(qOf γ * (zpt γ) ^ 2) by rw [hq]; ring]; ring

lemma norm_qOf (γ : ℝ) : ‖qOf γ‖ = 1 := norm_q_of_re (zpt_re γ)

lemma qOf_eq_exp (γ : ℝ) : qOf γ = Complex.exp ((thetaOf γ : ℝ) * I) := by
  have h := Complex.norm_mul_exp_arg_mul_I (qOf γ)
  rw [norm_qOf] at h
  simpa [thetaOf] using h.symm

/-- The conjugate-pair term: `g(ρ_k) + g(conj ρ_k) = -2 w cos (n θ)`. -/
lemma pair_term (γ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (1 - 1 / zpt γ) ^ (n - 1) / (zpt γ) ^ 2 + (1 - 1 / conj (zpt γ)) ^ (n - 1) / (conj (zpt γ)) ^ 2
      = ((-(2 * wOf γ * Real.cos ((n : ℝ) * thetaOf γ)) : ℝ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : (1 - 1 / zpt γ) ^ (m + 1 - 1) / (zpt γ) ^ 2 = -((wOf γ : ℝ) * qOf γ ^ (m + 1)) := by
    rw [Nat.add_sub_cancel, div_eq_mul_one_div, inv_sq_zpt, pow_succ]
    unfold qOf; ring
  have e2 : (1 - 1 / conj (zpt γ)) ^ (m + 1 - 1) / (conj (zpt γ)) ^ 2
      = conj ((1 - 1 / zpt γ) ^ (m + 1 - 1) / (zpt γ) ^ 2) := by
    simp [map_div₀, map_pow, map_sub]
  rw [e2, e1]
  have hq : qOf γ ^ (m + 1) = Complex.exp ((((m + 1 : ℕ) : ℝ) * thetaOf γ : ℝ) * I) := by
    rw [qOf_eq_exp, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hq, map_neg, map_mul, Complex.conj_ofReal]
  set z := Complex.exp ((((m + 1 : ℕ) : ℝ) * thetaOf γ : ℝ) * I) with hz
  have : -((wOf γ : ℝ) * z) + -((wOf γ : ℝ) * conj z) = -(((wOf γ : ℝ) : ℂ) * (z + conj z)) := by ring
  rw [this, Complex.add_conj, hz, Complex.exp_ofReal_mul_I_re]
  push_cast; ring

/-- A nontrivial zero on the line `re = 1/2`. -/
lemma nontriv_of_re {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re = 1 / 2) : IsNontrivialZero s := by
  refine ⟨hz, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h1; rw [h1] at hre; simp at hre

lemma zetaMult_pos {s : ℂ} (h : IsNontrivialZero s) : 1 ≤ zetaMult s := by
  classical
  have hs1 : s ≠ 1 := h.2.2
  have hU : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun x hx => (differentiableAt_riemannZeta hx).differentiableWithinAt)
      isOpen_compl_singleton
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hz2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hord2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    have : analyticOrderAt riemannZeta 2 = 0 := (hU 2 h2).analyticOrderAt_eq_zero.mpr hz2
    simp [this]
  have hordtop : analyticOrderAt riemannZeta s ≠ ⊤ :=
    fun htop => hz2 ((hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
      (show s ∈ ({1}ᶜ : Set ℂ) from hs1) (analyticOrderAt_eq_top.mp htop)) h2)
  have hord0 : analyticOrderAt riemannZeta s ≠ 0 := (hU s hs1).analyticOrderAt_ne_zero.mpr h.1
  have : 1 ≤ analyticOrderNatAt riemannZeta s := by
    unfold analyticOrderNatAt
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hordtop
    rw [← hk] at hord0 ⊢
    have : k ≠ 0 := fun h0 => hord0 (by simp [h0])
    simp only [ENat.toNat_natCast]
    omega
  unfold zetaMult
  rw [if_pos h]
  exact this

end lemmas

section main

variable {c : ℕ → ℝ} {K : ℕ} {lo hi : ℕ → ℚ}

/-- The chosen ordinates are strictly increasing and positive. -/
lemma gamma_incr (hord : IntervalsOrdered K lo hi) {γ : ℕ → ℝ}
    (hγ : ∀ k, k < K → (lo k : ℝ) ≤ γ k ∧ γ k ≤ (hi k : ℝ)) :
    (∀ k k', k < k' → k' < K → γ k < γ k') ∧ (∀ k, k < K → 0 < γ k) := by
  have hstep : ∀ k, k + 1 < K → γ k < γ (k + 1) := by
    intro k hk
    have h1 := (hγ k (by omega)).2
    have h2 := (hγ (k + 1) hk).1
    have h3 : (hi k : ℝ) < (lo (k + 1) : ℝ) := by exact_mod_cast hord.2.2 k hk
    linarith
  have hlt : ∀ k k', k < k' → k' < K → γ k < γ k' := by
    intro k k' hkk
    induction k', hkk using Nat.le_induction with
    | base => intro h; exact hstep k h
    | succ k' hle ih =>
        intro h
        exact (ih (by omega)).trans (hstep k' h)
  refine ⟨hlt, fun k hk => ?_⟩
  have h0 : (0 : ℝ) < lo 0 := by exact_mod_cast hord.1
  have h00 : (lo 0 : ℝ) ≤ γ 0 := (hγ 0 (by omega)).1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · linarith
  · have := hlt 0 k hk0 hk; linarith

/-- The main bridge. -/
theorem tail_decomp (hRH : RiemannHypothesis) (hL2 : LiSecondDiff c) (hLW : LiWeightSum)
    (hord : IntervalsOrdered K lo hi) {γ : ℕ → ℝ}
    (hγ : ∀ k, k < K → (lo k : ℝ) ≤ γ k ∧ γ k ≤ (hi k : ℝ))
    (hzero : ∀ k, k < K → riemannZeta (zpt (γ k)) = 0) :
    ∃ e : ℕ → ℝ, (∀ n, 1 ≤ n → c n =
        ∑ k ∈ range K, 2 * wOf (γ k) * Real.cos ((n : ℝ) * thetaOf (γ k)) + e n) ∧
      ∀ n, 1 ≤ n → |e n| ≤ Wtail K γ := by
  classical
  obtain ⟨hinc, hpos⟩ := gamma_incr hord hγ
  -- the finite set F of chosen zeros and their conjugates
  set ρ : ℕ → ℂ := fun k => zpt (γ k) with hρ
  set F : Finset ℂ := (range K).image ρ ∪ (range K).image (fun k => conj (ρ k)) with hF
  have hρinj : Set.InjOn ρ (range K : Set ℕ) := by
    intro k hk k' hk' h
    have hk1 := Finset.mem_range.mp hk
    have hk1' := Finset.mem_range.mp hk'
    have : γ k = γ k' := by
      have := congrArg Complex.im h; simpa [hρ, zpt_im] using this
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := hinc k k' h1 hk1'; linarith
    · have := hinc k' k h1 hk1; linarith
  have hcinj : Set.InjOn (fun k => conj (ρ k)) (range K : Set ℕ) := by
    intro k hk k' hk' h
    exact hρinj hk hk' (by simpa [Complex.conj_conj] using congrArg conj h)
  have hdisj : Disjoint ((range K).image ρ) ((range K).image (fun k => conj (ρ k))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k', hk', h⟩ := Finset.mem_image.mp hx'
    have := congrArg Complex.im h
    have hk1 := hpos k (Finset.mem_range.mp hk)
    have hk1' := hpos k' (Finset.mem_range.mp hk')
    simp [hρ, zpt_im] at this
    linarith
  have hFsum : ∀ f : ℂ → ℂ, ∑ x ∈ F, f x =
      ∑ k ∈ range K, (f (ρ k) + f (conj (ρ k))) := by
    intro f
    rw [hF, Finset.sum_union hdisj, Finset.sum_image hρinj, Finset.sum_image hcinj,
      Finset.sum_add_distrib]
  have hFsumR : ∀ f : ℂ → ℝ, ∑ x ∈ F, f x =
      ∑ k ∈ range K, (f (ρ k) + f (conj (ρ k))) := by
    intro f
    rw [hF, Finset.sum_union hdisj, Finset.sum_image hρinj, Finset.sum_image hcinj,
      Finset.sum_add_distrib]
  -- members of F are nontrivial zeros with multiplicity at least one
  have hFnt : ∀ x ∈ F, 1 ≤ zetaMult x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact zetaMult_pos (nontriv_of_re (hzero k (Finset.mem_range.mp hk)) (zpt_re _))
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      have hz : riemannZeta (conj (ρ k)) = 0 := by
        rw [riemannZeta_conj]; simp [hρ, hzero k (Finset.mem_range.mp hk)]
      exact zetaMult_pos (nontriv_of_re hz (by simp [hρ, zpt_re]))
  -- RH on the support
  have hre : ∀ x : ℂ, zetaMult x ≠ 0 → x.re = 1 / 2 := by
    intro x hx
    have : IsNontrivialZero x := by
      by_contra hnt; apply hx; unfold zetaMult; rw [if_neg hnt]
    exact hRH x this.1 this.2.1 this.2.2
  -- real weight sum
  have hs : HasSum (fun x : ℂ => (zetaMult x : ℝ) / ‖x‖ ^ 2) Cconst := by
    have h : HasSum (fun x : ℂ => (zetaMult x : ℂ) / (x * (1 - x))) ((Cconst : ℝ) : ℂ) := hLW
    have heq : (fun x : ℂ => (zetaMult x : ℂ) / (x * (1 - x))) =
        fun x : ℂ => (((zetaMult x : ℝ) / ‖x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      by_cases hm : zetaMult x = 0
      · simp [hm]
      · rw [mul_one_sub_of_re (hre x hm)]; push_cast; rfl
    rw [heq] at h
    have h' := Complex.reCLM.hasSum h
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h'
    exact h'
  -- indicator sums
  have hind : ∀ f : ℂ → ℂ, HasSum (fun x => if x ∈ F then f x else 0) (∑ x ∈ F, f x) := by
    intro f
    have : HasSum (fun x : ℂ => if x ∈ F then f x else 0) (∑ x ∈ F, (if x ∈ F then f x else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    rw [Finset.sum_congr rfl (fun x hx => by simp [hx] : ∀ x ∈ F, (if x ∈ F then f x else 0) = f x)]
      at this
    exact this
  have hindR : ∀ f : ℂ → ℝ, HasSum (fun x => if x ∈ F then f x else 0) (∑ x ∈ F, f x) := by
    intro f
    have : HasSum (fun x : ℂ => if x ∈ F then f x else 0) (∑ x ∈ F, (if x ∈ F then f x else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    rw [Finset.sum_congr rfl (fun x hx => by simp [hx] : ∀ x ∈ F, (if x ∈ F then f x else 0) = f x)]
      at this
    exact this
  -- multiplicity left over
  set dR : ℂ → ℝ := fun x => (zetaMult x : ℝ) - (if x ∈ F then 1 else 0) with hdR
  have hdR0 : ∀ x, 0 ≤ dR x := by
    intro x
    simp only [hdR]
    by_cases hx : x ∈ F
    · have := hFnt x hx; simp [hx]; exact_mod_cast this
    · simp [hx]
  have hu : HasSum (fun x => dR x / ‖x‖ ^ 2) (Cconst - ∑ x ∈ F, 1 / ‖x‖ ^ 2) := by
    have := hs.sub (hindR (fun x => 1 / ‖x‖ ^ 2))
    convert this using 1
    funext x
    simp only [hdR]
    by_cases hx : x ∈ F <;> simp [hx, sub_div]
  have hFw : ∑ x ∈ F, 1 / ‖x‖ ^ 2 = 2 * ∑ k ∈ range K, wOf (γ k) := by
    rw [hFsumR]
    rw [two_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_conj_sq, hρ, ← wOf_eq]
  refine ⟨fun n => c n - ∑ k ∈ range K, 2 * wOf (γ k) * Real.cos ((n : ℝ) * thetaOf (γ k)), ?_, ?_⟩
  · intro n _; ring
  intro n hn
  -- the n-th identity
  set g : ℂ → ℂ := fun x => (1 - 1 / x) ^ (n - 1) / x ^ 2 with hg
  have hsum_n := hL2 n hn
  have hr : HasSum (fun x => (dR x : ℂ) * g x) (-(c n : ℂ) - ∑ x ∈ F, g x) := by
    have := hsum_n.sub (hind g)
    convert this using 1
    funext x
    simp only [hdR, hg]
    by_cases hx : x ∈ F
    · simp [hx]; ring
    · simp [hx]; ring
  have hbd : ∀ x, ‖(dR x : ℂ) * g x‖ ≤ dR x / ‖x‖ ^ 2 := by
    intro x
    by_cases h0 : dR x = 0
    · simp [h0]
    · have hmpos : zetaMult x ≠ 0 := by
        intro hm
        apply h0
        simp only [hdR, hm]
        by_cases hx : x ∈ F
        · have := hFnt x hx; omega
        · simp [hx]
      have hx := hre x hmpos
      have : ‖g x‖ = 1 / ‖x‖ ^ 2 := by
        simp only [hg]
        rw [norm_div, norm_pow, norm_pow, norm_q_of_re hx]; simp
      rw [norm_mul, this, Complex.norm_real, Real.norm_of_nonneg (hdR0 x)]
      apply le_of_eq; ring
  have hnorm := hr.norm_le_of_bounded hu hbd
  -- evaluate the finite part
  have hgF : ∑ x ∈ F, g x = ((-(∑ k ∈ range K, 2 * wOf (γ k) * Real.cos ((n : ℝ) * thetaOf (γ k))) : ℝ) : ℂ) := by
    rw [hFsum]
    have : ∀ k ∈ range K, g (ρ k) + g (conj (ρ k)) =
        ((-(2 * wOf (γ k) * Real.cos ((n : ℝ) * thetaOf (γ k))) : ℝ) : ℂ) := by
      intro k _
      exact pair_term (γ k) n hn
    rw [Finset.sum_congr rfl this]
    push_cast; rw [Finset.sum_neg_distrib]
  have : ((c n - ∑ k ∈ range K, 2 * wOf (γ k) * Real.cos ((n : ℝ) * thetaOf (γ k)) : ℝ) : ℂ)
      = -( -(c n : ℂ) - ∑ x ∈ F, g x) := by
    rw [hgF]; push_cast; ring
  have h2 : ‖((c n - ∑ k ∈ range K, 2 * wOf (γ k) * Real.cos ((n : ℝ) * thetaOf (γ k)) : ℝ) : ℂ)‖
      ≤ Wtail K γ := by
    rw [this, norm_neg]
    unfold Wtail
    rw [hFw] at hnorm
    exact hnorm
  rw [Complex.norm_real, Real.norm_eq_abs] at h2
  exact h2

end main

end KeiperComb
