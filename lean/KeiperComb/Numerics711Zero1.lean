import KeiperComb.Tail

/-! B2, zero 1: the angle facts for `CombNumerics` (L = 711), from the exact values
`cos θ = 1 - w/2`, `sin θ = γ w`, for the first zero in `[14.1347241, 14.1347262]`
(the certified interval `(15177045555 ± 1025) / 2^30` lies inside). -/

open Complex Finset

namespace KeiperComb.N711

noncomputable section

lemma qOf_re (γ : ℝ) : (qOf γ).re = 1 - wOf γ / 2 := by
  have h : (1 / 4 + γ ^ 2) ≠ 0 := by positivity
  simp [qOf, zpt, wOf, Complex.inv_re, Complex.normSq_apply]
  field_simp
  ring

lemma qOf_im (γ : ℝ) : (qOf γ).im = γ * wOf γ := by
  have h : (1 / 4 + γ ^ 2) ≠ 0 := by positivity
  simp [qOf, zpt, wOf, Complex.inv_im, Complex.normSq_apply]
  field_simp
  ring

lemma wOf_pos (γ : ℝ) : 0 < wOf γ := by unfold wOf; positivity

lemma wOf_lt_two (γ : ℝ) (h : 1 ≤ γ) : wOf γ < 2 := by
  unfold wOf
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_nonneg γ]

lemma theta_sin (γ : ℝ) : Real.sin (thetaOf γ) = γ * wOf γ := by
  unfold thetaOf; rw [Complex.sin_arg, norm_qOf, div_one, qOf_im]

lemma theta_pos (γ : ℝ) (hγ1 : 1 ≤ γ) : 0 < thetaOf γ ∧ thetaOf γ < Real.pi / 2 := by
  have hγ : 0 < γ := by linarith
  have hs : 0 < Real.sin (thetaOf γ) := by rw [theta_sin]; exact mul_pos hγ (wOf_pos γ)
  have hre : 0 < (qOf γ).re := by rw [qOf_re]; linarith [wOf_lt_two γ hγ1]
  refine ⟨?_, Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)⟩
  have h0 : 0 ≤ thetaOf γ := Complex.arg_nonneg_iff.mpr (by rw [qOf_im]; exact (mul_pos hγ (wOf_pos γ)).le)
  rcases h0.eq_or_lt with h | h
  · rw [← h] at hs; simp at hs
  · exact h

lemma theta_ge (γ α : ℝ) (hγ : 1 ≤ γ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (h : α - α ^ 3 / 6 + α ^ 5 / 100 ≤ γ * wOf γ) : α ≤ thetaOf γ := by
  by_contra hlt
  push Not at hlt
  have hpi := Real.pi_gt_three
  have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [(theta_pos γ hγ).1]) (by linarith) hlt
  have hb := Real.sin_bound (x := α) (by rw [abs_of_pos hα0]; exact hα1)
  rw [abs_of_pos hα0] at hb
  rw [theta_sin] at hs
  linarith [(abs_le.mp hb).2]

lemma theta_le (γ α : ℝ) (hγ : 1 ≤ γ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (h : γ * wOf γ ≤ α - α ^ 3 / 6 - α ^ 5 / 100) : thetaOf γ ≤ α := by
  by_contra hlt
  push Not at hlt
  have hpi := Real.pi_gt_three
  have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith [(theta_pos γ hγ).2]) hlt
  have hb := Real.sin_bound (x := α) (by rw [abs_of_pos hα0]; exact hα1)
  rw [abs_of_pos hα0] at hb
  rw [theta_sin] at hs
  linarith [(abs_le.mp hb).1]

lemma gw_bounds (γ : ℝ) (hl : (141347241 : ℝ) / 10 ^ 7 ≤ γ) (hh : γ ≤ (141347262 : ℝ) / 10 ^ 7) :
    (7065 : ℝ) / 10 ^ 5 ≤ γ * wOf γ ∧ γ * wOf γ ≤ (70660 : ℝ) / 10 ^ 6 := by
  have hq : (0 : ℝ) < 1 / 4 + γ ^ 2 := by positivity
  have hp : 0 ≤ (γ - 141347241 / 10 ^ 7) * (141347262 / 10 ^ 7 - γ) :=
    mul_nonneg (by linarith) (by linarith)
  unfold wOf
  rw [mul_one_div]
  constructor
  · rw [le_div_iff₀ hq]; nlinarith
  · rw [div_le_iff₀ hq]; nlinarith

/-- Zero 1: angle facts. -/
theorem zero1_facts (γ : ℝ) (hl : (141347241 : ℝ) / 10 ^ 7 ≤ γ) (hh : γ ≤ (141347262 : ℝ) / 10 ^ 7) :
    0 < thetaOf γ ∧ thetaOf γ < Real.pi / 2 ∧ (8 : ℝ) * (2 * Real.pi / thetaOf γ) ≤ 711 ∧
      (99936 : ℝ) / 10 ^ 5 ≤ Real.cos (thetaOf γ / 2) := by
  have hγ : 1 ≤ γ := by linarith
  obtain ⟨hg1, hg2⟩ := gw_bounds γ hl hh
  obtain ⟨h0, h1⟩ := theta_pos γ hγ
  have hlo : (707 : ℝ) / 10 ^ 4 ≤ thetaOf γ :=
    theta_ge γ _ hγ (by norm_num) (by norm_num) (by norm_num; linarith)
  have hup : thetaOf γ ≤ (7072 : ℝ) / 10 ^ 5 :=
    theta_le γ _ hγ (by norm_num) (by norm_num) (by norm_num; linarith)
  refine ⟨h0, h1, ?_, ?_⟩
  · have := Real.pi_lt_d6
    rw [← mul_div_assoc, div_le_iff₀ h0]
    nlinarith
  · have := Real.one_sub_sq_div_two_le_cos (x := thetaOf γ / 2)
    nlinarith

end

end KeiperComb.N711
