import KeiperComb.Tail

/-!
# B2 glue, real part: transfer of a bound on `∑ a_j q_m^{v_j}` at a rational midpoint `m` to every
`γ` near `m` (Lipschitz in `γ`, no `arg`, no `arctan`), and the shape of the per-zero bound.
-/

open Complex Finset

namespace KeiperComb

lemma norm_pow_sub_pow_le {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [e]
    have h1 : ‖a‖ * ‖a ^ n - b ^ n‖ ≤ ‖a ^ n - b ^ n‖ := by
      nlinarith [norm_nonneg (a ^ n - b ^ n)]
    have h2 : ‖b‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
    have h3 : ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ := by nlinarith [norm_nonneg (a - b)]
    calc ‖a * (a ^ n - b ^ n) + (a - b) * b ^ n‖
        ≤ ‖a * (a ^ n - b ^ n)‖ + ‖(a - b) * b ^ n‖ := norm_add_le _ _
      _ ≤ n * ‖a - b‖ + ‖a - b‖ := by
        rw [norm_mul, norm_mul, norm_pow]; linarith
      _ = ((n + 1 : ℕ) : ℝ) * ‖a - b‖ := by push_cast; ring

lemma norm_qOf_sub (g m : ℝ) : ‖qOf g - qOf m‖ = |g - m| / (‖zpt g‖ * ‖zpt m‖) := by
  have hg : zpt g ≠ 0 := ne_zero_of_re (zpt_re g)
  have hm : zpt m ≠ 0 := ne_zero_of_re (zpt_re m)
  have e1 : zpt g - zpt m = ((g - m : ℝ) : ℂ) * I := by simp [zpt]; ring
  have e2 : qOf g - qOf m = (zpt g - zpt m) / (zpt g * zpt m) := by
    unfold qOf; field_simp; ring
  rw [e2, norm_div, norm_mul, e1, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs]

lemma norm_qOf_sub_le (g m P : ℝ) (hP : 0 < P) (hPle : P ≤ ‖zpt g‖ * ‖zpt m‖) :
    ‖qOf g - qOf m‖ ≤ |g - m| / P := by
  rw [norm_qOf_sub]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hP hPle

lemma Bnorm_bound (a : ℕ → ℝ) (M : ℕ) (v : ℕ → ℕ) (g m r P δ : ℝ) (vm : ℕ)
    (ha : ∀ j, 0 ≤ a j) (hB : ‖∑ j ∈ range M, (a j : ℂ) * (qOf m) ^ (v j)‖ ≤ r)
    (hP : 0 < P) (hPle : P ≤ ‖zpt g‖ * ‖zpt m‖) (hδ : |g - m| ≤ δ)
    (hv : ∀ j, j < M → v j ≤ vm) :
    ‖∑ j ∈ range M, (a j : ℂ) * (qOf g) ^ (v j)‖ ≤ r + (∑ j ∈ range M, a j) * vm * (δ / P) := by
  have hq := norm_qOf_sub_le g m P hP hPle
  have hqd : |g - m| / P ≤ δ / P := div_le_div_of_nonneg_right hδ hP.le
  have hsplit : ∑ j ∈ range M, (a j : ℂ) * (qOf g) ^ (v j) =
      ∑ j ∈ range M, (a j : ℂ) * (qOf m) ^ (v j) +
      ∑ j ∈ range M, (a j : ℂ) * ((qOf g) ^ (v j) - (qOf m) ^ (v j)) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => by ring
  have hterm : ∀ j ∈ range M, ‖(a j : ℂ) * ((qOf g) ^ (v j) - (qOf m) ^ (v j))‖ ≤
      a j * vm * (δ / P) := by
    intro j hj
    have hj' := hv j (Finset.mem_range.mp hj)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha j)]
    have := norm_pow_sub_pow_le (a := qOf g) (b := qOf m) (le_of_eq (norm_qOf g))
      (le_of_eq (norm_qOf m)) (v j)
    have hvj : (v j : ℝ) ≤ vm := by exact_mod_cast hj'
    have hd : 0 ≤ δ / P := le_trans (by positivity) (hq.trans hqd)
    have h4 : (v j : ℝ) * ‖qOf g - qOf m‖ ≤ vm * (δ / P) :=
      mul_le_mul hvj (hq.trans hqd) (norm_nonneg _) (Nat.cast_nonneg _)
    have := mul_le_mul_of_nonneg_left (this.trans h4) (ha j)
    linarith
  rw [hsplit]
  calc _ ≤ ‖∑ j ∈ range M, (a j : ℂ) * (qOf m) ^ (v j)‖ +
        ‖∑ j ∈ range M, (a j : ℂ) * ((qOf g) ^ (v j) - (qOf m) ^ (v j))‖ := norm_add_le _ _
    _ ≤ r + ∑ j ∈ range M, a j * vm * (δ / P) :=
        add_le_add hB ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

end KeiperComb
