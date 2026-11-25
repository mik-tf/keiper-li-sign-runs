import KeiperComb.Tail

/-! B2, the tail `W` for `CombNumerics` (L = 711).

* `Cconst_le : Cconst ≤ 0.0461945` (`γ_E ≤ H_127 - log 127.5` from the decreasing sequence
  `H_n - log (n + 1/2)`, `log 127.5` and `log (4π)` from the log series).
* `Wtail_le`: `Wtail K γ ≤ 0.0461945 - 2 T / 2^100`, `T = ∑_{k<K} ⌊2^160 / E_k⌋`,
  `E_k = (N_k + 1025)^2 + 2^58`, for any `γ k ∈ [0, (N_k + 1025)/2^30]`.
  The concrete `T` and the final rational comparison are for the assembly step. -/

open Finset Real Filter Topology

namespace KeiperComb.N711

noncomputable section

def aseq (n : ℕ) : ℝ := (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2)

lemma aseq_step (n : ℕ) : aseq (n + 1) ≤ aseq n := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  set x : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    rw [hx]; apply (div_lt_one (by positivity)).2; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hxa : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hxa
  have h0 : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * x ^ (2 * 0 + 1) ≤ Real.log (1 + x) - Real.log (1 - x) :=
    le_hasSum hs 0 (fun k _ => by positivity)
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, div_one, mul_one] at h0
  have e1 : (n : ℝ) + 1 + 1 / 2 = ((n : ℝ) + 1) * (1 + x) := by rw [hx]; field_simp; try ring
  have e2 : (n : ℝ) + 1 / 2 = ((n : ℝ) + 1) * (1 - x) := by rw [hx]; field_simp; try ring
  have hx1' : 0 < 1 - x := by linarith
  have l1 : Real.log ((n : ℝ) + 1 + 1 / 2) = Real.log ((n : ℝ) + 1) + Real.log (1 + x) := by
    rw [e1, Real.log_mul hn.ne' (by linarith)]
  have l2 : Real.log ((n : ℝ) + 1 / 2) = Real.log ((n : ℝ) + 1) + Real.log (1 - x) := by
    rw [e2, Real.log_mul hn.ne' hx1'.ne']
  have h2x : 2 * x = 1 / ((n : ℝ) + 1) := by rw [hx]; field_simp
  unfold aseq
  rw [harmonic_succ]
  push_cast
  have : ((n : ℝ) + 1)⁻¹ = 2 * x := by rw [h2x]; simp
  rw [this]
  have e3 : ((n : ℝ) + 1 + 1 / 2) = (n : ℝ) + 1 + 1 / 2 := rfl
  linarith

lemma eulerMascheroni_le_aseq (n : ℕ) (hn : 1 ≤ n) : Real.eulerMascheroniConstant ≤ aseq n := by
  have hanti : Antitone (fun m : ℕ => aseq (m + 1)) := antitone_nat_of_succ_le (fun m => aseq_step (m + 1))
  have ht : Tendsto (fun m : ℕ => aseq (m + 1)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h1 := (tendsto_add_atTop_iff_nat 1).2 Real.tendsto_harmonic_sub_log
    have h2 : Tendsto (fun m : ℕ => Real.log (1 + 1 / (2 * ((m : ℝ) + 1)))) atTop (𝓝 0) := by
      have : Tendsto (fun m : ℕ => 1 + 1 / (2 * ((m : ℝ) + 1))) atTop (𝓝 1) := by
        have h3 : Tendsto (fun m : ℕ => 1 / (2 * ((m : ℝ) + 1))) atTop (𝓝 0) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
          simp only [mul_zero] at this
          refine this.congr (fun m => ?_)
          field_simp
        simpa using h3.const_add 1
      simpa using this.log (by norm_num)
    have h4 := h1.sub h2
    simp only [sub_zero] at h4
    refine h4.congr (fun m => ?_)
    unfold aseq
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have e : (((m + 1 : ℕ) : ℝ) + 1 / 2) = ((m : ℝ) + 1) * (1 + 1 / (2 * ((m : ℝ) + 1))) := by
      push_cast; field_simp; try ring
    rw [e, Real.log_mul hm.ne' (by positivity)]
    push_cast
    ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hanti.le_of_tendsto ht m

lemma log_127_5 : (48481163521 : ℝ) / 10 ^ 10 ≤ Real.log (127.5) := by
  have hx : |(1 : ℝ) / 256| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 256)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h1 := (abs_le.mp h).1
  have e : (127.5 : ℝ) = 2 ^ 7 * (1 - 1 / 256) := by norm_num
  have l2 := Real.log_two_gt_d9
  rw [e, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num at h1 l2 ⊢
  linarith

lemma log_pi4 : (-2415647 : ℝ) / 10 ^ 7 ≤ Real.log (Real.pi / 4) := by
  have hp := Real.pi_gt_d6
  have h0 : (0.785398 : ℝ) ≤ Real.pi / 4 := by norm_num at hp ⊢; linarith
  have hx : |(1 - 0.785398 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 - 0.785398)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h1 := (abs_le.mp h).1
  have h2 : Real.log (0.785398) ≤ Real.log (Real.pi / 4) := Real.log_le_log (by norm_num) h0
  norm_num at h1 h2 ⊢
  linarith

lemma log_4pi : (25310240212 : ℝ) / 10 ^ 10 ≤ Real.log (4 * Real.pi) := by
  have e : 4 * Real.pi = 2 ^ 4 * (Real.pi / 4) := by ring
  have l2 := Real.log_two_gt_d9
  have h := log_pi4
  rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  norm_num at l2 h ⊢
  linarith

lemma harmonic_127 : (harmonic 127 : ℚ) ≤ 54253345927 / 10 ^ 10 := by decide +kernel

/-- `C = 2 + γ_E - log 4π ≤ 0.0461945`. -/
theorem Cconst_le : Cconst ≤ (461945 : ℝ) / 10 ^ 7 := by
  have h1 := eulerMascheroni_le_aseq 127 (by norm_num)
  have h2 : (harmonic 127 : ℝ) ≤ 54253345927 / 10 ^ 10 := by
    rw [show ((54253345927 : ℝ) / 10 ^ 10) = ((54253345927 / 10 ^ 10 : ℚ) : ℝ) by push_cast; ring]
    exact_mod_cast harmonic_127
  have h3 := log_127_5
  have h4 := log_4pi
  unfold aseq at h1
  unfold Cconst
  have e : ((127 : ℕ) : ℝ) + 1 / 2 = 127.5 := by norm_num
  rw [e] at h1
  linarith

/-- One zero: `γ ≤ (N + 1025) / 2^30` gives the weight lower bound `⌊2^160 / E⌋ / 2^100`. -/
theorem w_ge (N : ℕ) (γ : ℝ) (h0 : 0 ≤ γ) (h : γ ≤ ((N : ℝ) + 1025) / 2 ^ 30) :
    (((2 ^ 160 / ((N + 1025) ^ 2 + 2 ^ 58) : ℕ) : ℝ)) / 2 ^ 100 ≤ wOf γ := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 ^ 100 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 ^ 60 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hab : (2 : ℝ) ^ 160 = a * b := by rw [ha, hb, ← pow_add]
  have h30 : ((2 : ℝ) ^ 30) ^ 2 = b := by rw [hb, ← pow_mul]
  have h58 : (1 / 4 : ℝ) = 2 ^ 58 / b := by rw [hb]; norm_num
  rw [← ha]
  set E : ℕ := (N + 1025) ^ 2 + 2 ^ 58 with hE
  have hEp : (0 : ℝ) < E := by rw [hE]; positivity
  have hq : ((2 ^ 160 / E : ℕ) : ℝ) * E ≤ a * b := by
    have := Nat.div_mul_le_self (2 ^ 160) E
    have h' : (((2 ^ 160 / E : ℕ) : ℝ)) * E ≤ 2 ^ 160 := by exact_mod_cast this
    rwa [hab] at h'
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ((2 ^ 160 / E : ℕ) : ℝ) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  rw [← hQ] at hq ⊢
  have hg2 : γ ^ 2 ≤ (((N : ℝ) + 1025) / 2 ^ 30) ^ 2 := by gcongr
  have hden : (1 / 4 : ℝ) + γ ^ 2 ≤ (E : ℝ) / b := by
    have : (E : ℝ) = ((N : ℝ) + 1025) ^ 2 + 2 ^ 58 := by rw [hE]; push_cast; ring
    rw [this, add_div, ← h58]
    rw [div_pow, h30] at hg2
    linarith
  unfold wOf
  rw [div_le_div_iff₀ ha0 (by positivity)]
  have h5 : Q * (1 / 4 + γ ^ 2) ≤ a := by
    calc Q * (1 / 4 + γ ^ 2) ≤ Q * ((E : ℝ) / b) := mul_le_mul_of_nonneg_left hden hQ0
      _ = Q * E / b := by ring
      _ ≤ a * b / b := by gcongr
      _ = a := by field_simp
  linarith

/-- The tail bound: for ordinates `γ k ∈ [0, (N_k + 1025)/2^30]`, `k < K`,
`Wtail K γ ≤ 0.0461945 - 2 T / 2^100`, `T = ∑ ⌊2^160 / E_k⌋`. -/
theorem Wtail_le (K : ℕ) (γ : ℕ → ℝ) (ns : ℕ → ℕ)
    (h : ∀ k, k < K → 0 ≤ γ k ∧ γ k ≤ ((ns k : ℝ) + 1025) / 2 ^ 30) :
    Wtail K γ ≤ (461945 : ℝ) / 10 ^ 7
      - 2 * ((∑ k ∈ range K, (2 ^ 160 / ((ns k + 1025) ^ 2 + 2 ^ 58) : ℕ) : ℕ) : ℝ) / 2 ^ 100 := by
  have hs : ((∑ k ∈ range K, (2 ^ 160 / ((ns k + 1025) ^ 2 + 2 ^ 58) : ℕ) : ℕ) : ℝ) / 2 ^ 100
      ≤ ∑ k ∈ range K, wOf (γ k) := by
    rw [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum (fun k hk => w_ge (ns k) (γ k) (h k (Finset.mem_range.mp hk)).1
      (h k (Finset.mem_range.mp hk)).2)
  unfold Wtail
  have := Cconst_le
  linarith

end

end KeiperComb.N711
