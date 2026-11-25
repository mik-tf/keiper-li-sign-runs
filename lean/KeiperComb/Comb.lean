import KeiperComb.Defs

/-!
# The abstract comb argument (L1, no analytic input)

Data: `c n = ∑_{k<K} 2 w_k cos (n θ_k) + e n`, `|e n| ≤ W` for `n ≥ 1`.  Conclusion: every window of
`L` consecutive `n ≥ 1` contains `n` with `c n > 0` and `n'` with `c n' < 0`.  No RH, no zeta.
-/

open Complex Finset

namespace KeiperComb

/-- A pair of integers `2q + b` in `[x, x + 2)` with `b` given. -/
lemma exists_phase (x : ℝ) (b : ℤ) : ∃ q : ℤ, x ≤ ((2 * q + b : ℤ) : ℝ) ∧ ((2 * q + b : ℤ) : ℝ) < x + 2 := by
  refine ⟨⌈(x - b) / 2⌉, ?_, ?_⟩
  · have h := Int.le_ceil ((x - b) / 2)
    push_cast
    linarith
  · have h := Int.ceil_lt_add_one ((x - b) / 2)
    push_cast
    linarith

lemma cos_shift (y : ℝ) (q : ℤ) (b : ℤ) (ε : ℝ) (h : (b = 0 ∧ ε = 1) ∨ (b = 1 ∧ ε = -1)) :
    Real.cos (y + ((2 * q + b : ℤ) : ℝ) * Real.pi) = ε * Real.cos y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have := Real.cos_add_int_mul_two_pi y q
    have e : y + ((2 * q + 0 : ℤ) : ℝ) * Real.pi = y + (q : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [e, this]; ring
  · have := Real.cos_add_int_mul_two_pi (y + Real.pi) q
    have e : y + ((2 * q + 1 : ℤ) : ℝ) * Real.pi = (y + Real.pi) + (q : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [e, this, Real.cos_add_pi]; ring

/-- The uniform bound `|∑ a_j cos ((N + v_j) θ)| ≤ |B(v)|`, independent of the phase `N θ`. -/
lemma re_bound (a : ℕ → ℝ) (M : ℕ) (θ : ℝ) (N : ℤ) (v : ℕ → ℤ) :
    |∑ j ∈ range M, a j * Real.cos (((N + v j : ℤ) : ℝ) * θ)| ≤ ‖Bk a M θ v‖ := by
  have key : (∑ j ∈ range M, a j * Real.cos (((N + v j : ℤ) : ℝ) * θ)) =
      (Complex.exp (((N : ℝ) * θ : ℝ) * I) * Bk a M θ v).re := by
    unfold Bk
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Complex.exp (((N : ℝ) * θ : ℝ) * I) * ((a j : ℂ) * Complex.exp (((v j : ℝ) * θ : ℝ) * I))
        = (a j : ℂ) * Complex.exp ((((N + v j : ℤ) : ℝ) * θ : ℝ) * I) := by
      have : Complex.exp ((((N + v j : ℤ) : ℝ) * θ : ℝ) * I)
          = Complex.exp (((N : ℝ) * θ : ℝ) * I) * Complex.exp (((v j : ℝ) * θ : ℝ) * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [key]
  calc |(Complex.exp (((N : ℝ) * θ : ℝ) * I) * Bk a M θ v).re|
      ≤ ‖Complex.exp (((N : ℝ) * θ : ℝ) * I) * Bk a M θ v‖ := Complex.abs_re_le_norm _
    _ = ‖Bk a M θ v‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- One sign of the comb: for `ε = ±1` there is `n` in the window with `ε c n > 0`. -/
theorem comb_sign {K M L : ℕ} {w θ c e a : ℕ → ℝ} {W : ℝ} {V : Set (ℕ → ℤ)}
    (hK : 1 ≤ K) (hw : ∀ k, k < K → 0 ≤ w k) (hw0 : 0 < w 0)
    (hc : ∀ n, 1 ≤ n → c n = ∑ k ∈ range K, 2 * w k * Real.cos ((n : ℝ) * θ k) + e n)
    (he : ∀ n, 1 ≤ n → |e n| ≤ W)
    (ha : ∀ j, j < M → 0 ≤ a j) (hS : 0 < ∑ j ∈ range M, a j)
    (hθ0 : 0 < θ 0) (hθ1 : θ 0 < Real.pi / 2)
    (hML : (M : ℝ) * (2 * Real.pi / θ 0) ≤ L)
    (hV : ∀ u ∈ Set.Ico (0 : ℝ) 1, cvec (2 * Real.pi / θ 0) u ∈ V)
    (hN : ∀ v ∈ V, Nbound K M w θ a W v <
      2 * w 0 * (∑ j ∈ range M, a j) * Real.cos (θ 0 / 2))
    (n0 : ℕ) (hn0 : 1 ≤ n0) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∃ n, n0 ≤ n ∧ n < n0 + L ∧ 0 < ε * c n := by
  set S := ∑ j ∈ range M, a j with hSdef
  set P : ℝ := 2 * Real.pi / θ 0 with hPdef
  have hπ := Real.pi_pos
  have hP : 0 < P := by positivity
  have hPθ : P * θ 0 = 2 * Real.pi := by rw [hPdef]; field_simp
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  -- the phase
  obtain ⟨b, hb⟩ : ∃ b : ℤ, (b = 0 ∧ ε = 1) ∨ (b = 1 ∧ ε = -1) := by
    rcases hε with h | h
    · exact ⟨0, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  obtain ⟨q, hq1, hq2⟩ := exists_phase (((n0 : ℝ) - 1 / 2) * 2 / P) b
  set m : ℤ := 2 * q + b with hm
  set τ : ℝ := (m : ℝ) * P / 2 with hτ
  have hτ1 : (n0 : ℝ) - 1 / 2 ≤ τ := by
    have : ((n0 : ℝ) - 1 / 2) * 2 ≤ (m : ℝ) * P := by
      have := mul_le_mul_of_nonneg_right hq1 hP.le
      rwa [div_mul_cancel₀ _ hP.ne'] at this
    rw [hτ]; linarith
  have hτ2 : τ < (n0 : ℝ) - 1 / 2 + P := by
    have : (m : ℝ) * P < (((n0 : ℝ) - 1 / 2) * 2 / P + 2) * P := mul_lt_mul_of_pos_right hq2 hP
    have e2 : (((n0 : ℝ) - 1 / 2) * 2 / P + 2) * P = ((n0 : ℝ) - 1 / 2) * 2 + 2 * P := by
      field_simp
    rw [hτ]; linarith
  have hτθ : τ * θ 0 = (m : ℝ) * Real.pi := by
    rw [hτ]; have := hPθ; nlinarith
  set N0 : ℤ := ⌊τ⌋ with hN0
  set u : ℝ := τ - N0 with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith [Int.floor_le τ]
  have hu1 : u < 1 := by rw [hu]; linarith [Int.lt_floor_add_one τ]
  set v : ℕ → ℤ := cvec P u with hv
  have hvV : v ∈ V := hV u ⟨hu0, hu1⟩
  have hNv := hN v hvV
  -- n_j
  have hv1 : ∀ j : ℕ, (v j : ℝ) ≤ u + j * P + 1 / 2 := fun j => Int.floor_le _
  have hv2 : ∀ j : ℕ, u + j * P + 1 / 2 < (v j : ℝ) + 1 := fun j => Int.lt_floor_add_one _
  have hge : ∀ j : ℕ, n0 ≤ N0 + v j := by
    intro j
    have h1 := hv2 j
    have hj : (0 : ℝ) ≤ j * P := by positivity
    have : ((n0 : ℤ) : ℝ) - 1 < ((N0 + v j : ℤ) : ℝ) := by push_cast; linarith
    have : (n0 : ℤ) - 1 < N0 + v j := by exact_mod_cast this
    omega
  have hlt : ∀ j : ℕ, j < M → N0 + v j < n0 + L := by
    intro j hj
    have h1 := hv1 j
    have hjM : (j : ℝ) + 1 ≤ M := by exact_mod_cast hj
    have : (j : ℝ) * P + P ≤ M * P := by nlinarith
    have : ((N0 + v j : ℤ) : ℝ) < (((n0 + L : ℕ) : ℤ) : ℝ) := by push_cast; linarith
    have : N0 + v j < ((n0 + L : ℕ) : ℤ) := by exact_mod_cast this
    omega
  set nn : ℕ → ℕ := fun j => (N0 + v j).toNat with hnn
  have hnnZ : ∀ j, ((nn j : ℕ) : ℤ) = N0 + v j := by
    intro j; rw [hnn]; simp only; exact Int.toNat_of_nonneg (by have := hge j; omega)
  have hnnR : ∀ j, ((nn j : ℕ) : ℝ) = ((N0 + v j : ℤ) : ℝ) := by
    intro j; rw [← hnnZ j]; simp
  have hnn1 : ∀ j, 1 ≤ nn j := by intro j; have := hge j; have := hnnZ j; omega
  -- zero 0: exact
  set δ : ℕ → ℝ := fun j => (v j : ℝ) - u - j * P with hδ
  have hδ1 : ∀ j, |δ j| ≤ 1 / 2 := by
    intro j; rw [abs_le]; have := hv1 j; have := hv2 j; constructor <;> simp only [hδ] <;> linarith
  have hnδ : ∀ j : ℕ, ((nn j : ℕ) : ℝ) * θ 0 = δ j * θ 0 + ((2 * (q + j) + b : ℤ) : ℝ) * Real.pi := by
    intro j
    rw [hnnR]
    have : ((N0 + v j : ℤ) : ℝ) = δ j + τ + j * P := by
      simp only [hδ, hu]; push_cast; ring
    rw [this]
    have h3 : (τ + j * P) * θ 0 = ((m : ℝ) + 2 * j) * Real.pi := by
      have : τ * θ 0 = (m : ℝ) * Real.pi := hτθ
      have h4 : (j : ℝ) * P * θ 0 = 2 * j * Real.pi := by rw [mul_assoc, hPθ]; ring
      nlinarith
    have : (δ j + τ + j * P) * θ 0 = δ j * θ 0 + (τ + j * P) * θ 0 := by ring
    rw [this, h3]; push_cast [hm]; ring
  have hcos0 : ∀ j : ℕ, Real.cos (((nn j : ℕ) : ℝ) * θ 0) = ε * Real.cos (δ j * θ 0) := by
    intro j
    rw [hnδ j]
    exact cos_shift _ _ _ _ hb
  have hδcos : ∀ j : ℕ, Real.cos (θ 0 / 2) ≤ Real.cos (δ j * θ 0) := by
    intro j
    rw [← Real.cos_abs (δ j * θ 0)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
    rw [abs_mul, abs_of_pos hθ0]
    nlinarith [hδ1 j]
  -- the comb sum
  set T : ℝ := ∑ j ∈ range M, a j * c (nn j) with hT
  have hTexp : T = ∑ k ∈ range K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k))
      + ∑ j ∈ range M, a j * e (nn j) := by
    simp only [hT]
    have : ∀ j ∈ range M, a j * c (nn j) = ∑ k ∈ range K, 2 * w k * (a j * Real.cos (((nn j : ℕ) : ℝ) * θ k))
        + a j * e (nn j) := by
      intro j _
      rw [hc _ (hnn1 j), mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
  have hsplit : ∑ k ∈ range K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k))
      = 2 * w 0 * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0)) +
        ∑ k ∈ Ico 1 K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_eq_sum_Ico_succ_bot (show 0 < K by omega)
      (fun k => 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k)))
  rw [hsplit] at hTexp
  -- pieces
  have hA0 : ε * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0)) ≥ S * Real.cos (θ 0 / 2) := by
    have : ε * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0))
        = ∑ j ∈ range M, a j * Real.cos (δ j * θ 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcos0 j]; linear_combination (a j * Real.cos (δ j * θ 0)) * hε2
    rw [this, hSdef, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (hδcos j) (ha j (Finset.mem_range.mp hj))
  have hrest : ∀ k ∈ Ico 1 K,
      |2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k))| ≤ 2 * w k * ‖Bk a M (θ k) v‖ := by
    intro k hk
    have hk' : k < K := (Finset.mem_Ico.mp hk).2
    rw [abs_mul, abs_of_nonneg (by have := hw k hk'; positivity)]
    apply mul_le_mul_of_nonneg_left _ (by have := hw k hk'; positivity)
    have := re_bound a M (θ k) N0 v
    have heq : ∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k)
        = ∑ j ∈ range M, a j * Real.cos (((N0 + v j : ℤ) : ℝ) * θ k) :=
      Finset.sum_congr rfl fun j _ => by rw [hnnR]
    rw [heq]; exact this
  have hsumrest : |∑ k ∈ Ico 1 K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k))|
      ≤ ∑ k ∈ Ico 1 K, 2 * w k * ‖Bk a M (θ k) v‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    exact hrest k hk
  have hesum : |∑ j ∈ range M, a j * e (nn j)| ≤ W * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [abs_mul, abs_of_nonneg (ha j (Finset.mem_range.mp hj))]
    have := mul_le_mul_of_nonneg_left (he _ (hnn1 j)) (ha j (Finset.mem_range.mp hj))
    linarith
  -- ε T > 0
  have hεT : 0 < ε * T := by
    rw [hTexp, mul_add, mul_add]
    have h0 : ε * (2 * w 0 * ∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0))
        = 2 * w 0 * (ε * ∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0)) := by ring
    rw [h0]
    have hr : ε * ∑ k ∈ Ico 1 K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k))
        ≥ -(∑ k ∈ Ico 1 K, 2 * w k * ‖Bk a M (θ k) v‖) := by
      have := abs_le.mp hsumrest
      rcases hε with rfl | rfl <;> linarith [this.1, this.2]
    have he' : ε * ∑ j ∈ range M, a j * e (nn j) ≥ -(W * S) := by
      have := abs_le.mp hesum
      rcases hε with rfl | rfl <;> linarith [this.1, this.2]
    have hw0' : 2 * w 0 * (S * Real.cos (θ 0 / 2)) ≤ 2 * w 0 *
        (ε * ∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0)) :=
      mul_le_mul_of_nonneg_left hA0 (by positivity)
    have hNv' : W * S + ∑ k ∈ Ico 1 K, 2 * w k * ‖Bk a M (θ k) v‖
        < 2 * w 0 * S * Real.cos (θ 0 / 2) := hNv
    linarith
  -- some term is positive
  by_contra hcon
  push_neg at hcon
  have : ε * T ≤ 0 := by
    have : ε * T = ∑ j ∈ range M, a j * (ε * c (nn j)) := by
      rw [hT, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    refine Finset.sum_nonpos fun j hj => ?_
    have h1 := ha j (Finset.mem_range.mp hj)
    have h2 := hcon (nn j) (by have := hge j; have := hnnZ j; omega)
      (by have := hlt j (Finset.mem_range.mp hj); have := hnnZ j; omega)
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  linarith

/-- Both signs: every window of `L` consecutive `n ≥ 1` has `c n > 0` and `c n' < 0`. -/
theorem comb_both {K M L : ℕ} {w θ c e a : ℕ → ℝ} {W : ℝ} {V : Set (ℕ → ℤ)}
    (hK : 1 ≤ K) (hw : ∀ k, k < K → 0 ≤ w k) (hw0 : 0 < w 0)
    (hc : ∀ n, 1 ≤ n → c n = ∑ k ∈ range K, 2 * w k * Real.cos ((n : ℝ) * θ k) + e n)
    (he : ∀ n, 1 ≤ n → |e n| ≤ W)
    (ha : ∀ j, j < M → 0 ≤ a j) (hS : 0 < ∑ j ∈ range M, a j)
    (hθ0 : 0 < θ 0) (hθ1 : θ 0 < Real.pi / 2)
    (hML : (M : ℝ) * (2 * Real.pi / θ 0) ≤ L)
    (hV : ∀ u ∈ Set.Ico (0 : ℝ) 1, cvec (2 * Real.pi / θ 0) u ∈ V)
    (hN : ∀ v ∈ V, Nbound K M w θ a W v <
      2 * w 0 * (∑ j ∈ range M, a j) * Real.cos (θ 0 / 2))
    (n0 : ℕ) (hn0 : 1 ≤ n0) :
    (∃ n, n0 ≤ n ∧ n < n0 + L ∧ 0 < c n) ∧ (∃ n, n0 ≤ n ∧ n < n0 + L ∧ c n < 0) := by
  constructor
  · obtain ⟨n, h1, h2, h3⟩ := comb_sign hK hw hw0 hc he ha hS hθ0 hθ1 hML hV hN n0 hn0 1 (Or.inl rfl)
    exact ⟨n, h1, h2, by simpa using h3⟩
  · obtain ⟨n, h1, h2, h3⟩ := comb_sign hK hw hw0 hc he ha hS hθ0 hθ1 hML hV hN n0 hn0 (-1) (Or.inr rfl)
    exact ⟨n, h1, h2, by linarith⟩

end KeiperComb
