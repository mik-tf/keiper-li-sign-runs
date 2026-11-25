import KeiperComb.Numerics711Sound

open Complex Finset

namespace KeiperComb.N711

lemma foldl_add_sum (A : List Nat) : ∀ acc : Nat, ((A.foldl (· + ·) acc : Nat) : ℝ) =
    acc + ∑ j ∈ range A.length, (A.getD j 0 : ℝ) := by
  induction A with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    rw [List.foldl_cons, ih, List.length_cons, Finset.sum_range_succ' _ xs.length]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    push_cast; ring

lemma zpt_norm_sq_ge (g E : ℝ) (hE : 0 ≤ E) (hg : E ≤ g) : E ^ 2 ≤ ‖zpt g‖ ^ 2 := by
  rw [sq_norm_zpt]; nlinarith

/-- Soundness of one chain vector at one zero. -/
theorem chkOne_sound (A v : List Nat) (hlen : A.length = v.length) (hv : ∀ e ∈ v, e < 2048)
    (N rho U : Nat) (hN : Hw ≤ N) (tab : List (Nat × (Int × Int)))
    (htab : ∀ e ∈ v, lookupPow tab e = gpowBin (((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30)) 11 e)
    (h : chkOne A tab (N * N + 2 ^ 58) (((N : Int) - Hw) ^ 2 + 2 ^ 58) (A.foldl (· + ·) 0) v rho U = true) :
    ∀ γ : ℝ, ((N : ℝ) - Hw) / 2 ^ 30 ≤ γ → γ ≤ ((N : ℝ) + Hw) / 2 ^ 30 →
      2 * wOf γ * ‖∑ j ∈ range A.length, (((A.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf γ) ^ (v.getD j 0)‖
        ≤ (U : ℝ) / 2 ^ 40 := by
  intro γ hγ1 hγ2
  simp only [chkOne, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  set D : Nat := N * N + 2 ^ 58 with hD
  set vm : Nat := v.foldl max 0 with hvm
  set XY := (A.zip v).foldl (stepF tab D vm) (0, 0) with hXY
  -- Make D, vm, XY opaque: with their `let` values visible, defeq checks (the old
  -- `exact_mod_cast hDpos.ne'`) unfolded `Nat.cast (N * N + 2 ^ 58)` and blew up.
  clear_value XY vm D
  have hDn : 0 < D := by rw [hD]; exact Nat.add_pos_right _ (by norm_num)
  have hDc : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hDn.ne'
  -- complex identity at the midpoint
  have hsum : ∑ j ∈ range A.length, (((A.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf ((N : ℝ) / 2 ^ 30)) ^ (v.getD j 0)
      = gc XY / ((2 ^ 50 * D ^ vm : Nat) : ℂ) := by
    have hf := foldl_sound tab (((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30)) D vm A v hlen
      (fun e he => ⟨htab e he, hv e he⟩) (0, 0)
    rw [← hXY] at hf
    rw [hf, qOf_grid, ← hD]
    have : gc ((0 : Int), (0 : Int)) = 0 := by apply Complex.ext <;> simp [gc]
    rw [this, zero_add, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjv : j < v.length := by rw [← hlen]; exact Finset.mem_range.mp hj
    have hle : v.getD j 0 ≤ vm := by
      rw [hvm]; apply le_foldl_max; rw [List.getD_eq_getElem _ _ hjv]; exact List.getElem_mem hjv
    have hpow : (D : ℂ) ^ vm = (D : ℂ) ^ (vm - v.getD j 0) * (D : ℂ) ^ (v.getD j 0) := by
      rw [← pow_add]; congr 1; omega
    push_cast
    rw [div_pow, hpow]
    field_simp
    ring
  -- norm bound at the midpoint
  have hnormXY : ‖gc XY‖ ^ 2 = ((XY.1 * XY.1 + XY.2 * XY.2 : Int) : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [gc]; try ring
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ((2 ^ 50 * D ^ vm : Nat) : ℝ) := ⟨_, rfl⟩
  have hQpos : 0 < Q := by
    rw [hQ]; exact_mod_cast Nat.mul_pos (by norm_num) (pow_pos hDn _)
  have hB : ‖∑ j ∈ range A.length, (((A.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf ((N : ℝ) / 2 ^ 30)) ^ (v.getD j 0)‖
      ≤ (rho : ℝ) / 2 ^ 40 := by
    have hnQ : ‖(((2 ^ 50 * D ^ vm : Nat) : ℕ) : ℂ)‖ = Q := by rw [Complex.norm_natCast, hQ]
    have h1' : ((2 : ℝ) ^ 80) * ((XY.1 * XY.1 + XY.2 * XY.2 : Int) : ℝ) ≤ ((rho : ℝ) * Q) ^ 2 := by
      rw [hQ]; exact_mod_cast h1
    rw [hsum, norm_div, hnQ, div_le_div_iff₀ hQpos (by positivity)]
    have hsq : (‖gc XY‖ * 2 ^ 40) ^ 2 ≤ ((rho : ℝ) * Q) ^ 2 := by
      have : (‖gc XY‖ * 2 ^ 40) ^ 2 = 2 ^ 80 * ‖gc XY‖ ^ 2 := by ring
      rw [this, hnormXY]; exact h1'
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg (Nat.cast_nonneg _) hQpos.le)).2
  -- transfer to γ
  set E : ℝ := ((N : ℝ) - Hw) ^ 2 + 2 ^ 58 with hE
  have hE0 : (0 : ℝ) < E := by rw [hE]; positivity
  have hNH : (Hw : ℝ) ≤ N := by exact_mod_cast hN
  have hH0 : (0 : ℝ) ≤ Hw := Nat.cast_nonneg _
  set m : ℝ := (N : ℝ) / 2 ^ 30 with hm
  set g0 : ℝ := ((N : ℝ) - Hw) / 2 ^ 30 with hg0
  clear_value g0 m E
  have hEne : E ≠ 0 := hE0.ne'
  have hg0nn : 0 ≤ g0 := by rw [hg0]; exact div_nonneg (sub_nonneg.2 hNH) (by positivity)
  have hmg : g0 ≤ m := by rw [hg0, hm]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hEg : E / 2 ^ 60 = 1 / 4 + g0 ^ 2 := by rw [hE, hg0]; field_simp; ring
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = E / 2 ^ 60 := ⟨_, rfl⟩
  have hPe : P = 1 / 4 + g0 ^ 2 := hPd.trans hEg
  have hzs : ∀ x : ℝ, g0 ≤ x → P ≤ ‖zpt x‖ ^ 2 := by
    intro x hx
    rw [sq_norm_zpt, hPe]
    have := pow_le_pow_left₀ hg0nn hx 2
    linarith
  have hP : (0 : ℝ) < P := by rw [hPe]; positivity
  have hPle : P ≤ ‖zpt γ‖ * ‖zpt m‖ := by
    have h1 := hzs γ hγ1
    have h2' := hzs m hmg
    have : P ^ 2 ≤ (‖zpt γ‖ * ‖zpt m‖) ^ 2 := by
      rw [mul_pow, sq]
      exact mul_le_mul h1 h2' hP.le (le_trans hP.le h1)
    exact (abs_le_of_sq_le_sq' this (by positivity)).2
  have hδ : |γ - m| ≤ (Hw : ℝ) / 2 ^ 30 := by
    have e1 : g0 = m - (Hw : ℝ) / 2 ^ 30 := by rw [hg0, hm]; ring
    have e2 : ((N : ℝ) + Hw) / 2 ^ 30 = m + (Hw : ℝ) / 2 ^ 30 := by rw [hm]; ring
    rw [abs_le]; constructor <;> linarith
  have hvle : ∀ j, j < A.length → v.getD j 0 ≤ vm := by
    intro j hj
    have hjv : j < v.length := by rw [← hlen]; exact hj
    rw [hvm]; apply le_foldl_max; rw [List.getD_eq_getElem _ _ hjv]; exact List.getElem_mem hjv
  have hBn := Bnorm_bound (fun j => (A.getD j 0 : ℝ) / 2 ^ 50) A.length (fun j => v.getD j 0) γ m
    ((rho : ℝ) / 2 ^ 40) P ((Hw : ℝ) / 2 ^ 30) vm (fun j => by positivity) hB hP hPle hδ hvle
  have hS : (∑ j ∈ range A.length, ((A.getD j 0 : ℝ) / 2 ^ 50)) = ((A.foldl (· + ·) 0 : Nat) : ℝ) / 2 ^ 50 := by
    rw [← Finset.sum_div, foldl_add_sum]; simp
  simp only [hS] at hBn
  have hw : wOf γ ≤ 2 ^ 60 / E := by
    rw [wOf_eq]
    have := one_div_le_one_div_of_le hP (hzs γ hγ1)
    calc 1 / ‖zpt γ‖ ^ 2 ≤ 1 / P := this
      _ = 2 ^ 60 / E := by rw [hPd, one_div_div]
  have hw0 : 0 ≤ wOf γ := by unfold wOf; positivity
  have h2r : (2 : ℝ) ^ 61 * rho * E + 2 ^ 81 * (A.foldl (· + ·) 0 : Nat) * vm * Hw ≤ U * E ^ 2 := by
    have : (2 : Int) ^ 61 * (rho : Int) * (((N : Int) - Hw) ^ 2 + 2 ^ 58) +
        2 ^ 81 * ((A.foldl (· + ·) 0 : Nat) : Int) * vm * Hw ≤ (U : Int) * (((N : Int) - Hw) ^ 2 + 2 ^ 58) ^ 2 := h2
    rw [hE]
    exact_mod_cast this
  calc 2 * wOf γ * ‖∑ j ∈ range A.length, (((A.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf γ) ^ (v.getD j 0)‖
      ≤ 2 * (2 ^ 60 / E) * ((rho : ℝ) / 2 ^ 40 + (((A.foldl (· + ·) 0 : Nat) : ℝ) / 2 ^ 50) * vm *
          (((Hw : ℝ) / 2 ^ 30) / P)) := by
        apply mul_le_mul (by linarith) hBn (norm_nonneg _) (by positivity)
    _ = (2 ^ 61 * rho * E + 2 ^ 81 * (A.foldl (· + ·) 0 : Nat) * vm * Hw) / (2 ^ 40 * E ^ 2) := by
        rw [hPd]; field_simp
    _ ≤ (U : ℝ) / 2 ^ 40 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left h2r (by positivity : (0 : ℝ) ≤ 2 ^ 40)
        nlinarith

end KeiperComb.N711
