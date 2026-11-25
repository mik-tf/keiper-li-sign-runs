import KeiperComb.Numerics711Glue

open Complex Finset

namespace KeiperComb.N711

lemma gc_eq (z : Int × Int) : gc z = (z.1 : ℂ) + (z.2 : ℂ) * I := by
  apply Complex.ext <;> simp [gc]

lemma qOf_grid_gen (x c : ℝ) (hc : 0 < c) :
    qOf (x / c) = (((x ^ 2 - c ^ 2 / 4 : ℝ) : ℂ) + ((x * c : ℝ) : ℂ) * I) / ((x ^ 2 + c ^ 2 / 4 : ℝ) : ℂ) := by
  have hD : ((x ^ 2 + c ^ 2 / 4 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < x ^ 2 + c ^ 2 / 4 := by positivity
    exact_mod_cast this.ne'
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hz : (c : ℂ) / 2 + (x : ℂ) * I ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    simp at h1
    linarith
  have e : zpt (x / c) = ((c : ℂ) / 2 + (x : ℂ) * I) / c := by
    unfold zpt; push_cast; field_simp
  have hI : I ^ 2 = -1 := Complex.I_sq
  have hD2 : ((x ^ 2 + c ^ 2 / 4 : ℝ) : ℂ) = ((c : ℂ) / 2 + (x : ℂ) * I) * ((c : ℂ) / 2 - (x : ℂ) * I) := by
    push_cast; linear_combination (x : ℂ) ^ 2 * hI
  have h1 : (1 : ℂ) - 1 / (((c : ℂ) / 2 + (x : ℂ) * I) / c) = ((c : ℂ) / 2 + (x : ℂ) * I - c) / ((c : ℂ) / 2 + (x : ℂ) * I) := by
    rw [one_div_div, eq_div_iff hz, sub_mul, div_mul_cancel₀ _ hz, one_mul]
  unfold qOf
  rw [e, eq_div_iff hD, h1, hD2, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hz]
  push_cast
  linear_combination (-(x : ℂ) ^ 2) * hI

lemma qOf_grid (N : Nat) :
    qOf ((N : ℝ) / 2 ^ 30) =
      gc (((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30)) / ((N * N + 2 ^ 58 : Nat) : ℂ) := by
  have h := qOf_grid_gen (N : ℝ) (2 ^ 30) (by positivity)
  rw [h]
  have e1 : (((N : ℝ) ^ 2 - ((2 : ℝ) ^ 30) ^ 2 / 4 : ℝ) : ℂ) = ((N : ℂ) * N - 2 ^ 58) := by
    push_cast; ring
  have e2 : (((N : ℝ) * 2 ^ 30 : ℝ) : ℂ) = ((N : ℂ) * 2 ^ 30) := by push_cast; ring
  have e3 : (((N : ℝ) ^ 2 + ((2 : ℝ) ^ 30) ^ 2 / 4 : ℝ) : ℂ) = ((N * N + 2 ^ 58 : Nat) : ℂ) := by
    push_cast; ring
  rw [e1, e2, e3]
  have e4 : gc (((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30)) = ((N : ℂ) * N - 2 ^ 58) + ((N : ℂ) * 2 ^ 30) * I := by
    rw [gc_eq]; push_cast; ring
  rw [e4]

lemma gc_lin (f : Int) (z acc : Int × Int) :
    gc (acc.1 + f * z.1, acc.2 + f * z.2) = gc acc + (f : ℂ) * gc z := by
  apply Complex.ext <;> simp [gc]

lemma gc_step (tab D vm) (acc : Int × Int) (p : Nat × Nat) :
    gc (stepF tab D vm acc p) =
      gc acc + (((p.1 * D ^ (vm - p.2) : Nat) : Int) : ℂ) * gc (lookupPow tab p.2) := by
  unfold stepF; exact gc_lin _ _ _

lemma foldl_sound (tab : List (Nat × (Int × Int))) (Zc : Int × Int) (D vm : Nat) :
    ∀ (A v : List Nat), A.length = v.length →
    (∀ e ∈ v, lookupPow tab e = gpowBin Zc 11 e ∧ e < 2048) → ∀ acc : Int × Int,
    gc ((A.zip v).foldl (stepF tab D vm) acc) = gc acc +
      ∑ j ∈ range A.length, ((A.getD j 0 * D ^ (vm - v.getD j 0) : Nat) : ℂ) * (gc Zc) ^ (v.getD j 0) := by
  intro A
  induction A with
  | nil => intro v h _ acc; have : v = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
           subst this; simp
  | cons x xs ih =>
    intro v hl hv acc
    cases v with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      have hy := hv y (by simp)
      simp only [List.zip_cons_cons, List.foldl_cons, List.length_cons]
      rw [ih ys hl' (fun e he => hv e (List.mem_cons_of_mem _ he)), gc_step,
        Finset.sum_range_succ' _ xs.length, hy.1, gpowBin_sound _ 11 y (by have := hy.2; omega)]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      push_cast; ring

end KeiperComb.N711
