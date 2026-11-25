import KeiperComb.Numerics711Sound2

open Complex Finset

namespace KeiperComb.N711

/-- Soundness of one zero, all chain vectors (`col` = `(N, rho, U)` per vector). -/
theorem checkZeroAll_sound (A : List Nat) (vs : List (List Nat)) (c0 : Nat × Nat × Nat)
    (rest : List (Nat × Nat × Nat))
    (hlen : ∀ v ∈ vs, A.length = v.length) (hv : ∀ v ∈ vs, ∀ e ∈ v, e < 2048)
    (hN : Hw ≤ c0.1) (h : checkZeroAll A vs (c0 :: rest) = true) :
    ∀ q ∈ vs.zip (c0 :: rest), ∀ γ : ℝ, ((c0.1 : ℝ) - Hw) / 2 ^ 30 ≤ γ → γ ≤ ((c0.1 : ℝ) + Hw) / 2 ^ 30 →
      2 * wOf γ * ‖∑ j ∈ range A.length, (((A.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf γ) ^ (q.1.getD j 0)‖
        ≤ (q.2.2.2 : ℝ) / 2 ^ 40 := by
  intro q hq γ hγ1 hγ2
  rw [checkZeroAll_eq] at h
  unfold checkZeroAll' at h
  rw [List.all_eq_true] at h
  have hq' := h q hq
  have hqv : q.1 ∈ vs := (List.of_mem_zip hq).1
  refine chkOne_sound A q.1 (hlen _ hqv) (hv _ hqv) c0.1 q.2.2.1 q.2.2.2 hN (tabOf vs c0.1) ?_ hq' γ hγ1 hγ2
  intro e he
  unfold tabOf
  exact lookupPow_map _ (fun e => gpowBin (((c0.1 : Int) * c0.1 - 2 ^ 58, (c0.1 : Int) * 2 ^ 30)) 11 e) e
    (mem_dedup (mem_flat vs e q.1 hqv he))

/-- Soundness of the whole batch: every column (one zero, all chain vectors) is sound. -/
theorem checkBatchFast_sound (A : List Nat) (vs : List (List Nat)) (zsv : List (List (Nat × Nat × Nat)))
    (hlen : ∀ v ∈ vs, A.length = v.length) (hv : ∀ v ∈ vs, ∀ e ∈ v, e < 2048)
    (h : checkBatchFast A vs zsv = true) :
    ∀ col ∈ transpAux (zsv.headD []).length zsv, ∀ c0 rest, col = c0 :: rest → Hw ≤ c0.1 →
    ∀ q ∈ vs.zip col, ∀ γ : ℝ, ((c0.1 : ℝ) - Hw) / 2 ^ 30 ≤ γ → γ ≤ ((c0.1 : ℝ) + Hw) / 2 ^ 30 →
      2 * wOf γ * ‖∑ j ∈ range A.length, (((A.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf γ) ^ (q.1.getD j 0)‖
        ≤ (q.2.2.2 : ℝ) / 2 ^ 40 := by
  intro col hcol c0 rest hc hN q hq γ h1 h2
  unfold checkBatchFast at h
  rw [List.all_eq_true] at h
  have := h col hcol
  subst hc
  exact checkZeroAll_sound A vs c0 rest hlen hv hN this q hq γ h1 h2

end KeiperComb.N711
