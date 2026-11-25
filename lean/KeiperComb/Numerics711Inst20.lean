import KeiperComb.Numerics711Sound3
import KeiperComb.Numerics711Batch

open Complex Finset

namespace KeiperComb.N711

theorem fast_batch_ok' : checkBatchFast weightsA chainVecs zsAll = true := by decide +kernel

theorem hlen20 : ∀ v ∈ chainVecs, weightsA.length = v.length := by decide +kernel
theorem hv20 : ∀ v ∈ chainVecs, ∀ e ∈ v, e < 2048 := by decide +kernel

/-- Zeros 2 to 20 (0-indexed 1 to 19), all nine chain vectors, discharged in Lean. -/
theorem batch20_sound : ∀ col ∈ transpAux (zsAll.headD []).length zsAll, ∀ c0 rest, col = c0 :: rest → Hw ≤ c0.1 →
    ∀ q ∈ chainVecs.zip col, ∀ γ : ℝ, ((c0.1 : ℝ) - Hw) / 2 ^ 30 ≤ γ → γ ≤ ((c0.1 : ℝ) + Hw) / 2 ^ 30 →
      2 * wOf γ * ‖∑ j ∈ range weightsA.length, (((weightsA.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf γ) ^ (q.1.getD j 0)‖
        ≤ (q.2.2.2 : ℝ) / 2 ^ 40 := checkBatchFast_sound weightsA chainVecs zsAll hlen20 hv20 fast_batch_ok'

end KeiperComb.N711
#print axioms KeiperComb.N711.batch20_sound
