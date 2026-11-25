import KeiperComb.Numerics622Assembly

/-!
# Negative tests of the numerics (F6, B6): each is a PROVED fact, so the build stays green.

They show that the real checkers can fail: the window 621 is refused, the batch checker refuses a bad
witness or bound, and the final margin inequality refuses a loosened tail bound.
-/

open Finset

namespace KeiperComb.N622

/-- The window `L = 621` is refused: `P >= 1110601/12500` gives `7 P > 621` (7 * 88.84808 = 621.9). -/
example (P : ℝ) (hP : (1110601 : ℝ) / 12500 ≤ P) : ¬ ((7 : ℝ) * P ≤ 621) := by
  intro h; linarith

/-- Control: the first zero of chunk C00, all 8 chain vectors, passes the batch checker. -/
example : KeiperComb.N711.checkBatchFast weightsA chainVecs (C00.zsAll.map (fun l => l.take 1)) = true := by
  decide +kernel

/-- A zero bound `U` set to 0 is refused. -/
example : KeiperComb.N711.checkBatchFast weightsA chainVecs
    (C00.zsAll.map (fun l => (l.take 1).map (fun t => (t.1, t.2.1, 0)))) = false := by
  decide +kernel

/-- A square-root witness `rho` set to 0 is refused. -/
example : KeiperComb.N711.checkBatchFast weightsA chainVecs
    (C00.zsAll.map (fun l => (l.take 1).map (fun t => (t.1, 0, t.2.2)))) = false := by
  decide +kernel

/-- The final margin inequality fails when the tail bound `461945` (units 10^-7) is replaced by ten times. -/
example : ¬ (∀ i, i < 8 →
    4619450 * SA * 2 ^ 100 + Ui i * 2 ^ 110 * 10 ^ 7 < 2 * Fl * SA * 99936 * 100 + 2 * Tsum * SA * 10 ^ 7) := by
  unfold Ui Fl Tsum SA f160 N0; unfold USall; decide +kernel

end KeiperComb.N622
