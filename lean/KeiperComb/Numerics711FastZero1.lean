import KeiperComb.Numerics711Data1
/-! B2 speedup spike, one zero (k = 2, 0-indexed 1): all 9 chain vectors with the fast checker, `decide +kernel`.
Also a red-first check: with one `rho` halved the checker returns false. -/
namespace KeiperComb.N711
theorem fast_one_zero_ok : checkBatchFast weightsA chainVecs zsAll = true := by decide +kernel
theorem fast_one_zero_neg :
    checkBatchFast weightsA chainVecs
      (zsAll.map fun r => r.map fun t => (t.1, t.2.1 / 2, t.2.2)) = false := by decide +kernel
end KeiperComb.N711
#print axioms KeiperComb.N711.fast_one_zero_ok
#print axioms KeiperComb.N711.fast_one_zero_neg
