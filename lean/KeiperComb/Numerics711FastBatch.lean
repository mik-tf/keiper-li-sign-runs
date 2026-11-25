import KeiperComb.Numerics711Batch
/-! B2 speedup spike: zeros k = 2..20 (0-indexed 1..19), 9 chain vectors, fast checker, `decide +kernel`. -/
namespace KeiperComb.N711
theorem fast_batch_ok : checkBatchFast weightsA chainVecs zsAll = true := by decide +kernel
end KeiperComb.N711
#print axioms KeiperComb.N711.fast_batch_ok
