import KeiperComb.Numerics711Data200
/-! B2 speedup spike: zeros k = 2..200 (0-indexed 1..199), 9 chain vectors, fast checker, `decide +kernel`. -/
namespace KeiperComb.N711
theorem fast_200_ok : checkBatchFast weightsA chainVecs zsAll = true := by decide +kernel
end KeiperComb.N711
#print axioms KeiperComb.N711.fast_200_ok
