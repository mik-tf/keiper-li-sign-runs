import KeiperComb.Numerics711Data1
/-! B2 spike, one zero (k = 2, 0-indexed 1): all 9 chain vectors by `decide +kernel`. -/
namespace KeiperComb.N711
theorem one_zero_ok : checkBatch weightsA chainVecs zsAll = true := by decide +kernel
end KeiperComb.N711
