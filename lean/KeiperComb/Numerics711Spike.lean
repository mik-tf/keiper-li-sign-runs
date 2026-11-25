import KeiperComb.Numerics711Batch
/-! B2 spike: zeros k = 2..20 (0-indexed 1..19), 9 chain vectors, `decide +kernel`; plus the
zero-1 integer inequality `y^2 < w(hi)` behind `8 * 2pi/theta_1 <= 711` (N0 = gamma_1 * 2^30, H = 1025):
(16 * 3141593)^2 * ((N0+H)^2 + 2^58) < (711 * 10^6)^2 * 2^60. -/
namespace KeiperComb.N711
theorem batch_ok : checkBatch weightsA chainVecs zsAll = true := by decide +kernel
theorem zero1_P_bound :
    (16 * 3141593) ^ 2 * ((15177045555 + 1025) ^ 2 + 2 ^ 58) < (711 * 10 ^ 6) ^ 2 * 2 ^ 60 := by
  decide +kernel
end KeiperComb.N711
#print axioms KeiperComb.N711.batch_ok
