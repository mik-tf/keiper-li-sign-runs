import Lake
open Lake DSL

package keipercomb where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Same revisions as the step 0 spike (Mathlib fc4f59e5, LeanCert 2aed3bcd); see lake-manifest.json.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"
-- leancert is not imported by any module (B2: not needed); it stays only to keep the manifest and
-- toolchain pin identical to the step 0 spike.
require leancert from git "https://github.com/alerad/leancert" @ "v4.36.0"

@[default_target] lean_lib KeiperComb

-- The numerics modules (heavy, `decide +kernel`) are a separate target: `lake build KeiperCombNumerics`.
lean_lib KeiperCombNumerics where
  roots := #[`KeiperComb.AxiomsNumerics]

-- The comparator check (COMPARATOR.md): `Challenge` is the statement-only file, `Solution` imports the proofs.
lean_lib Challenge
lean_lib Solution
