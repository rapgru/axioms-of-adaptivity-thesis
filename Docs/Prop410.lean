import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
set_option verso.exampleModule "AxiomsOfAdaptivity.Basics"
set_option maxHeartbeats 20000000

#doc (Manual) "Summability of Estimator" =>
%%%
htmlSplit := .never
%%%

This chapter formalizes the proof of Proposition 4.10 from *AoA* which reads as

> *Proposition 4.10*: Assuming estimator reduction
  $$`
  η(𝓣_{ℓ+1}; U(𝓣_{ℓ+1}))² ≤ ρ_{est} η(𝓣_ℓ; U(𝓣_ℓ))² + C_{est} 𝕕[𝓣_{ℓ+1}; U(𝓣_{ℓ+1}), U(𝓣_ℓ)]².
  `
  and reliability, general quasi-orthogonality (A3) implies the summability statements
  1. _Uniform summability_: There exists a constant $`C_3 > 0` such that
      $$`∑_{k=l+1}^∞ η(𝒯_k; U(𝒯_k))² ≤ C_3 η(𝒯_l; U(𝒯_l))² \quad \text{for all } l ∈ ℕ_0.`
  2. _Inverse summability_: For all $`s > 0`, there exists a constant $`C_4 > 0` such that
      $$`∑_{k=0}^{l-1} η(𝒯_k; U(𝒯_k))^{-1/s} ≤ C_4 η(𝒯_l; U(𝒯_l))^{-1/s} \quad \text{for all } l ∈ ℕ_0.`
  3. _Uniform R-linear convergence on any level_: There exist constants $`0 < ρ_1 < 1` and $`C_5 > 0` such that
      $$`η(𝒯_{l+k}; U(𝒯_{l+k}))² ≤ C_5 ρ_1^k η(𝒯_l; U(𝒯_l))² \quad \text{for all } k, l ∈ ℕ_0.`
  where all constants $`C_3`, $`C_4`, $`C_5`, $`ρ_1` only depend on $`ρ_{est}`, $`C_{est}`, $`C_{qo}(ε_{qo})`, $`s`.

From  {ref "summability_equivalence"}[Lemma 4.9] we already know that the summability
statements are equivalent, so to prove this proposition we only need to show one of them.
