import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
set_option verso.exampleModule "AxiomsOfAdaptivity.EstimatorConvergence"
set_option maxHeartbeats 20000000

#doc (Manual) "Estimator Convergence" =>
%%%
htmlSplit := .never
%%%

This chapter formalizes the proof of Corollary 4.8 from *AoA* which states

> *Corollary 4.8*: Suppose we know a-priori convergence to some limit $`U_∞`
  $$`
  \lim_{l \to \infty} \mathbb{d}[\mathcal{T}_l; U_\infty, U(\mathcal{T}_l)] = 0
  `
  and have estimator reduction (for example from {ref "estimator_reduction"}[Lemma 4.7])
  $$`
  η(𝓣_{ℓ+1}; U(𝓣_{ℓ+1}))² ≤ ρ_{est} η(𝓣_ℓ; U(𝓣_ℓ))² + C_{est} 𝕕[𝓣_{ℓ+1}; U(𝓣_{ℓ+1}), U(𝓣_ℓ)]².
  `
  This implies the convergence of the estimator $`
  \lim_{l \to \infty} η^2(𝒯_l, U(𝒯_l)) = 0
  ` and therefore with reliability that $`
  \lim_{l \to \infty} \mathbb{d}(𝒯_l, u, U(𝒯_l)) = 0.
  `

# Formal statement

For the following variables
```anchor vars
variable {α β : Type*} [DecidableEq α] [Lattice α] [OrderBot α] (alg : AdaptiveAlgorithm α β)
```
we define as a convenient abbreviation
```anchor d_seq
def d_seq n := alg.d (alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 n)
```

Corollary 4.8 mentions two different convergences. We split these
into two Lean theorems. The "larger" theorem we want to ultimately show is
```
theorem convergence_of_apriori (hd_seq_lim : Tendsto (d_seq alg) atTop (𝓝 0)) :
  Tendsto (fun n ↦ alg.d (alg.𝒯 <| n) alg.u (alg.U <| alg.𝒯 n)) atTop (𝓝 0) := by { ... }
```
which means that $`\mathbb{d}(𝒯_l, u, U(𝒯_l))` converges to zero if
we have $`\lim_{l \to \infty} \mathbb{d}[\mathcal{T}_l; U(\mathcal{T}_{l+1}), U(\mathcal{T}_l)] = 0`.
Note that this is not exactly the statement from *AoA*. We have left out the implication
$$`
\lim_{l \to \infty} \mathbb{d}[\mathcal{T}_l; U_\infty, U(\mathcal{T}_l)] = 0 \Longrightarrow
\lim_{l \to \infty} \mathbb{d}[\mathcal{T}_l; U(\mathcal{T}_{l+1}), U(\mathcal{T}_l)] = 0.
`
-- TODO what about this implication??

We will reach this theorem by first showing the intermediate result
```
lemma convergence_of_estimator (hd_seq_lim : Tendsto (d_seq alg) atTop (𝓝 0)) :
    Tendsto alg.gη2_seq atTop (𝓝 0) := by { ... }
```
saying that $`η^2(𝒯_l, U(𝒯_l))` converges to zero given a-priori convergence.
This way, both implications from Corollary 4.8 are proven in Lean.

# Proof
