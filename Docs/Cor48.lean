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

Due to this proof being the first one to be formalized, its structure
is not optimal. It is split into a simple part where the
global error $`η` and the distance $`\mathbb{d}` are replaced by non-negative
sequences and a bridging theorem that uses the simpler result to show
estimator convergence for an arbitrary $`AdaptiveAlgorithm`, the main difference
being that the codomain of the involved functions (`η`, `d`) is `ℝ` instead of `NNReal`
which was used in the simple part.

## Simple Estimator reduction

In this section $`(η_n)` and $`(d_n)` will be non-negative sequences. This clashes
with the notation for the global error and distance, however because the result we will
prove is only useful when we plugin in the appropriate error estimator and distance sequences
choosing different notation would not be benefitial.

We begin by defining the simplified assumptions as a structure. In the same vein
as with `AdaptiveAlgorithm`, this is a convenient way to work with the
existential quanitification of multiple constants.
```anchor SimpleEstimatorReduction
structure SimpleEstimatorReduction (η d : ℕ → NNReal) where
  q : NNReal
  q_range : q ∈ Set.Ioo 0 1
  C : NNReal
  C_pos : C > 0
  bound : ∀ n, (η (n + 1))^2 ≤ q * (η n)^2 + C * (d n)^2
```
This models the assumption of estimator reduction.

All definitions and theorems of this section will be inside the
{anchorTerm SimpleEstimatorReduction_preamble}`SimpleEstimatorReduction` namespace and include an instance of {anchorTerm SimpleEstimatorReduction}`SimpleEstimatorReduction`
as an assumption:
```anchor SimpleEstimatorReduction_preamble
namespace SimpleEstimatorReduction

variable {η d : ℕ → NNReal} (h : SimpleEstimatorReduction η d)
include h
```

For convenience we define the following abbreviations for terms that appear in the
proofs of this section.
```anchor SimpleEstimatorReduction_defs
def weightedSum (n : ℕ) : NNReal :=
  ∑ k ∈ Finset.range (n + 1), h.q ^ (n - k) * (d k)^2

def upperBound (n : ℕ) : NNReal :=
  h.q ^ (n + 1) * (η 0)^2 + h.C * h.weightedSum n
```
The finite sum ranges up to $`n`, because the `Finset.range` function gives
the natural numbers less than its argument.
Note that they depend on the constants from the reduction property, which is
possible because of the variable definition from before. Because
of the namespace we can then access the e.g. `upperBound` for an instance `h : SimpleEstimatorReduction`
as `h.upperBound`.

The goal is to show from the assumption
$`\lim_{n→∞} d_n = 0` that $`\lim_{n→∞} η_n^2 = 0`, or in Lean
```
theorem convergence_of_estimator_simple (hd_lim : Tendsto d atTop (𝓝 0)) : Tendsto (η^2) atTop (𝓝 0) := by sorry
```

### Upper bound of Estimator

We start by showing that
$$`∀ n∈ℕ_0:\quad η_{n+1}^2 ≤ q^{n+1} η_0^2 + C ∑_{k=0}^{n} q^{n-k} d_k^2`
by induction. The case $`n=0` is trivial, and the step is shown by
$$`
\begin{aligned}
η_{n+2}^2 &≤ q η_{n+1}^2 + C d_{n+1}^2 \\
&\stackrel{(IH)}{≤} q \left( q^{n+1} η_0^2 + C ∑_{k=0}^n q^{n-k} d_k^2 \right) + C d_{n+1}^2 \\
&= q^{n+2} η_0^2 + C ∑_{k=0}^n q^{n-k+1} d_k^2 + C d_{n+1}^2 \\
&= q^{n+2} η_0^2 + C ∑_{k=0}^{n+1} q^{n-k+1} d_k^2
\end{aligned}
`

The Lean proof is very much identical, however the last equality
could be more efficient by using automated tactics in combination with
more granular calculation steps. Doing everything at once requires
surgical rewrites.
```anchor estimator_recursive_upper_bound
lemma estimator_recursive_upper_bound (n : ℕ) :
    (η (n+1))^2 ≤ h.upperBound n := by {
  induction' n with n ih
  · unfold upperBound weightedSum
    simp
    apply h.bound 0
  · calc  η (n + 1 + 1) ^ 2
      _ ≤ h.q * (η (n + 1))^2 + h.C * (d (n + 1))^2 := by apply h.bound
      _ ≤ h.q * h.upperBound n + h.C * (d (n + 1))^2 := by gcongr
      _ = h.upperBound (n+1) := by {
        unfold upperBound weightedSum
        nth_rw 2 [sum_range_succ]
        rw [mul_add, ← mul_assoc, ← pow_succ', ← mul_assoc, mul_comm h.q h.C, mul_assoc, mul_sum, mul_add]
        rw [Finset.sum_congr rfl fun k hk => by
          rw [← mul_assoc, ← pow_succ', ← Nat.sub_add_comm (mem_range_succ_iff.mp hk)]]
        simp [pow_zero, add_assoc]
      }
}
```

### Upper Bound on Weighted Sum

Next, we show that
$$`
∑_{k=0}^n q^{n-k} d_k^2 ≤ (\sup_{i ∈ ℕ_0} d_i)^2 \frac{q⁻¹}{q⁻¹ - 1}
`
assuming that $`(d_n)` is bounded above. This is clear from the calculation
$$`
\begin{aligned}
∑_{k=0}^n q^{n-k} d_k^2 &≤ ∑_{k=0}^n q^{n-k} (\sup_{i ∈ ℕ_0} d_i)^2 \\
&= (\sup_{i ∈ ℕ_0} d_i)^2 ∑_{k=0}^n q^{n-k} \\
&= (\sup_{i ∈ ℕ_0} d_i)^2 q^n ∑_{k=0}^n \frac{1}{q^k} \\
&= (\sup_{i ∈ ℕ_0} d_i)^2 q^n \frac{(1/q)^{n+1}-1}{1/q - 1} \\
&= (\sup_{i ∈ ℕ_0} d_i)^2 \frac{1/q - q^n}{1/q - 1} \\
&≤ (\sup_{i ∈ ℕ_0} d_i)^2 \frac{1/q}{1/q - 1}
\end{aligned}
`
where the essential steps are that we recognise the finite geometric sum and that
we use the bounds $`0 < q < 1`.

The Lean proof uses the same steps, showing supporting results that can be used
in rewrites first.
```anchor weighted_sum_bound
lemma weighted_sum_bound (hd : BddAbove (Set.range d)) (n : ℕ):
    h.weightedSum n ≤ (⨆ i, d i)^2 * (1/h.q) / (1/h.q - 1) := by {
  let ⟨q, q_range, C, C_pos, bound⟩ := h
  unfold weightedSum

  have hq₁ : 1/q ≥ 1 := by {
    simp
    apply one_le_inv_iff₀.mpr
    exact ⟨q_range.1, le_of_lt q_range.2⟩
  }
  have hq₂ : (1 / q) ^ (n + 1) ≥ 1 := one_le_pow₀ hq₁

  have h₁ : ∀ k, d k ≤ (⨆ i, d i) := by {
    intros k
    exact (le_ciSup_iff' hd).mpr fun b a ↦ a k
  }

  have h₂ : ∑ k ∈ (range (n + 1)), q^(n-k) = ∑ k ∈ (range (n + 1)), q^n/q^k := by {
    apply Finset.sum_congr rfl
    intros k hk
    rw [← NNReal.rpow_natCast]
    rw [Nat.cast_sub (mem_range_succ_iff.mp hk)]
    rw [NNReal.rpow_sub_natCast (ne_of_gt q_range.1)]
    simp
  }

  have h₃ : ∑ k ∈ range (n + 1), (1/q)^k = ((1/q)^(n+1) - 1)/(1/q - 1) := by {
    rw[← NNReal.coe_inj]
    push_cast [hq₁, hq₂]
    apply geom_sum_eq
    · simp [ne_of_lt q_range.2]
  }

  have h₄ : q^n * (1/q^(n+1) - 1)/(1/q - 1) = ((1/q) - q^n)/(1/q - 1) := by {
    rw [mul_tsub, mul_one, one_div]
    group
    rw [← zpow_add₀ (ne_of_gt q_range.1)]
    simp
  }

  have h₅ : (1/q) - q^n ≤ 1/q := by {
    have : q^n ≤ 1/q := by {
      trans 1
      · exact pow_le_one₀ (le_of_lt q_range.1) (le_of_lt q_range.2)
      · exact hq₁
    }
    rw [← NNReal.coe_le_coe]
    push_cast [this]
    simp
  }

  calc ∑ k ∈ (range (n + 1)), q^(n-k) * (d k)^2
    _ ≤ ∑ k ∈ (range (n + 1)), q^(n-k) * (⨆ i, d i)^2 := by gcongr; apply h₁
    _ = ∑ k ∈ (range (n + 1)), (⨆ i, d i)^2 * q^(n-k) := by simp_rw [mul_comm]
    _ = (⨆ i, d i)^2 * ∑ k ∈ range (n + 1), q^(n-k) := by simp [mul_sum]
    _ = (⨆ i, d i)^2 * ∑ k ∈ range (n + 1), q^n/q^k := by rw [h₂]
    _ = (⨆ i, d i)^2 * ∑ k ∈ range (n + 1), q^n * (1/q)^k := by field_simp
    _ = (⨆ i, d i)^2 * q^n * ∑ k ∈ range (n + 1), (1/q)^k := by simp [← mul_sum, mul_assoc]
    _ = (⨆ i, d i)^2 * (q^n * (1/q^(n+1) - 1)/(1/q - 1)) := by rw [h₃]; field_simp [mul_assoc]
    _ = (⨆ i, d i)^2 * ((1/q) - q^n)/(1/q - 1) := by rw [h₄, ← mul_div_assoc']
    _ ≤ (⨆ i, d i)^2 * (1/q)/(1/q - 1) := by gcongr
}
```
In {anchorTerm weighted_sum_bound}`h₃` we use the geometric sum theorem from mathlib,
which is formulated for the real numbers. Therefore we have to cast
to the reals and push the cast inwards. For this we have to supply
proof that the terms involved are non-negative ({anchorTerm weighted_sum_bound}`hq₁`,
{anchorTerm weighted_sum_bound}`hq₂`).

### Boundedness of η

-- TODO unify the "we need this because operators have defaults" stories
The main argument for $`\lim_{n→∞} η_n = 0` uses the $`\lim\sup` of $`(η_n)`.
Because the $`\lim\sup` of an unbounded sequence is defined to be zero
in Lean, the next step will be to explicitly show that $`(η_n)`
is bounded, giving us access to mathlib theorems about $`\lim\sup`.

We show that $(η_n)$ is bounded above by $`\sqrt{K}` where
$$`
K \coloneqq \max { η_0^2 + C (\sup_{i ∈ ℕ_0} d_i)^2 \frac{1/q}{1/q - 1}, η_0^2 }.
` (of course still assuming that $(d_n)$ is bounded).
Using the maximum here is mathematically non-sensical because
the first value is greater or equal than the second one. In Lean
it avoids having to show non-negativity of the
$`C (\sup_{i ∈ ℕ_0} d_i)^2 \frac{1/q}{1/q - 1}` term.

What is left to show after taking the square is that $`η_n^2 ≤ K`.
We make a case distinction. If $`n=0`, because of the maximum in the
definition of $`K`, the estimate is trivial. Otherwise, $`n-1` is still
a natural number and:
$$`
\begin{aligned}
η_n^2 &= η_{(n-1)+1}^2 \\
&\stackrel{(Estimator Bound)}{≤} q^{n} η_0^2 + C ∑_{k=0}^{n-1} q^{n-1-k} d_k^2 \\
&\stackrel{(Sum Bound)}{≤} q^{n} η_0^2 + C (\sup_{i ∈ ℕ_0} d_i)^2 \frac{q⁻¹}{q⁻¹ - 1}
&≤ η_0^2 + C (\sup_{i ∈ ℕ_0} d_i)^2 \frac{q⁻¹}{q⁻¹ - 1}
\end{aligned}
`

The Lean proof mirrors this argument:
```anchor estimator_bounded
lemma estimator_bounded (hd : BddAbove (Set.range d)) : BddAbove (Set.range η) := by {
  let K := ((η 0)^2 + h.C * ((⨆ i, d i)^2 * (1/h.q)/(1/h.q - 1))) ⊔ ((η 0)^2)
  use NNReal.sqrt K

  intros x hx
  rcases hx with ⟨n,hn⟩
  rw [← hn]

  apply NNReal.le_sqrt_iff_sq_le.mpr
  by_cases hn : n = 0
  case pos =>
    unfold K
    rw [hn]
    apply le_max_right
  case neg =>
    have : n-1+1 = n := Nat.succ_pred_eq_of_ne_zero hn
    calc (η n)^2
      _ = (η ((n-1)+1))^2 := by rw [this]
      _ ≤ h.upperBound (n-1) := by exact estimator_recursive_upper_bound h (n-1)
      _ = h.q^n * (η 0)^2 + h.C * h.weightedSum (n-1) := by {unfold upperBound; simp [this]}
      _ ≤ h.q^n * (η 0)^2 + h.C * ((⨆ i, d i)^2 * (1/h.q)/(1/h.q - 1)) := by rel [weighted_sum_bound h hd (n-1)]
      _ ≤ (η 0)^2 + h.C * ((⨆ i, d i)^2 * (1/h.q)/(1/h.q - 1)) := by {
        gcongr
        by_cases hη : (η 0)^2 = 0
        case pos =>
          simp [hη]
        case neg =>
          have : h.q^n ≤ 1 := pow_le_one' (le_of_lt h.q_range.2) n
          rw [← mul_le_mul_right (pos_of_ne_zero hη)] at this
          simpa using this
      }
      _ ≤ K := by unfold K; apply le_max_left
}
```

### Limsup of η is Zero

Now we can show that assuming $\lim_{n→∞} d_n = 0$ and boundedness
of $`η` that $`\lim\sup_{n→∞} η_n = 0`.
We do this with the help of the following lemma whose proof we will skip
```lean
lemma smaller_q_eq_zero (a q: NNReal) (hq : q < 1) (ha : a ≤ q*a) : a = 0 := by sorry
```

So using the $`q` from the estimator reduction assumption,
it suffices to show
$$`
\lim\sup_{n→∞} η_n ≤ q \lim\sup_{n→∞} η_n
`.

