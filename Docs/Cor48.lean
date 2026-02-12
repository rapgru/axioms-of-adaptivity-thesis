import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean hiding module
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
set_option verso.exampleModule "AxiomsOfAdaptivity.EstimatorConvergence"
set_option maxHeartbeats 20000000

#doc (Manual) "Estimator Convergence" =>
%%%
htmlSplit := .never
tag := "estimator_convergence"
%%%

This chapter formalizes the proof of Corollary 4.8 from *AoA* which states

> *Corollary 4.8*: Suppose we know a-priori convergence to some limit $`U_∞`
  $$`
  \lim_{l \to \infty} 𝕕[\mathcal{T}_l; U_\infty, U(\mathcal{T}_l)] = 0
  `
  and have estimator reduction (for example from {ref "estimator_reduction"}[Lemma 4.7])
  $$`
  η(\mathcal{T}_{l+1}; U(\mathcal{T}_{l+1}))² ≤ ρ_{\mathrm{est}} η(\mathcal{T}_l; U(\mathcal{T}_l))² + C_{\mathrm{est}} 𝕕[\mathcal{T}_{l+1}; U(\mathcal{T}_{l+1}), U(\mathcal{T}_l)]².
  `
  This implies the convergence of the estimator $`
  \lim_{l \to \infty} η^2(\mathcal{T}_l, U(\mathcal{T}_l)) = 0
  ` and therefore with reliability that $`
  \lim_{l \to \infty} 𝕕(\mathcal{T}_l, u, U(\mathcal{T}_l)) = 0.
  `

# Formal statement

We fix the type variables
```anchor vars
variable {α β : Type*} [DecidableEq α] [Lattice α] [OrderBot α] (alg : AdaptiveAlgorithm α β)
```
globally and define as a convenient abbreviation
```anchor d_seq
def d_seq n := alg.d (alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 n)
```

Corollary 4.8 contains two different convergence statement. We split these
into two Lean theorems. The "stronger" theorem we want to show is
```
theorem convergence_of_apriori (hd_seq_lim : Tendsto (d_seq alg) atTop (𝓝 0)) :
  Tendsto (fun n ↦ alg.d (alg.𝒯 <| n) alg.u (alg.U <| alg.𝒯 n)) atTop (𝓝 0) := by sorry
```
which means that $`𝕕(\mathcal{T}_l, u, U(\mathcal{T}_l))` converges to zero if
we have $`\lim_{l \to \infty} 𝕕[\mathcal{T}_l; U(\mathcal{T}_{l+1}), U(\mathcal{T}_l)] = 0`.

Note that this is not exactly the statement from *AoA*. We have left out the implication
$$`
\lim_{l \to \infty} 𝕕[\mathcal{T}_l; U_\infty, U(\mathcal{T}_l)] = 0 \Longrightarrow
\lim_{l \to \infty} 𝕕[\mathcal{T}_l; U(\mathcal{T}_{l+1}), U(\mathcal{T}_l)] = 0.
`

We will reach this theorem by first showing the intermediate result
```
lemma convergence_of_estimator (hd_seq_lim : Tendsto (d_seq alg) atTop (𝓝 0)) :
    Tendsto alg.gη2_seq atTop (𝓝 0) := by { ... }
```
saying that $`η^2(\mathcal{T}_l, U(\mathcal{T}_l))` converges to zero given a-priori convergence.
This way, both results from Corollary 4.8 are proven in Lean.

# Proof

Because this proof was the first to be formalized, its structure
is not optimal. It is split into a simple part where the
global error $`η^2` and the distance $`𝕕` are replaced by non-negative
sequences and a "glueing" theorem that uses the simpler result to show
estimator convergence for an arbitrary {anchorTerm vars}`AdaptiveAlgorithm`.
The main difference of the stronger variant is
that the codomain of the involved functions (`η`, `𝕕`) is `ℝ` instead of `NNReal`
which was used in the simple part.

## Simple Estimator reduction

In this section $`(η_n)` and $`(d_n)` will be non-negative sequences. This clashes
with the notation for the global error and distance, but because the result we will
prove is only useful when we plug in in the appropriate error estimator and distance sequences,
choosing different notation would be confusing.

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
This structure models the assumption of estimator reduction.

All definitions and theorems of this section will be inside the
`SimpleEstimatorReduction` namespace and include an instance of {anchorTerm SimpleEstimatorReduction}`SimpleEstimatorReduction`
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
The finite sum ranges up to $`n`, because the
{anchorTerm SimpleEstimatorReduction_defs}`Finset.range` function gives
the natural numbers less than its argument.

Note that these definitions depend on the constants from the reduction property, which is
possible because of the variable definition from before.
Since we made the definitions in the namespace `SimpleEstimatorReduction` we can then access e.g. the `upperBound` for an instance `h : SimpleEstimatorReduction`
as `h.upperBound` (dot notation).

The goal is to show that our assumptions and
$`\lim_{n→∞} d_n = 0` imply that $`\lim_{n→∞} η_n^2 = 0`. In Lean this
is written as
```
theorem convergence_of_estimator_simple (hd_lim : Tendsto d atTop (𝓝 0)) : Tendsto (η^2) atTop (𝓝 0) := by sorry
```
where of course we have the included assumption `(h : SimpleEstimatorReduction η d)` from the
`variable` statement. In the next sections we will outline the proof of this theorem.

### Upper bound of Estimator

We start by showing that
$$`∀ n∈ℕ:\quad η_{n+1}^2 ≤ q^{n+1} η_0^2 + C ∑_{k=0}^{n} q^{n-k} d_k^2`
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
    (η (n+1))^2 ≤ h.upperBound n := by
  induction' n with n ih
  · unfold upperBound weightedSum
    simp
    apply h.bound 0
  · calc  η (n + 1 + 1) ^ 2
      _ ≤ h.q * (η (n + 1))^2 + h.C * (d (n + 1))^2 := by apply h.bound
      _ ≤ h.q * h.upperBound n + h.C * (d (n + 1))^2 := by gcongr
      _ = h.upperBound (n+1) := by
        unfold upperBound weightedSum
        nth_rw 2 [sum_range_succ]
        rw [mul_add, ← mul_assoc, ← pow_succ', ← mul_assoc,
            mul_comm h.q h.C, mul_assoc, mul_sum, mul_add]
        rw [Finset.sum_congr rfl fun k hk => by
          rw [← mul_assoc, ← pow_succ',
              ← Nat.sub_add_comm (mem_range_succ_iff.mp hk)]]
        simp [pow_zero, add_assoc]
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

The Lean proof uses the same steps, showing supporting results that are used
in rewrites first.
```anchor weighted_sum_bound
lemma weighted_sum_bound (hd : BddAbove (Set.range d)) (n : ℕ):
    h.weightedSum n ≤ (⨆ i, d i)^2 * (1/h.q) / (1/h.q - 1) := by
  let ⟨q, q_range, C, C_pos, bound⟩ := h
  unfold weightedSum

  have hq₁ : 1/q ≥ 1 := by
    simp
    apply one_le_inv_iff₀.mpr
    exact ⟨q_range.1, le_of_lt q_range.2⟩
  have hq₂ : (1 / q) ^ (n + 1) ≥ 1 := one_le_pow₀ hq₁

  have h₁ : ∀ k, d k ≤ (⨆ i, d i) := by
    intros k
    exact (le_ciSup_iff' hd).mpr fun b a ↦ a k

  have h₂ : ∑ k ∈ (range (n + 1)), q^(n-k) = ∑ k ∈ (range (n + 1)), q^n/q^k := by
    apply Finset.sum_congr rfl
    intros k hk
    rw [← NNReal.rpow_natCast]
    rw [Nat.cast_sub (mem_range_succ_iff.mp hk)]
    rw [NNReal.rpow_sub_natCast (ne_of_gt q_range.1)]
    simp

  have h₃ : ∑ k ∈ range (n + 1), (1/q)^k = ((1/q)^(n+1) - 1)/(1/q - 1) := by
    rw[← NNReal.coe_inj]
    push_cast [hq₁, hq₂]
    apply geom_sum_eq
    · simp [ne_of_lt q_range.2]

  have h₄ : q^n * (1/q^(n+1) - 1)/(1/q - 1) = ((1/q) - q^n)/(1/q - 1) := by
    rw [mul_tsub, mul_one, one_div]
    group
    rw [← zpow_add₀ (ne_of_gt q_range.1)]
    simp

  have h₅ : (1/q) - q^n ≤ 1/q := by
    have : q^n ≤ 1/q := by
      trans 1
      · exact pow_le_one₀ (le_of_lt q_range.1) (le_of_lt q_range.2)
      · exact hq₁
    rw [← NNReal.coe_le_coe]
    push_cast [this]
    simp

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
```
In {anchorTerm weighted_sum_bound}`h₃` we use the geometric sum theorem from mathlib,
which assumes more structure than `NNReal` has. Therefore we have to cast
to the reals and push the cast inwards. For this we have to supply
proof that the terms involved are non-negative ({anchorTerm weighted_sum_bound}`hq₁`,
{anchorTerm weighted_sum_bound}`hq₂`).

### Boundedness of η
%%%
tag := "boundedness_eta"
%%%

The main $`d` argument for $`\lim_{n→∞} η_n = 0` uses the $`\limsup` of $`(η_n)`.
Because the $`\limsup` of an unbounded sequence is defined to be zero
in Lean, the next step will be to explicitly show that $`(η_n)`
is bounded, giving us access to mathlib theorems about $`\limsup`.

We show that $`(η_n)` is bounded above by $`\sqrt{K}` where
$$`
K \coloneqq \max \{ η_0^2 + C (\sup_{i ∈ ℕ_0} d_i)^2 \frac{\frac{1}{q}}{\frac{1}{q} - 1},\; η_0^2 \}
` (of course still assuming that $`(d_n)` is bounded).
Using the maximum here is mathematically non-sensical because
the first value is greater or equal than the second one. In Lean
it avoids having to show non-negativity of the
$`C (\sup_{i ∈ ℕ_0} d_i)^2 \frac{\frac{1}{q}}{\frac{1}{q} - 1}` term.

What is left to show after taking the square is that $`η_n^2 ≤ K`.
We make a case distinction. If $`n=0`, because of the maximum in the
definition of $`K`, the estimate is trivial. Otherwise, $`n-1` is still
a natural number and:
$$`
\begin{aligned}
η_n^2 &= η_{(n-1)+1}^2 \\
&\stackrel{(\mathrm{Estimator\ Bound})}{≤} q^{n} η_0^2 + C ∑_{k=0}^{n-1} q^{n-1-k} d_k^2 \\
&\stackrel{(\mathrm{Sum\ Bound})}{≤} q^{n} η_0^2 + C (\sup_{i ∈ ℕ_0} d_i)^2 \frac{q⁻¹}{q⁻¹ - 1}
&≤ η_0^2 + C (\sup_{i ∈ ℕ_0} d_i)^2 \frac{q⁻¹}{q⁻¹ - 1}
\end{aligned}
`

The Lean proof mirrors this argument:
```anchor estimator_bounded
lemma estimator_bounded (hd : BddAbove (Set.range d)) : BddAbove (Set.range η) := by
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
      _ ≤ (η 0)^2 + h.C * ((⨆ i, d i)^2 * (1/h.q)/(1/h.q - 1)) := by
        gcongr
        by_cases hη : (η 0)^2 = 0
        case pos =>
          simp [hη]
        case neg =>
          have : h.q^n ≤ 1 := pow_le_one' (le_of_lt h.q_range.2) n
          rw [← mul_le_mul_right (pos_of_ne_zero hη)] at this
          simpa using this
      _ ≤ K := by unfold K; apply le_max_left
```

### Limsup of η is Zero

Now we can show that $`\limsup_{n→∞} η_n = 0` assuming $`\lim_{n→∞} d_n = 0` and boundedness
of $`η`.
We do this with the help of the utility lemma
```
lemma smaller_q_eq_zero (a q: NNReal) (hq : q < 1) (ha : a ≤ q*a) : a = 0 := by sorry
```
whose proof we will skip. It is available in the {ref "code"}[Lean code].

So, with the constant $`q` from the estimator reduction assumption,
it suffices to show
$$`
\limsup_{n→∞} η_n ≤ q \limsup_{n→∞} η_n.
`

This is clear from
$$`
\begin{aligned}
\limsup_{n \to \infty} η_n^2 &= \limsup_{n \to \infty} η_{n+1}^2 \\
&≤ \limsup_{n \to \infty} (q η_n^2 + C d_n^2) \\
&≤ \limsup_{n \to \infty} q η_n^2 + \underbrace{\limsup_{n \to \infty} C d_n^2}_{=0\ (\mathrm{convergence\ of\ }\ d_n)} \\
&= \limsup_{n \to \infty} q η_n^2 \\
&= q \limsup_{n \to \infty} η_n^2
\end{aligned}
`
using the convergence of $`(d_n)` and boundedness of $`(η_n)`. The Lean proof
follows this idea and uses utility theorems to supply all necessary boundedness
proofs.

```anchor estimator_limsup_zero
lemma estimator_limsup_zero (hd : Tendsto d atTop (𝓝 0)) (hη₁ : BddAbove (Set.range η)) :
    limsup (η^2) atTop = 0 := by
  let ⟨q, q_range, C, C_pos, bound⟩ := h

  apply smaller_q_eq_zero _ q q_range.2

  have hdc : Tendsto (C • d^2) atTop (𝓝 0) := by
    have := Filter.Tendsto.pow hd 2
    have := Filter.Tendsto.mul_const C this
    simpa [mul_comm] using this

  have hη₂ : BddAbove (Set.range (η^2)) := monotone_map_bdd_above_range (pow_left_mono 2) hη₁
  have hη₃ : BddAbove (Set.range (q • η^2)) := monotone_map_bdd_above_range mul_left_mono hη₂

  have h₁ : limsup ((η^2) ∘ (· + 1)) atTop ≤ limsup (q • η^2 + C • d^2) atTop := by
    apply Filter.limsup_le_limsup
    · exact Filter.Eventually.of_forall bound
    · apply Filter.IsBoundedUnder.isCoboundedUnder_le
      apply BddBelow.isBoundedUnder_of_range
      apply nnreal_fun_bbd_below
    · apply BddAbove.isBoundedUnder_of_range
      apply BddAbove.range_add hη₃ <| Tendsto.bddAbove_range hdc

  have h₂ : limsup (q • η^2 + C • d^2) atTop ≤ limsup (q • η^2) atTop + limsup (C • d^2) atTop := by
    rw [← NNReal.coe_le_coe]
    push_cast [← NNReal.toReal_limsup]

    apply limsup_add_le ?cη_below ?cη_above ?cd_below ?cd_above
    case cη_below =>
      exact BddBelow.isBoundedUnder_of_range <| lift_bound_below _
    case cη_above =>
      exact BddAbove.isBoundedUnder_of_range <| lift_bound_above _ hη₃
    case cd_below =>
      exact Filter.IsBoundedUnder.isCoboundedUnder_le <| BddBelow.isBoundedUnder_of_range <| lift_bound_below _
    case cd_above =>
      exact BddAbove.isBoundedUnder_of_range <| lift_bound_above _ <| Tendsto.bddAbove_range hdc

  calc limsup (η^2) atTop
    _ = limsup (λ n ↦ (η (n+1))^2) atTop := by rw [← Filter.limsup_nat_add _ 1]; rfl
    _ = limsup ((η^2) ∘ (· + 1)) atTop := by rfl
    _ ≤ limsup (q • η^2 + C • d^2) atTop := by exact h₁
    _ ≤ limsup (q • η^2) atTop + limsup (C • d^2) atTop := by exact h₂
    _ = limsup (q • η^2) atTop := by simp [Tendsto.limsup_eq hdc]
    _ = q * limsup (η^2) atTop := by exact nnreal_limsup_const_mul <| BddAbove.isBoundedUnder_of_range hη₂
```
The boundedness proofs are necessary to apply mathlib theorems about `limsup` and use the result
from the {ref "boundedness_eta"}[previous section]. Also note that `•` is the pointwise
multiplication in Lean and is used in the proof multiple times to avoid writing the argument of
{anchorTerm estimator_limsup_zero}`limsup`
as an anonymous function.

### Convergence of η to Zero

The final step is to conclude convergence of $`(η_n)` . We already know that
$`\limsup_{n→∞} η_n = 0`. Naturally
$$`
\liminf_{n→∞} η_n ≤ \limsup_{n→∞} η_n = 0.
`
So by standard analysis, if $`\liminf` and $`\limsup` agree, we have
convergence, which means $`\lim_{n→∞} η_n = 0`.

The Lean proof is totally analogous, again supplying additional boundedness
proofs to unlock the analytical mathlib theorems
```anchor convergence_of_estimator_simple
theorem convergence_of_estimator_simple (hd_lim : Tendsto d atTop (𝓝 0)) : Tendsto (η^2) atTop (𝓝 0) := by
  let hd_above := Tendsto.bddAbove_range hd_lim
  let hη_above := estimator_bounded h hd_above
  have hη2_above := monotone_map_bdd_above_range (pow_left_mono 2) hη_above
  have hη2_below : BddBelow (Set.range (η^2)) := nnreal_fun_bbd_below _
  let hη_limsup := estimator_limsup_zero h hd_lim hη_above

  apply tendsto_of_liminf_eq_limsup
  case hinf =>
    apply nonpos_iff_eq_zero.mp
    rw [← hη_limsup]
    apply liminf_le_limsup
    · exact BddAbove.isBoundedUnder_of_range hη2_above
    · exact BddBelow.isBoundedUnder_of_range hη2_below
  case hsup => exact hη_limsup
  case h => exact BddAbove.isBoundedUnder_of_range hη2_above
  case h' => exact BddBelow.isBoundedUnder_of_range hη2_below
```
Now we have reached the final conclusion of `SimpleEstimatorReduction`.

## Estimator Convergence for `AdaptiveAlgorithm`

In a "glueing" theorem we can now use the theory of `SimpleEstimatorReduction`
to show the actual statement of Corollary 4.8. The first step is
to port the result of `SimpleEstimatorReduction` to the `AdaptiveAlgorithm`
world, i.e. we show that $`\lim_{l→∞} η^2(\mathcal{T}_l, U(\mathcal{T}_l)) = 0`
for the actual refinement indicator `η`.

The only non-trivial step in this endeavour is that
the estimator reduction in {ref "lemma47_formal_statement"}[Lemma 4.7]
was formulated
for any $`δ > 0` with $`ρ_{\mathrm{est}}(δ) < 1`. So, for an estimator reduction property
to actually hold, we have to find a concrete such $`δ`. This is done
in the utility lemma
```
lemma estimator_reduction_delta_exists : ∃ δ > 0, alg.ρ_est δ ∈ Set.Ioo 0 1 ∧ 0 < alg.C_est δ := by sorry
```
which is has an uninspiring proof of the fact that
$$`
δ := \frac12 ((1 - ρ_{\mathrm{red}}) θ (1 - (1 - ρ_{\mathrm{red}}) * θ)⁻¹)
`
fulfils $`ρ_{\mathrm{est}}(δ) < 1`.

Apart from that, mathematically speaking,
it is very obvious that the simplified theorem applies to
the sequences generated from the `AdaptiveAlgorithm`. However, in
Lean this requires a few lines of code. Especially the conversion
between sequences in the `NNReal`s and real sequences requires some
extra proofs:

```anchor convergence_of_estimator
lemma convergence_of_estimator (hd_seq_lim : Tendsto (d_seq alg) atTop (𝓝 0)) :
    Tendsto alg.gη2_seq atTop (𝓝 0) := by

  -- first define the object we want to apply the simplified convergence
  -- theorem to
  rcases alg.estimator_reduction_delta_exists with ⟨δ, hδ, ⟨hρ_est, hC_est⟩⟩

  let ρ_est := alg.ρ_est δ
  let C_est := alg.C_est δ

  have estimator_reduction := alg.estimator_reduction δ hδ hρ_est.2

  let d n := (d_seq alg n).toNNReal

  let est_red := {
    q := ρ_est.toNNReal,
    C := C_est.toNNReal,
    C_pos := by simpa using hC_est
    q_range := by simpa using hρ_est
    bound := by {
      intros n
      apply NNReal.coe_le_coe.mp
      push_cast

      have hd : d n = d_seq alg n := by
        apply Real.coe_toNNReal
        apply alg.non_neg

      have hq : ρ_est.toNNReal = ρ_est := by
        apply Real.coe_toNNReal
        exact le_of_lt hρ_est.1

      have hC : C_est.toNNReal = C_est := by
        apply Real.coe_toNNReal
        exact le_of_lt hC_est

      simp only [alg.hnn_gη_seq, hd, hq, hC]
      unfold d_seq
      exact estimator_reduction n
    }
  : SimpleEstimatorReduction alg.nn_gη_seq d}

  have hd_lim : Tendsto d atTop (𝓝 0) := by
    rw [Eq.symm Real.toNNReal_zero]
    apply tendsto_real_toNNReal hd_seq_lim

  conv =>
    enter [1, n]
    rw [← alg.hnn_gη_seq n]
    norm_cast
  rw [← NNReal.coe_zero]
  apply NNReal.tendsto_coe.mpr
  exact est_red.convergence_of_estimator_simple hd_lim
```
The main point here is that we define the instance {anchorTerm convergence_of_estimator}`est_red`
of type {anchorTerm convergence_of_estimator}`SimpleEstimatorReduction` and access its
{anchorTerm convergence_of_estimator}`est_red.convergence_of_estimator_simple` proof
to show the claim. The sequence we use for $`(η_n)` is {anchorTerm convergence_of_estimator}`nn_gη_seq`
from the {ref "adaptive_alg_defs"}[`AdaptiveAlgorithm` definitions].

Now, the final step is to show convergence of the distance to the unkown limit $`u`.
This follows from reliability, because it allows us to
sandwich $`(𝕕(\mathcal{T}_l, u, U(\mathcal{T}_l)))_{l∈ℕ}`
between the zero-convergent sequence $`(\sqrt{η^2(\mathcal{T}_l, U(\mathcal{T}_l))})_{l∈ℕ}` and the constant
zero sequence:
$$`
0 ≤ 𝕕(\mathcal{T}_l, u, U(\mathcal{T}_l)) ≤ C_{\mathrm{rel}} \sqrt{η^2(\mathcal{T}_l, U(\mathcal{T}_l))}
`
This is translates nicely to a Lean proof using the {anchorTerm convergence_of_apriori}`squeeze_zero`
theorem from mathlib.
```anchor convergence_of_apriori
theorem convergence_of_apriori (hd_seq_lim : Tendsto (d_seq alg) atTop (𝓝 0)) :
  Tendsto (fun n ↦ alg.d (alg.𝒯 <| n) alg.u (alg.U <| alg.𝒯 n)) atTop (𝓝 0) := by
    have := Filter.Tendsto.sqrt (convergence_of_estimator alg hd_seq_lim)
    have := Filter.Tendsto.const_mul alg.C_rel this
    simp at this

    apply squeeze_zero _ _ this
    · exact fun _ ↦ by apply alg.non_neg
    · intros t
      apply alg.reliability
```
This concludes the Lean proof of Corollary 4.8
