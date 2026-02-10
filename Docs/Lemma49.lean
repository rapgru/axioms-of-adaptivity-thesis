import VersoManual
import Docs.Papers
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Common

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
set_option verso.exampleModule "AxiomsOfAdaptivity.Summability"
set_option maxHeartbeats 20000000

#doc (Manual) "Summability Equivalence" =>
%%%
htmlSplit := .never
tag := "summability_equivalence"
%%%

This chapter formalizes the proof of the analytical summability Lemma 4.9 from *AoA*.
It states

> *Lemma 4.9*: The following statements are pairwise equivalent:
  1.) _Uniform summability_: There exists a constant $`C_3 > 0` such that
      $$`∑_{k=l+1}^∞ η(𝒯_k; U(𝒯_k))² ≤ C_3 η(𝒯_l; U(𝒯_l))² \quad \text{for all } l ∈ ℕ_0.`
  2.) _Inverse summability_: For all $`s > 0`, there exists a constant $`C_4 > 0` such that
      $$`∑_{k=0}^{l-1} η(𝒯_k; U(𝒯_k))^{-1/s} ≤ C_4 η(𝒯_l; U(𝒯_l))^{-1/s} \quad \text{for all } l ∈ ℕ_0.`
  3.) _Uniform R-linear convergence on any level_: There exist constants $`0 < ρ_1 < 1` and $`C_5 > 0` such that
      $$`η(𝒯_{l+k}; U(𝒯_{l+k}))² ≤ C_5 ρ_1^k η(𝒯_l; U(𝒯_l))² \quad \text{for all } k, l ∈ ℕ_0.`

# Formal statement
%%%
tag := "lem47_formal_statement"
%%%

While a sharp observer might immediately spot a missing assumption in this theorem,
the author only did so after the Lean proof did not work out at some point, which
shows that a formalization can help spot mistakes of this sort. The problem is that
inverse summability is only well-defined if $∀ n ∈ ℕ_0 : a_n ≠ 0$.
-- Ramifications in AoA?

We can also observe, that the statement is equally true if we replace the
global error estimator by an arbitrary non-negative sequence $`(a_n)`. Because $`η`
is non-negative by definition, we can recover the original form
by plugging in the sequence $`(η(𝒯_l, U(𝒯_l)))`. So we
will show the equivalence in the form:

> For any *positive* sequence $`(a_n)`, the following statements are pairwise equivalent:
  1.) _Uniform summability_: There exists a constant $`C_3 > 0` such that
      $$`∑_{k=l+1}^∞ a_k² ≤ C_3 a_l² \quad \text{for all } l ∈ ℕ.`
  2.) _Inverse summability_: For all $`s > 0`, there exists a constant $`C_4 > 0` such that
      $$`∑_{k=0}^{l-1} a_k^{-1/s} ≤ C_4 a_l^{-1/s} \quad \text{for all } l ∈ ℕ.`
  3.) _Uniform R-linear convergence on any level_: There exist constants $`0 < ρ_1 < 1` and $`C_5 > 0` such that
      $$`a{l+k}² ≤ C_5 ρ_1^k a_l² \quad \text{for all } k, l ∈ ℕ_0.`

To translate this into Lean, we first define the statements 1-3.) as `Prop`s
```anchor summability_defs
def uniform_summability (a : ℕ → NNReal) :=
  Summable (a^2) ∧ ∃ C > 0, ∀ l : ℕ, ∑' k, (a^2) (k + l + 1) ≤ C * (a^2) l

def inverse_summability (a : ℕ → NNReal) :=
  ∀ s : ℝ, s > 0 → ∃ C > 0, ∀ l : ℕ, ∑ k ∈ range l, (a k)^(-1/s) ≤ C * (a l)^(-1/s)

def uniform_r_linear_convergence (a : ℕ → NNReal) :=
  ∃ q ∈ (Set.Ioo 0 1), ∃ C > 0, ∀ k, ∀ l,
    (a^2) (l+k) ≤ C * q^k * (a^2) l
```

Note that the starting indices for the sums have been translated to an addition of
the lower index to the running index inside the sum. This is because
infinite sums over the natural numbers sum from $`0` to $`\infty` in Lean
and there is no syntax to change this summation range.

Also, because
an infinite sum appears in uniform summability, we need to add the technical
assumption that $`(a_n)` is summable in the first statement.
This is essential, because by convention mathlib4 handles the edge cases
of mathematical operators in the following way: Instead of
throwing an error or having operators only partially defined, when the
value of the operator is nonsensical a designated instance of the result datatype
is the result value. In the case of a divergent sum in the real numbers this designated
instance is the real $`0`. So to gain information when we use {anchorTerm summability_defs}`uniform_summability`
as an assumption we need to know that $`a_n` is summable, otherwise the estimate
is of no value because it says $`0 ≤ C * (a^2) l` which is always true.
This is no discrepancy to the text version of the theorem, because
when the reader will understand that the inequality sign of the statement also
says that the sum has to converge. In other words, in *AoA* the $`≤` sign means
more than the relation $`≤ ⊆ ℝ × ℝ`, while in Lean the latter relation is what
we have at our hands.

We fix {anchorTerm a_var}`a` to be a function from {anchorTerm a_var}`ℕ` to the non-negative
real numbers {anchorTerm a_var}`NNReal`.
```anchor a_var
variable {a : ℕ → NNReal}
```

Now we can formulate the theorem in Lean as
```
theorem summability_equivalence (ha : ∀ n, a n ≠ 0) :
    List.TFAE [uniform_summability a, inverse_summability a, uniform_r_linear_convergence a] := by sorry
```
where `List.TFAE` stands for "the following are equivalent" and is just
pairwise equivalence between all members of the argument behind the scenes.
A benefit of the `List.TFAE` property is that there are accompanying
tactics that construct the pairwise equivalences if sufficiently
many implications between the statements are given.

The full proof to the statement is
```anchor uniform_of_uniform_r_linear
theorem summability_equivalence (ha : ∀ n, a n ≠ 0) :
    List.TFAE [uniform_summability a, inverse_summability a, uniform_r_linear_convergence a] := by {
  tfae_have 1 → 3 := uniform_r_linear_of_uniform
  tfae_have 3 → 1 := uniform_of_uniform_r_linear
  tfae_have 3 → 2 := inverse_of_uniform_r_linear ha
  tfae_have 2 → 3 := uniform_r_linear_of_inverse ha
  tfae_finish
}
```
where the referenced proofs are the implications 1.) $`⇔` 3.) and 2.) $`⇔` 3.).
This approach follows the proof in *AoA*.

# Proof

We will now prove the implication one after the other.

## Uniform Summability implies Uniform R-linear

We begin by showing an upper bound for the series $`\sum_{k=l+n}^{\infty} \quad a_{k}^{2}`
by induction. In precise terms we will show that the estimate
$$`
∀ l,n ∈ ℕ_0 : \sum_{k=l+n}^{\infty} a_{k}^{2} \leq\left(\frac{1}{1+C^{-1}}\right)^{n} \sum_{k=l}^{\infty} a_{k}^{2}
`
holds whenever uniform summability holds with a constant $`C`.

In Lean the respective lemma is
```lean
lemma uniform_recursive_bound {C:NNReal} (hC : C > 0) (hSum: Summable (a ^ 2))
      (hBound : ∀ (l : ℕ), ∑' (k : ℕ), (a ^ 2) (k + l + 1) ≤ C * (a ^ 2) l):
    ∀ l n, ∑' k, (a^2) (k + l + n) ≤ 1/(1+C⁻¹)^n *  ∑' k, (a^2) (k + l) := by sorry
```

We use induction on $`n`. In the case that $`n=0` the estimate is trivial. For the step
we calculate
$$`
\begin{aligned}
∑_{k=l+n+1}^∞ a_k^2 &= \frac{1}{1+C⁻¹} \left( ∑_{k=l+n+1}^∞ a_k^2 + C⁻¹ ∑_{k=l+n+1}^∞ a_k^2 \right) \\
&\stackrel{(*)}{≤} \frac{1}{1+C⁻¹} \left( ∑_{k=l+n+1}^∞ a_k^2 + C⁻¹ C a_{l+n}^2 \right) \\
&= \frac{1}{1+C⁻¹} \left( ∑_{k=l+n+1}^∞ a_k^2 + a_{l+n}^2 \right) \\
&= \frac{1}{1+C⁻¹} ∑_{k=l+n}^∞ a_k^2 \\
&\stackrel{(IH)}{≤} \frac{1}{1+C⁻¹} \left(\frac{1}{1+C⁻¹}\right)^n ∑_{k=l}^∞ a_k^2 \\
&= \left(\frac{1}{1+C⁻¹}\right)^{n+1} ∑_{k=l}^∞ a_k^2
\end{aligned}
`
which finishes the proof. In the line marked with the asterisk we used the assumption from
uniform convergence.

The proof translates very nicely to Lean as a chain of inqualities when
care is taken to make the steps small enough such that the automated
tactics `rel`, `field_simp`, `ring` etc. can find proofs on their own.
Finding out what the appropriate steps are takes
some time getting used to. The reader is encouraged to
step through the Lean proof and compare with the abriged version above.

```anchor uniform_recursive_bound
lemma uniform_recursive_bound {C:NNReal} (hC : C > 0) (hSum: Summable (a ^ 2))
      (hBound : ∀ (l : ℕ), ∑' (k : ℕ), (a ^ 2) (k + l + 1) ≤ C * (a ^ 2) l):
    ∀ l n, ∑' k, (a^2) (k + l + n) ≤ 1/(1+C⁻¹)^n *  ∑' k, (a^2) (k + l) := by {
  intros l n
  induction' n with n ih
  · simp

  calc ∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))
    _ = 1/(1+C⁻¹) * (1+C⁻¹) * ∑' (k : ℕ), (a ^ 2) (k + l + (n + 1)) := by field_simp
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))
        + C⁻¹ * ∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))) := by ring
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))
        + C⁻¹ * ∑' (k : ℕ), (a ^ 2) (k + (l + n) + 1)) := by simp [add_assoc]
    _ ≤ 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))
        + C⁻¹ * (C * (a^2) (l+n))) := by rel [hBound (l+n)]
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + (n + 1)) + (a^2) (l+n)) := by field_simp
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + (l + n) + 1) + (a^2) (l+n)) := by simp [add_assoc]
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + (l + n))) := by {
      nth_rw 2 [NNReal.sum_add_tsum_nat_add 1]
      · simp [← add_assoc]
        nth_rw 3 [add_comm]
        congr with x
        congr 3
        ring
      · exact (NNReal.summable_nat_add_iff (l + n)).mpr hSum
    }
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + n)) := by simp [add_assoc]
    _ ≤ 1/(1+C⁻¹) * (1 / (1 + C⁻¹) ^ n * ∑' (k : ℕ), (a ^ 2) (k + l)) := by rel [ih]
    _ = 1/(1+C⁻¹) * (1 / (1 + C⁻¹) ^ n) * ∑' (k : ℕ), (a ^ 2) (k + l) := by ring
    _ = 1/((1+C⁻¹) * (1 + C⁻¹)^n) * ∑' (k : ℕ), (a ^ 2) (k + l) := by field_simp
    _ = 1/(1 + C⁻¹)^(n+1) * ∑' (k : ℕ), (a ^ 2) (k + l) := by rw [pow_succ' (1 + C⁻¹)]
}
```

Now we can show uniform R-linear convergence with $`ρ_1 = 1/(1+C⁻¹)` and $`C_3 = 1+C`.
The main argument is another calculation:

$$`
\begin{aligned}
a_{l+k}^2 &≤ ∑_{j=l+k}^∞ a_j^2 \\
&≤ \left(\frac{1}{1+C⁻¹}\right)^k ∑_{j=l}^∞ a_j^2 \\
&= \left(\frac{1}{1+C⁻¹}\right)^k \left(∑_{j=l+1}^∞ a_j^2 + a_l^2\right) \\
&\stackrel{(*)}{≤} \left(\frac{1}{1+C⁻¹}\right)^k (C a_l^2 + a_l^2) \\
&= (C+1) \left(\frac{1}{1+C⁻¹}\right)^k a_l^2
\end{aligned}
`

The Lean version follows exactly this idea, but the additional precision
we need to have is very visible:
```anchor uniform_r_linear_of_uniform
lemma uniform_r_linear_of_uniform (h : uniform_summability a) :
    uniform_r_linear_convergence a := by {
  rcases h with ⟨hSum, C, hC, hBound⟩

  use 1/(1+C⁻¹)
  constructor
  have h₁ : 1 < 1 + C⁻¹ := by simp [Right.inv_pos.mpr hC]
  · constructor
    · simp [one_div, inv_pos, h₁]
    · simp only [one_div]
      exact inv_lt_one_of_one_lt₀ h₁

  use (1+C)
  constructor
  · simp [hC]

  intros k l
  let g := fun j ↦ (a^2) (j + l + k)
  calc (a ^ 2) (l + k)
    _ = g 0 := by unfold g; simp only [Pi.pow_apply, zero_add]
    _ ≤ ∑' j, (a^2) (j + l + k) := by {
      apply Summable.le_tsum
      · unfold g
        simp only [add_assoc]
        apply NNReal.summable_nat_add _ hSum (l+k)
      · simp
    }
    _ ≤ 1/(1 + C⁻¹)^k * ∑' (j : ℕ), (a ^ 2) (j + l) := by apply uniform_recursive_bound hC hSum hBound l k
    _ = 1/(1 + C⁻¹)^k * (∑' (j : ℕ), (a ^ 2) (j + l + 1) + (a ^ 2) l) := by {
      rw [NNReal.sum_add_tsum_nat_add 1]
      simp [← add_assoc, add_comm]
      apply NNReal.summable_nat_add _ hSum l
    }
    _ ≤ 1/(1 + C⁻¹)^k * (C * (a ^ 2) l + (a ^ 2) l) := by rel [hBound l]
    _ = (1 + C) * (1/(1 + C⁻¹))^k * (a ^ 2) l := by rw [← NNReal.coe_inj]; push_cast; ring
}
```
First, we give the constants and justify that they are within their respective bounds.
Afterwards the proof is a `calc`-block that follows the mathematical proof.
Defining the function `g` seems extraneous at first glance, but is an effective
trick here to make Lean apply {anchorTerm uniform_r_linear_of_uniform}`Summable.le_tsum`
correctly.
Note that this is the proof where the summability assumption
for $`(a_n)` is essential to use. We need it to use mathlib theorems
about series that are not true for divergent sums (which are equal to $`0`).
Estimating one summand with the whole series and splitting of one summand
is where we needed a summability proof.

## Uniform R-linear implies Uniform Summability

This direction essentially uses the convergence of the geometric series.
From that we can derive a uniform upper bound on partial sums of the series
we are concerned with. Then the uniform summability follows easily from this
bound. We will present the Lean proof interlaced with mathematical explanations.

We start by establishing the assumptions and constants from uniform R-linear convergence
```anchor uniform_of_uniform_r_linear_1
lemma uniform_of_uniform_r_linear (h : uniform_r_linear_convergence a) :
    uniform_summability a := by {
  rcases h with ⟨q,hq,C,hC,h⟩
```
Then we prove for all $`l,n∈ℕ` the bound
$$`
\begin{aligned}
∑_{k=0}^{n-1} a_{k+l+1}^2 &≤ ∑_{k=0}^{n-1} C q^{k+1} a_l^2 \\
&= C q a_l^2 ∑_{k=0}^{n-1} q^k \\
&≤ C q a_l^2 ∑_{k=0}^{∞} q^k \\
&= C q a_l^2 (1-q)⁻¹
\end{aligned}
`
using exactly this calculation in a `have`-block:
```anchor uniform_of_uniform_r_linear_2
  have : ∀ l n, ∑ k ∈ range n, (a^2) (k + l + 1) ≤ C * q * (1 - q)⁻¹ * (a^2) l := by {
    intros l n
    calc ∑ k ∈ range n, (a^2) (k + l + 1)
      _ ≤ ∑ k ∈ range n, C * q^(k + 1) * (a^2) l := by {
        gcongr with k
        specialize h (k + 1) l
        rw [← add_assoc, add_comm l k] at h
        assumption
      }
      _ = ∑ k ∈ range n, (C * q * (a^2) l) * q^k := by congr with _; ring_nf
      _ = C * q * (a^2) l * ∑ k ∈ range n, q^k := by rw [← mul_sum]
      _ ≤ C * q * (a^2) l * ∑' k, q^k := by {
        gcongr

        apply Summable.sum_le_tsum
        · intros i hi
          exact pow_nonneg (le_of_lt hq.1) i

        exact NNReal.summable_coe.mp <| summable_geometric_of_lt_one (le_of_lt hq.1) hq.2
      }
      _ = C * q * (a^2) l * (1 - q)⁻¹ := by {
        congr
        rw [← NNReal.coe_inj]
        push_cast [le_of_lt hq.2]
        exact tsum_geometric_of_lt_one (le_of_lt hq.1) hq.2
      }
      _ = C * q * (1 - q)⁻¹ * (a^2) l := by ring
  }
```
In the first inquality we use uniform R-linear convergence and in
the second one the convergence of the geometric series because $`q<1`.

Now we can prove uniform summability, which means we have to
show that $`(a_n)` is summable and the bound
$$`
∑_{k=l+1}^∞ η(𝒯_k; U(𝒯_k))² ≤ C_3 η(𝒯_l; U(𝒯_l))².
`

We start with the bound, this follows directly from
our uniform bound by taking the limit (with `NNReal.tsum_le_of_sum_range_le`
mathlib theorem)
and choosing
$`C \coloneqq C q (1-q)⁻¹`. Of course we need to
prove that this constant is greater than zero. In Lean we
have
```anchor uniform_of_uniform_r_linear_3
  constructor
  swap
  · use C * q * (1-q)⁻¹
    constructor
    · apply mul_pos
      exact mul_pos hC hq.1
      apply Right.inv_pos.mpr
      exact tsub_pos_of_lt hq.2

    intros l
    apply NNReal.tsum_le_of_sum_range_le (this l)
```
where the `constructor` and `swap` tactics set us
up to show the bound first and then summability.

So what remains is that $`(a_n)` is actually summable.
This follows from our uniform partial sum bound by
setting $`l=0`. By calculating
$$`
\begin{aligned}
∑_{k=0}^{n-1} a_k^2 &≤ ∑_{k=0}^n a_k^2 \\
&= ∑_{k=0}^{n-1} a_{k+1}^2 + a_0^2 \\
&≤ C q (1-q)⁻¹ a_0^2 + a_0^2
\end{aligned}
`
we gain a constant bound for the partial sum which means
that $`(a_n)` must be summable. This transfers to Lean as
```anchor uniform_of_uniform_r_linear_4
  · apply NNReal.summable_of_sum_range_le

    intros n
    calc ∑ i ∈ range n, (a ^ 2) i
      _ ≤ ∑ i ∈ range (n+1), (a ^ 2) i := by {
        apply sum_le_sum_of_subset_of_nonneg (range_subset.mpr (by simp)) ?_
        · intros
          apply sq_nonneg
      }
      _ = ∑ i ∈ range n, (a ^ 2) (i + 1) + (a ^ 2) 0 := by simp [Finset.sum_range_succ']
      _ ≤ C * q * (1 - q)⁻¹ * (a ^ 2) 0 + (a ^ 2) 0 := by rel [this 0 n]
```
which concludes the proof.
