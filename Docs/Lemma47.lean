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

#doc (Manual) "Estimator Reduction" =>
%%%
htmlSplit := .never
tag := "estimator_reduction"
%%%

This chapter formalizes the proof of Lemma 4.7 from *AoA* which reads as

> *Lemma 4.7*: Stability (A1) and Reduction (A2) imply the estimator reduction
  $$`η(𝓣_{ℓ+1}; U(𝓣_{ℓ+1}))² ≤ ρ_{est} η(𝓣_ℓ; U(𝓣_ℓ))² + C_{est} 𝕕[𝓣_{ℓ+1}; U(𝓣_{ℓ+1}), U(𝓣_ℓ)]²`
  for all $`ℓ ∈ ℕ_0` with the constants $`0 < ρ_{est} < 1` and $`C_{est} > 0` which
  relate via
  $$`ρ_{est} = (1 + δ)(1 - (1 - ρ_{red})θ) \quad \text{and} \quad C_{est} = C_{red} + (1 + δ⁻¹)C_{stab}²`
  for all sufficiently small $`δ` such that $`ρ_{est} < 1`.

All the Lean code in this chapter is inside the `AdaptiveAlgorithm` namespace
so all definitions and theorems can be accessed on an instance of the
structure `AdaptiveAlgorithm` via dot notation. Also globally we introduce
the variable
```anchor alg
variable (alg : AdaptiveAlgorithm α β)
include alg
```

# Formal Statement
%%%
tag := "lemma47_formal_statement"
%%%

The wording "for all sufficiently small" hides the dependency
of the "constants" $`ρ_est` and $`C_est` on $`δ`. For the formalized version we
define these values as functions of $`δ` and show the estimator
reduction property for all $`δ > 0` such that $`ρ_{est}(δ) < 1`.

We define the functions `ρ_est` and `C_est` as
```anchor lemma47_consts
def ρ_est δ := (1+δ) * (1 - (1 - alg.ρ_red) * alg.θ)
noncomputable def C_est δ := alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2
```

Then, the statement we want to prove is
```
∀ δ > 0, (alg.ρ_est δ < 1) →
  ∀ l,
    alg.gη2_seq (l + 1)
    ≤ alg.ρ_est δ * alg.gη2_seq l
      + alg.C_est δ * alg.d (alg.𝒯 <| l + 1) (alg.U <| alg.𝒯 <| l+1) (alg.U <| alg.𝒯 <| l) ^ 2
```

# Utility lemmas

Before starting on the actual proof,
we show a few utility lemmata.

## Dörfler for refined elements

The first one is a Dörfler-type estimate for
the only the elements that have been refined:

> *Lemma (Dörfler for refined elements)*: For all $`l ∈ ℕ_0` we have the
  estimate
  $$`
  θ η^2(𝒯_{l}, U(𝒯_{l})) ≤ \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_{t}^2(𝒯_{l}, U(𝒯_{l}))
  `

The proof is straightforward, it follows from the Dörfler property,
$`ℳ_l ⊆ 𝒯_l \setminus 𝒯_{l+1}` and that a sum does not increase when
we add non-negative summands. In Lean the proof reads as
```anchor doerfler_for_refined_elements
lemma doerfler_for_refined_elements :
    ∀ l, alg.θ * gη2_seq alg l
      ≤ ∑ t ∈ (alg.𝒯 l \ alg.𝒯 (l+1)), alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by {
  intros l
  calc alg.θ * gη2_seq alg l
    _ ≤ ∑ t ∈ alg.ℳ l, alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by exact (alg.hℳ l).2.1
    _ ≤ ∑ t ∈ (alg.𝒯 l \ alg.𝒯 (l+1)), alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by {
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact (alg.hℳ l).1
      · exact fun _ _ _ ↦ sq_nonneg _
    }
}
```

## Estimate on Square of a Sum
Another purely analytical utility lemmas we are going to use is

> *Lemma (Square of Sum Estimate)*: For $`a,b ≥ 0` and $`δ > 0`
   $$`
   (a+b)^2 ≤ (1+δ)a^2 + (1+δ⁻¹)b^2
   `
   holds

To show this we first need a generalized Young inequality

> *Lemma (Generalized Young inequality)*: For $`a,b ≥ 0`, $`δ > 0` and a Hölder-conjugate pair
  $`p,q` (meaning $`\frac1p = \frac1q`) the inequality
  $$`
  ab ≤ \frac{δ}{p} a^p + \frac{1}{q δ^(\frac{q}{p})} b^q
  ` holds.

We first prove the Young-type inequality by estimating
$$`
\begin{aligned}
ab &= ab (δ^{1/p} δ^{-1/p}) \\
&= (a δ^{1/p}) (b δ^{-1/p}) \\
&≤ \frac{(a δ^{1/p})^p}{p} + \frac{(b δ^{-1/p})^q}{q} \\
&= \frac{δ}{p} a^p + \frac{1}{q δ^{q/p}} b^q
\end{aligned}
`
where we have used the regular Young inequality in step three.
This proof carries over to Lean using a `calc`-block:

```
lemma young_with_delta {a b δ p q : ℝ} (ha : 0 ≤ a)  (hb : 0 ≤ b) (hδ : 0 < δ) (hpq : p.HolderConjugate q): a*b ≤ δ/p * a^p + 1/(q*δ^(q/p)) * b^q := by {
  have hδ₂ := le_of_lt hδ
  have hpow_nonneg := Real.rpow_nonneg hδ₂

  calc a*b
    _ = a * b * (δ ^ p⁻¹ * (δ ^ p⁻¹)⁻¹) := by field_simp
    _ = a * δ ^ (1 / p) * (b * 1 / δ ^ (1 / p)) := by ring_nf
    _ ≤ (a * δ ^ (1 / p)) ^ p / p + (b * 1 / δ ^ (1 / p)) ^ q / q := by {
      apply Real.young_inequality_of_nonneg _ _ hpq
      · exact mul_nonneg ha (hpow_nonneg _)
      · apply mul_nonneg <;> simp [hb, ha, hpow_nonneg]
    }
    _ = δ/p * a^p + (b * 1 / δ ^ (1 / p)) ^ q / q := by {
      rw [Real.mul_rpow ha <| hpow_nonneg _, ←Real.rpow_mul hδ₂]
      simp [inv_mul_cancel₀ <| Real.HolderTriple.ne_zero hpq, mul_comm]
      ring
    }
    _ = δ/p * a^p + 1/(q*δ^(q/p)) * b^q := by {
      field_simp
      rw [Real.div_rpow hb <| hpow_nonneg _, ←Real.rpow_mul hδ₂]
      ring_nf
    }
}
```

Now we can show the estimate on the square of a sum again by
doing a calculation involving the generalized Young equation
with $`p=q=\frac12`.
$$`
\begin{aligned}
(a+b)^2 &= a^2 + 2ab + b^2 \\
&≤ a^2 + 2 (\frac{δ}{2} a^2 + \frac{1}{2δ} b^2) + b^2 \\
&= (1+δ)a^2 + (1+δ⁻¹)b^2
\end{aligned}
`

This is also straightforward to show this way in Lean
```
lemma sum_square_le_square_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ δ > 0, (a+b)^2 ≤ (1+δ)*a^2 + (1+δ⁻¹)*b^2 := by {
  intros δ hδ
  have := young_with_delta ha hb hδ Real.HolderConjugate.two_two
  calc (a + b) ^ 2
    _ = a^2 + 2*(a*b) + b^2 := by ring
    _ ≤ a^2 + 2*(δ/2 * a^2 + 1/(2*δ) * b^2) + b^2 := by simpa using this
    _ = (1+δ)*a^2 + (1+δ⁻¹)*b^2 := by ring
}
```

## Distance Estimate

The last utility lemma we will show is that for $`a,b,c ∈ ℝ`, $`a ≥ 0` the
condition $`|a-b| ≤ c` implies $`a^2 ≤ (b+c)^2`.

To show this we note that the condition especially implies $`a-b ≤ c`,
which means $`a ≤ b + c` by adding $`b`. Because by assumption $`a ≥ 0`
and we can take the square and arrive at the desired result. The Lean version
of this proof is
```
lemma square_estimate_of_small_distance {a b c : ℝ} (ha : 0 ≤ a) (h : |a-b| ≤ c) :
  a^2 ≤ (b+c)^2 := by {
  have : a - b ≤ c := le_of_max_le_left h
  have : a ≤ b + c := tsub_le_iff_left.mp this
  exact pow_le_pow_left₀ ha this 2
}
```

# Proof of Estimator Reduction

For the main proof of lemma 4.7,
we begin by introducing {anchorTerm estimator_reduction_1}`δ` and
{anchorTerm estimator_reduction_1}`l` along with the assumptions
that `δ > 0` and `alg.ρ_est δ < 1`. We also define abbreviations for
terms that appear in the proof and are lenghty to write.

```anchor estimator_reduction_1
theorem estimator_reduction : ∀ δ > 0, (alg.ρ_est δ < 1) →
    ∀ l, alg.gη2_seq (l + 1)
         ≤ alg.ρ_est δ * alg.gη2_seq l
           + alg.C_est δ * alg.d (alg.𝒯 <| l + 1) (alg.U <| alg.𝒯 <| l+1) (alg.U <| alg.𝒯 <| l) ^ 2 := by {
  intros δ hδ hρ_est l

  let summand n t := alg.η (alg.𝒯 n) (alg.U <| alg.𝒯 <| n) t ^ 2
  let distance n := alg.d (alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n) ^ 2
```

Then the estimate can be shown in one long chain of equalities and estimates,
starting from $`η^2(𝒯_{l+1}, U(𝒯_{l+1}))`, where every step has a Lean proof
of reasonable size. We will present the Lean proof interlaced with the mathematical
explanation of the current calculation step.

We start with
$$`
\begin{aligned}
& η^2(𝒯_{l+1}, U(𝒯_{l+1})) \\
&= \sum_{t \in 𝒯_{l+1} \setminus 𝒯_l} η_t^2(𝒯_{l+1}, U(𝒯_{l+1})) + \sum_{t \in 𝒯_l \cap 𝒯_{l+1}} η_t^2(𝒯_{l+1}, U(𝒯_{l+1}))
\end{aligned}
`
which hold by the definition of the global error and basic set identities. In Lean
we essentially use the {anchorTerm estimator_reduction_2}`sum_union` theorem from
mathlib:

```anchor estimator_reduction_2
  calc gη2_seq alg (l + 1)
    _ = ∑ t ∈ alg.𝒯 (l + 1) \ alg.𝒯 l, summand (l+1) t
        + ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l+1), summand (l+1) t := by {
      unfold gη2_seq gη2
      have h_eq : (alg.𝒯 (l + 1)).val = (↑(alg.𝒯 (l + 1)) \ ↑(alg.𝒯 l)) ∪ (↑(alg.𝒯 (l + 1)) ∩ ↑(alg.𝒯 l)) := by {
        exact Eq.symm (sdiff_union_inter _ _)
      }
      nth_rw 1 [h_eq]
      simp [sum_union (disjoint_sdiff_inter _ _)]
      nth_rw 1 [inter_comm]
    }
```

Next, we apply the reduction property on refined elements (A2) to reach

$$`
\begin{aligned}
&\le ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) + C_{red} 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&\quad + \sum_{t \in 𝒯_l \cap 𝒯_{l+1}} η_t^2(𝒯_{l+1}, U(𝒯_{l+1})).
\end{aligned}
`

In Lean we can see that this is really a direct application of the axiom:
```anchor estimator_reduction_3
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t
        + alg.C_red * distance l
        + (∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand (l + 1) t) := by
      rel[alg.a2 (alg.𝒯 l) (alg.𝒯 <| l + 1) (alg.h𝒯 l)]
```
We use the advanced tactic `rel` here which can automatically find
proofs for inqualities when a nested term is estimated. Often, it finds
proofs for non-negativity on its own, which is necessary for upper bounds
on products. E.g. when we have `h : a ≤ b` and successfully show `C*a ≤ C*b` using
`rel [h]` then the tactic had to account for the non-negativity of C.

Now, in one step we can estimate

$$`
\begin{aligned}
&\le ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) + C_{red} 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&\quad + (1+δ) \sum_{t \in 𝒯_l \cap 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) + (1+δ⁻¹) C_{stab}^2 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2
\end{aligned}
`
by combining stability on non-refined element domains (A1) and the
two utility lemmas from above. The Lean proof for this step reads as

```anchor estimator_reduction_4
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t
        + alg.C_red * distance l
        + ((1 + δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand l t
        + (1 + δ⁻¹) * (alg.C_stab ^ 2 * distance l)) := by {
      have := alg.a1
        (alg.𝒯 l)
        (alg.𝒯 <| l + 1)
        (alg.h𝒯 l)
        (alg.𝒯 l ∩ alg.𝒯 (l + 1))
        (fun _ a ↦ a)
        (alg.U <| alg.𝒯 <| l)
        (alg.U <| alg.𝒯 <| l + 1)
      have := square_estimate_of_small_distance (Real.sqrt_nonneg _) this
      have h₁ : 0 ≤ alg.C_stab * alg.d (alg.𝒯 (l + 1)) (alg.U (alg.𝒯 (l + 1))) (alg.U (alg.𝒯 l)) := by {
        apply mul_nonneg (le_of_lt alg.hC_stab)
        apply alg.non_neg
      }
      have := le_trans this <| sum_square_le_square_sum (Real.sqrt_nonneg _) h₁ δ hδ

      rw [Real.sq_sqrt, Real.sq_sqrt, mul_pow] at this
      · change ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand (l + 1) t
          ≤ (1 + δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand l t
          + (1 + δ⁻¹) * (alg.C_stab ^ 2 * distance l) at this
        rel [this]
      all_goals apply_rules [sum_nonneg', fun _ ↦ sq_nonneg _]
    }
```
Here we use the `change` tactic in order to switch to an equivalent type for hypotheses
{anchorTerm estimator_reduction_4}`this` in order for the `rel` tactic to suceed in
closing one of the three goals.

Then we rewrite
$$`
\begin{aligned}
&= ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) + (1+δ) \sum_{t \in 𝒯_l \cap 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) \\
&\quad + (C_{red} + (1+δ⁻¹) C_{stab}^2) 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2
\end{aligned}
`
by basic algebra. Lean can prove this on its own using the `ring` tactic:

```anchor estimator_reduction_5
    _ = alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t
        + (1+δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l+1), summand l t
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
```

Next, by definition of the global error $`η^2` and basic set identities
$$`
\begin{aligned}
&= ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) \\
&\quad + (1+δ) \left(η^2(𝒯_l, U(𝒯_l)) - \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l))\right).
\end{aligned}
`

The Lean proof is similar to the first step we did:
```anchor estimator_reduction_6
    _ = alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t
        + (1+δ) * (gη2_seq alg l -  ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t)
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      congr
      have h_eq : (alg.𝒯 l).val = (↑(alg.𝒯 l) \ ↑(alg.𝒯 (l + 1))) ∪ (↑(alg.𝒯 l) ∩ ↑(alg.𝒯 (l+1))) := by exact Eq.symm (sdiff_union_inter _ _)
      have h_dis: Disjoint ((alg.𝒯 l : Finset α) \ alg.𝒯 (l + 1)) (alg.𝒯 l ∩ alg.𝒯 (l+1)) := by {
        exact disjoint_sdiff_inter _ _
      }
      unfold gη2_seq gη2
      nth_rw 2 [h_eq]
      rw [sum_union (disjoint_sdiff_inter _  _)]
      ring
    }
```
The essential tool here
is {anchorTerm estimator_reduction_6}`sum_union` from mathlib. Also
note the use of the `gcongr` tactic which can simplify congruences in
proof goals. It has the same capabilities as `rel` but does not
try to close a goal. Given the current goal is an inequality,
it rather tries to find as much common terms on both sides as possible
and leaves the inequality between the terms that differ open as a new goal, filling
in the proof to go from the simpler inequality to the original goal on its own.

Now, because $`δ > 0` we have
$$`
\begin{aligned}
&\quad + (C_{red} + (1+δ⁻¹) C_{stab}^2) 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&\le (1+δ) ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)).
\end{aligned}
`

This is done rather easily in Lean using `gcongr` again:
```anchor estimator_reduction_7
    _ ≤ (1+δ) * alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t
        + (1+δ) * (gη2_seq alg l - ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t)
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      gcongr
      refine (le_mul_iff_one_le_left ?_).mpr ?_
      · exact alg.hρ_red.1
      · linarith
    }
```

The last steps are basic algebra and one application of the
Doerfler marking for refined elements lemma.
$$`
\begin{aligned}
&\quad + (1+δ) \left(η^2(𝒯_l, U(𝒯_l)) - \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l))\right) \\
&\quad + (C_{red} + (1+δ⁻¹) C_{stab}^2) 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&= (1+δ) \left(η^2(𝒯_l, U(𝒯_l)) - (1 - ρ_{red}) \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l))\right) \\
&\quad + (C_{red} + (1+δ⁻¹) C_{stab}^2) 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&\le (1+δ) (η^2(𝒯_l, U(𝒯_l)) - (1 - ρ_{red}) θ η^2(𝒯_l, U(𝒯_l))) \\
&\quad + (C_{red} + (1+δ⁻¹) C_{stab}^2) 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&= (1+δ) (1 - (1 - ρ_{red}) θ) η^2(𝒯_l, U(𝒯_l)) \\
&\quad + (C_{red} + (1+δ⁻¹) C_{stab}^2) 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2
\end{aligned}
`
This finished the proof as we have arrived at the upper bound we wanted to have.

It carries over to Lean very nicely:
```anchor estimator_reduction_8
    _ = (1+δ) * (gη2_seq alg l - (1-alg.ρ_red) * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t)
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
    _ ≤ (1+δ) * (gη2_seq alg l - (1-alg.ρ_red) * (alg.θ * gη2_seq alg l))
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      have h₁ : 0 ≤ 1 - alg.ρ_red := sub_nonneg_of_le <| le_of_lt alg.hρ_red.2
      rel[alg.doerfler_for_refined_elements l, h₁]
    }
    _ = (1+δ) * (1 - (1-alg.ρ_red) * alg.θ) * gη2_seq alg l
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
```
Now all Lean goals are closed and the theorem is proven.
