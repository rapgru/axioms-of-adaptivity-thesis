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

The wording "for all sufficiently small" hides the dependency
of the "constants" $`ρ_est` and $`C_est` on $`δ`. For the formalized version we
define these values as functions of $`δ` and show the estimator
reduction property for all $`δ` such that $`ρ_{est}(δ) < 1`.

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

# Proof

First we show a lemma about the Dörfler estimate for
the elements that have been refined:

> *Lemma (Dörfler for refined elements)*: For all $`l ∈ ℕ_0` we have the
  estimate
  $$`
  θ η^2(𝒯_{l}, U(𝒯_{l})) ≤ \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_{t}^2(𝒯_{l}, U(𝒯_{l}))
  `

The proof is straightforward, it follows from the Dörfler property,
$`ℳ_l ⊆ 𝒯_l \setminus 𝒯_{l+1}` and that a sum does not increase when
we add non-negative summands.

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

Other lemmas that our proof is going to use are
```
lemma square_estimate_of_small_distance {a b c : ℝ} (ha : 0 ≤ a) (h : |a-b| ≤ c) :
  a^2 ≤ (b+c)^2 := by <...>

lemma sum_square_le_square_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ δ > 0, (a+b)^2 ≤ (1+δ)*a^2 + (1+δ⁻¹)*b^2 := by <...>
```
We will skip the proofs, they can be found in the Lean repository.

For the main proof of lemma 4.7,
we begin by introducing {anchorTerm estimator_reduction_1}`δ` and
{anchorTerm estimator_reduction_1}`l` along with the assumptions
that `δ > 0` and `alg.ρ_est δ < 1`. Also we define abbreviations for
longer terms that appear in the proof.

```anchor estimator_reduction_1
  intros δ hδ hρ_est l

  let summand n t := alg.η (alg.𝒯 n) (alg.U <| alg.𝒯 <| n) t ^ 2
  let distance n := alg.d (alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n) ^ 2
```

Then the estimate can be shown in one long chain of equalities and estimates,
starting from $`η^2(𝒯_{l+1}, U(𝒯_{l+1}))`, where every step has a Lean proof
of reasonable size. We use a calc block in Lean to implement this chain.

We start with
$$`
\begin{aligned}
& η^2(𝒯_{l+1}, U(𝒯_{l+1})) \\
&= \sum_{t \in 𝒯_{l+1} \setminus 𝒯_l} η_t^2(𝒯_{l+1}, U(𝒯_{l+1})) + \sum_{t \in 𝒯_l \cap 𝒯_{l+1}} η_t^2(𝒯_{l+1}, U(𝒯_{l+1}))
\end{aligned}
`
by the definition of the global error and basic set identities.

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

$$`
\begin{aligned}
&\le ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) + C_{red} 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&\quad + \sum_{t \in 𝒯_l \cap 𝒯_{l+1}} η_t^2(𝒯_{l+1}, U(𝒯_{l+1}))
\end{aligned}
`
by an application of axiom A2.

```anchor estimator_reduction_3
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t
        + alg.C_red * distance l
        + (∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand (l + 1) t) := by
      rel[alg.a2 (alg.𝒯 l) (alg.𝒯 <| l + 1) (alg.h𝒯 l)]
```

$$`
\begin{aligned}
&\le ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) + C_{red} 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&\quad + (1+δ) \sum_{t \in 𝒯_l \cap 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) + (1+δ⁻¹) C_{stab}^2 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2
\end{aligned}
`

by a combination of A1 and the generalized young inequality.

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
      change ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand (l + 1) t ≤ (1 + δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand l t + (1 + δ⁻¹) * (alg.C_stab ^ 2 * distance l) at this
      rel [this]
      all_goals apply_rules [sum_nonneg', fun _ ↦ sq_nonneg _]
    }
```

$$`
\begin{aligned}
&= ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) + (1+δ) \sum_{t \in 𝒯_l \cap 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) \\
&\quad + (C_{red} + (1+δ⁻¹) C_{stab}^2) 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2
\end{aligned}
`
by basic algebra, which Lean can prove on its own:

```anchor estimator_reduction_5
    _ = alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t
        + (1+δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l+1), summand l t
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
```

$$`
\begin{aligned}
&= ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l)) \\
&\quad + (1+δ) \left(η^2(𝒯_l, U(𝒯_l)) - \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l))\right)
\end{aligned}
`
by definition of the global error $`η^2` and basic set identities,

```anchor estimator_reduction_6
    _ = alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t
        + (1+δ) * (gη2_seq alg l -  ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t)
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      congr
      have h_eq : (alg.𝒯 l).val = (↑(alg.𝒯 l) \ ↑(alg.𝒯 (l + 1))) ∪ (↑(alg.𝒯 l) ∩ ↑(alg.𝒯 (l+1))) := by exact Eq.symm (sdiff_union_inter _ _)
      have h_dis: @Disjoint (Finset α) Finset.partialOrder Finset.instOrderBot (alg.𝒯 l \ alg.𝒯 (l + 1)) (alg.𝒯 l ∩ alg.𝒯 (l+1)) := by {
        exact disjoint_sdiff_inter _ _
      }
      unfold gη2_seq gη2
      nth_rw 2 [h_eq]
      rw [sum_union (disjoint_sdiff_inter _  _)]
      ring
    }
```

$$`
\begin{aligned}
&\quad + (C_{red} + (1+δ⁻¹) C_{stab}^2) 𝕕[𝒯_{l+1}, U(𝒯_{l+1}), U(𝒯_l)]^2 \\
&\le (1+δ) ρ_{red} \sum_{t \in 𝒯_l \setminus 𝒯_{l+1}} η_t^2(𝒯_l, U(𝒯_l))
\end{aligned}
`

because $`δ > 0`.

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

by basic algebra and the Doerfler marking for refined elements lemma.

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
