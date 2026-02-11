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

#doc (Manual) "Summability of Estimator" =>
%%%
htmlSplit := .never
%%%

This chapter formalizes the proof of Proposition 4.10 from *AoA* which reads as

> *Proposition 4.10*: Assuming estimator reduction
  $$`
  η(\mathcal{T}_{l+1}; U(\mathcal{T}_{l+1}))² ≤ ρ_{est} η(\mathcal{T}_l; U(\mathcal{T}_l))² + C_{est} 𝕕[\mathcal{T}_{l+1}; U(\mathcal{T}_{l+1}), U(\mathcal{T}_l)]².
  `
  and reliability, general quasi-orthogonality (A3) implies the summability statements
  1. _Uniform summability_: There exists a constant $`C_3 > 0` such that
      $$`∑_{k=l+1}^∞ η(\mathcal{T}_k; U(\mathcal{T}_k))² ≤ C_3 η(\mathcal{T}_l; U(\mathcal{T}_l))² \quad \text{for all } l ∈ ℕ_0.`
  2. _Inverse summability_: For all $`s > 0`, there exists a constant $`C_4 > 0` such that
      $$`∑_{k=0}^{l-1} η(\mathcal{T}_k; U(\mathcal{T}_k))^{-1/s} ≤ C_4 η(\mathcal{T}_l; U(\mathcal{T}_l))^{-1/s} \quad \text{for all } l ∈ ℕ_0.`
  3. _Uniform R-linear convergence on any level_: There exist constants $`0 < ρ_1 < 1` and $`C_5 > 0` such that
      $$`η(\mathcal{T}_{l+k}; U(\mathcal{T}_{l+k}))² ≤ C_5 ρ_1^k η(\mathcal{T}_l; U(\mathcal{T}_l))² \quad \text{for all } k, l ∈ ℕ_0.`
  where all constants $`C_3`, $`C_4`, $`C_5`, $`ρ_1` only depend on $`ρ_{est}`, $`C_{est}`, $`C_{qo}(ε_{qo})`, $`s`.

From  {ref "summability_equivalence"}[Lemma 4.9] we already know that the summability
statements are equivalent, so to prove this proposition we only need to show one of them.

# Formal Statement

Using the definitions from {ref "lem47_formal_statement"}[Lemma 4.9] and the
`NNReal`, square-root version of $`η` from {ref "adaptive_alg_defs"}[the definitions in
the AdaptiveAlgorithm structure] we can simply formulate the proposition in Lean as

```
theorem summability : uniform_summability alg.nn_gη_seq := by sorry
```

# Proof

## Constants Lemma

In the main proof we will need to use a concrete value for
the $`δ` parameter of the estimator reduction constants.
Specifically we need $`δ > 0` such that
$$`ρ_{est}(δ) < 1`
and
$$`ε_{qo} < \frac{1-ρ_{est}(δ)}{C_{rel}^2 C_{est}(δ)}.`

Because
$$`
ε_{qo} < ε^*_{qo}(θ) \coloneqq \sup_{δ > 0} \frac{1-(1+δ)(1-(1-ρ_{red})θ)}{C_{rel}^2 (C_{red} + (1+δ⁻¹)C_{stab}^2)}
`
we can find a $`δ > 0` such that
$$`
ε_{qo} < \frac{1-(1+δ)(1-(1-ρ_{red})θ)}{C_{rel}^2 (C_{red} + (1+δ⁻¹)C_{stab}^2) ≤ ε^*_{qo}(θ).
`
It can be shown that this $`δ` in fact satisfies the properties we need.
Due to the way Lean internally defines suprema over the positive
reals it is highly technical and we will only cite the statement here.
The full proof can be found in the Lean source repository.

```
lemma ε_qo_lt_est_consts :
    ∃ δ > 0, alg.ε_qo < (1 - alg.ρ_est δ) / (alg.C_rel^2 * alg.C_est δ) ∧ alg.ρ_est δ < 1 := by sorry
```

## Cancel Lemma

A small and technical lemma that is used multiple times in the proof is
{anchorTerm cancel}`cancel`:
```anchor cancel
lemma cancel {δ a} (hδ : δ > 0) : a * (alg.C_rel^2 * alg.C_est δ / (alg.C_rel^2 * alg.C_est δ)) = a := by
  apply mul_right_eq_self₀.mpr
  left
  apply EuclideanDomain.div_self
  apply ne_of_gt
  exact alg.C_rel_mul_C_est_pos hδ
```

## Main Proof

We will present the proof in the interlaced format again as it is quite lenghty.
In the typeset versions we will also use the shifted sums that start from zero
because the proof steps are rather technical and alignment with
the Lean implementation is preferrable. Because the exact number of
summands is not very relevant, we write the sums up to an index $`n`.
Because lean sums over a range of natural numbers have an exclusive upper limit
the sums correspond with the Lean sums
Also, we define an analogon
to `gη2_seq` with $$`η^2_n \coloneqq η^2(\mathcal{T}_{n}, U(\mathcal{T}_{n}))`

We start the proof by taking a concrete $`δ > 0` such that
$`ρ_{est}(δ) < 1` (estimator reduction applies) and
$`ε_{qo} < \frac{1-ρ_{est}(δ)}{C_{rel}^2 C_{est}(δ)}` from the constants
lemma.
Then we define a new quantity
$$`v \coloneqq ε_{qo} C_{rel}^2 C_{est}(δ)`
which can easily be shown to satisfy $`0 ≤ v < 1 - ρ_{est}(δ)`
with our choice of $`δ`.

In Lean we do exactly that to start the proof
```anchor summability_1
theorem summability : uniform_summability alg.nn_gη_seq := by
  rcases alg.ε_qo_lt_est_consts with ⟨δ, hδ, hε_qo, hρ_est⟩
  -- TODO clean up the lt_est_consts lemma !!

  let v := alg.ε_qo * alg.C_rel^2 * alg.C_est δ
  have hv₁ : v < 1 - alg.ρ_est δ := calc
      _ = alg.ε_qo * alg.C_rel^2 * alg.C_est δ := by rfl
      _ < (1 - alg.ρ_est δ) / (alg.C_rel^2 * alg.C_est δ) * alg.C_rel^2 * alg.C_est δ := by
        gcongr
        · exact alg.C_est_pos hδ
        · exact pow_pos alg.hC_rel 2
      _ = (1 - alg.ρ_est δ) * (alg.C_rel^2 * alg.C_est δ / (alg.C_rel^2 * alg.C_est δ)) := by
        field_simp
        rw [mul_assoc]
      _ = 1 - alg.ρ_est δ := cancel alg hδ

  have hv₂ : 0 ≤ v := by
    simp [v, mul_assoc]
    apply Left.mul_nonneg alg.hε_qo.1
    exact le_of_lt <| alg.C_rel_mul_C_est_pos hδ

```

The first step is to show
$$`
\begin{aligned}
  ∑_{k=0}^n η^2_{k+l+1} &≤ ∑_{k=0}^n (ρ_{est}(δ) + v) η^2_{k+l} \\
  &\quad + C_{est}(δ) C_{qo} η^2_l
\end{aligned}
`
for all $`n,l ∈ ℕ`

This can be formulated in a calculation that is ideal for finding a
Lean proof:
$$`
\begin{aligned}
  ∑_{k=0}^n η^2_{k+l+1}
  &≤ ∑_{k=0}^n [ρ_{est}(δ) η^2_{k+l} + C_{est}(δ) 𝕕[\mathcal{T}_{k+l+1}; U(\mathcal{T}_{k+l+1}), U(\mathcal{T}_{k+l})]^2] \\
  &= ∑_{k=0}^n [(ρ_{est}(δ) + v) η^2_{k+l} + C_{est}(δ) (𝕕[\mathcal{T}_{k+l+1}; U(\mathcal{T}_{k+l+1}), U(\mathcal{T}_{k+l})]^2 - v C_{est}(δ)^{-1} η^2_{k+l})] \\
  &≤ ∑_{k=0}^n [(ρ_{est}(δ) + v) η^2_{k+l} + C_{est}(δ) (𝕕[\mathcal{T}_{k+l+1}; U(\mathcal{T}_{k+l+1}), U(\mathcal{T}_{k+l})]^2 - v C_{est}(δ)^{-1} (C_{rel}^{-1} 𝕕[\mathcal{T}_{k+l}; u, U(\mathcal{T}_{k+l})])^2)] \\
  &= ∑_{k=0}^n [(ρ_{est}(δ) + v) η^2_{k+l} + C_{est}(δ) (𝕕[\mathcal{T}_{k+l+1}; U(\mathcal{T}_{k+l+1}), U(\mathcal{T}_{k+l})]^2 - \frac{v}{C_{rel}^2 C_{est}(δ)} 𝕕[\mathcal{T}_{k+l}; u, U(\mathcal{T}_{k+l})]^2)] \\
  &= ∑_{k=0}^n [(ρ_{est}(δ) + v) η^2_{k+l} + C_{est}(δ) (𝕕[\mathcal{T}_{k+l+1}; U(\mathcal{T}_{k+l+1}), U(\mathcal{T}_{k+l})]^2 - ε_{qo} 𝕕[\mathcal{T}_{k+l}; u, U(\mathcal{T}_{k+l})]^2)] \\
  &= ∑_{k=0}^n (ρ_{est}(δ) + v) η^2_{k+l} + C_{est}(δ) ∑_{k=0}^n (𝕕[\mathcal{T}_{k+l+1}; U(\mathcal{T}_{k+l+1}), U(\mathcal{T}_{k+l})]^2 - ε_{qo} 𝕕[\mathcal{T}_{k+l}; u, U(\mathcal{T}_{k+l})]^2) \\
  &≤ ∑_{k=0}^n (ρ_{est}(δ) + v) η^2_{k+l} + C_{est}(δ) C_{qo} η^2_l
\end{aligned}
`

In the Lean proof we continue with this chain of reasoning:
```anchor summability_2
  have : ∀ N l:ℕ, ∑ k ∈ range N, alg.gη2_seq (k + l + 1)
      ≤ ∑ k ∈ range N, (alg.ρ_est δ + v) * alg.gη2_seq (k + l)
        + alg.C_est δ * alg.C_qo * alg.gη2_seq l := by {
    intros N l
    calc ∑ k ∈ range N, alg.gη2_seq (k + l + 1)
      _ ≤ ∑ k ∈ range N, (alg.ρ_est δ * alg.gη2_seq (k + l)
          + alg.C_est δ * d_seq alg (k + l)^2) := by
        gcongr with k hk
        exact alg.estimator_reduction δ hδ hρ_est (k+l)
      _ = ∑ k ∈ range N, (
            (alg.ρ_est δ + v) * alg.gη2_seq (k + l)
            + alg.C_est δ * (d_seq alg (k + l)^2
            - v * (alg.C_est δ)⁻¹ * alg.gη2_seq (k + l))
          ) := by
        congr
        funext k
        rw [add_mul, mul_sub]
        conv in _ - _ =>
          rhs
          rw [← mul_assoc]
          lhs
          tactic =>
            calc alg.C_est δ * (v * (alg.C_est δ)⁻¹)
              _ = (alg.C_est δ * (alg.C_est δ)⁻¹) * v := by ring
              _ = v := by rw [mul_inv_cancel₀ <| ne_of_gt <| alg.C_est_pos hδ, one_mul]

        ring
      _ ≤ ∑ k ∈ range N, (
            (alg.ρ_est δ + v) * alg.gη2_seq (k + l)
            + alg.C_est δ * (
              d_seq alg (k + l)^2
              - v * (alg.C_est δ)⁻¹ * (alg.C_rel⁻¹ * alg.d (alg.𝒯 <| k + l) alg.u (alg.U <| alg.𝒯 <| k + l))^2
            )
          ) := by
        gcongr with k hk
        · exact le_of_lt <| alg.C_est_pos hδ
        · refine mul_nonneg hv₂ ?_
          exact inv_nonneg.mpr <| le_of_lt <| alg.C_est_pos hδ
        · rw [mul_pow]
          calc alg.C_rel⁻¹ ^ 2 * alg.d (alg.𝒯 (k + l)) alg.u (alg.U (alg.𝒯 (k + l))) ^ 2
            _ ≤ alg.C_rel⁻¹ ^ 2 * (alg.C_rel ^ 2 * alg.gη2_seq (k + l)) := by {
              have := (sq_le_sq₀ (alg.non_neg _ _ _) ?_).mpr (alg.reliability <| alg.𝒯 <| k + l)
              swap
              · apply mul_nonneg
                · exact le_of_lt <| alg.hC_rel
                · apply Real.sqrt_nonneg
              simp [mul_pow, Real.sq_sqrt (gη2_nonneg _ _ _)] at this
              unfold AdaptiveAlgorithm.gη2_seq
              rel [this]
            }
            _ = alg.gη2_seq (k + l) := by {
              rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ <| ne_of_gt <| alg.hC_rel]
              simp
            }
      _ = ∑ k ∈ range N, (
            (alg.ρ_est δ + v) * alg.gη2_seq (k + l)
            + alg.C_est δ * (
              d_seq alg (k + l)^2
              - v / (alg.C_rel^2 * alg.C_est δ) * (alg.d (alg.𝒯 <| k + l) alg.u (alg.U <| alg.𝒯 <| k + l))^2
            )
          ) := by
        field_simp
        rw [mul_comm]
      _ = ∑ k ∈ range N, (
            (alg.ρ_est δ + v) * alg.gη2_seq (k + l)
            + alg.C_est δ * (
              d_seq alg (k + l)^2
              - alg.ε_qo * alg.d (alg.𝒯 <| k + l) alg.u (alg.U <| alg.𝒯 <| k + l)^2
            )
          ) := by
        dsimp [v]
        rw [mul_assoc, EuclideanDomain.mul_div_assoc, cancel alg hδ]
        · exact dvd_of_eq rfl
      _ = ∑ k ∈ range N, (alg.ρ_est δ + v) * alg.gη2_seq (k + l)
          + alg.C_est δ * ∑ k ∈ range N, (
              d_seq alg (k + l)^2
              - alg.ε_qo * alg.d (alg.𝒯 <| k + l) alg.u (alg.U <| alg.𝒯 <| k + l)^2
            ) := by
        rw [Finset.sum_add_distrib]
        conv =>
          lhs
          rhs
          rw [← Finset.mul_sum]
      _ ≤ ∑ k ∈ range N, (alg.ρ_est δ + v) * alg.gη2_seq (k + l)
          + alg.C_est δ * alg.C_qo * alg.gη2_seq l := by
        unfold d_seq
        have := alg.a3 l N
        apply add_le_add (by simp)
        rw [mul_assoc]
        exact (mul_le_mul_left <| alg.C_est_pos hδ).mpr this
  }
```

Using this first result we can continue to show
$$`
(1 - (ρ_{est}(δ) + ν)) ∑_{k=0}^n η^2_{k+l+1} ≤ (C_{est}(δ) C_{qo} + ρ_{est}(δ) + ν) η^2_l
`

This follows from the calculation
$$`
\begin{aligned}
  (1 - (ρ_{est}(δ) + ν)) ∑_{k=0}^n η^2_{k+l+1}
  &= (1 - (ρ_{est}(δ) + ν)) (∑_{k=0}^n η^2_{k+l+1} + η^2_l - η^2_l) \\
  &= (1 - (ρ_{est}(δ) + ν)) ∑_{k=0}^{n+1} η^2_{k+l} - (1 - (ρ_{est}(δ) + ν)) η^2_l \\
  &= (1 - (ρ_{est}(δ) + ν)) (∑_{k=0}^n η^2_{k+l} + η^2_{n+l+1}) - (1 - (ρ_{est}(δ) + ν)) η^2_l \\
  &≤ (1 - (ρ_{est}(δ) + ν)) ∑_{k=0}^n η^2_{k+l} + η^2_{n+l+1} - (1 - (ρ_{est}(δ) + ν)) η^2_l \\
  &= ∑_{k=0}^n η^2_{k+l} - (ρ_{est}(δ) + ν) ∑_{k=0}^n η^2_{k+l} + η^2_{n+l+1} - η^2_l + (ρ_{est}(δ) + ν) η^2_l \\
  &= ∑_{k=0}^n η^2_{k+l+1} - (ρ_{est}(δ) + ν) ∑_{k=0}^n η^2_{k+l} + (ρ_{est}(δ) + ν) η^2_l \\
  &≤ ∑_{k=0}^n (ρ_{est}(δ) + ν) η^2_{k+l} + C_{est}(δ) C_{qo} η^2_l - (ρ_{est}(δ) + ν) ∑_{k=0}^n η^2_{k+l} + (ρ_{est}(δ) + ν) η^2_l \\
  &= C_{est}(δ) C_{qo} η^2_l + (ρ_{est}(δ) + ν) η^2_l \\
  &= (C_{est}(δ) C_{qo} + ρ_{est}(δ) + ν) η^2_l
\end{aligned}
`
where the first inequality uses the fact that $`(1-(ρ_{est}(δ)+v)) < 1` and
the second one is the previous step of the proof. In Lean this
translates to the following section
```anchor summability_3
  have : ∀ N l:ℕ, (1-(alg.ρ_est δ + v)) * ∑ k ∈ range N, alg.gη2_seq (k + l + 1)
      ≤ (alg.C_est δ * alg.C_qo + alg.ρ_est δ + v) * alg.gη2_seq l := by {
    intros N l
    calc (1-(alg.ρ_est δ + v)) * ∑ k ∈ range N, alg.gη2_seq (k + l + 1)
      _ = (1-(alg.ρ_est δ + v)) * (∑ k ∈ range N, alg.gη2_seq (k + l + 1) + alg.gη2_seq l - alg.gη2_seq l) := by ring
      _ = (1-(alg.ρ_est δ + v)) * (∑ k ∈ range (N + 1), alg.gη2_seq (k + l) - alg.gη2_seq l) := by
        congr
        rw [Finset.sum_range_succ']
        conv =>
          rhs
          congr
          · rhs
            intro k
            rw [Nat.add_right_comm]
          · simp
      _ = (1-(alg.ρ_est δ + v)) * ∑ k ∈ range (N + 1), alg.gη2_seq (k + l)
          - (1-(alg.ρ_est δ + v)) * alg.gη2_seq l := by ring
      _ = (1-(alg.ρ_est δ + v)) * (∑ k ∈ range N, alg.gη2_seq (k + l)+ alg.gη2_seq (N + l))
          - (1-(alg.ρ_est δ + v)) * alg.gη2_seq l := by rw [Finset.sum_range_succ]
      _ ≤ (1-(alg.ρ_est δ + v)) * ∑ k ∈ range N, alg.gη2_seq (k + l)
          + alg.gη2_seq (N + l)
          - (1-(alg.ρ_est δ + v)) * alg.gη2_seq l := by
        rw [mul_add]
        gcongr
        apply mul_le_of_le_one_left
        · exact alg.gη2_seq_nonneg _
        · rw [← sub_sub]
          linarith [hv₁, hv₂, alg.ρ_est_pos hδ]
      _ = ∑ k ∈ range N, alg.gη2_seq (k + l)
          - (alg.ρ_est δ + v) * ∑ k ∈ range N, alg.gη2_seq (k + l)
          + alg.gη2_seq (N + l)
          - alg.gη2_seq l
          + (alg.ρ_est δ + v) * alg.gη2_seq l := by simp [sub_mul, one_mul, sub_add]
      _ = ∑ k ∈ range (N+1), alg.gη2_seq (k + l)
          - (alg.ρ_est δ + v) * ∑ k ∈ range N, alg.gη2_seq (k + l)
          - alg.gη2_seq l
          + (alg.ρ_est δ + v) * alg.gη2_seq l := by rw [Finset.sum_range_succ]; ring
      _ = ∑ k ∈ range N, alg.gη2_seq (k + l + 1)
          - (alg.ρ_est δ + v) * ∑ k ∈ range N, alg.gη2_seq (k + l)
          + (alg.ρ_est δ + v) * alg.gη2_seq l := by
        rw [Finset.sum_range_succ']
        conv =>
          enter [1,1,1,1]
          congr
          · rhs
            intro k
            rw [Nat.add_right_comm]
          · simp
        ring
      _ ≤ ∑ k ∈ range N, (alg.ρ_est δ + v) * alg.gη2_seq (k + l)
          + alg.C_est δ * alg.C_qo * alg.gη2_seq l
          - (alg.ρ_est δ + v) * ∑ k ∈ range N, alg.gη2_seq (k + l)
          + (alg.ρ_est δ + v) * alg.gη2_seq l := by rel [this N l]
      _ = alg.C_est δ * alg.C_qo * alg.gη2_seq l
          + (alg.ρ_est δ + v) * alg.gη2_seq l := by rw [Finset.mul_sum]; ring
      _ = (alg.C_est δ * alg.C_qo + alg.ρ_est δ + v) * alg.gη2_seq l := by ring
  }
```

Now noting that $`0 < 1 - (ρ_{est}(δ) + v)` we can divide on both
sides and setting $`C \coloneqq \frac{(C_{est}(δ) C_{qo} + ρ_{est}(δ) + ν)}{1 - (ρ_{est}(δ) + v)}`
arrive at
$$`
∑_{k=0}^n η^2_{k+l+1} ≤ C η^2_l
`

In Lean we prove this as the key observation
```anchor summability_4
  let C := (alg.C_est δ * alg.C_qo + alg.ρ_est δ + v)/(1-(alg.ρ_est δ + v))

  have key : ∀ N l:ℕ, ∑ k ∈ range N, alg.gη2_seq (k + l + 1) ≤ C * alg.gη2_seq l := by
    intros N l
    unfold C
    rw [div_mul_eq_mul_div₀]
    apply (le_div_iff₀ ?_).mpr
    · rw [mul_comm]
      apply this
    · linarith [hv₁]
```

Because the upper bound is independent of $`n` we also have summability of
$`(η_n)`:
```anchor summability_5
  have summable : Summable alg.gη2_seq := by
    apply (summable_nat_add_iff 1).mp
    apply summable_of_sum_range_le
    · intros n
      apply alg.gη2_seq_nonneg

    have := fun N ↦ key N 0
    simpa using this
```

Now mathematically the proof is finished, we have uniform summability of $`(η_n)`.
However, in Lean we need some glueing again because we defined
the summability
statements in the {ref "summability_equivalence"}[summability equivalence] only
for sequences in the `NNReal`s.
So we need to carry what we have shown over to the
NNReal version of $`η`, namely {anchorTerm summability_6}`alg.gη2_seq_nonneg`.
Also a proof of $`C > 0` is necessary.

```anchor summability_6
  constructor
  · rw [← NNReal.summable_coe]
    conv =>
      arg 1
      intro n
      simp
      rw [alg.hnn_gη_seq n]
    exact summable
  · have C_pos : C > 0 := by
      refine (lt_div_iff₀' ?_).mpr ?_
      · linarith [hv₁]
      · simp only [mul_zero]
        refine Left.add_pos_of_pos_of_nonneg ?_ hv₂
        refine add_pos ?_ <| alg.ρ_est_pos hδ
        apply mul_pos (alg.C_est_pos hδ)
        linarith [alg.hC_qo]

    have C_cast : ↑C.toNNReal = C := by
      rw [Real.coe_toNNReal]
      exact le_of_lt C_pos

    use C.toNNReal
    refine ⟨Real.toNNReal_pos.mpr C_pos, ?_⟩

    intros l
    apply NNReal.coe_le_coe.mp
    push_cast
    rw [C_cast]
    simp only [Pi.pow_apply, NNReal.coe_pow, alg.hnn_gη_seq l]
    conv =>
      lhs
      arg 1
      intro k
      rw [alg.hnn_gη_seq _]
    refine Real.tsum_le_of_sum_range_le ?_ fun n ↦ key n l
    intros n
    apply alg.gη2_seq_nonneg
```
The `constructor` makes us first show summability of
{anchorTerm summability_6}`alg.gη2_seq_nonneg`
and then the estimate part of uniform summability.
