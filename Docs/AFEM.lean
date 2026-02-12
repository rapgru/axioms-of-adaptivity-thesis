import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Docs

set_option pp.rawOnError true

#doc (Manual) "Adaptive FEM" =>
%%%
tag := "afem"
htmlSplit := .never
%%%

The Adaptive Finite Element Method is an iterative approach for solving
partial differential equations based on the Finite Element Method.
It uses a-posteriori error estimators to guide a local mesh-refinement process.
This allows to resolve local features of the solution more efficiently while
keeping the overall degrees of freedom lower compared to uniform mesh refinement.
In the following, we summarize the basic concepts of this method.

# A Posteriori Error Estimators

For this section, assume that we want to approximate the solution $`u` of a
partial differential equation using the finite element method (in an appropriate
function space $`\mathcal{X}`). For a mesh $`\mathcal{T} ∈ \mathbb{T}` of
the problem domain, we can obtain a discrete approximations $`u_{\mathcal{T}}`
living on this mesh.

A posteriori error estimators are computable quantities that estimate the error
of a numerical solution to a partial differential equation. _Computable_ means
that, in contrast to a-priori error estimates, they do not use information about
the exact solution $`u`, which is usually unknown in practical applications.
In general, they depend on the discrete solution $`u_\mathcal{T}` for the
mesh $`\mathcal{T}` and
possibly other input data to the problem such as the right-hand side $`f` of the PDE.

For the moment lets denote by $`\eta(u_\mathcal{T})` an a-posteriori error estimator
for discrete solutions $`u_\mathcal{T}`.
In a very strong sense, we want the error estimator $`\eta` to be _reliable_ and _efficient_:

: Reliability

   means that the error estimator bounds the actual error from above,
   i.e., there exists a constant $`C_{\mathrm{rel}} > 0` such that for all meshes
   $`\mathcal{T}` of the problem domain
   $$`\|u - u_{\mathcal{T}}\|_\mathcal{X} \leq C_{\mathrm{rel}} \, \eta(u_{\mathcal{T}}).`

: Efficiency

   means that the error estimator also bounds the error from below,
   i.e., there exists a constant $`C_{\mathrm{eff}} > 0` such that for all meshes
   $`\mathcal{T}` of the problem domain
   $$`C_{\mathrm{eff}} \, \eta(u_{\mathcal{T}}) \leq \|u - u_{\mathcal{T}}\|_\mathcal{X} .`

These two properties ensure that the error estimator is a good measure
of the actual error. Reliability ensures that the computed solution is accurate
when the estimator is small, while efficiency ensures that the estimator
will converge to zero as the numerical solution approaches the exact solution.
In short, a reliable and efficient error estimator has the same order of
convergence as the actual error $`\|u - u_{\mathcal{T}}\|_\mathcal{X}`.

Usually, error estimators are defined as sums of local contributions from each element
of the mesh. So
$$`\eta(u_\mathcal{T}) = \left(\sum_{T \in \mathcal{T}} \eta_T^2(u_\mathcal{T})\right)^{1/2},`
where $`\eta_T` is the local error indicator for the element $`T \in \mathcal{T}`.
These local indicators should reflect the local error on the element $`T`.

A posteriori error estimators have two major applications:
- They can be used to have an estimate of the error of the numerical solution.
- They can be used to guide adaptive mesh refinement by refining elements
  with large local error indicators (AFEM).

An example of an a posteriori error estimator for the Poisson equation with
homogeneous Dirichlet boundary conditions $`u=0` on $`\partial\Omega` is the
residual error estimator {citep feischl2025fem}[].

# Adaptive Finite Element Method
%%%
tag := "afem_alg"
%%%

The adaptive finite element method (AFEM) concerns iterative algorithms
that adaptively refine the current mesh in regions where the local error is
large. The estimators $`\eta_T` are used as the measure of local error
and are also called _refinement indicators_ in this context.

The general structure of an AFEM algorithm is as follows:
1. Start with an initial mesh $`\mathcal{T}_0`.
2. For each iteration $`k = 0, 1, 2, \ldots`:
   1. Solve the discrete problem on the current mesh $`\mathcal{T}_k` to obtain
      the discrete Galerkin solution $`u_{\mathcal{T}_k}`.
   2. Compute the local error indicators $`\eta_T(u_{\mathcal{T}_k})` for each element
      $`T \in \mathcal{T}_k` and the global error estimator $`\eta(u_{\mathcal{T}_k})`.
   3. Stop if the global error estimator is below a given threshold.
   4. Choose a minimal set of elements $`\mathcal{M}_k \subseteq \mathcal{T}_k`
      such that
      $$`\left(\sum_{T \in \mathcal{M}_k} \eta_T^2(u_{\mathcal{T}_k})\right)^{1/2}
        \geq \theta \, \eta(u_{\mathcal{T}_k})`
      for a given marking parameter $`0 < \theta \leq 1`. This strategy is called
      _Dörfler marking_.
   5. Refine the marked elements to create a new shape-regular mesh $`\mathcal{T}_{k+1}`.

One can show that under suitable assumptions that the AFEM algorithm converges to
the exact solution $`u` as the number of iterations $`k \to \infty`.
Moreover, the convergence can be shown to be optimal in the sense that
the error decreases at the best possible rate compared to any other mesh refinement
strategy.

The article *AoA* states general
assumptions on the error estimator and refinement procedure that are sufficient
to show quasi-optimal convergence of the AFEM algorithm.
These axioms are formulated in an abstract setting and can be applied
to a wide range of problems. In the following chapters, we will
formalize these axioms and parts of the quasi-optimality proof in Lean.

# Example: L-shaped Domain

Consider the equation $`-\Delta u = 0` on the L-shaped domain
$`\Omega = (-1,1)^2 \setminus [-1,0) \times (-1,0]`. The function
$$`u(r,\varphi) \coloneqq r^{2/3} \sin(2\varphi/3),`
where $`(r,\varphi)` are polar coordinates centered at the re-entrant corner,
is a solution on the interior of $`\Omega`.
![Solution](static_files/afem/exact_solution.svg)
However, it has a singularity
at the re-entrant corner $`(0,0)` and thus is not in $`H^2(\Omega)`. We can
expect the error of the discrete solution
to be large near this corner when approximating $`u` using FEM.

Using [netgen and ngsolve](https://ngsolve.org) we can perform adaptive mesh refinement
for this problem. Starting from an initial coarse mesh and using
the trace of $`u` on the boundary as Dirichlet data, along
with the residual error estimator and Dörfler marking with $`\theta = 0.25`,
we obtain the following sequence of meshes and solutions:

![AFEM Loop](static_files/afem/collage_small.png)

On the left side we see the current mesh and on the right side the
local refinement indicators represented as colored patches on the elements.
As expected, the mesh is refined more heavily near the re-entrant corner
where the solution has a singularity. The algorithm used
is exactly the loop from the previous section.
By concentrating on the re-entrant corner we arrive at a better
approximation of the solution than with uniform refinement using the same
computational effort.

The next chapter will show the very abstract setting and assumptions
*AoA* makes about AFEM and how they translate to Lean.
