# Statistical Learning Theory in Lean 4: Empirical Processes from Scratch (ICML 2026)
<p align="center">
  <a href="https://arxiv.org/abs/2602.02285"><img src="https://img.shields.io/badge/arXiv-Paper-red?style=for-the-badge" alt="Paper"></a>
  <a href="https://huggingface.co/collections/liminho123/statistical-learning-theory-in-lean-4"><img src="https://img.shields.io/badge/🤗-Dataset-yellow?style=for-the-badge" alt="Dataset"></a>
  <a href="https://github.com/YuanheZ/lean-stat-learning-theory/releases/tag/v4.31.0"><img src="https://img.shields.io/badge/Lean-v4.31.0-blue?style=for-the-badge" alt="Lean v4.31.0"></a>
</p>

## Table of Contents

- [Abstract](#abstract)
- [Current Library](#current-library)
- [Implementation Roadmap](#implementation-roadmap)
- [How to Run](#how-to-run)
- [Major Results](#major-results)
- [Repository Map](#repository-map)
- [Dataset](#dataset)
- [Recipe for Vibe Formalization](#recipe-for-vibe-formalization)
- [References](#references)
- [Acknowledgement](#acknowledgement)

## Abstract
We present the first comprehensive Lean 4 formalization of statistical learning theory (SLT) grounded in empirical process theory. The ICML 2026 paper artifact develops Gaussian Lipschitz concentration, Dudley's entropy integral theorem for sub-Gaussian processes, and an application to least-squares regression with a sharp rate. The project was carried out using a human-AI collaborative workflow, in which humans design proof strategies and AI agents execute tactical proof construction under supervision. Beyond implementation, the formalization process exposes and resolves implicit assumptions and missing details in standard SLT textbooks, enforcing a granular, line-by-line understanding of the theory.

The repository has since grown into a broader high-dimensional probability library. The current `v4.31.0` release upgrades the project to Lean and Mathlib `v4.31.0` and adds substantial developments in Hanson-Wright inequalities, matrix concentration, matrix perturbation theory, and random matrix theory.

<div align="center">
    <img src="./figs/level-1.jpg" width="600" alt="Level 1 diagram"><br>
    <em>
     Lean formulation for Localized Empirical Process Framework.
     It includes the <span style="color:#1f4fbf;">blue</span> part for the capacity control
     and the <span style="color:#b30000;">red</span> part for concentration.
     The colored zone indicates the major results in the chapters of
     Wainwright (2019, <em>High-Dimensional Statistics</em>) and
     Boucheron et al. (2013, <em>Concentration Inequalities</em>).    
    </em>
</div>

## Current Library

The `SLT` library is fully proved: it contains no `sorry`, `axiom`, `admit`, or `native_decide`. At the `v4.31.0` release, the library contains 65 Lean files and about 56k lines of formalized mathematics.

The current repository includes both the ICML 2026 empirical-process formalization and newer infrastructure for:

- metric entropy, covering numbers, sub-Gaussian processes, and chaining;
- Efron-Stein, entropy duality, Gaussian Poincare, and Gaussian log-Sobolev inequalities;
- Gaussian Lipschitz concentration and least-squares regression rates;
- finite-dimensional matrix spectral theory, SVD, Courant-Fischer, Eckart-Young-Mirsky, Weyl perturbation, and Davis-Kahan;
- Hanson-Wright inequalities for quadratic forms of independent sub-Gaussian variables;
- random matrix theory results from high-dimensional probability, including sub-Gaussian matrix norm bounds, two-sided singular-value bounds, Lieb's inequality, and matrix Bernstein.

## Implementation Roadmap

<h1 align="center"> 
    <img src="./figs/level-2.jpg" width="1200">
</h1>

The figure above is the roadmap for the ICML 2026 paper artifact. The expanded `v4.31.0` library can be read in layers:

| Layer | Main files | Purpose |
|------|------------|---------|
| Foundational probability and metric tools | `SmallBallProb`, `MeasureInfrastructure`, `MetricEntropy`, `CoveringNumber`, `SubGaussian` | Basic probability, covering numbers, metric entropy, sub-Gaussian variables and processes. |
| Empirical process theory | `Chaining`, `Dudley`, `TDudley`, `LeastSquares/*` | Chaining, Dudley bounds, truncated Dudley, and least-squares applications. |
| Gaussian concentration | `GaussianMeasure`, `GaussianPoincare/*`, `GaussianSobolevDense/*`, `GaussianLipConcen` | Gaussian approximation, Poincare inequality, Sobolev density, and Lipschitz concentration. |
| Entropy and log-Sobolev theory | `EfronStein`, `GaussianLSI/*` | Efron-Stein, entropy duality, subadditivity of entropy, Bernoulli and Gaussian log-Sobolev inequalities. |
| Matrix and spectral infrastructure | `MatrixInfra/*` | Singular values, SVD, Courant-Fischer, Eckart-Young-Mirsky, Weyl perturbation, Davis-Kahan, and matrix calculus. |
| High-dimensional probability and RMT | `HansonWright`, `RMT/*` | Hanson-Wright, sub-Gaussian random matrices, two-sided singular-value bounds, Lieb, and matrix Bernstein. |

## How to Run

The project is pinned to Lean `v4.31.0` and Mathlib `v4.31.0`.

```bash
# Optional: get the Mathlib cache
lake exe cache get

# Build the whole SLT library.
# Lake has no -j/--jobs flag; use LEAN_NUM_THREADS for parallelism.
LEAN_NUM_THREADS=$(nproc) lake build

# Build selected modules
LEAN_NUM_THREADS=$(nproc) lake build SLT.HansonWright
LEAN_NUM_THREADS=$(nproc) lake build SLT.RMT.MatBern
```

There is no separate test suite. A clean `lake build` is the verification. The `lakefile.lean` globs every module under `SLT/`; there is no `SLT.lean` root file.

## Major Results

Our formalization library `SLT` contains the following representative results.

### ICML 2026 paper core

| Name | Reference |
|------|-----------|
| `small_ball_prob` | Vershynin (2018), Exercise 2.2.10 |
| `coveringNumber_lt_top_of_totallyBounded` | Vershynin (2018), Remark 4.2.3 |
| `isENet_of_maximal` | Vershynin (2018), Lemma 4.2.6 |
| `coveringNumber_euclideanBall_le` | Vershynin (2018), Corollary 4.2.13 |
| `coveringNumber_l1Ball_le` | Daras et al. (2021), Theorem 2 |
| `subGaussian_finite_max_bound` | Wainwright (2019), Exercise 2.12 |
| `dudley` | Boucheron et al. (2013), Corollary 13.2 |
| `efronStein` | Boucheron et al. (2013), Theorem 3.1 |
| `gaussianPoincare` | Boucheron et al. (2013), Theorem 3.20 |
| `han_inequality` | Boucheron et al. (2013), Theorem 4.1 |
| `entropy_duality` | Boucheron et al. (2013), Theorem 4.13 |
| `entropy_duality_T` | Boucheron et al. (2013), Remark 4.4 |
| `entropy_subadditive` | Boucheron et al. (2013), Theorem 4.22 |
| `bernoulli_logSobolev` | Boucheron et al. (2013), Theorem 5.1 |
| `gaussian_logSobolev_W12_pi` | Boucheron et al. (2013), Theorem 5.4 |
| `lipschitz_cgf_bound` | Boucheron et al. (2013), Theorem 5.5 |
| `gaussian_lipschitz_concentration` | Boucheron et al. (2013), Theorem 5.6 |
| `one_step_discretization` | Wainwright (2019), Proposition 5.17 |
| `local_gaussian_complexity_bound` | Wainwright (2019), (5.48) Gaussian Case |
| `master_error_bound` | Wainwright (2019), Theorem 13.5 |
| `gaussian_complexity_monotone` | Wainwright (2019), Lemma 13.6 |
| `linear_minimax_rate_rank` | Wainwright (2019), Example 13.8 |
| `bad_event_probability_bound` | Wainwright (2019), Lemma 13.12 |
| `l1BallImage_coveringNumber_le` | Raskutti et al. (2011), Lemma 4, q=1 |

### v4.31.0 extensions

| Name | Reference / role |
|------|------------------|
| `truncated_dudley_entropy_bound` | Truncated Dudley entropy bound for global oscillation |
| `hanson_wright_inequality` | Hanson-Wright tail bound from a proved MGF certificate |
| `hanson_wright_inequality_hdp` | HDP-style Hanson-Wright inequality with maximum coordinate `psi2` scale |
| `Matrix.singularValues` | Singular values of matrices via Euclidean linear maps |
| `Matrix.eq_sum_singularValue_vecMulVec` | Matrix SVD reconstruction |
| `LinearMap.IsSymmetric.eigenvalues_eq_courantFischerMaxMin_succ` | Courant-Fischer max-min theorem |
| `LinearMap.IsSymmetric.eigenvalues_eq_courantFischerMinMax_sub` | Courant-Fischer min-max theorem |
| `LinearMap.singularValues_eq_singularCourantFischerMaxMin_succ` | Singular-value Courant-Fischer max-min theorem |
| `LinearMap.singularValues_eq_singularCourantFischerMinMax_sub` | Singular-value Courant-Fischer min-max theorem |
| `Matrix.eckartYoungMirsky_hdp` | HDP Theorem 4.1.13, Eckart-Young-Mirsky |
| `LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm` | HDP Lemma 4.1.14, Weyl eigenvalue perturbation |
| `LinearMap.abs_singularValues_sub_le_opNorm` | HDP Lemma 4.1.14, singular-value perturbation |
| `LinearMap.IsSymmetric.davisKahan_eigenvector_angle_hdp` | HDP Theorem 4.1.15, Davis-Kahan eigenvector angle bound |
| `LinearMap.IsSymmetric.davisKahan_spectralProjection_hdp` | HDP Lemma 4.1.16, Davis-Kahan spectral projection bound |
| `Matrix.lieb_inequality_hdp_5_4_8` | HDP Theorem 5.4.8, deterministic Lieb concavity |
| `RMT.lieb_inequality_random_matrices_hdp_5_4_9` | HDP Lemma 5.4.9, random-matrix Lieb inequality |
| `RMT.matrix_bernstein_inequality_hdp_all` | HDP Theorem 5.4.1, matrix Bernstein inequality |
| `RMT.norm_subgaussian_matrices_hdp_of_pos` | HDP Theorem 4.4.3, norm of matrices with sub-Gaussian entries |
| `RMT.norm_subgaussian_matrices_expectation_hdp_of_pos` | HDP Remark 4.4.4, expectation bound |
| `RMT.norm_random_matrices_lower_bound_hdp_of_pos` | HDP Exercise 4.42, lower bound for random matrix norm |
| `RMT.norm_symmetric_subgaussian_matrices_hdp_of_pos` | HDP Corollary 4.4.7, symmetric sub-Gaussian matrix norm |
| `RMT.two_sided_subgaussian_matrices_hdp_of_pos` | HDP Theorem 4.6.1, two-sided singular-value bound |
| `RMT.two_sided_subgaussian_matrices_expectation_hdp_of_pos` | HDP Remark 4.6.2, sample covariance expectation bound |

## Repository Map

| Path | Contents |
|------|----------|
| `SLT/SubGaussian.lean` | Scalar sub-Gaussian variables, processes, `psi2` scale, finite maxima, and Bernstein-style CGF tails. |
| `SLT/CoveringNumber.lean`, `SLT/MetricEntropy.lean` | Nets, covering numbers, entropy integrands, Euclidean and `l1` covering bounds. |
| `SLT/Chaining.lean`, `SLT/Dudley.lean`, `SLT/TDudley.lean` | Chaining, Dudley's entropy integral theorem, and truncated Dudley. |
| `SLT/EfronStein.lean` | Product-measure conditional expectation infrastructure and Efron-Stein. |
| `SLT/GaussianLSI/` | Entropy, entropy duality, subadditivity, Bernoulli and Gaussian log-Sobolev inequalities. |
| `SLT/GaussianPoincare/` | Gaussian Poincare via Rademacher approximation and Levy continuity. |
| `SLT/GaussianSobolevDense/` | Smooth approximation and density tools for Gaussian Sobolev arguments. |
| `SLT/LeastSquares/` | Localized least-squares framework and linear or `l1` regression applications. |
| `SLT/MatrixInfra/` | Matrix spectral theory, SVD, Courant-Fischer, EYM, perturbation, Davis-Kahan, and matrix calculus. |
| `SLT/HansonWright.lean` | Hanson-Wright MGF certificates and tail inequalities. |
| `SLT/RMT/` | Random matrix theory: sub-Gaussian matrix bounds, Lieb, and matrix Bernstein. |

## Dataset

We release a high-quality Lean 4 training dataset for LLM's formal reasoning — 865 traced theorems, 18,669 tactic steps, 300M tokens from the ICML 2026 SLT library artifact and its referenced dependencies. Every proof is human-verified, non-LLM-synthetic with full proof state traces (state_before → tactic → state_after).

<div align="center">

| **Dataset** | **Download** |
| :------------: | :------------: |
| **Novel** | [🤗 HuggingFace](https://huggingface.co/datasets/liminho123/lean4-stat-learning-theory-novel)   |
| **Random** | [🤗 HuggingFace](https://huggingface.co/datasets/liminho123/lean4-stat-learning-theory-random)   |
| **Corpus** | [🤗 HuggingFace](https://huggingface.co/datasets/liminho123/lean4-stat-learning-theory-corpus)   |

</div>

- **Novel**: Validation and test sets contain theorems that use premises not seen during training (harder evaluation).
- **Random**: Theorems are split randomly.
- **Corpus**: 3,021 premises across 470 files (SLT library + referenced Mathlib/Lean4 stdlib declarations). Used for retrieval-augmented proving.

## Recipe for Vibe Formalization

We provide a practical recipe for human–AI collaborative formalization in Lean 4, distilled from our experience producing ~30,000 lines of human-verified code with Claude Code (`Claude-Opus-4.5`). The full guide and example prompts live in [`vibe-recipe/`](./vibe-recipe/).

**Workflow at a glance.** The process follows four iterative steps:

1. **Decompose proofs into small lemmas.** We recommend to ensure the target to formalize can be finished within a single agent context window (~300 lines) without auto-compaction. Small units increase the agent's effective thinking budget, reduce the information loss of context compaction.

2. **Design high-quality prompts.** Supply the agent with (a) signatures of possibly-needed project-local declarations obtained via the file outline MCP tool—*never* full file contents, which quickly fill the context window and cause hallucinations—and (b) a well-written mathematical proof to formalize. Mathlib declarations can be discovered on-the-fly through Lean search MCP tools. A worked example is given in [`vibe-recipe/EXAMPLE_INSTRUCTIONS.md`](./vibe-recipe/EXAMPLE_INSTRUCTIONS.md).

3. **Clean compiler warnings.** Instruct the agent to eliminate all warnings, explicitly directing it to *remove* unused variables rather than masking them with `_` (a harmful preference of `Claude-Opus-4.5`).

4. **Clean unused `have` statements.** Use the custom `#check_unused_have` metaprogram ([`vibe-recipe/UnusedHaveDetector.lean`](./vibe-recipe/UnusedHaveDetector.lean)) to detect and remove dead `have` bindings from proof terms. Repeat Steps 3–4 until both are clean.

**Human-in-the-loop intervention.** A recurring failure mode we observe is that when the agent faces many simultaneous tactic errors in a long proof, it tends to abandon a largely correct proof structure in favor of drastic—and often incorrect—rewrites (e.g., *"Let me simplify the approach…"*). To counteract this, we instruct to encourage the agent always to fix errors first. This forces incremental error resolution, which surfaces structurally diagnostic errors that expose the true root cause rather than triggering wholesale re-proofs.

## References

- Boucheron, S., Lugosi, G., & Massart, P. (2013). *Concentration Inequalities: A Nonasymptotic Theory of Independence*. Oxford University Press.
- Daras, G., Dean, J., Jalal, A., & Dimakis, A. (2021). Intermediate Layer Optimization for Inverse Problems using Deep Generative Models. In *Proceedings of the 38th International Conference on Machine Learning* (Vol. 139, pp. 2421–2432). PMLR.
- Raskutti, G., Wainwright, M. J., & Yu, B. (2011). Minimax rates of estimation for high-dimensional linear regression over ℓ_q-balls. *IEEE Transactions on Information Theory*, 57(10), 6976–6994.
- Tropp, J. A. (2015). An Introduction to Matrix Concentration Inequalities. *Foundations and Trends in Machine Learning*, 8(1-2), 1-230.
- Vershynin, R. (2018). *High-Dimensional Probability: An Introduction with Applications in Data Science* (Vol. 47). Cambridge University Press.
- Wainwright, M. J. (2019). *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Vol. 48). Cambridge University Press.

## Acknowledgement

- `SLT/SeparableSpaceSup.lean` is sourced from [lean-rademacher](https://github.com/auto-res/lean-rademacher.git). We use `separableSpaceSup_eq_real` from it in `SLT/Dudley.lean`. [lean-rademacher](https://github.com/auto-res/lean-rademacher.git) formalized the Dudley's entropy integral bound for Rademacher complexity, please refer to it if you'are interested!
- `SLT/GaussianPoincare/LevyContinuity.lean` is sourced from [CLT](https://github.com/RemyDegenne/CLT.git). We use `tendsto_iff_tendsto_charFun` from `Clt/Inversion.lean` in `SLT/GaussianPoincare/Limit.lean`.
- We use mcp tools from [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp.git) to enable the agent to interact with live LSP feedbacks and retrieve relevant information.

We greatly appreciate these remarkable repositories.
