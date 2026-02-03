# Statistical Learning Theory in Lean 4: Empirical Processes from Scratch

## Abstract
We present the first comprehensive Lean 4 formalization of statistical learning theory (SLT) grounded in empirical process theory. Our end-to-end formal infrastructure implement the missing contents in latest Lean library, including a complete development of Gaussian Lipschitz concentration, the first formalization of Dudley’s entropy integral theorem for sub-Gaussian processes, and an application to least-squares regression with a sharp rate. The project was carried out using a human–AI collaborative workflow, in which humans design proof strategies and AI agents execute tactical proof construction, resulting in approximately 30,000 lines of human-verified Lean 4 code produced over 500 hours of supervised development. Beyond implementation, the formalization process exposes and resolves implicit assumptions and missing details in standard SLT textbooks, enforcing a granular, line-by-line understanding of the theory. This work establishes a reusable formal foundation for future developments in machine learning theory.

<div align="center">
    <img src="./figs/level-1.jpg" width="600" alt="Level 1 diagram"><br>
    <em>Figure 1 — Level 1 architecture overview</em>
</div>

## Implementation Roadmap

<h1 align="center"> 
    <img src="./figs/level-2.jpg" width="1200">
</h1>

## How to Run
  ```bash
  # get Mathlib4 cache 
  lake exe cache get

  # build the project
  lake build
  ```

## Major Results

Our formalization library `SLT` contains (but not limited to):

| Name | Reference |
|------|-----------|
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

## References

- Boucheron, S., Lugosi, G., & Massart, P. (2013). *Concentration Inequalities: A Nonasymptotic Theory of Independence*. Oxford University Press.
- Daras, G., Dean, J., Jalal, A., & Dimakis, A. (2021). Intermediate Layer Optimization for Inverse Problems using Deep Generative Models. In *Proceedings of the 38th International Conference on Machine Learning* (Vol. 139, pp. 2421–2432). PMLR.
- Raskutti, G., Wainwright, M. J., & Yu, B. (2011). Minimax rates of estimation for high-dimensional linear regression over ℓ_q-balls. *IEEE Transactions on Information Theory*, 57(10), 6976–6994.
- Vershynin, R. (2018). *High-Dimensional Probability: An Introduction with Applications in Data Science* (Vol. 47). Cambridge University Press.
- Wainwright, M. J. (2019). *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Vol. 48). Cambridge University Press.

## Acknowledgement

- `SLT/SeparableSpaceSup.lean` is sourced from [lean-rademacher](https://github.com/auto-res/lean-rademacher.git). We use `separableSpaceSup_eq_real` from it in `SLT/Dudley.lean`.
- `Clt/` is sourced from [CLT](https://github.com/RemyDegenne/CLT.git). We use `tendsto_iff_tendsto_charFun` from `Clt/Inversion.lean` in `SLT/GaussianPoincare/Limit.lean`.

We greatly appreciate these two remarkable repositories.
