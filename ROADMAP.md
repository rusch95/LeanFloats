# LeanFloats Roadmap

This roadmap tracks theorem-driven build-out across three complementary
float models:

- **Bitwise model**: exact encodings, decode functions, special values,
  rounding predicates, and kernel factoring identities.
- **Relational semantic model**: implementation-independent refinement
  statements that connect a concrete low-precision computation to a real
  or high-precision specification.
- **Probabilistic affine error model**: less pessimistic error tracking for
  stochastic rounding, randomized quantization, and independent error terms.

The first five examples have Lean entry points in `MX.Examples`.

## Phase 1: Seed Exemplars

1. `blockDot_refines_decoded_dot`
   - Model: bitwise + relational decode.
   - Use case: MXFP4 block dot products for low-precision matmul.
   - Statement: the block-factored MX dot product equals the dot product
     over fully decoded real values.
   - Status: started in `MX.Examples`, using `MX.MXVec.dotBlocked_eq_dotDecoded`.

2. `stochastic_sum_variance_bound`
   - Model: probabilistic affine error.
   - Use case: stochastic-rounding reductions in training loops.
   - Statement: independent zero-mean rounding errors compose with variance
     equal to the sum of per-term variances, then bounded by a chosen budget.
   - Status: started in `MX.Examples` with a reusable variance-budget predicate.

3. `softmax_shift_invariant_rel`
   - Model: relational semantic.
   - Use case: numerically stable softmax in attention kernels.
   - Statement: adding the same real constant to every logit preserves the
     semantic softmax result.
   - Status: started in `MX.Examples` as a shift-invariance relation; later
     work should instantiate it with an actual real softmax definition.

4. `rounding_refines_format_relation`
   - Model: relational semantic + bitwise scalar format.
   - Use case: encode paths from real/high-precision tensors into FP4/FP6/FP8.
   - Statement: a rounding implementation produces an encoding related to the
     source real by the format's rounding predicate.
   - Status: started in `MX.Examples`, including an E2M1 round-to-nearest-even
     specialization.

5. `quantized_dot_unbiased`
   - Model: probabilistic affine error.
   - Use case: stochastic quantization of dot-product inputs.
   - Statement: if each scalar quantizer is unbiased, a weighted dot against
     deterministic weights is unbiased.
   - Status: started in `MX.Examples` with finite-support expectation.

## Phase 2: Matrix And Attention Kernels

6. `mx_block_shared_scale_affine_bound`
   - Model: probabilistic affine error + bitwise block format.
   - Use case: MXFP4/MXFP6/MXFP8 block quantization.
   - Statement: shared-scale quantization error splits into a scale-selection
     term and per-element rounding terms.

7. `gemm_tile_refines_decoded_matmul`
   - Model: bitwise + relational semantic.
   - Use case: tiled GEMM over MX/NV blocks.
   - Statement: a tiled block GEMM refines decoded real matrix multiplication
     when every tile uses the same decode contract.

8. `attention_score_variance_bound`
   - Model: probabilistic affine error.
   - Use case: attention score computation `QK^T / sqrt(d)`.
   - Statement: score variance is bounded by the weighted sum of quantization
     variances from the query and key vectors.

9. `softmax_perturbation_bound`
   - Model: relational semantic + analytic error.
   - Use case: robustness of attention probabilities to bounded logit error.
   - Statement: bounded logit perturbations imply bounded softmax-output
     perturbations.

10. `rmsNorm_refines_real_spec`
    - Model: relational semantic.
    - Use case: transformer normalization layers.
    - Statement: an RMSNorm implementation refines the real-valued RMSNorm
      formula under specified accumulator and reciprocal-square-root relations.

## Phase 3: Scientific Reductions

11. `pairwise_sum_error_bound`
    - Model: deterministic affine error.
    - Use case: reproducible reductions in simulation and linear algebra.
    - Statement: a fixed pairwise tree has a logarithmic-depth error budget
      rather than a fully sequential budget.

12. `stochastic_tree_sum_variance_bound`
    - Model: probabilistic affine error.
    - Use case: randomized reductions with stochastic rounding.
    - Statement: a fixed reduction tree accumulates variance according to tree
      structure and independent node-level rounding variances.

13. `fma_refines_real_fma`
    - Model: bitwise + relational semantic.
    - Use case: BLAS kernels and polynomial kernels.
    - Statement: fused multiply-add rounds once and refines the real operation
      `a * b + c` under the chosen rounding mode.

14. `horner_refines_polynomial_eval`
    - Model: relational semantic + affine error.
    - Use case: transcendental approximations and special functions.
    - Statement: Horner evaluation refines the target polynomial with an error
      budget induced by the FMA chain.

15. `fft_butterfly_error_bound`
    - Model: affine error.
    - Use case: FFT kernels in signal processing and spectral solvers.
    - Statement: one butterfly step preserves the exact butterfly relation up
      to bounded multiply/add rounding errors.

16. `finite_difference_constant_preservation`
    - Model: relational semantic.
    - Use case: PDE stencils and numerical differentiation.
    - Statement: the finite-difference stencil maps constant fields to zero
      even after low-precision decode/encode, under exact constant encoding.

17. `finite_difference_roundoff_bound`
    - Model: affine error.
    - Use case: PDE stencils on low-precision accelerators.
    - Statement: the finite-difference stencil has a roundoff budget controlled
      by coefficient magnitudes and input quantization error.

18. `cg_matvec_residual_error_bound`
    - Model: relational semantic + affine error.
    - Use case: conjugate-gradient and iterative solvers.
    - Statement: a low-precision matrix-vector product induces a bounded
      residual perturbation in one CG iteration.

## Phase 4: Statistics And Training

19. `mean_stochastic_round_unbiased`
    - Model: probabilistic affine error.
    - Use case: streaming means and activation statistics.
    - Statement: the mean of stochastically rounded samples is unbiased when
      each rounded sample is unbiased.

20. `variance_estimator_rounding_error_bound`
    - Model: probabilistic affine error.
    - Use case: normalization statistics and scientific data analysis.
    - Statement: bounded or unbiased scalar rounding yields a controlled error
      in sample variance.

21. `gradient_quantization_unbiased`
    - Model: probabilistic affine error.
    - Use case: quantization-aware training and compressed optimizers.
    - Statement: a stochastic gradient quantizer has expectation equal to the
      original gradient.

22. `gradient_quantization_concentration`
    - Model: probabilistic affine error.
    - Use case: convergence reasoning for quantized SGD.
    - Statement: the quantized gradient concentrates around the exact gradient
      with a tail bound derived from per-coordinate quantization ranges.

