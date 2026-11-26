# Solving a dense linear system has the same arithmetic exponent as matrix multiplication

[Read the paper (PDF)](output/pdf/single-coordinate.pdf) · [LaTeX source](paper/single-coordinate.tex)

How much arithmetic does it take to solve $Ax=b$ for a dense, nonsingular $n\times n$ rational matrix $A$? Given a candidate solution, one matrix-vector product checks it in $O(n^2)$ operations. Computing just the first coordinate has the same exponent $\omega$ as square matrix multiplication, even when $b=e_1=(1,0,\ldots,0)^\top$ is fixed in advance. We count each addition, subtraction, multiplication, or division in a fixed, exact program as one operation.

## Why one coordinate suffices

By Cramer's rule, the first coordinate is a cofactor divided by $\det A$. When the entries of $A$ are treated as variables, this fraction is already in lowest terms. Tracking numerators and denominators in an $s$-gate program for the coordinate gives a division-free computation of a nonzero multiple of $\det A$ with at most $3s$ multiplications. Results of Andrews and Bini then give $s\ge\lfloor n/4\rfloor^\omega/18$ for every $n\ge 8$. [Andrews, Theorem 3.4](https://arxiv.org/pdf/2208.01078#page=14) · [Bini](https://doi.org/10.1007/BF02575865)

## Check the Lean proof

Lean verifies the denominator argument. Taking Andrews's theorem and the OpenAI preprint's border-rank bound as hypotheses, it also proves $s\ge n^{9/4}/2304$ for $n\ge 8$. [Lean theorem](SingleCoordinate/Exponent.lean) · [Preprint](https://github.com/openai/math/blob/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf)

With elan installed, run the following command from the repository root to build the proof with Lean 4.19.0 and check its axioms.

```sh
./scripts/verify
```
