# Small-vs-Weakly-Small-and-Talagrand-Discrete-Convexty-Conjecture

This project contains complete Lean proofs of the main results in the two uploaded PDFs: Talagrand's conjecture that smallness is equivalent to weak smallness up to a universal change of density, and Talagrand's discrete-convexity conjecture. The covering budget is **1/2**, and the numerical constants are those in the PDFs. Proofs use Lean's kernel and mathlib; no paper result is declared as an axiom or left as an unproved hypothesis.

## Verified statements

| Uploaded result | Lean declaration | Conclusion |
| --- | --- | --- |
| *Integral and fractional expectation thresholds are equivalent*, Theorem 1.1 | `TalagrandIntegral.comparison_theorem_1_1` | `fractionalThreshold F ≤ (25 * 512^4) * integralThreshold F` |
| Its budget-preserving rounding statement | `TalagrandIntegral.fractional_to_integral` | A fractional cover of cost ≤ 1/2 at `r ≥ 0` gives an integral cover of cost ≤ 1/2 at `r / (25 * 512^4)` |
| Its Theorem 2.1 | `TalagrandIntegral.multiscale_selector`, `mean_selector` | Simultaneous capture and mean color ≤ 2 with probability at least 9/10 |
| Its Lemma 2.2 | `TalagrandIntegral.maximal_truncation` | Existence of a maximal admissible cutoff and the bound on the number of heavy coordinates |
| Its Corollary 4.1; also Corollary 1.2 of the discrete-convexity paper | `TalagrandIntegral.integral_two_unions` | At Bernoulli measure ≥ 1/2, the two-union exceptional family is small at `p / (50 * 512^4)` |
| *Talagrand's discrete-convexity conjecture*, Theorem 1.1 | `TalagrandIntegral.discrete_convexity_theorem_1_1` | For `k = 2^75`, measure ≥ `1 - 1/k` implies that the `k`-union exceptional family is small at the original density `p` |
| Its Proposition 3.1 | `TalagrandIntegral.discrete_convexity_proposition_3_1` | The 32-union exceptional family of a family of measure ≥ 1/2 is small at `q / 2^70` |

The two discrete-convexity results assume `0 < p < 1` (or `0 < q < 1`), as in the paper. They apply to arbitrary families, without monotonicity. The comparison theorem is proved for any finite family excluding the empty set, a stronger statement than the increasing-family version. The threshold definitions are suprema; `integralThreshold_isGreatest` and `fractionalThreshold_isGreatest` prove that they are attained, so they are the paper's maxima.

## Definitions and proof scope

`Finset X` represents a subset of a finite ground set. `Small p F` means that there exists a finite containment cover `G` with `∑ S ∈ G, p^S.card ≤ 1/2`. `FractionalCover` includes nonnegative coefficients bounded by one, coverage of each family member, and the same cost budget. Natural powers use `p^0 = 1`, including at zero.

The inherited fractional-certificate development uses the equivalent Boolean-cube representation `Cube X = X → Bool`. `finsetCube` supplies the explicit equivalence; `IntegralSmall`, `measure`, `badTwo`, and `badUnions` denote integral smallness, Bernoulli product measure, and the relevant union obstructions. `CubeBridge.lean` proves the conversion, including coefficient capping.

The comparison proof follows charged truncation, minimum-displacement recoloring, reconstruction, counting, and the polynomial expectation argument. Its counting step uses ordered encodings and a factorial bound in place of the paper's multinomial estimate.

The discrete-convexity theorem and Proposition 3.1 are proved through the companion comparison theorem, the fully proved Li fractional certificate included here, and explicit finite probability couplings. This is an alternative proof of those statements. **The discrete paper's separate hypergraph-covering Lemma 2.1 and signed 32-row kernel construction are not formalized.** The high-density coupling uses a mixture of a uniformly chosen single row and all rows; this has the required row marginals and full union.

## Reproduce the verification

Required versions are pinned:

- Lean **4.32.0** (`leanprover/lean4:v4.32.0`).
- mathlib commit **81a5d257c8e410db227a6665ed08f64fea08e997**.

Install Lean's `elan` toolchain manager, unzip this directory, and run:

```sh
lake exe cache get Mathlib.Tactic Mathlib.Analysis.MeanInequalities Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Topology.Order.Compact Mathlib.Data.Fintype.Perm Mathlib.Analysis.SpecificLimits.Normed Mathlib.Analysis.Complex.ExponentialBounds
sh scripts/verify.sh
```

The first command downloads the needed mathlib build cache. The archive contains source and configuration, not the Lean toolchain or downloaded dependencies.

`Small-vs-Weakly-Small-and-Talagrand-Discrete-Convexty-Conjecture.lean` is the complete single-file version. It has only mathlib imports and can be checked in the pinned project with:

```sh
lake env lean Small-vs-Weakly-Small-and-Talagrand-Discrete-Convexty-Conjecture.lean
```

`verification/` contains the compiler logs, the axiom audit, a version and source profile, and source hashes. The audited theorems depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `admit`, custom axioms, `native_decide`, or unsafe declarations in the proof sources. This is a classical existence proof of covers, not an executable algorithm for finding them efficiently.
