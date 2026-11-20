# The Two-Step Hardy Ladder in Higher Dimensions

**An exact four-level pairing formula and a twelve-level state that attains the plastic-constant bound**

Each observer chooses among three measurements with two outcomes. The Hardy ladder requires five joint outcomes to have probability zero. How large can the probability of the sixth outcome be if the state uses more than two quantum levels?

For any pure state with four positive Schmidt coefficients, testing three pairings gives the exact answer. Write the coefficients as $d_1,d_2,d_3,d_4$, with $\sum_i d_i^2=1$, and define

$$
E_{ij}=\left(\frac{d_i d_j^5-d_j d_i^5}{d_i^5+d_j^5}\right)^2.
$$

The maximum success probability is

$$
\max\{E_{12}+E_{34},\ E_{13}+E_{24},\ E_{14}+E_{23}\}.
$$

Choose a maximizing pairing. On each of its two pairs, run the optimal two-level ladder for those coefficients. The sums above are the Born probabilities of these measurements, and arbitrary complex binary measurements obey the same upper bound. If the coefficients are supplied at a common unnormalized scale, divide the displayed maximum by $\sum_i d_i^2$.

## Where the plastic constant enters

Let $\rho$ be the real root of $\rho^3=\rho+1$. The registered two-qubit value is $p_*=(8\rho^2+\rho-11)/25\approx0.174549571489$. A four-level state reaches it exactly when its Schmidt coefficients can be paired so that the smaller divided by the larger equals $\rho^{-2}$ in both pairs. For example, normalizing $(1,\rho^{-2},2,2\rho^{-2})$ gives an optimizer with four distinct coefficients. The fixed-spectrum formula also covers repeated coefficients and ties between pairings.

| Schmidt support or measurement class | Result |
|---|---|
| Up to three levels, arbitrary binary effects | Success is at most $p_*$. Every pure state with three positive Schmidt coefficients is strictly below it. |
| Four positive levels, arbitrary binary effects | The best disjoint pairing gives the fixed-state optimum and the ratio test characterizes attainment of $p_*$. |
| Finite ensembles of Schmidt rank at most four | Five exact zeros in the ensemble imply the $p_*$ ceiling, even when the components have different spectra and compressed effects. |
| Any finite number of levels, one-dimensional endpoint or complementary one-dimensional endpoint | Success is at most $p_*$. |
| Twelve levels | A pure state with twelve distinct positive Schmidt weights attains $p_*$ exactly. |

For the twelve-level state, take sector probabilities $(1,2,3,5,7,11)/29$. Each sector of weight $w$ contributes squared Schmidt coefficients $w\rho^{-1}$ and $w\rho^{-5}$. The measurements preserve the sectors. Their joint probabilities add to those of the optimal qubit strategy. This explains how a full-rank state can reproduce the optimum despite using twelve unequal weights. The first general upper-bound case left open here has five positive levels and a terminal two-plane.

## Verification

The full formula uses the five ideal zeros. The measurement convention, two-plane argument and direct-sum construction are in the [proof](PROOF.md). The two main declarations are `HardyExtension.four_level_measurement_maximum` and `HardyExtension.four_level_measurement_equality`. The [challenge](HardyExtension/Challenge.lean) defines the observables independently using Mathlib. The [solution](HardyExtension/Solution.lean) connects each statement to the proof modules.

From the repository root, install the toolchain in `lean-toolchain`, then run

```sh
lake exe cache get
lake build
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator
```

The last command is the sandboxed registry-style comparison on Linux with bubblewrap available. For a local replay on macOS, use `lake comparator --inadvisably-no-sandbox` with the same toolchain bin directory in PATH. The file `comparator.json` enables the independent nanoda kernel. The protected challenge uses placeholders for the statements under review. The solution and proof modules contain the proofs.

An independent Python calculation reconstructs all six measurements on 160 seeded complex cases, checks explicit maximizing measurements and verifies the symbolic coefficients. With NumPy, SciPy and SymPy installed, run `python3 -B checks/check_four_level_pairing.py`. The exact bounds come from Lean.

A separate [five-tick calculation](HardyClockPreparation.lean) gives the first tick at which a specified cubic dephasing channel can prepare the optimal qubit spectrum from a pure input. It is a conditional preparation result. The Hardy measurement theorem applies independently of how the state is prepared.

## Relation to earlier work

The scalar two-qubit proof is reused at its exact registered commit. This extension optimizes over higher-dimensional states at a fixed spectrum. [Earlier Palomar entry](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-30-000005) · [Pinned Lean proof](https://github.com/stalex444/hardy-ladder/tree/5764ec4a239fcb14f8de263372fc906bd217f349)

Boschi and colleagues introduced the ladder experiment. Liang, Spekkens and Wiseman discuss the three-setting binary-outcome problem in §IV.E. Chen, Mal, Tabia and Liang give numerical lower and upper bounds of 0.17455 and 0.17459 for this case in Table I(a). Their unrestricted-dimensional question remains open here. [Boschi et al.](https://doi.org/10.1103/PhysRevLett.79.2755) · [Liang et al.](https://arxiv.org/abs/1010.1273) · [Chen et al.](https://doi.org/10.1103/PhysRevA.109.042206)
