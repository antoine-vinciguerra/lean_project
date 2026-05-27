# Formalization of the Laplace Transform in Lean 4

This repository contains a formalization of the Laplace Transform, its operational properties, and its analytical inversion formula using the **Lean 4** proof assistant and **Mathlib**.

The formalization spans Banach space measure theory, complex contour integration, and the explicit evaluation of the Dirichlet integral.

## Project Report

A detailed mathematical report explaining the proof architecture, intermediate lemmas, and formalization methodology can be found here:

📄 **[laplace_transform_lean_project.pdf](./laplace_transform/docs/laplace_transform_lean_project.pdf)**

---

## Repository Structure

The source code is structured into four main Lean files:

* **`LaplaceTransformDef.lean`**
    Defines the generalized version of the Laplace transform (`GeneralizedLaplaceTransform`) for functions taking values in a complete normed ring / Banach space. It establishes structural properties such as linearity, additivity, and scalar commutation.
  * **`RealLaplaceTransform.lean`**
    Focuses on the classical Laplace transform for real-domain functions mapping to the complex plane and establishes the main inversion theorem (`IsInverseLaplace`). It bridges the complex contour line integration with the Dirichlet integral limits to recover the original function $f(t)$ from its transform.
* **`DirichletIntegral.lean`**
    Provides a standalone, rigorous proof of the Dirichlet integral (the improper integral of the sinc function from $0$ to $+\infty$ equals $\pi/2$). 
* **`LaplaceTransformProperties.lean`**
   It formalizes both truncated (`finiteLaplaceTransform`) and improper integrals, computes standard transforms ($1$, $t$, $e^{at}$), implements integration by parts (IBP), and proves the derivative operational theorem.


---

## Key Formalized Theorems

### 1. Standard Transforms
* **Constant function**: $\mathcal{L}\{1\} = \frac{1}{s}$ (for $\text{Re}(s) > 0$)
* **Identity function**: $\mathcal{L}\{t\} = \frac{1}{s^2}$
* **Exponential function**: $\mathcal{L}\{e^{at}\} = \frac{1}{s-a}$

### 2. Operational Calculi
* **First Derivative**: $\mathcal{L}\{f'\} = s\mathcal{L}\{f\} - f(0)$
* **Higher-order Derivatives**: Generalization to the $n$-th iterated derivative using induction (`finite_laplace_iteratedDeriv_eq`).

### 3. Asymptotics & Limits
* **Dirichlet Evaluation**: Formal proof that $\int_{0}^{+\infty} \text{sinc}^2(t) \, dt = \frac{\pi}{2}$ and its extension to the improper limit of $\text{sinc}(t)$.

### 4. Analytical Inversion
* **`IsInverseLaplace`**: Proves that under appropriate differentiability and exponential decay conditions, the Bromwich contour integral accurately recovers $f(t)$ almost everywhere.

## How to Verify and Compile the Project

This project is fully compatible with the standard Lean 4 toolchain. To fetch the pre-compiled Mathlib binaries matching this project's version and verify all proofs locally, open your terminal at the root of the repository and run:

```bash
lake exe cache get
lake build
