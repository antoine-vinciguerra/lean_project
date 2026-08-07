# Dirichlet Integral and Lobachevsky's Formula in Lean 4

Lean 4 formalization of the Dirichlet integral, its classical applications, and Lobachevsky's integral formula.

## Contents

The project includes:

- the formalization of the Dirichlet integral;
- the Dirichlet cutoff and its convergence to the Heaviside function;
- quadratic trigonometric integral identities;
- Lobachevsky's integral formula;

## Dependencies

This project uses [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

## Project Report

A detailed mathematical report explaining the proof architecture, intermediate lemmas, and formalization methodology can be found here:

📄 [Dirichlet_integral.pdf](https://github.com/antoine-vinciguerra/lean_project/blob/main/Dirichlet%20Integral/docs/Dirichlet_integral.pdf)

## Project Structure

Dirichlet Integral/
├── DirichletIntegral.lean
├── DirichletIntegralApplications.lean
└── LobachevskyFormula.lean

`DirichletIntegral.lean` contains the formal proof of the Dirichlet integral and the evaluation of the squared sinc integral.

`DirichletIntegralApplications.lean` develops consequences of the Dirichlet integral, including the Dirichlet cutoff, the Heaviside convergence theorem, and several trigonometric integral identities.

`LobachevskyFormula.lean` contains the formalization of Lobachevsky's integral formula using Fourier approximation on the additive circle.

## License

Add the license for this repository here.

Note that your license applies only to material for which you hold the necessary rights. Code adapted from another repository remains subject to the rights and licensing terms of its original authors.
