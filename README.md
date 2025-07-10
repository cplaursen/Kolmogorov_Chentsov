# The Kolmogorov-Chentsov theorem in Isabelle/HOL

## Abstract

Continuous-time stochastic processes often carry the condition of having
almost-surely continuous paths. If some process $X$ satisfies certain bounds on
its expectation, then the Kolmogorov-Chentsov theorem lets us construct
a modification of $X$, i.e. a process $X'$ such that $\forall t. X_t = X'_t$
almost surely, that has Hölder continuous paths.

In this work, we mechanise the Kolmogorov-Chentsov theorem. To get there,
we develop a theory of stochastic processes, together with Hölder
continuity, convergence in measure, and arbitrary intervals of dyadic
rationals.

With this, we pave the way towards a construction of Brownian motion. The work
is based on the exposition in [Achim Klenke's probability theory
text](https://link.springer.com/book/10.1007/978-3-030-56402-5)

## This repository

The theory presented in this repository is available from the [AFP](https://www.isa-afp.org/entries/Kolmogorov_Chentsov.html). Here we catalogue minor changes to be pushed in the next Isabelle release.

In order to inspect and edit this work, download (Isabelle)[https://isabelle.in.tum.de], and run Isabelle/jEdit with the HOL-Probability heap image loaded:

```
isabelle jedit -l HOL-Probability
```

The main theorem is under Kolmogorov_Chentsov.thy. We define general helper theorems under Kolmogorov_Chentsov_Extras.thy, and develop theories of stochastic processes, convergence in measure, holder continuity, and dyadic rationals in the correspondingly named files.
