# jensen-ladder

Scaffold for a planned formally verified result:

> **Target.** For every degree `1 ≤ d ≤ D₀`, the degree-`d` Jensen section
> of the Riemann ξ function is hyperbolic (all its zeros are real) —
> certified in Lean 4 with proved rational enclosures of the ξ moments.

Each section's hyperbolicity is a necessary condition for the Riemann
Hypothesis (via the Pólya–Jensen criterion); this repository will hold the
machine-checked certificates, the verified moment-enclosure layer, and the
manuscript, following the same standards as
[theorem-m](../theorem-m): zero `sorry`s, standard axioms only, external
kernel re-check, CI replay, and a numerical verifier that re-derives every
claim independently.

**Status: scaffold only — no mathematical claims yet.** The theorem
statement and `D₀` will be frozen after the numerical pre-certification
phase completes.

License: MIT.
