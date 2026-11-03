# Short-Weierstrass curves

This package develops `y^2 = x^3 + a*x + b`, with a point at infinity,
over fields in the existing algebra hierarchy.

## Theories

* `shortWeierstrass` defines points, the curve equation, discriminant,
  curve predicate, and carrier.
* `swAssocAlgebra` proves the ring identities used for associativity.
* `shortWeierstrassGroup` defines point addition and negation, and proves
  the group, Abelian-group, and finite-group results.
* `shortWeierstrassSmall` instantiates `y^2 = x^3 + 1` over `GF 5`, yielding
  a six-element Abelian group with generator `ECAffine 2 2`.

## Assumptions and API

`ShortWeierstrassCurve r a b` requires a field with coefficients in its
carrier, characteristic other than 2 or 3, and nonzero discriminant.
Finiteness is required only by the finite-group theorem.

Points, addition, and negation are total HOL values and functions; their
curve and group laws require the corresponding membership hypotheses.
`sw_group r a b` uses `ECInfinity` as its identity. Its existing `.exp`
operation provides natural-number scalar multiplication.

## Build

From the repository root:

```sh
(cd examples/algebra/elliptic && ../../../bin/Holmake)
```

The historical `examples/elliptic` development is separate and uses its
own legacy field and group hierarchy.
