# Short-Weierstrass curves

This package develops the affine equation `y^2 = x^3 + a*x + b`, together
with a point at infinity, over arbitrary fields in the existing algebra
hierarchy. It does not introduce a new field or group hierarchy.

## Theory map

* `shortWeierstrass`: the datatype `'a sw_point`, constructors
  `ECInfinity` and `ECAffine x y`, curve equation, discriminant,
  `ShortWeierstrassCurve`, `sw_on_curve` and `sw_points`.
* `swAssocAlgebra`: ring-based polynomial identities for secant and tangent
  equations and the associativity calculation, proved using `ringLib`.
* `shortWeierstrassGroup`: `sw_neg`, `sw_add`, the record `sw_group`, closure,
  inverses, commutativity and associativity. The main results are
  `short_weierstrass_group`, `short_weierstrass_abelian_group` and
  `short_weierstrass_finite_group`.
* `ellipticTorsion`: scalar laws, rational n-torsion as a kernel subgroup,
  generated groups, point orders and cofactor clearing.
* `ellipticMorphisms`: coordinatewise maps induced by field homomorphisms
  and isomorphisms, preserving group operations, scalars and torsion.
* `ellipticScaling`: invertible coordinate scaling between curves, with
  group, scalar, point-order and torsion transport.
* `shortWeierstrassSmall`: the example `y^2 = x^3 + 1` over `GF 5`.
  Its carrier has cardinality six and `ECAffine 2 2` has order six.
  The examples identify its rational 3-torsion and generated six-point
  group, transport points to an option field, and scale by `u = 2` to
  `y^2 = x^3 + 4`, preserving generator order six. They use existing
  primality facts, not new primality APIs.

## API semantics

`ShortWeierstrassCurve r a b` requires `Field r`, coefficients in
`r.carrier`, `char r <> 2`, `char r <> 3`, and nonzero discriminant
`-16 * (4*a^3 + 27*b^2)`. The generic results do not require a finite field;
`FiniteField r` is an additional premise of the finite-group theorem.

The point datatype is total: `ECAffine x y` can be constructed even when
coordinates are outside the field carrier or do not satisfy the equation.
`sw_on_curve` checks both coordinate membership and the equation;
`sw_points` is the resulting carrier and always contains `ECInfinity`.
Addition and negation are total HOL functions too. Their curve/group laws
require the stated curve and point-membership hypotheses, not merely
values of the point datatype.

Infinity is the identity. Negation sends `(x,y)` to `(x,-y)`. Adding affine
points with the same x-coordinate and opposite y-coordinates yields
infinity, including doubling a point with y-coordinate zero. Otherwise,
equal x-coordinates use the tangent slope `(3*x^2+a)/(2*y)` and distinct
x-coordinates use the secant slope `(y2-y1)/(x2-x1)`. These cases, including
infinity and inverse cases, are covered by the group and associativity
results; the formulas alone are not unconditional group laws off-carrier.

`sw_group r a b` is an existing `'a sw_point group` record with carrier
`sw_points r a b`, identity `ECInfinity` and operation `sw_add r a b`.
Use its existing `.exp` operation for natural-number scalar multiplication
and `order (sw_group r a b) P` for point order. `sw_group_inv` identifies
the existing derived group inverse with `sw_neg r P` on the carrier.
There is no separate scalar-multiplication or point-order API.

`sw_torsion_group r a b n` is the kernel of the nth-power endomorphism:
its carrier consists of points in `sw_points r a b` killed by `n`.
These are rational points over the given field, not all torsion points
over an algebraic closure. For `n = 0` it is the whole curve group; for
`n = 1` its carrier is just infinity. This is distinct from
`Generated (sw_group r a b) P`, the existing group API's named generated
group. Its subgroup and cyclicity results here assume a finite field;
its cardinality equals the order of `P` when that order is positive.
For a finite field, if the curve cardinality is `h * n`, cofactor clearing
by `h` lands in rational n-torsion. It need not give a nonidentity point
or a point in a chosen generator's subgroup. The stronger exact-order
result requires the input point itself to have order `h * n`, with
`h` and `n` positive.

`sw_map_point f` fixes infinity and maps `(x,y)` to `(f x,f y)`.
Given a source curve, a target field and `FieldHomo f r s`, it induces
an injective group homomorphism to coefficients `(f a,f b)`, preserving
scalar multiplication and sending rational n-torsion to rational n-torsion.
It need not cover all points over a larger target field. `FieldIso`
supports group isomorphism, point-order preservation and isomorphism of
the corresponding rational torsion groups.

`sw_scale_point r u` fixes infinity and sends `(x,y)` to
`(u^2*x,u^3*y)`. For `u IN r.carrier` and `u <> 0`, it gives a group
isomorphism from coefficients `(a,b)` to `(u^4*a,u^6*b)`, with inverse
scaling by `u^-1`, preserving scalar multiplication, order and torsion.
This changes affine coordinates and curve coefficients; it is not
homogeneous-coordinate scaling. These group and transport results retain
the stated curve, field and point-membership hypotheses.

## Native builds

With HOL configured and built, run from the repository root:

```sh
(cd examples/algebra/elliptic && ../../../bin/Holmake)
```

The native algebra aggregate also includes this directory:

```sh
(cd examples/algebra && ../../bin/Holmake)
```

The package is explicitly registered in the core parallel build's level-1
example set; it is not dependent on the level-2 algebra aggregate for
selftest coverage. Its local include paths use the sibling `field` and
`ring` directories.

## Scope and legacy development

The historical `examples/elliptic` directory is a separate development
with its own legacy field/group hierarchy and tooling. This package does
not import or modify that hierarchy; its field and group records come
from the current algebra libraries.

This package contains no projective-coordinate or complex-multiplication
development, cardinality certificates or concrete cryptographic instances.
The GF(5) examples illustrate the generic group and transport interfaces.
