# Colimit conversion at coniveau stage transitions

The affected declaration is `coniveauCohomologyTransition` in
`Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Stages`.
The source basis is Colib `5cbe5cbd7603e03431b55bac03741129117d4ef3`, Lean 4.35.0,
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and Stacks
`c496df0d9beea9deaeabcea8492605f9a0a2313b`.

For codimension bounds `a ≤ b`, inclusion of the support indices induces a
map from stage `b` to stage `a`. The term `colimit.pre F I` takes as source
the colimit of `I ⋙ F`, where `I` is the inclusion of indices and `F` is
the support diagram at bound `a`. The statement uses the original diagram at
bound `b`. Native job `100df0423db9537452280d271b2fcd49` at
`72d372bb3bfd8f74a0d9cc6a200d720ff8f533cd` hit the `whnf` limit of 800000
heartbeats while identifying these source types. The module also had a
separate stage-zero error. Its source SHA-256 was
`72b2b95b460f3840d7dc9be9d5526af9afb3ec6c53de0cc645203082888f081f`.

The repaired term applies `colimit.desc` to a cocone on the original
diagram at bound `b`. At a support `Z` the cocone map is the stage-`a`
injection at `I.obj Z`. Each naturality equation is `colimit.w` for the
corresponding inclusion of supports. The `colimit.ι_desc` equation
identifies the transition on every original generator.

Job `100df0423db9537452280d271b2fcd4b` at
`e38867eac50e11329b1b2c562a4e6ef181f6a034` cleared the transition error
and reached the separate stage-zero error. The source SHA-256 was
`f478adbd79dcea1c49186c26d8b38be9472aa4cecdc6b765fe333034855d6478`.
Job `100df0423db9537452280d271b2fcd4d` at
`4a5cc4b43df4f10fb8ad8028baf01c47d3c72c22` compiled `Stages` in 137 seconds
after moving the stage-zero comparison to its consuming module. Its source
SHA-256 was `5fda5869565a703650e5a869c60178e8c6c7b20c5a965f2e948634ade1846841`.
These results validate the transition and its generator formula on the cited
lock. The module timing includes the other stage declarations.

To reproduce at the successful revision, build the named stage module.

```sh
lake build Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Stages
```

## Distinguishedness after a middle quotient comparison

The same lock applies to `Filtration.Basic`. The triangle for nested
complementary opens has as middle object the motive of their composite arrow.
The support-stage diagram uses the original inclusion of the complement of
the larger support. Equality of the original open inclusions gives an arrow
isomorphism with identity domain and codomain components.

Native job `100df0423db9537452280d271b2fcd4e` at
`a670ce56664869166ea253395662ee81f7a4cbeb` hit a `whnf` limit of 900000
heartbeats in the concrete `supportPairTriangleIso` data declaration and
reported three deterministic kernel timeouts there. The module ran for
2065 seconds. The source SHA-256 was
`383eea8b579f9274d41d8eae3a41e29c674b903546212c98cdacfb2fd53ae3f4`.

In `feb32f0d7ffff0de0047e77b311cd9278973f9f5`, the generic lemma
`distinguished_change_middle` transports the property in a pretriangulated
category. For effective motives, first factor the original smooth-pair
arrows in the arrow category, then apply `effectivePairMotiveFunctor` and
`Functor.map_comp` to obtain the two typed equations. The original positive
`effectiveNestedPairBoundary` remains the third map. The same change
restores ordinary transparency in Basic and gives the colimit complex
typed projections.

Job `100df0423db9537452280d271b2fcd50` compiled Basic in 837 seconds, with
source SHA-256 `3c616edd042a2b8918e5f817a38158d29190728b16122b9ec8b4bbb89411a717`.
Its scope includes the signed pointwise sequence and all three exactness
statements on the colimit windows. The subsequent Restriction proof produced
separate diagnostics. Both times cover the individual module versions.

```sh
lake build Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Basic
```

## Functor transport in open-pair excision

The same lock applies to `Supports.Strata.OpenPairs`. The cover pushout
comes from the original transfer representables. Its comparison on relative
quotients is obtained by applying `transferPairCokernelFunctor` to the
original arrow. Shifted Hom on the effective pair motives is the
cohomology functor.

Job `7568170833774e6d9460f41e4a21ef30` at
`4b7d554e5134b956620c4a1532957926fc78e76a` timed out at `whnf` with
200000 heartbeats in three places. These were the application of the
pushout-to-cokernel lemma, the application to shifted Hom and the
substitution of the equality of complements. The module ran for 45
seconds with source SHA-256
`f0b721d81564c3134e21cbf3cc6570c30d2fa1261b15679bfc3e247a0c797d42`.
A scoped profiler attempt had stopped during import preparation and
produced zero declaration measurements.

The repair fixes each functor factorization as a typed equality before
specializing it. A generic lemma transports `IsIso` across that equality,
with the actual transfer quotient and represented cohomology functors as
arguments. The substitution of the complement equality takes place in an
arbitrary target category, and then specializes to the represented
functor. The applications use ordinary transparency.

Job `762d157b0c8d4f95bacc7c28d83150f5` at
`750fd587be1b5323c78b89bd3e09f4a8d8701127` compiled OpenPairs in 23
seconds with the same heartbeat budget. Its source SHA-256 was
`7f83e33665cbe75fea77769c52277afa0c643a2e6f88245dbce696c0264894ce`.
This checks the original maps and transport along equality of complements
at the cited version, before the geometric pair maps moved to
`Strata.OpenPairs.Maps`.

```sh
lake build Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.OpenPairs
```

## Associating ambient restriction diagrams

In `Supports/Filtration/Restriction.lean`, an ambient smooth open
immersion maps the original complementary-open arrows after inverse
image of supports. The support and window diagrams are composites
with the same contravariant represented cohomology functor.
Whiskering the restriction initially gives a different association
of these composites.

Job `100df0423db9537452280d271b2fcd53` at
`901ebcbc516bfbd84dd04cfc4d550a18efea8499` elaborated the maps of
the original arrow diagrams. The conversion to each native diagram
timed out at whnf at 550000 heartbeats in
`coniveauCohomologyDiagramRestrict` and
`coniveauRelativeSupportDiagramRestrict`. The source SHA-256 was
`c950dd0a02da480adf006529c750672b648606b01558935e56cce609f571d5f0`.

The repair uses `Functor.associator` and `Functor.isoWhiskerLeft`
on the native functor types. A generic lemma transports the
whiskered natural transformation through those comparisons. Their
components are identities. The typed representative equations
cancel the identities before the original restriction maps descend
to the two colimits. The represented cohomology functor stays opaque
while this file elaborates.

Job `100df0423db9537452280d271b2fcd54` at
`df03ee48da019dcd2242d7b7d12a6e28995d8bb7` built Restriction in
759 seconds and returned exit 0. This checks identity, composition
and the three adjacent naturality squares. The accepted source
SHA-256 is
`faae7d8179b22e0595f2492fb89f40f4270f056aa83eea7b4ecf7df066dce746`.
The same declaration bytes built in 743 seconds with the
`WindowData` extraction at `6c727b7aa24c32ab070b7a5ca6c6a7f7525f9a37`
in job `100df0423db9537452280d271b2fcd55`.

## Colimit descent for the point-to-window map

`Supports.Strata.PointWindow` uses open excision to compare the
stage for the closure of a point and its complement in an ambient
open with the actual supported cohomology on that open. The inverse
of this excision comparison followed by the original window injection
gives the stage map. The narrowed input imports the relative diagram
from `Supports.Filtration.WindowData`.

| Exact source | Native job | PointWindow result |
|---|---|---|
| `292ac8eba121a3696652bb75f4ffd88e24b428a6` | `db2d24ef79d04d20be6ca2e02b7dfa39` | Concrete descent around a generic cocone timed out in `whnf` at 200000 heartbeats and line 207. The module ran for 98 seconds. |
| `904df1630087c366be84bbddecc6a16f2a1aa9a6` | `08d2cebf43a04b52a8119424759dac2b` | Generic descent specialization timed out in `isDefEq` at 200000 heartbeats and line 214. The module ran for 97 seconds. |
| `2d30d0cee2da2d014e328c820e5541f8b6ddbd93` | `3f8111c1701e4574a1114922281d9fba` | Explicit diagrams, colimit instances and naturality reached a `whnf` timeout at 450000 heartbeats and line 218. The module ran for 95 seconds with two Lake threads. |
| `f87f7e256d69a3eb278055420d4541c6f5fafa4a` | `dd9da55f9f6e47cfabc165518d984b01` | Separate stage maps, inverse naturality and cocone built PointWindow in 140 seconds with two Lake threads and default heartbeats. The downstream PointProjection had its own failure. |

The scoped profiler `d195044b7d0248aaa45c51690277bf90` on the
third source stopped on out-of-date imports during preparation and
measured zero declarations. The durations describe successive proof
versions with different term structure and allowances.

In the accepted proof, separate declarations give the inverse-excision
stage maps, their naturality, and the cocone on the original neighbourhood
diagram. The final definition applies `colimit.desc` to the cocone.
Its generator formula applies `colimit.ι_desc` to the original
injections. The accepted source SHA-256 is
`b6e64f756212672d245a97db8408a43309bba31ae88e63cb0df793c81693572a`,
also retained at `85820216014b55650814333ee3c3b4d04afdfa89`.

## Finite generation by the point groups

In `Supports.Strata`, refine the lower support so the
codimension points give disjoint strata. The effective relative
motives of a finite open cover form a coproduct. Precomposition
with its original arrows detects a cohomology class. The matching
point arrows are open-excision isomorphisms, and the crossed arrows
factor through a zero relative pair. The finite class sum maps
through the original point coproduct into the coniveau window.

| Exact source | Native job | Strata result |
|---|---|---|
| `6f4b87ee29cc21b7f02953e31b3fdfcf2d2bdc0f` | `00f723854cee456aada0319b4db88038` | The Abelian instance name collided on import. Give the finite cover's existing local instance an explicit name. |
| `c37045e3e95d847d4ed26868f9d2ac20dacd8f19` | `d98cc5dd284444ea859bca9e5d5db9cf` | The combined stage generation proof timed out in `whnf` at 200000 heartbeats. Module time 38 seconds. |
| `42e3b87c85a351cd8da0e7ec7bbca8db0639c079` | `cee03b352f184aefb1320f2262dac71a` | Splitting the stage proof isolated four concrete cohomology conversions and an unused-variable diagnostic. Module time 77 seconds. |
| `f766dc33d64ceb307041cc7897316b87d0814a33` | `41053cd0111642f2a691aa69127be1c9` | Separate geometry and typed stage maps left one timeout in `stageCover_separates` at 200000 heartbeats. Module time 166 seconds. |
| `6f01234c8d9fcbc55e570eb13063e107699981cc` | `ed567f2a6b2345f49a7dd0c28260f735` | Generic represented separation elaborated. Its specialization timed out at 200000 heartbeats. Module time 165 seconds. |
| `b9cd65a84a9415be31913186f8804dd0e996f1ca` | `8dcaf2d3fa054fbca74c0575fc4a8782` | The original cofan specialization elaborated. The sole diagnostic was the concrete motive hypotheses inherited by the generic lemma. Module time 186 seconds. |

The repaired version proves the geometry outside the motive context
and computes the finite class sum in the original abelian groups.
Separation uses a generic coproduct and a typed comparison with
represented Hom. A separate declaration supplies the original
effective cofan. The final specialization has a local 500000
heartbeat budget. Moving the generic lemma before the motive
variables clears the scope diagnostic.

At `affac1efe26fadc1e025d5594f12ae9ab321aa06`, native job
`874a4acaff3749bab677126bb8537f03` built Strata in 187 seconds as a
dependency of `Gersten.CousinSheaves.Window`, with two Lake threads.
The accepted source SHA-256 is
`76e395c3fbf37406dc1f49d658963732e7277cad74c10465be24a550162a36db`.
The durations describe successive proof versions under the same
toolchain and dependency pins.

## Naturality statements in declaration lint

At `d762f846c3c297f943d3f7aa3091f534833c9b8a`, remote job
`d762f846c3c297f943d3f7aa3091f534` built all 33,972 production
targets and passed the package tests and axiom audit. Full
declaration lint reported three deterministic timeouts at its
200000 heartbeat budget. Batteries `checkType` applies
`isTypeCorrect` to the stored declaration type under its default
reducibility.

| Private statement | File | Timeout |
|---|---|---|
| `supportPairCohomologyBoundary_naturality` | `Supports/Filtration/Basic.lean` | `isDefEq` |
| `pointSupportImageRestriction_naturality` | `Supports/PointSupport/OpenRestriction.lean` | `whnf` |
| `pointSupportWindowRestriction_naturality` | `Supports/Strata/PointWindow.lean` | `whnf` |

For the boundary, give the two triangle maps their original types in
each consumer and apply the generic `representedBoundary_naturality`.
For the two point comparisons, retain the componentwise squares inside
`NatIso.ofComponents`. The image comparison takes the colimit of that
natural isomorphism. For the window comparison, inverse naturality
gives the actual square with the stage maps before the colimit
injection. The public generator formulas keep the original
component maps. Full declaration lint tests the resulting declaration
types at the same limit.

## Opposite triangles in the closed-support spectral object

`Supports.SpectralSequence.ClosedSupports` moves the middle object of
each original nested-open triangle through the identity-component
arrow isomorphism. The spectral-object field requires an opposite
triangle on the exact coface maps. In the first revision the kernel
expanded the effective motive at that field. The second revision
moved the conversion to a separate concrete theorem and hit the
elaborator limit there. The direct `rfl` of the represented
connecting map also timed out in the kernel.

| Source revision | Native job | ClosedSupports result |
|---|---|---|
| `e64c6549ebab486a1aab3c923d5e2ce2d23e2a2b` | `ca111ed20a112026bc60de0000000003` | Kernel timeout in the distinguishedness field after 689 seconds with two Lake threads. |
| `e117d027d194601ad72f1b31ec18e3c1d6f1b3e7` | `ca111ed20a112026bc60de0000000005` | Concrete opposite-triangle comparison timed out in `whnf` at 900000 heartbeats. The boundary comparison timed out in the kernel. Module time 491 seconds with one thread. |
| `207f75e7e6ae46498481de839f4e9aa08eef865b` | `ca111ed20a112026bc60de0000000006` | Exit 0 after building the leaf in 572 seconds with two threads. |

The accepted version restores the original positive middle comparison.
The generic `ofOppositeBoundaries` constructor takes an arrow diagram,
the typed signed boundary and the positive distinguished triangles.
It applies `op_distinguished` in the abstract category. The
represented connecting-map calculation also runs in the abstract
category, using that the two triangles have the same endpoints and
third map. The accepted file SHA-256 is
`1144ca4512ce5f91bc3871d288f653e9da4ca17e4420c0c5825b7f1c2c3b8222`.

```sh
lake build Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.ClosedSupports
```

## Weakening relative window bounds

At `75c310abfc08d9c4beb9f609d626d45dbd094960`, the two-thread
job `75c310abfc08d9c4beb9f609d626d401` ran `WindowColimits` for
59 seconds. Applying `colimit.pre` timed out in `isDefEq` at
200000 heartbeats while identifying its composite diagram with
the original source diagram.

The repaired map uses `colimit.desc` on a cocone typed over the
original source diagram. Its legs are the target injections for the
same supports with weakened bounds. It derives naturality from
`colimit.w` and the generator formula from `colimit.ι_desc`.
With the same dependency pins, job `fa8a2a9b14228f7cab2766970a26d0ba`
at `fa8a2a9b14228f7cab2766970a26d0bade2fc220` built the repaired
`WindowColimits` in 54 seconds and its `SpectralObject` consumer in
13 seconds with one thread. Separate modules failed in that job.
The accepted `WindowColimits.lean` file SHA-256 is
`b59285eb39c15d479911d37055a64c4fe528ac37e885e458869ee7aae7b50aab`.

```sh
lake build Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.WindowColimits.SpectralObject
```

## Composing the weakening and absolute stage maps

In `AbsoluteWindows` the weakening square compares four maps on
coniveau colimits. Native job `d59700ca8f646df64203c9f2252ba399`
timed out at 750000 heartbeats in `whnf` in the concrete square
and reported a universe error in its generated reassociation.
The module ran for 86 seconds.

Give the categorical composition lemma the four typed generator
laws. Keep the represented cohomology functor locally opaque and
omit the unused generated reassociation. At
`b4684f92d3d478313d64b663b6246f93c286f6f6`, native job
`30c0e43802c048e18b1d92f0f1b54562` checked the exact repaired
leaf in 43 seconds at the same heartbeat limit, with one thread.
The current file has Git blob `08e789e10f7ef54939e7c3ec15ae3fb677a25e7e`.
This comparison measures the changes together.

## Comparing the signed representative boundaries

`Boundary.Representatives` compares the localization boundary of
a closed-support flag beginning at the empty support with the
original boundary into the absolute support group followed by
restriction. The first comparison was made in the concrete
effective motive category with both triangles and all coefficient
instances in scope.

New Lit job `022b776d393caec06f8a709d9186fb07` at
`022b776d393caec06f8a709d9186fb07045d93a3` reported two `whnf`
timeouts during the 221-second module build. The scoped heartbeat
profile `684f336daebc4b6c9323ac85dcc19ede` on the same source timed
out after recording 650013 heartbeats for the geometry equation
and 900015 for the represented comparison. Its generic
postcomposition proof used 331 heartbeats.

The repair factors the geometry equation through the actual
naturality of the nested-pair boundary with identity first map.
It proves the shifted Hom equality in an abstract category and
then passes the two original signed representative formulas to it.
The graph and transfer representable stay locally opaque during
the specialization. Job `9b2cee56bd959cf364e309f9104cdb58` at
`9b2cee56bd959cf364e309f9104cdb58684de132` built the repaired
leaf in 232 seconds using the default eight threads. The checked
file has Git blob `83af1d81900215877af89c57237fdd16175dd945`.

```sh
lake build Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.Boundary.Representatives
```

The upper `Boundary` comparison also timed out in `whnf` at
900000 heartbeats in the same job, after 208 seconds. Its
repair passes the four typed colimit generator equations to
an abstract categorical proof. The resulting `Boundary.lean`
blob `829218ec34ee5fe6aa7466e7ae923cd59719c1d4` compiled in
92 seconds in job `5023170fe74c37b72e6bdd76752afcae` at
`5023170fe74c37b72e6bdd76752afcaee45e6c65`. That job also
built `FirstPage` in 24 seconds and the umbrella in 10 seconds
with the same native default of eight threads.

## Typing the coniveau generators for declaration lint

Job `06be681ec05efef6c6cfaf24026ffab5` at
`06be681ec05efef6c6cfaf24026ffab58744b712` built all 34,165
production targets. The `checkType` pass over 118,383
declarations timed out at 200000 heartbeats in
`closedSupportSpectralObject_δ_bot`, `ι_coniveauWindowMap`,
and the latter's generated reassociation.

Name the original flag boundary and weakened-pair injection
as morphisms with the literal relative-diagram endpoints.
The equations use these typed maps. The weakening proof
uses its original cocone legs directly and omits the unused
reassociation. The flag comparison uses the same signed
boundary and original support restriction.
