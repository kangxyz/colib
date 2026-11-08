# Whole based-additivity transformation square

COL-0301 records the complete transformation square, not a release of its
supporting nerve or pushout helpers. COL-0296--COL-0301 were integrated into main
at the commit recorded below, whose sources and tests passed native CI.
Compilation and source correspondence remain distinct from independent
mathematical review; the CI result does not confer established review status.

## Actual statement and hypotheses

Let C and D have object universe u and morphism universe v, independently;
the source and target share u and v as in the original implementation. Let V
and W be their Waldhausen structures and assume binary coproducts in D.
For functors F,G,H,F',G',H' from C to D, retain both witnesses
IsCofibrationSequence V W a b and IsCofibrationSequence V W a' b'.
The three natural transformations etaF, etaG and etaH are pointwise W-weak.
Both squares commute: a >> etaG = etaF >> a' and
b >> etaH = etaG >> b'. No additional fibration theorem, cylinder structure,
strict chosen-zero equality, connectivity or canonical-comparison weakness
is a premise of the final square.

The domain is I × (I × |diagonal(delta.op ⋙ bisimplicialSSet V)|);
the codomain is |diagonal(bisimplicialSSet W)|. Here delta is the existing
ordinal subdivision, not an alternate K-theory model. The first coordinate
t is transformation time, the second s is additivity time, and x is an
arbitrary point of the subdivided realization. These coordinates stay
independent throughout the construction.

The actual pasting is prefix.symm.trans (middle.trans suffix). The identity
prefix is reversed once, the middle minimum-cut square follows, and the
separated endpoint square closes the path. With the existing trans clock,
these pieces occupy one half, one quarter and one quarter of additivity time.
No reassociation or second reversal is substituted. The sum track uses the
original quotient-first coproduct order, H before F.

## Four whole faces and the zero surface

- At s = 0 the square is the actual rebased middle transformation homotopy,
  after the original horizontal endpoint restriction, for every t and x.
- At s = 1 it is the actual normalized quotient-first sum transformation
  homotopy for every t and x.
- At t = 0 it is subdividedBasedAdditivityHomotopy V W a b hs for every s and x.
- At t = 1 it is subdividedBasedAdditivityHomotopy V W a' b' hs' for every s and x.
- At x = subdivisionBasepoint V it equals realizationPoint (diagonalZeroVertex W)
  for every pair t,s. This is the whole parameter square, not just its corners.

These are equalities of the actual parameterized maps, not merely equalities
of induced K-group maps. The final regression source includes four full-face
function equalities, a full-zero function equality and the literal pasting
identity. These regression modules were included in the successful integrated
native CI recorded below.

## Source and native owners

Implementation provenance is the existing bibliography key `quillen`, fixed
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The three principal originals are
Quillen/Waldhausen/Additivity/MixedTransformationSquare.lean (26 declarations),
EndpointTransformationSquare.lean (29), and BasedTransformationSquare.lean (16).
The generic transposedSquareHomotopyRel is included in that last count and
belongs to Colib.Topology.Homotopy.SquareBoundaryPaths. Categorical squares
belong to Colib.CategoryTheory.Waldhausen; realized and based squares belong
to Colib.KTheory.Waldhausen. Existing public imports preserve old consumers.

The supporting layers retain the actual pushout.map, gluing proof, independent
restrictions and cuts, chosen-zero conjugates, diagonal weak-grid square,
two inverse cylinder comparisons and all full faces and zero surfaces.
The coordinated overlays contain 28 production Lean files and three regression
modules with 23 examples (11 + 6 + 6); counts include edited existing owners.
Their source reports record 36 foundation declarations, 34 original pushout/mixed
transformation declarations plus three unchanged native moves, and all 71
original square declarations. Those inventories describe source correspondence,
not a newly compiled declaration total.

Seven native reference bindings attach only the final relative homotopy,
continuous square, four full-face theorems and fixed-zero theorem to COL-0301.
Their exact original declaration spans are 157–165, 168–173, 188–196,
199–206, 209–228, 231–250 and 253–272 in BasedTransformationSquare.lean.
The relation is adaptation: native namespaces/import ownership change;
hypotheses, maps, interval ordering and proof bodies are preserved. The
parameterized square is attributed to that implementation, not verbatim to a
classical paper. No new bibliography entry is needed.

## Verification boundary

Historical preparation input: 09c26aeb9905eea82fe3382373d3cedac798a52d, tree e8c4fbfb.
That metadata-preparation stage recorded normalized body correspondence and
text-level import closure checks, without running native checks. Such source
checks do not establish elaboration, definitional reduction, simp behavior,
universe inference, a native axiom audit or CI success.

The integrated sources and tests at
[`ea4dc640a5bec4e7eb49e0268c08c9f1fed1fc01`](https://github.com/kangxyz/colib/commit/ea4dc640a5bec4e7eb49e0268c08c9f1fed1fc01)
passed the repository's native checks in
[CI run 42435539991](https://github.com/kangxyz/colib/actions/runs/42435539991):
the `Build` and `Test, lint and axiom audit` jobs both succeeded. This
supersedes the uncompiled preparation status. `author_checked` continues to record source
correspondence only; independent mathematical review retains its own evidence
and checked span. No kernel-replay pass is claimed.
The coordinated lower-owner extractions were included in that integrated build.
No ring/scheme ownership moves or scalar, support, Laurent, Bass or
nonconnective consequences follow from this general result alone.
