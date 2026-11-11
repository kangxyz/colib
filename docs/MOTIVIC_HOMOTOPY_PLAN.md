# Motivic homotopy development plan

The first endpoint is natural Nisnevich representability for the motivic cohomology groups
already defined by Colib. Use `PresheafWithTransfers.motivicSheafComplex` and
`PresheafWithTransfers.motivicFiniteSheafComplex` as the coefficient complexes. The second
is the multiplication cone on the ordinary underlying integral complex. Preserve its integral
reduction and positive connecting map in comparisons. COL-1008 and COL-1007 give the
weight-one norm and graph formulas for checking the represented degree-one classes.
[Motivic Cohomology](library/chapters/motivic-cohomology.toml)

## Nisnevich representability

1. For a pointed simplicial presheaf apply objectwise reduced free abelianization, degreewise
   Nisnevich sheafification, and then normalized Moore chains. On the underlying pointed
   presheaf use Mathlib's simplicial circle to identify smash suspension with the actual
   reduced cone quotient. Record the cone map in the comparison.
2. Use the actual pointed Nisnevich neighborhoods of points of smooth schemes. Prove that
   these points are jointly conservative, and compare reduced normalized chains after taking
   each site fiber. An equivalence on the realizations of the stalk simplicial sets then
   induces a quasi-isomorphism of reduced sheaf chains. This makes their derived functor
   available on the localization of pointed simplicial presheaves.
3. For a cochain complex \(A\), shift its functorial K-injective resolution by \(p\).
   Apply inverse Dold–Kan to the resulting connective chain truncation.
   The zero point comes from the additive
   structure. Compare maps from a localized pointed presheaf to this object with derived
   maps from its reduced chains. On a representable \(X_+\), the reduced chain complex
   identifies with the free representing Nisnevich sheaf in degree zero. This gives natural
   bijections for both \(H^{p,q}(X,\mathbb Z)\) and \(H^{p,q}(X,\mathbb Z/n)\) using the
   existing complexes and pullbacks.
4. Extend the comparison to coefficient maps, including the integral reduction and the
   connecting morphism at the actual cone sign. Check the suspension degree shift and the
   resulting Bockstein on the represented classes. COL-1018 identifies the positive
   mod-\(n\) Bockstein as the connecting map of the actual
   \(K/n\to K/n^2\to K/n\) triangle and proves its square-zero formula on cochains.

The construction uses the Nisnevich localization and the specified K-injective resolutions.
The smooth-site specialization imports the existing motivic coefficient complexes. Keep the
generic point, chain, realization, and derived-category lemmas at their mathematical owners.
The Motivic Homotopy chapter contains the pointed constructions used for motivic homotopy
and the smooth-site representability results.
[Morel–Voevodsky, \(\mathbb A^1\)-homotopy theory of schemes](https://www.math.ias.edu/vladimir/node/65)
· [Voevodsky and Deligne, Lectures on motivic cohomology 2000/2001](https://arxiv.org/abs/0805.4436)

## Adapting the earlier Colib development

The earlier development at `6897d796398e` is the proof source for the pointed
presheaf, Nisnevich, affine-line, Čech, and Tate constructions. Its revert is
`6bd21f3`. Reuse the current reduced torus, transfer singular complex, ordinary
motivic complexes, and multiplication cone. Adapt the reduced Bockstein to the
positive connecting morphism and current reduction maps. Use the current
`SmoothSite.Contraction` projections and the native torus identity for the strict
Tate quotient. Recover the original collapse maps, distinguished-square
comparison, and Čech generators in that order. Match current Library identifiers
to the adapted mathematical endpoints.
[Earlier development](https://github.com/kangxyz/colib/commit/6897d796398ea31071d8dd84217b87fe68df54a8)
· [Revert](https://github.com/kangxyz/colib/commit/6bd21f3)

## Affine-line localization and the Tate suspension

1. In the Nisnevich homotopy category, localize at the actual pointed projections
   \((X\times\mathbb A^1)_+\to X_+\). The comparison in COL-1016 assumes invariance of
   reduced hypercohomology under every pointed cylinder projection. Identify the scheme
   projections with the cylinders on representables and prove the extension from the
   geometric tests to the required cylinders. To identify the entire mapping spaces, use
   the invariance in all degrees that occur as their homotopy groups. The strict-invariance
   migration supplies the corresponding sheaf-cohomology theorem. The comparison for the
   actual coefficient complexes also needs a truncation or finite Nisnevich cohomological
   dimension argument for passage from cohomology sheaves to hypercohomology.
2. Develop the pointed constructions for \((\mathbb G_m,1)\) and
   \((\mathbb P^1,\infty)\), with their actual maps. Compare the motivic Tate sphere with
   \(S^1\wedge(\mathbb G_m,1)\), and record the comparison on reduced chains. The geometric
   cofiber constructions and explicit maps in COL-1017 and the stalkwise quotient
   comparison in COL-1020 precede the coefficient locality proof.
3. Use the product with the Tate class to construct the bonding maps
   \(T\wedge K(\Lambda(q),2q)\to K(\Lambda(q+1),2q+2)\). Verify the actual exterior-product
   maps, base points, signs, and coefficient functoriality. Identify the simplicial
   suspension with cup product by the simplicial suspension class and the Tate suspension
   with cup product by the Tate class. For the stable representation, prove the loop
   comparison in the chosen motivic model and identify its represented cohomology.
   Voevodsky's cancellation theorem supplies the effective-motive comparison for tensoring
   with the Tate motive. Relate it to the bonding maps used here.
   [Voevodsky, Cancellation theorem](https://ems.press/books/dms/255/5073)

## Reduced powers and the norm-residue proof

Construct the total power on the unstable representatives, keeping the diagonal and the
finite-group action visible in the comparison with transfer complexes. Work at a prime
invertible in the base for the norm-residue application. Use Riou's relative smooth site
construction for well-definedness of the total power and his proof of Bockstein
vanishing for the symmetric-group power. Identify the operation's
coefficients and prove naturality, suspension compatibility, and the Cartan and Adem
relations used to form the Milnor operations. The proof of the mod-two case also needs
their action on Thom classes and the Margolis vanishing for reduced Čech cones. The
general-prime argument uses the comparison of its symmetric-power construction with
\(\beta P^n\) up to a nonzero scalar, with the hypotheses of Voevodsky's Theorem 3.8.
[Reduced power operations](https://arxiv.org/abs/math/0107109)
· [Riou, Opérations de Steenrod motiviques, §§3.6–3.7](https://arxiv.org/abs/1207.3121)
· [On 2-torsion in motivic cohomology](https://arxiv.org/abs/math/0107110)
· [On motivic cohomology with \(\mathbb Z/\ell\) coefficients](https://arxiv.org/abs/0805.4430)

## Comparison with later constructions

Voevodsky computes motives of unstable representatives and studies operations using derived
symmetric powers. This is the source for the unstable comparison needed in the general
norm-residue argument. Hoyois–Kelly–Østvær compute bistable operations and spectrum
cooperations in positive characteristic at primes invertible on the base. Their results
provide a later comparison for the stable model and specify what the spectrum should
recover. [Voevodsky, Motivic Eilenberg–MacLane spaces](https://pmihes.centre-mersenne.org/articles/10.1007/s10240-010-0024-9/)
· [Hoyois–Kelly–Østvær, The motivic Steenrod algebra in positive characteristic](https://arxiv.org/abs/1305.5690)

Framed recognition gives a different presentation of motivic infinite \(\mathbb P^1\)-loop
spaces. Comparing it with the present finite-correspondence and chain-complex construction
would need framed transfers and their compatibility with the existing finite
correspondences. Bachmann and Hopkins' November 2026 preprint addresses the
characteristic-prime case via a homotopical model for the Eilenberg–Mac Lane spaces, with
normed structures and \(\mathbb P^1\)-loop-space calculations as inputs. Treat its
characteristic-prime computations as a separate comparison target.
[Elmanto–Hoyois–Khan–Sosnilo–Yakerson, Motivic infinite loop spaces](https://arxiv.org/abs/1711.05248)
· [Bachmann–Hopkins, Motivic Eilenberg–Mac Lane spaces at the characteristic](https://arxiv.org/abs/2611.02320)
