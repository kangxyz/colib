# Colib

Colib formalizes cohomology and homotopy theory in algebraic geometry, including their
motivic and algebraic K-theoretic interfaces. It pins its mathematical dependencies to exact
commits of [Mathlib](https://github.com/leanprover-community/mathlib4) and
[Stacks](https://github.com/AxiomMath/Stacks).

## Library

The [Colib Library](https://kangxyz.github.io/colib/) connects results through mathematical
exposition in chapters and sections. Each permanent item gives its statement, scope,
Lean declarations, defining imports and precise literature references.

The [Library organization guide](docs/LIBRARY.md) covers chapter structure, mathematical
writing and references. See the [contribution guide](CONTRIBUTING.md) for adding a result
and its Lean declarations.

## Use and build

The pinned toolchain is Lean 4.35.0. Add the repository as a Lake dependency
using a Git checkout and an exact release commit.

```lean
import Colib
```

```sh
bash scripts/cache.sh
lake build Colib
lake test
bash scripts/check.sh
```

The [development guide](docs/DEVELOPMENT.md) owns checks and caches.
The [architecture](docs/ARCHITECTURE.md) owns mathematical organization.
The [migration plan](docs/MIGRATION.md) records subsequent Quillen and Motivic work.
The catalog's `author_checked` state records the author's source comparison.

## License

[Apache-2.0](LICENSE).
