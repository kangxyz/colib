/-
Copyright (c) 2026 Andrew Yang, Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood

/-!
# Nisnevich neighborhoods isolating a quasi-finite branch

A separated morphism locally of finite type admits, at each quasi-finite point,
a pointed etale base neighborhood whose actual residue-field map is an
isomorphism and over which the chosen branch lies in a finite clopen piece.
The underlying point set of its fiber over the distinguished base point is a
singleton; the fiber need not be reduced.

The finite pointed neighborhood is the native construction
`Stacks.Flatness.exists_etaleNeighborhood_finiteAt`. Its specification retains
both the actual residue-field map and the unique branch. Separatedness makes
the finite open a closed subscheme, providing its open complement.

Implementation adapted from
`Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/Lifting/QuasiFinite.lean`
at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380, lines 72-170.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A quasi-finite branch of a separated, locally finite-type morphism becomes
finite and isolated after a pointed Nisnevich base change. The residue-field
isomorphism is the one induced by the neighborhood morphism itself. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/Lifting/QuasiFinite.lean:72-170"
  "adaptation" "Finite clopen branch with the actual residue-field map and unique point"]
theorem exists_nisnevich_isCompl_of_quasiFiniteAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f]
    {x : X} {s : S} (h : f x = s) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ (u : U), g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (V W : (pullback f g).Opens) (v : V),
      IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧
      pullback.fst f g v.1 = x ∧ pullback.snd f g v.1 = u ∧
      ∀ v' : V, pullback.snd f g v'.1 = u → v' = v := by
  subst s
  obtain ⟨N⟩ := Stacks.Flatness.exists_etaleNeighborhood_finiteAt f x
    (f.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx)
  obtain ⟨hfinite, ⟨v, hv, huniq⟩, hpoint⟩ := N.spec
  have : IsFinite (N.openSubscheme.ι ≫ pullback.snd f N.neighborhood.toBase) := hfinite
  have : IsFinite N.openSubscheme.ι :=
    .of_comp _ (pullback.snd f N.neighborhood.toBase)
  let W : (pullback f N.neighborhood.toBase).Opens :=
    ⟨(N.openSubscheme : Set (pullback (C := Scheme) f N.neighborhood.toBase))ᶜ,
      by simpa only [Scheme.Opens.range_ι] using
        N.openSubscheme.ι.isClosedMap.isClosed_range.isOpen_compl⟩
  refine ⟨N.neighborhood.scheme, N.neighborhood.toBase, inferInstance,
    N.neighborhood.point, N.neighborhood.map_point,
    N.neighborhood.isElementary_iff.mp N.elementary, N.openSubscheme, W, v,
    ?_, hfinite, (hpoint v hv).1, hv, huniq⟩
  simp [isCompl_iff, disjoint_iff, codisjoint_iff, W, SetLike.ext'_iff]

end AlgebraicGeometry
