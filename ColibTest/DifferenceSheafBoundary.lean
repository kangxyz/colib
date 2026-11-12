module

import Colib.AlgebraicGeometry.Divisors.DifferenceSheafBoundary

/-!
# Tests for the specified divisor-difference boundary trivialization
-/

open CategoryTheory AlgebraicGeometry Stacks.Divisors

universe u

-- The unit ideal, not the zero ideal, cuts out the empty inverse-image divisor.
example {X Y : Scheme.{u}} (i : X ⟶ Y) (D : Y.IdealSheafData)
    (h : ∀ x : X, i x ∉ D.support) : D.comap i = ⊤ :=
  comap_eq_top_of_avoids_support i D h

-- The specified map is the actual pullback comparison followed by empty-divisor evaluation.
example {X Y : Scheme.{u}} (i : X ⟶ Y) (D E : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsPullbackDefined i D] [IsPullbackDefined i E]
    (hD : D.comap i = ⊤) (hE : E.comap i = ⊤) :
    differenceSheafBoundaryIsoOfComapEqTop i D E hD hE =
      differenceSheafPullbackIso i D E ≪≫
        eqToIso (congrArg₂ differenceSheaf hD hE) ≪≫ differenceSheafTopIso X := rfl

-- A nonzero square-zero section is explicitly allowed on the original affine boundary.
example (B : Type u) [CommRing B] (b : B) (_hb : b ^ 2 = 0) (_hb0 : b ≠ 0)
    {Y Z W : Scheme.{u}} (i : Spec (CommRingCat.of B) ⟶ Y)
    (s : Z ⟶ Y) (t : W ⟶ Y) [IsClosedImmersion s] [IsClosedImmersion t]
    [IsEffectiveCartierDivisor s.ker] [IsEffectiveCartierDivisor t.ker]
    (hs : Disjoint (Set.range i) (Set.range s))
    (ht : Disjoint (Set.range i) (Set.range t)) :
    Nonempty ((Scheme.Modules.pullback i).obj (differenceSheaf s.ker t.ker) ≅
      SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :=
  ⟨differenceSheafBoundaryIsoOfDisjointRange i s t hs ht⟩

#print axioms Stacks.Divisors.differenceSheafBoundaryIso
#print axioms Stacks.Divisors.differenceSheafBoundaryIsoOfDisjointRange
