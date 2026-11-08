/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectJoint
public import Colib.CategoryTheory.ExactCategory.Functor.Pushouts

/-! # Exact functors on native perfect complexes

Every ambient monomorphism between native perfect complexes has a perfect cokernel.
Consequently the inherited admissible monomorphisms are precisely the existing
ambient monomorphisms. This comparison is used only to prove preservation results;
the original Waldhausen structure, its zero, and its weak equivalences stay unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.RingedSpace
universe u
variable (X : RingedSpace.{u, u})
local instance : HasFiniteBiproducts
    (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ) :=
  Abelian.hasFiniteBiproducts (C := CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ)

local instance : HasFiniteBiproducts
    (ObjectProperty.FullSubcategory (IsPerfectComplex (X := X))) :=
  by
    let := isPerfectComplex_closedUnderFiniteProducts X
    exact ExactSubcategory.subcategoryHasFiniteBiproducts (IsPerfectComplex (X := X))

/-- Admissibility in the inherited exact structure is exactly ambient monicity. -/
theorem perfectComplexes_inflation_iff
    {K L : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X))} (f : K ⟶ L) :
    (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ))
      (IsPerfectComplex (X := X))).inflation f ↔ Mono f.hom := by
  constructor
  · rintro ⟨Q, p, w, hS⟩
    exact hS.mono_f
  · intro hf
    let : Mono f.hom := hf
    let S := ShortComplex.mk f.hom (cokernel.π f.hom) (cokernel.condition f.hom)
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact f.hom }
    exact ⟨⟨cokernel f.hom, isPerfectComplex_X₃_of_shortExact hS K.property L.property⟩,
      ObjectProperty.homMk (cokernel.π f.hom),
      ObjectProperty.hom_ext _ (cokernel.condition f.hom), hS⟩

/-- A lifted additive functor preserving ambient short exact sequences and actual
quasi-isomorphisms is exact for the existing ambient-monomorphism structures. -/
theorem perfectComplexes_lift_isExact
    (Q : ObjectProperty (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ))
    (hQ : Waldhausen.CofibrationClosedSubcategory.Closed
      (Waldhausen.complexes (StrictlyPerfect.OXMod.{u, u, u} X)) Q)
    (F : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X)) ⥤ Q.FullSubcategory)
    [F.Additive]
    (hF : ∀ S : ShortComplex (ObjectProperty.FullSubcategory (IsPerfectComplex (X := X))),
      (S.map (ObjectProperty.ι (IsPerfectComplex (X := X)))).ShortExact →
        ((S.map F).map Q.ι).ShortExact)
    (hweak : ∀ {K L : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X))}
      (f : K ⟶ L), QuasiIso f.hom → QuasiIso (F.map f).hom) :
    Waldhausen.IsExact (perfectComplexesWaldhausen X).cof
      (perfectComplexesWaldhausen X).weq
      (Waldhausen.CofibrationClosedSubcategory.waldhausenStructure
        (Waldhausen.complexes (StrictlyPerfect.OXMod.{u, u, u} X)) Q hQ).cof
      (Waldhausen.CofibrationClosedSubcategory.waldhausenStructure
        (Waldhausen.complexes (StrictlyPerfect.OXMod.{u, u, u} X)) Q hQ).weq F := by
  let EF : ExactCategory.ExactFunctor
      (ExactSubcategory.exactStructure
        (abelianExactStructure (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ))
        (IsPerfectComplex (X := X)))
      (abelianExactStructure (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ)) :=
    { toFunctor := F ⋙ Q.ι
      map_conflation := hF }
  refine { zero := fun h => F.map_isZero h, cofibration := ?_, weak := hweak, pushout := ?_ }
  · intro K L f hf
    exact (abelianExactStructure_inflation_iff _ _).1
      (EF.map_inflation f ((perfectComplexes_inflation_iff X f).2 hf))
  · intro A B D T i f g k hi h
    apply IsPushout.of_map_of_faithful Q.ι
    exact EF.map_isPushout ((perfectComplexes_inflation_iff X i).2 hi) h

end AlgebraicGeometry.RingedSpace
