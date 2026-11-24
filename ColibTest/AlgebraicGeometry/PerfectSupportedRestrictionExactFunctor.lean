module

import Colib.AlgebraicGeometry.KTheory.PerfectSupportedRestrictionExactFunctor

set_option autoImplicit false

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

universe u

local notation:max "W[" X "]" =>
  RingedSpace.perfectComplexesWaldhausen
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X))
local notation:max "R[" j "]" => perfectComplexesRestrictOpenImmersion j

variable {V X V' X' : Scheme.{u}} (j : V ⟶ X) (j' : V' ⟶ X')
  [IsOpenImmersion j] [IsOpenImmersion j'] (T : X.Opens) (T' : X'.Opens)
  {F : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := X.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
        (X := X'.toRingedSpace))}
  {H : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := T.toScheme.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
        (X := T'.toScheme.toRingedSpace))}
  {G : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := V.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
        (X := V'.toRingedSpace))}
  {I : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := (j ⁻¹ᵁ T).toScheme.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
        (X := (j' ⁻¹ᵁ T').toScheme.toRingedSpace))}
  (hf : IsExact (W[X]).cof (W[X]).weq (W[X']).cof (W[X']).weq F)
  (hh : IsExact (W[T.toScheme]).cof (W[T.toScheme]).weq
    (W[T'.toScheme]).cof (W[T'.toScheme]).weq H)
  (hg : IsExact (W[V]).cof (W[V]).weq (W[V']).cof (W[V']).weq G)
  (hi : IsExact (W[(j ⁻¹ᵁ T).toScheme]).cof (W[(j ⁻¹ᵁ T).toScheme]).weq
    (W[(j' ⁻¹ᵁ T').toScheme]).cof (W[(j' ⁻¹ᵁ T').toScheme]).weq I)
  (d : F ⋙ R[T'.ι] ≅ R[T.ι] ⋙ H)
  (e : G ⋙ R[(j' ⁻¹ᵁ T').ι] ≅ R[(j ⁻¹ᵁ T).ι] ⋙ I)
  (c : F ⋙ R[j'] ≅ R[j] ⋙ G)

variable (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
  (hcover' : ∀ x : X', x ∈ Set.range j' ∨ x ∈ T')

include c in
-- The actual inverse to excision commutes with the induced maps in degree zero.
example (x : PerfectSupportedK (j ⁻¹ᵁ T).ι 0) :
    KMap (perfectSupportedFunctorOfRestrictIso_isExact T.ι T'.ι hf hh d) 0
        ((perfectSupportedExcisionKEquiv j T hcover 0).symm x) =
      (perfectSupportedExcisionKEquiv j' T' hcover' 0).symm
        (KMap (perfectSupportedFunctorOfRestrictIso_isExact
          (j ⁻¹ᵁ T).ι (j' ⁻¹ᵁ T').ι hg hi e) 0 x) :=
  perfectSupportedExcisionInverse_natural_of_exactFunctors
    j j' T T' hf hh hg hi d e c hcover hcover' 0 x

variable [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace (j ⁻¹ᵁ T).toScheme]
  [CompactSpace V'] [QuasiSeparatedSpace V'] [CompactSpace (j' ⁻¹ᵁ T').toScheme]

attribute [local instance] HasDerivedCategory.standard

include hh hg d e c in
-- This compares the actual connective boundary from overlap degree one to ambient degree zero.
example :
    (PerfectMayerVietoris.connectingHom j' T' hcover' 0).comp (KMap hi 1) =
      (KMap hf 0).comp (PerfectMayerVietoris.connectingHom j T hcover 0) :=
  PerfectMayerVietoris.connectingHom_natural_of_exactFunctors
    j j' T T' hf hh hg hi d e c hcover hcover' 0
