/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietorisBoundaryNaturality
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenBoundaryNaturality
public import Colib.AlgebraicGeometry.Modules.PerfectOpenExactSquare

/-! # Naturality of supported restriction and the Mayer–Vietoris boundary -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

local notation:max "W[" X "]" =>
  RingedSpace.perfectComplexesWaldhausen
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X))
local notation:max "R[" j "]" => perfectComplexesRestrictOpenImmersion j

section

variable {A B X Y : Scheme.{u}} (i : A ⟶ X) (k : B ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion k]
  {F : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := X.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
        (X := Y.toRingedSpace))}
  {G : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := A.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
        (X := B.toRingedSpace))}
  (hf : IsExact (W[X]).cof (W[X]).weq (W[Y]).cof (W[Y]).weq F)
  (hg : IsExact (W[A]).cof (W[A]).weq (W[B]).cof (W[B]).weq G)
  (e : F ⋙ R[k] ≅ R[i] ⋙ G)

include hf hg e in
/-- Restrict the given ambient functor to the actual supported full categories. -/
def perfectSupportedFunctorOfRestrictIso :
    (perfectSupported i).FullSubcategory ⥤ (perfectSupported k).FullSubcategory :=
  perfectSupportedToAcyclic i ⋙
    acyclicFunctor (perfectOpenNested i) (perfectOpenNested k)
      (perfectOpen_coarseExact_of_restrictIso i k hf hg e) ⋙ perfectAcyclicToSupported k

/-- The actual supported functor inherits exactness from the given fine and open functors. -/
theorem perfectSupportedFunctorOfRestrictIso_isExact :
    IsExact (perfectSupportedWaldhausen i).cof (perfectSupportedWaldhausen i).weq
      (perfectSupportedWaldhausen k).cof (perfectSupportedWaldhausen k).weq
      (perfectSupportedFunctorOfRestrictIso i k hf hg e) :=
  (perfectSupportedToAcyclic_exact i).comp
    ((acyclicFunctor_exact (perfectOpenNested i) (perfectOpenNested k) hf
      (perfectOpen_coarseExact_of_restrictIso i k hf hg e)).comp
        (perfectAcyclicToSupported_exact k))

/-- The actual supported functor commutes with the fine inclusion that forgets support. -/
theorem perfectSupportedKMap_comp_functorOfRestrictIso (n : ℕ) :
    (perfectSupportedKMap k n).comp
        (KMap (perfectSupportedFunctorOfRestrictIso_isExact i k hf hg e) n) =
      (KMap hf n).comp (perfectSupportedKMap i n) := by
  have h₁ := KMap_comp_KMap (perfectSupportedFunctorOfRestrictIso_isExact i k hf hg e)
    (perfectSupportedInclusion_isExact k) n
  have h₂ := KMap_comp_KMap (perfectSupportedInclusion_isExact i) hf n
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  exact KMap_eq_of_iso _ _ (eqToIso (by rfl)) n

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace A]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace B]

attribute [local instance] HasDerivedCategory.standard

/-- The localization boundary is natural for the actual fine and supported functors. -/
theorem perfectQcqsConnectingHom_natural_of_restrictIso (n : ℕ) :
    (perfectQcqsConnectingHom k n).comp (KMap hg (n + 1)) =
      (KMap (perfectSupportedFunctorOfRestrictIso_isExact i k hf hg e) n).comp
        (perfectQcqsConnectingHom i n) := by
  let hcoarse := perfectOpen_coarseExact_of_restrictIso i k hf hg e
  let : Fact (OpenDerivedImage.HasDerivedRoofs i) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs i⟩
  refine MonoidHom.ext fun x => ?_
  obtain ⟨a, ha⟩ := (OpenDerivedImage.relativeKRestrictEquiv i
    (OpenDerivedImage.hasPerfectComplements_of_qcqs i) n).surjective x
  change perfectOpenKRestrict i (n + 1) a = x at ha
  subst x
  have hres : perfectOpenKRestrict k (n + 1) (KMap hcoarse (n + 1) a) =
      KMap hg (n + 1) (perfectOpenKRestrict i (n + 1) a) :=
    DFunLike.congr_fun (perfectOpenKRestrict_natural i k hcoarse hg (n + 1) e) a
  have hsrc : perfectQcqsConnectingHom i n (perfectOpenKRestrict i (n + 1) a) =
      perfectOpenConnectingHom i n a :=
    DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative i n) a
  have htgt : perfectQcqsConnectingHom k n
        (perfectOpenKRestrict k (n + 1) (KMap hcoarse (n + 1) a)) =
      perfectOpenConnectingHom k n (KMap hcoarse (n + 1) a) :=
    DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative k n)
      (KMap hcoarse (n + 1) a)
  let hs := perfectSupportedFunctorOfRestrictIso_isExact i k hf hg e
  have hrel : KMap hs n (perfectOpenConnectingHom i n a) =
      perfectOpenConnectingHom k n (KMap hcoarse (n + 1) a) :=
    DFunLike.congr_fun
      (perfectOpenConnectingHom_natural i k hf hcoarse hs n (eqToIso (by rfl))) a
  exact (congrArg (perfectQcqsConnectingHom k n) hres.symm).trans
    (htgt.trans (hrel.symm.trans (congrArg (KMap hs n) hsrc.symm)))

end

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

include c in
set_option backward.isDefEq.respectTransparency false in
/-- The actual ambient isomorphism lifts to the actual supported restriction square. -/
def perfectSupportedRestrictionIsoOfExactFunctors :
    perfectSupportedFunctorOfRestrictIso T.ι T'.ι hf hh d ⋙ perfectSupportedRestrict j' T' ≅
      perfectSupportedRestrict j T ⋙
        perfectSupportedFunctorOfRestrictIso (j ⁻¹ᵁ T).ι (j' ⁻¹ᵁ T').ι hg hi e :=
  Functor.fullyFaithfulCancelRight (perfectSupported (j' ⁻¹ᵁ T').ι).ι
    (Functor.isoWhiskerLeft (perfectSupportedInclusion T.ι)
      (Functor.isoWhiskerRight c
        (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := V'.toRingedSpace)))))

include c in
/-- The K-theory square follows from the specified isomorphisms, not extra K-map hypotheses. -/
@[colib_tag "COL-1341", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenFunctorMayerVietoris.lean:43-54"
  "adaptation" "Naturality of the actual supported restriction under exact functors."]
theorem perfectSupportedRestrictionKMap_natural_of_exactFunctors (n : ℕ) :
    (perfectSupportedKRestrict j' T' n).comp
        (KMap (perfectSupportedFunctorOfRestrictIso_isExact T.ι T'.ι hf hh d) n) =
      (KMap (perfectSupportedFunctorOfRestrictIso_isExact
        (j ⁻¹ᵁ T).ι (j' ⁻¹ᵁ T').ι hg hi e) n).comp (perfectSupportedKRestrict j T n) := by
  unfold perfectSupportedKRestrict
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _
    (perfectSupportedRestrictionIsoOfExactFunctors j j' T T' hf hh hg hi d e c) n

variable (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
  (hcover' : ∀ x : X', x ∈ Set.range j' ∨ x ∈ T')

include c in
/-- The actual inverse to supported restriction commutes with the given supported functors. -/
@[colib_tag "COL-1341", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenFunctorMayerVietoris.lean:59-71"
  "adaptation" "Naturality of the actual inverse to supported excision."]
theorem perfectSupportedExcisionInverse_natural_of_exactFunctors (n : ℕ)
    (a : PerfectSupportedK (j ⁻¹ᵁ T).ι n) :
    KMap (perfectSupportedFunctorOfRestrictIso_isExact T.ι T'.ι hf hh d) n
        ((perfectSupportedExcisionKEquiv j T hcover n).symm a) =
      (perfectSupportedExcisionKEquiv j' T' hcover' n).symm
        (KMap (perfectSupportedFunctorOfRestrictIso_isExact
          (j ⁻¹ᵁ T).ι (j' ⁻¹ᵁ T').ι hg hi e) n a) := by
  apply (perfectSupportedExcisionKEquiv j' T' hcover' n).injective
  have h := DFunLike.congr_fun
    (perfectSupportedRestrictionKMap_natural_of_exactFunctors j j' T T' hf hh hg hi d e c n)
    ((perfectSupportedExcisionKEquiv j T hcover n).symm a)
  change perfectSupportedExcisionKEquiv j' T' hcover' n
      (KMap (perfectSupportedFunctorOfRestrictIso_isExact T.ι T'.ι hf hh d) n
        ((perfectSupportedExcisionKEquiv j T hcover n).symm a)) =
    KMap (perfectSupportedFunctorOfRestrictIso_isExact (j ⁻¹ᵁ T).ι (j' ⁻¹ᵁ T').ι hg hi e) n
      (perfectSupportedExcisionKEquiv j T hcover n
        ((perfectSupportedExcisionKEquiv j T hcover n).symm a)) at h
  simpa only [MulEquiv.apply_symm_apply] using h

variable [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace (j ⁻¹ᵁ T).toScheme]
  [CompactSpace V'] [QuasiSeparatedSpace V'] [CompactSpace (j' ⁻¹ᵁ T').toScheme]

attribute [local instance] HasDerivedCategory.standard

include hh hg d e c in
/-- The given exact functors and actual restriction isomorphisms commute with the
Mayer–Vietoris boundary, including the map into degree zero. -/
@[colib_tag "COL-1341", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenFunctorMayerVietoris.lean:78-96"
  "adaptation" "Naturality of the actual excision-defined boundary under exact functors."]
theorem PerfectMayerVietoris.connectingHom_natural_of_exactFunctors (n : ℕ) :
    (PerfectMayerVietoris.connectingHom j' T' hcover' n).comp (KMap hi (n + 1)) =
      (KMap hf n).comp (PerfectMayerVietoris.connectingHom j T hcover n) :=
  PerfectMayerVietoris.connectingHom_natural_of_support_squares j j' T T' hcover hcover' n
    (KMap (perfectSupportedFunctorOfRestrictIso_isExact T.ι T'.ι hf hh d) n)
    (KMap (perfectSupportedFunctorOfRestrictIso_isExact (j ⁻¹ᵁ T).ι (j' ⁻¹ᵁ T').ι hg hi e) n)
    (KMap hf n) (KMap hi (n + 1))
    (perfectSupportedRestrictionKMap_natural_of_exactFunctors j j' T T' hf hh hg hi d e c n)
    (perfectSupportedKMap_comp_functorOfRestrictIso T.ι T'.ι hf hh d n)
    (perfectQcqsConnectingHom_natural_of_restrictIso (j ⁻¹ᵁ T).ι (j' ⁻¹ᵁ T').ι hg hi e n)

end AlgebraicGeometry.Scheme.Modules
