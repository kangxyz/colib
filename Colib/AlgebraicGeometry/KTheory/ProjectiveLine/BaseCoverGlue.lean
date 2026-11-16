/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Group.MayerVietorisFiveTerm
public import Colib.Algebra.Group.MayerVietorisShuffle
public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietorisZero
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BaseCoverOverlapDifference
public import Colib.Util.References

/-! # The projective-line formula glues over a two-open cover -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]

local notation "P" => projectiveSpaceOver 1 X
local notation "Q" => projectiveSpaceOver 1 V
local notation "J" => projectiveSpaceOverMap 1 j
local notation "Tₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (P ↘ X))))) T
local notation "U" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "B" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom J)))) Tₚ
local notation "Uₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (Q ↘ V))))) U
local notation "e" => Eq.symm (projectiveLine_preimage_preimage j T)

local instance baseCoverGluePProper : IsProper (P ↘ X) := isProper_projectiveSpaceOver 1 X
local instance baseCoverGlueQProper : IsProper (Q ↘ V) := isProper_projectiveSpaceOver 1 V
local instance baseCoverGluePCompact : CompactSpace P :=
  QuasiCompact.compactSpace_of_compactSpace (P ↘ X)
local instance baseCoverGlueQCompact : CompactSpace Q :=
  QuasiCompact.compactSpace_of_compactSpace (Q ↘ V)
local instance baseCoverGluePQS : QuasiSeparatedSpace P :=
  quasiSeparatedSpace_of_quasiSeparated (P ↘ X)
local instance baseCoverGlueQQS : QuasiSeparatedSpace Q :=
  quasiSeparatedSpace_of_quasiSeparated (Q ↘ V)
local instance baseCoverGlueTCompact : CompactSpace (Scheme.Opens.toScheme Tₚ) :=
  QuasiCompact.compactSpace_of_compactSpace ((P ↘ X) ∣_ T)
local instance baseCoverGlueUCompact : CompactSpace (Scheme.Opens.toScheme Uₚ) :=
  QuasiCompact.compactSpace_of_compactSpace ((Q ↘ V) ∣_ U)
local instance baseCoverGlueBCompact : CompactSpace (Scheme.Opens.toScheme B) :=
  e ▸ (inferInstance : CompactSpace (Scheme.Opens.toScheme Uₚ))

/-- Regroup the two copies of the local pair, putting the two coefficients on each open together. -/
def projectiveLineBaseCoverLocalPairKMap (n : ℕ) :=
  (projectiveLineBaseCoverPairKMap (V := V) T n).comp
    (MulEquiv.prodProdProdComm (perfectK T.toScheme n) (perfectK V n)
      (perfectK T.toScheme n) (perfectK V n)).toMonoidHom

omit [IsOpenImmersion j] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  [QuasiSeparatedSpace V] [CompactSpace T.toScheme] in
/-- The map of the overlap groups is bijective by the projective-line formula on the overlap. -/
theorem projectiveLineBaseCoverOverlapKMap_bijective (n : ℕ) :
    Function.Bijective (projectiveLineBaseCoverOverlapKMap j T n) := by
  exact (KMap_openCongrPerfect_bijective e n).comp
    (projectiveLineOpenKMap_bijective V U n)

omit [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace V] in
/-- The maps on the two cover members are bijective, with the two coefficients kept together. -/
theorem projectiveLineBaseCoverLocalPairKMap_bijective (n : ℕ) :
    Function.Bijective (projectiveLineBaseCoverLocalPairKMap (V := V) T n) := by
  have hT := projectiveLineOpenKMap_bijective X T n
  have hV := (projectiveLineKEquiv V n).bijective
  have h : Function.Bijective (projectiveLineBaseCoverPairKMap (V := V) T n) := by
    exact Function.Bijective.prodMap hT hV
  exact h.comp (MulEquiv.prodProdProdComm (perfectK T.toScheme n) (perfectK V n)
    (perfectK T.toScheme n) (perfectK V n)).bijective

/-- The original five-term ladder proves bijectivity on the whole scheme from the local maps. -/
@[colib_tag "COL-1293",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeMayerVietorisGlue.lean"
    "adaptation" "The bijective_of_cover proof with the original three comparison maps"]
theorem projectiveLineKMap_bijective_of_baseOpenCover
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) (n : ℕ) :
    Function.Bijective (projectiveLineKMap X n) := by
  let hcover' := projectiveLine_baseOpenCover j T hcover
  have hx := fiveTerm_exact j T hcover n
  have hp := fiveTerm_exact J Tₚ hcover' n
  have hd (m : ℕ) :
      (overlapDifference J Tₚ m).comp (projectiveLineBaseCoverLocalPairKMap (V := V) T m) =
        (projectiveLineBaseCoverOverlapKMap j T m).comp
          ((overlapDifference j T m).prodMap (overlapDifference j T m)) := by
    unfold projectiveLineBaseCoverLocalPairKMap
    rw [← MonoidHom.comp_assoc, projectiveLineBaseCover_overlapDifference, MonoidHom.comp_assoc]
    congr 1
  have hr :
      (restrictionPair J Tₚ n).comp (projectiveLineKMap X n) =
        (projectiveLineBaseCoverLocalPairKMap (V := V) T n).comp
          ((restrictionPair j T n).prodMap (restrictionPair j T n)) := by
    unfold projectiveLineBaseCoverLocalPairKMap
    rw [MonoidHom.comp_assoc, projectiveLineBaseCover_restrictionPair]
    congr 1
  exact GroupMayerVietoris.bijective_of_fiveTerm
    (overlapDifference j T (n + 1)) (connectingHom j T hcover n)
    (restrictionPair j T n) (overlapDifference j T n)
    (overlapDifference J Tₚ (n + 1)) (connectingHom J Tₚ hcover' n)
    (restrictionPair J Tₚ n) (overlapDifference J Tₚ n)
    (projectiveLineBaseCoverLocalPairKMap (V := V) T (n + 1))
    (projectiveLineBaseCoverOverlapKMap j T (n + 1)) (projectiveLineKMap X n)
    (projectiveLineBaseCoverLocalPairKMap (V := V) T n) (projectiveLineBaseCoverOverlapKMap j T n)
    hx hp (hd (n + 1)) (projectiveLineBaseCover_connecting j T hcover n) hr (hd n)
    (projectiveLineBaseCoverLocalPairKMap_bijective (V := V) T (n + 1))
    (projectiveLineBaseCoverOverlapKMap_bijective j T (n + 1))
    (projectiveLineBaseCoverLocalPairKMap_bijective (V := V) T n)
    (projectiveLineBaseCoverOverlapKMap_bijective j T n)

end AlgebraicGeometry.Scheme
