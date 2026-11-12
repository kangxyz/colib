module
import Colib.RingTheory.KTheory.Bass.StrictLaurentSeedContraction

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Functor CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open KTheory.Bass CommRingCat.PolynomialLaurent
noncomputable section
universe u w

section ModelContractions
variable {V W T U : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
  (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
  (hθ : ∀ X, W.obj.waldhausen.weq (θ.app X))

example (J : W ⟶ T) (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy
      (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.hom.toFunctor) (whiskerRight θ J.hom.toFunctor)
      (fun X ↦ J.hom.isExact.weak _ (hη X))
      (fun X ↦ J.hom.isExact.weak _ (hθ X))).level n (r, (s, x)) =
      (prespectrumMap J).map n
        ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x))) :=
  prespectrumTransformationCompositionHomotopy_postcomp_level η θ hη hθ J n r s x

example (J : T ⟶ V) (n : ℕ) (r s t : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumTransformationCompositionHomotopy
      (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
      (fun X ↦ hη (J.hom.toFunctor.obj X)) (fun X ↦ hθ (J.hom.toFunctor.obj X))).level
        (n + 1) (r, (s, (prespectrum T).structureMap n x t)) =
      (prespectrum W).structureMap n
        ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n
          (r, (s, (prespectrumMap J).map n x))) t :=
  prespectrumTransformationCompositionHomotopy_precomp_structure η θ hη hθ J n r s t x
end ModelContractions

section Endotransformations
variable {V W T U : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
  (η : F.hom.toFunctor ⟶ F.hom.toFunctor)
  (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
  (hz : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F).app X))

example (J : W ⟶ T) :
    whiskerRight (zeroEndotransformation F) J.hom.toFunctor =
      zeroEndotransformation (F ≫ J) := zeroEndotransformation_postcomp F J

example (J : W ⟶ T)
    (hz' : ∀ X, T.obj.waldhausen.weq ((zeroEndotransformation (F ≫ J)).app X))
    (r s q : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 T) (stagePoint 0 T) from
      (prespectrumEndotransformationContraction (F ≫ J) (whiskerRight η J.hom.toFunctor)
        (fun X ↦ J.hom.isExact.weak _ (hη X)) hz').level 0 (r, (s, γ))) q =
      SSet.toTop.map ((stages 0).map J)
        ((show Path (stagePoint 0 W) (stagePoint 0 W) from
          (prespectrumEndotransformationContraction F η hη hz).level 0 (r, (s, γ))) q) :=
  prespectrumEndotransformationContraction_postcomp_zero_apply F η hη hz J hz' r s q γ

example (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U) (h : F ≫ b = a ≫ G)
    (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X))
    (hz' : ∀ X, U.obj.waldhausen.weq ((zeroEndotransformation G).app X))
    (he : whiskerRight η b.hom.toFunctor =
      eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ whiskerLeft a.hom.toFunctor θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap b).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) =
      (prespectrumEndotransformationContraction G θ hθ hz').level n
        (r, (s, (prespectrumMap a).map n x)) :=
  prespectrumEndotransformationContraction_naturality F G a b h η θ hη hθ hz hz' he n r s x
end Endotransformations

section LaurentContractions
variable {R : CommRingCat.{u}} {C : Under R ⥤ WideSubcategory preservesZero.{w}}
  (A : LaurentSeed.ModelAction C)
  (hz : ∀ (a : Under R) (X : (C.obj a).obj.Obj),
    (C.obj ((laurentUnderFunctor R).obj a)).obj.waldhausen.weq
      ((zeroEndotransformation (C.map ((laurentUnderCoefficient R).app a))).app X))

example {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : (prespectrum (C.obj a)).space n) :
    ((C ⋙ prespectrumFunctor).map ((laurentUnderFunctor R).map g)).map n
      ((A.contraction hz a).level n (r, (t, x))) =
    (A.contraction hz b).level n
      (r, (t, ((C ⋙ prespectrumFunctor).map g).map n x)) :=
  A.contraction_naturality hz g n r t x

example {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : (prespectrum (C.obj a)).space n) :
    (LaurentSeed.coefficientConeMap (C ⋙ prespectrumFunctor) g).map n
      ((A.seedNullComparison hz a).level n (r, (t, x))) =
    (A.seedNullComparison hz b).level n
      (r, (t, ((C ⋙ prespectrumFunctor).map g).map n x)) :=
  A.seedNullComparison_naturality hz g n r t x

example {a b : Under R} (g : a ⟶ b) (n : ℕ) (r : unitInterval)
    (x : (prespectrum (C.obj a)).space n) :
    (parameterLoopingMap (LaurentSeed.coefficientConeMap (C ⋙ prespectrumFunctor) g)).map n
      ((A.seedNullHomotopy hz a).level n (r, x)) =
    (A.seedNullHomotopy hz b).level n
      (r, ((C ⋙ prespectrumFunctor).map g).map n x) :=
  A.seedNullHomotopy_naturality hz g n r x

example (a : Under R) (n : ℕ) (r : unitInterval)
    (x : (prespectrum (C.obj a)).space n) :
    ((A.seedDiagramNull hz).homotopy a).level n (r, x) =
      (A.seedNullHomotopy hz a).level n (r, x) := rfl
end LaurentContractions
