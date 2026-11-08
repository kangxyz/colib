/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality

/-!
# Literal naturality of original model automorphism homotopies

An automorphism of an actual zero-preserving exact model morphism gives its original whole
prespectrum self-homotopy. A strictly commuting model square with the actual transformation
square preserves that entire homotopy, including the degree-zero loop and structure parameters.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/PrespectrumIsoNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology SSet

/-- The original transformation homotopy of an automorphism of an exact model morphism. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/PrespectrumIsoNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def prespectrumIsoHomotopy {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (e :
  F.hom.toFunctor ≅ F.hom.toFunctor) :
    LoopPrespectrum.Homotopy (prespectrumMap F) (prespectrumMap F) :=
  prespectrumTransformationHomotopy e.hom (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance)

/-- Equality transport of a model morphism retains the entire supplied automorphism track. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/PrespectrumIsoNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem prespectrumIsoHomotopy_congr_level {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (h : F = G) (e : F.hom.toFunctor ≅ F.hom.toFunctor) (e' : G.hom.toFunctor ≅ G.hom.toFunctor)
    (he : e.hom ≫ eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h) ≫ e'.hom) (n : ℕ) :
    (prespectrumIsoHomotopy F e).level n = (prespectrumIsoHomotopy G e').level n := by
  subst G
  have he' : e.hom = e'.hom := by simpa using he
  have he'' : e = e' := Iso.ext he'
  subst e'
  rfl

/-- A strict model square and its original automorphism square preserve every interval value. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/PrespectrumIsoNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem prespectrumIsoHomotopy_square_apply {V W T U : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (e : F.hom.toFunctor ≅ F.hom.toFunctor) (e' : G.hom.toFunctor ≅ G.hom.toFunctor) (h : F ≫ b = a
      ≫ G)
    (he : Functor.whiskerRight e.hom b.hom.toFunctor ≫
        eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h) ≫ Functor.whiskerLeft a.hom.toFunctor e'.hom)
    (n : ℕ) (t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap b).map n ((prespectrumIsoHomotopy F e).level n (t, x)) =
      (prespectrumIsoHomotopy G e').level n (t, (prespectrumMap a).map n x) := by
  have hp := prespectrumTransformationHomotopy_postcomp_level e.hom
    (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance) b n
  have hq := prespectrumTransformationHomotopy_precomp_level e'.hom
    (fun _ ↦ U.obj.waldhausen.weq_iso _ inferInstance) a n
  have hc := prespectrumIsoHomotopy_congr_level h
    (Functor.isoWhiskerRight e b.hom.toFunctor) (Functor.isoWhiskerLeft a.hom.toFunctor e') he n
  exact (congrArg (fun k ↦ k (t, x)) hp).symm.trans
    ((congrArg (fun k ↦ k (t, x)) hc).trans (congrArg (fun k ↦ k (t, x)) hq))

/-- Every time slice is strictly natural on the original whole prespectrum maps. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/PrespectrumIsoNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem prespectrumIsoHomotopy_square_at {V W T U : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (e : F.hom.toFunctor ≅ F.hom.toFunctor) (e' : G.hom.toFunctor ≅ G.hom.toFunctor) (h : F ≫ b = a
      ≫ G)
    (he : Functor.whiskerRight e.hom b.hom.toFunctor ≫
        eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h) ≫ Functor.whiskerLeft a.hom.toFunctor e'.hom)
    (t : unitInterval) :
    (prespectrumIsoHomotopy F e).at t ≫ prespectrumMap b =
      prespectrumMap a ≫ (prespectrumIsoHomotopy G e').at t := by
  apply LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact prespectrumIsoHomotopy_square_apply F G a b e e' h he n t x

end CategoryTheory.Waldhausen.IteratedS
