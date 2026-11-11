/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.StrictDiagramIterateStableEquivalence
public import Colib.KTheory.Waldhausen.Iterated.FiniteConnectivity
public import Colib.KTheory.Waldhausen.Iterated.PointHEP
public import Colib.KTheory.Waldhausen.Iterated.ExactModelEquivalence

/-!
# Bass preservation for original iterated-S model diagrams

Any actual strict model diagrams on the same index category supply their original S-prespectra.
The proved original S-model topology and all-point growth discharge every initial hypothesis
of finite Bass preservation for an arbitrary actual square functor. The resulting arrow is the
unchanged iterate of the supplied original natural transformation. A categorical exact-equivalence
specialization proves its stability directly from the actual original forward model maps.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- Original model diagrams need no additional topology or growth inputs for Bass preservation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramStableEquivalence.lean:33"
  "adaptation" "Original finite Bass preservation and actual exact-equivalence maps"]
theorem modelDiagramIterate_map_isStableEquivalence (i : ℕ)
    (F G : C ⥤ WideSubcategory preservesZero.{w})
    (η : F ⋙ prespectrumFunctor ⟶ G ⋙ prespectrumFunctor)
    (hη : ∀ X, IsStableEquivalence (η.app X)) (X : C) :
    IsStableEquivalence (((strictDiagramIterate Q i).map η).app X) := by
  let : ∀ Y m, T1Space (((F ⋙ prespectrumFunctor).obj Y).space m) :=
    fun Y m ↦ prespectrumSpaceT1Space (F.obj Y) m
  let : ∀ Y m, T1Space (((G ⋙ prespectrumFunctor).obj Y).space m) :=
    fun Y m ↦ prespectrumSpaceT1Space (G.obj Y) m
  exact strictDiagramIterate_map_isStableEquivalence_of_linearGrowth Q i
    (F ⋙ prespectrumFunctor) (G ⋙ prespectrumFunctor)
    (fun Y m ↦ prespectrum_point_homotopyExtensionProperty (F.obj Y) m)
    (fun Y m ↦ prespectrum_point_homotopyExtensionProperty (G.obj Y) m) 0 0
    (fun Y n k hk x ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (F.obj Y) (n + 1) k (by omega) x)
    (fun Y n k hk x ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (G.obj Y) (n + 1) k (by omega) x) η hη X

/-- Exact categorical equivalences preserve the actual model-map Bass iterates, with no stable
premise and with the original forward functors retained literally. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramStableEquivalence.lean:52"
  "adaptation" "Original finite Bass preservation and actual exact-equivalence maps"]
theorem modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence
    (i : ℕ) (F G : C ⥤ WideSubcategory preservesZero.{w}) (η : F ⟶ G)
    (e : ∀ X, (F.obj X).obj.Obj ≌ (G.obj X).obj.Obj)
    (he : ∀ X, (e X).functor = (η.app X).hom.toFunctor)
    (hinv : ∀ X, IsExact (G.obj X).obj.waldhausen.cof (G.obj X).obj.waldhausen.weq
      (F.obj X).obj.waldhausen.cof (F.obj X).obj.waldhausen.weq (e X).inverse) (X : C) :
    IsStableEquivalence (((strictDiagramIterate Q i).map
      (Functor.whiskerRight η prespectrumFunctor)).app X) := by
  apply modelDiagramIterate_map_isStableEquivalence Q i F G
    (Functor.whiskerRight η prespectrumFunctor) _ X
  intro Y
  have hF : IsExact (F.obj Y).obj.waldhausen.cof (F.obj Y).obj.waldhausen.weq
      (G.obj Y).obj.waldhausen.cof (G.obj Y).obj.waldhausen.weq (e Y).functor := by
    rw [he Y]
    exact (η.app Y).hom.isExact
  have h0 : (e Y).functor.obj (F.obj Y).obj.waldhausen.zero = (G.obj Y).obj.waldhausen.zero := by
    rw [he Y]
    exact (η.app Y).property
  have hf : ExactModelEquivalence.forward (e Y) hF h0 = η.app Y := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact he Y
  have hs := ExactModelEquivalence.isStableEquivalence (e Y) hF (hinv Y) h0
  rw [hf] at hs
  exact hs

end KTheory.Bass


namespace KTheory.Bass

attribute [colib_tag "COL-0577"] modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence

end KTheory.Bass
