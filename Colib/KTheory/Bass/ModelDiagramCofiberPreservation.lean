/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.StrictDiagramCofiberDescent
public import Colib.KTheory.Bass.ModelDiagramCofiberComparison
public import Colib.KTheory.Bass.StrictDiagramStableEquivalence

/-!
# Bass preserves actual cofiber comparisons between finite original Model diagrams

The cone of an original arrow between any two finite Model-diagram Bass stages has the actual
point HEP and all-point growth inherited from those stages. The genuine Bass functor therefore
preserves its stable original cone descent. The literal Bass cofiber comparison and its
prescribed-null factorization identify the result with the unchanged cone descent of the Bass
images, using exactly the Bass action on the original null track. No point-topology, excision,
or future connectivity premise remains; stability of the original localization comparison is
the mathematical input. This statement does not assert compatibility with an original seed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (i j : ℕ) (F G : C ⥤ WideSubcategory preservesZero.{w})
    (a : (strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor) ⟶
      (strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor))

/-- Actual corner cofibers retain the original chosen-point HEP at every finite Model stage. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramCofiberPreservation.lean:34"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem modelDiagramCone_point_homotopyExtensionProperty (X : C) (m : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      (((mappingConeDiagram a).obj X).point m))) :=
  ReducedMappingCone.point_homotopyExtensionProperty _ _ _ ((a.app X).map_point m)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F X m)
    (modelDiagramIterate_point_homotopyExtensionProperty Q j G X m)

/-- The original pointwise cones retain all-point vanishing with the maximum actual stage offset. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramCofiberPreservation.lean:42"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem modelDiagramCone_homotopyGroup_subsingleton (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : ((mappingConeDiagram a).obj X).space (n + max i j + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      (((mappingConeDiagram a).obj X).space (n + max i j + 2)) x) :=
  ReducedMappingCone.homotopyGroup_subsingleton _ _ _ ((a.app X).map_point _)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F X _)
    (modelDiagramIterate_point_homotopyExtensionProperty Q j G X _) n
    (fun y t ht ↦ modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F X
      (n + max i j + 2) (by omega) t (by omega) y)
    (fun y t ht ↦ modelDiagramIterate_homotopyGroup_subsingleton_of_le Q j G X
      (n + max i j + 2) (by omega) t (by omega) y) x k hk

/-- The coefficient-natural original comparison is stable at every actual finite Model stage. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramCofiberPreservation.lean:55"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem modelDiagramCofiberComparison_isStableEquivalence (X : C) :
    IsStableEquivalence ((strictDiagramCofiberComparison Q a).app X) :=
  modelDiagramSquare_loopedConeCofiberComparison_isStableEquivalence Q i F (Q.obj X)
    j G (Q.obj X) (diagramSquareMap a (Q.obj X))

/-- Bass preserves the original stable cone descent, with its entire original null action. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramCofiberPreservation.lean:61"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem modelDiagramCofiberDesc_bass_isStableEquivalence
    (k : ℕ) (K : C ⥤ WideSubcategory preservesZero.{w})
    (b : (strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor) ⟶
      (strictDiagramIterate Q k).obj (K ⋙ prespectrumFunctor))
    (N : ∀ X, Homotopy (a.app X ≫ b.app X)
      (zeroHom (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X)
        (((strictDiagramIterate Q k).obj (K ⋙ prespectrumFunctor)).obj X)))
    (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
      ((((strictDiagramIterate Q k).obj (K ⋙ prespectrumFunctor)).map f).map n
        ((N X).level n (r, x))) =
      (N Y).level n (r, (((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor)).map f).map n x))
    (hdesc : ∀ X, IsStableEquivalence (mappingConeDesc (a.app X) (b.app X) (N X))) (X : C) :
    IsStableEquivalence (mappingConeDesc (((strictDiagramFunctor Q).map a).app X)
      (((strictDiagramFunctor Q).map b).app X) (strictDiagramNullHomotopy a b N hN Q X)) := by
  rw [← strictDiagramCofiberComparison_desc Q a b N hN X]
  apply (modelDiagramCofiberComparison_isStableEquivalence Q i j F G a X).comp
  exact strictDiagramFunctor_map_isStableEquivalence_of_linearGrowth Q
    (mappingConeDiagram a) ((strictDiagramIterate Q k).obj (K ⋙ prespectrumFunctor))
    (modelDiagramCone_point_homotopyExtensionProperty Q i j F G a)
    (modelDiagramIterate_point_homotopyExtensionProperty Q k K) (max i j) k
    (modelDiagramCone_homotopyGroup_subsingleton Q i j F G a)
    (fun Y n t ht y ↦ modelDiagramIterate_homotopyGroup_subsingleton_at Q k K Y n t ht y)
    (mappingConeDescTransformation a b N hN) hdesc X

end KTheory.Bass

