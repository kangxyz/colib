/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftOperations
public import Colib.KTheory.Waldhausen.Iterated.SimplexParameterPaths
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIntertwiningHomotopy

/-!
# The original intertwining word on four complete reference nodes

The two original composition triangles, their reversal, concatenation and endpoint transport
are retained literally. This lifts the prescribed intertwining comparison, not merely a surface
with the same four boundary paths.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen Convexity
open Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.SimplexIntertwiningLift

/-- The first original composition triangle follows nodes zero, one and three. -/
def firstFace : ⦋2⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 3], by decide⟩

/-- The second original composition triangle follows nodes zero, two and three. -/
def secondFace : ⦋2⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![0, 2, 3], by decide⟩

/-- The exact two-triangle parameter word of the original intertwining comparison. -/
def parameter : ((edge (k := 3) 0 1).trans (edge 1 3)).Homotopy
    ((edge 0 2).trans (edge 2 3)) :=
  (triangle firstFace).symm.trans (triangle secondFace)

private def pastingTemplate {E D : Topology.LoopPrespectrum.{u}} {f g : E ⟶ D}
    {A B C D' : Homotopy f g} (e : A = B)
    (J : A.RelHomotopy C) (K : B.RelHomotopy D') : C.RelHomotopy D' :=
  J.symm.trans ((congrArg (fun H ↦ H.RelHomotopy D') e.symm).mp K)

private theorem native_cast
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (S : ModelSimplex V W 3)
    {a b : StdSimplex ℝ (Fin 4)} {p q : Path a b} {J : p.Homotopy q}
    {f g : prespectrum V ⟶ prespectrum W}
    {H H' K K' : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift S J M)
    (hH : H = H') (hK : K = K') (he : H.RelHomotopy K = H'.RelHomotopy K') :
    HomotopyLift S J (he.mp M) := by
  subst H'
  subst K'
  exact hJ

private theorem template_lift {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (S : ModelSimplex V W 3)
    {f g : prespectrum V ⟶ prespectrum W} {A B C D : Homotopy f g}
    (e : A = B) (J : A.RelHomotopy C) (K : B.RelHomotopy D)
    (hJ : HomotopyLift S (triangle firstFace) J)
    (hK : HomotopyLift S (triangle secondFace) K) :
    HomotopyLift S parameter (pastingTemplate e J K) :=
  HomotopyLift.trans S (HomotopyLift.symm S hJ)
    (native_cast S hK e.symm rfl
      (congrArg (fun H ↦ H.RelHomotopy D) e.symm))

private theorem composite_eq {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {F G G' H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (η' : F.hom.toFunctor ⟶ G'.hom.toFunctor) (θ' : G'.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A))
    (hθ' : ∀ A, W.obj.waldhausen.weq (θ'.app A)) (he : η ≫ θ = η' ≫ θ') :
    prespectrumTransformationHomotopy (η ≫ θ)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) =
    prespectrumTransformationHomotopy (η' ≫ θ')
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
  congr 1

/-- Two exact triangle lifts recover the entire existing pasting, including its stored cast. -/
theorem pasting_lift {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {F G G' H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (η' : F.hom.toFunctor ⟶ G'.hom.toFunctor) (θ' : G'.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A))
    (hθ' : ∀ A, W.obj.waldhausen.weq (θ'.app A)) (he : η ≫ θ = η' ≫ θ')
    (S : ModelSimplex V W 3)
    (hfirst : HomotopyLift S (triangle firstFace)
      (prespectrumTransformationCompositionHomotopy η θ hη hθ))
    (hsecond : HomotopyLift S (triangle secondFace)
      (prespectrumTransformationCompositionHomotopy η' θ' hη' hθ')) :
    HomotopyLift S parameter
      (prespectrumTransformationPastingHomotopy η θ η' θ' hη hθ hη' hθ' he) := by
  have hform : prespectrumTransformationPastingHomotopy η θ η' θ' hη hθ hη' hθ' he =
      pastingTemplate (composite_eq η θ η' θ' hη hθ hη' hθ' he)
        (prespectrumTransformationCompositionHomotopy η θ hη hθ)
        (prespectrumTransformationCompositionHomotopy η' θ' hη' hθ') := rfl
  rw [hform]
  exact template_lift S _ _ _ hfirst hsecond

variable {V W T U : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
  (α : F.hom.toFunctor ≅ F.hom.toFunctor)
  (i : (F ≫ b).hom.toFunctor ≅ (a ≫ G).hom.toFunctor)

/-- The original four vertices, including the separately anchored repeated vertices. -/
def vertices : Fin 4 → (V ⟶ U) := ![F ≫ b, F ≫ b, a ≫ G, a ≫ G]

/-- All four full reference isomorphisms are the original whiskering and comparison word. -/
def anchors : ∀ n, (F ≫ b).hom.toFunctor ≅ (vertices F G a b n).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (isoWhiskerRight α b.hom.toFunctor)
    (Fin.cases i (Fin.cases (isoWhiskerRight α b.hom.toFunctor ≪≫ i) (fun j ↦ Fin.elim0 j))))

/-- The actual common simplex retains the full original reference nodes. -/
def simplex : ModelSimplex V U 3 :=
  ModelSimplex.ofIsos (F ≫ b) (vertices F G a b) (anchors F G a b α i)

variable (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
  (hα : ∀ X, W.obj.waldhausen.weq (α.hom.app X))
  (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X))
  (hi : ∀ X, U.obj.waldhausen.weq (i.hom.app X))
  (he : whiskerRight α.hom b.hom.toFunctor ≫ i.hom = i.hom ≫ whiskerLeft a.hom.toFunctor θ)

/-- The first whole triangle is the original postwhiskered unit followed by comparison. -/
theorem first_lift : HomotopyLift (simplex F G a b α i) (triangle firstFace)
    (prespectrumTransformationCompositionHomotopy
      (F := F ≫ b) (G := F ≫ b) (H := a ≫ G) (whiskerRight α.hom b.hom.toFunctor) i.hom
      (fun X ↦ b.hom.isExact.weak _ (hα X)) hi) := by
  intro n r s x
  exact prespectrumSimplexFamily_ofIsos_triangle (F ≫ b) (vertices F G a b)
    (anchors F G a b α i) firstFace (whiskerRight α.hom b.hom.toFunctor) i.hom
    (fun X ↦ b.hom.isExact.weak _ (hα X)) hi (Category.id_comp _) rfl n r s x

/-- The second whole triangle uses the actual intertwining equality at its final anchor. -/
theorem second_lift
    (he : whiskerRight α.hom b.hom.toFunctor ≫ i.hom = i.hom ≫ whiskerLeft a.hom.toFunctor θ) :
    HomotopyLift (simplex F G a b α i) (triangle secondFace)
    (prespectrumTransformationCompositionHomotopy
      (F := F ≫ b) (G := a ≫ G) (H := a ≫ G) i.hom (whiskerLeft a.hom.toFunctor θ)
      hi (fun X ↦ hθ (a.hom.toFunctor.obj X))) := by
  intro n r s x
  exact prespectrumSimplexFamily_ofIsos_triangle (F ≫ b) (vertices F G a b)
    (anchors F G a b α i) secondFace i.hom (whiskerLeft a.hom.toFunctor θ)
    hi (fun X ↦ hθ (a.hom.toFunctor.obj X)) (Category.id_comp _) he.symm n r s x

/-- The original ofLevels wrapper preserves an exact two-triangle lift on any given simplex. -/
theorem of_triangle_lifts (S : ModelSimplex V U 3)
    (hfirst : HomotopyLift S (triangle firstFace)
      (prespectrumTransformationCompositionHomotopy
        (F := F ≫ b) (G := F ≫ b) (H := a ≫ G) (whiskerRight α.hom b.hom.toFunctor) i.hom
        (fun X ↦ b.hom.isExact.weak _ (hα X)) hi))
    (hsecond : HomotopyLift S (triangle secondFace)
      (prespectrumTransformationCompositionHomotopy
        (F := F ≫ b) (G := a ≫ G) (H := a ≫ G) i.hom (whiskerLeft a.hom.toFunctor θ)
        hi (fun X ↦ hθ (a.hom.toFunctor.obj X)))) :
    HomotopyLift S parameter
      (prespectrumTransformationIntertwiningHomotopy F G a b α.hom θ i.hom hα hθ hi he) := by
  unfold prespectrumTransformationIntertwiningHomotopy
  exact HomotopyLift.ofLevels S
    (pasting_lift (F := F ≫ b) (G := F ≫ b) (G' := a ≫ G) (H := a ≫ G)
      (whiskerRight α.hom b.hom.toFunctor) i.hom i.hom (whiskerLeft a.hom.toFunctor θ)
      (fun X ↦ b.hom.isExact.weak _ (hα X)) hi hi (fun X ↦ hθ (a.hom.toFunctor.obj X)) he
      S hfirst hsecond) _ _ _ _

/-- The original full intertwining comparison has exactly the two-triangle parameter word. -/
theorem native : HomotopyLift (simplex F G a b α i) parameter
    (prespectrumTransformationIntertwiningHomotopy F G a b α.hom θ i.hom hα hθ hi he) :=
  of_triangle_lifts F G a b α i θ hα hθ hi he (simplex F G a b α i)
    (first_lift F G a b α i hα hi) (second_lift F G a b α i θ hθ hi he)

end CategoryTheory.Waldhausen.IteratedS.SimplexIntertwiningLift
