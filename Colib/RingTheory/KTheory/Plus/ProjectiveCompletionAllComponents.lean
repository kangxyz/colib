/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionComponents
public import Colib.Topology.ClassifyingSpace.ZerothHomotopy

/-! # All components of the original projective telescope completion map -/
open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveCompletionAllComponents.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory
universe u
namespace ModuleCat.FiniteProjective.StableFreeRight
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  CategoryTheory.Localization.groupoid
variable (R : Type u) [Ring R]

/-- A genuine completed path between equal-denominator pairs gives one common stabilization. -/
theorem exists_stabilizedHom_of_completed_pair_joined
    (E P Q : IsoCategory Rᵐᵒᵖ)
    (h : Joined (classifyingSpacePoint (⟨E, P⟩ : StableCompletion.Completion R))
      (classifyingSpacePoint (⟨E, Q⟩ : StableCompletion.Completion R))) :
    ∃ s : IsoCategory Rᵐᵒᵖ, Nonempty (s ⊗ P ⟶ s ⊗ Q) := by
  obtain ⟨a, -⟩ := classifyingGroupoidCompletionFunctor_map_surjective
    (StableCompletion.Completion R) ⟨E, P⟩ ⟨E, Q⟩
    (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk h.somePath))
  obtain ⟨⟨A, B⟩, p, q, -⟩ := CategoryTheory.Localization.exists_right_roof
    ActionLocalization.exists_common_right_multiple a
  obtain ⟨r, -⟩ := ActionLocalization.mkHom_surjective (E, P) (A, B) p
  obtain ⟨s, -⟩ := ActionLocalization.mkHom_surjective (E, Q) (A, B) q
  refine ⟨r.denom ⊗ E, ⟨?_⟩⟩
  exact ((β_ r.denom E).hom ▷ P) ≫ (α_ E r.denom P).hom ≫
    E ◁ (r.map.2 ≫ inv s.map.2) ≫ (α_ E s.denom Q).inv ≫
      ((β_ E s.denom).hom ▷ Q) ≫ ((s.map.1 ≫ inv r.map.1) ▷ Q)

/-- The original map reflects joinedness for any two vertices at the same stage. -/
theorem completionFunctor_same_stage_reflects_joined (n : ℕ)
    (P Q : IsoCategory Rᵐᵒᵖ)
    (h : Joined
      (classifyingSpacePoint ((completionFunctor R).obj ⟨n, AsSmall.up.obj P⟩))
      (classifyingSpacePoint ((completionFunctor R).obj ⟨n, AsSmall.up.obj Q⟩))) :
    Joined (classifyingSpacePoint (⟨n, AsSmall.up.obj P⟩ : ProjectiveTelescope R))
      (classifyingSpacePoint (⟨n, AsSmall.up.obj Q⟩ : ProjectiveTelescope R)) := by
  obtain ⟨s, ⟨f⟩⟩ := exists_stabilizedHom_of_completed_pair_joined R
    (rankOnePower Rᵐᵒᵖ n) P Q h
  apply (projectiveTelescopeTranslation_joined_iff R s _ _).mp
  rw [classifyingSpaceMap_point, classifyingSpaceMap_point]
  exact ⟨classifyingSpacePath
    ((Grothendieck.ι (projectiveTelescopeDiagram R) n).map (AsSmall.up.map f))⟩

/-- A complement of the actual denominator gives an original telescope vertex in its component. -/
theorem completionFunctor_surjective_vertex_components (U : StableCompletion.Completion R) :
    ∃ X : ProjectiveTelescope R,
      Joined (classifyingSpacePoint ((completionFunctor R).obj X)) (classifyingSpacePoint U) := by
  rcases U with ⟨A, B⟩
  obtain ⟨n, Q, ⟨f⟩⟩ := rankOne_cofinal Rᵐᵒᵖ A
  let V : IsoCategory Rᵐᵒᵖ := Q ⊗ B
  refine ⟨⟨n, AsSmall.up.obj V⟩, ?_⟩
  have h := classifyingSpacePath (CategoryTheory.GroupCompletion.Localization.mkHom
    (X := (A, B)) (Y := (rankOnePower Rᵐᵒᵖ n, V))
    Q ((β_ Q A).hom ≫ f.hom) (𝟙 V))
  exact Joined.symm ⟨h⟩

/-- Raising both original vertices to a common stage detects their original components. -/
theorem completionFunctor_vertex_reflects_joined (X Y : ProjectiveTelescope R)
    (h : Joined (classifyingSpacePoint ((completionFunctor R).obj X))
      (classifyingSpacePoint ((completionFunctor R).obj Y))) :
    Joined (classifyingSpacePoint X) (classifyingSpacePoint Y) := by
  let k := max X.base Y.base
  let a : X.base ⟶ k := homOfLE (Nat.le_max_left _ _)
  let b : Y.base ⟶ k := homOfLE (Nat.le_max_right _ _)
  let X' : ProjectiveTelescope R :=
    ⟨k, ((projectiveTelescopeDiagram R).map a).toFunctor.obj X.fiber⟩
  let Y' : ProjectiveTelescope R :=
    ⟨k, ((projectiveTelescopeDiagram R).map b).toFunctor.obj Y.fiber⟩
  let f : X ⟶ X' := ⟨a, 𝟙 _⟩
  let g : Y ⟶ Y' := ⟨b, 𝟙 _⟩
  have hx : Joined (classifyingSpacePoint X) (classifyingSpacePoint X') :=
    ⟨classifyingSpacePath f⟩
  have hy : Joined (classifyingSpacePoint Y) (classifyingSpacePoint Y') :=
    ⟨classifyingSpacePath g⟩
  have hx' : Joined (classifyingSpacePoint ((completionFunctor R).obj X))
      (classifyingSpacePoint ((completionFunctor R).obj X')) :=
    ⟨classifyingSpacePath ((completionFunctor R).map f)⟩
  have hy' : Joined (classifyingSpacePoint ((completionFunctor R).obj Y))
      (classifyingSpacePoint ((completionFunctor R).obj Y')) :=
    ⟨classifyingSpacePath ((completionFunctor R).map g)⟩
  have h' := hx'.symm.trans (h.trans hy')
  have hxy : Joined (classifyingSpacePoint X') (classifyingSpacePoint Y') :=
    completionFunctor_same_stage_reflects_joined R k
      (AsSmall.down.obj X'.fiber) (AsSmall.down.obj Y'.fiber) h'
  exact hx.trans (hxy.trans hy.symm)

/-- The actual original completion map preserves and reflects every path component. -/
theorem completionMap_joined_iff (x y : ClassifyingSpace (ProjectiveTelescope R)) :
    Joined (classifyingSpaceMapUniversal (completionFunctor R) x)
      (classifyingSpaceMapUniversal (completionFunctor R) y) ↔ Joined x y := by
  constructor
  · intro h
    obtain ⟨X, hx⟩ := classifyingSpace_joined_vertex x
    obtain ⟨Y, hy⟩ := classifyingSpace_joined_vertex y
    have hv := (hx.map (classifyingSpaceMapUniversal (completionFunctor R)).continuous).trans
      (h.trans (hy.map (classifyingSpaceMapUniversal (completionFunctor R)).continuous).symm)
    rw [classifyingSpaceMapUniversal_point, classifyingSpaceMapUniversal_point] at hv
    exact hx.symm.trans ((completionFunctor_vertex_reflects_joined R X Y hv).trans hy)
  · exact fun h ↦ h.map (classifyingSpaceMapUniversal (completionFunctor R)).continuous

/-- Every actual completed realization point is reached up to a genuine path. -/
theorem completionMap_surjective_components
    (y : ClassifyingSpace (StableCompletion.Completion R)) :
    ∃ x, Joined (classifyingSpaceMapUniversal (completionFunctor R) x) y := by
  obtain ⟨U, hy⟩ := classifyingSpace_joined_vertex y
  obtain ⟨X, hx⟩ := completionFunctor_surjective_vertex_components R U
  refine ⟨classifyingSpacePoint X, ?_⟩
  rw [classifyingSpaceMapUniversal_point]
  exact hx.trans hy

/-- The map on actual path-component quotients is induced by the original completion functor. -/
def completionMapComponents :
    ZerothHomotopy (ClassifyingSpace (ProjectiveTelescope R)) →
      ZerothHomotopy (ClassifyingSpace (StableCompletion.Completion R)) :=
  ZerothHomotopy.lift
    (fun x ↦ ZerothHomotopy.mk (classifyingSpaceMapUniversal (completionFunctor R) x))
    (fun _ _ p ↦ ZerothHomotopy.sound
      (p.map (classifyingSpaceMapUniversal (completionFunctor R)).continuous))

/-- The original map induces a genuine bijection on all path components. -/
theorem completionMapComponents_bijective : Function.Bijective (completionMapComponents R) := by
  constructor
  · intro a b h
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
    exact Quotient.sound ((completionMap_joined_iff R x y).mp (Quotient.exact h))
  · intro b
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
    obtain ⟨x, hx⟩ := completionMap_surjective_components R y
    exact ⟨ZerothHomotopy.mk x, Quotient.sound hx⟩

/-- All components of the original telescope and completion are equivalent through that map. -/
def completionMapComponentsEquiv :
    ZerothHomotopy (ClassifyingSpace (ProjectiveTelescope R)) ≃
      ZerothHomotopy (ClassifyingSpace (StableCompletion.Completion R)) :=
  Equiv.ofBijective (completionMapComponents R) (completionMapComponents_bijective R)

/-- The component equivalence changes no original realization point. -/
theorem completionMapComponentsEquiv_mk (x : ClassifyingSpace (ProjectiveTelescope R)) :
    completionMapComponentsEquiv R (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (classifyingSpaceMapUniversal (completionFunctor R) x) := rfl

end ModuleCat.FiniteProjective.StableFreeRight
