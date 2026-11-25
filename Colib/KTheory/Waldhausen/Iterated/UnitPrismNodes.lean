/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SimplexTriangleLift

/-!
# Six full reference nodes for two consecutive unit squares

Three actual model maps and their unit-shifted references form one common simplex. The two
categorical commuting equations identify the original geometric and normalization triangles.
Repeated underlying functors retain distinct references; only the ordered primitive triangles
are asserted to be faces, not the nonmonotone normalization diamond.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS.UnitPrismNodes

open SmallWaldhausenCategory

variable {V W : WideSubcategory preservesZero.{u}} (F₀ F₁ F₂ : V ⟶ W)
  (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor) (n : F₁.hom.toFunctor ≅ F₂.hom.toFunctor)
  (α : F₀.hom.toFunctor ≅ F₀.hom.toFunctor) (β : F₁.hom.toFunctor ≅ F₁.hom.toFunctor)
  (δ : F₂.hom.toFunctor ≅ F₂.hom.toFunctor)

/-- The actual reference nodes keep their isomorphisms even when their model maps repeat. -/
def nodes : Fin 6 → Σ F : V ⟶ W, F₀.hom.toFunctor ≅ F.hom.toFunctor :=
  ![⟨F₀, Iso.refl _⟩, ⟨F₁, e⟩, ⟨F₂, e ≪≫ n⟩,
    ⟨F₀, α⟩, ⟨F₁, e ≪≫ β⟩, ⟨F₂, (e ≪≫ n) ≪≫ δ⟩]

/-- One common family contains both original unit squares with all six full references. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SConstruction/Iterated/UnitPrismNodes.lean:27-40"
  "adaptation" "The original common-reference simplex with all six dependent nodes"]
def simplex : ModelSimplex V W 5 :=
  ModelSimplex.ofIsos F₀ (fun i ↦ (nodes F₀ F₁ F₂ e n α β δ i).1)
    (fun i ↦ (nodes F₀ F₁ F₂ e n α β δ i).2)

/-- The first geometric triangle follows the original comparison then the middle unit. -/
def geometricFirst : ⦋2⦌ ⟶ ⦋5⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 4], by decide⟩

/-- The second geometric triangle follows the source unit then the original comparison. -/
def geometricSecond : ⦋2⦌ ⟶ ⦋5⦌ := SimplexCategory.Hom.mk ⟨![0, 3, 4], by decide⟩

/-- The first normalization triangle follows the middle unit then normalization. -/
def normalizationFirst : ⦋2⦌ ⟶ ⦋5⦌ := SimplexCategory.Hom.mk ⟨![1, 4, 5], by decide⟩

/-- The second normalization triangle follows normalization then the final unit. -/
def normalizationSecond : ⦋2⦌ ⟶ ⦋5⦌ := SimplexCategory.Hom.mk ⟨![1, 2, 5], by decide⟩

/-- The geometric triangle is a face with both original component transformations. -/
theorem geometric_first :
    (simplex F₀ F₁ F₂ e n α β δ).face geometricFirst =
      ModelSimplex.triangle e.hom β.hom
        (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp e.hom
  · rfl

/-- The geometric unit equation identifies the second whole primitive triangle. -/
theorem geometric_second (he : e.hom ≫ β.hom = α.hom ≫ e.hom) :
    (simplex F₀ F₁ F₂ e n α β δ).face geometricSecond =
      ModelSimplex.triangle α.hom e.hom
        (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp α.hom
  · exact he.symm

/-- The original normalization equation identifies the first whole ordered triangle. -/
theorem normalization_first (hn : β.hom ≫ n.hom = n.hom ≫ δ.hom) :
    (simplex F₀ F₁ F₂ e n α β δ).face normalizationFirst =
      ModelSimplex.triangle β.hom n.hom
        (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (e.hom ≫ β.hom) ≫ n.hom = (e.hom ≫ n.hom) ≫ δ.hom
    simpa only [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) hn

/-- The second ordered normalization triangle retains the terminal unit's actual reference. -/
theorem normalization_second :
    (simplex F₀ F₁ F₂ e n α β δ).face normalizationSecond =
      ModelSimplex.triangle n.hom δ.hom
        (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · rfl

/-- The unit-shifted middle node agrees only after its full reference is transported. -/
theorem middle_reference (he : e.hom ≫ β.hom = α.hom ≫ e.hom) :
    nodes F₀ F₁ F₂ e n α β δ 4 = ⟨F₁, α ≪≫ e⟩ := by
  have hi : e ≪≫ β = α ≪≫ e := Iso.ext he
  change (⟨F₁, e ≪≫ β⟩ : Σ F : V ⟶ W, F₀.hom.toFunctor ≅ F.hom.toFunctor) = _
  rw [hi]

/-- The unit-shifted final node keeps the original normalization alternative reference. -/
theorem final_reference (hn : β.hom ≫ n.hom = n.hom ≫ δ.hom) :
    nodes F₀ F₁ F₂ e n α β δ 5 = ⟨F₂, (e ≪≫ β) ≪≫ n⟩ := by
  have hi : (e ≪≫ n) ≪≫ δ = (e ≪≫ β) ≪≫ n := by
    apply Iso.ext
    change (e.hom ≫ n.hom) ≫ δ.hom = (e.hom ≫ β.hom) ≫ n.hom
    simpa only [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) hn.symm
  change (⟨F₂, (e ≪≫ n) ≪≫ δ⟩ :
    Σ F : V ⟶ W, F₀.hom.toFunctor ≅ F.hom.toFunctor) = _
  rw [hi]

end CategoryTheory.Waldhausen.IteratedS.UnitPrismNodes
