/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Colib.AlgebraicGeometry.Chow.FiniteScalarFundamentalCycle
public import Colib.AlgebraicGeometry.Sites.Smooth.ScalarExtension.Finite.Basic

/-!
# Actual finite scalar trace and its full degree

The trace is the native correspondence of the whole finite-flat span, with
identity right leg. Its composite with the projection graph is the scalar
extension degree times the diagonal on the original base object. This does not
assert the reverse composite on the scalar-extended object.

Source: motivic `Correspondences/BaseChange/ScalarTrace.lean`, blob
689f9e6bac02314fe9a3e8caee212e703ef172ec. This leaf supplies the trace and degree
part. Whole embedded-span Cartesian pullback and trace naturality are a separate
remaining endpoint, not assumed here. Sectionwise scalar local-zero descent
only needs projection naturality and this degree identity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- Transpose of an actual finite flat map between smooth site objects. -/
def finiteFlatTrace {X Y : SmoothSite (Spec (.of k))} (p : Y ⟶ X)
    [IsFinite p.left] [Flat p.left] : Cor.mk X ⟶ Cor.mk Y :=
  ofFiniteFlatSpan p.left (𝟙 Y.left) (by simp [MorphismProperty.Over.w p])

variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- Scalar restriction then trace acts by the entire field degree on the original object. -/
theorem finiteScalarTrace_comp_graph (X : SmoothSite (Spec (.of k))) :
    finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X) ≫
        (graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X) =
      (Module.finrank k E : ℤ) • 𝟙 (Cor.mk X) := by
  let p := (SmoothSite.finiteScalarProjection (E := E) X).left
  letI : IsNoetherian (SmoothSite.finiteScalarExtension (E := E) X).left :=
    isNoetherian_of_finiteType p
  let d : X.left ⟶ pullback X.hom X.hom :=
    pullback.lift (𝟙 X.left) (𝟙 X.left) (by simp)
  letI : IsFinite d := isFinite_spanMap (𝟙 X.left) (𝟙 X.left) _
  letI : IsFinite (pullback.lift (f := X.hom) (g := X.hom) p p rfl) :=
    isFinite_spanMap p p rfl
  have hd : pullback.lift p p rfl = p ≫ d := by
    apply pullback.hom_ext <;> simp [d, Category.assoc]
  rw [finiteFlatTrace, ofFiniteFlatSpan_comp_graph, ← ofFiniteFlatSpan_id X]
  simp only [Category.id_comp]
  apply Subtype.ext
  change finiteCyclePushforward (pullback.lift p p rfl)
      (AlgebraicCycle.fundamentalCycle (SmoothSite.finiteScalarExtension (E := E) X).left) =
    (Module.finrank k E : ℤ) • finiteCyclePushforward d (AlgebraicCycle.fundamentalCycle X.left)
  have hpush : finiteCyclePushforward (pullback.lift p p rfl)
      (AlgebraicCycle.fundamentalCycle (SmoothSite.finiteScalarExtension (E := E) X).left) =
      finiteCyclePushforward (p ≫ d)
        (AlgebraicCycle.fundamentalCycle (SmoothSite.finiteScalarExtension (E := E) X).left) := by
    have congrPush {A B : Scheme.{u}} (a b : A ⟶ B) [IsFinite a] [IsFinite b]
        (hab : a = b) (c : AlgebraicCycle A ℤ) :
        finiteCyclePushforward a c = finiteCyclePushforward b c := by
      cases hab
      rfl
    exact congrPush _ _ hd _
  rw [hpush, ← finiteCyclePushforward_comp, AddMonoidHom.comp_apply]
  rw [finitePushforward_scalar_fundamentalCycle X.hom, map_zsmul]

end AlgebraicGeometry.Cor
