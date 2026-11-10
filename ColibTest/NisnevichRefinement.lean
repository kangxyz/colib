module

import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Refinement
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Native consumers of affine Nisnevich refinement

The first examples consume the geometric refinement and the comparison with the big
over-site. The final examples use Mathlib's canonical sheafification comparison and its
unit formula directly, replacing the two wrappers in the original
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Nisnevich/Sheafification.lean`.
The sheafification and pointwise right Kan extension assumptions remain explicit.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u}) [IsAffine S]

example (X : SmoothSite S) {R : Sieve X.left} (hR : R ∈ Nisnevich.topology X.left) :
    ∃ Q : Presieve X, Q ∈ nisnevichPrecoverage S X ∧
      Q ≤ (R.functorPullback (forgetScheme S)).arrows :=
  exists_nisnevich_refinement X hR

example (X : SmoothSite S) {R : Sieve ((forget S).obj X)}
    (hR : R ∈ (Nisnevich.topology.over S) _) :
    ∃ Q : Presieve X, Q ∈ nisnevichPrecoverage S X ∧
      Q ≤ (R.functorPullback (forget S)).arrows :=
  exists_nisnevich_refinement_over X hR

example : (forget S).LocallyCoverDense (Nisnevich.topology.over S) := inferInstance

example : nisnevichTopology S = (forget S).restrictedTopology (Nisnevich.topology.over S) :=
  nisnevichTopology_eq_restrictedTopology S

example : nisnevichTopology S = (forget S).inducedTopology (Nisnevich.topology.over S) :=
  nisnevichTopology_eq_inducedTopology S

example (X : SmoothSite S) (R : Sieve X) :
    R ∈ nisnevichTopology S X ↔
      R.functorPushforward (forget S) ∈ (Nisnevich.topology.over S) ((forget S).obj X) :=
  mem_nisnevichTopology_iff_functorPushforward R

example : (forget S).IsCocontinuous (nisnevichTopology S) (Nisnevich.topology.over S) :=
  inferInstance

variable (A : Type w) [Category.{v} A]
  [HasWeakSheafify (nisnevichTopology S) A]
  [HasWeakSheafify (Nisnevich.topology.over S) A]
  [∀ F : (SmoothSite S)ᵒᵖ ⥤ A, (forget S).op.HasPointwiseRightKanExtension F]

example :
    (Functor.whiskeringLeft _ _ A).obj (forget S).op ⋙
      presheafToSheaf (nisnevichTopology S) A ≅
    presheafToSheaf (Nisnevich.topology.over S) A ⋙ restrictNisnevichSheaf S A :=
  (forget S).pushforwardContinuousSheafificationCompatibility A _ _

example (P : (Over S)ᵒᵖ ⥤ A) :
    toSheafify (nisnevichTopology S) ((forget S).op ⋙ P) ≫
      (((forget S).pushforwardContinuousSheafificationCompatibility A
        (nisnevichTopology S) (Nisnevich.topology.over S)).hom.app P).hom =
      Functor.whiskerLeft (forget S).op (toSheafify (Nisnevich.topology.over S) P) :=
  (forget S).toSheafify_pullbackSheafificationCompatibility A _ _ P

end AlgebraicGeometry.Scheme.SmoothSite
