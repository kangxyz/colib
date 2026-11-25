/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenCompactFamily
public import Colib.Topology.Prespectrum.ParameterLooping
public import Colib.Topology.Prespectrum.RelativeHomotopy
public import Colib.Topology.Realization.SimplexCubeFaces

/-!
# Exact extension of the six carrier-valued boundary faces

The original six faces glue along their twelve full edges. The result extends into the
actual two-tip carrier, fixing the complete start and finish paths and both distinct
tip faces. The parameter coordinates are comparison time, route time and seed time,
in that order. Compact native evaluation and currying the seed time yield a relative
homotopy whenever the two specified whole routes are recovered on the boundary.
No geometric construction of those routes is included here.

Adapted from `CommonReferenceNerveCutOpenRelativeExtension.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
open SmallWaldhausenCategory Topology.SimplexCubeExtension

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ T)
  (G : V ⟶ T) (ε₀ ε₁ : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)

/-- Six whole carrier faces, with all twelve full geometric edge equalities. -/
structure RelativeBoundary where
  /-- The six carrier-valued faces, indexed by coordinate and by `false`/`true` for zero/one. -/
  faces : ∀ a : Fin 3 × Bool, C(face a, space F J G ε₀ ε₁)
  compatible : EdgeCompatible (fun a ↦ faces a)
  /-- The seed path fixed on the route-time-zero face, independently of comparison time. -/
  start : C(I, space F J G ε₀ ε₁)
  /-- The seed path fixed on the route-time-one face, independently of comparison time. -/
  finish : C(I, space F J G ε₀ ε₁)
  route_zero (z : face (1, false)) : faces (1, false) z = start (z.val.val 2)
  route_one (z : face (1, true)) : faces (1, true) z = finish (z.val.val 2)
  seed_zero (z : face (2, false)) : faces (2, false) z = tipMinus F J G ε₀ ε₁
  seed_one (z : face (2, true)) : faces (2, true) z = tipPlus F J G ε₀ ε₁

namespace RelativeBoundary
variable {F J G ε₀ ε₁} (B : RelativeBoundary F J G ε₀ ε₁)

/-- The closed-cover gluing retains every supplied face at its exact parameter value. -/
def boundaryMap : C(boundary, space F J G ε₀ ε₁) :=
  glueClosedCover face isClosed_face faces_cover B.faces
    (edgeCompatible_pairwise (fun a ↦ B.faces a) B.compatible)

/-- Contractibility of the actual two-tip carrier fills the glued boundary. -/
def extension : C(Fin 3 → I, space F J G ε₀ ε₁) :=
  cubeExtension F J G ε₀ ε₁ 3 B.boundaryMap

/-- The extension changes no point of any of its six original faces. -/
theorem extension_face (a : Fin 3 × Bool) (z : face a) :
    B.extension z.val.val = B.faces a z := by
  exact (DFunLike.congr_fun
    (cubeExtension_restrict F J G ε₀ ε₁ 3 B.boundaryMap) z.val).trans
      (glueClosedCover_apply face isClosed_face faces_cover B.faces
        (edgeCompatible_pairwise (fun a ↦ B.faces a) B.compatible) a z)

/-- Place a point with a specified endpoint coordinate into its whole boundary face. -/
def onFace (a : Fin 3 × Bool) (z : Fin 3 → I) (h : z a.1 = endpoint a.2) : face a :=
  ⟨⟨z, ⟨a.1, by cases a.2 <;> simp_all [endpoint]⟩⟩, h⟩

/-- Comparison, route and seed time are three separate coordinates in this order. -/
def coordinates (r s t : I) : Fin 3 → I := ![r, s, t]

/-- The chosen extension in product coordinates, retaining every original clock. -/
def carrier : C((I × I) × I, space F J G ε₀ ε₁) :=
  B.extension.comp ⟨fun z ↦ coordinates z.1.1 z.1.2 z.2, by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [coordinates] <;> fun_prop⟩

/-- The entire lower seed face is the first tip. -/
theorem carrier_zero (r s : I) : B.carrier ((r, s), 0) = tipMinus F J G ε₀ ε₁ :=
  (B.extension_face (2, false) (onFace (2, false) (coordinates r s 0) rfl)).trans
    (B.seed_zero _)

/-- The entire upper seed face is the distinct second tip. -/
theorem carrier_one (r s : I) : B.carrier ((r, s), 1) = tipPlus F J G ε₀ ε₁ :=
  (B.extension_face (2, true) (onFace (2, true) (coordinates r s 1) rfl)).trans
    (B.seed_one _)

/-- Route time zero fixes the whole start path, independently of comparison time. -/
theorem carrier_start (r t : I) : B.carrier ((r, 0), t) = B.start t :=
  (B.extension_face (1, false) (onFace (1, false) (coordinates r 0 t) rfl)).trans
    (B.route_zero _)

/-- Route time one fixes the whole finish path, independently of comparison time. -/
theorem carrier_finish (r t : I) : B.carrier ((r, 1), t) = B.finish t :=
  (B.extension_face (1, true) (onFace (1, true) (coordinates r 1 t) rfl)).trans
    (B.route_one _)

/-- Joint evaluation uses compactness of the three parameter intervals, not an assumed
continuous global native evaluator. The whole original input is retained at every level. -/
def joint (n : ℕ) : C(((I × I) × I) × (prespectrum V).space n, (nativeCone J).space n) :=
  compactNativeFamily F J G ε₀ ε₁ B.carrier n

/-- Curry seed time only after evaluating the two distinct tips at the native basepoint. -/
def loops (n : ℕ) : C((I × I) × (prespectrum V).space n,
    (parameterLooping (nativeCone J)).space n) where
  toFun z :=
    { toFun t := B.joint n ((z.1, t), z.2)
      continuous_toFun := by fun_prop
      source' := by
        change nativeEval F J G ε₀ ε₁ n (B.carrier (z.1, 0)) z.2 = _
        rw [B.carrier_zero]
        exact nativeEval_tipMinus F J G ε₀ ε₁ n z.2
      target' := by
        change nativeEval F J G ε₀ ε₁ n (B.carrier (z.1, 1)) z.2 = _
        rw [B.carrier_one]
        exact nativeEval_tipPlus F J G ε₀ ε₁ n z.2 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : ((I × I) × (prespectrum V).space n) × I ↦
      B.joint n ((z.1.1, z.2), z.1.2))
    fun_prop

variable {f g : prespectrum V ⟶ parameterLooping (nativeCone J)}
  (H K : Homotopy f g)

/-- The only remaining native hypotheses identify the two supplied outer boundary faces
with the original whole routes. No equality or homotopy of their interiors is assumed. -/
structure RecoversRoutes : Prop where
  left (z : face (0, false)) (n : ℕ) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n (B.faces (0, false) z) x =
      Path.toContinuousMap (H.level n (z.val.val 1, x)) (z.val.val 2)
  right (z : face (0, true)) (n : ℕ) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n (B.faces (0, true) z) x =
      Path.toContinuousMap (K.level n (z.val.val 1, x)) (z.val.val 2)

variable (h : B.RecoversRoutes H K)

/-- The initial native face is exactly the original left route at every seed time. -/
theorem loops_left (h : B.RecoversRoutes H K) (n : ℕ) (s : I) (x : (prespectrum V).space n) :
    B.loops n ((0, s), x) = H.level n (s, x) := by
  apply Path.ext
  funext t
  exact (congrArg (fun y ↦ nativeEval F J G ε₀ ε₁ n y x)
    (B.extension_face (0, false) (onFace (0, false) (coordinates 0 s t) rfl))).trans
      (h.left _ n x)

/-- The final native face is exactly the original right route at every seed time. -/
theorem loops_right (h : B.RecoversRoutes H K) (n : ℕ) (s : I) (x : (prespectrum V).space n) :
    B.loops n ((1, s), x) = K.level n (s, x) := by
  apply Path.ext
  funext t
  exact (congrArg (fun y ↦ nativeEval F J G ε₀ ε₁ n y x)
    (B.extension_face (0, true) (onFace (0, true) (coordinates 1 s t) rfl))).trans
      (h.right _ n x)

/-- A legitimate relative comparison produced from the six matching boundary faces. -/
def relativeComparison : H.RelHomotopy K where
  level n :=
    { toFun z := B.loops n ((z.1, z.2.1), z.2.2)
      continuous_toFun := by fun_prop
      map_zero_left z := B.loops_left H K h n z.1 z.2
      map_one_left z := B.loops_right H K h n z.1 z.2
      prop' r z hz := by
        change B.loops n ((r, z.1), z.2) = H.level n (z.1, z.2)
        rcases hz with hz | hz | hz
        · rcases z with ⟨s, x⟩
          dsimp at hz
          subst s
          refine Eq.trans ?_ (B.loops_left H K h n 0 x)
          apply Path.ext
          funext t
          exact congrArg (fun y ↦ nativeEval F J G ε₀ ε₁ n y x)
            ((B.carrier_start r t).trans (B.carrier_start 0 t).symm)
        · rcases z with ⟨s, x⟩
          dsimp at hz
          subst s
          refine Eq.trans ?_ (B.loops_left H K h n 1 x)
          apply Path.ext
          funext t
          exact congrArg (fun y ↦ nativeEval F J G ε₀ ε₁ n y x)
            ((B.carrier_finish r t).trans (B.carrier_finish 0 t).symm)
        · rw [hz, H.at_point]
          apply Path.ext
          funext t
          exact nativeEval_point F J G ε₀ ε₁ n (B.carrier ((r, z.1), t)) }
  comm n r s x t := by
    apply Path.ext
    funext v
    exact nativeEval_structure F J G ε₀ ε₁ n (B.carrier ((r, s), v)) x t

end RelativeBoundary

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
