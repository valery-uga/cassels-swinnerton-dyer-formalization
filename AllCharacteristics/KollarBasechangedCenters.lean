import AllCharacteristics.KollarResidualBaseChangeRoots
import AllCharacteristics.KollarGeometricCenterTransport

/-! Both residual centers keep their geometric genericity
after the explicit coefficient base change to an algebraically closed
constant field. The residual parameter may be either of the original roots. -/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry HomogeneousProjective PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Bounded composition cut, before inserting any concrete residual field. -/
theorem geometricCenter_map_comp
    {L E M : Type u} [Field L] [Field E] [Field M]
    (C : Cubic L 4) (p : Fin 4 → L) (B : L →+* E) (φ : E →+* M)
    (h : GeometricallyNoContainedLineThrough (C.map B) (fun i => B (p i))) :
    GeometricallyNoContainedLineThrough (C.map (φ.comp B))
      (fun i => φ (B (p i))) := by
  have hh : GeometricallyNoContainedLineThrough ((C.map B).map φ)
      (fun i => φ (B (p i))) :=
    GeometricallyNoContainedLineThrough.map (C.map B) (fun i => B (p i)) h φ
  exact hh

set_option backward.isDefEq.respectTransparency false in
theorem kollar_basechanged_residual_center_geometricallyNoContainedLine
    {k l : Type u} [Field k] [Field l] [IsAlgClosed l]
    (f : k →+* l) (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint k) = 0)
    (hsec : c.mixed (kollarBasePoint k)
      (kollarAffineLineDirection k (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)]
    [Fact (Irreducible (kollarGenericResidualPolynomial c))]
    [Fact (Irreducible (kollarGenericResidualPolynomial (c.map f)))]
    (r : AdjoinRoot (kollarGenericResidualPolynomial c))
    (hr : Polynomial.aeval r (kollarGenericResidualPolynomial c) = 0) :
    GeometricallyNoContainedLineThrough
      ((c.map ((AdjoinRoot.of (kollarGenericResidualPolynomial c)).comp
          (algebraMap k (FractionRing (MvPolynomial (Fin 3) k))))).map
        (kollarResidualRootBaseChange f c))
      (fun i => kollarResidualRootBaseChange f c (kollarResidualLinePoint c r i)) := by
  let Lbar := AdjoinRoot (kollarGenericResidualPolynomial (c.map f))
  let B := kollarResidualRootBaseChange f c
  letI : Smooth (hypersurfaceToBase (c.map f).toMvPolynomial
      (kollarMappedCubic_isHomogeneous f c hhom)) := kollarMappedCubic_smooth f c hhom
  have hroot := kollarResidualRootBaseChange_eval_root f c r hr
  have hno := kollar_residual_center_geometricallyNoContainedLine
    (c.map f) (kollarMappedCubic_isHomogeneous f c hhom)
    (kollarMappedCubic_basePoint_eval f c hp) (kollarMappedCubic_secant_ne_zero f c hsec)
    (B r) hroot
  have hc : (c.map ((AdjoinRoot.of (kollarGenericResidualPolynomial c)).comp
        (algebraMap k (FractionRing (MvPolynomial (Fin 3) k))))).map B =
      (c.map f).map (algebraMap l Lbar) := by
    funext i
    change B (AdjoinRoot.of (kollarGenericResidualPolynomial c)
      (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)) (c i))) = _
    rw [kollarResidualRootBaseChange_base]
    exact IsScalarTower.algebraMap_apply l
      (FractionRing (MvPolynomial (Fin 3) l)) Lbar (f (c i))
  rw [hc]
  change GeometricallyNoContainedLineThrough ((c.map f).map (algebraMap l Lbar))
    (fun i => B (((fun i => AdjoinRoot.of (kollarGenericResidualPolynomial c)
      (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)) (kollarBasePoint k i))) +
      r • (fun i => AdjoinRoot.of (kollarGenericResidualPolynomial c)
        (kollarGenericProjectiveLineDirection k i))) i))
  rw [kollarResidualLinePoint_map f c r]
  exact hno

/-- Composition with any further field embedding, including the algebraic
closure of the displayed base-changed root field, preserves both callbacks. -/
theorem kollar_basechanged_residual_center_geometricallyNoContainedLine_map
    {k l M : Type u} [Field k] [Field l] [Field M] [IsAlgClosed l]
    (f : k →+* l) (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint k) = 0)
    (hsec : c.mixed (kollarBasePoint k)
      (kollarAffineLineDirection k (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)]
    [Fact (Irreducible (kollarGenericResidualPolynomial c))]
    [Fact (Irreducible (kollarGenericResidualPolynomial (c.map f)))]
    (r : AdjoinRoot (kollarGenericResidualPolynomial c))
    (hr : Polynomial.aeval r (kollarGenericResidualPolynomial c) = 0)
    (φ : AdjoinRoot (kollarGenericResidualPolynomial (c.map f)) →+* M) :
    GeometricallyNoContainedLineThrough
      ((c.map ((AdjoinRoot.of (kollarGenericResidualPolynomial c)).comp
          (algebraMap k (FractionRing (MvPolynomial (Fin 3) k))))).map
        (φ.comp (kollarResidualRootBaseChange f c)))
      (fun i => φ (kollarResidualRootBaseChange f c (kollarResidualLinePoint c r i))) := by
  have hno := kollar_basechanged_residual_center_geometricallyNoContainedLine
    f c hhom hp hsec r hr
  exact geometricCenter_map_comp _ _ (kollarResidualRootBaseChange f c) φ hno

end AllCharacteristics
