import PfaffianDescent.ActualRescaledTensorComponentSquare
import PfaffianDescent.FourTangentDualComponentAmbientSquare
import AllCharacteristics.FiniteSigmaSpec

/-! SOURCE ONLY, UNVERIFIED. The four actual component squares imply the
whole nilpotent scheme square via the genuine finite spectrum coproduct. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual dual-factor inclusions determine a morphism on the whole
product spectrum. This uses a coproduct Iso, not equality on point sets. -/
theorem fourDual_actual_components_hom_ext {X : Scheme.{u}}
    (f g : Spec (.of (FourTangentDualAlgebra K)) ⟶ X)
    (h : ∀ row, Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) row)) ≫ f =
      Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) row)) ≫ g) : f = g := by
  let c := sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K))
  letI : IsIso c := AllCharacteristics.isIso_sigmaSpec_const_finite (Fin 4) (DualNumber K)
  apply (cancel_epi c).mp
  apply Sigma.hom_ext
  intro row
  simpa only [c, ← Category.assoc, ι_sigmaSpec] using h row

/-- Full embedded source square, not just a comparison of homogeneous
vanishing kernels. All four nilpotent components are transported jointly. -/
theorem actualRescaledQuarticSchemeIso_whole_frame_square
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Algebra k K]
    [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (x : Fin 4 → Γ(Z, ⊤)) (j : Fin 4) (hxj : x j = 1)
    (pi : Equiv.Perm (Fin 4)) (hpi : pi 0 = j)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x (pi r)) = inl (b r) + inr (v r))
    (hb0 : b 0 = 1) (full : Fin 4 ≃ (L →ₐ[k] K))
    (hs : Submodule.span K
      (Set.range (fun sigma : L →ₐ[k] K => fun r => sigma (b r))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0) :
    letI := finiteSchemeCoefficientAlgebra t
    let S := actualRescaledQuarticSchemeIso t eA b full l hl
    let Q := (finiteSchemeActualFieldBaseChangeIso (K := K) t).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
    let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
    S.inv ≫ Q ≫ ambientProjectiveRenameMap (K := K) pi =
      fourTangentDualToProjective U ≫ quotientProjMap ⊥ ≫
        (linearCoordinateChangeAmbientIso
          (basisCoordinateMatrix (conjugateBasis full b hs))
          (basisCoordinateMatrix_isUnit _)).inv := by
  letI := finiteSchemeCoefficientAlgebra t
  let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
  have hdiag : ∀ row, U row row = 0 := by
    intro row
    simp [U, rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  apply fourDual_actual_components_hom_ext
  intro row
  have hModel : Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) row)) ≫
      fourTangentDualToProjective U ≫ quotientProjMap ⊥ =
      ambientNormalizedCoordinateChartPoint (F := K) (tangentDualPoint U row) row
        (by simp [tangentDualPoint, hdiag]) := by
    have h := fourTangentDual_component_actual_ambient_square U hdiag row
    have hCoordinates :
        (fun r => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) row r) +
          TrivSqZeroExt.inr (U row r)) = tangentDualPoint U row := by
      funext r
      rfl
    have hPointCongr (a b : Fin 4 → DualNumber K) (ha : a row = 1) (hb : b row = 1)
        (hab : a = b) : ambientNormalizedCoordinateChartPoint (F := K) a row ha =
          ambientNormalizedCoordinateChartPoint (F := K) b row hb := by
      subst b
      rfl
    exact h.trans (hPointCongr _ _ _ _ hCoordinates)
  have hComponent := actualRescaledQuarticSchemeIso_component_frame_square
    t eA x j hxj pi hpi b v hx hb0 full hs l hl row
  have hBack := congrArg (fun f => f ≫
    (linearCoordinateChangeAmbientIso
      (basisCoordinateMatrix (conjugateBasis full b hs))
      (basisCoordinateMatrix_isUnit _)).inv) hModel.symm
  simpa only [Category.assoc] using hComponent.trans hBack

end PfaffianDescent.QuarticNet
