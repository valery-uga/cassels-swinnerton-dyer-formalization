import PfaffianDescent.SchemeModuleCanonicalSignedPointTensorWord
import PfaffianDescent.SchemeModuleClosedPointCenteredStalkFieldRanges
import PfaffianDescent.SchemeModuleClosedPointOffCenterStalkFieldImage
import PfaffianDescent.SchemeModuleFixedFrameTensorStalkFieldMultiplication
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Actual signed-step stalk range and local exponent, with original
factor order and original common-complement chart. Centered factors use
ONE actual generator, while off-center factors have exponent zero.
No product-image, valuation or comparison certificate is assumed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual local order of a point tensor: ideal contributes +1, dual
contributes -1, and a factor away from the fixed center contributes 0. -/
def schemeSignedClosedPointTensorLocalOrder
    (P : closedPoints X) (operation : closedPoints X × Bool) : ℤ := by
  classical
  exact if operation.1 = P then if operation.2 then -1 else 1 else 0

/-- Sum of the actual local orders of the specified signed word. Repeated
points are retained; this is negative count minus positive count at P. -/
def schemeSignedPointTensorWordLocalOrder
    (P : closedPoints X) (ops : List (closedPoints X × Bool)) : ℤ :=
  (ops.map (schemeSignedClosedPointTensorLocalOrder P)).sum

private theorem range_mul_swap {A B F : Type*} [CommMonoid F]
    (f : A → F) (g : B → F) :
    Set.range (fun p : A × B => f p.1 * g p.2) =
      Set.range (fun p : B × A => g p.1 * f p.2) := by
  apply Set.Subset.antisymm
  · rintro z ⟨p, hp⟩
    exact ⟨⟨p.2, p.1⟩, (mul_comm _ _).trans hp⟩
  · rintro z ⟨p, hp⟩
    exact ⟨⟨p.2, p.1⟩, (mul_comm _ _).trans hp⟩

variable {K : Type u} [Field K] [IsIntegral X]

/-- The SAME canonical signed-step map has the FULL product image of
the original L map and canonical factor map. The negative ideal-first
tensor order is retained internally; commutativity only reorders field
values. Genuine factor/L rank-one geometry supplies pure-germ generation. -/
theorem schemeModuleSignedClosedPointTensor_stalkRange_product
    (pi : X ⟶ Spec (CommRingCat.of K)) (operation : closedPoints X × Bool)
    (C : X.Opens) [Nonempty C] (hPC : operation.1.1 ∉ C)
    (L : X.Modules) (hL : schemeModuleLocallyRankOne L)
    (eL : L.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (hM : ∀ Q : closedPoints X,
      let i := X.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
      schemeModuleLocallyRankOne (closedImmersionModule i)) (x : X) :
    let F := schemeModuleSignedClosedPointFactor operation
    let T := schemeModuleSignedClosedPointTensor operation L
    letI := schemeModuleStalkModule L x
    letI := schemeModuleStalkModule F x
    letI := schemeModuleStalkModule T x
    Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi T C
      (schemeModuleSignedClosedPointTensorOverCanonicalIso operation C hPC L eL) x) =
      Set.range (fun p : L.presheaf.stalk x × F.presheaf.stalk x =>
        @HMul.hMul X.functionField X.functionField X.functionField inferInstance
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi L C eL x p.1)
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi F C
            (schemeModuleSignedClosedPointFactorOverCanonicalIso operation C hPC) x p.2)) := by
  dsimp only
  letI := schemeModuleStalkModule L x
  letI := schemeModuleStalkModule (schemeModuleSignedClosedPointFactor operation) x
  letI := schemeModuleStalkModule (schemeModuleSignedClosedPointTensor operation L) x
  rcases operation with ⟨Q, sign⟩
  let i := X.fromSpecResidueField Q.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
  let M := (show X.Modules from closedImmersionModule i)
  have hIdeal : schemeModuleLocallyRankOne M := hM Q
  cases sign
  · exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_range_tensor_product
      pi M L hIdeal hL C (schemeModuleClosedPointIdealOverCanonicalIso Q C hPC) eL x).trans
        (range_mul_swap _ _)
  · exact schemeModuleFixedFrameStalkToFunctionFieldLinearMap_range_tensor_product
      pi L (SchemeModuleInternalHom.dual M) hL (schemeModuleLocallyRankOne_dual M hIdeal) C
      eL (schemeModuleClosedPointDualOverCanonicalIso Q C hPC) x

/-- The canonical actual signed-factor image is a power of the SINGLE
actual affine generator chosen at P. A centered sign uses its proved
positive/negative range; an off-center factor uses its actual unit image.
Only actual regular-principal geometry is input, never an image formula. -/
theorem schemeModuleSignedClosedPointFactor_stalkRange_localOrder
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (V : X.affineOpens) (hPV : P.1 ∈ V.1)
    (C : X.Opens) [Nonempty C]
    (operation : closedPoints X × Bool) (hQC : operation.1.1 ∉ C) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let F := schemeModuleSignedClosedPointFactor operation
    letI := schemeModuleStalkModule F P.1
    ∀ (m : M.val.obj (op V.1)),
      @IsRegular (Γ(X, V.1)) inferInstance
        ((closedImmersionModuleToUnit i).val.app (op V.1) m) →
      i.ker.ideal V = Ideal.span
        ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1)) →
      let zP := X.presheaf.germ V.1 P.1 hPV
        ((closedImmersionModuleToUnit i).val.app (op V.1) m)
      Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi F C
        (schemeModuleSignedClosedPointFactorOverCanonicalIso operation C hQC) P.1) =
        Set.range (fun r : X.presheaf.stalk P.1 =>
          @HMul.hMul X.functionField X.functionField X.functionField inferInstance
            (algebraMap (X.presheaf.stalk P.1) X.functionField r)
            ((algebraMap (X.presheaf.stalk P.1) X.functionField zP) ^
              schemeSignedClosedPointTensorLocalOrder P operation)) := by
  classical
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI := schemeModuleStalkModule (schemeModuleSignedClosedPointFactor operation) P.1
  intro m hreg hprincipal
  rcases operation with ⟨Q, sign⟩
  by_cases hQP : Q = P
  · subst Q
    have h := schemeModuleClosedPointFixedComplement_centeredStalkFieldRanges
      pi P C hQC V hPV m hreg hprincipal
    cases sign
    · simpa only [schemeModuleSignedClosedPointFactor, schemeModuleSignedClosedPointFactorOverCanonicalIso,
        schemeSignedClosedPointTensorLocalOrder, Bool.false_eq_true, ite_true, ite_false, zpow_one] using h.2.1
    · simpa only [schemeModuleSignedClosedPointFactor, schemeModuleSignedClosedPointFactorOverCanonicalIso,
        schemeSignedClosedPointTensorLocalOrder, Bool.false_eq_true, ite_true, ite_false, zpow_neg_one, div_eq_mul_inv] using h.2.2
  · have hPQ : P.1 ≠ Q.1 := fun he => hQP (Subtype.ext he.symm)
    cases sign
    · simpa only [schemeModuleSignedClosedPointFactor, schemeModuleSignedClosedPointFactorOverCanonicalIso,
        schemeSignedClosedPointTensorLocalOrder, if_neg hQP, zpow_zero, mul_one] using
        (schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_offCenter pi Q C hQC P.1 hPQ).2
    · simpa only [schemeModuleSignedClosedPointFactor, schemeModuleSignedClosedPointFactorOverCanonicalIso,
        schemeSignedClosedPointTensorLocalOrder, if_neg hQP, zpow_zero, mul_one] using
        (schemeModuleClosedPointDualFixedComplementStalkToFunctionField_offCenter pi Q C hQC P.1 hPQ).2

end PfaffianDescent.Coray
