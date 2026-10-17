import PfaffianDescent.ActualGlobalConormalOpenChartGeneratorSquare
import PfaffianDescent.ActualAffineConormalNativeSectionClass
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! SOURCE ONLY, UNVERIFIED. The whole genuine original/global conormal
differential agrees with the genuine affine-chart differential after actual
source/target Isos. Native affine ideal sections generate the tensor fiber;
global ideal sections on the original projective scheme are not assumed
to generate it. No map, generator, or fiber square is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v w

/- An ordinary abstract map-composition law. Its proof checks only actual
functoriality and ModuleCat composition; geometric expressions are arguments. -/
private theorem actualGlobalConormalMappedCompApply002
    {R₀ : Type u} [Ring R₀] {C : Type v} [Category.{w} C]
    (F : C ⥤ ModuleCat.{u} R₀) {M N O : C}
    (a : M ⟶ N) (b : N ⟶ O) (x : F.obj M) :
    F.map (a ≫ b) x = F.map b (F.map a x) := by
  rw [Functor.map_comp, ModuleCat.comp_apply]

lemma actualGlobalConormalAffineOpenFullMapSquare
    {k R L : Type u} [CommRing k] [CommRing R] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) (f : Spec (.of R) ⟶ X) [IsOpenImmersion f]
    (rho : R →+* L) (hrho : Function.Surjective rho)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom rho) ≫ f)] :
    let j := Spec.map (CommRingCat.ofHom rho)
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ hrho
    let J := closedImmersionModule (j ≫ f)
    let Es := actualModulePointChartSourceFactorizationIso f j (j ≫ f) rfl
      J (closedImmersionModule j)
      (cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j)
    let Et := actualModulePointChartSourceFactorizationIso f j (j ≫ f) rfl
      (schemeRelativeDifferentials g) (schemeRelativeDifferentials (f ≫ g))
      (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm
    ((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap g (j ≫ f) ≫ Et.hom)).hom =
    ((moduleSpecΓFunctor (R := .of L)).map
      (Es.hom ≫ actualGlobalClosedConormalDifferentialMap (f ≫ g) j)).hom := by
  intro j J Es Et
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ hrho
  let Ji := closedImmersionModule j
  let e := cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j
  let G := moduleSpecΓFunctor (R := .of L)
  let E := (G.mapIso Es).toLinearEquiv.trans (actualAffineConormalTensorEquiv rho hrho)
  let A := (G.map (actualGlobalClosedConormalDifferentialMap g (j ≫ f) ≫ Et.hom)).hom
  let B := (G.map (Es.hom ≫ actualGlobalClosedConormalDifferentialMap (f ≫ g) j)).hom
  have hGenerators (x : RingHom.ker rho) : A (E.symm ((1 : L) ⊗ₜ[R] x)) =
      B (E.symm ((1 : L) ⊗ₜ[R] x)) := by
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x
    let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))
    let z := e.inv.val.app (op ⊤) zx
    let w := actualPointLocalSectionClass (j ≫ f) J (f ''ᵁ ⊤)
      (actualFieldPointFactor_preimage_image_top f j (j ≫ f) rfl) z
    have hz : e.hom.val.app (op ⊤) (e.inv.val.app (op ⊤) zx) = zx := by
      exact congrArg (fun a => a.val.app (op ⊤) zx) e.inv_hom_id
    have hSource : G.map Es.hom w = actualModulePointSectionClass j Ji sx := by
      rw [actualPointLocalChartSourceFactorization_image_top]
      change actualPointLocalSectionClass j Ji ⊤ _
        (e.hom.val.app (op ⊤) (e.inv.val.app (op ⊤) zx)) = _
      rw [hz]
      exact actualPointLocalSectionClass_top_of_unitHom j Ji sx
    have hE : E w = (1 : L) ⊗ₜ[R] x := by
      change actualAffineConormalTensorEquiv rho hrho (G.map Es.hom w) = _
      rw [hSource, actualAffineConormalTensorEquiv_nativeSection]
    have hW : E.symm ((1 : L) ⊗ₜ[R] x) = w := by
      apply E.injective
      rw [E.apply_symm_apply, hE]
    rw [hW]
    have h := actualGlobalConormalOpenChartGeneratorSquare g f j zx
    change G.map Et.hom
        (G.map (actualGlobalClosedConormalDifferentialMap g (j ≫ f)) w) =
      G.map (actualGlobalClosedConormalDifferentialMap (f ≫ g) j)
        (actualPointLocalSectionClass j Ji ⊤ _ zx) at h
    have hTop : actualPointLocalSectionClass j Ji ⊤ (by rfl) zx =
        actualModulePointSectionClass j Ji sx :=
      actualPointLocalSectionClass_top_of_unitHom j Ji sx
    have hNative := h.trans (congrArg
      (fun v => G.map (actualGlobalClosedConormalDifferentialMap (f ≫ g) j) v) hTop)
    change G.map (actualGlobalClosedConormalDifferentialMap g (j ≫ f) ≫ Et.hom) w =
      G.map (Es.hom ≫ actualGlobalClosedConormalDifferentialMap (f ≫ g) j) w
    exact (actualGlobalConormalMappedCompApply002 G
      (actualGlobalClosedConormalDifferentialMap g (j ≫ f)) Et.hom w).trans
      (hNative.trans ((congrArg
        (fun v => G.map (actualGlobalClosedConormalDifferentialMap (f ≫ g) j) v)
        hSource.symm).trans
        (actualGlobalConormalMappedCompApply002 G Es.hom
          (actualGlobalClosedConormalDifferentialMap (f ≫ g) j) w).symm))
  have h : ∀ t : L ⊗[R] RingHom.ker rho, A (E.symm t) = B (E.symm t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      have ht : a ⊗ₜ[R] x = a • ((1 : L) ⊗ₜ[R] x) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, E.symm.map_smul, A.map_smul, B.map_smul, hGenerators]
    | add t s ht hs => simp only [map_add, ht, hs]
  change A = B
  apply LinearMap.ext
  intro w
  exact (congrArg (fun v => A v) (E.symm_apply_apply w)).symm.trans
    ((h (E w)).trans (congrArg (fun v => B v) (E.symm_apply_apply w)))

end PfaffianDescent
