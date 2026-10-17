import PfaffianDescent.CorayEntireModelIncidenceCycle
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Genuine native affine evaluation onto the entire literal original-point
model fibre, retaining all nilpotents/multiplicities and the residue factor. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem nativeAppLE_sameMorphism
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  cases h
  rfl

/-- Every point of the ENTIRE original-point pullback lies over an affine
neighborhood of the SAME P. The fibre source is unchanged, not reduced or
replaced by selected support points. Finiteness is unnecessary for this identity. -/
theorem nativeOriginalPointFiber_preimage_neighborhood_eq_top001
    {X Y : Scheme.{u}} (f : Y ⟶ X) (P : closedPoints X)
    (U : X.Opens) (hPU : P.1 ∈ U) :
    let ep := X.fromSpecResidueField P.1
    let a := pullback.snd ep f
    a ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
  let ep := X.fromSpecResidueField P.1
  let a := pullback.snd ep f
  let c := pullback.fst ep f
  have hMap : a ≫ f = c ≫ ep := (pullback.condition (f := ep) (g := f)).symm
  ext z
  change f (a z) ∈ U ↔ True
  have hPoint : f (a z) = P.1 :=
    (congrArg (fun g : pullback ep f ⟶ X => g z) hMap).trans (Scheme.fromSpecResidueField_apply P.1 (c z))
  rw [hPoint]
  exact iff_true_intro hPU

variable {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]

/-- The actual SAME I/D/P finite coefficient morphism constructs a surjective
native affine map to sections of its ENTIRE literal fibre and proves its
factorization square through the original residue-field spectrum. No desired
surjectivity, commutative square, rank, reducedness or incidence count is input. -/
theorem originalPointModelIncidence_entireFiber_affineEvaluation_surjective_and_residueFactorSquare001
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) (U : (scheme I).Opens)
    (hU : IsAffineOpen U) (hPU : P.1 ∈ U) :
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hID
    let Z := pullback ep f
    let a := pullback.snd ep f
    let c := pullback.fst ep f
    ∃ hA : (⊤ : Z.Opens) ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U),
    ∃ hE : (⊤ : (Spec ((scheme I).residueField P.1)).Opens) ≤ ep ⁻¹ᵁ U,
      Function.Surjective (a.appLE (f ⁻¹ᵁ U) ⊤ hA) ∧
        f.app U ≫ a.appLE (f ⁻¹ᵁ U) ⊤ hA =
          ep.appLE U ⊤ hE ≫ c.appLE ⊤ ⊤ (by simp) := by
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let Z := pullback ep f
  let a := pullback.snd ep f
  let c := pullback.fst ep f
  let V := f ⁻¹ᵁ U
  letI : IsFinite f := (coefficientComponentToOriginal_finite_and_toBase I D hID).1
  letI : IsClosedImmersion ep := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion a := inferInstance
  have hV : IsAffineOpen V := hU.preimage f
  have hTop : a ⁻¹ᵁ V = ⊤ := nativeOriginalPointFiber_preimage_neighborhood_eq_top001 f P U hPU
  have hA : (⊤ : Z.Opens) ≤ a ⁻¹ᵁ V := hTop.symm.le
  have hE : (⊤ : (Spec ((scheme I).residueField P.1)).Opens) ≤ ep ⁻¹ᵁ U := by
    intro z _
    change ep z ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hPU
  have hSurjective : Function.Surjective (a.appLE V ⊤ hA) := by
    have hApp : Function.Surjective (a.app V) := a.app_surjective V hV
    have hRestriction : (homOfLE hA : (⊤ : Z.Opens) ⟶ a ⁻¹ᵁ V) = eqToHom hTop.symm :=
      Subsingleton.elim _ _
    rw [Scheme.Hom.appLE, hRestriction]
    exact (ConcreteCategory.bijective_of_isIso
      (Z.presheaf.map (eqToHom hTop.symm).op)).surjective.comp hApp
  have hMap : a ≫ f = c ≫ ep := (pullback.condition (f := ep) (g := f)).symm
  have hLeft : (⊤ : Z.Opens) ≤ (a ≫ f) ⁻¹ᵁ U := by
    intro z _
    change f (a z) ∈ U
    have hPoint : f (a z) = P.1 :=
      (congrArg (fun g : Z ⟶ scheme I => g z) hMap).trans (Scheme.fromSpecResidueField_apply P.1 (c z))
    rw [hPoint]
    exact hPU
  have hRight : (⊤ : Z.Opens) ≤ (c ≫ ep) ⁻¹ᵁ U := by
    intro z _
    change ep (c z) ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hPU
  refine ⟨hA, hE, hSurjective, ?_⟩
  calc
    f.app U ≫ a.appLE V ⊤ hA = (a ≫ f).appLE U ⊤ hLeft := by
      rw [f.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE a f U V ⊤ le_rfl hA
    _ = (c ≫ ep).appLE U ⊤ hRight := nativeAppLE_sameMorphism hMap U ⊤ hLeft hRight
    _ = ep.appLE U ⊤ hE ≫ c.appLE ⊤ ⊤ (by simp) :=
      (Scheme.Hom.appLE_comp_appLE c ep U ⊤ ⊤ hE (by simp)).symm

end PfaffianDescent.Coray
