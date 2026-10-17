import PfaffianDescent.CubicElevenPointGroundKernelData
import PfaffianDescent.CubicFieldPointScaledComponentCoordinates
import PfaffianDescent.CubicElevenPointGroundRestrictionSurjective
import PfaffianDescent.CubicPolynomialJetEquation

/-! Apply an interpolation witness to the actual canonical degree-eleven
chart restriction. GroundKernelFactory derives this witness internally from
the original smooth cubic; this helper retains the interpolation hypotheses. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

local instance {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hO : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left] :
    IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := hO

abbrev cubicElevenPointGroundChartKernel_of_interpolation
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    [IsIntegral (cubicConfigurationBase p hp 11)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 11).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
      cubicConfigurationToBase p hp 11)
    (U : Scheme.{u}) [IsAffine U]
    (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
    (c : Fin 4 → K)
    (t : Fin 11 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (cubicGroundChartClass p hp c)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
        (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 k).left)
    (b : K →+* Γ(U, ⊤))
    (hb : b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom))
    (x : Fin 11 → Fin 4 → Γ(U, ⊤))
    (hx : x = fun k r => pulledLinearChartCoordinate (equationIdeal p hp)
      (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) r)
    (h : Γ(U, ⊤) →+* E)
    (β : (cubicConfigurationBase p hp 11).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
        (cubicConfigurationBase p hp 11).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp 11)) =
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ i) ≫
        configurationQuotientMap (equationIdeal p hp) 11)
    (anchor : Fin 11 → Fin 4) (pivot : Fin 3 → Fin 3)
    (y : Fin 11 → Fin 4 → E)
    (hden : ∀ k, h (x k (anchor k)) ≠ 0)
    (hy : ∀ k r, y k r = (h (x k (anchor k)))⁻¹ * h (x k r))
    (hpy : ∀ k, (p.map (h.comp b)).eval (y k) = 0)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction y
      (cubicFullJetCoordinates y (cubicPolynomialSurfaceTangentRows
        (p.map (h.comp b)) y (fun k => anchor (k.castAdd 8)) pivot)))) := by
  classical
  let F := (cubicConfigurationBase p hp 11).functionField
  let P := p.map a.hom
  let hP := hp.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme p hp 11 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 11 a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  let L := Γ(D.val.subscheme, ⊤)
  letI : Field L :=
    (cubicConfigurationGenericFiniteSubscheme_isField p hp 11 a ha (0 : Fin 11)).toField
  letI : FiniteDimensional F L := finiteSchemeCoefficient_finite pD
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (h.comp b).toAlgebra
  let J := cubicFullJetCoordinates y (cubicPolynomialSurfaceTangentRows
    (p.map (h.comp b)) y (fun k => anchor (k.castAdd 8)) pivot)
  have hresidue : ∀ k r, (J k r).fst = y (k.castAdd 8) r := by
    intro k r
    exact cubicFullJetCoordinates_residue y _ k r
  let hkernel :=
    cubicElevenPointCanonicalChart_exists_kernel p hp a ha U i c t ht b hb x hx h β hβ
      (anchor 0) (hden 0) y (fun k => (h (x k (anchor k)))⁻¹) hy J hresidue hfull
  let g := Classical.choose hkernel
  have hgb := (Classical.choose_spec hkernel).1
  have hgi := (Classical.choose_spec hkernel).2.1
  have hmem := (Classical.choose_spec hkernel).2.2.1
  have hdim := (Classical.choose_spec hkernel).2.2.2.1
  have hspan := (Classical.choose_spec hkernel).2.2.2.2
  let α : Fin 11 → (L →ₐ[F] E) := fun k =>
    cubicConfigurationOrderedFieldComponentAlgHom p hp 11
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ i) β hβ a ha k
  let hnormalized := cubicConfigurationAffineField_normalized_components
    p hp 11 a ha U i c t ht b hb x hx h β hβ
  let he := Classical.choose hnormalized
  let hn := Classical.choose (Classical.choose_spec hnormalized)
  let hpoint := Classical.choose_spec (Classical.choose_spec hnormalized)
  have hcoordinates : ∀ k, h (x k (anchor 0)) ≠ 0 ∧ ∀ r,
      α k (g (linearChartCoordinate (equationIdeal P hP)
        (coordinate (equationIdeal P hP) (anchor 0))
        (coordinate_mem (equationIdeal P hP) (anchor 0)) r)) =
      (h (x k (anchor 0)))⁻¹ * h (x k r) := by
    intro k
    exact cubicFieldPoint_component_coordinates_eq_selected_ratios a.hom p hp P hP
      (finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D) (anchor 0) g hgi
      (α k).toRingHom (fun r => h (x k r)) (homogeneousLinearForm c)
      (homogeneousLinearForm_isHomogeneous c) (he k) (hn k) (hpoint k)
  have hratios : ∀ k, y k (anchor 0) ≠ 0 ∧ ∀ r,
      (y k (anchor 0))⁻¹ * y k r =
        (h (x k (anchor 0)))⁻¹ * h (x k r) := by
    intro k
    exact cubicFieldPoint_scaled_coordinate_ratios (fun r => h (x k r)) (y k)
      (h (x k (anchor k)))⁻¹ (inv_ne_zero (hden k)) (hy k) (anchor 0) (hcoordinates k).1
  have hcoeff : h.comp b = β.comp a.hom :=
    cubicConfigurationGeneric_affineFieldPoint_coefficients p hp 11 a ha i h b hb β hβ
  have honto : Function.Surjective (cubicHomogeneousChartRestriction (equationIdeal P hP)
      (coordinate (equationIdeal P hP) (anchor 0))
      (coordinate_mem (equationIdeal P hP) (anchor 0)) g) :=
    cubicElevenPoint_groundRestriction_surjective _
      (cubicConfigurationGenericFiniteSubscheme_finrank p hp 11 a ha) hdim
  have hPmap : P.map β = p.map (h.comp b) := by
    rw [show P = p.map a.hom by rfl, MvPolynomial.map_map, ← hcoeff]
  have hvalues : ∀ k, aeval (y k) (P.map β) = 0 := by
    intro k
    rw [hPmap]
    change (p.map (h.comp b)).eval (y k) = 0
    exact hpy k
  have hJp0 : ∀ k, aeval (J k) (p.map (h.comp b)) = 0 :=
    cubicPolynomialSurfaceTangentRows_firstJets_cubic_of_eval (p.map (h.comp b)) y
      (fun k => anchor (k.castAdd 8)) pivot hpy
  have hJp : ∀ k, aeval (J k) (P.map β) = 0 :=
    (congrArg (fun Q => ∀ k, aeval (J k) Q = 0) hPmap).mpr hJp0
  exact cubicFieldChartKernelData_of_witnesses P hP
    (finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D)
    β (anchor 0) g α y J hgb hgi (fun k => (hratios k).1)
    (fun k r => ((hcoordinates k).2 r).trans ((hratios k).2 r).symm)
    hvalues hresidue hJp hfull hmem honto hdim hspan

end PfaffianDescent
