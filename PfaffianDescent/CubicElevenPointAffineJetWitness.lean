import PfaffianDescent.CubicElevenPointGroundConfiguration
import PfaffianDescent.CubicGroundChartConfigurationCoordinates
import PfaffianDescent.CubicElevenPointCoordinateLocalization

/-!
The native full-jet witness on actual integral affine configuration
coordinates, retaining their literal ground-field and specialization maps.
-/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem exists_cubicSurfaceElevenPoint_native_affineJet_witness
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (_ : IsIntegral U)
      (c : Fin 4 → K)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (a : Spec (.of L) ⟶ U)
      (t : Fin 11 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c)))))
      (b : K →+* Γ(U, ⊤)) (f : Γ(U, ⊤) →+* L)
      (u : Fin 11 → Fin 4 → Γ(U, ⊤)) (v : Fin 11 → Fin 4 → L)
      (anchor : Fin 11 → Fin 4) (pivot : Fin 3 → Fin 3)
      (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3),
      IsOpenImmersion i ∧ _root_.IsDomain Γ(U, ⊤) ∧
      b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
        (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom) ∧
      f = voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a ∧
      u = (fun k z => pulledLinearChartCoordinate (equationIdeal p hp)
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) z) ∧
      f.comp b = algebraMap K L ∧
      (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
          (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
          (by decide : 0 < 1) =
        (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 k).left) ∧
      (∀ k, (p.map b).eval (u k) = 0) ∧
      (∀ k, ((homogeneousLinearForm c).map b).eval (u k) = 1) ∧
      (∀ k z, f (u k z) = cubicGroundChartNormalizedVector c (v k) z) ∧
      (∀ k, (homogeneousLinearForm c).eval₂ (algebraMap K L) (v k) ≠ 0) ∧
      (∀ k, v k (anchor k) = 1) ∧
      IsUnit (cubicPolynomialJetMinorDet (p.map (algebraMap K L)) v
        (fun k => anchor (k.castAdd 8)) pivot m) := by
  classical
  obtain ⟨v, anchor, pivot, m, c, hv, hc, A, hanchor, _, _, hm, hOint, hBint, hA, hcoords⟩ :=
    exists_cubicSurfaceElevenPoint_ground_configuration_jet_witness (L := L) p hp hp0
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left := hOint
  letI : IsIntegral (cubicConfigurationBase p hp 11) := hBint
  obtain ⟨U, Q, hUa, _, i, _, _, a, t, hi, _, _, _, hUint, _, ha, _, _, _, ht, _⟩ :=
    cubicGroundChart_exists_integral_affine_configuration_charts p hp 11 c v hv hc A hcoords
  letI : IsAffine U := hUa
  letI : IsIntegral U := hUint
  let b : K →+* Γ(U, ⊤) := voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
    (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom)
  let f : Γ(U, ⊤) →+* L := voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a
  let u : Fin 11 → Fin 4 → Γ(U, ⊤) := fun k z =>
    pulledLinearChartCoordinate (equationIdeal p hp) (cubicGroundChartClass p hp c)
      (cubicGroundChartClass_mem p hp c) U (t k) z
  have habase : a ≫ (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← Category.assoc, ha]
    exact hA
  have hfb : f.comp b = algebraMap K L :=
    voisinDegreeTenSelectedAvoidance_fieldPointSpecialization_base U _ a habase
  have hfu : ∀ k z, f (u k z) = cubicGroundChartNormalizedVector c (v k) z := by
    intro k z
    apply cubicGroundChart_fieldPointSpecialization_coordinate p hp c (v k) (hv k) (hc k)
      U a (t k)
    rw [Category.assoc, ht k]
    change ((a ≫ i) ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 k).left = _
    rw [ha]
    exact hcoords k
  refine ⟨U, hUa, hUint, c, i, a, t, b, f, u, v, anchor, pivot, m,
    hi, inferInstance, rfl, rfl, rfl, hfb, ht, ?_, ?_, hfu, hc, hanchor, hm⟩
  · intro k
    exact (cubicGroundChart_pulled_equations p hp c 11 U i t ht k).1
  · intro k
    exact (cubicGroundChart_pulled_equations p hp c 11 U i t ht k).2

end PfaffianDescent
