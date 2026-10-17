import PfaffianDescent.CubicExtensionVectorConfigurationWitness
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridIntegralBase
import AllCharacteristics.ProjectiveFiberSmoothness

/-! Native full-jet witness on the actual original-field configuration space. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
set_option backward.isDefEq.respectTransparency false

theorem exists_cubicSurfaceElevenPoint_ground_configuration_jet_witness
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (x : Fin 11 → Fin 4 → L) (anchor : Fin 11 → Fin 4)
      (pivot : Fin 3 → Fin 3) (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
      (c : Fin 4 → K)
      (hv : ∀ i, p.eval₂ (algebraMap K L) (x i) = 0)
      (hc : ∀ i, (homogeneousLinearForm c).eval₂ (algebraMap K L) (x i) ≠ 0)
      (A : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left),
      (∀ i, x i (anchor i) = 1) ∧
      (∀ i j, i ≠ j → ∀ a : L, a • x i ≠ x j) ∧
      (∀ i, aeval (x (i.castAdd 8))
        (pderiv ((anchor (i.castAdd 8)).succAbove (pivot i)) (p.map (algebraMap K L))) ≠ 0) ∧
      IsUnit (cubicPolynomialJetMinorDet (p.map (algebraMap K L)) x
        (fun i => anchor (i.castAdd 8)) pivot m) ∧
      IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left ∧
      IsIntegral (cubicConfigurationBase p hp 11) ∧
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
      ∀ i, (A ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left =
          cubicExtensionVectorPointInGroundChart p hp c (x i) (hv i) (hc i) := by
  let f := algebraMap K L
  have hp'0 : p.map f ≠ 0 := by
    intro h
    apply hp0
    apply MvPolynomial.map_injective f f.injective
    simpa using h
  letI : Smooth (hypersurfaceToBase (p.map f) (hp.map f)) :=
    smooth_hypersurfaceToBase_map f p hp
  obtain ⟨x, anchor, pivot, m, hx, hpx, hdir, hpivot, hm⟩ :=
    exists_cubicSurfaceElevenPoint_native_polynomialJetMinor (p.map f) (hp.map f) hp'0
  have hv : ∀ i, p.eval₂ (algebraMap K L) (x i) = 0 := by
    intro i
    simpa only [aeval_eq_eval, MvPolynomial.eval_map, f] using hpx i
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i hi
    have hz := congrFun hi (anchor i)
    rw [hx i] at hz
    exact one_ne_zero hz
  letI : Infinite K := CharZero.infinite K
  obtain ⟨c, hc, A, hA, hcoords⟩ := cubicExtensionVector_exists_orderedConfiguration
    11 p hp x hv hx0 hdir
  obtain ⟨hOint, hBint⟩ :=
    voisinDegreeTenSelectedAvoidance_configuration_integral_of_fieldPoint p hp hp0 11 A
  refine ⟨x, anchor, pivot, m, c, hv, hc, A, hx, hdir, hpivot, ?_, hOint, hBint, hA, hcoords⟩
  change IsUnit (homogeneousFullJetEvaluationMinor m x (fun i =>
    cubicPolynomialTangentRow (anchor (i.castAdd 8))
      (fun j => (pderiv j (p.map f)).eval (x (i.castAdd 8))) (pivot i))).det
  simpa only [aeval_eq_eval] using hm

end PfaffianDescent
