import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericWitnessData
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridResidueFactor
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridFractionPoint

/-! The chosen grid witness supplies the actual ordered generic residue
factor independently of the native finite-datum coefficient algebra. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_gridWitness_exists_orderedResidueFactor
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (w : VoisinDegreeTenSelectedAvoidanceGridGenericFiniteWitness p hp) :
    letI : IsAffine w.U := w.affine
    letI : IsDomain Γ(w.U, ⊤) := w.hdom
    let S := Localization.Away (homogeneousMinorDet w.m w.x)
    letI : IsDomain S := Localization.Away.isDomain w.hdet
    let E := FractionRing S
    let h : Γ(w.U, ⊤) →+* E := (algebraMap S E).comp (algebraMap Γ(w.U, ⊤) S)
    let c := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
    let O := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
    let Q := cubicConfigurationBase p hp 16
    let z := genericPoint O
    ∃ hz : configurationQuotientMap (equationIdeal p hp) 16 z =
        Q.fromSpecStalk (genericPoint Q) (IsLocalRing.closedPoint Q.functionField),
      ∃ g : O.residueField z →+* E,
        Spec.map (CommRingCat.ofHom g) ≫ O.fromSpecResidueField z = c ≫ w.i := by
  dsimp only
  letI : IsAffine w.U := w.affine
  letI : IsIntegral w.U := w.integral
  letI : IsOpenImmersion w.i := w.openImmersion
  letI : IsDomain Γ(w.U, ⊤) := w.hdom
  let S := Localization.Away (homogeneousMinorDet w.m w.x)
  letI : IsDomain S := Localization.Away.isDomain w.hdet
  let E := FractionRing S
  let h : Γ(w.U, ⊤) →+* E := (algebraMap S E).comp (algebraMap Γ(w.U, ⊤) S)
  let c := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
  let O := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
  let Q := cubicConfigurationBase p hp 16
  let z := genericPoint O
  letI : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 16).left := by
    change IsIntegral O
    infer_instance
  letI : IsIntegral (configurationQuotientOpen (equationIdeal p hp) 16).toScheme := by
    change IsIntegral Q
    infer_instance
  have hz : configurationQuotientMap (equationIdeal p hp) 16 z =
      Q.fromSpecStalk (genericPoint Q) (IsLocalRing.closedPoint Q.functionField) := by
    exact (genericPoint_map_of_surjective
      (configurationQuotientMap (equationIdeal p hp) 16)).trans
        Scheme.fromSpecStalk_closedPoint.symm
  have hinj : Function.Injective h :=
    (IsFractionRing.injective S E).comp
      (IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors w.hdet))
  have hcU := voisinDegreeTenSelectedAvoidance_affineFieldPoint_generic h hinj
  have hcO : (c ≫ w.i) (IsLocalRing.closedPoint E) = genericPoint O := by
    change w.i (c (IsLocalRing.closedPoint E)) = _
    rw [hcU]
    exact genericPoint_eq_of_isOpenImmersion w.i
  exact ⟨hz, voisinDegreeTenSelectedAvoidance_genericFieldPoint_exists_residueFactor
    (c ≫ w.i) hcO⟩

end PfaffianDescent
