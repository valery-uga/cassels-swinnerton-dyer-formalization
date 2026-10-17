import PfaffianDescent.SingleClosedPointFiniteSchemeAlgebra
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice

/-! SOURCE ONLY / UNVERIFIED. Extract the actual map on the FIXED original
point chart from EVERY supplied finite rank-eight closed subscheme supported
at that point. Residue surjectivity, locality, the coefficient-field lift,
the dual presentation, and the chart-map reduction are all derived internally.
There is no supplied dual map or comparison certificate. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem actualOriginal_allSingleSupport_rankEight_nativeDualMap
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hSupport : Set.range i = {P.1})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    ∃ e : Γ(Z, ⊤) ≃ₐ[K] DualNumber L,
      ∃ phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L,
        Function.Surjective phi ∧
        (∀ r, (phi r).fst = C.residue r) ∧
        Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
            chartι (equationIdeal p hp) C.index =
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  letI : IsLocalRing Γ(Z, ⊤) := singleSupport_globalSections_isLocalRing i P.1 hSupport
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let L := (hypersurface p hp).residueField P.1
  let R := ChartRing (equationIdeal p hp) C.index
  letI : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  let rho := singleClosedSupportResidueAlgHom i (hypersurfaceToBase p hp) P hSupport
  have hrho : Function.Surjective rho :=
    singleClosedSupportResidueAlgHom_surjective i (hypersurfaceToBase p hp) P hSupport
  have hL : finrank K L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree
      (hypersurfaceToBase p hp) P).trans hP
  have hA : finrank K Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hZ
  obtain ⟨e0, he0⟩ :=
    lengthEightLocal_quarticResidue_dual_equiv_with_residue rho hrho hL hA
  let e := e0.symm
  have he (a : Γ(Z, ⊤)) : (e a).fst = rho a := by
    have h := he0 (e a)
    simpa only [e, AlgEquiv.apply_symm_apply] using h.symm
  have hrange : Set.range i ⊆ Set.range (chartι (equationIdeal p hp) C.index) := by
    rintro _ ⟨z, rfl⟩
    have hiz : i z = P.1 := by
      apply Set.mem_singleton_iff.mp
      rw [← hSupport]
      exact Set.mem_range_self z
    rw [hiz]
    exact actualOriginalQuarticCotangentChartChoice_contains_original_point p hp P hP
  let iU := IsOpenImmersion.lift (chartι (equationIdeal p hp) C.index) i hrange
  have hU : iU ≫ chartι (equationIdeal p hp) C.index = i :=
    IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (iU ≫ chartι (equationIdeal p hp) C.index) :=
    hU.symm ▸ inferInstance
  letI : IsClosedImmersion iU :=
    IsClosedImmersion.of_comp iU (chartι (equationIdeal p hp) C.index)
  let gCat := Spec.preimage (Z.isoSpec.inv ≫ iU)
  let g : R →+* Γ(Z, ⊤) := gCat.hom
  have hg : Spec.map gCat = Z.isoSpec.inv ≫ iU := Spec.map_preimage _
  have hgs : Function.Surjective g :=
    AllCharacteristics.spec_preimage_surjective_of_closedImmersion (Z.isoSpec.inv ≫ iU)
  have hpoint : Spec.map (CommRingCat.ofHom g) ≫
      chartι (equationIdeal p hp) C.index = Z.isoSpec.inv ≫ i := by
    change Spec.map gCat ≫ _ = _
    rw [hg, Category.assoc, hU]
  have hgb : g.comp (chartBaseMap (equationIdeal p hp) C.index) =
      algebraMap K Γ(Z, ⊤) := by
    have hcat : CommRingCat.ofHom (chartBaseMap (equationIdeal p hp) C.index) ≫ gCat =
        CommRingCat.ofHom (algebraMap K Γ(Z, ⊤)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, ← chartι_toBase, finiteSchemeCoefficient_spec]
      have hUbase : iU ≫ chartι (equationIdeal p hp) C.index ≫
          hypersurfaceToBase p hp = i ≫ hypersurfaceToBase p hp := by
        rw [← Category.assoc, hU]
      rw [Category.assoc]
      exact congrArg (fun f => Z.isoSpec.inv ≫ f) hUbase
    exact congrArg CommRingCat.Hom.hom hcat
  let qZ := singleClosedSupportResidueLift i P hSupport
  have hqBase : qZ ≫ (i ≫ hypersurfaceToBase p hp) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← Category.assoc, singleClosedSupportResidueLift_comp,
      AllCharacteristics.pointAlgebra_spec]
  have hrhoSpec : Spec.map (CommRingCat.ofHom rho.toRingHom) = qZ ≫ Z.isoSpec.hom :=
    finiteSchemePointAlgHom_spec (i ≫ hypersurfaceToBase p hp) qZ
      (algebraMap K L) hqBase
  have hgLPoint : Spec.map (CommRingCat.ofHom (rho.toRingHom.comp g)) ≫
      chartι (equationIdeal p hp) C.index =
        (hypersurface p hp).fromSpecResidueField P.1 := by
    change Spec.map (CommRingCat.ofHom g ≫ CommRingCat.ofHom rho.toRingHom) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, hpoint, hrhoSpec]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact singleClosedSupportResidueLift_comp i P hSupport
  have hresidue : rho.toRingHom.comp g = C.residue := by
    have hspec : Spec.map (CommRingCat.ofHom (rho.toRingHom.comp g)) =
        Spec.map (CommRingCat.ofHom C.residue) :=
      (cancel_mono (chartι (equationIdeal p hp) C.index)).mp
        (hgLPoint.trans C.factorization.symm)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)
  let gK : R →ₐ[K] Γ(Z, ⊤) :=
    { g with commutes' := fun c => RingHom.congr_fun hgb c }
  let phi : R →ₐ[K] DualNumber L := e.toAlgHom.comp gK
  have hred (r : R) : (phi r).fst = C.residue r := by
    exact (he (g r)).trans (RingHom.congr_fun hresidue r)
  refine ⟨e, phi, e.surjective.comp hgs, hred, ?_⟩
  change Spec.map (CommRingCat.ofHom g ≫ CommRingCat.ofHom e.toRingHom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, hpoint]

end PfaffianDescent
