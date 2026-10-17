import PfaffianDescent.CorayNormalizationClosedPointIdealStalk
import PfaffianDescent.VoisinFixedCurveStalkwiseCartierCriterion

/-! Spread the SAME actual point ideal from its internally derived DVR
stalk to an ACTUAL affine neighborhood, with an ACTUAL section of the
original ideal module and its original inclusion. No principal/local-free/
comparison/evaluation certificate in the primitive p/q caller.
SOURCE ONLY / UNVERIFIED. Invertibility and inverse pole module remain later. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Natural localization intermediate: transfer an ACTUAL localized ideal
generator along the canonical localization equivalence, then reuse the
genuine finite-denominator spreading proof. The geometric caller below
internally proves its finite generation, generator and exact ideal equality. -/
theorem actualPrimeLocalization_regularPrincipal_spreads
    {A R : Type u} [CommRing A] [IsDomain A] [CommRing R]
    (I Q : Ideal A) [Q.IsPrime] [Algebra A R] [IsLocalization Q.primeCompl R]
    (hfg : I.FG) (ϖ : R) (hϖ : ϖ ≠ 0)
    (hI : I.map (algebraMap A R) = Ideal.span ({ϖ} : Set R)) :
    ∃ s : A, s ∉ Q ∧ ∃ z : A, z ∈ I ∧
      IsRegular (algebraMap A (Localization.Away s) z) ∧
      I.map (algebraMap A (Localization.Away s)) =
        Ideal.span ({algebraMap A (Localization.Away s) z} : Set (Localization.Away s)) := by
  let S := Localization.AtPrime Q
  let E := IsLocalization.algEquiv Q.primeCompl R S
  have hE : E.toRingHom.comp (algebraMap A R) = algebraMap A S := by
    ext a
    exact E.commutes a
  have hmap : (I.map (algebraMap A R)).map E.toRingHom = I.map (algebraMap A S) := by
    rw [Ideal.map_map, hE]
  have hprincipal : I.map (algebraMap A S) = Ideal.span ({E ϖ} : Set S) := by
    rw [← hmap, hI, Ideal.map_span, Set.image_singleton]
    rfl
  have hnonzero : E ϖ ≠ 0 := by simpa only [map_zero] using E.injective.ne hϖ
  exact ideal_localRegularPrincipal_spreads_to_basicOpen I Q hfg
    ⟨E ϖ, isRegular_iff_ne_zero.mpr hnonzero, hprincipal⟩

/-- Generic natural local-DVR lemma. The SAME affine ideal of an actual
closed point is principal on an ACTUAL smaller affine basic open. Both the
generator and equality use original scheme restriction maps, not a supplied
section-isomorphism or ideal-comparison condition. -/
theorem closedPointIdeal_affine_regularPrincipal_neighborhood_of_stalk_isDVR
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    (U : X.affineOpens) (hPU : P.1 ∈ U.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∃ s : Γ(X, U), P.1 ∈ X.basicOpen s ∧
      ∃ z : Γ(X, U), z ∈ i.ker.ideal U ∧
        IsRegular (X.presheaf.map (homOfLE (X.basicOpen_le s)).op z) ∧
        i.ker.ideal ⟨X.basicOpen s, U.2.basicOpen s⟩ =
          Ideal.span ({X.presheaf.map (homOfLE (X.basicOpen_le s)).op z} :
            Set Γ(X, X.basicOpen s)) := by
  classical
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let A := Γ(X, U)
  let R := X.presheaf.stalk P.1
  let Q := (U.2.primeIdealOf ⟨P.1, hPU⟩).asIdeal
  let I := i.ker.ideal U
  letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
  letI : IsDomain A := inferInstance
  letI : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  letI : Algebra A R := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P.1, hPU⟩
  letI : Q.IsPrime := inferInstance
  letI : IsLocalization Q.primeCompl R := U.2.isLocalization_stalk ⟨P.1, hPU⟩
  have hfg : I.FG := IsNoetherian.noetherian I
  have hpoint : i (default : Spec (X.residueField P.1)) = P.1 :=
    Scheme.fromSpecResidueField_apply P.1 _
  have hpointU : i (default : Spec (X.residueField P.1)) ∈ U.1 := by
    rw [hpoint]
    exact hPU
  have hmax : I.map (algebraMap A R) = IsLocalRing.maximalIdeal R := by
    let predicate : U.1 → Prop := fun x =>
      (i.ker.ideal U).map (X.presheaf.germ U.1 x.1 x.2).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)
    have hsub : (⟨i (default : Spec (X.residueField P.1)), hpointU⟩ : U.1) =
        ⟨P.1, hPU⟩ := Subtype.ext hpoint
    exact Eq.mp (congrArg predicate hsub)
      (cubicClosedPointSerreZeroIdealStalk_map_eq_maximal i U
        (default : Spec (X.residueField P.1)) hpointU)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨s, hs, z, hz, hzreg, hAway⟩ := actualPrimeLocalization_regularPrincipal_spreads
    I Q hfg ϖ hϖ.ne_zero (hmax.trans hϖ.maximalIdeal_eq)
  have hPs : P.1 ∈ X.basicOpen s := by
    have hq : U.2.primeIdealOf ⟨P.1, hPU⟩ ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact hs
    change U.2.fromSpec (U.2.primeIdealOf ⟨P.1, hPU⟩) ∈ X.basicOpen s at hq
    rw [IsAffineOpen.fromSpec_primeIdealOf] at hq
    exact hq
  let V := X.basicOpen s
  let VA : X.affineOpens := ⟨V, U.2.basicOpen s⟩
  let B := Γ(X, V)
  let ρ := X.presheaf.map (homOfLE (X.basicOpen_le s)).op
  letI : Nonempty V := ⟨⟨P.1, hPs⟩⟩
  letI : IsDomain B := inferInstance
  letI : Algebra A B := ρ.hom.toAlgebra
  letI : IsLocalization.Away s B := U.2.isLocalization_basicOpen s
  let F := IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) B
  have hF : F.toRingHom.comp (algebraMap A (Localization.Away s)) = ρ.hom := by
    ext a
    exact F.commutes a
  have hFz : F (algebraMap A (Localization.Away s) z) = ρ z := F.commutes z
  have hmap : (I.map (algebraMap A (Localization.Away s))).map F.toRingHom =
      i.ker.ideal VA := by
    rw [Ideal.map_map, hF]
    exact i.ker.map_ideal (U := VA) (V := U) (X.basicOpen_le s)
  have hprincipal : i.ker.ideal VA = Ideal.span ({ρ z} : Set B) := by
    rw [← hmap, hAway, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({F (algebraMap A (Localization.Away s) z)} : Set B) = _
    rw [hFz]
  have hs0 : s ≠ 0 := by
    intro hzero
    exact hs (by simpa only [hzero] using Q.zero_mem)
  letI : IsDomain (Localization.Away s) := Localization.Away.isDomain hs0
  have hBnonzero : ρ z ≠ 0 := by
    rw [← hFz]
    exact (RingEquiv.map_ne_zero_iff F.toRingEquiv).mpr (isRegular_iff_ne_zero.mp hzreg)
  exact ⟨s, hPs, z, hz, isRegular_iff_ne_zero.mpr hBnonzero, hprincipal⟩

/-- Generic geometric construction, before specializing the scheme to a
normalization. The original ideal section and its inclusion are retained. -/
private theorem closedPointIdeal_affine_regularGenerator_of_stalk_isDVR
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    ∃ V : X.affineOpens, P.1 ∈ V.1 ∧
      ∃ m : M.val.presheaf.obj (op V.1),
        let t : Γ(X, V) :=
          (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op V.1) m
        IsRegular t ∧ i.ker.ideal V = Ideal.span ({t} : Set Γ(X, V)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨_, ⟨U, hU, rfl⟩, hPU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P.1) isOpen_univ
  obtain ⟨s, hPs, z, hz, hreg, hprincipal⟩ :=
    closedPointIdeal_affine_regularPrincipal_neighborhood_of_stalk_isDVR
      X P ⟨U, hU⟩ hPU
  let V : X.affineOpens := ⟨X.basicOpen s, hU.basicOpen s⟩
  let t : Γ(X, V) := X.presheaf.map (homOfLE (X.basicOpen_le s)).op z
  have hmem : t ∈ i.ker.ideal V := by
    rw [hprincipal]
    exact Ideal.mem_span_singleton_self t
  obtain ⟨m, hm⟩ := IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem i V t hmem
  refine ⟨V, hPs, m, ?_⟩
  rw [hm]
  exact ⟨hreg, hprincipal⟩

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Primitive original-geometry point-ideal neighborhood. The chosen V is
ACTUALLY affine, contains the actual closed P of the SAME normalization,
and carries an ACTUAL ideal-module section whose original inclusion is a
regular generator of the SAME affine kernel ideal. All local geometry and
affine choice are derived; no DVR/principality/free/evaluation certificate. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_affine_regularGenerator
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
      ∃ V : N.affineOpens, P.1 ∈ V.1 ∧
        ∃ m : M.val.presheaf.obj (op V.1),
          let t : Γ(N, V) :=
            (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op V.1) m
          IsRegular t ∧ i.ker.ideal V = Ideal.span ({t} : Set Γ(N, V)) := by
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  letI : IsLocallyNoetherian N := integralGenericNormalization_isLocallyNoetherian X
    (toBase (projectiveIntersectionIdeal p q hp hq))
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsDiscreteValuationRing (N.presheaf.stalk P.1) :=
    projectiveIntersection_genericNormalization_closedPoint_stalk_isDVR p q hp hp0 n hn hq hnot P
  exact closedPointIdeal_affine_regularGenerator_of_stalk_isDVR N P

end PfaffianDescent.Coray
