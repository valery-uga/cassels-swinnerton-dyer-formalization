import PfaffianDescent.CorayOwnComponentProperConstants
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift
import PfaffianDescent.NormalizationResidueGlobalTransport
import PfaffianDescent.CorayIntegralFullConstantsNormalizationDefectBound
import PfaffianDescent.CoraySignedCycleWordDegreeSelection

/-! Source-only conditional downstream Ai glue. An ACTUAL regular degree-three
point of the SAME selected integral whole original curve is an honest input.
The natural tangent-good point and regular-at-A q selector are not constructed.
No GI, normalization cycle, regular-P or constants-rank-one premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Ordinary finite arithmetic retains both possible constants ranks. -/
private theorem ai_regularDegreeThreePoint_fullConstants_defect_contradiction001
    (G d r delta : ℕ) (hG : 1 ≤ G) (hstrict : G < d)
    (hdiv : r ∣ 3) (hupper : delta + 1 ≤ r + G)
    (hsingular : d ≤ delta) (hthree : 3 ∣ r → 2 * d ≤ delta) : False := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hr | hr
  · subst r
    omega
  · have hlower := hthree (hr.symm ▸ (dvd_rfl : 3 ∣ 3))
    subst r
    omega

/-- On the SAME literal integral original p/q scheme, a genuine regular
original degree-three auxiliary point forces the strict large-degree original
point regular. The regular auxiliary point is lifted internally, hence full
normalization constants divide three. The three-constants alternative is
eliminated by the existing actual global defect theorem. No GI assumption. -/
theorem projectiveIntersection_integral_originalClosedPoint_isRegularLocalRing_of_degree_gt_of_regular_degreeThreePoint001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P A : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) 3)
    (hstrict : 3 * n.choose 2 + 1 <
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1)
    (hAdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree A.1 = 3)
    (hAregular : IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk A.1)) :
    IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let piX := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let piN := nu ≫ piX
  letI : IsIntegral N := inferInstance
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X piX
  letI : IsProper piN := inferInstance
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver piN
  letI : AddCommGroup (schemeModuleCohomology N ON 1) := Ext.instAddCommGroup
  letI : Module K (schemeModuleCohomology N ON 1) := Ext.instModule
  letI : AddCommGroup (SchemeModuleOpenSectionsOver piN ON ⊤) :=
    inferInstanceAs (AddCommGroup Γ(ON, ⊤))
  letI : Module K (SchemeModuleOpenSectionsOver piN ON ⊤) :=
    Module.compHom Γ(ON, ⊤) (schemeOpenBaseRingHom piN ⊤)
  let Q : X.Modules := genericNormalizationQuotientSheaf X
  letI : AddCommGroup (SchemeModuleOpenSectionsOver piX Q ⊤) :=
    inferInstanceAs (AddCommGroup Γ(Q, ⊤))
  letI : Module K (SchemeModuleOpenSectionsOver piX Q ⊤) :=
    Module.compHom Γ(Q, ⊤) (schemeOpenBaseRingHom piX ⊤)
  let r := Module.finrank K (SchemeModuleOpenSectionsOver piN ON ⊤)
  let delta := Module.finrank K (SchemeModuleGlobalSectionsOver piX Q)
  obtain ⟨AN, _hANpoint, _hANiso, _hANrelative, hANdegree⟩ :=
    projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot A hAregular
  have hDegreeA : piN.residueDegree AN.1 = 3 := hANdegree.trans hAdegree
  have hdiv : r ∣ 3 := by
    have h := integralProper_originalUnitSections_finrank_dvd_residueDegree piN AN
    change r ∣ piN.residueDegree AN.1 at h
    rw [hDegreeA] at h
    exact h
  have hupper : delta + 1 ≤ r + (3 * n.choose 2 + 1) := by
    have hbound :
        Module.finrank K (schemeModuleCohomology N ON 1) +
            Module.finrank K (SchemeModuleOpenSectionsOver piX Q ⊤) + 1 ≤
          r + (1 + 3 * n * (n - 1) / 2) :=
      projectiveIntersection_integral_genericNormalization_cohomology_one_add_globalQuotient_fullConstants_bound
        p q hp hp0 n hn hq hnot
    have hQ : delta = Module.finrank K (SchemeModuleOpenSectionsOver piX Q ⊤) :=
      (schemeModuleGlobalSectionsLinearEquivOpenTop piX Q).finrank_eq
    rw [← coray_choose_genus_eq_euler_bound n] at hbound
    omega
  by_contra hsingular
  have hsingularDegree : piX.residueDegree P.1 ≤ delta :=
    projectiveIntersection_genericNormalization_nonregular_originalClosedPoint_degree_le_globalDefect
      p q hp hp0 n hq hnot P hsingular
  have hthree : 3 ∣ r → 2 * piX.residueDegree P.1 ≤ delta :=
    projectiveIntersection_three_constants_globalDefect_ge_twice_point_degree
      p q hp hp0 n hq hnot P hPcop
  exact ai_regularDegreeThreePoint_fullConstants_defect_contradiction001
    (3 * n.choose 2 + 1) (piX.residueDegree P.1) r delta (by omega)
      hstrict hdiv hupper hsingularDegree hthree

end PfaffianDescent.Coray
