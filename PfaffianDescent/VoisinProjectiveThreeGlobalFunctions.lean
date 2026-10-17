import PfaffianDescent.VoisinNegativeTwistGlobalH0
import PfaffianDescent.SchemePushforwardUnitSections
import PfaffianDescent.SchemeAffineFunctions
import AllCharacteristics.HomogeneousProjectiveAmbient

/-!
# Global functions on projective three-space

The standard four-chart Laurent calculation for the concrete zero twist
identifies every global section with a degree-zero polynomial, hence with a
ground-field scalar.  Via the previously constructed zero-twist comparison,
this gives the corresponding result for the structure sheaf.
-/

noncomputable section

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open LaurentLocalization TwistLaurent TwistCechTerms
open TwistCechTerms.GenericEvaluation

universe u

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- A degree-zero polynomial gives a global section of the concrete zero
twist by the fraction `p/1`. -/
noncomputable def p3ZeroTwistGlobalSectionOfHomogeneous (p : PS 0) :
    (sheafOfModules PS 0).sections := by
  let M := sheafOfModules PS 0
  let b : PS 0 := 1
  have hb : (b : MvPolynomial (Fin 4) K) = 1 := rfl
  have hU : ProjectiveSpectrum.basicOpen PS (b : MvPolynomial (Fin 4) K) = ⊤ := by
    rw [hb]
    exact ProjectiveSpectrum.basicOpen_one PS
  let sTop : M.val.obj (op (⊤ : Opens (Proj PS))) :=
    M.val.map (eqToHom hU.symm).op
      (sectionInBasicOpen PS 0 0 p b)
  exact M.val.sectionsMk
    (fun U ↦ M.val.map
      (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op sTop)
    (by
      intro U V f
      rw [← M.val.map_comp_apply]
      congr)

/-- The zero-twist section represented by a ground-field scalar. -/
noncomputable def p3ZeroTwistConstantSection (c : K) :
    (sheafOfModules PS 0).sections :=
  p3ZeroTwistGlobalSectionOfHomogeneous K
    ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin 4) c⟩

/-- The global section `p/1` has its defining homogeneous fraction as its
value at every projective point. -/
theorem p3ZeroTwistGlobalSectionOfHomogeneous_value
    (p : PS 0) (x : ProjectiveSpectrum.top PS) :
    (PresheafOfModules.sections.eval
      (p3ZeroTwistGlobalSectionOfHomogeneous K p)
      (op (⊤ : Opens (Proj PS)))).1 ⟨x, trivial⟩ =
      Localization.mk (p : MvPolynomial (Fin 4) K)
        ⟨1, Submonoid.one_mem _⟩ := by
  rfl

theorem p3ZeroTwistGlobalSectionOfHomogeneous_cechValue
    (p : PS 0) (n : ℕ) (f : Fin (n + 1) → Fin 4) :
    (PresheafOfModules.sections.eval
      (p3ZeroTwistGlobalSectionOfHomogeneous K p)
      (op (cechBasicOpen K n f))).1 (cechGenericPoint K n f) =
      Localization.mk (p : MvPolynomial (Fin 4) K)
        ⟨1, Submonoid.one_mem _⟩ := by
  rfl

/-- On each coordinate chart, the Laurent representative of `p/1` is the
ordinary Laurent image of `p`. -/
theorem p3ZeroTwistGlobalSectionOfHomogeneous_chartLaurent
    (p : PS 0) (i : Fin 4) :
    p3NegativeTwistGlobalCechLaurent K 0 0 ![i]
        (p3ZeroTwistGlobalSectionOfHomogeneous K p) =
      polynomialToLaurent (K := K) (p : MvPolynomial (Fin 4) K) := by
  let t : Fin 1 → Fin 4 := ![i]
  let s := p3ZeroTwistGlobalSectionOfHomogeneous K p
  let z := chartAway K 0 t 0 (t 0)
    (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 t)
    (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 t)))
  have hval := genericLocalizationMap_chartAway K 0 t 0 (t 0)
    (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 t)
    (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 t)))
  have hpoint := p3ZeroTwistGlobalSectionOfHomogeneous_cechValue K p 0 t
  change _ = _ *
    (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 t))).1
      (cechGenericPoint K 0 t) at hval
  rw [hpoint] at hval
  have hcross : z.val =
      algebraMap (MvPolynomial (Fin 4) K)
        (Localization.Away (p3CechDenominator (K := K) 0 t))
        (p : MvPolynomial (Fin 4) K) := by
    apply genericLocalizationMap_injective K 0 t
    rw [genericLocalizationMap_algebraMap K 0 t]
    calc
      _ = algebraMap (MvPolynomial (Fin 4) K)
            (Fiber PS (p3GenericPoint K))
            ((degreeOnePower PS (p3Coordinate K (t 0)) 0 : PS 0) :
              MvPolynomial (Fin 4) K) *
          Localization.mk (p : MvPolynomial (Fin 4) K)
            ⟨1, Submonoid.one_mem _⟩ := hval
      _ = _ := by
        simp only [degreeOnePower, pow_zero, map_one, one_mul]
        exact Localization.mk_one_eq_algebraMap _
  have hL := congrArg (localizationAwayToLaurent (K := K) 0 t) hcross
  rw [localizationAwayToLaurent_algebraMap] at hL
  change awayToLaurent (K := K) 0 t z =
    polynomialToLaurent (K := K) (p : MvPolynomial (Fin 4) K) at hL
  have hshift : AddMonoidAlgebra.single (twistShift 0 (t 0)) (1 : K) = 1 := by
    simp [twistShift, ← AddMonoidAlgebra.one_def]
  change awayToLaurent (K := K) 0 t z *
    AddMonoidAlgebra.single (twistShift 0 (t 0)) 1 =
      polynomialToLaurent (K := K) (p : MvPolynomial (Fin 4) K)
  rw [hshift, mul_one]
  exact hL

/-- A zero-twist global section is determined by its Laurent representative
on the four standard charts. -/
theorem p3ZeroTwist_global_eq_of_chartLaurent_eq
    (s t : (sheafOfModules PS 0).sections)
    (h : ∀ i : Fin 4,
      p3NegativeTwistGlobalCechLaurent K 0 0 ![i] s =
        p3NegativeTwistGlobalCechLaurent K 0 0 ![i] t) : s = t := by
  have hlocal (i : Fin 4) :
      PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 ![i])) =
        PresheafOfModules.sections.eval t (op (cechBasicOpen K 0 ![i])) := by
    have haway :
        chartAway K 0 ![i] 0 i
            (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
            (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 ![i]))) =
          chartAway K 0 ![i] 0 i
            (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
            (PresheafOfModules.sections.eval t (op (cechBasicOpen K 0 ![i]))) := by
      apply twistAwayToLaurent_injective (K := K) 0 0 ![i]
      exact h i
    let e := p3NegativeTwistBasicOpenIsoAway K
      (p3CechDenominator (K := K) 0 ![i]) 1
      (p3CechDenominator_mem (K := K) 0 ![i]) (by decide)
      i (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i]) 0
    change e.hom
        (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 ![i]))) =
      e.hom
        (PresheafOfModules.sections.eval t (op (cechBasicOpen K 0 ![i])))
      at haway
    exact (ConcreteCategory.bijective_of_isIso e.hom).1 haway
  let M := sheafOfModules PS 0
  let G : TopCat.Sheaf AddCommGrpCat (Proj PS) :=
    (SheafOfModules.toSheaf (Proj PS).ringCatSheaf).obj M
  have htop : PresheafOfModules.sections.eval s
        (op (⊤ : Opens (Proj PS))) =
      PresheafOfModules.sections.eval t
        (op (⊤ : Opens (Proj PS))) := by
    apply G.eq_of_locally_eq'
      (fun i : Fin 4 => cechBasicOpen K 0 ![i])
      (⊤ : Opens (Proj PS))
      (fun _ => homOfLE le_top)
      (by rw [p3CechSingleOpen_iSup K])
    intro i
    change M.presheaf.map
        (homOfLE (show cechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval s
            (op (⊤ : Opens (Proj PS)))) =
      M.presheaf.map
        (homOfLE (show cechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval t
            (op (⊤ : Opens (Proj PS))))
    have hsres : M.presheaf.map
          (homOfLE (show cechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval s
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval s
          (op (cechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property s _
    have htres : M.presheaf.map
          (homOfLE (show cechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval t
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval t
          (op (cechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property t _
    rw [hsres, htres]
    exact hlocal i
  apply PresheafOfModules.sections_ext
  intro U
  let r := M.presheaf.map
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have hsU := PresheafOfModules.sections_property s
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have htU := PresheafOfModules.sections_property t
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have hres : r (PresheafOfModules.sections.eval s
        (op (⊤ : Opens (Proj PS)))) =
      r (PresheafOfModules.sections.eval t
        (op (⊤ : Opens (Proj PS)))) := congrArg (fun q => r q) htop
  exact hsU.symm.trans (hres.trans htU)

/-- The common Laurent representative of a zero-twist global section has
degree zero and no negative exponents. -/
theorem p3ZeroTwist_commonLaurent_support
    (s : (sheafOfModules PS 0).sections) :
    ∀ a ∈ (p3NegativeTwistGlobalCechLaurent K 0 0 ![0] s).coeff.support,
      totalDegree a = 0 ∧ negativeSupport a = ∅ := by
  intro a ha
  have hzero := p3NegativeTwistGlobalCechLaurent_support K 0 0 ![0] s a ha
  have haone : a ∈
      (p3NegativeTwistGlobalCechLaurent K 0 0 ![1] s).coeff.support := by
    rw [← p3NegativeTwistGlobalChartLaurent_eq K 0 s 0 1]
    exact ha
  have hone := p3NegativeTwistGlobalCechLaurent_support K 0 0 ![1] s a haone
  exact ⟨by simpa using hzero.1,
    negativeSupport_eq_empty_of_subset_singletons a
      (by simpa using hzero.2) (by simpa using hone.2)⟩

/-- Every global section of the concrete zero twist comes from a
degree-zero homogeneous polynomial. -/
theorem p3ZeroTwistGlobalSectionOfHomogeneous_surjective :
    Function.Surjective (p3ZeroTwistGlobalSectionOfHomogeneous K) := by
  intro s
  let g := p3NegativeTwistGlobalCechLaurent K 0 0 ![0] s
  have hp := polynomialOfNonnegativeLaurent_mem_and_map K g 0
    (p3ZeroTwist_commonLaurent_support K s)
  let p : PS 0 := ⟨polynomialOfNonnegativeLaurent K g, hp.1⟩
  refine ⟨p, ?_⟩
  apply p3ZeroTwist_global_eq_of_chartLaurent_eq K
  intro i
  calc
    p3NegativeTwistGlobalCechLaurent K 0 0 ![i]
        (p3ZeroTwistGlobalSectionOfHomogeneous K p) =
      polynomialToLaurent (K := K) (p : MvPolynomial (Fin 4) K) :=
        p3ZeroTwistGlobalSectionOfHomogeneous_chartLaurent K p i
    _ = g := hp.2
    _ = p3NegativeTwistGlobalCechLaurent K 0 0 ![i] s :=
      p3NegativeTwistGlobalChartLaurent_eq K 0 s 0 i

/-- Every concrete zero-twist section is a scalar section. -/
theorem p3ZeroTwistConstantSection_surjective :
    Function.Surjective (p3ZeroTwistConstantSection K) := by
  intro s
  obtain ⟨p, rfl⟩ := p3ZeroTwistGlobalSectionOfHomogeneous_surjective K s
  let c : K := (p : MvPolynomial (Fin 4) K).coeff 0
  have hpdegree : (p : MvPolynomial (Fin 4) K).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 4)).mpr p.property
  have hp : (p : MvPolynomial (Fin 4) K) = MvPolynomial.C c :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hpdegree
  refine ⟨c, ?_⟩
  exact congrArg (p3ZeroTwistGlobalSectionOfHomogeneous K)
    (Subtype.ext hp.symm)

/-- Distinct scalars give distinct concrete zero-twist sections. -/
theorem p3ZeroTwistConstantSection_injective :
    Function.Injective (p3ZeroTwistConstantSection K) := by
  intro c d h
  have hchart := congrArg
    (p3NegativeTwistGlobalCechLaurent K 0 0 ![0]) h
  dsimp only [p3ZeroTwistConstantSection] at hchart
  rw [p3ZeroTwistGlobalSectionOfHomogeneous_chartLaurent,
    p3ZeroTwistGlobalSectionOfHomogeneous_chartLaurent] at hchart
  exact MvPolynomial.C_injective (Fin 4) K
    (polynomialToLaurent_injective (K := K) hchart)

theorem p3ZeroTwistConstantSection_bijective :
    Function.Bijective (p3ZeroTwistConstantSection K) :=
  ⟨p3ZeroTwistConstantSection_injective K,
    p3ZeroTwistConstantSection_surjective K⟩

/-- The ground-field scalar viewed as an ordinary global regular function
on projective three-space. -/
noncomputable def p3GlobalFunctionScalar (c : K) : Γ(Proj PS, ⊤) :=
  moduleSectionsEquivTop (Proj PS)
    (SheafOfModules.unit (Proj PS).ringCatSheaf)
    (SheafOfModules.sectionsMap (unitIsoZeroTwist PS).inv
      (p3ZeroTwistConstantSection K c))

/-- Every regular function on projective three-space is a scalar. -/
theorem p3GlobalFunctionScalar_surjective :
    Function.Surjective (p3GlobalFunctionScalar K) := by
  intro r
  let eUnit := moduleSectionsEquivTop (Proj PS)
    (SheafOfModules.unit (Proj PS).ringCatSheaf)
  let eZero := schemeModuleSectionsEquivOfIso (unitIsoZeroTwist PS).symm
  obtain ⟨c, hc⟩ := p3ZeroTwistConstantSection_surjective K
    (eZero.symm (eUnit.symm r))
  refine ⟨c, ?_⟩
  change eUnit (eZero (p3ZeroTwistConstantSection K c)) = r
  rw [hc, eZero.apply_symm_apply]
  exact eUnit.apply_symm_apply r

theorem p3GlobalFunctionScalar_injective :
    Function.Injective (p3GlobalFunctionScalar K) := by
  intro c d h
  let eUnit := moduleSectionsEquivTop (Proj PS)
    (SheafOfModules.unit (Proj PS).ringCatSheaf)
  let eZero := schemeModuleSectionsEquivOfIso (unitIsoZeroTwist PS).symm
  have hc : eUnit (eZero (p3ZeroTwistConstantSection K c)) =
      eUnit (eZero (p3ZeroTwistConstantSection K d)) := h
  exact p3ZeroTwistConstantSection_injective K
    (eZero.injective (eUnit.injective hc))

theorem p3GlobalFunctionScalar_bijective :
    Function.Bijective (p3GlobalFunctionScalar K) :=
  ⟨p3GlobalFunctionScalar_injective K,
    p3GlobalFunctionScalar_surjective K⟩

/-- The scalar global function has the expected value in every homogeneous
localization stalk. -/
theorem p3GlobalFunctionScalar_value
    (c : K) (x : ProjectiveSpectrum.top PS) :
    ((p3GlobalFunctionScalar K c).1 ⟨x, trivial⟩).val =
      Localization.mk (MvPolynomial.C c : MvPolynomial (Fin 4) K)
        (1 : (pointIdeal PS x).primeCompl) := by
  let t := p3ZeroTwistConstantSection K c
  let eZero := schemeModuleSectionsEquivOfIso (unitIsoZeroTwist PS).symm
  have hback : SheafOfModules.sectionsMap (unitIsoZeroTwist PS).hom
      (SheafOfModules.sectionsMap (unitIsoZeroTwist PS).inv t) = t :=
    eZero.symm_apply_apply t
  have hv := congrArg
    (fun q : (sheafOfModules PS 0).sections =>
      (PresheafOfModules.sections.eval q (op (⊤ : Opens (Proj PS)))).1
        ⟨x, trivial⟩) hback
  change ((p3GlobalFunctionScalar K c).1 ⟨x, trivial⟩).val =
      (PresheafOfModules.sections.eval t (op (⊤ : Opens (Proj PS)))).1
        ⟨x, trivial⟩ at hv
  exact hv.trans (p3ZeroTwistGlobalSectionOfHomogeneous_value K
    ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin 4) c⟩ x)

/-- The standard projective-space structure map to the ground field. -/
noncomputable def p3BaseMap : Proj PS ⟶ Spec (.of K) :=
  Proj.toSpecZero PS ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (PS 0)))

private lemma affineFunctionHom_toSpecZero_section
    (b : PS 0) :
    affineFunctionHom (Proj.toSpecZero PS) b =
      ((CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)) ≫
        Proj.awayToSection PS 1 ≫
        (Proj.basicOpen PS 1).topIso.inv ≫
        ((Proj PS).isoOfEq (Proj.basicOpen_one PS)).inv.appTop ≫
        (Proj PS).topIso.inv.appTop).hom b) := by
  unfold affineFunctionHom
  rw [Proj.toSpecZero]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  simp only [Proj.basicOpenToSpec, Scheme.Hom.comp_appTop,
    Scheme.Opens.toSpecΓ_appTop, Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc
    (Proj.awayToSection PS 1)]
  simp

private lemma open_eq_top_section_transport_apply
    (U : (Proj PS).Opens) (e : U = ⊤) (s : Γ(Proj PS, U))
    (x : ProjectiveSpectrum.top PS) :
    (((U.topIso.inv ≫ ((Proj PS).isoOfEq e).inv.appTop ≫
      (Proj PS).topIso.inv.appTop).hom s).1 ⟨x, trivial⟩) =
        s.1 ⟨x, e.symm ▸ trivial⟩ := by
  subst U
  simp only [Scheme.isoOfEq_rfl, Iso.refl_inv]
  change ((((Proj PS).topIso.hom.appTop ≫
    (Proj PS).topIso.inv.appTop).hom s).1 ⟨x, trivial⟩) = _
  rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
  rfl

private lemma localizationMap_mk_one
    {R : Type u} [CommRing R] (M N : Submonoid R)
    (h : M ≤ Submonoid.comap (RingHom.id R) N) (r : R) :
    IsLocalization.map (Localization N) (RingHom.id R)
        h (Localization.mk r (1 : M)) =
      Localization.mk r (1 : N) := by
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  rw [← Localization.mk_eq_mk']
  congr 2

set_option backward.isDefEq.respectTransparency false

/-- The actual structure morphism sends a ground-field scalar to the same
fraction `C c / 1` at every projective point. -/
private lemma p3BaseMap_scalar_value
    (c : K) (x : ProjectiveSpectrum.top PS) :
    ((affineFunctionHom (p3BaseMap K) c).1 ⟨x, trivial⟩).val =
      Localization.mk (MvPolynomial.C c : MvPolynomial (Fin 4) K)
        (1 : (pointIdeal PS x).primeCompl) := by
  change ((affineFunctionHom
      (Proj.toSpecZero PS ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (PS 0)))) c).1
        ⟨x, trivial⟩).val = _
  have hbase : affineFunctionHom
      (Proj.toSpecZero PS ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (PS 0)))) c =
      affineFunctionHom (Proj.toSpecZero PS)
        (algebraMap K (PS 0) c) := by
    simpa using congrArg (fun f => f c)
      (affineFunctionHom_comp_Spec (Proj.toSpecZero PS)
        (algebraMap K (PS 0)))
  rw [hbase]
  rw [affineFunctionHom_toSpecZero_section K]
  let U := Proj.basicOpen PS 1
  let e : U = (⊤ : (Proj PS).Opens) := Proj.basicOpen_one PS
  let b : PS 0 := algebraMap K (PS 0) c
  let s : Γ(Proj PS, U) :=
    (Proj.awayToSection PS 1).hom
      (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1) b)
  have htransport := open_eq_top_section_transport_apply K U e s x
  have hsection :
      ((CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)) ≫
        Proj.awayToSection PS 1 ≫ U.topIso.inv ≫
        ((Proj PS).isoOfEq e).inv.appTop ≫
        (Proj PS).topIso.inv.appTop).hom b) =
      ((U.topIso.inv ≫ ((Proj PS).isoOfEq e).inv.appTop ≫
        (Proj PS).topIso.inv.appTop).hom s) := rfl
  rw [hsection, htransport]
  dsimp only [s, b]
  let y : U := ⟨x, e.symm ▸ trivial⟩
  have haw := ProjectiveSpectrum.Proj.awayToSection_apply PS
    (1 : MvPolynomial (Fin 4) K)
    (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)
      (algebraMap K (PS 0) c)) y
  change HomogeneousLocalization.val
    (((CommRingCat.Hom.hom (Proj.awayToSection PS 1))
      (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)
        (algebraMap K (PS 0) c))).1 y) = _ at haw
  have hbval :
      (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)
        (algebraMap K (PS 0) c)).val =
      Localization.mk ((algebraMap K (PS 0) c) : MvPolynomial (Fin 4) K)
        (1 : Submonoid.powers (1 : MvPolynomial (Fin 4) K)) := rfl
  rw [hbval] at haw
  have hMN : Submonoid.powers (1 : MvPolynomial (Fin 4) K) ≤
      Submonoid.comap (RingHom.id (MvPolynomial (Fin 4) K))
        (pointIdeal PS x).primeCompl := by
    intro z hz
    exact (Submonoid.powers_le.mpr y.2) hz
  have hmap := localizationMap_mk_one
    (Submonoid.powers (1 : MvPolynomial (Fin 4) K))
    (pointIdeal PS x).primeCompl hMN
    ((algebraMap K (PS 0) c) : MvPolynomial (Fin 4) K)
  rw [hmap] at haw
  have hbcoord : ((algebraMap K (PS 0) c) :
      MvPolynomial (Fin 4) K) = MvPolynomial.C c := rfl
  have haw' := haw.trans (congrArg
    (fun z => Localization.mk z (1 : (pointIdeal PS x).primeCompl)) hbcoord)
  simpa only [y, b] using haw'

/-- The explicit scalar fraction is exactly the ground-field pullback along
the standard projective-space structure morphism. -/
theorem p3GlobalFunctionScalar_eq_affineFunctionHom
    (c : K) :
    p3GlobalFunctionScalar K c = affineFunctionHom (p3BaseMap K) c := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  exact (p3GlobalFunctionScalar_value K c x.1).trans
    (p3BaseMap_scalar_value K c x.1).symm

/-- The canonical pullback of ground-field scalars is a bijection onto the
ordinary global regular functions of projective three-space. -/
theorem p3BaseMap_affineFunctionHom_bijective :
    Function.Bijective (affineFunctionHom (p3BaseMap K)) := by
  constructor
  · intro c d h
    apply p3GlobalFunctionScalar_injective K
    rw [p3GlobalFunctionScalar_eq_affineFunctionHom,
      p3GlobalFunctionScalar_eq_affineFunctionHom]
    exact h
  · intro r
    obtain ⟨c, hc⟩ := p3GlobalFunctionScalar_surjective K r
    exact ⟨c, (p3GlobalFunctionScalar_eq_affineFunctionHom K c).symm.trans hc⟩

/-- The project's standard ambient structure morphism identifies the ground
field with all global regular functions on projective three-space. -/
theorem ambientToBase_affineFunctionHom_bijective :
    Function.Bijective (affineFunctionHom
      (AllCharacteristics.HomogeneousProjective.ambientToBase
        (R := K) (σ := Fin 4))) := by
  change Function.Bijective (affineFunctionHom (p3BaseMap K))
  exact p3BaseMap_affineFunctionHom_bijective K

end PfaffianDescent.ProjectiveNegativeTwist
